use std::process::Output;
use std::sync::{Arc, OnceLock, Weak};
use std::time::Duration;

use crossbeam::channel::{Receiver, RecvTimeoutError, SendTimeoutError, Sender};
use ruff_db::system::{CommandExecutor, System, SystemPathBuf, WhichError};

use super::{MetadataTarget, Uv, unsupported_command_execution, uv_executable_error};
use crate::Db;

const MAX_UV_WORKERS: usize = 2;
const MAX_QUEUED_UV_TASKS: usize = 8;
/// Maximum time to block before checking cancellation and yielding to Rayon.
const POLL_TIMEOUT: Duration = Duration::from_millis(1);

/// A standalone script environment that should be synchronized by uv.
#[derive(Debug)]
pub(crate) struct ScriptSyncTask {
    pub(crate) path: SystemPathBuf,
    pub(crate) python: Option<SystemPathBuf>,
}

/// Synchronizes standalone script environments with uv.
///
/// A project stores one service in its shared `ScriptEnvironments`, so every database snapshot uses
/// the same workers and bounded request queue. This limits how many uv processes and queued jobs a
/// project can create.
///
/// Database updates cancel older Salsa snapshots and wait for them to be dropped, but a uv job can
/// outlive the check that scheduled it. Workers therefore do not retain the database. They also use
/// a detached command executor because applying filesystem changes requires exclusive access to the
/// database's `System`.
#[derive(Default)]
pub(crate) struct UvSyncService {
    workers: OnceLock<std::io::Result<UvWorkerPool>>,
}

impl UvSyncService {
    /// Synchronizes one script and waits for its result.
    ///
    /// Waiting cooperatively yields the current Rayon worker so it can execute other checking work.
    pub(crate) fn run(&self, db: &dyn Db, task: ScriptSyncTask) -> std::io::Result<Output> {
        let workers = self.worker_pool(db.system())?;

        // Dropping the guard during Salsa unwinding cancels a job that hasn't started yet.
        let (_cancellation_guard, cancellation) = UvJobCancellation::new();

        // Each job produces one result. Buffering that result lets the worker publish it without
        // waiting for this caller to be scheduled again.
        let (result_sender, result_receiver) = crossbeam::channel::bounded(1);

        let mut request = UvJob {
            task,
            result: result_sender,
            cancellation,
            span: tracing::Span::current(),
        };

        // Queue the job, checking for Salsa cancellation while waiting for capacity.
        loop {
            match workers.requests.send_timeout(request, POLL_TIMEOUT) {
                Ok(()) => break,
                Err(SendTimeoutError::Timeout(pending)) => {
                    db.unwind_if_revision_cancelled();
                    // Keep the unsent request and let Rayon run another queued task before
                    // retrying. This prevents a full uv queue from idling a checking worker.
                    request = pending;
                    rayon::yield_now();
                }
                Err(SendTimeoutError::Disconnected(_)) => return Err(worker_disconnected()),
            }
        }

        // Wait for the result.
        loop {
            match result_receiver.recv_timeout(POLL_TIMEOUT) {
                Ok(output) => return output,
                Err(RecvTimeoutError::Timeout) => {
                    db.unwind_if_revision_cancelled();
                    // If the snapshot is still current, let Rayon run another queued task before
                    // polling for the uv result again.
                    rayon::yield_now();
                }
                Err(RecvTimeoutError::Disconnected) => return Err(worker_disconnected()),
            }
        }
    }

    fn worker_pool(&self, system: &dyn System) -> std::io::Result<&UvWorkerPool> {
        match self.workers.get_or_init(|| {
            let command_executor = system
                .command_executor()
                .ok_or_else(unsupported_command_execution)?;
            let uv = Uv::new(system);
            UvWorkerPool::new(command_executor, &uv)
        }) {
            Ok(workers) => Ok(workers),
            Err(error) => Err(std::io::Error::new(error.kind(), error.to_string())),
        }
    }
}

impl std::panic::RefUnwindSafe for UvSyncService {}

/// A bounded worker pool for synchronizing standalone script environments with uv.
struct UvWorkerPool {
    requests: Sender<UvJob>,
}

impl UvWorkerPool {
    /// Creates worker threads using a detached command executor and resolved uv executable.
    fn new(
        command_executor: &dyn CommandExecutor,
        uv: &Result<Uv, WhichError>,
    ) -> std::io::Result<Self> {
        let (requests, receiver) = crossbeam::channel::bounded(MAX_QUEUED_UV_TASKS);
        let workers = ruff_db::max_parallelism().get().min(MAX_UV_WORKERS);
        tracing::debug!("Starting {workers} uv synchronization workers");

        for index in 0..workers {
            let worker = UvWorker {
                executor: command_executor.dyn_clone(),
                uv: uv.clone(),
                requests: receiver.clone(),
            };

            let _ = std::thread::Builder::new()
                .name(format!("ty-uv-sync-{index}"))
                .spawn(move || worker.run())?;
        }

        Ok(Self { requests })
    }
}

struct UvJob {
    task: ScriptSyncTask,
    result: Sender<std::io::Result<Output>>,
    cancellation: UvJobCancellation,
    span: tracing::Span,
}

/// Detects whether the blocking Salsa operation that queued a uv job is still alive.
///
/// The scheduling operation holds a [`UvJobCancellationGuard`] while the queued job holds this weak
/// token. Salsa cancellation unwinds the scheduling operation and drops the guard, allowing the
/// worker to discard the job without retaining the database or explicitly updating shared state.
/// An already running uv process is not interrupted.
struct UvJobCancellation(Weak<()>);

impl UvJobCancellation {
    fn new() -> (UvJobCancellationGuard, Self) {
        let guard = UvJobCancellationGuard(Arc::new(()));
        let cancellation = Self(Arc::downgrade(&guard.0));
        (guard, cancellation)
    }

    fn is_cancelled(&self) -> bool {
        self.0.upgrade().is_none()
    }
}

/// Keeps a blocking uv job active while its scheduling operation is running.
struct UvJobCancellationGuard(Arc<()>);

struct UvWorker {
    executor: Box<dyn CommandExecutor>,
    uv: Result<Uv, WhichError>,
    requests: Receiver<UvJob>,
}

impl UvWorker {
    fn run(self) {
        for job in &self.requests {
            if job.cancellation.is_cancelled() {
                tracing::debug!(
                    "Discarded cancelled script synchronization for `{}`",
                    job.task.path
                );
                continue;
            }

            let output = self.execute(&job);
            let _ = job.result.send(output);
        }
    }

    fn execute(&self, request: &UvJob) -> std::io::Result<Output> {
        let _span = request.span.enter();
        tracing::info!("Synchronizing script `{}`", request.task.path);

        let uv = self
            .uv
            .as_ref()
            .map_err(|error| uv_executable_error(*error))?;

        let target = MetadataTarget::Script {
            path: &request.task.path,
            python: request.task.python.as_deref(),
        };

        let output = uv.execute(self.executor.as_ref(), target);

        if output.as_ref().is_ok_and(|output| output.status.success()) {
            tracing::debug!("Successfully synchronized script `{}`", request.task.path);
        } else {
            tracing::debug!("Failed to synchronize script `{}`", request.task.path);
        }

        output
    }
}

fn worker_disconnected() -> std::io::Error {
    std::io::Error::new(
        std::io::ErrorKind::BrokenPipe,
        "uv synchronization worker terminated unexpectedly",
    )
}

#[cfg(test)]
mod tests {
    use std::panic::AssertUnwindSafe;
    use std::sync::Arc;
    use std::time::Duration;

    use ruff_db::system::{OsSystem, System as _, SystemPath, SystemPathBuf, TestSystem};
    use salsa::{Cancelled, Database as _};
    use ty_static::EnvVars;

    use super::{ScriptSyncTask, UvSyncService, UvWorkerPool};
    use crate::ProjectMetadata;
    use crate::db::testing::TestDb;

    #[test]
    fn database_write_cancels_pending_uv_sync() -> anyhow::Result<()> {
        let root = SystemPath::new("/project").to_path_buf();
        let path = root.join("script.py");
        let mut db = TestDb::new(ProjectMetadata::new("test", root));
        let snapshot = db.clone();
        let service = Arc::new(UvSyncService::default());
        let waiting_service = Arc::clone(&service);
        let (request_sender, request_receiver) = crossbeam::channel::bounded(1);
        assert!(
            service
                .workers
                .set(Ok(UvWorkerPool {
                    requests: request_sender,
                }))
                .is_ok()
        );

        let waiting = std::thread::spawn(move || {
            Cancelled::catch(AssertUnwindSafe(|| {
                waiting_service.run(&snapshot, ScriptSyncTask { path, python: None })
            }))
        });
        let request = request_receiver.recv_timeout(Duration::from_secs(5))?;

        db.trigger_cancellation();

        let result = waiting
            .join()
            .map_err(|_| anyhow::anyhow!("uv synchronization waiter panicked"))?;
        assert!(matches!(result, Err(Cancelled::PendingWrite)));
        assert!(request.cancellation.is_cancelled());

        Ok(())
    }

    #[test]
    fn uv_resolution_is_lazy_and_cached() -> anyhow::Result<()> {
        let current_exe = SystemPathBuf::from_path_buf(std::env::current_exe()?)
            .map_err(|path| anyhow::anyhow!("non-UTF-8 test executable: {}", path.display()))?;
        let cwd = current_exe
            .parent()
            .ok_or_else(|| anyhow::anyhow!("test executable has no parent"))?;
        let missing = cwd.join("__ty_missing_uv_executable__");

        let system = TestSystem::new(OsSystem::new(cwd));
        assert!(!system.path_exists(&missing));
        system.set_env_var(EnvVars::UV, missing.as_str());
        let service = UvSyncService::default();
        assert!(service.workers.get().is_none());

        system.set_env_var(EnvVars::UV, current_exe.as_str());
        let first = service.worker_pool(&system)?;

        system.set_env_var(EnvVars::UV, missing.as_str());
        let second = service.worker_pool(&system)?;
        assert!(std::ptr::eq(first, second));

        Ok(())
    }
}
