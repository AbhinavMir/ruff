use std::process::Output;
use std::sync::{Arc, OnceLock, Weak};
use std::time::Duration;

use crossbeam::channel::{Receiver, RecvTimeoutError, SendTimeoutError, Sender};
use ruff_db::files::File;
use ruff_db::system::{CommandExecutor, System, SystemPathBuf, WhichError};

use super::{MetadataTarget, Uv, unsupported_command_execution, uv_executable_error};
use crate::{Db, ScriptSyncProgress};

const MAX_UV_WORKERS: usize = 2;
const MAX_QUEUED_UV_TASKS: usize = 8;
/// Maximum time to block before checking cancellation and yielding to Rayon.
const POLL_TIMEOUT: Duration = Duration::from_millis(1);

/// Determines whether a script environment needs to be synchronized.
///
/// Equal keys let ty reuse the current environment without invoking uv. The key changes when the
/// extracted PEP 723 metadata text or configured Python override changes; edits elsewhere in the
/// script leave it unchanged.
pub(crate) type ScriptEnvironmentCacheKey = u64;

/// A standalone script environment that should be synchronized by uv.
#[derive(Debug)]
pub(crate) struct ScriptSyncTask {
    pub(crate) file: File,
    pub(crate) request: ScriptSyncRequest,
}

impl ScriptSyncTask {
    pub(crate) fn new(
        file: File,
        path: SystemPathBuf,
        python: Option<SystemPathBuf>,
        cache_key: ScriptEnvironmentCacheKey,
    ) -> Self {
        Self {
            file,
            request: ScriptSyncRequest(Arc::new(ScriptSyncRequestData {
                path,
                python,
                cache_key,
            })),
        }
    }
}

/// The immutable inputs to one uv synchronization.
///
/// The entry state and worker retain cheap clones because a job can outlive the Salsa snapshot that
/// scheduled it.
#[derive(Clone, Debug)]
pub(crate) struct ScriptSyncRequest(Arc<ScriptSyncRequestData>);

impl ScriptSyncRequest {
    pub(crate) fn path(&self) -> &ruff_db::system::SystemPath {
        &self.0.path
    }

    pub(crate) fn python(&self) -> Option<&ruff_db::system::SystemPath> {
        self.0.python.as_deref()
    }

    pub(crate) fn cache_key(&self) -> ScriptEnvironmentCacheKey {
        self.0.cache_key
    }
}

#[derive(Debug)]
struct ScriptSyncRequestData {
    path: SystemPathBuf,
    python: Option<SystemPathBuf>,
    cache_key: ScriptEnvironmentCacheKey,
}

/// The result of synchronizing a standalone script environment.
///
/// This owns the progress guard so progress remains active until the result is consumed.
pub struct ScriptSyncResult {
    pub(crate) task: ScriptSyncTask,
    pub(crate) output: std::io::Result<Output>,
    pub(crate) progress: Option<Box<dyn ScriptSyncProgress>>,
}

impl ScriptSyncResult {
    /// Returns the absolute path of the synchronized script.
    pub fn path(&self) -> &ruff_db::system::SystemPath {
        self.task.request.path()
    }
}

impl std::fmt::Debug for ScriptSyncResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ScriptSyncResult")
            .field("task", &self.task)
            .field("output", &self.output)
            .finish_non_exhaustive()
    }
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
pub(crate) struct UvSyncService {
    workers: OnceLock<std::io::Result<UvWorkerPool>>,
    results_sender: Sender<ScriptSyncResult>,
    results: Receiver<ScriptSyncResult>,
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
            progress: None,
            result: result_sender,
            cancellation: Some(cancellation),
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
                Ok(result) => return result.output,
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

    /// Returns a receiver for background synchronization results.
    ///
    /// The receiver can be cloned, but callers should designate one receiver as the consumer: a
    /// cloned crossbeam receiver distributes results rather than broadcasting them.
    pub(crate) fn results(&self) -> Receiver<ScriptSyncResult> {
        self.results.clone()
    }

    /// Admits one script synchronization and returns any completed work drained while waiting.
    ///
    /// Both the request and result queues are bounded. If the request queue is full, receiving
    /// completed work allows a worker blocked on the result queue to resume and accept another
    /// request. A blocking job can also free request capacity without publishing a background
    /// result, so scheduling selects over both directions rather than waiting on either in turn.
    pub(crate) fn schedule_one(
        &self,
        system: &dyn System,
        task: ScriptSyncTask,
        progress: Option<Box<dyn ScriptSyncProgress>>,
    ) -> Vec<ScriptSyncResult> {
        let workers = match self.worker_pool(system) {
            Ok(workers) => workers,
            Err(error) => {
                return vec![ScriptSyncResult {
                    task,
                    output: Err(error),
                    progress,
                }];
            }
        };

        let path = task.request.path().to_path_buf();
        let request = UvJob {
            task,
            progress,
            result: self.results_sender.clone(),
            cancellation: None,
            span: tracing::debug_span!(
                "sync_script_environment",
                script = %path,
            ),
        };
        let mut completed = Vec::new();

        loop {
            crossbeam::channel::select_biased! {
                recv(self.results) -> result => {
                    match result {
                        Ok(result) => completed.push(result),
                        Err(_) => {
                            completed.push(request.into_result(Err(worker_disconnected())));
                            return completed;
                        }
                    }
                }
                send(workers.requests, request) -> result => {
                    match result {
                        Ok(()) => {
                            tracing::debug!("Queued script synchronization for `{path}`");
                        }
                        Err(error) => {
                            completed.push(
                                error.into_inner().into_result(Err(worker_disconnected())),
                            );
                        }
                    }
                    return completed;
                }
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

impl Default for UvSyncService {
    fn default() -> Self {
        let (results_sender, results) = crossbeam::channel::bounded(MAX_QUEUED_UV_TASKS);
        Self {
            workers: OnceLock::new(),
            results_sender,
            results,
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
    progress: Option<Box<dyn ScriptSyncProgress>>,

    /// Receives this job's result.
    ///
    /// Blocking jobs use a private channel; background jobs use the service's shared result channel.
    result: Sender<ScriptSyncResult>,

    /// Lets a worker discard a queued blocking job after its Salsa operation is cancelled.
    cancellation: Option<UvJobCancellation>,
    span: tracing::Span,
}

impl UvJob {
    fn complete(self, output: std::io::Result<Output>) {
        let Self {
            task,
            progress,
            result,
            ..
        } = self;

        // The receiver disappears when the blocking caller is cancelled or the owning project is
        // dropped.
        let _ = result.send(ScriptSyncResult {
            task,
            output,
            progress,
        });
    }

    fn into_result(self, output: std::io::Result<Output>) -> ScriptSyncResult {
        ScriptSyncResult {
            task: self.task,
            output,
            progress: self.progress,
        }
    }
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
            if let Some(cancellation) = &job.cancellation
                && cancellation.is_cancelled()
            {
                tracing::debug!(
                    "Discarded cancelled script synchronization for `{}`",
                    job.task.request.path()
                );
                continue;
            }

            let output = self.execute(&job);
            job.complete(output);
        }
    }

    fn execute(&self, request: &UvJob) -> std::io::Result<Output> {
        let _span = request.span.enter();
        tracing::info!("Synchronizing script `{}`", request.task.request.path());

        let uv = self
            .uv
            .as_ref()
            .map_err(|error| uv_executable_error(*error))?;
        let target = MetadataTarget::Script {
            path: request.task.request.path(),
            python: request.task.request.python(),
        };

        let output = uv.execute(self.executor.as_ref(), target);

        if output.as_ref().is_ok_and(|output| output.status.success()) {
            tracing::debug!(
                "Successfully synchronized script `{}`",
                request.task.request.path()
            );
        } else {
            tracing::debug!(
                "Failed to synchronize script `{}`",
                request.task.request.path()
            );
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
    use std::time::Duration;

    use ruff_db::files::{File, system_path_to_file};
    use ruff_db::system::{
        DbWithWritableSystem, OsSystem, System as _, SystemPath, SystemPathBuf, TestSystem,
    };
    use salsa::{Cancelled, Database as _};
    use ty_static::EnvVars;

    use super::{
        ScriptSyncResult, ScriptSyncTask, UvJob, UvJobCancellation, UvSyncService, UvWorkerPool,
    };
    use crate::db::testing::TestDb;
    use crate::{
        CollectReporter, Db as _, ProgressReporter, ProjectDatabase, ProjectMetadata,
        ScriptSyncProgress, UseUv,
    };

    struct NoopScriptSyncProgress;

    impl ScriptSyncProgress for NoopScriptSyncProgress {}

    struct PanickingScriptSyncProgress;

    impl ScriptSyncProgress for PanickingScriptSyncProgress {}

    impl Drop for PanickingScriptSyncProgress {
        fn drop(&mut self) {
            panic!("progress failed");
        }
    }

    struct PanickingProgressReporter;

    impl ProgressReporter for PanickingProgressReporter {
        fn set_files(&mut self, _files: usize) {}

        fn for_script(
            &self,
            _db: &dyn crate::Db,
            _file: File,
        ) -> Option<Box<dyn ScriptSyncProgress>> {
            Some(Box::new(PanickingScriptSyncProgress))
        }

        fn report_checked_file(
            &self,
            _db: &ProjectDatabase,
            _file: File,
            _diagnostics: &[ruff_db::diagnostic::Diagnostic],
        ) {
        }

        fn report_diagnostics(
            &mut self,
            _db: &ProjectDatabase,
            _diagnostics: Vec<ruff_db::diagnostic::Diagnostic>,
        ) {
        }
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

    #[test]
    fn progress_panic_propagates_to_blocking_caller() -> anyhow::Result<()> {
        let root = SystemPath::new("/project").to_path_buf();
        let path = root.join("script.py");
        let metadata = ProjectMetadata::new("test", root).with_use_uv(UseUv::Scripts);
        let mut db = TestDb::new(metadata);
        db.write_file(&path, "# /// script\n# dependencies = []\n# ///\n")?;
        let file = system_path_to_file(&db, &path)?;
        let reporter = PanickingProgressReporter;

        let panic = std::panic::catch_unwind(AssertUnwindSafe(|| {
            db.script_environments()
                .ensure_environment_initialized(&db, file, &reporter);
        }));

        assert_eq!(
            panic
                .expect_err("finishing progress should panic on the checking thread")
                .downcast_ref::<&str>(),
            Some(&"progress failed")
        );

        Ok(())
    }

    #[test]
    fn database_write_cancels_pending_uv_initialization() -> anyhow::Result<()> {
        let root = SystemPath::new("/project").to_path_buf();
        let path = root.join("script.py");
        let metadata = ProjectMetadata::new("test", root).with_use_uv(UseUv::Scripts);
        let mut db = TestDb::new(metadata);
        db.write_file(&path, "# /// script\n# dependencies = []\n# ///\n")?;
        let file = system_path_to_file(&db, &path)?;
        let snapshot = db.clone();
        let environments = db.script_environments().clone();
        let checking_environments = environments.clone();

        let (request_sender, request_receiver) = crossbeam::channel::bounded(1);
        assert!(
            db.script_environments()
                .sync_service()
                .workers
                .set(Ok(UvWorkerPool {
                    requests: request_sender,
                }))
                .is_ok()
        );

        let checking = std::thread::spawn(move || {
            Cancelled::catch(AssertUnwindSafe(|| {
                checking_environments.ensure_environment_initialized(
                    &snapshot,
                    file,
                    &CollectReporter::default(),
                );
            }))
        });

        let _request = request_receiver.recv_timeout(Duration::from_secs(5))?;

        // Scheduling an asynchronous refresh must not wait for the checking thread's uv call.
        // It briefly observes the running synchronization and returns.
        let preparing_environments = environments.clone();
        let mut preparing_snapshot = db.clone();
        let (prepared_sender, prepared_receiver) = crossbeam::channel::bounded(1);
        let preparing = std::thread::spawn(move || {
            let result = Cancelled::catch(AssertUnwindSafe(|| {
                preparing_environments
                    .schedule_sync(&mut preparing_snapshot, file, &|_, _| None)
                    .is_empty()
            }));
            if matches!(result, Ok(true)) {
                let _ = prepared_sender.send(());
            }
            result
        });
        let prepared_without_waiting = prepared_receiver
            .recv_timeout(Duration::from_secs(5))
            .is_ok();

        db.trigger_cancellation();

        let result = checking
            .join()
            .map_err(|_| anyhow::anyhow!("checking thread panicked"))?;
        assert!(matches!(result, Err(Cancelled::PendingWrite)));
        let prepare_result = preparing
            .join()
            .map_err(|_| anyhow::anyhow!("preparing thread panicked"))?;
        assert!(prepared_without_waiting);
        assert!(matches!(prepare_result, Ok(true)));

        assert!(
            environments
                .schedule_sync(&mut db, file, &|_, _| None)
                .is_empty()
        );
        let _request = request_receiver.recv_timeout(Duration::from_secs(5))?;

        Ok(())
    }

    #[test]
    fn scheduling_makes_progress_when_shared_queue_contains_blocking_jobs() -> anyhow::Result<()> {
        let root = SystemPath::new("/project").to_path_buf();
        let first_path = root.join("first.py");
        let mut db = TestDb::new(ProjectMetadata::new("test", root));
        db.write_file(&first_path, "# /// script\n# dependencies = []\n# ///\n")?;
        let first_file = system_path_to_file(&db, &first_path)?;

        let (request_sender, request_receiver) = crossbeam::channel::bounded(1);
        let system = TestSystem::default();
        let service = UvSyncService::default();
        assert!(
            service
                .workers
                .set(Ok(UvWorkerPool {
                    requests: request_sender.clone(),
                }))
                .is_ok()
        );
        let task = || ScriptSyncTask::new(first_file, first_path.clone(), None, 2);

        let (blocking_result, _blocking_receiver) = crossbeam::channel::bounded(1);
        let (_cancellation_guard, cancellation) = UvJobCancellation::new();
        request_sender
            .send(UvJob {
                task: task(),
                progress: None,
                result: blocking_result,
                cancellation: Some(cancellation),
                span: tracing::Span::none(),
            })
            .map_err(|_| anyhow::anyhow!("test worker request queue disconnected"))?;

        service
            .results_sender
            .send(ScriptSyncResult {
                task: task(),
                output: Err(std::io::Error::other("test result")),
                progress: None,
            })
            .map_err(|_| anyhow::anyhow!("script result receiver disconnected"))?;
        let pending = task();
        let scheduling = std::thread::spawn(move || {
            service.schedule_one(&system, pending, Some(Box::new(NoopScriptSyncProgress)))
        });

        let _first_request = request_receiver.recv_timeout(Duration::from_secs(1))?;
        let completed = scheduling
            .join()
            .map_err(|_| anyhow::anyhow!("scheduling thread panicked"))?;
        assert_eq!(completed.len(), 1);
        assert_eq!(completed[0].task.file, first_file);

        let second_request = request_receiver.recv_timeout(Duration::from_secs(1))?;
        assert_eq!(
            second_request.task.request.path().as_str(),
            first_path.as_str()
        );
        assert!(second_request.progress.is_some());

        Ok(())
    }
}
