//! Integrates uv-managed script environments with incremental checking.
//!
//! The metadata returned by uv determines a script's Python version and module search paths. We
//! store it in a Salsa input so changes invalidate the semantic queries that depend on it.
//!
//! Synchronizing an environment may create a virtual environment or install packages, so it can
//! take long enough to affect interactive latency. A one-shot CLI check waits for synchronization
//! because it must produce one complete result.
//!
//! CLI watch mode starts synchronization after applying filesystem changes. It delays the next
//! check until all pending synchronizations finish, so the check uses environments matching the
//! changed scripts. If more changes arrive while uv is running, only the latest requested
//! environment is synchronized next.

use std::hash::Hasher;
use std::sync::Arc;
use std::time::Duration;

use crossbeam::channel::Receiver;
use parking_lot::{Condvar, Mutex, MutexGuard};
use ruff_cache::{CacheKey, CacheKeyHasher};
use ruff_db::FxDashMap;
use ruff_db::files::{File, Files};
use ruff_db::system::SystemPathBuf;
use salsa::Setter;
use ty_static::EnvVars;

use super::script_tag;
use crate::metadata::uv::{
    ScriptEnvironmentCacheKey, ScriptSyncRequest, ScriptSyncResult, ScriptSyncTask, Uv, UvMetadata,
    UvSyncService,
};
use crate::{Db, ProgressReporter, ScriptSyncProgress};

const CANCELLATION_CHECK_INTERVAL: Duration = Duration::from_millis(1);

/// Returns the script environment input for `file`.
///
/// Project checks call [`ScriptEnvironments::ensure_environment_initialized`] before entering
/// semantic queries. CLI watch mode calls [`ScriptEnvironments::schedule_sync`] after filesystem
/// changes, which creates the input before submitting the background work. A missing input means
/// that semantic analysis started without either path preparing the script first.
pub(super) fn script_environment(db: &dyn Db, file: File) -> Option<ScriptEnvironment> {
    db.script_environments().environment(db, file)
}

/// Manages uv environments for standalone scripts.
#[derive(Clone, Default)]
pub struct ScriptEnvironments {
    inner: Arc<ScriptEnvironmentsInner>,
}

impl ScriptEnvironments {
    /// Returns completed background synchronizations.
    pub fn sync_results(&self) -> Receiver<ScriptSyncResult> {
        self.inner.sync_service.results()
    }

    /// Initializes `file`'s environment before a project check analyzes it.
    ///
    /// Project checks can discover scripts while iterating their files, so they initialize those
    /// scripts synchronously. This may invoke uv and creates the [`ScriptEnvironment`] input that
    /// semantic queries depend on.
    ///
    /// Concurrent callers wait for the initial environment creation to finish.
    /// If blocking initialization is cancelled or otherwise unwinds, the environment remains
    /// uninitialized and waiters are woken so a caller can retry.
    pub(crate) fn ensure_environment_initialized(
        &self,
        db: &dyn Db,
        file: File,
        reporter: &dyn ProgressReporter,
    ) {
        if !script_integration_enabled(db) {
            return;
        }

        let Some(task) = script_sync_task(db, file) else {
            return;
        };
        let entry = self.entry(file);

        let mut state = entry.state.lock();
        // An initializer that is cancelled or otherwise unwinds restores the state to `Vacant`.
        // Re-check the state after waiting so this caller can take over the abandoned work.
        loop {
            match &*state {
                ScriptEnvironmentEntryState::Initializing { .. } => {
                    state = entry.wait_until_initialized(db, state);
                }
                ScriptEnvironmentEntryState::Current { .. }
                | ScriptEnvironmentEntryState::Synchronizing { .. } => return,
                ScriptEnvironmentEntryState::Vacant => {
                    let cache_key = task.request.cache_key();
                    *state = ScriptEnvironmentEntryState::Initializing {
                        request: task.request.clone(),
                    };
                    let claim = InitializationClaim::new(&entry);
                    drop(state);

                    db.unwind_if_revision_cancelled();
                    tracing::debug!(
                        "Initializing script environment for `{}`",
                        task.request.path()
                    );

                    let output = {
                        let _progress = reporter.for_script(db, file);
                        self.inner.sync_service.run(db, task)
                    };

                    let (uv_metadata, initialization_error) =
                        script_environment_metadata(db, output);
                    let environment = ScriptEnvironment::new(
                        db,
                        Some(cache_key),
                        uv_metadata,
                        initialization_error,
                    );
                    claim.complete(environment);
                    return;
                }
            }
        }
    }

    /// Synchronizes `file` in the background when its requested environment is not current.
    ///
    /// The progress factory is called only when a new worker task will be submitted. If another
    /// request is already running, this records only the latest replacement; completing the
    /// running request schedules that replacement with the same progress guard.
    ///
    /// Returns the files whose completed environment results were applied while waiting for worker
    /// capacity.
    pub fn schedule_sync(
        &self,
        db: &mut dyn Db,
        file: File,
        make_progress: &dyn Fn(&dyn Db, File) -> Option<Box<dyn ScriptSyncProgress>>,
    ) -> Vec<File> {
        let Some(PendingSync { task, progress }) = self.begin_sync(db, file, make_progress) else {
            return Vec::new();
        };

        let completed = self
            .inner
            .sync_service
            .schedule_one(db.system(), task, progress);
        self.complete_results(db, completed)
    }

    /// Applies a synchronization result and schedules any superseding work.
    ///
    /// Returns the scripts whose environments changed. Scheduling replacement work may drain
    /// results for other scripts while waiting for queue capacity, so one completion can update
    /// multiple scripts.
    pub fn complete_sync(&self, db: &mut dyn Db, result: ScriptSyncResult) -> Vec<File> {
        self.complete_results(db, vec![result])
    }

    /// Returns whether an environment synchronization is in progress.
    pub fn has_pending_synchronizations(&self) -> bool {
        self.inner.by_file.iter().any(|entry| {
            matches!(
                *entry.state.lock(),
                ScriptEnvironmentEntryState::Initializing { .. }
                    | ScriptEnvironmentEntryState::Synchronizing { .. }
            )
        })
    }

    /// Returns whether an environment input exists for `file`.
    pub fn contains(&self, file: File) -> bool {
        self.existing_entry(file)
            .is_some_and(|entry| entry.state.lock().environment().is_some())
    }

    /// Schedules synchronization for every known script whose environment may be stale.
    ///
    /// This assumes that no semantic check is running and can add another script environment while
    /// the method snapshots the known files. The CLI watch loop satisfies that requirement by
    /// calling this immediately after [`ProjectDatabase::apply_changes`], which cancels and waits
    /// for the active check.
    ///
    /// A background uv job may still finish after this method returns. If a changed script is
    /// already synchronizing, preparing it records the latest request as its replacement; the main
    /// loop handles the earlier result normally before scheduling that replacement.
    ///
    /// [`ProjectDatabase::apply_changes`]: crate::ProjectDatabase::apply_changes
    pub fn schedule_resync_all(
        &self,
        db: &mut dyn Db,
        make_progress: &dyn Fn(&dyn Db, File) -> Option<Box<dyn ScriptSyncProgress>>,
    ) -> Vec<File> {
        // Drop the map's shard guards before scheduling. `schedule_sync` acquires each entry's
        // state lock and may wait for worker capacity.
        let files: Vec<_> = self
            .inner
            .by_file
            .iter()
            .map(|entry| *entry.key())
            .collect();

        let mut changed_files = Vec::new();
        for file in files {
            changed_files.extend(self.schedule_sync(db, file, make_progress));
        }
        changed_files
    }

    fn environment(&self, db: &dyn Db, file: File) -> Option<ScriptEnvironment> {
        if !script_integration_enabled(db) || file.path(db).as_system_path().is_none() {
            return None;
        }

        let Some(entry) = self.existing_entry(file) else {
            panic!("script environment was not initialized before semantic analysis");
        };
        let state = entry.state.lock();
        // Project checks and CLI watch mode prepare the input before entering semantic queries, so
        // this normally returns immediately. It waits only when two checks race to perform the
        // first blocking initialization.
        let state = entry.wait_until_initialized(db, state);
        let environment = state.environment();
        assert!(
            environment.is_some(),
            "script environment was not initialized before semantic analysis"
        );
        environment
    }

    fn complete_results(
        &self,
        db: &mut dyn Db,
        mut pending_results: Vec<ScriptSyncResult>,
    ) -> Vec<File> {
        let mut changed_scripts = Vec::new();

        while let Some(result) = pending_results.pop() {
            match self.complete_one(db, result) {
                SyncCompletion::Applied(file) => changed_scripts.push(file),
                SyncCompletion::Superseded(PendingSync { task, progress }) => {
                    pending_results.extend(self.inner.sync_service.schedule_one(
                        db.system(),
                        task,
                        progress,
                    ));
                }
            }
        }

        changed_scripts
    }

    fn begin_sync(
        &self,
        db: &mut dyn Db,
        file: File,
        make_progress: &dyn Fn(&dyn Db, File) -> Option<Box<dyn ScriptSyncProgress>>,
    ) -> Option<PendingSync> {
        if !script_integration_enabled(db) {
            return None;
        }

        let task = script_sync_task(db, file)?;
        let request = task.request.clone();
        let entry: Arc<ScriptEnvironmentEntry> = self.entry(file);
        let mut state = entry.state.lock();

        let environment = match &mut *state {
            ScriptEnvironmentEntryState::Initializing { request: running } => {
                // A blocking check already owns the first synchronization. All inputs to the
                // cache key belong to its Salsa snapshot, so a different key would require
                // cancellation of that snapshot before this request can run.
                debug_assert_eq!(running.cache_key(), request.cache_key());
                tracing::trace!(
                    "Script environment synchronization for `{}` is already running",
                    request.path()
                );
                return None;
            }
            ScriptEnvironmentEntryState::Vacant => ScriptEnvironment::new(db, None, None, None),
            ScriptEnvironmentEntryState::Current { environment } => {
                let already_synchronized =
                    environment.synchronized_cache_key(db) == Some(request.cache_key());

                if already_synchronized {
                    tracing::trace!(
                        "Script environment for `{}` is already synchronized",
                        request.path()
                    );
                    return None;
                }
                *environment
            }
            ScriptEnvironmentEntryState::Synchronizing { sync, .. } => {
                if !sync.replace_queued(request) {
                    tracing::trace!(
                        "Script environment synchronization for `{}` is already requested",
                        task.request.path()
                    );
                } else {
                    tracing::debug!(
                        "Updated pending script environment synchronization for `{}`",
                        task.request.path()
                    );
                }

                return None;
            }
        };

        let progress = make_progress(db, file);
        *state = ScriptEnvironmentEntryState::Synchronizing {
            environment,
            sync: InFlightSync::new(request),
        };

        tracing::debug!(
            "Requested script environment synchronization for `{}`",
            task.request.path()
        );

        Some(PendingSync { task, progress })
    }

    /// Applies one worker result or returns the superseding synchronization to schedule.
    ///
    /// An applied result identifies the script whose diagnostics must be recomputed. A result
    /// superseded before application carries the replacement task and preserves its progress
    /// guard.
    fn complete_one(&self, db: &mut dyn Db, result: ScriptSyncResult) -> SyncCompletion {
        let ScriptSyncResult {
            task,
            output,
            progress,
        } = result;
        let file = task.file;
        let request = task.request;
        let Some(entry) = self.existing_entry(file) else {
            panic!(
                "received a synchronization result for unknown script `{}`",
                request.path(),
            );
        };

        let completion = {
            let mut state = entry.state.lock();
            state.begin_completion(&request)
        };
        let environment = match completion {
            Some(CompletionAction::Apply(environment)) => environment,
            Some(CompletionAction::Schedule(next)) => {
                tracing::debug!(
                    "Discarded superseded script environment synchronization result for `{}`",
                    request.path()
                );
                return SyncCompletion::Superseded(PendingSync {
                    task: ScriptSyncTask {
                        file,
                        request: next,
                    },
                    progress,
                });
            }
            None => panic!(
                "synchronization result for `{}` does not match any task currently in flight",
                request.path(),
            ),
        };

        apply_sync_result(db, environment, &request, output);

        let mut state = entry.state.lock();
        state.finish_completion(&request);
        SyncCompletion::Applied(file)
    }

    fn existing_entry(&self, file: File) -> Option<Arc<ScriptEnvironmentEntry>> {
        let entry = self.inner.by_file.get(&file)?;
        Some(Arc::clone(entry.value()))
    }

    fn entry(&self, file: File) -> Arc<ScriptEnvironmentEntry> {
        // Drop the map's shard guard before initializing an entry so unrelated scripts can
        // initialize concurrently even when their files occupy the same map shard.
        Arc::clone(self.inner.by_file.entry(file).or_default().value())
    }

    #[cfg(test)]
    pub(crate) fn sync_service(&self) -> &UvSyncService {
        &self.inner.sync_service
    }
}

impl std::panic::RefUnwindSafe for ScriptEnvironments {}

/// The Salsa input that supplies a standalone script's environment.
#[salsa::input(heap_size=ruff_memory_usage::heap_size)]
#[derive(Debug)]
pub(super) struct ScriptEnvironment {
    /// The cache key for the last completed `uv metadata` synchronization.
    ///
    /// `None` means that no synchronization has completed yet. CLI watch mode creates the input
    /// with this field unset before scheduling the first synchronization.
    #[returns(copy)]
    synchronized_cache_key: Option<ScriptEnvironmentCacheKey>,

    /// The metadata for the most recently completed `uv metadata` call (parsed).
    ///
    /// `None` means that the first synchronization is still pending or that the most recent
    /// synchronization failed; `initialization_error` distinguishes the failure case. A successful
    /// synchronization stores `Some` even when uv reports no environment for the script.
    #[returns(as_ref)]
    pub(super) uv_metadata: Option<UvMetadata>,

    /// The error message when `uv metadata` failed.
    ///
    /// `None` if the metadata sync hasn't completed yet or the most recent sync was successful.
    #[returns(as_deref)]
    pub(super) initialization_error: Option<Box<str>>,
}

#[derive(Default)]
struct ScriptEnvironmentsInner {
    by_file: FxDashMap<File, Arc<ScriptEnvironmentEntry>>,
    sync_service: UvSyncService,
}

#[derive(Default)]
struct ScriptEnvironmentEntry {
    state: Mutex<ScriptEnvironmentEntryState>,

    /// Wakes callers when blocking initialization completes or is abandoned.
    initialized: Condvar,
}

impl ScriptEnvironmentEntry {
    /// Waits for a blocking initial synchronization to finish.
    fn wait_until_initialized<'entry>(
        &'entry self,
        db: &dyn Db,
        mut state: MutexGuard<'entry, ScriptEnvironmentEntryState>,
    ) -> MutexGuard<'entry, ScriptEnvironmentEntryState> {
        loop {
            // Database updates cancel existing snapshots and wait for them to unwind. Poll for
            // cancellation so this waiting snapshot cannot prevent the update from completing.
            db.unwind_if_revision_cancelled();
            if !matches!(*state, ScriptEnvironmentEntryState::Initializing { .. }) {
                return state;
            }

            if self
                .initialized
                .wait_for(&mut state, CANCELLATION_CHECK_INTERVAL)
                .timed_out()
            {
                db.unwind_if_revision_cancelled();
                drop(state);

                // Let Rayon run another queued task before polling the initialization state again.
                rayon::yield_now();
                state = self.state.lock();
            }
        }
    }
}

/// Coordinates a script's Salsa environment input with its synchronization work.
///
/// The state belongs to one project database because `File` and `ScriptEnvironment` are Salsa
/// handles from that database.
#[derive(Default)]
enum ScriptEnvironmentEntryState {
    /// No environment input exists and no synchronization owns this entry.
    #[default]
    Vacant,

    /// A blocking check owns the script's initial synchronization.
    Initializing {
        /// The request owned by the blocking check.
        request: ScriptSyncRequest,
    },

    /// No synchronization is running, and semantic queries use the stored environment input.
    /// A completed blocking or background synchronization transitions the entry to this state.
    Current {
        /// The environment input read by semantic queries.
        environment: ScriptEnvironment,
    },

    /// An environment input exists and a background synchronization is running.
    ///
    /// The current input remains available until the synchronization completes. Its synchronized
    /// cache key is absent if this is the first synchronization.
    Synchronizing {
        /// The current environment input, updated in place when synchronization completes.
        environment: ScriptEnvironment,

        /// The running request and latest queued replacement.
        sync: InFlightSync,
    },
}

impl ScriptEnvironmentEntryState {
    fn environment(&self) -> Option<ScriptEnvironment> {
        match self {
            Self::Current { environment } | Self::Synchronizing { environment, .. } => {
                Some(*environment)
            }
            Self::Vacant | Self::Initializing { .. } => None,
        }
    }

    /// Claims a matching result and decides whether to apply or supersede it.
    fn begin_completion(&mut self, request: &ScriptSyncRequest) -> Option<CompletionAction> {
        let Self::Synchronizing { environment, sync } = self else {
            return None;
        };
        if !sync.is_running(request) {
            return None;
        }

        let Some(next) = sync.queued.take() else {
            return Some(CompletionAction::Apply(*environment));
        };

        // uv updates the path-keyed script environment in place. Even if `next` matches the
        // previously synchronized cache key, the superseded command may have changed that
        // environment on disk, so `next` must run again to restore it.
        sync.running = next.clone();
        Some(CompletionAction::Schedule(next))
    }

    /// Marks an applied result as current.
    fn finish_completion(&mut self, request: &ScriptSyncRequest) {
        let Self::Synchronizing { environment, sync } = self else {
            panic!(
                "synchronization for `{}` stopped while applying its result",
                request.path()
            );
        };
        assert!(
            sync.is_running(request),
            "a different synchronization started while applying the result for `{}`",
            request.path()
        );
        assert!(
            sync.queued.is_none(),
            "a synchronization was prepared while applying the result for `{}`",
            request.path()
        );

        *self = Self::Current {
            environment: *environment,
        };
    }
}

/// A running synchronization and the latest replacement requested while it runs.
struct InFlightSync {
    running: ScriptSyncRequest,
    queued: Option<ScriptSyncRequest>,
}

impl InFlightSync {
    fn new(running: ScriptSyncRequest) -> Self {
        Self {
            running,
            queued: None,
        }
    }

    fn is_running(&self, request: &ScriptSyncRequest) -> bool {
        self.running.cache_key() == request.cache_key()
    }

    /// Records `request` as the desired synchronization.
    ///
    /// Returning to the running request removes a previously queued replacement.
    fn replace_queued(&mut self, request: ScriptSyncRequest) -> bool {
        let desired = self.queued.as_ref().unwrap_or(&self.running);
        if desired.cache_key() == request.cache_key() {
            return false;
        }

        self.queued = if self.running.cache_key() == request.cache_key() {
            None
        } else {
            Some(request)
        };
        true
    }
}

struct PendingSync {
    task: ScriptSyncTask,
    progress: Option<Box<dyn ScriptSyncProgress>>,
}

enum SyncCompletion {
    Applied(File),
    Superseded(PendingSync),
}

enum CompletionAction {
    Apply(ScriptEnvironment),
    Schedule(ScriptSyncRequest),
}

/// Owns responsibility for finishing a script's blocking initial synchronization.
///
/// The initializer marks the entry as `Initializing`, creates this claim, and then releases the
/// state lock while uv runs. Completing the claim stores the initialized environment and wakes
/// every waiter. If the initializer returns early or unwinds, dropping the claim restores the
/// entry to `Vacant` and wakes the waiters so another caller can retry.
#[must_use]
struct InitializationClaim<'entry>(Option<&'entry ScriptEnvironmentEntry>);

impl<'entry> InitializationClaim<'entry> {
    fn new(entry: &'entry ScriptEnvironmentEntry) -> Self {
        Self(Some(entry))
    }

    fn complete(mut self, environment: ScriptEnvironment) {
        self.finish(ScriptEnvironmentEntryState::Current { environment });
    }

    fn finish(&mut self, next: ScriptEnvironmentEntryState) {
        if let Some(entry) = self.0.take() {
            let mut state = entry.state.lock();
            debug_assert!(matches!(
                *state,
                ScriptEnvironmentEntryState::Initializing { .. }
            ));
            *state = next;
            drop(state);
            entry.initialized.notify_all();
        }
    }
}

impl Drop for InitializationClaim<'_> {
    fn drop(&mut self) {
        self.finish(ScriptEnvironmentEntryState::Vacant);
    }
}

fn apply_sync_result(
    db: &mut dyn Db,
    environment: ScriptEnvironment,
    request: &ScriptSyncRequest,
    output: std::io::Result<std::process::Output>,
) {
    let previous_root = environment
        .uv_metadata(db)
        .and_then(UvMetadata::environment)
        .map(ToOwned::to_owned);
    let (uv_metadata, initialization_error) = script_environment_metadata(db, output);

    if let Some(root) = previous_root {
        // uv may change installed packages without changing the environment path.
        // FIXME: This only refreshes files that ty already knows about. Watch script environments
        // and route their changes through `ProjectDatabase::apply_changes` instead.
        Files::sync_all_recursive(db, [root]);
    }

    environment.set_uv_metadata(db).to(uv_metadata);
    environment
        .set_initialization_error(db)
        .to(initialization_error);
    // Publish the cache key last because it identifies the metadata and error as the completed
    // result for this script source.
    environment
        .set_synchronized_cache_key(db)
        .to(Some(request.cache_key()));

    tracing::debug!(
        "Updated script environment metadata for `{}`",
        request.path()
    );
}

fn script_environment_metadata(
    db: &dyn Db,
    output: std::io::Result<std::process::Output>,
) -> (Option<UvMetadata>, Option<Box<str>>) {
    match Uv::parse_metadata_output(db.system(), output) {
        Ok(metadata) => (Some(metadata), None),
        Err(error) => (None, Some(error.to_string().into_boxed_str())),
    }
}

fn script_integration_enabled(db: &dyn Db) -> bool {
    matches!(
        db.system().env_var(EnvVars::TY_UV).as_deref(),
        Ok("1" | "true" | "scripts")
    )
}

fn script_sync_task(db: &dyn Db, file: File) -> Option<ScriptSyncTask> {
    let path = file.path(db).as_system_path()?;
    let tag = script_tag(db, file)?;
    let python = script_python(db);

    // No reusable parsed metadata exists before environment synchronization. Hashing the extracted
    // text avoids parsing it a second time; formatting-only metadata changes may therefore invoke uv.
    let mut hasher = CacheKeyHasher::new();
    tag.metadata().cache_key(&mut hasher);
    python.cache_key(&mut hasher);

    Some(ScriptSyncTask::new(
        file,
        path.to_path_buf(),
        python,
        hasher.finish(),
    ))
}

fn script_python(db: &dyn Db) -> Option<SystemPathBuf> {
    let metadata = db.project().metadata(db);

    metadata
        .override_options
        .as_deref()
        .and_then(|options| options.environment.as_ref())
        .and_then(|environment| environment.python.as_ref())
        .map(|python| python.absolute(metadata.root(), db.system()))
}

#[cfg(test)]
mod tests {
    use std::io;
    use std::panic::AssertUnwindSafe;
    use std::sync::Arc;
    use std::time::Duration;

    use anyhow::Context;
    use ruff_db::files::{File, system_path_to_file};
    use ruff_db::system::{DbWithWritableSystem, SystemPath};
    use salsa::{Cancelled, Database as _};
    use ty_static::EnvVars;

    use super::{
        InitializationClaim, PendingSync, ScriptEnvironmentEntryState, ScriptEnvironments,
        ScriptSyncResult, ScriptSyncTask, SyncCompletion, script_sync_task,
    };
    use crate::db::testing::TestDb;
    use crate::{Db as _, ProjectMetadata, ScriptSyncProgress};

    struct NoopScriptSyncProgress;

    impl ScriptSyncProgress for NoopScriptSyncProgress {}

    fn begin_sync(
        environments: &ScriptEnvironments,
        db: &mut TestDb,
        file: File,
    ) -> Option<ScriptSyncTask> {
        environments
            .begin_sync(db, file, &|_, _| None)
            .map(|pending| pending.task)
    }

    #[test]
    fn superseded_synchronization_only_applies_the_latest_cache_key() -> anyhow::Result<()> {
        let root = SystemPath::new("/project").to_path_buf();
        let path = root.join("script.py");
        let mut db = TestDb::new(ProjectMetadata::new("test", root));
        db.writable_system().set_env_var(EnvVars::TY_UV, "scripts");
        db.write_file(&path, "# /// script\n# dependencies = []\n# ///\n")?;
        let file = system_path_to_file(&db, &path)?;
        let environments: ScriptEnvironments = db.script_environments().clone();

        assert!(!environments.has_pending_synchronizations());

        let first = begin_sync(&environments, &mut db, file)
            .context("the initial script metadata should be synchronized")?;
        assert!(environments.has_pending_synchronizations());
        assert!(begin_sync(&environments, &mut db, file).is_none());

        db.write_file(&path, "# /// script\n# dependencies = [\"anyio\"]\n# ///\n")?;
        assert!(begin_sync(&environments, &mut db, file).is_none());
        let second_cache_key = script_sync_task(&db, file)
            .context("the script should have synchronization work")?
            .request
            .cache_key();

        // Source visible to Salsa can change without another synchronization request, as it does
        // for unsaved LSP edits. Reschedule the explicitly requested cache key, not that newer
        // source.
        db.write_file(&path, "# /// script\n# dependencies = [\"idna\"]\n# ///\n")?;
        let third_cache_key = script_sync_task(&db, file)
            .context("the script should have synchronization work")?
            .request
            .cache_key();
        assert_ne!(second_cache_key, third_cache_key);

        let first = ScriptSyncResult {
            task: first,
            output: Err(io::Error::other("uv failed")),
            progress: Some(Box::new(NoopScriptSyncProgress)),
        };
        let SyncCompletion::Superseded(PendingSync {
            task: second,
            progress,
        }) = environments.complete_one(&mut db, first)
        else {
            panic!("the stale synchronization should be superseded");
        };
        assert!(environments.has_pending_synchronizations());
        assert!(progress.is_some());
        assert_eq!(second.request.cache_key(), second_cache_key);

        let second = ScriptSyncResult {
            task: second,
            output: Err(io::Error::other("uv failed")),
            progress,
        };
        assert!(matches!(
            environments.complete_one(&mut db, second),
            SyncCompletion::Applied(changed) if changed == file
        ));
        assert!(!environments.has_pending_synchronizations());
        let third = begin_sync(&environments, &mut db, file)
            .context("the newer source should synchronize when explicitly requested")?;
        assert!(environments.has_pending_synchronizations());
        assert_eq!(third.request.cache_key(), third_cache_key);
        assert!(matches!(
            environments.complete_one(
                &mut db,
                ScriptSyncResult {
                    task: third,
                    output: Err(io::Error::other("uv failed")),
                    progress: None,
                },
            ),
            SyncCompletion::Applied(changed) if changed == file
        ));
        assert!(!environments.has_pending_synchronizations());
        assert!(begin_sync(&environments, &mut db, file).is_none());

        Ok(())
    }

    #[test]
    fn returning_to_current_environment_resynchronizes() -> anyhow::Result<()> {
        let root = SystemPath::new("/project").to_path_buf();
        let path = root.join("script.py");
        let initial_source = "# /// script\n# dependencies = []\n# ///\n";
        let mut db = TestDb::new(ProjectMetadata::new("test", root));
        db.writable_system().set_env_var(EnvVars::TY_UV, "scripts");
        db.write_file(&path, initial_source)?;
        let file = system_path_to_file(&db, &path)?;
        let environments = db.script_environments().clone();

        let initial = begin_sync(&environments, &mut db, file)
            .context("the initial environment should be synchronized")?;
        let initial_cache_key = initial.request.cache_key();
        assert!(matches!(
            environments.complete_one(
                &mut db,
                ScriptSyncResult {
                    task: initial,
                    output: Err(io::Error::other("initial synchronization failed")),
                    progress: None,
                },
            ),
            SyncCompletion::Applied(changed) if changed == file
        ));

        db.write_file(&path, "# /// script\n# dependencies = [\"anyio\"]\n# ///\n")?;
        let superseded = begin_sync(&environments, &mut db, file)
            .context("the changed environment should be synchronized")?;
        assert_ne!(superseded.request.cache_key(), initial_cache_key);

        db.write_file(&path, initial_source)?;
        assert!(begin_sync(&environments, &mut db, file).is_none());

        let SyncCompletion::Superseded(PendingSync { task, progress }) = environments.complete_one(
            &mut db,
            ScriptSyncResult {
                task: superseded,
                output: Err(io::Error::other("superseded synchronization failed")),
                progress: None,
            },
        ) else {
            panic!("the current environment should be restored");
        };
        assert_eq!(task.request.cache_key(), initial_cache_key);

        assert!(matches!(
            environments.complete_one(
                &mut db,
                ScriptSyncResult {
                    task,
                    output: Err(io::Error::other("restoration failed")),
                    progress,
                },
            ),
            SyncCompletion::Applied(changed) if changed == file
        ));
        assert!(!environments.has_pending_synchronizations());

        Ok(())
    }

    #[test]
    fn salsa_cancellation_interrupts_script_environment_wait() -> anyhow::Result<()> {
        let root = SystemPath::new("/project").to_path_buf();
        let path = root.join("script.py");
        let mut db = TestDb::new(ProjectMetadata::new("test", root));
        db.writable_system().set_env_var(EnvVars::TY_UV, "scripts");
        db.write_file(&path, "# /// script\n# dependencies = []\n# ///\n")?;
        let file = system_path_to_file(&db, &path)?;
        let snapshot = db.clone();
        let environments = db.script_environments().clone();
        let entry = environments.entry(file);
        let request = script_sync_task(&db, file)
            .context("the script should have synchronization work")?
            .request;
        *entry.state.lock() = ScriptEnvironmentEntryState::Initializing { request };
        let claim = InitializationClaim::new(&entry);
        let (ready_sender, ready_receiver) = crossbeam::channel::bounded(1);
        let waiting_entry = Arc::clone(&entry);

        let waiter = std::thread::spawn(move || {
            Cancelled::catch(AssertUnwindSafe(|| {
                let state = waiting_entry.state.lock();
                let _ = ready_sender.try_send(());
                let state = waiting_entry.wait_until_initialized(&snapshot, state);
                drop(state);
            }))
        });

        ready_receiver.recv_timeout(Duration::from_secs(1))?;
        db.trigger_cancellation();
        drop(claim);

        let result = waiter
            .join()
            .map_err(|_| anyhow::anyhow!("synchronization waiter panicked"))?;
        assert!(matches!(result, Err(Cancelled::PendingWrite)));
        assert!(matches!(
            *entry.state.lock(),
            ScriptEnvironmentEntryState::Vacant
        ));

        let task = begin_sync(&environments, &mut db, file)
            .context("the abandoned synchronization should be retried")?;
        assert_eq!(task.file, file);

        Ok(())
    }
}
