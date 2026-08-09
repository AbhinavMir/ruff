//! Integrates uv-managed script environments with incremental checking.
//!
//! The metadata returned by uv determines a script's Python version and module search paths. We
//! store it in a Salsa input so changes invalidate the semantic queries that depend on it.
//!
//! Synchronizing an environment may create a virtual environment or install packages, so it can
//! take long enough to affect interactive latency. A one-shot CLI check waits for synchronization
//! because it must produce one complete result.

use std::sync::{Arc, OnceLock};

use ruff_db::FxDashMap;
use ruff_db::files::File;
use ruff_db::system::SystemPathBuf;
use ty_static::EnvVars;

use super::script_tag;
use crate::metadata::uv::{ScriptSyncTask, Uv, UvMetadata, UvSyncService};
use crate::{Db, ProgressReporter};

/// Returns the script environment input for `file`.
///
/// Project checks call [`ScriptEnvironments::ensure_environment_initialized`] before entering
/// semantic queries. That operation creates the input and waits for any concurrent initializer, so
/// this lookup is immediate during semantic analysis. A missing input means that the project check
/// reached semantic analysis without initializing the script first.
pub(super) fn script_environment(db: &dyn Db, file: File) -> Option<ScriptEnvironment> {
    db.script_environments().environment(db, file)
}

/// Manages uv environments for standalone scripts.
#[derive(Clone, Default)]
pub struct ScriptEnvironments {
    inner: Arc<ScriptEnvironmentsInner>,
}

impl ScriptEnvironments {
    /// Initializes `file`'s environment before a project check analyzes it.
    ///
    /// Project checks can discover scripts while iterating their files, so they initialize those
    /// scripts synchronously. This may invoke uv and creates the [`ScriptEnvironment`] input that
    /// semantic queries depend on.
    ///
    /// Concurrent callers wait for the initial environment creation to finish.
    pub(crate) fn ensure_environment_initialized(
        &self,
        db: &dyn Db,
        file: File,
        reporter: &dyn ProgressReporter,
    ) {
        if !script_integration_enabled(db) || script_tag(db, file).is_none() {
            return;
        }

        let Some(path) = file.path(db).as_system_path() else {
            return;
        };

        self.get_or_init_with(file, || {
            let python = script_python(db);

            db.unwind_if_revision_cancelled();
            let _progress = reporter.for_script(db, file);

            let task = ScriptSyncTask {
                path: path.to_path_buf(),
                python,
            };
            let output = self.inner.sync_service.run(db, task);

            let (uv_metadata, initialization_error) = script_environment_metadata(db, output);
            ScriptEnvironment::new(db, uv_metadata, initialization_error)
        });
    }

    fn environment(&self, db: &dyn Db, file: File) -> Option<ScriptEnvironment> {
        if !script_integration_enabled(db) || file.path(db).as_system_path().is_none() {
            return None;
        }

        let Some(shared_environment) = self.inner.by_file.get(&file) else {
            panic!("script environment was not initialized before semantic analysis");
        };
        let environment = shared_environment.value().get().copied();
        assert!(
            environment.is_some(),
            "script environment was not initialized before semantic analysis"
        );
        environment
    }

    fn get_or_init_with(
        &self,
        file: File,
        initialize: impl FnOnce() -> ScriptEnvironment,
    ) -> ScriptEnvironment {
        // Drop the map's shard guard before invoking uv so unrelated scripts sharing that shard
        // can initialize concurrently.
        let environment = Arc::clone(self.inner.by_file.entry(file).or_default().value());
        *environment.get_or_init(initialize)
    }
}

impl std::panic::RefUnwindSafe for ScriptEnvironments {}

/// Stable input recording script-specific uv metadata or an initialization failure.
#[salsa::input(heap_size=ruff_memory_usage::heap_size)]
pub(super) struct ScriptEnvironment {
    #[returns(as_ref)]
    pub(super) uv_metadata: Option<UvMetadata>,

    #[returns(as_deref)]
    pub(super) initialization_error: Option<Box<str>>,
}

#[derive(Default)]
struct ScriptEnvironmentsInner {
    by_file: FxDashMap<File, Arc<OnceLock<ScriptEnvironment>>>,
    sync_service: UvSyncService,
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

fn script_python(db: &dyn Db) -> Option<SystemPathBuf> {
    let metadata = db.project().metadata(db);

    metadata
        .override_options
        .as_deref()
        .and_then(|options| options.environment.as_ref())
        .and_then(|environment| environment.python.as_ref())
        .map(|python| python.absolute(metadata.root(), db.system()))
}
