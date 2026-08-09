use lsp_server::ErrorCode;
use lsp_types::{
    DidChangeTextDocumentNotification, DidChangeTextDocumentParams, TextDocumentIdentifier,
    VersionedTextDocumentIdentifier,
};
use ty_project::Db as _;

use crate::server::Result;
use crate::server::api::LSPResult;
use crate::server::api::diagnostics::publish_diagnostics_if_needed;
use crate::server::api::traits::{NotificationHandler, SyncNotificationHandler};
use crate::session::Session;
use crate::session::client::Client;

pub(crate) struct DidChangeTextDocumentHandler;

impl NotificationHandler for DidChangeTextDocumentHandler {
    type NotificationType = DidChangeTextDocumentNotification;
}

impl SyncNotificationHandler for DidChangeTextDocumentHandler {
    fn run(
        session: &mut Session,
        client: &Client,
        params: DidChangeTextDocumentParams,
    ) -> Result<()> {
        let DidChangeTextDocumentParams {
            text_document:
                VersionedTextDocumentIdentifier {
                    text_document_identifier: TextDocumentIdentifier { uri },
                    version,
                },
            content_changes,
        } = params;

        let mut document = session
            .document_handle(&uri)
            .with_failure_code(ErrorCode::InternalError)?;

        document
            .update_text_document(session, content_changes, version)
            .with_failure_code(ErrorCode::InternalError)?;

        let db = session.project_db_mut(document.notebook_or_file_path());
        if let Some(file) = document.notebook_or_file(db) {
            let environments = db.script_environments().clone();
            environments.ensure_environment_available(db, file);
        }

        publish_diagnostics_if_needed(&document, session, client);

        Ok(())
    }
}
