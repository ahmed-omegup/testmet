use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::Mutex;

/// A batch holds mapping from document id -> waiting query ids.
#[derive(Debug, Default)]
pub struct RetrievalBatch {
    pub waiting: HashMap<i64, Vec<u32>>, // doc_id -> queries waiting
}

impl RetrievalBatch {
    fn add(&mut self, doc_id: i64, query_id: u32) {
        self.waiting.entry(doc_id).or_insert_with(Vec::new).push(query_id);
    }
    fn take(&mut self, doc_id: i64) -> Vec<u32> {
        self.waiting.remove(&doc_id).unwrap_or_default()
    }
}

#[derive(Debug)]
struct Inner {
    processing: RetrievalBatch,
    registration: RetrievalBatch,
    cycle: u64,
}

/// RetrievalJobIndex implements a double-buffer (processing + registration) for document retrieval waiting lists.
/// Queries register interest in documents not yet materialized; when a processing cycle ends, registration becomes
/// the new processing batch. Documents arriving only trigger notifications for the current processing batch.
pub struct RetrievalJobIndex {
    inner: Mutex<Inner>,
}

impl RetrievalJobIndex {
    pub fn new() -> Self {
        Self { inner: Mutex::new(Inner { processing: RetrievalBatch::default(), registration: RetrievalBatch::default(), cycle: 0 }) }
    }

    /// Register a query waiting for a document. Goes into the registration batch of the current cycle.
    pub async fn register(&self, doc_id: i64, query_id: u32) {
        let mut inner = self.inner.lock().await;
        inner.registration.add(doc_id, query_id);
    }

    /// Rotate batches: processing batch is considered finished; registration promoted to processing; new empty registration created.
    pub async fn rotate(&self) {
        let mut inner = self.inner.lock().await;
        inner.processing = std::mem::take(&mut inner.registration);
        inner.registration = RetrievalBatch::default();
        inner.cycle += 1;
    }

    /// Promote registration batch to processing only if there is something waiting.
    /// This is a conditional rotation used when chaining after a processing cycle.
    pub async fn promote_if_needed(&self) {
        let mut inner = self.inner.lock().await;
        if !inner.registration.waiting.is_empty() {
            inner.processing = std::mem::take(&mut inner.registration);
            inner.registration = RetrievalBatch::default();
            inner.cycle += 1;
        }
    }

    /// Called when a document arrives from the database. Returns queries waiting in the processing batch for this doc.
    /// Registration batch is intentionally ignored until rotation to avoid mid-cycle race conditions.
    pub async fn document_arrived(&self, doc_id: i64) -> Vec<u32> {
        let mut inner = self.inner.lock().await;
        inner.processing.take(doc_id)
    }

    /// Introspection helper primarily for tests.
    pub async fn len_processing(&self) -> usize { self.inner.lock().await.processing.waiting.len() }
    pub async fn len_registration(&self) -> usize { self.inner.lock().await.registration.waiting.len() }
    pub async fn cycle(&self) -> u64 { self.inner.lock().await.cycle }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tokio::runtime::Runtime;

    #[tokio::test]
    async fn retrieval_job_basic_flow() {
        let idx = RetrievalJobIndex::new();
        // Register doc 10 in registration batch
        idx.register(10, 1).await;
        idx.register(10, 2).await;
        assert_eq!(idx.len_processing().await, 0);
        assert_eq!(idx.len_registration().await, 1);

        // Rotate -> registration becomes processing
        idx.rotate().await;
        assert_eq!(idx.len_processing().await, 1);
        assert_eq!(idx.len_registration().await, 0);
        assert_eq!(idx.cycle().await, 1);

        // Document arrives -> queries 1,2 returned
        let q = idx.document_arrived(10).await;
        assert_eq!(q, vec![1,2]);
        assert_eq!(idx.len_processing().await, 0);

        // Register doc 11 after arrival but before rotation -> stays in registration
        idx.register(11, 3).await;
        assert_eq!(idx.len_processing().await, 0);
        assert_eq!(idx.len_registration().await, 1);

        // Document arrives early (should not notify yet)
        let early = idx.document_arrived(11).await; // processing batch only -> empty
        assert!(early.is_empty());
        // Rotate, then arrival triggers
        idx.rotate().await;
        let late = idx.document_arrived(11).await;
        assert_eq!(late, vec![3]);
    }
}
