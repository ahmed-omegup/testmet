use std::hash::Hash;

/// Change events for documents flowing into the limit layer.
#[derive(Clone, Debug)]
pub enum DocChange<DocId, DocState> {
    Upsert { id: DocId, new: DocState },
    Remove { id: DocId },
}

/// Query lifecycle events (register / update / remove).
#[derive(Clone, Debug)]
pub enum QueryRequest<QueryId, QuerySpec> {
    Upsert { id: QueryId, spec: QuerySpec },
    Remove { id: QueryId },
}

/// Output notification emitted by the limit layer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LimitEvent<DocId, QueryId> {
    pub doc_id: DocId,
    pub added_to: Vec<QueryId>,
    pub removed_from: Vec<QueryId>,
    pub evictions: Vec<QueryId>,
}

impl<DocId: Clone, QueryId> LimitEvent<DocId, QueryId> {
    pub fn new(doc_id: DocId) -> Self {
        Self { doc_id, added_to: Vec::new(), removed_from: Vec::new(), evictions: Vec::new() }
    }
}

/// Helper to coalesce per-document events before emitting downstream.
pub(crate) struct EventCollector<DocId, QueryId> {
    inner: std::collections::HashMap<DocId, LimitEvent<DocId, QueryId>>,
}

impl<DocId: Eq + Hash + Clone, QueryId: Clone> EventCollector<DocId, QueryId> {
    pub fn new() -> Self {
        Self { inner: std::collections::HashMap::new() }
    }

    fn entry(&mut self, doc_id: DocId) -> &mut LimitEvent<DocId, QueryId> {
        self.inner.entry(doc_id.clone()).or_insert_with(|| LimitEvent::new(doc_id))
    }

    pub fn added(&mut self, doc_id: DocId, query_id: QueryId) {
        self.entry(doc_id).added_to.push(query_id);
    }

    pub fn removed(&mut self, doc_id: DocId, query_id: QueryId) {
        self.entry(doc_id).removed_from.push(query_id);
    }

    pub fn evicted(&mut self, doc_id: DocId, query_id: QueryId) {
        self.entry(doc_id).evictions.push(query_id);
    }

    pub fn finish(self) -> Vec<LimitEvent<DocId, QueryId>> {
        self.inner.into_values().collect()
    }
}
