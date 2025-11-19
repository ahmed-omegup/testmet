use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::sync::{Arc, RwLock};

use dashmap::DashMap;
use futures::{Stream, StreamExt};
use tokio::sync::mpsc;

/// Change events for documents flowing into the limit layer.
#[derive(Clone, Debug)]
pub enum DocChange<DocId, DocState> {
    Upsert { id: DocId, new: DocState },
    Remove { id: DocId },
}

/// Query lifecycle events (register, update, remove).
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

impl<DocId: Clone, QueryId: Clone> LimitEvent<DocId, QueryId> {
    fn new(doc_id: DocId) -> Self {
        Self { doc_id, added_to: Vec::new(), removed_from: Vec::new(), evictions: Vec::new() }
    }
}

/// Abstraction over whichever document index / tree backs the limit operator.
pub trait LimitIndex: Send + Sync {
    type DocId: Clone + Send + Sync + Eq + Hash + 'static;
    type DocState: Clone + Send + Sync + 'static;
    type QueryId: Clone + Send + Sync + Eq + Hash + 'static;
    type QuerySpec: Clone + Send + Sync + 'static;

    fn apply_change(&self, change: DocChange<Self::DocId, Self::DocState>) -> Vec<LimitEvent<Self::DocId, Self::QueryId>>;
    fn apply_query(&self, query: QueryRequest<Self::QueryId, Self::QuerySpec>) -> Vec<LimitEvent<Self::DocId, Self::QueryId>>;
}

/// Internal helper used by `spawn_limit_layer` to multiplex the two upstream streams.
enum StreamInput<C, Q> {
    Change(C),
    Query(Q),
}

/// Wire a change stream and a query stream into the limit index, returning a receiver of limit events.
pub fn spawn_limit_layer<I, CS, QS>(
    index: Arc<I>,
    changes: CS,
    queries: QS,
    buffer: usize,
) -> mpsc::Receiver<LimitEvent<I::DocId, I::QueryId>>
where
    I: LimitIndex + 'static,
    CS: Stream<Item = DocChange<I::DocId, I::DocState>> + Send + 'static + Unpin,
    QS: Stream<Item = QueryRequest<I::QueryId, I::QuerySpec>> + Send + 'static + Unpin,
{
    let (tx, rx) = mpsc::channel(buffer);
    tokio::spawn(async move {
        let change_stream = changes.map(StreamInput::Change);
        let query_stream = queries.map(StreamInput::Query);
        let mut combined = futures::stream::select(change_stream, query_stream);
        while let Some(item) = combined.next().await {
            let emitted = match item {
                StreamInput::Change(evt) => index.apply_change(evt),
                StreamInput::Query(evt) => index.apply_query(evt),
            };
            for event in emitted {
                if tx.send(event).await.is_err() {
                    return;
                }
            }
        }
    });
    rx
}

/// Simple scored document used by the reference index.
#[derive(Clone, Debug)]
pub struct ScoredDoc {
    pub score: i64,
}

/// Range-based query with a strict cap.
#[derive(Clone, Debug)]
pub struct RangeSpec {
    pub min_score: i64,
    pub max_score: i64,
    pub limit: usize,
}

impl RangeSpec {
    fn contains(&self, score: i64) -> bool {
        score >= self.min_score && score <= self.max_score
    }
}

struct QueryState {
    spec: RangeSpec,
    members: HashMap<u64, i64>,
}

impl QueryState {
    fn new(spec: RangeSpec) -> Self {
        Self { spec, members: HashMap::new() }
    }

    fn retain_top_k(&mut self) -> Option<u64> {
        if self.members.len() <= self.spec.limit {
            return None;
        }
        let mut candidate: Option<(u64, i64)> = None;
        for (doc, score) in self.members.iter() {
            candidate = match candidate {
                None => Some((*doc, *score)),
                Some((best_doc, best_score)) => {
                    if *score < best_score || (*score == best_score && *doc < best_doc) {
                        Some((*doc, *score))
                    } else {
                        Some((best_doc, best_score))
                    }
                }
            };
        }
        if let Some((doc, _)) = candidate {
            self.members.remove(&doc);
            return Some(doc);
        }
        None
    }
}

/// Thread-safe in-memory reference implementation using range filters + hard limits.
pub struct RangeLimitIndex {
    docs: DashMap<u64, ScoredDoc>,
    queries: RwLock<HashMap<u64, QueryState>>,
}

impl RangeLimitIndex {
    pub fn new() -> Self {
        Self { docs: DashMap::new(), queries: RwLock::new(HashMap::new()) }
    }

    fn handle_upsert(&self, doc_id: u64, doc: ScoredDoc) -> Vec<LimitEvent<u64, u64>> {
        self.docs.insert(doc_id, doc.clone());
        let mut collector = EventCollector::new();
        let mut queries = self.queries.write().expect("poisoned query lock");
        for (query_id, state) in queries.iter_mut() {
            let matches = state.spec.contains(doc.score);
            let was_member = state.members.contains_key(&doc_id);
            if matches {
                state.members.insert(doc_id, doc.score);
                let evicted = state.retain_top_k();
                let is_member = state.members.contains_key(&doc_id);
                if !was_member && is_member {
                    collector.added(doc_id, *query_id);
                }
                if let Some(evicted_doc) = evicted {
                    collector.evicted(evicted_doc, *query_id);
                }
                if was_member && !is_member {
                    collector.evicted(doc_id, *query_id);
                }
            } else if was_member {
                state.members.remove(&doc_id);
                collector.removed(doc_id, *query_id);
            }
        }
        collector.finish()
    }

    fn handle_remove(&self, doc_id: u64) -> Vec<LimitEvent<u64, u64>> {
        self.docs.remove(&doc_id);
        let mut collector = EventCollector::new();
        let mut queries = self.queries.write().expect("poisoned query lock");
        for (query_id, state) in queries.iter_mut() {
            if state.members.remove(&doc_id).is_some() {
                collector.removed(doc_id, *query_id);
            }
        }
        collector.finish()
    }

    fn handle_query_upsert(&self, query_id: u64, spec: RangeSpec) -> Vec<LimitEvent<u64, u64>> {
        let mut new_state = QueryState::new(spec.clone());
        for entry in self.docs.iter() {
            if spec.contains(entry.value().score) {
                new_state.members.insert(*entry.key(), entry.value().score);
            }
        }
        while new_state.members.len() > spec.limit {
            new_state.retain_top_k();
        }
        let mut collector = EventCollector::new();
        let mut queries = self.queries.write().expect("poisoned query lock");
        let old = queries.insert(query_id, new_state);
        let new_keys: HashSet<u64> = queries
            .get(&query_id)
            .map(|state| state.members.keys().copied().collect())
            .unwrap_or_default();
        let old_keys: HashSet<u64> = old
            .as_ref()
            .map(|state| state.members.keys().copied().collect())
            .unwrap_or_default();
        for doc in new_keys.iter() {
            if !old_keys.contains(doc) {
                collector.added(*doc, query_id);
            }
        }
        for doc in old_keys.iter() {
            if !new_keys.contains(doc) {
                collector.removed(*doc, query_id);
            }
        }
        collector.finish()
    }

    fn handle_query_remove(&self, query_id: u64) -> Vec<LimitEvent<u64, u64>> {
        let mut collector = EventCollector::new();
        let mut queries = self.queries.write().expect("poisoned query lock");
        if let Some(state) = queries.remove(&query_id) {
            for doc in state.members.keys() {
                collector.removed(*doc, query_id);
            }
        }
        collector.finish()
    }
}

impl LimitIndex for RangeLimitIndex {
    type DocId = u64;
    type DocState = ScoredDoc;
    type QueryId = u64;
    type QuerySpec = RangeSpec;

    fn apply_change(&self, change: DocChange<Self::DocId, Self::DocState>) -> Vec<LimitEvent<Self::DocId, Self::QueryId>> {
        match change {
            DocChange::Upsert { id, new } => self.handle_upsert(id, new),
            DocChange::Remove { id } => self.handle_remove(id),
        }
    }

    fn apply_query(&self, query: QueryRequest<Self::QueryId, Self::QuerySpec>) -> Vec<LimitEvent<Self::DocId, Self::QueryId>> {
        match query {
            QueryRequest::Upsert { id, spec } => self.handle_query_upsert(id, spec),
            QueryRequest::Remove { id } => self.handle_query_remove(id),
        }
    }
}

struct EventCollector<DocId, QueryId> {
    inner: HashMap<DocId, LimitEvent<DocId, QueryId>>,
}

impl<DocId: Eq + Hash + Clone, QueryId: Clone> EventCollector<DocId, QueryId> {
    fn new() -> Self {
        Self { inner: HashMap::new() }
    }

    fn entry(&mut self, doc_id: DocId) -> &mut LimitEvent<DocId, QueryId> {
        self.inner.entry(doc_id.clone()).or_insert_with(|| LimitEvent::new(doc_id))
    }

    fn added(&mut self, doc_id: DocId, query_id: QueryId) {
        self.entry(doc_id).added_to.push(query_id);
    }

    fn removed(&mut self, doc_id: DocId, query_id: QueryId) {
        self.entry(doc_id).removed_from.push(query_id);
    }

    fn evicted(&mut self, doc_id: DocId, query_id: QueryId) {
        self.entry(doc_id).evictions.push(query_id);
    }

    fn finish(self) -> Vec<LimitEvent<DocId, QueryId>> {
        self.inner.into_values().collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use futures::stream;

    #[tokio::test]
    async fn enforces_limits_and_evictions() {
        let index = Arc::new(RangeLimitIndex::new());
        let changes = stream::iter(vec![
            DocChange::Upsert { id: 1, new: ScoredDoc { score: 50 } },
            DocChange::Upsert { id: 2, new: ScoredDoc { score: 40 } },
            DocChange::Upsert { id: 3, new: ScoredDoc { score: 10 } },
            DocChange::Upsert { id: 4, new: ScoredDoc { score: 60 } },
        ]);
        let queries = stream::iter(vec![
            QueryRequest::Upsert { id: 100, spec: RangeSpec { min_score: 0, max_score: 100, limit: 2 } },
        ]);

        let mut rx = spawn_limit_layer(index, changes, queries, 16);
        let mut events = Vec::new();
        while let Some(evt) = rx.recv().await {
            events.push(evt);
        }
        let doc1_added: Vec<_> = events
            .iter()
            .filter(|e| e.doc_id == 1)
            .flat_map(|e| e.added_to.iter().copied())
            .collect();
        assert_eq!(doc1_added, vec![100]);
        let doc2_added: Vec<_> = events
            .iter()
            .filter(|e| e.doc_id == 2)
            .flat_map(|e| e.added_to.iter().copied())
            .collect();
        assert!(doc2_added.contains(&100));
        let doc2_evictions: Vec<_> = events
            .iter()
            .filter(|e| e.doc_id == 2)
            .flat_map(|e| e.evictions.iter().copied())
            .collect();
        assert!(doc2_evictions.contains(&100));
        let doc4_added: Vec<_> = events
            .iter()
            .filter(|e| e.doc_id == 4)
            .flat_map(|e| e.added_to.iter().copied())
            .collect();
        assert_eq!(doc4_added, vec![100]);
    }

    #[tokio::test]
    async fn query_add_and_remove() {
        let index = Arc::new(RangeLimitIndex::new());
        let changes = stream::iter(vec![
            DocChange::Upsert { id: 1, new: ScoredDoc { score: 20 } },
            DocChange::Upsert { id: 2, new: ScoredDoc { score: 30 } },
        ]);
        let queries = stream::iter(vec![
            QueryRequest::Upsert { id: 5, spec: RangeSpec { min_score: 0, max_score: 50, limit: 5 } },
            QueryRequest::Remove { id: 5 },
        ]);

        let mut rx = spawn_limit_layer(index, changes, queries, 16);
        let mut events = Vec::new();
        while let Some(evt) = rx.recv().await {
            events.push(evt);
        }
        let doc1_events: Vec<_> = events.iter().filter(|e| e.doc_id == 1).collect();
        assert!(doc1_events.iter().any(|e| e.added_to.contains(&5)));
        assert!(doc1_events.iter().any(|e| e.removed_from.contains(&5)));
    }
}
