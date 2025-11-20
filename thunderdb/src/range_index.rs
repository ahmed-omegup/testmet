use std::collections::{HashMap, HashSet};
use std::sync::RwLock;

use dashmap::DashMap;

use crate::events::{DocChange, EventCollector, LimitEvent, QueryRequest};
use crate::limit_layer::LimitIndex;

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

    fn upsert(&mut self, doc_id: u64, score: i64) {
        self.members.insert(doc_id, score);
    }

    fn remove(&mut self, doc_id: &u64) -> bool {
        self.members.remove(doc_id).is_some()
    }

    fn trim_to_limit(&mut self) -> Option<u64> {
        if self.members.len() <= self.spec.limit {
            return None;
        }
        let (evicted_doc, _) = self
            .members
            .iter()
            .min_by_key(|(doc, score)| (*score, *doc))
            .map(|(doc, score)| (*doc, *score))
            .expect("members not empty");
        self.members.remove(&evicted_doc);
        Some(evicted_doc)
    }

    fn snapshot_keys(&self) -> HashSet<u64> {
        self.members.keys().copied().collect()
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

    fn rebuild_query_members(&self, spec: &RangeSpec) -> QueryState {
        let mut state = QueryState::new(spec.clone());
        for entry in self.docs.iter() {
            if spec.contains(entry.value().score) {
                state.upsert(*entry.key(), entry.value().score);
            }
        }
        while state.members.len() > spec.limit {
            state.trim_to_limit();
        }
        state
    }

    fn handle_upsert(&self, doc_id: u64, doc: ScoredDoc) -> Vec<LimitEvent<u64, u64>> {
        self.docs.insert(doc_id, doc.clone());
        let mut collector = EventCollector::new();
        let mut queries = self.queries.write().expect("poisoned query lock");
        for (query_id, state) in queries.iter_mut() {
            let matches = state.spec.contains(doc.score);
            let was_member = state.members.contains_key(&doc_id);
            match (matches, was_member) {
                (true, true) => {
                    state.upsert(doc_id, doc.score);
                }
                (true, false) => {
                    state.upsert(doc_id, doc.score);
                    if state.members.len() > state.spec.limit {
                        if let Some(evicted_doc) = state.trim_to_limit() {
                            collector.evicted(evicted_doc, *query_id);
                        }
                        if state.members.contains_key(&doc_id) {
                            collector.added(doc_id, *query_id);
                        }
                    } else {
                        collector.added(doc_id, *query_id);
                    }
                }
                (false, true) => {
                    state.members.remove(&doc_id);
                    collector.removed(doc_id, *query_id);
                }
                (false, false) => {}
            }
        }
        collector.finish()
    }

    fn handle_remove(&self, doc_id: u64) -> Vec<LimitEvent<u64, u64>> {
        self.docs.remove(&doc_id);
        let mut collector = EventCollector::new();
        let mut queries = self.queries.write().expect("poisoned query lock");
        for (query_id, state) in queries.iter_mut() {
            if state.remove(&doc_id) {
                collector.removed(doc_id, *query_id);
            }
        }
        collector.finish()
    }

    fn handle_query_upsert(&self, query_id: u64, spec: RangeSpec) -> Vec<LimitEvent<u64, u64>> {
        let mut collector = EventCollector::new();
        let mut queries = self.queries.write().expect("poisoned query lock");
        let new_state = self.rebuild_query_members(&spec);
        let new_keys = new_state.snapshot_keys();
        let old_state = queries.insert(query_id, new_state);
        let old_keys = old_state.map(|state| state.snapshot_keys()).unwrap_or_default();

        for doc in new_keys.difference(&old_keys) {
            collector.added(*doc, query_id);
        }
        for doc in old_keys.difference(&new_keys) {
            collector.removed(*doc, query_id);
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
