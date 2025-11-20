use std::collections::HashMap;
use std::sync::RwLock;

use dashmap::DashMap;

use crate::events::{DocChange, EventCollector, LimitEvent, QueryRequest};
use crate::limit_layer::LimitIndex;

use super::types::{DocId, QueryId, RangeSpec, Score, ScoredDoc};

/// Thread-safe in-memory reference implementation using range filters + hard limits.
pub struct RangeLimitIndex {
    docs: DashMap<DocId, ScoredDoc>,
    queries: RwLock<HashMap<QueryId, RangeSpec>>,
}

impl RangeLimitIndex {
    pub fn new() -> Self {
        Self {
            docs: DashMap::new(),
            queries: RwLock::new(HashMap::new()),
        }
    }

    fn count_matching_docs(&self, spec: &RangeSpec) -> Vec<(DocId, Score)> {
        let mut docs: Vec<_> = self
            .docs
            .iter()
            .filter(|e| spec.contains(e.value().score))
            .map(|e| (*e.key(), e.value().score))
            .collect();
        docs.sort_by_key(|(id, score)| (*score, *id));
        docs
    }

    fn handle_change(&self, change: &DocChange<DocId, ScoredDoc>) -> Vec<LimitEvent<DocId, QueryId>> {
        let doc_id = change.id;

        // Update doc store
        match (&change.old, &change.new) {
            (_, Some(new_doc)) => {
                self.docs.insert(doc_id, new_doc.clone());
            }
            (Some(_), None) => {
                self.docs.remove(&doc_id);
            }
            (None, None) => {}
        }

        let mut collector = EventCollector::new();
        let queries = self.queries.read().expect("poisoned query lock");

        for (query_id, spec) in queries.iter() {
            let old_matches = change.old.as_ref().map(|d| spec.contains(d.score)).unwrap_or(false);
            let new_matches = change.new.as_ref().map(|d| spec.contains(d.score)).unwrap_or(false);

            // Compute top-k for this query
            let mut top_docs = self.count_matching_docs(spec);
            top_docs.truncate(spec.limit);
            let top_set: std::collections::HashSet<DocId> = top_docs.iter().map(|(id, _)| *id).collect();

            let was_in_top = change.old.is_some() && old_matches && top_set.contains(&doc_id);
            let is_in_top = change.new.is_some() && new_matches && top_set.contains(&doc_id);

            match (old_matches, new_matches, was_in_top, is_in_top) {
                // Moved into top-k
                (false, true, false, true) | (_, true, false, true) => {
                    collector.added(doc_id, *query_id);
                    // Check if this displaced someone
                    let all_matching = self.count_matching_docs(spec);
                    if all_matching.len() > spec.limit {
                        if let Some((evicted_id, _)) = all_matching.get(spec.limit) {
                            if *evicted_id != doc_id {
                                collector.eviction_caused(doc_id, *query_id, *evicted_id);
                            }
                        }
                    }
                }
                // Fell out of top-k
                (true, _, true, false) => {
                    collector.removed(doc_id, *query_id);
                }
                // Moved out of range entirely
                (true, false, _, _) => {
                    if was_in_top {
                        collector.removed(doc_id, *query_id);
                    }
                }
                _ => {}
            }
        }

        collector.finish()
    }

    fn handle_query_upsert(&self, query_id: QueryId, spec: RangeSpec) -> Vec<LimitEvent<DocId, QueryId>> {
        let mut collector = EventCollector::new();
        let mut queries = self.queries.write().expect("poisoned query lock");

        let mut new_top = self.count_matching_docs(&spec);
        new_top.truncate(spec.limit);
        let new_set: std::collections::HashSet<DocId> = new_top.iter().map(|(id, _)| *id).collect();

        let old_set: std::collections::HashSet<DocId> = if let Some(old_spec) = queries.get(&query_id) {
            let mut old_top = self.count_matching_docs(old_spec);
            old_top.truncate(old_spec.limit);
            old_top.iter().map(|(id, _)| *id).collect()
        } else {
            std::collections::HashSet::new()
        };

        queries.insert(query_id, spec);

        for doc in new_set.difference(&old_set) {
            collector.added(*doc, query_id);
        }
        for doc in old_set.difference(&new_set) {
            collector.removed(*doc, query_id);
        }
        collector.finish()
    }

    fn handle_query_remove(&self, query_id: QueryId) -> Vec<LimitEvent<DocId, QueryId>> {
        let mut collector = EventCollector::new();
        let mut queries = self.queries.write().expect("poisoned query lock");
        if let Some(spec) = queries.remove(&query_id) {
            let mut top = self.count_matching_docs(&spec);
            top.truncate(spec.limit);
            for (doc_id, _) in top {
                collector.removed(doc_id, query_id);
            }
        }
        collector.finish()
    }
}

impl LimitIndex for RangeLimitIndex {
    type DocId = DocId;
    type DocState = ScoredDoc;
    type QueryId = QueryId;
    type QuerySpec = RangeSpec;

    fn apply_change(
        &self,
        change: &DocChange<Self::DocId, Self::DocState>,
    ) -> Vec<LimitEvent<Self::DocId, Self::QueryId>> {
        self.handle_change(change)
    }

    fn apply_query(
        &self,
        query: QueryRequest<Self::QueryId, Self::QuerySpec>,
    ) -> Vec<LimitEvent<Self::DocId, Self::QueryId>> {
        match query {
            QueryRequest::Upsert { id, spec } => self.handle_query_upsert(id, spec),
            QueryRequest::Remove { id } => self.handle_query_remove(id),
        }
    }
}
