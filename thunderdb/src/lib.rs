pub mod events;
pub mod limit_layer;
pub mod range_index;

pub use events::{DocChange, LimitEvent, QueryRequest};
pub use limit_layer::{spawn_limit_layer, LimitIndex};
pub use range_index::{DocId, QueryId, RangeLimitIndex, RangeSpec, Score, ScoredDoc};

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use futures::stream;

    use super::*;

    #[tokio::test]
    async fn enforces_limits_and_evictions() {
        let index = Arc::new(RangeLimitIndex::new());
        let changes = stream::iter(vec![
            DocChange { id: 1, old: None, new: Some(ScoredDoc { score: 50 }) },
            DocChange { id: 2, old: None, new: Some(ScoredDoc { score: 40 }) },
            DocChange { id: 3, old: None, new: Some(ScoredDoc { score: 10 }) },
            DocChange { id: 4, old: None, new: Some(ScoredDoc { score: 60 }) },
        ]);
        let queries = stream::iter(vec![
            QueryRequest::Upsert { id: 100, spec: RangeSpec { min_score: 0, max_score: 100, limit: 2 } },
        ]);

        let mut rx = spawn_limit_layer(index, changes, queries, 16);
        let mut events = Vec::new();
        while let Some(evt) = rx.recv().await {
            println!("Event: doc_id={}, added_to={:?}, removed_from={:?}, evictions={:?}", 
                evt.doc_id, evt.added_to, evt.removed_from, evt.evictions);
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
        // Doc 4 causes eviction of doc 2 from query 100
        let doc4_evictions: Vec<_> = events
            .iter()
            .filter(|e| e.doc_id == 4)
            .flat_map(|e| e.evictions.iter().map(|(q, evicted)| (*q, *evicted)))
            .collect();
        assert!(doc4_evictions.contains(&(100, 2)));
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
            DocChange { id: 1, old: None, new: Some(ScoredDoc { score: 20 }) },
            DocChange { id: 2, old: None, new: Some(ScoredDoc { score: 30 }) },
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
