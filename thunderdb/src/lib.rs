pub mod events;
pub mod limit_layer;
pub mod range_index;

pub use events::{DocChange, LimitEvent, QueryRequest};
pub use limit_layer::{spawn_limit_layer, LimitIndex};
pub use range_index::{RangeLimitIndex, RangeSpec, ScoredDoc};

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use futures::stream;

    use super::*;

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
