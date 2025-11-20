use std::sync::Arc;

use futures::{Stream, StreamExt};
use tokio::sync::mpsc;

use crate::events::{DocChange, LimitEvent, QueryRequest};

/// Abstraction over whichever document index backs the limit operator.
pub trait LimitIndex: Send + Sync + 'static {
    type DocId: Clone + Send + Sync + 'static;
    type DocState: Clone + Send + Sync + 'static;
    type QueryId: Clone + Send + Sync + 'static;
    type QuerySpec: Clone + Send + Sync + 'static;

    fn apply_change(&self, change: DocChange<Self::DocId, Self::DocState>) -> Vec<LimitEvent<Self::DocId, Self::QueryId>>;
    fn apply_query(&self, query: QueryRequest<Self::QueryId, Self::QuerySpec>) -> Vec<LimitEvent<Self::DocId, Self::QueryId>>;
}

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
    I: LimitIndex,
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
