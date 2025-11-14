use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::{RwLock, mpsc};
use serde::{Serialize};

#[derive(Debug, Clone, Serialize)]
pub struct DocState {
    pub score: Option<i32>,
    pub timestamp: Option<i32>,
}

#[derive(Debug, Clone, Serialize)]
#[serde(tag = "type")]
pub enum Notification {
    #[serde(rename = "added")]
    Added { id: u32, score: i32, timestamp: i32 },
    #[serde(rename = "updated")]
    Updated { id: u32, old: DocState, new: DocState },
    #[serde(rename = "removed")]
    Removed { id: u32 },
}

pub type NotificationSender = mpsc::UnboundedSender<Notification>;

// Removed complex ChangeEvent/document meta now that multiplexing emits direct per-connection doc events.

/// Registry of active WebSocket connections
pub struct ConnectionRegistry {
    connections: RwLock<HashMap<u64, NotificationSender>>,
}

impl ConnectionRegistry {
    pub fn new() -> Arc<Self> {
        Arc::new(Self {
            connections: RwLock::new(HashMap::new()),
        })
    }

    /// Register a new connection
    pub async fn register(&self, connection_id: u64, sender: NotificationSender) {
        let mut conns = self.connections.write().await;
        conns.insert(connection_id, sender);
    }

    /// Unregister a connection
    pub async fn unregister(&self, connection_id: u64) {
        let mut conns = self.connections.write().await;
        conns.remove(&connection_id);
    }

    /// Send notification to a specific connection
    pub async fn notify(&self, connection_id: u64, notification: Notification) {
        let conns = self.connections.read().await;
        if let Some(sender) = conns.get(&connection_id) {
            let _ = sender.send(notification);
        }
    }

    /// Send notification to multiple connections
    pub async fn notify_many(&self, connection_ids: &[u64], notification: Notification) {
        let conns = self.connections.read().await;
        for conn_id in connection_ids {
            if let Some(sender) = conns.get(conn_id) {
                let _ = sender.send(notification.clone());
            }
        }
    }
}
