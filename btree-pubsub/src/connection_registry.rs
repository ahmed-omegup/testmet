use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::{RwLock, mpsc};
use serde::{Serialize};

#[derive(Debug, Clone, Serialize)]
#[serde(tag = "type")]
pub enum Notification {
    #[serde(rename = "added")]
    Added {
        query_id: u32,
        id: u32,
        score: i32,
        timestamp: i32,
    },
    #[serde(rename = "updated")]
    Updated {
        query_id: u32,
        id: u32,
        score: i32,
        timestamp: i32,
    },
    #[serde(rename = "removed")]
    Removed { query_id: u32, id: u32 },
    #[serde(rename = "changeEvent")]
    ChangeEvent {
        id: u32,
        old: Option<Document>,
        new: Option<Document>,
        #[serde(rename = "addedToQueries")]
        added_to: Vec<u32>,
        #[serde(rename = "removedFromQueries")]
        removed_from: Vec<u32>,
        meta: Option<ChangeMeta>,
    },
}

pub type NotificationSender = mpsc::UnboundedSender<Notification>;

/// Lightweight document shape used for ChangeEvent payloads
#[derive(Debug, Clone, Serialize)]
pub struct Document {
    pub id: u32,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub score: Option<i32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub timestamp: Option<i32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct ChangeMeta {
    pub op: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub lsn: Option<String>,
}

/// Registry of active WebSocket connections
pub struct ConnectionRegistry {
    connections: RwLock<HashMap<String, NotificationSender>>,
}

impl ConnectionRegistry {
    pub fn new() -> Arc<Self> {
        Arc::new(Self {
            connections: RwLock::new(HashMap::new()),
        })
    }

    /// Register a new connection
    pub async fn register(&self, connection_id: String, sender: NotificationSender) {
        let mut conns = self.connections.write().await;
        conns.insert(connection_id, sender);
    }

    /// Unregister a connection
    pub async fn unregister(&self, connection_id: &str) {
        let mut conns = self.connections.write().await;
        conns.remove(connection_id);
    }

    /// Send notification to a specific connection
    pub async fn notify(&self, connection_id: &str, notification: Notification) {
        let conns = self.connections.read().await;
        if let Some(sender) = conns.get(connection_id) {
            let _ = sender.send(notification);
        }
    }

    /// Send notification to multiple connections
    pub async fn notify_many(&self, connection_ids: &[String], notification: Notification) {
        let conns = self.connections.read().await;
        for conn_id in connection_ids {
            if let Some(sender) = conns.get(conn_id) {
                let _ = sender.send(notification.clone());
            }
        }
    }
}
