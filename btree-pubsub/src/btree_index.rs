use std::collections::BTreeMap;
use std::ops::Bound::{Included, Unbounded};

#[derive(Debug, Clone)]
pub struct QuerySubscription {
    pub connection_id: String,
    pub query_id: String,
    pub min_score: i32,
    pub max_score: i32,
}

/// Range-based query index using Rust's BTreeMap
/// Key: (min_score, max_score, query_id)
/// This allows efficient range queries
pub struct RangeQueryIndex {
    // BTreeMap for efficient range scanning
    // Maps score ranges to queries interested in that range
    queries: BTreeMap<i32, Vec<QuerySubscription>>,
    // Quick lookup by query_id
    query_lookup: std::collections::HashMap<String, QuerySubscription>,
}

impl RangeQueryIndex {
    pub fn new(_min: i32, _max: i32) -> Self {
        Self {
            queries: BTreeMap::new(),
            query_lookup: std::collections::HashMap::new(),
        }
    }

    /// Add a query subscription
    pub fn add_query(&mut self, connection_id: String, query_id: String, min_score: i32, max_score: i32) {
        let subscription = QuerySubscription {
            connection_id: connection_id.clone(),
            query_id: query_id.clone(),
            min_score,
            max_score,
        };

        // Store in lookup map
        self.query_lookup.insert(query_id.clone(), subscription.clone());

        // Add to range index at min_score
        self.queries
            .entry(min_score)
            .or_insert_with(Vec::new)
            .push(subscription);
    }

    /// Remove a query subscription
    pub fn remove_query(&mut self, query_id: &str) {
        if let Some(subscription) = self.query_lookup.remove(query_id) {
            // Remove from range index
            if let Some(subs) = self.queries.get_mut(&subscription.min_score) {
                subs.retain(|s| s.query_id != query_id);
                if subs.is_empty() {
                    self.queries.remove(&subscription.min_score);
                }
            }
        }
    }

    /// Find all connections interested in a document with the given score
    pub fn find_connections_for_score(&self, score: i32) -> Vec<String> {
        let mut connections = std::collections::HashSet::new();

        // Scan all ranges that might overlap with this score
        // We need to check all queries where min_score <= score
        for (_, subscriptions) in self.queries.range((Unbounded, Included(&score))) {
            for sub in subscriptions {
                if score >= sub.min_score && score <= sub.max_score {
                    connections.insert(sub.connection_id.clone());
                }
            }
        }

        connections.into_iter().collect()
    }

    /// Get all queries for a connection
    pub fn get_queries_for_connection(&self, connection_id: &str) -> Vec<QuerySubscription> {
        self.query_lookup
            .values()
            .filter(|s| s.connection_id == connection_id)
            .cloned()
            .collect()
    }

    /// Get statistics
    pub fn get_stats(&self) -> (usize, usize) {
        let total_queries = self.query_lookup.len();
        let unique_ranges = self.queries.len();
        (total_queries, unique_ranges)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_range_query() {
        let mut index = RangeQueryIndex::new(0, 1000);
        
        index.add_query("conn1".to_string(), "q1".to_string(), 100, 200);
        index.add_query("conn2".to_string(), "q2".to_string(), 150, 250);
        index.add_query("conn3".to_string(), "q3".to_string(), 300, 400);

        // Score 175 should match conn1 and conn2
        let connections = index.find_connections_for_score(175);
        assert_eq!(connections.len(), 2);

        // Score 350 should match only conn3
        let connections = index.find_connections_for_score(350);
        assert_eq!(connections.len(), 1);
        assert!(connections.contains(&"conn3".to_string()));
    }
}
