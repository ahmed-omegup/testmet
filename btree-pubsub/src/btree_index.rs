use std::collections::{BTreeMap, HashMap, HashSet};

#[derive(Debug, Clone)]
pub struct Query {
    pub query_id: String,
    pub min_score: i32,
}

#[derive(Debug, Default)]
pub struct QueryChangeResult {
    pub added_to: Vec<String>,    // query_ids document now matches
    pub removed_from: Vec<String>, // query_ids document no longer matches
}

/// Range-based query index using Rust's BTreeMap
/// Indexed by min_score for efficient O(log n) lookups
pub struct RangeQueryIndex {
    // B-tree indexed by min_score -> query (unique key, no Vec needed)
    queries_by_min: BTreeMap<i32, Query>,
    // Track which queries currently match each document (doc_id -> set of query_ids)
    document_queries: HashMap<String, HashSet<String>>,
    // Track connections subscribed to each query (query_id -> set of connection_ids)
    query_connections: HashMap<String, HashSet<String>>,
}

impl RangeQueryIndex {
    pub fn new(_min: i32, _max: i32) -> Self {
        Self {
            queries_by_min: BTreeMap::new(),
            document_queries: HashMap::new(),
            query_connections: HashMap::new(),
        }
    }

    /// Add or update a query (independent of connections)
    pub fn add_query(&mut self, query_id: String, min_score: i32) {
        let query = Query {
            query_id: query_id.clone(),
            min_score,
        };

        // Insert into B-tree (replaces if exists at this min_score)
        self.queries_by_min.insert(min_score, query);
    }

    /// Subscribe a connection to a query
    pub fn subscribe_connection(&mut self, connection_id: String, query_id: String) {
        self.query_connections
            .entry(query_id)
            .or_insert_with(HashSet::new)
            .insert(connection_id);
    }

    /// Unsubscribe a connection from a query
    pub fn unsubscribe_connection(&mut self, connection_id: &str, query_id: &str) {
        if let Some(connections) = self.query_connections.get_mut(query_id) {
            connections.remove(connection_id);
            if connections.is_empty() {
                self.query_connections.remove(query_id);
            }
        }
    }

    /// Remove a query entirely by min_score
    pub fn remove_query(&mut self, min_score: i32) {
        if let Some(query) = self.queries_by_min.remove(&min_score) {
            // Remove from document tracking
            for doc_queries in self.document_queries.values_mut() {
                doc_queries.remove(&query.query_id);
            }
            // Remove connection subscriptions
            self.query_connections.remove(&query.query_id);
        }
    }

    /// Get queries affected by a document change (insert/update)
    /// Checks exactly 2 BTree entries: node at score and predecessor node
    pub fn get_queries_for_change(&mut self, doc_id: &str, old_score: Option<i32>, new_score: i32) -> QueryChangeResult {
        let mut new_matches = HashSet::new();
        
        // Get the query at new_score (if exists)
        if let Some(query) = self.queries_by_min.get(&new_score) {
            new_matches.insert(query.query_id.clone());
        }
        
        // Get the predecessor entry (largest key < new_score)
        if let Some((_, query)) = self.queries_by_min.range(..new_score).next_back() {
            new_matches.insert(query.query_id.clone());
        }

        // Get previous matches if this is an update
        let old_matches = if old_score.is_some() {
            self.document_queries
                .get(doc_id)
                .cloned()
                .unwrap_or_default()
        } else {
            HashSet::new()
        };

        // Calculate diffs
        let added_to: Vec<String> = new_matches
            .difference(&old_matches)
            .cloned()
            .collect();
        
        let removed_from: Vec<String> = old_matches
            .difference(&new_matches)
            .cloned()
            .collect();

        // Update tracking
        if new_matches.is_empty() {
            self.document_queries.remove(doc_id);
        } else {
            self.document_queries.insert(doc_id.to_string(), new_matches);
        }

        QueryChangeResult {
            added_to,
            removed_from,
        }
    }

    /// Remove document from tracking (for deletes)
    pub fn remove_document(&mut self, doc_id: &str) -> Vec<String> {
        self.document_queries
            .remove(doc_id)
            .map(|queries| queries.into_iter().collect())
            .unwrap_or_default()
    }

    /// Get connections subscribed to a query
    pub fn get_connections_for_query(&self, query_id: &str) -> Vec<String> {
        self.query_connections
            .get(query_id)
            .map(|conns| conns.iter().cloned().collect())
            .unwrap_or_default()
    }

    /// Get all queries for a connection
    pub fn get_queries_for_connection(&self, connection_id: &str) -> Vec<String> {
        self.query_connections
            .iter()
            .filter(|(_, conns)| conns.contains(connection_id))
            .map(|(qid, _)| qid.clone())
            .collect()
    }

    /// Get query by min_score
    pub fn get_query(&self, min_score: i32) -> Option<&Query> {
        self.queries_by_min.get(&min_score)
    }

    /// Get statistics
    pub fn get_stats(&self) -> (usize, usize) {
        let total_queries = self.queries_by_min.len();
        let tracked_docs = self.document_queries.len();
        (total_queries, tracked_docs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_query_matching_with_change() {
        let mut index = RangeQueryIndex::new(0, 1000);
        
        // Add queries (only min_score, no max_score)
        index.add_query("q1".to_string(), 100);
        index.add_query("q2".to_string(), 150);
        index.add_query("q3".to_string(), 300);

        // Subscribe connections to queries
        index.subscribe_connection("conn1".to_string(), "q1".to_string());
        index.subscribe_connection("conn2".to_string(), "q2".to_string());
        index.subscribe_connection("conn3".to_string(), "q3".to_string());

        // Insert doc with score 175 - should match q2 (150) and q1 (100, predecessor)
        let result = index.get_queries_for_change("doc1", None, 175);
        assert_eq!(result.added_to.len(), 2);
        assert!(result.added_to.contains(&"q1".to_string()));
        assert!(result.added_to.contains(&"q2".to_string()));
        assert_eq!(result.removed_from.len(), 0);

        // Update doc1 to score 225 - should match q2 (150, predecessor) only
        let result = index.get_queries_for_change("doc1", Some(175), 225);
        assert_eq!(result.added_to.len(), 0);
        assert_eq!(result.removed_from.len(), 1);
        assert!(result.removed_from.contains(&"q1".to_string()));

        // Update doc1 to score 350 - should match q3 (300, predecessor)
        let result = index.get_queries_for_change("doc1", Some(225), 350);
        assert_eq!(result.added_to.len(), 1);
        assert!(result.added_to.contains(&"q3".to_string()));
        assert_eq!(result.removed_from.len(), 1);
        assert!(result.removed_from.contains(&"q2".to_string()));

        // Verify connections can be retrieved
        let conns = index.get_connections_for_query("q3");
        assert_eq!(conns.len(), 1);
        assert!(conns.contains(&"conn3".to_string()));
    }

    #[test]
    fn test_document_removal() {
        let mut index = RangeQueryIndex::new(0, 1000);
        
        index.add_query("q1".to_string(), 100);
        index.add_query("q2".to_string(), 150);

        // Add document (insert at score 175)
        let result = index.get_queries_for_change("doc1", None, 175);
        assert_eq!(result.added_to.len(), 2);

        // Remove document
        let removed = index.remove_document("doc1");
        assert_eq!(removed.len(), 2);
        assert!(removed.contains(&"q1".to_string()));
        assert!(removed.contains(&"q2".to_string()));
    }

    #[test]
    fn test_efficient_btree_lookup() {
        let mut index = RangeQueryIndex::new(0, 1000);
        
        // Add many queries with min_scores at 0, 100, 200, ...
        for i in 0..10 {
            let min = i * 100;
            index.add_query(format!("q{}", i), min);
        }

        // Insert at score 225 should only check:
        // - Entry at 200 (predecessor)
        // - No entry at 225 (doesn't exist)
        // So should match only q2
        let result = index.get_queries_for_change("doc1", None, 225);
        assert_eq!(result.added_to.len(), 1);
        assert!(result.added_to.contains(&"q2".to_string()));
    }
}
