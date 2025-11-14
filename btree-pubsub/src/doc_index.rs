use rand::{rngs::SmallRng, Rng, SeedableRng};

/// Internal node handle is just its index (u32) in the parallel arrays.
pub type NodeId = u32;
pub const NULL: NodeId = u32::MAX;

/// Order-statistic treap for documents keyed by score.
/// Supports insert, update (reinsert), delete, rank(score), and range_count(min,max).
pub struct DocIndex {
    left: Vec<NodeId>,
    right: Vec<NodeId>,
    priority: Vec<u32>,
    doc_id: Vec<u32>,
    score: Vec<i32>,
    size: Vec<u32>,
    root: NodeId,
    free: Vec<NodeId>,
    rng: SmallRng,
}

impl DocIndex {
    pub fn new() -> Self {
        Self {
            left: Vec::new(),
            right: Vec::new(),
            priority: Vec::new(),
            doc_id: Vec::new(),
            score: Vec::new(),
            size: Vec::new(),
            root: NULL,
            free: Vec::new(),
            rng: SmallRng::from_entropy(),
        }
    }

    fn alloc_node(&mut self, doc_id: u32, score: i32) -> NodeId {
        let id = if let Some(reuse) = self.free.pop() { reuse } else { self.left.len() as u32 };
        if id as usize == self.left.len() {
            self.left.push(NULL);
            self.right.push(NULL);
            self.priority.push(self.rng.gen());
            self.doc_id.push(doc_id);
            self.score.push(score);
            self.size.push(1);
        } else {
            let idx = id as usize;
            self.left[idx] = NULL;
            self.right[idx] = NULL;
            self.priority[idx] = self.rng.gen();
            self.doc_id[idx] = doc_id;
            self.score[idx] = score;
            self.size[idx] = 1;
        }
        id
    }

    #[inline]
    fn recalc(&mut self, id: NodeId) {
        if id == NULL { return; }
        let l = self.left[id as usize];
        let r = self.right[id as usize];
        let ls = if l != NULL { self.size[l as usize] } else { 0 };
        let rs = if r != NULL { self.size[r as usize] } else { 0 };
        self.size[id as usize] = 1 + ls + rs;
    }

    /// Insert new document. If doc already present (by doc_id) with previous score, remove old first.
    pub fn insert(&mut self, doc_id: u32, score: i32) {
        // For simplicity assume doc_id unique; caller ensures delete/update semantics.
        let node = self.alloc_node(doc_id, score);
        self.root = self.insert_rec(self.root, node);
    }

    fn insert_rec(&mut self, cur: NodeId, node: NodeId) -> NodeId {
        if cur == NULL { return node; }
        let node_score = self.score[node as usize];
        let cur_score = self.score[cur as usize];
        if node_score < cur_score || (node_score == cur_score && self.doc_id[node as usize] < self.doc_id[cur as usize]) {
            let left_new = self.insert_rec(self.left[cur as usize], node);
            self.left[cur as usize] = left_new;
            if self.priority[left_new as usize] > self.priority[cur as usize] {
                return self.rotate_right(cur);
            }
        } else {
            let right_new = self.insert_rec(self.right[cur as usize], node);
            self.right[cur as usize] = right_new;
            if self.priority[right_new as usize] > self.priority[cur as usize] {
                return self.rotate_left(cur);
            }
        }
        self.recalc(cur);
        cur
    }

    /// Update score for existing doc: remove old node and reinsert with new score.
    pub fn update(&mut self, doc_id: u32, old_score: i32, new_score: i32) {
        self.delete(doc_id, old_score);
        self.insert(doc_id, new_score);
    }

    pub fn delete(&mut self, doc_id: u32, score: i32) {
        self.root = self.delete_rec(self.root, doc_id, score);
    }

    fn delete_rec(&mut self, cur: NodeId, doc_id: u32, score: i32) -> NodeId {
        if cur == NULL { return NULL; }
        let cur_score = self.score[cur as usize];
        let cur_id = self.doc_id[cur as usize];
        if score < cur_score || (score == cur_score && doc_id < cur_id) {
            let left_new = self.delete_rec(self.left[cur as usize], doc_id, score);
            self.left[cur as usize] = left_new;
        } else if score > cur_score || (score == cur_score && doc_id > cur_id) {
            let right_new = self.delete_rec(self.right[cur as usize], doc_id, score);
            self.right[cur as usize] = right_new;
        } else {
            // Found
            let l = self.left[cur as usize];
            let r = self.right[cur as usize];
            if l == NULL && r == NULL {
                // reclaim
                self.free.push(cur);
                return NULL;
            } else if l == NULL {
                return r;
            } else if r == NULL {
                return l;
            } else {
                // Merge by rotating highest priority child up
                if self.priority[l as usize] > self.priority[r as usize] {
                    let new_root = self.rotate_right(cur);
                    let right_of_new_root = self.right[new_root as usize];
                    self.right[new_root as usize] = self.delete_rec(right_of_new_root, doc_id, score);
                    self.recalc(new_root);
                    return new_root;
                } else {
                    let new_root = self.rotate_left(cur);
                    let left_of_new_root = self.left[new_root as usize];
                    self.left[new_root as usize] = self.delete_rec(left_of_new_root, doc_id, score);
                    self.recalc(new_root);
                    return new_root;
                }
            }
        }
        self.recalc(cur);
        cur
    }

    fn rotate_left(&mut self, id: NodeId) -> NodeId {
        let r = self.right[id as usize];
        let rl = if r != NULL { self.left[r as usize] } else { NULL };
        self.right[id as usize] = rl;
        self.recalc(id);
        if r != NULL {
            self.left[r as usize] = id;
            self.recalc(r);
        }
        r
    }

    fn rotate_right(&mut self, id: NodeId) -> NodeId {
        let l = self.left[id as usize];
        let lr = if l != NULL { self.right[l as usize] } else { NULL };
        self.left[id as usize] = lr;
        self.recalc(id);
        if l != NULL {
            self.right[l as usize] = id;
            self.recalc(l);
        }
        l
    }

    /// Rank: number of documents with score <= target.
    pub fn rank(&self, target: i32) -> u32 {
        let mut cur = self.root;
        let mut acc = 0u32;
        while cur != NULL {
            let cur_score = self.score[cur as usize];
            let left = self.left[cur as usize];
            if target < cur_score {
                cur = left;
            } else {
                let left_size = if left != NULL { self.size[left as usize] } else { 0 };
                acc += 1 + left_size;
                cur = self.right[cur as usize];
            }
        }
        acc
    }

    /// Count documents with score in [min, max]. Assumes inclusive range, min <= max.
    pub fn range_count(&self, min: i32, max: i32) -> u32 {
        if min > max { return 0; }
        let rmax = self.rank(max);
        // For min-1 we need strict less than min
        let rmin_exclusive = if min == i32::MIN { 0 } else { self.rank(min - 1) };
        rmax - rmin_exclusive
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_insert_rank_range() {
        let mut idx = DocIndex::new();
        let data = vec![(0,10), (1,5), (2,20), (3,15), (4,30), (5,25)];
        for (id, score) in data.iter() {
            idx.insert(*id, *score);
        }
        // Scores: 5,10,15,20,25,30
        assert_eq!(idx.rank(4), 0, "rank(4) should be 0");
        assert_eq!(idx.rank(5), 1, "rank(5) should be 1");
        assert_eq!(idx.rank(10), 2, "rank(10) should be 2");
        assert_eq!(idx.rank(15), 3, "rank(15) should be 3");
        assert_eq!(idx.rank(20), 4, "rank(20) should be 4");
        assert_eq!(idx.rank(100), 6, "rank(100) should be 6");
        assert_eq!(idx.range_count(10,20), 3, "range [10,20] should contain 3 docs");
        assert_eq!(idx.range_count(5,25), 5, "range [5,25] should contain 5 docs");
    }

    #[test]
    fn update_and_delete() {
        let mut idx = DocIndex::new();
        idx.insert(1, 10);
        idx.insert(2, 20);
        idx.insert(3, 30);
        assert_eq!(idx.range_count(0,100), 3);
        // Update doc 2 from 20 to 5
        idx.update(2,20,5);
        // Scores now: 5,10,30
        assert_eq!(idx.rank(5), 1, "rank(5) should be 1");
        assert_eq!(idx.rank(10), 2, "rank(10) should be 2");
        assert_eq!(idx.range_count(5,10), 2, "range [5,10] should contain 2 docs");
        // Delete doc 1 (score 10)
        idx.delete(1,10);
        // Scores now: 5,30
        assert_eq!(idx.range_count(0,100), 2, "after delete total count should be 2");
        assert_eq!(idx.rank(6), 1, "rank(6) should be 1 after delete");
    }
}