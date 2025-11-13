use rand::Rng;

// -------------------- Docs Treap (dynamic prefix sums) --------------------

pub struct DocsNode {
    pub key: f64,           // value
    pub cnt: i64,           // docs at key
    pub sum: i64,           // subtree sum
    pub prio: f64,
    pub left: Option<Box<DocsNode>>,
    pub right: Option<Box<DocsNode>>,
}

impl DocsNode {
    pub fn new(key: f64, cnt: i64) -> Self {
        Self {
            key,
            cnt,
            sum: cnt,
            prio: rand::thread_rng().gen(),
            left: None,
            right: None,
        }
    }

    pub fn sum(node: &Option<Box<DocsNode>>) -> i64 {
        node.as_ref().map_or(0, |n| n.sum)
    }

    pub fn pull(&mut self) {
        self.sum = self.cnt + Self::sum(&self.left) + Self::sum(&self.right);
    }
}

pub struct DocsTreap {
    pub root: Option<Box<DocsNode>>,
}

impl DocsTreap {
    pub fn new() -> Self {
        Self { root: None }
    }

    pub fn update(&mut self, key: f64, delta: i64) {
        self.root = Self::update_node(self.root.take(), key, delta);
    }

    fn update_node(node: Option<Box<DocsNode>>, key: f64, delta: i64) -> Option<Box<DocsNode>> {
        let mut node = match node {
            None => return Some(Box::new(DocsNode::new(key, delta))),
            Some(n) => n,
        };

        if (key - node.key).abs() < 1e-9 {
            node.cnt += delta;
        } else if key < node.key {
            node.left = Self::update_node(node.left.take(), key, delta);
            if node.left.as_ref().map_or(false, |l| l.prio > node.prio) {
                return Some(Self::rotate_right(node));
            }
        } else {
            node.right = Self::update_node(node.right.take(), key, delta);
            if node.right.as_ref().map_or(false, |r| r.prio > node.prio) {
                return Some(Self::rotate_left(node));
            }
        }
        node.pull();
        Some(node)
    }

    fn rotate_right(mut p: Box<DocsNode>) -> Box<DocsNode> {
        let mut q = p.left.take().unwrap();
        p.left = q.right.take();
        p.pull();
        q.right = Some(p);
        q.pull();
        q
    }

    fn rotate_left(mut p: Box<DocsNode>) -> Box<DocsNode> {
        let mut q = p.right.take().unwrap();
        p.right = q.left.take();
        p.pull();
        q.left = Some(p);
        q.pull();
        q
    }

    // prefix sum of keys strictly less than key
    pub fn prefix_sum(&self, key: f64) -> i64 {
        let mut cur = self.root.as_ref();
        let mut res = 0i64;
        while let Some(node) = cur {
            if key <= node.key {
                cur = node.left.as_ref();
            } else {
                res += DocsNode::sum(&node.left) + node.cnt;
                cur = node.right.as_ref();
            }
        }
        res
    }
}
