// Dynamic point-stabbing retrieval over queries with document-count-defined ranges
// Query q = (a=minValue, k=numDocs) covers values starting at a until it has seen k documents.
// Given dynamic docs[x] and dynamic queries, efficiently retrieve all queries that currently cover a value v.
//
// Core idea:
// - Maintain dynamic prefix sums P(i) over docs with a treap keyed by value (sparse, no coordinate compression).
// - Maintain queries in a treap keyed by a. Each node stores a lazy add (affecting the entire subtree)
//   representing increases in P(a-1) due to document updates at smaller t, plus a per-node multiset of queries.
// - For a value v, compute cutoff = P(v-1). A query (a,k) matches v iff a <= v and (P(a-1)+k) > cutoff.
// - We support: document update at t by Δ via split-by-key (a > t) and apply a single lazy add to that suffix.
// - Retrieval: split by a <= v, traverse with pruning using subtreeMax to output only matching queries, then merge.
//
// Complexities (Q queries, V distinct values):
// - addDocument(t, Δ): O(log V + log Q)
// - addQuery(a,k): O(log V + log Q)
// - removeQuery(id): O(log Q)
// - getQueriesCovering(v): O(log V + log Q + matches)

type Nullable<T> = T | null;


// -------------------- Docs treap (dynamic prefix sums) --------------------
let count = 0;
class DocsNode {
	key: number; // value
	cnt: bigint; // docs at key
	sum: bigint; // subtree sum
	prio: number;
	l: Nullable<DocsNode> = null;
	r: Nullable<DocsNode> = null;
	constructor(key: number, cnt: bigint) {
		this.key = key;
		this.cnt = cnt;
		this.sum = cnt;
		this.prio = Math.random();
	}
}

class DocsTreap {
	root: Nullable<DocsNode> = null;

	private static sum(n: Nullable<DocsNode>): bigint { return n ? n.sum : 0n; }
	private static pull(n: DocsNode): void {
		n.sum = n.cnt + DocsTreap.sum(n.l) + DocsTreap.sum(n.r);
	}

	private rotateRight(p: DocsNode): DocsNode {
		const q = p.l!;
		p.l = q.r;
		q.r = p;
		DocsTreap.pull(p);
		DocsTreap.pull(q);
		return q;
	}
	private rotateLeft(p: DocsNode): DocsNode {
		const q = p.r!;
		p.r = q.l;
		q.l = p;
		DocsTreap.pull(p);
		DocsTreap.pull(q);
		return q;
	}

	update(key: number, delta: bigint): void {
		this.root = this._update(this.root, key, delta);
	}

	private _update(n: Nullable<DocsNode>, key: number, delta: bigint): DocsNode {
		if (!n) return new DocsNode(key, delta);
		if (key === n.key) {
			n.cnt += delta;
		} else if (key < n.key) {
			n.l = this._update(n.l, key, delta);
			if (n.l && (n.l.prio > n.prio)) n = this.rotateRight(n);
		} else {
			n.r = this._update(n.r, key, delta);
			if (n.r && (n.r.prio > n.prio)) n = this.rotateLeft(n);
		}
		DocsTreap.pull(n);
		return n;
	}

	// prefix sum of keys strictly less than key
	prefixSum(key: number): bigint {
		let cur = this.root;
		let res = 0n;
		while (cur) {
			if (key <= cur.key) {
				cur = cur.l;
			} else {
				res += DocsTreap.sum(cur.l) + cur.cnt;
				cur = cur.r;
			}
		}
		return res;
	}
}

// -------------------- Queries treap (keyed by a=minValue) --------------------

type QueryId = number;

interface QueryInfo { id: QueryId; a: number; k: bigint; max: number; }

class QueriesNode {
	key: number; // a
	prio: number;
	add: bigint; // lazy add applied to entire subtree (effective score shift)
	// Local multiset of queries at this exact 'a', storing base scores (effective - accumulated adds here)
	localScores: bigint[] = []; // sorted ascending
	itemsByScore: Map<bigint, Set<QueryId>> = new Map();
	baseLocalMax: bigint | null = null; // max of localScores (base, no add)
	subtreeMax: bigint | null; // add + max(baseLocalMax, left.subtreeMax, right.subtreeMax)
	// Track per-node and per-subtree maximum of query.max (upper bound on value coverage)
	localMaxCap: number = Number.NEGATIVE_INFINITY;
	subtreeMaxCap: number; // max(localMaxCap, left.subtreeMaxCap, right.subtreeMaxCap)
	// frequency map to maintain localMaxCap efficiently
	localMaxFreq: Map<number, number> = new Map();
	l: Nullable<QueriesNode> = null;
	r: Nullable<QueriesNode> = null;
	constructor(key: number) {
		this.key = key;
		this.prio = Math.random();
		this.add = 0n;
		this.subtreeMax = null;
		this.subtreeMaxCap = Number.NEGATIVE_INFINITY;
	}
}

const max = (a: bigint | null, b: bigint | null): bigint | null => {
	if (a === null) return b;
	if (b === null) return a;
	return (a > b) ? a : b;
}

class QueriesTreap {
	root: Nullable<QueriesNode> = null;

	private static negInf = Number.NEGATIVE_INFINITY;

	private static getSubMax(n: Nullable<QueriesNode>): bigint | null { return n ? n.subtreeMax : null; }
	private static getSubCap(n: Nullable<QueriesNode>): number { return n ? n.subtreeMaxCap : QueriesTreap.negInf; }

	private static pull(n: QueriesNode): void {
		// subtreeMax is node.add + max(localBaseMax, left.subtreeMax, right.subtreeMax)
		const leftMax = QueriesTreap.getSubMax(n.l);
		const rightMax = QueriesTreap.getSubMax(n.r);
		const local = n.baseLocalMax;
		const mx = max(local, max(leftMax, rightMax));
		n.subtreeMax = (mx === null) ? null : n.add + mx;
		// subtreeMaxCap aggregates max cap across subtree
		const leftCap = QueriesTreap.getSubCap(n.l);
		const rightCap = QueriesTreap.getSubCap(n.r);
		n.subtreeMaxCap = Math.max(n.localMaxCap, Math.max(leftCap, rightCap));
	}

	private rotateRight(p: QueriesNode): QueriesNode {
		const q = p.l!;
		p.l = q.r;
		q.r = p;
		QueriesTreap.pull(p);
		QueriesTreap.pull(q);
		return q;
	}
	private rotateLeft(p: QueriesNode): QueriesNode {
		const q = p.r!;
		p.r = q.l;
		q.l = p;
		QueriesTreap.pull(p);
		QueriesTreap.pull(q);
		return q;
	}

	private upperBound(arr: bigint[], x: bigint): number {
		// first index with arr[i] >= x
		let lo = 0, hi = arr.length;
		while (lo < hi) {
			const mid = (lo + hi) >>> 1;
			if (arr[mid] < x) lo = mid + 1; else hi = mid;
		}
		return lo;
	}

	private insertIntoLocal(n: QueriesNode, id: QueryId, baseScore: bigint, maxCap: number): void {
		const idx = this.upperBound(n.localScores, baseScore); // stable for floats
		n.localScores.splice(idx, 0, baseScore);
		let set = n.itemsByScore.get(baseScore);
		if (!set) { set = new Set(); n.itemsByScore.set(baseScore, set); }
		set.add(id);
		n.baseLocalMax = n.localScores.length ? n.localScores[n.localScores.length - 1] : null;
		// update max cap freq
		n.localMaxFreq.set(maxCap, (n.localMaxFreq.get(maxCap) ?? 0) + 1);
		if (maxCap > n.localMaxCap) n.localMaxCap = maxCap;
	}

	private removeFromLocal(n: QueriesNode, id: QueryId, baseScore: bigint, maxCap: number): boolean {
		const set = n.itemsByScore.get(baseScore);
		if (!set || !set.delete(id)) return false;
		if (set.size === 0) n.itemsByScore.delete(baseScore);
		// remove one occurrence of baseScore from localScores
		const idx = this.findOneIndex(n.localScores, baseScore);
		if (idx >= 0) n.localScores.splice(idx, 1);
		n.baseLocalMax = n.localScores.length ? n.localScores[n.localScores.length - 1] : null;
		// update max cap freq
		const prev = n.localMaxFreq.get(maxCap) ?? 0;
		if (prev <= 1) {
			n.localMaxFreq.delete(maxCap);
			if (n.localMaxCap === maxCap) {
				// recompute current localMaxCap
				let m = QueriesTreap.negInf;
				for (const cap of n.localMaxFreq.keys()) if (cap > m) m = cap;
				n.localMaxCap = m;
			}
		} else {
			n.localMaxFreq.set(maxCap, prev - 1);
		}
		return true;
	}

	private findOneIndex(arr: bigint[], x: bigint): number {
		// find any index with arr[i] === x (arr sorted, but duplicates possible)
		let lo = 0, hi = arr.length - 1;
		while (lo <= hi) {
			const mid = (lo + hi) >>> 1;
			if (arr[mid] === x) return mid;
			if (arr[mid] < x) lo = mid + 1; else hi = mid - 1;
		}
		return -1;
	}

	// Range add Δ to all nodes with key > t: implemented via split and applyAdd at the right root
	rangeAddKeysGreaterThan(t: number, delta: bigint): void {
		const [L, R] = this.splitByKey(this.root, t);
		if (R) {
			R.add += delta;
			if (R.subtreeMax !== null) R.subtreeMax += delta;
		}
		this.root = this.merge(L, R);
	}

	// Insert a query at key=a with effectiveScore = P(a-1)+k and max cap
	insert(a: number, id: QueryId, effectiveScore: bigint, maxCap: number): void {
		this.root = this._insert(this.root, a, id, effectiveScore, maxCap, 0n);
	}

	private _insert(n: Nullable<QueriesNode>, a: number, id: QueryId, effectiveScore: bigint, maxCap: number, accAdd: bigint): QueriesNode {
		if (!n) {
			const node = new QueriesNode(a);
			const baseScore = effectiveScore - accAdd - node.add; // node.add is 0 here
			this.insertIntoLocal(node, id, baseScore, maxCap);
			QueriesTreap.pull(node);
			return node;
		}
		if (a === n.key) {
			const baseScore = effectiveScore - accAdd - n.add;
			this.insertIntoLocal(n, id, baseScore, maxCap);
			QueriesTreap.pull(n);
			return n;
		}
		if (a < n.key) {
			n.l = this._insert(n.l, a, id, effectiveScore, maxCap, accAdd + n.add);
			if (n.l && n.l.prio > n.prio) n = this.rotateRight(n);
		} else {
			n.r = this._insert(n.r, a, id, effectiveScore, maxCap, accAdd + n.add);
			if (n.r && n.r.prio > n.prio) n = this.rotateLeft(n);
		}
		QueriesTreap.pull(n);
		return n;
	}

	// Remove a query by (a, id, baseScore, maxCap)
	remove(a: number, id: QueryId, baseScore: bigint, maxCap: number): void {
		this.root = this._remove(this.root, a, id, baseScore, maxCap);
	}

	private _remove(n: Nullable<QueriesNode>, a: number, id: QueryId, baseScore: bigint, maxCap: number): Nullable<QueriesNode> {
		if (!n) return null;
		if (a === n.key) {
			// remove from local; if local empty and one child exists, rotate to remove node
			this.removeFromLocal(n, id, baseScore, maxCap);
		} else if (a < n.key) {
			n.l = this._remove(n.l, a, id, baseScore, maxCap);
		} else {
			n.r = this._remove(n.r, a, id, baseScore, maxCap);
		}
		// If current node has no local items and one child missing, collapse via rotation/merge
		if (n.baseLocalMax === null && !n.l && !n.r) {
			return null;
		}
		// If empty local but two children present, keep node as structural with add; it's fine.
		QueriesTreap.pull(n);
		return n;
	}

	// Collect queries with key <= v and effective score > cutoff, and predicate over id (e.g., max >= v)
	collectForValue(v: number, cutoff: bigint, isAllowed: (id: QueryId) => boolean, visit: (id: QueryId) => void): void {
		// Split by key to isolate ≤ v
		const [L, R] = this.splitByKey(this.root, v);
		this._collect(L, 0n, cutoff, v, isAllowed, visit);
		this.root = this.merge(L, R);
	}

	private _collect(n: Nullable<QueriesNode>, accAdd: bigint, cutoff: bigint, v: number, isAllowed: (id: QueryId) => boolean, visit: (id: QueryId) => void): void {
		count ++
		if (!n) return;
		// prune by max-cap first
		if (n.subtreeMaxCap < v) return;
		const effSubMax = (n.subtreeMax === null) ? null : n.subtreeMax + accAdd;
		if (effSubMax === null || effSubMax <= cutoff) return;
		const accHere = accAdd + n.add;
		// Visit local items: need baseScore > cutoff - accHere (strict inequality)
		const thresholdBase = cutoff - accHere;
		if (n.localScores.length) {
			// upperBound gives first >= thresholdBase, but we need strictly > cutoff
			// So use thresholdBase + 1 to get first > thresholdBase
			const idx = this.upperBound(n.localScores, thresholdBase + 1n);
			for (let i = idx; i < n.localScores.length; i++) {
				const base = n.localScores[i];
				const set = n.itemsByScore.get(base);
				if (!set) continue;
				for (const id of set) if (isAllowed(id)) visit(id);
			}
		}
		// Recurse
		this._collect(n.l, accHere, cutoff, v, isAllowed, visit);
		this._collect(n.r, accHere, cutoff, v, isAllowed, visit);
	}

	// Treap split by key: returns [<= key, > key]
	private splitByKey(n: Nullable<QueriesNode>, key: number): [Nullable<QueriesNode>, Nullable<QueriesNode>] {
		if (!n) return [null, null];
		if (key < n.key) {
			const [l1, l2] = this.splitByKey(n.l, key);
			n.l = l2;
			QueriesTreap.pull(n);
			return [l1, n];
		} else {
			const [r1, r2] = this.splitByKey(n.r, key);
			n.r = r1;
			QueriesTreap.pull(n);
			return [n, r2];
		}
	}

	private merge(a: Nullable<QueriesNode>, b: Nullable<QueriesNode>): Nullable<QueriesNode> {
		if (!a || !b) return a ? a : b;
		if (a.prio > b.prio) {
			a.r = this.merge(a.r, b);
			QueriesTreap.pull(a);
			return a;
		} else {
			b.l = this.merge(a, b.l);
			QueriesTreap.pull(b);
			return b;
		}
	}
}

// -------------------- Public API --------------------

export class DynamicRangeQueries {
	private docs = new DocsTreap();
	private queries = new QueriesTreap();
	private nextId: number = 1;
	private idToQuery: Map<QueryId, QueryInfo> = new Map();
	// baseScore stored at insertion for fast removal
	private idToBaseScore: Map<QueryId, bigint> = new Map();

	// Update document count at a specific value by delta (can be negative)
	addDocument(value: number, delta = 1n): void {
		if (delta === 0n) return;
		this.docs.update(value, delta);
		// All queries with a > value increase their score by delta
		this.queries.rangeAddKeysGreaterThan(value, delta);
	}

	// Add a query (a=minValue, k=numDocs, max=upper bound on value). Returns query id.
	addQuery(a: number, k: bigint, max = Number.POSITIVE_INFINITY): QueryId {
		const id = this.nextId++;
		const effectiveScore = this.docs.prefixSum(a) + k;
		this.queries.insert(a, id, effectiveScore, max);
		// We need to store baseScore used at the node for deletion. Compute it by re-deriving via a targeted lookup.
		// Easiest: store as effectiveScore minus current accumulated add at position a.
		// We can compute accumulated add at position a by walking the treap without modifying it.
		const baseScore = this.getBaseScoreAtKeyForValue(a, effectiveScore);
		this.idToBaseScore.set(id, baseScore);
		this.idToQuery.set(id, { id, a, k, max });
		return id;
	}

	// Internal: compute baseScore = effectiveScore - accumulatedAddAtPosition(a)
	private getBaseScoreAtKeyForValue(a: number, effectiveScore: bigint): bigint {
		let n = this.queries.root;
		let accAdd = 0n;
		while (n) {
			if (a === n.key) {
				accAdd += n.add;
				break;
			}
			accAdd += n.add;
			n = (a < n.key) ? n.l : n.r;
		}
		return effectiveScore - accAdd;
	}

	// Remove a query by id. Returns true if removed.
	removeQuery(id: QueryId): boolean {
		const info = this.idToQuery.get(id);
		if (!info) return false;
		const baseScore = this.idToBaseScore.get(id);
		if (baseScore === undefined) return false;
		this.queries.remove(info.a, id, baseScore, info.max);
		this.idToBaseScore.delete(id);
		this.idToQuery.delete(id);
		return true;
	}

	// Retrieve all queries (ids) that currently cover value v.
	// If you want full (a,k), map over ids via getQueryInfo.
	getQueriesCovering(v: number): QueryId[] {
		const cutoff = this.docs.prefixSum(v);
		const out: QueryId[] = [];
		this.queries.collectForValue(
			v,
			cutoff,
			(id) => {
				const qi = this.idToQuery.get(id);
				return !!qi && qi.max >= v;
			},
			(id) => out.push(id)
		);
		return out;
	}

	getQueryInfo(id: QueryId): QueryInfo | undefined { return this.idToQuery.get(id); }
}

// -------------------- Minimal sanity check (optional) --------------------

// Execute quick self-test when run directly (node -r ts-node/register dynqueries.ts)
const dyn = new DynamicRangeQueries();

// docs: values 1..10 with counts
dyn.addDocument(1, 2n); // P(1)=2
dyn.addDocument(3, 1n); // P(3)=3
dyn.addDocument(5, 4n); // P(5)=7

// queries
const q1 = dyn.addQuery(1, 1n); // starts at 1, needs 1 doc => covers value 1
const q2 = dyn.addQuery(1, 3n); // needs 3 docs => accum across 1,3 => covers up to value 3
const q3 = dyn.addQuery(2, 4n); // from 2, needs 4 docs => docs at 3(1)+5(4)=5 => covers to 5
const q4 = dyn.addQuery(6, 1n); // from 6, needs 1 doc => covers 6 only if docs at 6+

console.log('Covering 1:', dyn.getQueriesCovering(1).map(id => dyn.getQueryInfo(id)));
console.log('Covering 3:', dyn.getQueriesCovering(3).map(id => dyn.getQueryInfo(id)));
console.log('Covering 5:', dyn.getQueriesCovering(5).map(id => dyn.getQueryInfo(id)));

// Update docs to affect suffix queries
dyn.addDocument(2, 1n); // increases P(a-1) for a>2 by +1

console.log('After doc at 2, covering 2:', dyn.getQueriesCovering(2).map(id => dyn.getQueryInfo(id)));
console.log('After doc at 2, covering 6:', dyn.getQueriesCovering(6).map(id => dyn.getQueryInfo(id)));

console.log(new Date)
dyn.addQuery(1000000, 20000000n)
for(let i = 0; i < 300000; i++) {
	dyn.addQuery(10000000+i, 1n)
}

count = 0;
dyn.addDocument(15000000);

console.log(new Date)
console.log(dyn.getQueriesCovering(20000000));
console.log(new Date)


console.log('Node visits during last query:', count);