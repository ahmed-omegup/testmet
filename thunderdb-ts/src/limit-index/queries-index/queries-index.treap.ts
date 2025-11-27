import { Nullable } from "../docs-index.ts/docs-index";
import { QueryId } from "../types";
import { CollectDebugConfig, QueriesIndex } from "./queries-index";


class QueriesNode {
	key: number; // a
	prio: number;
	add: bigint; // lazy add applied to entire subtree (effective score shift)
	localAdd: bigint = 0n; // accumulated add applied to locals
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
export class QueriesTreap implements QueriesIndex {
	root: Nullable<QueriesNode> = null;

	private static negInf = Number.NEGATIVE_INFINITY;

	private static getSubMax(n: Nullable<QueriesNode>): bigint | null { return n ? n.subtreeMax : null; }
	private static getSubCap(n: Nullable<QueriesNode>): number { return n ? n.subtreeMaxCap : QueriesTreap.negInf; }

	private static pull(n: QueriesNode): void {
		// subtreeMax is node.add + max(localBaseMax, left.subtreeMax, right.subtreeMax)
		const leftMax = QueriesTreap.getSubMax(n.l);
		const rightMax = QueriesTreap.getSubMax(n.r);
		const local = (n.baseLocalMax === null) ? null : n.baseLocalMax + n.localAdd;
		const mx = max(local, max(leftMax, rightMax));
		n.subtreeMax = (mx === null) ? null : n.add + mx;
		// subtreeMaxCap aggregates max cap across subtree
		const leftCap = QueriesTreap.getSubCap(n.l);
		const rightCap = QueriesTreap.getSubCap(n.r);
		n.subtreeMaxCap = Math.max(n.localMaxCap, Math.max(leftCap, rightCap));
	}

	private static push(n: Nullable<QueriesNode>): void {
		if (!n || n.add === 0n) return;
		if (n.l) {
			n.l.add += n.add;
			if (n.l.subtreeMax !== null) n.l.subtreeMax += n.add;
		}
		if (n.r) {
			n.r.add += n.add;
			if (n.r.subtreeMax !== null) n.r.subtreeMax += n.add;
		}
		n.localAdd += n.add;
		n.add = 0n;
	}

	private rotateRight(p: QueriesNode, l: QueriesNode) {
		QueriesTreap.push(p);
		QueriesTreap.push(l);
		p.l = l.r;
        const q = Object.assign(l, { r: p })
		QueriesTreap.pull(p);
		QueriesTreap.pull(q);
		return q;
	}
	private rotateLeft(p: QueriesNode, r: QueriesNode) {
		QueriesTreap.push(p);
		QueriesTreap.push(r);
		p.r = r.l;
        const q = Object.assign(r, { l: p })
		QueriesTreap.pull(p);
		QueriesTreap.pull(q);
		return q;
	}

	private upperBound(arr: bigint[], x: bigint): number {
		// first index with arr[i] >= x
		let lo = 0, hi = arr.length;
		while (lo < hi) {
			const mid = (lo + hi) >>> 1;
			if (arr[mid]! < x) lo = mid + 1; else hi = mid;
		}
		return lo;
	}

	private insertIntoLocal(n: QueriesNode, id: QueryId, baseScore: bigint, maxCap: number): void {
		const idx = this.upperBound(n.localScores, baseScore); // stable for floats
		n.localScores.splice(idx, 0, baseScore);
		let set = n.itemsByScore.get(baseScore);
		if (!set) { set = new Set(); n.itemsByScore.set(baseScore, set); }
		set.add(id);
		n.baseLocalMax = n.localScores.length ? n.localScores[n.localScores.length - 1]! : null;
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
		n.baseLocalMax = n.localScores.length ? n.localScores[n.localScores.length - 1]! : null;
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
			if (arr[mid]! < x) lo = mid + 1; else hi = mid - 1;
		}
		return -1;
	}

	// Range add Δ to all nodes with key > t: implemented via split and lazy add on the right root
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
			const baseScore = effectiveScore - accAdd;
			this.insertIntoLocal(node, id, baseScore, maxCap);
			QueriesTreap.pull(node);
			return node;
		}
		if (a === n.key) {
			const baseScore = effectiveScore - accAdd - n.add - n.localAdd;
			this.insertIntoLocal(n, id, baseScore, maxCap);
			QueriesTreap.pull(n);
			return n;
		}
		if (a < n.key) {
			n.l = this._insert(n.l, a, id, effectiveScore, maxCap, accAdd + n.add);
			if (n.l && n.l.prio > n.prio) n = this.rotateRight(n, n.l);
		} else {
			n.r = this._insert(n.r, a, id, effectiveScore, maxCap, accAdd + n.add);
			if (n.r && n.r.prio > n.prio) n = this.rotateLeft(n, n.r);
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
		QueriesTreap.push(n);
		if (a === n.key) {
			// remove from local; if local empty and one child exists, rotate to remove node
			this.removeFromLocal(n, id, baseScore, maxCap);
		} else if (a < n.key) {
			n.l = this._remove(n.l, a, id, baseScore, maxCap);
		} else {
			n.r = this._remove(n.r, a, id, baseScore, maxCap);
		}
		// If current node has no local items and one child missing, collapse via rotation/merge
		if (n.baseLocalMax === null) {
			return this.merge(n.l, n.r);
		}
		QueriesTreap.pull(n);
		return n;
	}

	// Collect queries with key <= v and effective score > cutoff, and predicate over id (e.g., max >= v)
	collectForValue(v: number, cutoff: bigint, isAllowed: (id: QueryId) => boolean, visit: (id: QueryId) => void, debug?: CollectDebugConfig): void {
		this._collectTraverse(this.root, 0n, cutoff, v, isAllowed, visit, debug);
	}

	private _collectTraverse(n: Nullable<QueriesNode>, accAdd: bigint, cutoff: bigint, v: number, isAllowed: (id: QueryId) => boolean, visit: (id: QueryId) => void, debug?: CollectDebugConfig): void {
		if (!n) return;
		if (n.subtreeMaxCap < v) {
			this.debugPrune('maxCap', n, accAdd, cutoff, v, debug);
			return;
		}
		const effSubMax = (n.subtreeMax === null) ? null : n.subtreeMax + accAdd;
		if (effSubMax === null || effSubMax <= cutoff) {
			this.debugPrune('subtreeMax', n, accAdd, cutoff, v, debug);
			return;
		}
		const accForChildren = accAdd + n.add;
		const accHere = accForChildren + n.localAdd;
		if (n.key > v) {
			this._collectTraverse(n.l, accForChildren, cutoff, v, isAllowed, visit, debug);
			return;
		}
		this._collectTraverse(n.l, accForChildren, cutoff, v, isAllowed, visit, debug);
		this.visitLocalQueries(n, accHere, cutoff, v, isAllowed, visit);
		this._collectTraverse(n.r, accForChildren, cutoff, v, isAllowed, visit, debug);
	}

	private visitLocalQueries(n: QueriesNode, accHere: bigint, cutoff: bigint, v: number, isAllowed: (id: QueryId) => boolean, visit: (id: QueryId) => void): void {
		if (!n.localScores.length) return;
		if (n.key > v) return;
		const thresholdBase = cutoff - accHere;
		let i = this.upperBound(n.localScores, thresholdBase + 1n);
		while (i < n.localScores.length) {
			const base = n.localScores[i]!;
			const set = n.itemsByScore.get(base);
			if (set) {
				for (const id of set) if (isAllowed(id)) visit(id);
			}
			while (i < n.localScores.length && n.localScores[i] === base) i++;
		}
	}

	private debugPrune(reason: string, n: QueriesNode, accAdd: bigint, cutoff: bigint, v: number, debug?: CollectDebugConfig): void {
		if (!debug) return;
		if (!this.subtreeContainsQuery(n, debug.queryId)) return;
		const effSubMax = (n.subtreeMax === null) ? null : n.subtreeMax + accAdd;
		debug.onPrune({
			reason,
			nodeKey: n.key,
			nodeAdd: n.add.toString(),
			localAdd: n.localAdd.toString(),
			subtreeMax: n.subtreeMax ? n.subtreeMax.toString() : null,
			subtreeMaxCap: n.subtreeMaxCap,
			effSubMax: effSubMax ? effSubMax.toString() : null,
			cutoff: cutoff.toString(),
			value: v,
		});
	}

	private subtreeContainsQuery(n: Nullable<QueriesNode>, id: QueryId): boolean {
		if (!n) return false;
		for (const set of n.itemsByScore.values()) {
			if (set.has(id)) return true;
		}
		return this.subtreeContainsQuery(n.l, id) || this.subtreeContainsQuery(n.r, id);
	}

	// Treap split by key: returns [<= key, > key]
	private splitByKey(n: Nullable<QueriesNode>, key: number): [Nullable<QueriesNode>, Nullable<QueriesNode>] {
		if (!n) return [null, null];
		QueriesTreap.push(n);
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
		QueriesTreap.push(a);
		QueriesTreap.push(b);
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

	accumulatedAddAtKey(a: number): bigint {
		let n = this.root;
		let acc = 0n;
		while (n) {
			acc += n.add;
			if (a === n.key) {
				acc += n.localAdd;
				break;
			}
			n = (a < n.key) ? n.l : n.r;
		}
		return acc;
	}
}

