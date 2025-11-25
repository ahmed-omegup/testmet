import { DocsIndex, Nullable } from "./docs-index";
import { DocId, Score } from "../types";


class DocsNode {
    score: Score; // value
    ids = new Set<DocId>; // docs at score
    sum: bigint; // subtree sum
    prio: number;
    count(): bigint { return BigInt(this.ids.size); }
    l: Nullable<DocsNode> = null;
    r: Nullable<DocsNode> = null;
    constructor(score: Score, ids: DocId[]) {
        this.score = score;
        ids.forEach(id => this.ids.add(id));
        this.sum = this.count();
        this.prio = Math.random();
    }
}


export class DocsTreap implements DocsIndex {
    root: Nullable<DocsNode> = null;

    private static sum(n: Nullable<DocsNode>): bigint { return n ? n.sum : 0n; }
    private static pull(n: DocsNode): void {
        n.sum = n.count() + DocsTreap.sum(n.l) + DocsTreap.sum(n.r);
    }

    private rotateRight(p: DocsNode, l: DocsNode) {
        p.l = l.r;
        const q = Object.assign(l, { r: p })
        DocsTreap.pull(p);
        DocsTreap.pull(q);
        return q;
    }
    private rotateLeft(p: DocsNode, r: DocsNode) {
        p.r = r.l;
        const q = Object.assign(r, { l: p })
        DocsTreap.pull(p);
        DocsTreap.pull(q);
        return q;
    }

    add(score: Score, id: DocId): void {
        this.root = this._update(this.root, score, n => {
            if (!n) return new DocsNode(score, [id]);
            n.ids.add(id);
            return n;
        });
    }
    private _delete(node: DocsNode): Nullable<DocsNode> {
        if (!node.l) return node.r;
        if (!node.r) return node.l;
        if (node.l.prio > node.r.prio) {
            const node2 = node = this.rotateRight(node, node.l);
            node.r = this._delete(node2.r);
        } else {
            const node2 = node = this.rotateLeft(node, node.r);
            node.l = this._delete(node2.l);
        }
        DocsTreap.pull(node);
        return node;
    }
    remove(score: Score, id: DocId): void {
        this.root = this._update(this.root, score, n => {
            if (!n) return n;
            n.ids.delete(id);
            if (n.ids.size === 0) {
                return this._delete(n);
            }
            return n;
        });
    }

    private _update(n: Nullable<DocsNode>, score: Score, handle: (n: DocsNode | null) => DocsNode | null): Nullable<DocsNode> {
        if (!n) return handle(n);
        if (score === n.score) {
            n = handle(n);
        } else if (score < n.score) {
            n.l = this._update(n.l, score, handle);
            if (n.l && (n.l.prio > n.prio)) n = this.rotateRight(n, n.l);
        } else {
            n.r = this._update(n.r, score, handle);
            if (n.r && (n.r.prio > n.prio)) n = this.rotateLeft(n, n.r);
        }
        if (n) DocsTreap.pull(n);
        return n;
    }

    // prefix sum of scores strictly less than score
    rank(score: Score): bigint {
        let cur = this.root;
        let res = 0n;
        while (cur) {
            if (score <= cur.score) {
                cur = cur.l;
            } else {
                res += DocsTreap.sum(cur.l) + cur.count();
                cur = cur.r;
            }
        }
        return res;
    }

    // prefix sum of scores less than or equal to score
    countAtMost(score: Score): bigint {
        let cur = this.root;
        let res = 0n;
        while (cur) {
            if (score < cur.score) {
                cur = cur.l;
            } else {
                res += DocsTreap.sum(cur.l) + cur.count();
                cur = cur.r;
            }
        }
        return res;
    }
    getAtRank(rank: bigint): Nullable<[score: Score, ids: Set<DocId>, position: bigint]> {
        let cur = this.root;;
        let r = rank;
        while (cur) {
            const leftSum = DocsTreap.sum(cur.l);
            if (r < leftSum) {
                cur = cur.l;
            } else if (r < leftSum + cur.count()) {
                return [cur.score, cur.ids, r - leftSum];
            } else {
                r -= leftSum + cur.count();
                cur = cur.r;
            }
        }
        return null;
    }

    collectRange(min: Score, max: Score, limit: bigint): DocId[] {
        const out: DocId[] = [];
        if (limit <= 0n) return out;
        const cap = limit > BigInt(Number.MAX_SAFE_INTEGER) ? Number.MAX_SAFE_INTEGER : Number(limit);
        this._collectRange(this.root, min, max, cap, out);
        return out;
    }

    private _collectRange(node: Nullable<DocsNode>, min: Score, max: Score, remaining: number, out: DocId[]): number {
        if (!node || remaining <= 0) return remaining;
        if (min < node.score) {
            remaining = this._collectRange(node.l, min, max, remaining, out);
        }
        if (remaining <= 0) return 0;
        if (node.score >= min && node.score <= max) {
            for (const docId of node.ids) {
                out.push(docId);
                remaining -= 1;
                if (remaining <= 0) return 0;
            }
        }
        if (remaining <= 0) return 0;
        if (node.score < max) {
            remaining = this._collectRange(node.r, min, max, remaining, out);
        }
        return remaining;
    }
}