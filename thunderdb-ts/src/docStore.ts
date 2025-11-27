import { open, RootDatabase } from 'lmdb';
import os from 'node:os';
import path from 'node:path';
import fs from 'node:fs';
import { DocId, DocStateDom } from './limit-index/types';

export type LmdbDurability = 'durable' | 'relaxed';

export interface LmdbDocStoreOptions {
  directory?: string;
  durability?: LmdbDurability;
}

function resolveOptions(input?: string | LmdbDocStoreOptions): { directory: string; durability: LmdbDurability } {
  const defaultDurability: LmdbDurability = process.env.THUNDERDB_DOCSTORE_DURABILITY === 'relaxed' ? 'relaxed' : 'durable';
  if (!input || typeof input === 'string') {
    const directory = input ?? path.join(os.tmpdir(), `thunderdb-docstore-${process.pid}-${Date.now()}`);
    return { directory, durability: defaultDurability };
  }
  return {
    directory: input.directory ?? path.join(os.tmpdir(), `thunderdb-docstore-${process.pid}-${Date.now()}`),
    durability: input.durability ?? defaultDurability,
  };
}

export class LmdbDocStore<DocState extends DocStateDom> {
  private db: RootDatabase<DocState>;
  private directory: string;

  constructor(options?: string | LmdbDocStoreOptions) {
    const resolved = resolveOptions(options);
    this.directory = resolved.directory;
    fs.mkdirSync(this.directory, { recursive: true });
    const relaxed = resolved.durability === 'relaxed';
    this.db = open<DocState>({
      path: this.directory,
      compression: true,
      mapSize: 2 * 1024 * 1024 * 1024, // 2 GiB default, adjustable later
      noSync: relaxed,
      noMetaSync: relaxed,
      noMemInit: relaxed,
    });
  }

  put(id: DocId, state: DocState): void {
    this.db.putSync(id.toString(), state);
  }

  putMany(entries: ReadonlyArray<[DocId, DocState]>): void {
    if (entries.length === 0) return;
    this.db.transactionSync(() => {
      for (const [id, state] of entries) {
        this.db.putSync(id.toString(), state);
      }
    });
  }

  delete(id: DocId): void {
    this.db.removeSync(id.toString());
  }

  get(id: DocId): DocState | undefined {
    return this.db.get(id.toString());
  }

  async getMany(ids: DocId[]): Promise<Map<DocId, DocState>> {
    if (ids.length === 0) return new Map();
    const keys = ids.map(id => id.toString());
    const values = await this.db.getMany(keys) as (DocState | undefined)[];
    const map = new Map<DocId, DocState>();
    for (let i = 0; i < ids.length; i += 1) {
      const value = values[i];
      if (value) {
        map.set(ids[i]!, value);
      }
    }
    return map;
  }

  clear(): void {
    this.db.clearSync();
  }

  path(): string {
    return this.directory;
  }
}
