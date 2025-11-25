import { open, RootDatabase } from 'lmdb';
import os from 'node:os';
import path from 'node:path';
import fs from 'node:fs';
import { DocId, DocStateDom } from './limit-index/types';

export class LmdbDocStore<DocState extends DocStateDom> {
  private db: RootDatabase<DocState>;
  private directory: string;

  constructor(dir?: string) {
    this.directory = dir ?? path.join(os.tmpdir(), `thunderdb-docstore-${process.pid}-${Date.now()}`);
    fs.mkdirSync(this.directory, { recursive: true });
    this.db = open<DocState>({
      path: this.directory,
      compression: true,
      mapSize: 2 * 1024 * 1024 * 1024, // 2 GiB default, adjustable later
    });
  }

  put(id: DocId, state: DocState): void {
    this.db.putSync(id.toString(), state);
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
        map.set(ids[i], value);
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
