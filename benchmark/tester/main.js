import { MongoClient } from "mongodb";
import WebSocket from "ws";

const MONGO_URL = process.env.MONGO_URL;
const METEOR_URL = process.env.METEOR_URL;
const CUSTOMERS = parseInt(process.env.CUSTOMERS || "100000");
const DURATION = parseInt(process.env.DURATION || "10");
const INIT_TIME = parseInt(process.env.INIT_TIME || "10");

function prng(seed) {
  return () => (seed = (seed * 48271) % 0x7fffffff) / 0x7fffffff;
}
const rand = prng(42);

const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

async function seedDb() {
  const client = new MongoClient(MONGO_URL);
  await client.connect();
  const db = client.db("benchmark");
  const docs = db.collection("docs");
  await docs.deleteMany({});
  console.log("DB cleared");

  const N = 1_000_000;
  console.log(`Seeding ${N} documents`);
  const bulk = [];
  for (let i = 0; i < N; i++) {
    bulk.push({
      insertOne: {
        document: {
          _id: i,
          name: `doc_${i}`,
          score: Math.floor(rand() * 1000),
          timestamp: i,
        },
      },
    });
    if (bulk.length === 10_000) {
      await docs.bulkWrite(bulk);
      bulk.length = 0;
    }
  }
  if (bulk.length) await docs.bulkWrite(bulk);
  console.log("Seeding done");
  await client.close();
}

function customerRange(c) {
  const a = (c % 1000) * 0.9;
  const width = 50 + (c % 200);
  return [a, Math.min(1000, a + width)];
}

async function spawnCustomers() {
  const start = Date.now();
  let active = 0;
  for (let c = 0; c < CUSTOMERS; c++) {
    const ws = new WebSocket(METEOR_URL);
    const [a, b] = customerRange(c);
    ws.on("open", () => {
      ws.send(
        JSON.stringify({
          msg: "sub",
          id: `sub${c}`,
          name: "latestDocs",
          params: [a, b],
        })
      );
      active++;
    });
    if (c % 1000 === 0) console.log(`Spawned ${c} customers`);
    await sleep(0.1); // 100 µs each
  }
  console.log(`All ${CUSTOMERS} customers started in ${Date.now() - start}ms`);
}

async function periodicUpdates() {
  const client = new MongoClient(MONGO_URL);
  await client.connect();
  const docs = client.db("benchmark").collection("docs");
  const N = await docs.countDocuments();
  const updates = Math.floor(0.05 * N);
  const inserts = Math.floor(0.01 * N);
  const deletes = Math.floor(0.01 * N);
  let tick = 0;

  while (tick < DURATION) {
    const bulk = [];
    for (let i = 0; i < updates; i++) {
      const id = Math.floor(rand() * N);
      bulk.push({
        updateOne: {
          filter: { _id: id },
          update: {
            $set: { score: Math.floor(rand() * 1000), timestamp: tick },
          },
        },
      });
    }
    for (let i = 0; i < inserts; i++) {
      const id = N + tick * inserts + i;
      bulk.push({
        insertOne: {
          document: {
            _id: id,
            name: `doc_${id}`,
            score: Math.floor(rand() * 1000),
            timestamp: tick,
          },
        },
      });
    }
    for (let i = 0; i < deletes; i++) {
      const id = Math.floor(rand() * N);
      bulk.push({ deleteOne: { filter: { _id: id } } });
    }

    await docs.bulkWrite(bulk);
    console.log(`Tick ${tick}: ${bulk.length} ops`);
    tick++;
    await sleep(1000);
  }

  await client.close();
}

(async () => {
  await seedDb();
  await spawnCustomers();
  await periodicUpdates();
})();