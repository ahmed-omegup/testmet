# Real-time Database Benchmark

Compare Meteor/MongoDB vs Custom Server/RethinkDB for real-time WebSocket subscriptions.

## Architecture

### Specification-Oriented Development
Formal specifications and decision logs are maintained under `specs/`:

- `specs/README.md` (index & workflow)
- `specs/decisions.md` (chronological decisions D001+)
- `specs/change-events.md` (replication change payload contract)
- `specs/top-k-selection.md` (limit handling & demand-aware buffer design)
- `specs/memory-and-scaling.md` (footprint estimates & optimization levers)
- `specs/implementation-roadmap.md` (phased execution plan)

Contribution flow:
1. Update or extend a spec section.
2. Reference the spec (file + heading) in commits/PRs.
3. Append a decision row if architectural direction changes.
4. Never delete decisions; add amendments/reversals.

This preserves intent and enables incremental optimization of the real-time engine.

### MongoDB/Meteor Setup
- **MongoDB**: Replica set with oplog for change streams
- **Meteor**: DDP server with reactive publications
- **Tester**: WebSocket clients subscribing to filtered document ranges

### RethinkDB Setup
- **RethinkDB**: Native changefeeds for real-time updates
- **RethinkDB Server**: Custom Node.js WebSocket server with changefeed subscriptions
- **Tester**: Same WebSocket clients (DDP protocol compatible)

## Running the Benchmarks

### Test MongoDB/Meteor
```bash
docker compose up --build
```

### Test RethinkDB
```bash
docker compose -f docker-compose-rethink.yml up --build
```

### Test ThunderDB (worker + perf)
Runs the ThunderDB limit-stream worker and the perf harness in separate containers that communicate over a TCP socket.

```bash
docker compose -f docker-compose-thunderdb.yml up --build
```

The compose file uses the `oven/bun` image for both services:

- `thunderdb-worker` starts `src/socketWorker.ts` and listens on port `4100` (configurable via `WORKER_PORT`).
- `thunderdb-perf` launches `src/perf.ts`, generates the event workload, and streams it to the worker over the internal Docker network.

Environment variables prefixed with `PERF_` mirror the existing standalone perf script. Remote execution is enabled via:

```
PERF_REMOTE_WORKER=1
PERF_WORKER_HOST=<hostname>
PERF_WORKER_PORT=<port>
```

For local development outside of Docker you can run the worker directly (`npm run worker`) and then execute `PERF_REMOTE_WORKER=1 PERF_WORKER_HOST=127.0.0.1 npm run perf`.

The worker honors `THUNDERDB_DOCSTORE_DURABILITY` (`durable` or `relaxed`) to control LMDB sync behavior; the compose file sets it to `relaxed` to match the optimized perf profile.

### Monitor Resources
In a separate terminal while tests are running:
```bash
# MongoDB setup
docker stats benchmark-mongo-1 benchmark-meteor-1 benchmark-tester-1

# RethinkDB setup
docker stats benchmark-rethinkdb-1 benchmark-rethinkdb-server-1 benchmark-tester-1
```

## Configuration

Edit environment variables in the respective docker-compose files:

```yaml
- CUSTOMERS=500      # Number of concurrent WebSocket connections
- DURATION=10        # Duration of update phase (seconds)
- INIT_TIME=10       # Time to spawn all customers (seconds)
- DOCUMENTS=10000    # Number of documents to seed
```

## Resource Limits

Both setups use identical resource constraints for fair comparison:

**Database (MongoDB/RethinkDB)**:
- Memory: 2GB limit, 1GB reserved

**Server (Meteor/RethinkDB-Server)**:
- Memory: 2GB limit, 512MB reserved
- CPU: 2 cores

## Benchmark Phases

1. **Seeding**: Insert DOCUMENTS into database
2. **Customer Spawn**: Create CUSTOMERS WebSocket connections over INIT_TIME seconds
3. **Updates**: Run periodic updates/inserts/deletes for DURATION seconds
4. **Cleanup**: Wait for all customers to receive final updates and disconnect

## RethinkDB Admin UI

When running RethinkDB setup, access admin UI at:
```
http://localhost:8080
```

## Results

The benchmark outputs:
- Connection timing (customers/second)
- Update throughput (operations/second)
- Memory and CPU usage (via docker stats)

Compare the results between MongoDB/Meteor and RethinkDB to determine which performs better for your workload.
