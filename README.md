# Real-time Database Benchmark

Compare Meteor/MongoDB vs Custom Server/RethinkDB for real-time WebSocket subscriptions.

## Architecture

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
