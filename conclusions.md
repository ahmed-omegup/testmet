## Rethink DB

it was able to handle under 3GB memory and 2 vCores :
* a throughput of 35k change / minute
* 10k active customer 
* 550 read per customer / minute 

## Meteor

it was able to handle under 3GB memory and 2 vCores :
* a throughput of 35k change / 50s
* 700 active customer 
* 350 read per customer / 50s 

## Electric

it was able to handle under 3GB memory and 2 vCores :
* a throughput of 35k change / 50s
* 100 active customer 
* 90 read per customer / 50s 



400000
[perf] 350000 events processing took 31407.59 ms

[perf] summary
  duration: 47139.70 ms (~9551.29 events/s)
  match events: 298,061 (evictions: 795,636)
  retrieval batches: 152,393 (docs: 5,473,897)

## Dafny Clean Limit Engine

it was able to handle under 3GB memory and 2 vCores:
* a throughput of 213k change / minute
* 10k active customer
* 3 read per customer / minute

Benchmark details:
* 400,000 seeded documents
* 10,000 active customers
* 350,000 change events across five ticks
* query limit 50
* document density 10
* wall duration: 98.655 seconds
* throughput: 350,000 / 98.655 seconds, approximately 212,872 changes/minute
* raw output: 349,972 match events, 30,136,300 evictions, 360,000 retrieval batches, 500,000 retrieved documents

Measured with `./specs/clean-dafny/run-clean-limit-400k.sh` using `specs/dafny-ts/CleanLimitMutablePerf400k.dfy`, a verification-independent mutable array/bucket runtime. `specs/dafny-ts/MutableDocumentIndexProof.dfy` separately verifies a small native mutable-index contract, but it does not prove this benchmark runtime. This benchmark avoided the immutable clean-engine store/treap copying that stalled in the proof-oriented 400k run. The eviction and retrieval summaries are not yet equivalent to the TypeScript implementation and must not be interpreted as end-to-end networked parity.

The existing 1,651-event clean-engine benchmark remains a separate proof-oriented smoke/performance sample; it does not scale to this workload.