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

Measured benchmark entry pending. Run:

```bash
./specs/clean-dafny/run-clean-limit-400k.sh
```

The runner produces the requested format:

it was able to handle under 3GB memory and 2 vCores:
* a throughput of x change / minute
* y active customer
* z read per customer / minute

Benchmark shape:
* 400,000 seeded documents
* 10,000 active customers
* 350,000 change events across five ticks
* query limit 50
* document density 10

The large run was stopped after 13 minutes because current clean-Dafny/treap processing remained active and did not produce a result in a practical benchmark window. This is not a failure or capacity result. It must not be reported until the runner completes and prints measured values.

The existing 1,651-event in-memory Dafny benchmark remains a separate smoke/performance sample; three runs took 0.55 s, 0.54 s, and 0.54 s. It does not scale its result to 400,000 documents or 350,000 changes.