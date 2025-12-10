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