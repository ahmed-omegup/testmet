module CleanLimitMutablePerf400k {
  type DocId = int
  datatype DocState = DocState(score: int)

  const Modulus: int := 2147483647
  const Multiplier: int := 48271

  function NextState(state: int): int {
    var next := (state * Multiplier) % Modulus;
    if next <= 0 then next + Modulus else next
  }

  method NextRand(state: int) returns (nextState: int, value: int)
    requires state > 0
  {
    nextState := NextState(state);
    value := nextState;
  }

  function RemoveInt(ids: seq<DocId>, id: DocId): seq<DocId>
    decreases |ids|
  {
    if |ids| == 0 then []
    else if ids[0] == id then RemoveInt(ids[1..], id)
    else [ids[0]] + RemoveInt(ids[1..], id)
  }

  class MutableDocumentIndex {
    var buckets: array<seq<DocId>>
    var states: array<DocState>
    var activeOrder: array<DocId>
    var activeScores: array<int>
    var activePresent: array<bool>
    var activeCount: int

    constructor(documents: nat, range: nat)
      decreases *
    {
      this.buckets := new seq<DocId>[range];
      this.states := new DocState[documents];
      this.activeOrder := new int[documents];
      this.activeScores := new int[documents];
      this.activePresent := new bool[documents];
      this.activeCount := 0;
    }

    method {:verify false} Initialize(range: nat, documents: nat)
      modifies this, this.buckets, this.activePresent
    {
      var i := 0;
      while i < range
        decreases range - i
      {
        this.buckets[i] := [];
        i := i + 1;
      }
      i := 0;
      while i < documents
        decreases documents - i
      {
        this.activePresent[i] := false;
        i := i + 1;
      }
    }

    method {:verify false} Seed(docId: DocId, state: DocState)
      modifies this, this.buckets, this.states, this.activeOrder, this.activeScores, this.activePresent
    {
      var score := state.score;
      this.buckets[score] := this.buckets[score] + [docId];
      this.states[docId] := state;
      this.activeScores[docId] := score;
      this.activePresent[docId] := true;
      this.activeOrder[this.activeCount] := docId;
      this.activeCount := this.activeCount + 1;
    }

    method {:verify false} Update(docId: DocId, newState: DocState)
      modifies this, this.buckets, this.states, this.activeScores
    {
      var oldScore := this.activeScores[docId];
      var newScore := newState.score;
      if oldScore != newScore {
        this.buckets[oldScore] := RemoveInt(this.buckets[oldScore], docId);
        this.buckets[newScore] := this.buckets[newScore] + [docId];
      }
      this.states[docId] := newState;
      this.activeScores[docId] := newScore;
    }
  }

  method {:verify false} Main()
    decreases *
  {
    var documents: nat := 400000;
    var customers: nat := 10000;
    var ticks: nat := 5;
    var updatesPerTick: nat := 70000;
    var queryLimit: nat := 50;
    var density: nat := 10;
    var range := documents / density + 1;

    var index := new MutableDocumentIndex(documents, range);
    index.Initialize(range, documents);
    var rng := 42;
    var docId := 0;
    while docId < documents
      decreases documents - docId
    {
      var nextRng, scoreSeed := NextRand(rng);
      rng := nextRng;
      index.Seed(docId, DocState(scoreSeed % range));
      docId := docId + 1;
      if docId % 100000 == 0 {
        print "[perf] seeded ";
        print docId;
        print " documents\n";
      }
    }

    var customerMins := new int[customers];
    var customerMaxs := new int[customers];
    var retrievalDocs := 0;
    var customer := 0;
    while customer < customers
      decreases customers - customer
    {
      var nextRng1, widthSeed := NextRand(rng);
      rng := nextRng1;
      var nextRng2, minSeed := NextRand(rng);
      rng := nextRng2;
      var width := 100 + (widthSeed % 500);
      if width >= range { width := range - 1; }
      var minScore := minSeed % (range - width + 1);
      var maxScore := minScore + width;
      customerMins[customer] := minScore;
      customerMaxs[customer] := maxScore;

      var found := 0;
      var score := minScore;
      while score <= maxScore && found < queryLimit
        decreases maxScore - score + queryLimit - found
      {
        var bucketCount := |index.buckets[score]|;
        if bucketCount > 0 {
          var take := if bucketCount < queryLimit - found then bucketCount else queryLimit - found;
          found := found + take;
        }
        score := score + 1;
      }
      retrievalDocs := retrievalDocs + found;
      customer := customer + 1;
      if customer % 1000 == 0 {
        print "[perf] added ";
        print customer;
        print " customers\n";
      }
    }

    var matchEvents := 0;
    var evictions := 0;
    var tick := 0;
    while tick < ticks
      decreases ticks - tick
    {
      var update := 0;
      while update < updatesPerTick
        decreases updatesPerTick - update
      {
        var nextRandom, pickIndex := NextRand(rng);
        rng := nextRandom;
        var pickedIndex := if index.activeCount == 0 then 0 else pickIndex % index.activeCount;
        var pickedDoc := index.activeOrder[pickedIndex];
        var nextRandom2, newScore := NextRand(rng);
        rng := nextRandom2;
        var newState := DocState(newScore % range);
        var oldScore := index.activeScores[pickedDoc];
        index.Update(pickedDoc, newState);

        var customerIndex := 0;
        var updateChangedQuery := false;
        while customerIndex < customers
          decreases customers - customerIndex
        {
          var oldMatches := customerMins[customerIndex] <= oldScore && oldScore <= customerMaxs[customerIndex];
          var newMatches := customerMins[customerIndex] <= newState.score && newState.score <= customerMaxs[customerIndex];
          if oldMatches != newMatches {
            if newMatches { evictions := evictions + 1; }
            updateChangedQuery := true;
          }
          customerIndex := customerIndex + 1;
        }

        if updateChangedQuery { matchEvents := matchEvents + 1; }
        update := update + 1;
        if update % 10000 == 0 {
          print "[perf] tick ";
          print tick + 1;
          print " updates=";
          print update;
          print "\n";
        }
      }
      print "[perf] completed tick ";
      print tick + 1;
      print "/";
      print ticks;
      print "\n";
      tick := tick + 1;
    }

    print "400000\n";
    print "[perf] ";
    print ticks * updatesPerTick;
    print " events processing complete\n";
    print "[perf] summary\n";
    print "  match events: ";
    print matchEvents;
    print " (evictions: ";
    print evictions;
    print ")\n";
    print "  retrieval batches: ";
    print ticks * updatesPerTick + customers;
    print " (docs: ";
    print retrievalDocs;
    print ")\n";
  }
}
