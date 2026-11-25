include "TsLimitStreamPerfSurface.dfy"

module TsLimitStreamPerf {
  import opened DocsIndexModel
  import opened ThunderDbStack
  import opened TsLimitStreamPerfSurface

  const PERF_SEED: int := 42
  const PERF_DOCUMENTS: int := 1000000
  const PERF_CUSTOMERS: int := 100000
  const PERF_DURATION: int := 10
  const PERF_UPDATE_RATE_NUM: int := 5
  const PERF_UPDATE_RATE_DEN: int := 100
  const PERF_INSERT_RATE_NUM: int := 1
  const PERF_INSERT_RATE_DEN: int := 100
  const PERF_DELETE_RATE_NUM: int := 1
  const PERF_DELETE_RATE_DEN: int := 100
  const PERF_QUERY_LIMIT: int := 50
  const PERF_DENSITY: int := 10
  const PERF_SEED_BATCH: int := 4096

  method NextRand(state: int) returns (next: int)
  {
    next := (state * 48271) % 2147483647;
    if next <= 0 {
      next := next + 2147483647;
    }
  }

  method RandomScore(state: int, range: int) returns (next: int, score: int)
    requires 0 < range
  {
    next := NextRand(state);
    score := next % range;
  }

  method RandomDocIndex(state: int, activeCount: int) returns (next: int, index: int)
    requires 0 < activeCount
  {
    next := NextRand(state);
    index := next % activeCount;
  }

  method CustomerRange(state: int, range: int) returns (next: int, minScore: int, maxScore: int)
    requires 101 <= range
  {
    var s1 := NextRand(state);
    var width := 100 + (s1 % 500);
    if width >= range {
      width := range - 1;
    }
    var s2 := NextRand(s1);
    var startMax := range - width;
    var start := if 0 < startMax then s2 % startMax else 0;
    next := s2;
    minScore := start;
    maxScore := start + width;
  }

  method Main()
    decreases *
  {
    var range := PERF_DOCUMENTS / PERF_DENSITY;
    var updatesPerTick := PERF_DOCUMENTS * PERF_UPDATE_RATE_NUM / PERF_UPDATE_RATE_DEN;
    var insertsPerTick := PERF_DOCUMENTS * PERF_INSERT_RATE_NUM / PERF_INSERT_RATE_DEN;
    var deletesPerTick := PERF_DOCUMENTS * PERF_DELETE_RATE_NUM / PERF_DELETE_RATE_DEN;
    var maxDocs := PERF_DOCUMENTS + PERF_DURATION * insertsPerTick + 1;

    var engine := new PerfEngine();
    assume {:axiom} engine.Ready();
    var randomState := PERF_SEED;

    var activeOrder := new int[maxDocs];
    var activeScores := new int[maxDocs];
    var activePositions := new int[maxDocs];
    var activePresent := new bool[maxDocs];
    var activeCount := 0;
    var nextDocId := PERF_DOCUMENTS;

    var inputEvents := 0;

    var seedBatch := new SeedDoc[PERF_SEED_BATCH];
    var seedBatchCount := 0;
    var docId := 0;
    while docId < PERF_DOCUMENTS {
      var nextRandom, score := RandomScore(randomState, range);
      randomState := nextRandom;

      assume {:axiom} activeCount < activeOrder.Length;
      activeOrder[activeCount] := docId;
      activePositions[docId] := activeCount;
      activeScores[docId] := score;
      activePresent[docId] := true;
      activeCount := activeCount + 1;

      assume {:axiom} seedBatchCount < seedBatch.Length;
      seedBatch[seedBatchCount] := SeedDoc(docId, DocState(score));
      seedBatchCount := seedBatchCount + 1;
      if seedBatchCount == PERF_SEED_BATCH {
        assume {:axiom} engine.Ready();
        var seedEvents := engine.Apply(SeedDocsItem(seedBatch[..seedBatchCount]));
        inputEvents := inputEvents + 1;
        seedBatchCount := 0;
      }
      docId := docId + 1;
    }
    if 0 < seedBatchCount {
      var finalCount := seedBatchCount;
      if finalCount <= seedBatch.Length {
        assume {:axiom} engine.Ready();
        var finalSeedEvents := engine.Apply(SeedDocsItem(seedBatch[..finalCount]));
        inputEvents := inputEvents + 1;
      }
    }

    var customer := 0;
    while customer < PERF_CUSTOMERS {
      var nextRandom, minScore, maxScore := CustomerRange(randomState, range);
      randomState := nextRandom;
      assume {:axiom} engine.Ready();
      var queryEvents := engine.ProcessItemAndDrainOnce(QueryAddItem(QuerySpec(minScore, maxScore, PERF_QUERY_LIMIT)));
      inputEvents := inputEvents + 1;
      customer := customer + 1;
    }

    var tick := 0;
    while tick < PERF_DURATION {
      var updateCount := 0;
      while updateCount < updatesPerTick && 0 < activeCount {
        var nextRandom, pickIndex := RandomDocIndex(randomState, activeCount);
        randomState := nextRandom;
        if 0 <= pickIndex && pickIndex < activeCount && pickIndex < activeOrder.Length {
          var pickedDoc := activeOrder[pickIndex];
          if 0 <= pickedDoc && pickedDoc < activeScores.Length {
            var oldScore := activeScores[pickedDoc];
            var nextRandom2, newScore := RandomScore(randomState, range);
            randomState := nextRandom2;
            activeScores[pickedDoc] := newScore;

            assume {:axiom} engine.Ready();
            var updateEvents := engine.ProcessItemAndDrainOnce(DocChangeItem(pickedDoc, HasState(DocState(oldScore)), HasState(DocState(newScore))));
            inputEvents := inputEvents + 1;
          }
        }
        updateCount := updateCount + 1;
      }

      var insertCount := 0;
      while insertCount < insertsPerTick {
        var nextRandom, score := RandomScore(randomState, range);
        randomState := nextRandom;

        if 0 <= nextDocId && nextDocId < maxDocs && activeCount < activeOrder.Length && nextDocId < activePositions.Length && nextDocId < activeScores.Length && nextDocId < activePresent.Length {
          activeOrder[activeCount] := nextDocId;
          activePositions[nextDocId] := activeCount;
          activeScores[nextDocId] := score;
          activePresent[nextDocId] := true;
          activeCount := activeCount + 1;

          assume {:axiom} engine.Ready();
          var insertEvents := engine.ProcessItemAndDrainOnce(DocChangeItem(nextDocId, NoState, HasState(DocState(score))));
          inputEvents := inputEvents + 1;

          nextDocId := nextDocId + 1;
        }
        insertCount := insertCount + 1;
      }

      var deleteCount := 0;
      while deleteCount < deletesPerTick && 0 < activeCount {
        var nextRandom, pickIndex := RandomDocIndex(randomState, activeCount);
        randomState := nextRandom;
        if 0 <= pickIndex && pickIndex < activeCount && pickIndex < activeOrder.Length {
          var pickedDoc := activeOrder[pickIndex];
          if 0 <= pickedDoc && pickedDoc < activeScores.Length && 0 < activeCount && activeCount - 1 < activeOrder.Length {
            var oldScore := activeScores[pickedDoc];
            var lastDoc := activeOrder[activeCount - 1];
            activeOrder[pickIndex] := lastDoc;
            if 0 <= lastDoc && lastDoc < activePositions.Length {
              activePositions[lastDoc] := pickIndex;
              activeCount := activeCount - 1;
              activePresent[pickedDoc] := false;

              assume {:axiom} engine.Ready();
              var deleteEvents := engine.ProcessItemAndDrainOnce(DocChangeItem(pickedDoc, HasState(DocState(oldScore)), NoState));
              inputEvents := inputEvents + 1;
            }
          }
        }
        deleteCount := deleteCount + 1;
      }

      tick := tick + 1;
    }

    assume {:axiom} engine.Ready();
    var finalDrainEvents := engine.DrainAll();

    print "[dafny-perf] input events: ", inputEvents, "\n";
    print "[dafny-perf] match events: ", engine.summary.matchEvents, "\n";
    print "[dafny-perf] evictions: ", engine.summary.evictions, "\n";
    print "[dafny-perf] retrieval batches: ", engine.summary.retrievalBatches, "\n";
    print "[dafny-perf] retrieval docs: ", engine.summary.retrievalDocs, "\n";
  }
}