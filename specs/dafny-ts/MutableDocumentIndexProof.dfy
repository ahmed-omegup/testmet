module MutableDocumentIndexProof {
  type Score = int

  class MutableDocumentIndex {
    var activePresent: array<bool>
    var activeScores: array<Score>
    var activeOrder: array<int>
    var activeCount: nat

    constructor (capacity: nat)
      ensures activePresent.Length == capacity
      ensures activeScores.Length == capacity
      ensures activeOrder.Length == capacity
      ensures activeCount == 0
    {
      activePresent := new bool[capacity];
      activeScores := new Score[capacity];
      activeOrder := new int[capacity];
      activeCount := 0;
    }

    ghost predicate InitializedPrefix(i: nat)
      reads this, activePresent
    {
      i <= activePresent.Length &&
      (forall j :: 0 <= j < i ==> !activePresent[j])
    }

    ghost predicate ValidIndex()
      reads this, activePresent, activeScores, activeOrder
    {
      activePresent.Length == activeScores.Length &&
      activeScores.Length == activeOrder.Length &&
      activeCount <= activePresent.Length &&
      (forall i :: 0 <= i < activeCount ==>
        0 <= activeOrder[i] && activeOrder[i] < activePresent.Length)
    }

    method Seed(docId: nat, score: Score)
      requires activePresent.Length == activeScores.Length
      requires activeScores.Length == activeOrder.Length
      requires docId < activePresent.Length
      requires activeCount < activePresent.Length
      requires !activePresent[docId]
      modifies this, activePresent, activeScores, activeOrder
      ensures activePresent.Length == old(activePresent.Length)
      ensures activeScores.Length == old(activeScores.Length)
      ensures activeOrder.Length == old(activeOrder.Length)
      ensures activePresent.Length == activeScores.Length
      ensures activeScores.Length == activeOrder.Length
      ensures activePresent[docId]
      ensures activeCount == old(activeCount) + 1
      ensures activeOrder[old(activeCount)] == docId
    {
      activePresent[docId] := true;
      UpdateScore(docId, score);
      assert activeCount < activeOrder.Length;
      activeOrder[activeCount] := docId;
      activeCount := activeCount + 1;
    }

    method UpdateScore(docId: nat, score: Score)
      requires activePresent.Length == activeScores.Length
      requires docId < activePresent.Length
      requires activePresent[docId]
      modifies activeScores
      ensures activePresent.Length == old(activePresent.Length)
      ensures activeScores.Length == old(activeScores.Length)
      ensures activeScores[docId] == score
    {
      activeScores[docId] := score;
    }
  }
}
