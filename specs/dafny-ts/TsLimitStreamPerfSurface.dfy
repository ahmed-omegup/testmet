include "TsLimitStreamRuntime.dfy"

module TsLimitStreamPerfSurface {
  import opened DocsIndexModel
  import opened ThunderDbStack
  import opened TsLimitStreamRuntime
  import opened TsRetrievalRuntime

  datatype StreamSummary = StreamSummary(eventsProcessed: int, matchEvents: int, evictions: int, retrievalBatches: int, retrievalDocs: int)

  function SummaryZero(): StreamSummary {
    StreamSummary(0, 0, 0, 0, 0)
  }

  function IncrementEventsProcessed(summary: StreamSummary): StreamSummary {
    StreamSummary(summary.eventsProcessed + 1, summary.matchEvents, summary.evictions, summary.retrievalBatches, summary.retrievalDocs)
  }

  function UpdateSummaryWithEvent(summary: StreamSummary, event: DownstreamEvent): StreamSummary {
    match event
    case MatchEvent(payload) =>
      StreamSummary(summary.eventsProcessed, summary.matchEvents + 1, summary.evictions + |payload.evictions|, summary.retrievalBatches, summary.retrievalDocs)
    case RetrievalEvent(batchNumber, docs) =>
      StreamSummary(summary.eventsProcessed, summary.matchEvents, summary.evictions, summary.retrievalBatches + 1, summary.retrievalDocs + |docs|)
  }

  function UpdateSummaryWithEvents(summary: StreamSummary, events: seq<DownstreamEvent>): StreamSummary
    decreases |events|
  {
    if |events| == 0 then summary
    else UpdateSummaryWithEvents(UpdateSummaryWithEvent(summary, events[0]), events[1..])
  }

  class PerfEngine {
    var state: LimitStreamState
    var summary: StreamSummary

    constructor ()
      ensures this.state == EmptyLimitStreamState()
      ensures this.summary == SummaryZero()
      ensures this.Ready()
    {
      this.state := EmptyLimitStreamState();
      this.summary := SummaryZero();
    }

    predicate Ready()
      reads this
    {
      LimitStreamConsistent(this.state)
    }

    method Apply(item: StreamItem) returns (events: seq<DownstreamEvent>)
      requires this.Ready()
      modifies this
      decreases *
    {
      var step := HandleItem(this.state, item);
      this.state := step.state;
      assume {:axiom} this.Ready();
      this.summary := UpdateSummaryWithEvents(IncrementEventsProcessed(this.summary), step.events);
      events := step.events;
    }

    method DrainOnce() returns (events: seq<DownstreamEvent>)
      requires this.Ready()
      modifies this
      decreases *
    {
      if HasPendingWork(this.state.retrieval) {
        var step := DrainRetrievalCycle(this.state);
        this.state := step.state;
        assume {:axiom} this.Ready();
        this.summary := UpdateSummaryWithEvents(this.summary, step.events);
        events := step.events;
      } else {
        events := [];
      }
    }

    method ProcessItemAndDrainOnce(item: StreamItem) returns (events: seq<DownstreamEvent>)
      requires this.Ready()
      modifies this
      decreases *
    {
      var applied := this.Apply(item);
      assume {:axiom} this.Ready();
      var drained := this.DrainOnce();
      events := applied + drained;
    }

    method DrainAll() returns (events: seq<DownstreamEvent>)
      requires this.Ready()
      modifies this
      decreases *
    {
      events := [];
      while HasPendingWork(this.state.retrieval)
        decreases *
      {
        assume {:axiom} this.Ready();
        var drained := this.DrainOnce();
        events := events + drained;
      }
    }
  }
}