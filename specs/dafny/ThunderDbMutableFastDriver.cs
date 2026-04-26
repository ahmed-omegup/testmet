using System.Diagnostics;
using System.Numerics;
using Dafny;
using ThunderDbMutable;
using ThunderDbStack;

namespace ThunderDbMutableFastDriver;

internal static class Program
{
    private const int Modulus = 2147483647;
    private const int Multiplier = 48271;

    private readonly record struct Summary(long EventsProcessed, long MatchEvents, long Evictions, long RetrievalBatches, long RetrievalDocs);
    private enum DrainMode
    {
        Immediate,
        PerTick,
    }

    private static int NextState(int state)
    {
        long next = (long)state * Multiplier % Modulus;
        return next <= 0 ? (int)(next + Modulus) : (int)next;
    }

    private static int NextRand(ref int state)
    {
        state = NextState(state);
        return state;
    }

    private static BigInteger BI(int value) => new(value);

    private static ThunderDbStack._ISeedDoc SeedDoc(int id, int score) => ThunderDbStack.SeedDoc.create(BI(id), BI(score));

    private static ThunderDbStack._IQuerySpec QuerySpec(int minScore, int maxScore, int limit) => ThunderDbStack.QuerySpec.create(BI(minScore), BI(maxScore), BI(limit));

    private static ThunderDbStack._IMaybeDocState NoState() => ThunderDbStack.MaybeDocState.create_NoState();

    private static ThunderDbStack._IMaybeDocState HasState(int score) => ThunderDbStack.MaybeDocState.create_HasState(BI(score));

    private static Summary UpdateSummary(Summary summary, Dafny.ISequence<ThunderDbStack._IDownstreamEvent> events)
    {
        summary = summary with { EventsProcessed = summary.EventsProcessed + 1 };
        foreach (var ev in events)
        {
            if (ev.is_MatchEvent)
            {
                summary = summary with
                {
                    MatchEvents = summary.MatchEvents + 1,
                    Evictions = summary.Evictions + ev.dtor_payload.dtor_evictions.LongCount
                };
            }
            else
            {
                summary = summary with
                {
                    RetrievalBatches = summary.RetrievalBatches + 1,
                    RetrievalDocs = summary.RetrievalDocs + ev.dtor_docs.LongCount
                };
            }
        }

        return summary;
    }

    private static Summary RunScenario(DrainMode drainMode, out double elapsedMs)
    {
        const int seed = 123;
        const int documents = 800;
        const int customers = 120;
        const int ticks = 30;
        const int updatesPerTick = 35;
        const int insertsPerTick = 8;
        const int deletesPerTick = 8;
        const int queryLimit = 25;
        const int density = 10;

        int rng = seed <= 0 ? 1 : seed;
        int nextDocId = documents;
        int range = density == 0 ? 1 : documents / density + 1;

        var engine = new MutableEngine();
        engine.__ctor();

        var docStates = new Dictionary<int, int>(documents * 2);
        var docOrder = new List<int>(documents * 2);
        var docIndex = new Dictionary<int, int>(documents * 2);

        var seedDocs = new ThunderDbStack._ISeedDoc[documents];
        for (int i = 0; i < documents; i++)
        {
            int score = NextRand(ref rng) % range;
            seedDocs[i] = SeedDoc(i, score);
            docStates[i] = score;
            docIndex[i] = docOrder.Count;
            docOrder.Add(i);
        }

        var summary = new Summary();
        var stopwatch = Stopwatch.StartNew();

        engine.SeedDocs(Sequence<ThunderDbStack._ISeedDoc>.FromArray(seedDocs));
        summary = summary with { EventsProcessed = 1 };

        for (int i = 0; i < customers; i++)
        {
            int width = 1 + (NextRand(ref rng) % (range / 2 + 1));
            int minScore = NextRand(ref rng) % range;
            int maxScore = minScore + width;
            Dafny.ISequence<ThunderDbStack._IDownstreamEvent> events;
            if (drainMode == DrainMode.Immediate)
            {
                engine.AddQuery(QuerySpec(minScore, maxScore, queryLimit), out _, out events);
            }
            else
            {
                engine.AddQueryDeferred(QuerySpec(minScore, maxScore, queryLimit), out _, out events);
            }
            summary = UpdateSummary(summary, events);
        }
        if (drainMode != DrainMode.Immediate)
        {
            summary = UpdateSummary(summary, engine.DrainPendingRetrievals());
        }

        for (int tick = 0; tick < ticks; tick++)
        {
            for (int update = 0; update < updatesPerTick; update++)
            {
                if (docOrder.Count == 0)
                {
                    continue;
                }

                int docId = docOrder[NextRand(ref rng) % docOrder.Count];
                int newScore = NextRand(ref rng) % range;
                int oldScore = docStates[docId];
                docStates[docId] = newScore;
                var events = drainMode == DrainMode.Immediate
                    ? engine.ApplyDocChange(BI(docId), HasState(oldScore), HasState(newScore))
                    : engine.ApplyDocChangeDeferred(BI(docId), HasState(oldScore), HasState(newScore));
                summary = UpdateSummary(summary, events);
            }

            for (int insert = 0; insert < insertsPerTick; insert++)
            {
                int newScore = NextRand(ref rng) % range;
                int docId = nextDocId++;
                docStates[docId] = newScore;
                docIndex[docId] = docOrder.Count;
                docOrder.Add(docId);
                var events = drainMode == DrainMode.Immediate
                    ? engine.ApplyDocChange(BI(docId), NoState(), HasState(newScore))
                    : engine.ApplyDocChangeDeferred(BI(docId), NoState(), HasState(newScore));
                summary = UpdateSummary(summary, events);
            }

            for (int delete = 0; delete < deletesPerTick; delete++)
            {
                if (docOrder.Count == 0)
                {
                    continue;
                }

                int pick = NextRand(ref rng) % docOrder.Count;
                int docId = docOrder[pick];
                int oldScore = docStates[docId];

                int lastIndex = docOrder.Count - 1;
                int lastDocId = docOrder[lastIndex];
                docOrder[pick] = lastDocId;
                docIndex[lastDocId] = pick;
                docOrder.RemoveAt(lastIndex);
                docIndex.Remove(docId);
                docStates.Remove(docId);

                var events = drainMode == DrainMode.Immediate
                    ? engine.ApplyDocChange(BI(docId), HasState(oldScore), NoState())
                    : engine.ApplyDocChangeDeferred(BI(docId), HasState(oldScore), NoState());
                summary = UpdateSummary(summary, events);
            }

            if (drainMode != DrainMode.Immediate)
            {
                summary = UpdateSummary(summary, engine.DrainPendingRetrievals());
            }
        }

        if (drainMode != DrainMode.Immediate)
        {
            summary = UpdateSummary(summary, engine.DrainPendingRetrievals());
        }

        stopwatch.Stop();
        elapsedMs = stopwatch.Elapsed.TotalMilliseconds;
        return summary;
    }

    private static void PrintResult(string name, Summary summary, double elapsedMs)
    {
        Console.WriteLine($"scenario {name} done: events={summary.EventsProcessed}, matches={summary.MatchEvents}, evictions={summary.Evictions}, retrievalBatches={summary.RetrievalBatches}, retrievalDocs={summary.RetrievalDocs}");
        Console.WriteLine($"elapsed_ms={elapsedMs:F2}");
    }

    private static void Main()
    {
        var immediate = RunScenario(DrainMode.Immediate, out var immediateElapsedMs);
        PrintResult("whole-stack-benchmark-like-mutable-fast-immediate", immediate, immediateElapsedMs);

        var perTick = RunScenario(DrainMode.PerTick, out var perTickElapsedMs);
        PrintResult("whole-stack-benchmark-like-mutable-fast-per-tick", perTick, perTickElapsedMs);
    }
}