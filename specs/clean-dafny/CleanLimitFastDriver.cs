using System.Diagnostics;
using System.Numerics;
using Dafny;
using CleanLimitEngine;
using ThunderDbStack;

namespace CleanLimitFastDriver;

internal static class Program
{
    private const int Modulus = 2147483647;
    private const int Multiplier = 48271;

    private readonly record struct Summary(long EventsProcessed, long MatchEvents, long Evictions, long RetrievalBatches, long RetrievalDocs);

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

    private static ThunderDbStack._IStreamItem SeedDocsItem(ThunderDbStack._ISeedDoc[] docs) => ThunderDbStack.StreamItem.create_SeedDocsItem(Sequence<ThunderDbStack._ISeedDoc>.FromArray(docs));

    private static ThunderDbStack._IStreamItem QueryAddItem(int minScore, int maxScore, int limit) => ThunderDbStack.StreamItem.create_QueryAddItem(QuerySpec(minScore, maxScore, limit));

    private static ThunderDbStack._IStreamItem DocChangeItem(int docId, ThunderDbStack._IMaybeDocState oldState, ThunderDbStack._IMaybeDocState newState) => ThunderDbStack.StreamItem.create_DocChangeItem(BI(docId), oldState, newState);

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

    private static Summary RunScenario(out double elapsedMs)
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

        var engine = new CleanEngine();
        engine.__ctor();

        var docStates = new Dictionary<int, int>(documents * 2);

        var seedDocs = new ThunderDbStack._ISeedDoc[documents];
        for (int i = 0; i < documents; i++)
        {
            int score = NextRand(ref rng) % range;
            seedDocs[i] = SeedDoc(i, score);
            docStates[i] = score;
        }

        var summary = new Summary();
        var stopwatch = Stopwatch.StartNew();

        engine.ProcessItem(SeedDocsItem(seedDocs), out var seedEvents, out _);
        summary = UpdateSummary(summary, seedEvents);

        for (int i = 0; i < customers; i++)
        {
            int width = 1 + (NextRand(ref rng) % (range / 2 + 1));
            int minScore = NextRand(ref rng) % range;
            int maxScore = minScore + width;
            engine.ProcessItem(QueryAddItem(minScore, maxScore, queryLimit), out var events, out _);
            summary = UpdateSummary(summary, events);
        }

        for (int tick = 0; tick < ticks; tick++)
        {
            for (int update = 0; update < updatesPerTick; update++)
            {
                if (engine.docIds.Count == 0)
                {
                    continue;
                }

                int picked = NextRand(ref rng) % engine.docIds.Count;
                int docId = (int)engine.docIds.Select(BI(picked));
                int newScore = NextRand(ref rng) % range;
                int oldScore = docStates[docId];
                docStates[docId] = newScore;
                engine.ProcessItem(DocChangeItem(docId, HasState(oldScore), HasState(newScore)), out var events, out _);
                summary = UpdateSummary(summary, events);
            }

            for (int insert = 0; insert < insertsPerTick; insert++)
            {
                int newScore = NextRand(ref rng) % range;
                int docId = nextDocId++;
                docStates[docId] = newScore;
                engine.ProcessItem(DocChangeItem(docId, NoState(), HasState(newScore)), out var events, out _);
                summary = UpdateSummary(summary, events);
            }

            for (int delete = 0; delete < deletesPerTick; delete++)
            {
                if (engine.docIds.Count == 0)
                {
                    continue;
                }

                int pick = NextRand(ref rng) % engine.docIds.Count;
                int docId = (int)engine.docIds.Select(BI(pick));
                int oldScore = docStates[docId];
                docStates.Remove(docId);

                engine.ProcessItem(DocChangeItem(docId, HasState(oldScore), NoState()), out var events, out _);
                summary = UpdateSummary(summary, events);
            }
        }

        stopwatch.Stop();
        elapsedMs = stopwatch.Elapsed.TotalMilliseconds;
        return summary;
    }

    private static void Main()
    {
        var summary = RunScenario(out var elapsedMs);
        Console.WriteLine($"scenario whole-stack-benchmark-like-clean-fast done: events={summary.EventsProcessed}, matches={summary.MatchEvents}, evictions={summary.Evictions}, retrievalBatches={summary.RetrievalBatches}, retrievalDocs={summary.RetrievalDocs}");
        Console.WriteLine($"elapsed_ms={elapsedMs:F2}");
    }
}