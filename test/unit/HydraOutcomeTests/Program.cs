using System.Reflection;
using CoreLib;
using Outcome = VC.VcOutcome;

static void Expect(bool condition, string message)
{
    if (!condition)
        throw new InvalidOperationException(message);
}

var merge = typeof(HydraParallel).GetMethod(
    "MergeOutcome", BindingFlags.Static | BindingFlags.NonPublic);
Expect(merge != null, "HydraParallel.MergeOutcome was not found");

Outcome Combine(Outcome current, Outcome next)
{
    return (Outcome)merge!.Invoke(null, new object[] { current, next })!;
}

var nonSafeOutcomes = new[]
{
    Outcome.Inconclusive,
    Outcome.TimedOut,
    Outcome.OutOfMemory,
    Outcome.OutOfResource,
    Outcome.SolverException
};

foreach (var outcome in nonSafeOutcomes)
{
    Expect(Combine(outcome, Outcome.Correct) == outcome,
        $"Correct overwrote earlier {outcome}");
    Expect(Combine(Outcome.Correct, outcome) == outcome,
        $"Earlier Correct suppressed later {outcome}");
}

foreach (var outcome in nonSafeOutcomes)
{
    Expect(Combine(Outcome.Errors, outcome) == Outcome.Errors,
        $"Unsafe did not dominate {outcome}");
    Expect(Combine(outcome, Outcome.Errors) == Outcome.Errors,
        $"Later unsafe did not dominate {outcome}");
}

Expect(Combine(Outcome.Correct, Outcome.Correct) == Outcome.Correct,
    "Two safe partitions did not remain safe");
Console.WriteLine("HYDRA outcome aggregation tests passed");
