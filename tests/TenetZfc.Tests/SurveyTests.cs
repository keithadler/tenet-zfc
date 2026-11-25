using TenetZfc;
using Xunit;

namespace TenetZfc.Tests;

public class SurveyTests
{
    private static string Fixture(string name) => Path.Combine(AppContext.BaseDirectory, "fixtures", name);

    [Fact]
    public void TheSurveyCountsWhatTheTableTranslatesAndRanksWhatBlocksTheRest()
    {
        var t = new Terms();
        Survey.Result r = new Survey(t, Reader.ReadExport(t, Fixture("lenapp.ndjson"))).Run();
        // The export is List.length_append and the theorems its proof uses: 12 in all.
        Assert.Equal(12, r.Theorems);
        // List.length_append's own statement is in the table, so at least that one translates.
        Assert.InRange(r.StatementsTranslated, 1, r.Theorems);
        Assert.Equal(r.Theorems - r.StatementsTranslated, r.Reasons.Sum(x => x.Count));
        // Adding every blocker covers every theorem, statement and proof alike.
        (int added, int s, int f) = r.Curve[^1];
        Assert.Equal((r.Theorems, r.Theorems), (s, f));
        // The ranking is in decreasing order of statements, and only names constants outside the table.
        Assert.True(r.Blockers.Zip(r.Blockers.Skip(1)).All(p => p.First.Statements >= p.Second.Statements));
        Assert.DoesNotContain(r.Blockers, b => Survey.Covered.Contains(b.Const.ToString()));
    }
}
