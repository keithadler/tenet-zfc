using System.Diagnostics;
using TenetZfc.Metamath;
using Xunit;
using Env = TenetZfc.Environment;

namespace TenetZfc.Tests;

/// <summary>
/// String literals, axioms and the quotient in the generic model (docs/milestone3.md, step 5), on fixtures exported
/// from Lean 4.36.0's Init. The equations need set.mm (TENET_ZFC_SETMM); both verifiers check them when
/// TENET_ZFC_METAMATH and TENET_ZFC_MMVERIFY are set, and mmj2's definitionCheck when TENET_ZFC_JAVA and
/// TENET_ZFC_MMJ2 are.
/// </summary>
public class BuiltinsTests(Xunit.Abstractions.ITestOutputHelper output)
{
    private static string Fixture(string name) => Path.Combine(AppContext.BaseDirectory, "fixtures", name);
    private static string? SetMm => System.Environment.GetEnvironmentVariable("TENET_ZFC_SETMM");

    [Fact]
    public void AStringLiteralIsStringOfListOverItsCodePoints()
    {
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("strings.ndjson"));
        var m = new Model(t, env, new Prover(new Database()), dryRun: true);
        m.Define(t.Of("Lean.origin"));
        m.Define(t.Of("String.instInhabited"));
        string d = m.Declarations;
        // "leanprover/lean4": l = 108, then e = 101, …, ending in 4 = 52 and the empty list of Char.
        Assert.Contains("df-lean.Lean.origin $a |- lean.Lean.origin = ( u e. Univ |-> ( ( lean.String.ofList ` u ) ` ( ( ( lean.String.-cons ` u ) ` ; ; 1 0 8 ) ` ( ( ( lean.String.-cons ` u ) ` ; ; 1 0 1 ) `", d);
        Assert.Contains("` ( ( ( lean.String.-cons ` u ) ` ; 5 2 ) ` ( ( lean.List.nil ` u ) ` ( lean.Char ` u ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) $.", d);
        // One character: List.cons of Char.ofNat of the code point as a Nat literal.
        Assert.Contains("df-lean.String.-cons $a |- lean.String.-cons = ( u e. Univ |-> ( x e. NN0 |-> ( y e. ( ( lean.List ` u ) ` ( lean.Char ` u ) ) |-> ( ( ( ( lean.List.cons ` u ) ` ( lean.Char ` u ) ) ` ( ( lean.Char.ofNat ` u ) ` ( lean.Nat.-lit ` ( lean.Nat.-ofnum ` x ) ) ) ) ` y ) ) ) ) $.", d);
        // The empty string.
        Assert.Contains("( ( lean.String.ofList ` u ) ` ( ( lean.List.nil ` u ) ` ( lean.Char ` u ) ) )", d);
    }

    [Fact]
    public void PropAxiomsAreProofsAndChoiceIsRefusedWithTheReason()
    {
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("axioms.ndjson"));
        var m = new Model(t, env, new Prover(new Database()), dryRun: true);
        m.Define(t.Of("propext"));
        m.Define(t.Of("Quot.ind"));
        Assert.Contains("df-lean.propext $a |- lean.propext = ( u e. Univ |-> (/) ) $.", m.Declarations);
        Assert.Contains("df-lean.Quot.ind $a |- lean.Quot.ind = ( u e. Univ |-> (/) ) $.", m.Declarations);
        var e = Assert.Throws<Model.Refused>(() => m.Define(t.Of("Classical.choice")));
        Assert.Contains("no definable global choice function", e.Message);
    }

    [Fact]
    public void AQuotientIsTheClassesOfTheLeastEquivalenceRelationContainingR()
    {
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("axioms.ndjson"));
        var m = new Model(t, env, new Prover(new Database()), dryRun: true);
        m.Define(t.Of("Quot.lift"));
        string d = m.Declarations;
        output.WriteLine(d);
        Assert.Contains("lean.Quot.-eqv = ( u e. Univ |-> ( x e. u |-> ( y e. ( ( 2o ^m x ) ^m x ) |-> ( ( x X. x ) i^i |^| { a e. ~P ( x X. x ) | ( { <. b , c >. | ( ( b e. x /\\ c e. x ) /\\ (/) e. ( ( y ` b ) ` c ) ) } C_ a /\\ a Er x ) } ) ) ) ) $.", d);
        Assert.Contains("lean.Quot = ( u e. Univ |-> ( x e. u |-> ( y e. ( ( 2o ^m x ) ^m x ) |-> ( x /. ( ( ( lean.Quot.-eqv ` u ) ` x ) ` y ) ) ) ) ) $.", d);
        Assert.Contains("|-> [ z ] ( ( ( lean.Quot.-eqv ` u ) ` x ) ` y ) ) ) ) ) $.", d);
        Assert.Contains("|-> ran ( r e. x |-> <. [ r ] ( ( ( lean.Quot.-eqv ` u ) ` x ) ` y ) , ( w ` r ) >. ) ) ) ) ) ) ) $.", d);
    }

    [Fact]
    public void TheEquationsOfStringLiteralsVerify()
    {
        if (SetMm is null)
        {
            return;
        }
        var t = new Terms();
        var m = new Model(t, Reader.ReadExport(t, Fixture("strings.ndjson")), new Prover(Database.Read(Path.Combine(SetMm, "set.mm"))));
        var w = new Writer("set.mm", "tenet-zfc string literals test");
        var eqs = new[] { "Lean.origin", "String.instInhabited" }.Select(n => (n, m.Equation(t.Of(n)))).ToList();
        w.Raw(m.Declarations);
        foreach (var (n, (s, p, dv)) in eqs)
        {
            w.Theorem($"lean-test-{n}-eq", "test", s, p, dv);
        }
        Check(w);
    }

    [Fact]
    public void TheQuotientsEquationsAndComputationRuleVerify()
    {
        if (SetMm is null)
        {
            return;
        }
        var t = new Terms();
        var m = new Model(t, Reader.ReadExport(t, Fixture("axioms.ndjson")), new Prover(Database.Read(Path.Combine(SetMm, "set.mm"))));
        var w = new Writer("set.mm", "tenet-zfc axioms and quotients test");
        var eqs = new[] { "propext", "Quot", "Quot.mk", "Quot.lift" }.Select(n => (n, m.Equation(t.Of(n)))).ToList();
        var (qs, qp, qd) = m.QuotLiftIota();
        output.WriteLine($"{qs} ({qp.Count} steps)");
        // Quot.lift f h (Quot.mk r a) = f a.
        Assert.EndsWith("` ( ( ( ( lean.Quot.mk ` U ) ` A ) ` B ) ` F ) ) = ( D ` F ) )", qs.ToString());
        w.Raw(m.Declarations);
        foreach (var (n, (s, p, dv)) in eqs)
        {
            w.Theorem($"lean-test-{n}-eq", "test", s, p, dv);
        }
        w.Theorem("lean-test-Quot.lift-iota", "test", qs, qp, qd);
        Check(w);
    }

    /// <summary>Both verifiers and mmj2's definitionCheck, each when its tools are configured.</summary>
    private void Check(Writer w)
    {
        string file = Path.Combine(SetMm!, $"tenet-zfc-builtins-{Guid.NewGuid():N}.mm");
        File.WriteAllText(file, w.ToString());
        try
        {
            string? metamath = System.Environment.GetEnvironmentVariable("TENET_ZFC_METAMATH");
            string? mmverify = System.Environment.GetEnvironmentVariable("TENET_ZFC_MMVERIFY");
            if (metamath is not null && mmverify is not null)
            {
                string mm = Run(metamath, SetMm!, $"\"read {Path.GetFileName(file)}\" \"verify proof *\" \"exit\"", out _);
                Assert.DoesNotContain("?Error", mm);
                Assert.Contains("All proofs in the database were verified", mm);
                Run("python3", SetMm!, $"-I \"{mmverify}\" \"{Path.GetFileName(file)}\"", out int code);
                Assert.Equal(0, code);
            }
            string? java = System.Environment.GetEnvironmentVariable("TENET_ZFC_JAVA");
            string? mmj2 = System.Environment.GetEnvironmentVariable("TENET_ZFC_MMJ2");
            if (java is not null && mmj2 is not null)
            {
                string script = Path.Combine(AppContext.BaseDirectory, "..", "..", "..", "..", "..", "scripts", "check-definitions");
                output.WriteLine(Run(script, SetMm!, $"\"{java}\" \"{mmj2}\" \"{file}\"", out int dc));
                Assert.Equal(0, dc);
            }
        }
        finally
        {
            File.Delete(file);
        }
    }

    private static string Run(string exe, string dir, string args, out int code)
    {
        var psi = new ProcessStartInfo(exe, args) { WorkingDirectory = dir, RedirectStandardOutput = true, RedirectStandardError = true };
        using Process p = Process.Start(psi)!;
        string o = p.StandardOutput.ReadToEnd() + p.StandardError.ReadToEnd();
        p.WaitForExit();
        code = p.ExitCode;
        return o;
    }
}
