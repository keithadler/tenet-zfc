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
        var m = new Model(t, env, new Prover(new Database()), dryRun: true, tower: false);
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
    public void InTheTowerAStringLiteralsConstantsAreTheInstancesWhateverIsDefinedFirst()
    {
        // The literal's List.cons and Char.ofNat were looked up by their names as exported. Char.ofNat then came out
        // defined through the exported dite when a string literal was the first to need it, and through dite.{1}
        // when anything else was: two texts for one definition, by the order of a run.
        static (string OfNat, string Cons) Define(params string[] order)
        {
            var t = new Terms();
            var mono = new Monomorph(t, Reader.ReadExport(t, Fixture("strings.ndjson")));
            var m = new Model(t, mono.Env, new Prover(new Database()), dryRun: true, tower: true);
            foreach (string n in order)
            {
                m.Define(mono.Instance(t.Of(n), []));
            }
            string d = m.Declarations;
            string Of(string label)
            {
                int i = d.IndexOf($"{label} $a", StringComparison.Ordinal);
                return d[i..d.IndexOf(" $.", i, StringComparison.Ordinal)];
            }
            return (Of("df-lean.Char.ofNat"), Of("df-lean.String.-cons"));
        }
        var literalFirst = Define("Lean.origin", "Char.ofNat");
        var constantFirst = Define("Char.ofNat", "Lean.origin");
        Assert.Equal(constantFirst.OfNat, literalFirst.OfNat);
        Assert.Contains("lean.dite.{1}", literalFirst.OfNat);
        Assert.DoesNotContain("( lean.dite ` u )", literalFirst.OfNat);
        // The literal's list is List.{0}'s, as a theorem about it has it.
        Assert.Contains("( y e. ( ( lean.List.{0} ` u ) ` ( lean.Char ` u ) ) |-> ( ( ( ( lean.List.cons.{0} ` u ) ` ( lean.Char ` u ) )", literalFirst.Cons);
    }

    [Fact]
    public void PropAxiomsAreProofsAndChoiceIsTheLeastElementInAWellOrdering()
    {
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("axioms.ndjson"));
        var m = new Model(t, env, new Prover(new Database()), dryRun: true, tower: false);
        m.Define(t.Of("propext"));
        m.Define(t.Of("Quot.ind"));
        Assert.Contains("df-lean.propext $a |- lean.propext = ( u e. Univ |-> (/) ) $.", m.Declarations);
        Assert.Contains("df-lean.Quot.ind $a |- lean.Quot.ind = ( u e. Univ |-> (/) ) $.", m.Declarations);
        m.Define(t.Of("Classical.propDecidable"));
        string d = m.Declarations;
        output.WriteLine(d);
        // Choice takes a well-ordering v of the universe after it, and picks α's least element in v.
        Assert.Contains("df-lean.Classical.choice $a |- lean.Classical.choice = ( u e. Univ |-> ( v e. ~P ( u X. u ) |-> ( x e. u |-> ( y e. ( ( lean.Nonempty ` u ) ` x ) |-> ( iota_ z e. x A. w e. x -. w v z ) ) ) ) ) $.", d);
        // What uses choice takes the well-ordering too, and passes it on.
        Assert.Contains("lean.Classical.propDecidable = ( u e. Univ |-> ( y e. ~P ( u X. u ) |-> ( x e. 2o |-> ( ( ( ( lean.Classical.choice ` u ) ` y ) ` ( ( lean.Decidable ` u ) ` x ) ) ` (/) ) ) ) ) $.", d);
    }

    [Fact]
    public void AQuotientIsTheClassesOfTheLeastEquivalenceRelationContainingR()
    {
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("axioms.ndjson"));
        var m = new Model(t, env, new Prover(new Database()), dryRun: true, tower: false);
        m.Define(t.Of("Quot"));
        m.Define(t.Of("Quot.mk"));
        m.Define(t.Of("Quot.lift"));
        string d = m.Declarations;
        output.WriteLine(d);
        Assert.Contains("lean.Quot.-eqv = ( u e. Univ |-> ( x e. u |-> ( y e. ( ( 2o ^m x ) ^m x ) |-> ( ( x X. x ) i^i |^| { a e. ~P ( x X. x ) | ( { <. b , c >. | ( ( b e. x /\\ c e. x ) /\\ (/) e. ( ( y ` b ) ` c ) ) } C_ a /\\ a Er x ) } ) ) ) ) $.", d);
        Assert.Contains("lean.Quot = ( u e. Univ |-> ( x e. u |-> ( y e. ( ( 2o ^m x ) ^m x ) |-> ( x /. ( ( ( lean.Quot.-eqv ` u ) ` x ) ` y ) ) ) ) ) $.", d);
        Assert.Contains("|-> [ z ] ( ( ( lean.Quot.-eqv ` u ) ` x ) ` y ) ) ) ) ) $.", d);
        Assert.Contains("|-> ran ( r e. x |-> <. [ r ] ( ( ( lean.Quot.-eqv ` u ) ` x ) ` y ) , ( w ` r ) >. ) ) ) ) ) ) ) $.", d);
    }

    [VerifierFact("TENET_ZFC_SETMM", "TENET_ZFC_METAMATH", "TENET_ZFC_MMVERIFY")]
    public void TheEquationsOfStringLiteralsVerify()
    {
        if (SetMm is null)
        {
            return;
        }
        var t = new Terms();
        var m = new Model(t, Reader.ReadExport(t, Fixture("strings.ndjson")), new Prover(Database.Read(Path.Combine(SetMm, "set.mm"))), tower: false);
        var w = new Writer("set.mm", "tenet-zfc string literals test");
        var eqs = new[] { "Lean.origin", "String.instInhabited" }.Select(n => (n, m.Equation(t.Of(n)))).ToList();
        w.Raw(m.Declarations);
        foreach (var (n, (s, p, dv)) in eqs)
        {
            w.Theorem($"lean-test-{n}-eq", "test", s, p, dv);
        }
        Check(w);
    }

    [VerifierFact("TENET_ZFC_SETMM", "TENET_ZFC_METAMATH", "TENET_ZFC_MMVERIFY")]
    public void TheQuotientsAndChoicesEquationsAndRulesVerify()
    {
        if (SetMm is null)
        {
            return;
        }
        var t = new Terms();
        var m = new Model(t, Reader.ReadExport(t, Fixture("axioms.ndjson")), new Prover(Database.Read(Path.Combine(SetMm, "set.mm"))), tower: false);
        var w = new Writer("set.mm", "tenet-zfc axioms and quotients test");
        var eqs = new[] { "propext", "Quot", "Quot.mk", "Quot.lift", "Classical.choice", "Classical.choose", "Classical.propDecidable" }
            .Select(n => (n, m.Equation(t.Of(n)))).ToList();
        var (qs, qp, qd) = m.QuotLiftIota();
        var (cs, cp, cd) = m.ChoiceSpec();
        // Given W We U, choice picks an element of α.
        Assert.EndsWith("/\\ W We U ) -> ( ( ( ( lean.Classical.choice ` U ) ` W ) ` A ) ` B ) e. A )", cs.ToString());
        output.WriteLine($"{qs} ({qp.Count} steps)");
        // Quot.lift f h (Quot.mk r a) = f a.
        Assert.EndsWith("` ( ( ( ( lean.Quot.mk ` U ) ` A ) ` B ) ` F ) ) = ( D ` F ) )", qs.ToString());
        w.Raw(m.Declarations);
        foreach (var (n, (s, p, dv)) in eqs)
        {
            w.Theorem($"lean-test-{n}-eq", "test", s, p, dv);
        }
        w.Theorem("lean-test-Quot.lift-iota", "test", qs, qp, qd);
        w.Theorem("lean-test-Classical.choice-spec", "test", cs, cp, cd);
        Check(w);
    }

    [Fact]
    public void InTheTowerAQuotientIsDefinedAtItsLevelAndChoiceOrdersTheTowersUnion()
    {
        var t = new Terms();
        var mono = new Monomorph(t, Reader.ReadExport(t, Fixture("axioms.ndjson")));
        var m = new Model(t, mono.Env, new Prover(new Database()), dryRun: true, tower: true);
        Level one = t.Succ(t.Zero);
        foreach (Name n in new[] { mono.Instance(t.Of("Quot"), [one]), mono.Instance(t.Of("Quot.mk"), [one]), mono.Instance(t.Of("Quot.lift"), [one, one]),
            mono.Instance(t.Of("Quot"), [t.Zero]), mono.Instance(t.Of("Quot.mk"), [t.Zero]), mono.Instance(t.Of("Classical.choice"), [one]) })
        {
            m.Define(n);
        }
        string d = m.Declarations;
        output.WriteLine(d);
        // One relation helper for every level: α ranges over the tower's union.
        Assert.Contains("lean.Quot.-eqv = ( u e. lean.-tower |-> ( x e. U. ran u |-> ( y e. ( ( 2o ^m x ) ^m x ) |-> ( ( x X. x ) i^i |^| { a e. ~P ( x X. x ) | ( { <. b , c >. | ( ( b e. x /\\ c e. x ) /\\ (/) e. ( ( y ` b ) ` c ) ) } C_ a /\\ a Er x ) } ) ) ) ) $.", d);
        Assert.Contains("lean.Quot.{1} = ( u e. lean.-tower |-> ( x e. ( u ` (/) ) |-> ( y e. ( ( 2o ^m x ) ^m x ) |-> ( x /. ( ( ( lean.Quot.-eqv ` u ) ` x ) ` y ) ) ) ) ) $.", d);
        Assert.Contains("lean.Quot.mk.{1} = ( u e. lean.-tower |-> ( x e. ( u ` (/) ) |-> ( y e. ( ( 2o ^m x ) ^m x ) |-> ( z e. x |-> [ z ] ( ( ( lean.Quot.-eqv ` u ) ` x ) ` y ) ) ) ) ) $.", d);
        // h's type is a proposition in the tower.
        Assert.Contains("lean.Quot.lift.{1,1} = ( u e. lean.-tower |-> ( x e. ( u ` (/) ) |-> ( y e. ( ( 2o ^m x ) ^m x ) |-> ( z e. ( u ` (/) ) |-> ( w e. ( z ^m x ) |-> ( r e. if ( A. v e. x", d);
        // A quotient of a proposition is the proposition; its class map is then a proof.
        Assert.Contains("lean.Quot.{0} = ( u e. lean.-tower |-> ( x e. 2o |-> ( y e. ( ( 2o ^m x ) ^m x ) |-> x ) ) ) $.", d);
        Assert.Contains("lean.Quot.mk.{0} = ( u e. lean.-tower |-> (/) ) $.", d);
        // One well-ordering of U. ran u serves every level.
        Assert.Contains("lean.Classical.choice.{1} = ( u e. lean.-tower |-> ( v e. ~P ( U. ran u X. U. ran u ) |-> ( x e. ( u ` (/) ) |-> ( y e. ( ( lean.Nonempty.{1} ` u ) ` x ) |-> ( iota_ z e. x A. w e. x -. w v z ) ) ) ) ) $.", d);
        Assert.Contains("Choice: Classical.choice is the least element in a well-ordering W of U. ran U, the tower's union", m.Assumptions());
    }

    [VerifierFact("TENET_ZFC_SETMM", "TENET_ZFC_METAMATH", "TENET_ZFC_MMVERIFY")]
    public void InTheTowerTheQuotientsAndChoicesEquationsAndRulesVerify()
    {
        if (SetMm is null)
        {
            return;
        }
        var t = new Terms();
        var mono = new Monomorph(t, Reader.ReadExport(t, Fixture("axioms.ndjson")));
        var m = new Model(t, mono.Env, new Prover(Database.Read(Path.Combine(SetMm, "set.mm"))), tower: true);
        Level one = t.Succ(t.Zero);
        Name quot = mono.Instance(t.Of("Quot"), [one]), mk = mono.Instance(t.Of("Quot.mk"), [one]), lift = mono.Instance(t.Of("Quot.lift"), [one, one]);
        Name choice = mono.Instance(t.Of("Classical.choice"), [one]), quot0 = mono.Instance(t.Of("Quot"), [t.Zero]);
        var w = new Writer("set.mm", "tenet-zfc axioms and quotients in the tower test");
        var eqs = new[] { quot, mk, lift, choice, quot0 }.Select(n => (n, m.Equation(n))).ToList();
        var (qs, qp, qd) = m.QuotLiftIota(lift, mk);
        var (cs, cp, cd) = m.ChoiceSpec(choice);
        Assert.EndsWith("` ( ( ( ( lean.Quot.mk.{1} ` U ) ` A ) ` B ) ` F ) ) = ( D ` F ) )", qs.ToString());
        Assert.EndsWith("/\\ W We U. ran U ) -> ( ( ( ( lean.Classical.choice.{1} ` U ) ` W ) ` A ) ` B ) e. A )", cs.ToString());
        w.Assumptions(m.Assumptions());
        w.Raw(m.Declarations);
        foreach (var (n, (s, p, dv)) in eqs)
        {
            w.Theorem($"lean-test-{Model.LabelPart($"{n}")}-eq", "test", s, p, dv);
        }
        w.Theorem("lean-test-Quot.lift-iota", "test", qs, qp, qd);
        w.Theorem("lean-test-Classical.choice-spec", "test", cs, cp, cd);
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
