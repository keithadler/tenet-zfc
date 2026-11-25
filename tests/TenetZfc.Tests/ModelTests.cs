using System.Diagnostics;
using TenetZfc.Metamath;
using Xunit;
using Env = TenetZfc.Environment;

namespace TenetZfc.Tests;

/// <summary>
/// The generic model of milestone 3 (docs/milestone3.md) on id, Function.comp and Function.const from Lean 4.36.0's
/// Init. The equations need set.mm (TENET_ZFC_SETMM); both verifiers check them when TENET_ZFC_METAMATH and
/// TENET_ZFC_MMVERIFY are set.
/// </summary>
public class ModelTests(Xunit.Abstractions.ITestOutputHelper output)
{
    private static string Fixture(string name) => Path.Combine(AppContext.BaseDirectory, "fixtures", name);
    private static string? SetMm => System.Environment.GetEnvironmentVariable("TENET_ZFC_SETMM");

    [Fact]
    public void LambdaIsAMapAndEveryNonPropSortIsTheUniverse()
    {
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("model.ndjson"));
        var m = new Model(t, env, new Prover(new Database()));
        // id := fun {α : Sort u} (a : α) => a
        Assert.Equal("( x e. u |-> ( y e. x |-> y ) )", m.Class(env.Find(t.Of("id"))!.Value!, "u", new Dictionary<ulong, string>()));
        // Function.comp's type: a non-dependent arrow is a set of functions, ( B ^m A ).
        string comp = m.Class(env.Find(t.Of("Function.comp"))!.Value!, "u", new Dictionary<ulong, string>());
        Assert.Contains("( w e. ( z ^m y ) |-> ( v e. ( y ^m x ) |-> ( t e. x |-> ( w ` ( v ` t ) ) ) ) )", comp);
    }

    [Fact]
    public void WhatTheModelDoesNotCoverYetIsRefusedWithTheReason()
    {
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("lenapp.ndjson"));
        var m = new Model(t, env, new Prover(new Database()));
        // List.length is about List, a recursive inductive type: not in the model yet.
        var e = Assert.Throws<Model.Refused>(() => m.Define(t.Of("List.length")));
        output.WriteLine(e.Message);
        Assert.Equal("List is a recursive inductive type; only non-recursive ones are in the model so far", e.Message);
        Assert.Throws<Model.Refused>(() => m.Define(t.Of("No.such.constant")));
        Assert.Equal("", m.Declarations);   // nothing written for a refused definition
    }

    [Fact]
    public void TheDefinitionalEquationsOfIdCompAndConstVerify()
    {
        if (SetMm is null)
        {
            return;
        }
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("model.ndjson"));
        var pr = new Prover(Database.Read(Path.Combine(SetMm, "set.mm")));
        var m = new Model(t, env, pr);
        var w = new Writer("set.mm", "tenet-zfc model test");
        var eqs = new List<(string, Metamath.Expr, List<string>, string[])>();
        foreach (string n in new[] { "id", "Function.comp", "Function.const" })
        {
            var (stmt, proof, distinct) = m.Equation(t.Of(n));
            output.WriteLine($"{n}: {stmt} ({proof.Count} steps)");
            eqs.Add(($"lean-test-{n}-eq", stmt, proof, distinct));
        }
        Assert.Equal("|- ( ( ( U e. Univ /\\ A e. U ) /\\ B e. A ) -> ( ( ( lean.id ` U ) ` A ) ` B ) = B )", eqs[0].Item2.ToString());
        Assert.EndsWith("( ( ( ( ( ( ( lean.Function.comp ` U ) ` A ) ` B ) ` C ) ` D ) ` E ) ` F ) = ( D ` ( E ` F ) ) )", eqs[1].Item2.ToString());
        Assert.EndsWith("( ( ( ( ( lean.Function.const ` U ) ` A ) ` B ) ` C ) ` D ) = C )", eqs[2].Item2.ToString());

        string? metamath = System.Environment.GetEnvironmentVariable("TENET_ZFC_METAMATH");
        string? mmverify = System.Environment.GetEnvironmentVariable("TENET_ZFC_MMVERIFY");
        if (metamath is null || mmverify is null)
        {
            return;
        }
        w.Raw(m.Declarations);
        foreach (var (label, stmt, proof, distinct) in eqs)
        {
            w.Theorem(label, "test", stmt, proof, distinct);
        }
        string file = Path.Combine(SetMm, $"tenet-zfc-model-{Guid.NewGuid():N}.mm");
        File.WriteAllText(file, w.ToString());
        try
        {
            string mm = Run(metamath, SetMm, $"\"read {Path.GetFileName(file)}\" \"verify proof *\" \"exit\"", out _);
            Assert.DoesNotContain("?Error", mm);
            Assert.Contains("All proofs in the database were verified", mm);
            Run("python3", SetMm, $"-I \"{mmverify}\" \"{Path.GetFileName(file)}\"", out int code);
            Assert.Equal(0, code);
        }
        finally
        {
            File.Delete(file);
        }
    }

    [Fact]
    public void TheTranslatedDefinitionsPassTheDefinitionCheckerAndABadOneDoesNot()
    {
        // mmj2's definitionCheck, through scripts/check-definitions. Needs TENET_ZFC_JAVA (Java 11) and TENET_ZFC_MMJ2.
        string? java = System.Environment.GetEnvironmentVariable("TENET_ZFC_JAVA");
        string? mmj2 = System.Environment.GetEnvironmentVariable("TENET_ZFC_MMJ2");
        if (SetMm is null || java is null || mmj2 is null)
        {
            return;
        }
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("model.ndjson"));
        var m = new Model(t, env, new Prover(Database.Read(Path.Combine(SetMm, "set.mm"))));
        foreach (string n in new[] { "id", "Function.comp", "Function.const" })
        {
            m.Define(t.Of(n));
        }
        string script = Path.Combine(AppContext.BaseDirectory, "..", "..", "..", "..", "..", "scripts", "check-definitions");
        string good = Path.Combine(SetMm, $"tenet-zfc-defs-{Guid.NewGuid():N}.mm");
        string bad = Path.Combine(SetMm, $"tenet-zfc-baddefs-{Guid.NewGuid():N}.mm");
        var w = new Writer("set.mm", "tenet-zfc definition check test");
        w.Raw(m.Declarations);
        File.WriteAllText(good, w.ToString());
        // The same, plus a definition with a free variable: lean.bad would be a different set for each x.
        File.WriteAllText(bad, w + "$c lean.bad $.\nclean.bad $a class lean.bad $.\ndf-lean.bad $a |- lean.bad = ( y e. Univ |-> x ) $.\n");
        try
        {
            output.WriteLine(Run(script, SetMm, $"\"{java}\" \"{mmj2}\" \"{good}\"", out int okCode));
            Assert.Equal(0, okCode);
            string why = Run(script, SetMm, $"\"{java}\" \"{mmj2}\" \"{bad}\"", out int badCode);
            output.WriteLine(why);
            Assert.Equal(1, badCode);
            Assert.Contains("df-lean.bad has failed the definitional soundness check", why);
        }
        finally
        {
            File.Delete(good);
            File.Delete(bad);
        }
    }

    [Fact]
    public void ANonRecursiveTypeIsItsTaggedTuplesAndItsConstructorsBuildThem()
    {
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("inductives.ndjson"));
        var m = new Model(t, env, new Prover(new Database()), dryRun: true);
        m.Define(t.Of("Option.rec"));
        string decls = m.Declarations;
        output.WriteLine(decls);
        // Option α is none's tag, plus some's tag around each a in α; the recursor tests the first tag.
        Assert.Contains("df-lean.Option $a |- lean.Option = ( u e. Univ |-> ( x e. u |-> ( { <. (/) , (/) >. } u. U_ y e. x { <. 1o , <. (/) , <. y , (/) >. >. >. } ) ) ) $.", decls);
        Assert.Contains("df-lean.Option.some $a |- lean.Option.some = ( u e. Univ |-> ( x e. u |-> ( y e. x |-> <. 1o , <. (/) , <. y , (/) >. >. >. ) ) ) $.", decls);
        Assert.Contains("if ( ( 1st ` ", decls);
    }

    [Fact]
    public void TheComputationRulesOfBoolProdAndOptionVerify()
    {
        if (SetMm is null)
        {
            return;
        }
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("inductives.ndjson"));
        var pr = new Prover(Database.Read(Path.Combine(SetMm, "set.mm")));
        var m = new Model(t, env, pr);
        var rules = new List<(string, Metamath.Expr, List<string>, string[])>();
        foreach (string c in new[] { "Bool.false", "Bool.true", "Prod.mk", "Option.none", "Option.some" })
        {
            var (stmt, proof, distinct) = m.Iota(t.Of(c));
            output.WriteLine($"{c}: {stmt} ({proof.Count} steps)");
            rules.Add(($"lean-test-{c}-iota", stmt, proof, distinct));
        }
        // Each reduces to its own minor premise: Bool.rec motive B C false = B, … true = C.
        Assert.EndsWith("` ( lean.Bool.false ` U ) ) = B )", rules[0].Item2.ToString());
        Assert.EndsWith("` ( lean.Bool.true ` U ) ) = C )", rules[1].Item2.ToString());
        Assert.EndsWith(") = ( ( D ` E ) ` F ) )", rules[2].Item2.ToString());   // Prod.rec … (Prod.mk a b) = minor a b
        Assert.EndsWith(") = C )", rules[3].Item2.ToString());
        Assert.EndsWith(") = ( D ` E ) )", rules[4].Item2.ToString());

        string? metamath = System.Environment.GetEnvironmentVariable("TENET_ZFC_METAMATH");
        string? mmverify = System.Environment.GetEnvironmentVariable("TENET_ZFC_MMVERIFY");
        if (metamath is null || mmverify is null)
        {
            return;
        }
        var w = new Writer("set.mm", "tenet-zfc inductive types test");
        w.Raw(m.Declarations);
        foreach (var (label, stmt, proof, distinct) in rules)
        {
            w.Theorem(label, "test", stmt, proof, distinct);
        }
        string file = Path.Combine(SetMm, $"tenet-zfc-ind-{Guid.NewGuid():N}.mm");
        File.WriteAllText(file, w.ToString());
        try
        {
            string mm = Run(metamath, SetMm, $"\"read {Path.GetFileName(file)}\" \"verify proof *\" \"exit\"", out _);
            Assert.DoesNotContain("?Error", mm);
            Assert.Contains("All proofs in the database were verified", mm);
            Run("python3", SetMm, $"-I \"{mmverify}\" \"{Path.GetFileName(file)}\"", out int code);
            Assert.Equal(0, code);
        }
        finally
        {
            File.Delete(file);
        }
    }

    [Fact]
    public void ProofsAreEmptyAndPropositionsAreInTwoO()
    {
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("props.ndjson"));
        var m = new Model(t, env, new Prover(new Database()), dryRun: true);
        foreach (string n in new[] { "Eq.rec", "And.rec", "False.rec", "Or.rec" })
        {
            m.Define(t.Of(n));
        }
        string d = m.Declarations;
        output.WriteLine(d);
        // Eq α a b is 1o when b = a and (/) otherwise; its one proof is (/).
        Assert.Contains("df-lean.Eq $a |- lean.Eq = ( u e. Univ |-> ( x e. u |-> ( y e. x |-> ( z e. x |-> if ( z = y , 1o , (/) ) ) ) ) ) $.", d);
        Assert.Contains("df-lean.Eq.refl $a |- lean.Eq.refl = ( u e. Univ |-> ( x e. u |-> ( y e. x |-> (/) ) ) ) $.", d);
        // Eq.rec eliminates into any sort: it is its minor premise. Or.rec only into Prop: it is a proof, (/).
        Assert.Matches(@"df-lean\.Eq\.rec .* \|-> (\w) \) \) \) \) \) \) \) \$\.", d);
        Assert.Contains("df-lean.False $a |- lean.False = ( u e. Univ |-> (/) ) $.", d);
    }

    [Fact]
    public void TheInferencerTellsProofsFromData()
    {
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("props.ndjson"));
        var ty = new Typing(t, env);
        var ctx = new Dictionary<ulong, TenetZfc.Expr>();
        // True.intro : True : Prop is a proof; True itself is a proposition, not a proof.
        Assert.True(ty.IsProof(t.Const(t.Of("True.intro"), []), ctx));
        Assert.False(ty.IsProof(t.Const(t.Of("True"), []), ctx));
        Assert.True(ty.IsProposition(t.Const(t.Of("True"), []), ctx));
    }

    [Fact]
    public void TheComputationRulesOfEqAndAndVerify()
    {
        if (SetMm is null)
        {
            return;
        }
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("props.ndjson"));
        var pr = new Prover(Database.Read(Path.Combine(SetMm, "set.mm")));
        var m = new Model(t, env, pr);
        var rules = new List<(string, Metamath.Expr, List<string>, string[])>();
        foreach (string c in new[] { "Eq.refl", "And.intro", "True.intro" })
        {
            var (stmt, proof, distinct) = m.Iota(t.Of(c));
            output.WriteLine($"{c}: {stmt} ({proof.Count} steps)");
            rules.Add(($"lean-test-{c}-iota", stmt, proof, distinct));
        }
        // Eq.rec … motive m a (refl) = m; And.rec … (intro h1 h2) = minor (/) (/).
        Assert.EndsWith("` B ) ` (/) ) = D )", rules[0].Item2.ToString());
        Assert.EndsWith(") = ( ( D ` (/) ) ` (/) ) )", rules[1].Item2.ToString());
        Assert.Throws<Model.Refused>(() => m.Iota(t.Of("Or.inl")));   // into Prop only: nothing to prove

        string? metamath = System.Environment.GetEnvironmentVariable("TENET_ZFC_METAMATH");
        string? mmverify = System.Environment.GetEnvironmentVariable("TENET_ZFC_MMVERIFY");
        if (metamath is null || mmverify is null)
        {
            return;
        }
        var w = new Writer("set.mm", "tenet-zfc inductive propositions test");
        w.Raw(m.Declarations);
        foreach (var (label, stmt, proof, distinct) in rules)
        {
            w.Theorem(label, "test", stmt, proof, distinct);
        }
        string file = Path.Combine(SetMm, $"tenet-zfc-props-{Guid.NewGuid():N}.mm");
        File.WriteAllText(file, w.ToString());
        try
        {
            string mm = Run(metamath, SetMm, $"\"read {Path.GetFileName(file)}\" \"verify proof *\" \"exit\"", out _);
            Assert.DoesNotContain("?Error", mm);
            Assert.Contains("All proofs in the database were verified", mm);
            Run("python3", SetMm, $"-I \"{mmverify}\" \"{Path.GetFileName(file)}\"", out int code);
            Assert.Equal(0, code);
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
