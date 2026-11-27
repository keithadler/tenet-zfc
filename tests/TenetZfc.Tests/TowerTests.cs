using System.Diagnostics;
using TenetZfc.Metamath;
using Xunit;
using Env = TenetZfc.Environment;

namespace TenetZfc.Tests;

/// <summary>
/// The model's default, tower mode (docs/milestone3.md, "Tower mode"): constants are monomorphized, Sort (k+1) is
/// ( U ` k ), and each output's header states the universes it uses. ModelTests, BuiltinsTests and SetVarTests keep
/// covering the one-universe mode (--single-universe). The equations need set.mm (TENET_ZFC_SETMM); both verifiers
/// check them when TENET_ZFC_METAMATH and TENET_ZFC_MMVERIFY are set.
/// </summary>
public class TowerTests(Xunit.Abstractions.ITestOutputHelper output)
{
    private static string Fixture(string name) => Path.Combine(AppContext.BaseDirectory, "fixtures", name);
    private static string? SetMm => System.Environment.GetEnvironmentVariable("TENET_ZFC_SETMM");

    [Fact]
    public void TheModelIsATowerByDefaultAndSortsAreItsLevels()
    {
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("model.ndjson"));
        var mono = new Monomorph(t, env);
        var m = new Model(t, mono.Env, new Prover(new Database()), dryRun: true);
        Level one = t.Succ(t.Zero);
        // id.{1} : {α : Type} → α → α. Its universe is the tower's first level.
        Name id1 = mono.Instance(t.Of("id"), [one]);
        m.Define(id1);
        Assert.Contains("df-lean.id.u1 $a |- lean.id.{1} = ( u e. lean.-tower |-> ( x e. ( u ` (/) ) |-> ( y e. x |-> y ) ) ) $.", m.Declarations);
        // id.{0} : {α : Prop} → α → α is a proof, (/).
        Name id0 = mono.Instance(t.Of("id"), [t.Zero]);
        m.Define(id0);
        Assert.Contains("df-lean.id.u0 $a |- lean.id.{0} = ( u e. lean.-tower |-> (/) ) $.", m.Declarations);
    }

    [Fact]
    public void TheHeaderStatesWhichUniversesAreUsedAndByWhom()
    {
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("theorems.ndjson"));
        var mono = new Monomorph(t, env);
        var m = new Model(t, mono.Env, new Prover(new Database()), dryRun: true);
        m.Define(mono.Instance(t.Of("Nat.add"), []));
        string a = m.Assumptions();
        output.WriteLine(a);
        Assert.Contains("Each theorem has the hypothesis U e. lean.-tower", a);
        Assert.Contains("Levels used: 1 universe, ( U ` (/) ) (Lean's Type 0).", a);
        Assert.Matches(@"\( U ` \(/\) \) \(Type 0\) is used directly by: [^\n]*Nat\.below\.\{1\}", a);
        Assert.Contains("U. ran U, the whole tower, is the codomain of the motives of: Nat.rec", a);
        Assert.DoesNotContain("$)", a);

        var single = new Model(t, env, new Prover(new Database()), dryRun: true, tower: false);
        single.Define(t.Of("Nat.add"));
        Assert.Contains("one Grothendieck universe for every universe level", single.Assumptions());
    }

    [Fact]
    public void TheWriterPutsTheAssumptionsAfterTheHeader()
    {
        var w = new Writer("set.mm", "a header");
        w.Raw("$( body $)\n");
        w.Assumptions("Assumptions: none.");
        Assert.StartsWith("$( a header $)\n$(\nAssumptions: none.\n$)\n$[ set.mm $]", w.ToString().Replace("\r\n", "\n"));
    }

    [Fact]
    public void NestedBlocksAreMonomorphizedWithTheirAuxiliaryRecursors()
    {
        // Rose α nests List (Rose α): its block has an auxiliary recursor Rose.rec_1, instantiated with Rose.{0}.
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("mutual.ndjson"));
        var mono = new Monomorph(t, env);
        Name rose = mono.Instance(t.Of("Rose"), [t.Zero]);
        Assert.Equal("Rose.{0}", $"{rose}");
        Assert.NotNull(mono.Env.Find(t.Of("Rose.{0}.rec_1")));
        Name aux = mono.Instance(t.Of("Rose.rec_1"), [t.Zero, t.Zero]);
        Assert.Equal("Rose.{0}.rec_1", $"{aux}");
        var m = new Model(t, mono.Env, new Prover(new Database()), dryRun: true);
        m.Define(rose);
        Assert.Contains("df-lean.Rose.u0 $a |- lean.Rose.{0} = ( u e. lean.-tower |-> ( x e. ( u ` (/) ) |->", m.Declarations);
    }

    [Fact]
    public void NatAndListRecursionComputeInTheTowerAndVerify()
    {
        if (SetMm is null)
        {
            return;
        }
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("recursive.ndjson"));
        var mono = new Monomorph(t, env);
        var pr = new Prover(Database.Read(Path.Combine(SetMm, "set.mm")));
        var m = new Model(t, mono.Env, pr);
        var proved = new List<(string Label, Metamath.Expr S, List<string> P, string[] D)>();
        foreach (Name n in new[] { mono.Instance(t.Of("Nat.zero"), []), mono.Instance(t.Of("Nat.succ"), []),
                     mono.Instance(t.Of("List.nil"), [t.Zero]), mono.Instance(t.Of("List.cons"), [t.Zero]) })
        {
            var (s, p, d) = m.Iota(n);
            output.WriteLine($"{n}: {s} ({p.Count} steps)");
            proved.Add(($"lean-test-{Model.LabelPart($"{n}")}-iota", s, p, d));
        }
        Assert.StartsWith("|- ( ( ( ( U e. lean.-tower /\\ A e. ( U. ran U ^m ( lean.Nat ` U ) ) )", proved[0].S.ToString());
        Assert.EndsWith("` ( lean.Nat.zero ` U ) ) = B )", proved[0].S.ToString());
        Assert.Contains("lean.List.{0}", proved[3].S.ToString());

        string? metamath = System.Environment.GetEnvironmentVariable("TENET_ZFC_METAMATH");
        string? mmverify = System.Environment.GetEnvironmentVariable("TENET_ZFC_MMVERIFY");
        if (metamath is null || mmverify is null)
        {
            return;
        }
        var w = new Writer("set.mm", "tenet-zfc tower test", pr.Database);
        w.Assumptions(m.Assumptions());
        w.Raw(m.Declarations);
        foreach (var p in proved)
        {
            w.Theorem(p.Label, "test", p.S, p.P, p.D);
        }
        string file = Path.Combine(SetMm, $"tenet-zfc-tower-{Guid.NewGuid():N}.mm");
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
    public void AccIsALeastFixedPointAndItsRecursorIsWellFoundedRecursion()
    {
        // Acc's premise h : ∀ y, r y x → Acc r y is a function into Acc, so ω stages don't reach its least fixed point:
        // Acc is the intersection of the closed sets, and Acc.rec is frecs over it (Model.Least.cs).
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("acc436.ndjson"));
        var mono = new Monomorph(t, env);
        Level one = t.Succ(t.Zero);
        Name acc = mono.Instance(t.Of("Acc"), [one]), intro = mono.Instance(t.Of("Acc.intro"), [one]);
        Name rec = mono.Instance(t.Of("Acc.rec"), [t.Zero, one]);
        var dry = new Model(t, mono.Env, new Prover(new Database()), dryRun: true);
        dry.Define(rec);
        string decls = dry.Declarations;
        Assert.Contains("df-lean.Acc.u1.-least $a |- lean.Acc.{1}.-least = ( x e. _V |-> |^| { y | ( lean.Acc.{1}.-step ` <. x , y >. ) C_ y } ) $.", decls);
        Assert.Contains("if ( <. z , (/) >. e. ( lean.Acc.{1}.-least ` <. u , <. x , <. y , (/) >. >. >. ) , 1o , (/) )", decls);
        Assert.Contains("( frecs ( U_ ", decls);
        if (SetMm is null)
        {
            return;
        }
        var pr = new Prover(Database.Read(Path.Combine(SetMm, "set.mm")));
        var m = new Model(t, mono.Env, pr);
        var proved = new List<(string Label, Metamath.Expr S, List<string> P, string[] D)>();
        foreach (Name n in new[] { acc, intro, rec })
        {
            var (s, p, d) = m.Equation(n);
            output.WriteLine($"{n}: {s} ({p.Count} steps)");
            proved.Add(($"lean-test-{Model.LabelOf(n)}-eq", s, p, d));
        }
        // The computation rule needs the well-foundedness of R on the least set, not proved yet.
        Assert.Contains("computation rule is not in the model yet", Assert.Throws<Model.Refused>(() => m.Iota(intro)).Message);

        string? metamath = System.Environment.GetEnvironmentVariable("TENET_ZFC_METAMATH");
        string? mmverify = System.Environment.GetEnvironmentVariable("TENET_ZFC_MMVERIFY");
        if (metamath is null || mmverify is null)
        {
            return;
        }
        var w = new Writer("set.mm", "tenet-zfc Acc test", pr.Database);
        w.Assumptions(m.Assumptions());
        w.Raw(m.Declarations);
        foreach (var p in proved)
        {
            w.Theorem(p.Label, "test", p.S, p.P, p.D);
        }
        string file = Path.Combine(SetMm, $"tenet-zfc-acc-{Guid.NewGuid():N}.mm");
        File.WriteAllText(file, w.ToString());
        try
        {
            string mm = Run(metamath, SetMm, $"\"read {Path.GetFileName(file)}\" \"verify proof lean-*\" \"exit\"", out _);
            Assert.DoesNotContain("?Error", mm);
            Run("python3", SetMm, $"-I \"{mmverify}\" -b lean-test-Acc.u1-eq \"{Path.GetFileName(file)}\"", out int code);
            Assert.Equal(0, code);
        }
        finally
        {
            File.Delete(file);
        }
    }

    [Fact]
    public void TheRestOfInitsBlockersTranslateAndVerify()
    {
        // rest.ndjson: one constant for each fix of "The Init-wide run, again" (docs/milestone3.md).
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("rest.ndjson"));
        var mono = new Monomorph(t, env);
        Name Inst(string n) => mono.Instance(t.Of(n), env.Find(t.Of(n))!.LevelParams.Select(_ => t.Zero).ToArray());
        var dry = new Model(t, mono.Env, new Prover(new Database()), dryRun: true);
        dry.Define(Inst("List.head?"));
        Assert.Contains("$c lean.List.head-Q.{0} $.", dry.Declarations);
        Assert.Contains("df-lean.List.head-Q.u0 $a |- lean.List.head-Q.{0} = ", dry.Declarations);
        Assert.Contains("$( The Lean definition List.head?.{0}, translated", dry.Declarations);
        // A type with no constructors: its recursor's major premise ranges over (/).
        dry.Define(mono.Instance(t.Of("Empty.rec"), [t.Zero]));
        Assert.Contains("df-lean.Empty.rec $a |- lean.Empty.rec = ( u e. lean.-tower |-> ( x e. ( U. ran u ^m ( lean.Empty ` u ) ) |-> ( y e. ( lean.Empty ` u ) |-> (/) ) ) ) $.", dry.Declarations);
        if (SetMm is null)
        {
            return;
        }
        var pr = new Prover(Database.Read(Path.Combine(SetMm, "set.mm")));
        var m = new Model(t, mono.Env, pr);
        var proved = new List<(string Label, Metamath.Expr S, List<string> P, string[] D)>();
        foreach (Name n in new[] { mono.Instance(t.Of("Empty.rec"), [t.Zero]), Inst("IO.Error.rec"), Inst("List.head?") })
        {
            var (s, p, d) = m.Equation(n);
            proved.Add(($"lean-test-{Model.LabelOf(n)}-eq", s, p, d));
        }
        // IO.Error.rec has 21 arguments: one class variable of the output's own.
        Assert.Contains("cAA1 $f class AA1 $.", m.Declarations);
        Assert.Contains(" AA1 e. ", proved[1].S.ToString());
        foreach (string n in new[] { "Bind.mk", "Iff.intro", "HAdd.mk" })
        {
            var (s, p, d) = m.Iota(Inst(n));
            output.WriteLine($"{n}: {p.Count} steps");
            proved.Add(($"lean-test-{Model.LabelOf(Inst(n))}-iota", s, p, d));
        }

        string? metamath = System.Environment.GetEnvironmentVariable("TENET_ZFC_METAMATH");
        string? mmverify = System.Environment.GetEnvironmentVariable("TENET_ZFC_MMVERIFY");
        if (metamath is null || mmverify is null)
        {
            return;
        }
        var w = new Writer("set.mm", "tenet-zfc rest-of-Init test", pr.Database);
        w.Assumptions(m.Assumptions());
        w.Raw(m.Declarations);
        foreach (var p in proved)
        {
            w.Theorem(p.Label, "test", p.S, p.P, p.D);
        }
        string file = Path.Combine(SetMm, $"tenet-zfc-rest-{Guid.NewGuid():N}.mm");
        File.WriteAllText(file, w.ToString());
        try
        {
            string mm = Run(metamath, SetMm, $"\"read {Path.GetFileName(file)}\" \"verify proof lean-*\" \"exit\"", out _);
            Assert.DoesNotContain("?Error", mm);
            Run("python3", SetMm, $"-I \"{mmverify}\" -b {proved[0].Label} \"{Path.GetFileName(file)}\"", out int code);
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
