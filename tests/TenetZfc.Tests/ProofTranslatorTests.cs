using System.Diagnostics;
using TenetZfc.Metamath;
using Xunit;
using Env = TenetZfc.Environment;

namespace TenetZfc.Tests;

/// <summary>
/// The proof translator on the two cases of List.length_append's induction, taken from its actual proof term (Lean
/// 4.36.0's Init). Needs set.mm (TENET_ZFC_SETMM); both verifiers check the result when TENET_ZFC_METAMATH and
/// TENET_ZFC_MMVERIFY are set.
/// </summary>
public class ProofTranslatorTests(Xunit.Abstractions.ITestOutputHelper output)
{
    private static string Fixture(string name) => Path.Combine(AppContext.BaseDirectory, "fixtures", name);
    private static string? SetMm => System.Environment.GetEnvironmentVariable("TENET_ZFC_SETMM");

    [Fact]
    public void TheTwoInductionCasesTranslateAndVerify()
    {
        if (SetMm is null)
        {
            return;
        }
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("lenapp.ndjson"));
        var db = Database.Read(Path.Combine(SetMm, "set.mm"));
        var pr = new Prover(db);
        var ops = new Ops(t);
        var tr = new ProofTranslator(t, env, pr);

        // fun α as bs => List.rec α motive nilCase consCase as
        TenetZfc.Expr v = env.Find(t.Of("List.length_append"))!.Value!;
        ulong id = 1UL << 60;
        TenetZfc.Expr Fresh() => t.FVar(id++);
        var alpha = Fresh();
        var b1 = (Binder)v;
        var b2 = (Binder)ops.Instantiate(b1.Body, [alpha]);
        TenetZfc.Expr asTy = b2.Domain;
        var xs = Fresh();
        var b3 = (Binder)ops.Instantiate(b2.Body, [xs]);
        TenetZfc.Expr bsTy = b3.Domain;
        var ys = Fresh();
        TenetZfc.Expr body = ops.Instantiate(b3.Body, [ys]);
        TenetZfc.Expr head = Ops.Spine(body, out List<TenetZfc.Expr> args);
        Assert.Equal("List.rec", ((Const)head).Name.ToString());
        TenetZfc.Expr motive = args[1], nilCase = args[2], consCase = args[3];

        // The nil case, under bs ∈ Word α.
        tr.Begin([(alpha, "A")], "A", [(ys, "C", bsTy, false)]);
        var nilGoal = t.App(motive, t.App(t.Const(t.Of("List.nil"), ((Const)Ops.Head(asTy)).Levels), alpha));
        var nil = tr.ProveAs(nilCase, nilGoal);
        output.WriteLine($"nil:  {nil.Proves}  ({nil.Proof.Count} steps)");

        // The cons case: fun head tail ih => …, under bs, head ∈ α, tail ∈ Word α and the induction hypothesis.
        var c1 = (Binder)consCase;
        var hd = Fresh();
        var c2 = (Binder)ops.Instantiate(c1.Body, [hd]);
        var tl = Fresh();
        var c3 = (Binder)ops.Instantiate(c2.Body, [tl]);
        var ih = Fresh();
        TenetZfc.Expr consBody = ops.Instantiate(c3.Body, [ih]);
        TenetZfc.Expr ihTy = ops.Instantiate(c3.Domain, []);
        tr.Begin([(alpha, "A")], "A", [(ys, "C", bsTy, false), (hd, "D", c1.Domain, false), (tl, "E", ops.Instantiate(c2.Domain, [hd]), false), (ih, "", ihTy, true)]);
        var consTerm = t.MkApp(t.Const(t.Of("List.cons"), ((Const)Ops.Head(asTy)).Levels), [alpha, hd, tl]);
        var cons = tr.ProveAs(consBody, t.App(motive, consTerm));
        output.WriteLine($"cons: {cons.Proves}  ({cons.Proof.Count} steps)");

        Assert.Equal("|- ( C e. Word A -> ( # ` ( (/) ++ C ) ) = ( ( # ` (/) ) + ( # ` C ) ) )", nil.Proves.ToString());
        Assert.EndsWith("-> ( # ` ( ( <\" D \"> ++ E ) ++ C ) ) = ( ( # ` ( <\" D \"> ++ E ) ) + ( # ` C ) ) )", cons.Proves.ToString());

        string? metamath = System.Environment.GetEnvironmentVariable("TENET_ZFC_METAMATH");
        string? mmverify = System.Environment.GetEnvironmentVariable("TENET_ZFC_MMVERIFY");
        if (metamath is null || mmverify is null)
        {
            return;
        }
        var w = new Writer("set.mm", "tenet-zfc proof translator test");
        w.Theorem("lean-test-length_append-nil", "test", nil.Proves, nil.Proof);
        w.Theorem("lean-test-length_append-cons", "test", cons.Proves, cons.Proof);
        string file = Path.Combine(SetMm, $"tenet-zfc-pt-{Guid.NewGuid():N}.mm");
        File.WriteAllText(file, w.ToString());
        try
        {
            string mm = Run(metamath, SetMm, $"\"read {Path.GetFileName(file)}\" \"verify proof *\" \"exit\"", out _);
            Assert.DoesNotContain("?Error", mm);
            Run("python3", SetMm, $"-I \"{mmverify}\" \"{Path.GetFileName(file)}\"", out int code);
            Assert.Equal(0, code);
        }
        finally
        {
            File.Delete(file);
        }
    }

    [Fact]
    public void ListLengthAppendIsTranslatedFromItsProofAndVerifies()
    {
        if (SetMm is null)
        {
            return;
        }
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("lenapp.ndjson"));
        var pr = new Prover(Database.Read(Path.Combine(SetMm, "set.mm")));
        ConstInfo thm = env.Find(t.Of("List.length_append"))!;
        (var proof, string? why) = new ListInduction(t, env, pr).Prove(thm);
        Assert.Null(why);
        output.WriteLine($"{proof!.Value.Proves}  ({proof.Value.Proof.Count} steps)");
        // Exactly the translated statement: the theorem, not a variant of it.
        Assert.Equal(new StatementTranslator(t).Statement(thm.Type), proof.Value.Proves.ToString());

        string? metamath = System.Environment.GetEnvironmentVariable("TENET_ZFC_METAMATH");
        string? mmverify = System.Environment.GetEnvironmentVariable("TENET_ZFC_MMVERIFY");
        if (metamath is null || mmverify is null)
        {
            return;
        }
        var w = new Writer("set.mm", "tenet-zfc proof translator test");
        w.Theorem("lean-test-List.length_append", "test", proof.Value.Proves, proof.Value.Proof, ListInduction.Distinct);
        string file = Path.Combine(SetMm, $"tenet-zfc-la-{Guid.NewGuid():N}.mm");
        File.WriteAllText(file, w.ToString());
        try
        {
            string mm = Run(metamath, SetMm, $"\"read {Path.GetFileName(file)}\" \"verify proof *\" \"exit\"", out _);
            output.WriteLine(string.Join("\n", mm.Split('\n').Where(l => l.Contains('?') || l.Contains("verified"))));
            Assert.DoesNotContain("?Error", mm);
            Run("python3", SetMm, $"-I \"{mmverify}\" \"{Path.GetFileName(file)}\"", out int code);
            Assert.Equal(0, code);
        }
        finally
        {
            File.Delete(file);
        }
    }

    [Fact]
    public void AProofOfADifferentStatementIsRefused()
    {
        if (SetMm is null)
        {
            return;
        }
        var t = new Terms();
        Env env = Reader.ReadExport(t, Fixture("lenapp.ndjson"));
        var pr = new Prover(Database.Read(Path.Combine(SetMm, "set.mm")));
        ConstInfo thm = env.Find(t.Of("List.length_append"))!;
        // Claim the lengths add the other way round: len (as ++ bs) = len bs + len as. The proof does not prove it.
        var ops = new Ops(t);
        TenetZfc.Expr ty = thm.Type;
        var b1 = (Binder)ty;
        var b2 = (Binder)b1.Body;
        var b3 = (Binder)b2.Body;
        TenetZfc.Expr head = Ops.Spine(b3.Body, out List<TenetZfc.Expr> eq);
        TenetZfc.Expr sumHead = Ops.Spine(eq[2], out List<TenetZfc.Expr> sum);
        TenetZfc.Expr swapped = t.MkApp(sumHead, [sum[0], sum[1], sum[2], sum[3], sum[5], sum[4]]);
        TenetZfc.Expr wrong = t.Binding(true, b1.BinderName, b1.Info, b1.Domain, t.Binding(true, b2.BinderName, b2.Info, b2.Domain,
            t.Binding(true, b3.BinderName, b3.Info, b3.Domain, t.MkApp(head, [eq[0], eq[1], swapped]))));
        typeof(ConstInfo).GetProperty(nameof(ConstInfo.Type))!.SetValue(thm, wrong);
        (var proof, string? why) = new ListInduction(t, env, pr).Prove(thm);
        Assert.Null(proof);
        Assert.Contains("but the theorem states", why);
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
