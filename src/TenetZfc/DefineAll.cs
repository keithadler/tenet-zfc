using System.Diagnostics;
using System.Text;
using System.Text.RegularExpressions;
using TenetZfc.Metamath;

namespace TenetZfc;

/// <summary>
/// Milestone 3 at scale (docs/milestone3.md, "The Init-wide run"): every constant of an export that the generic model
/// handles, written with its definitional equation, and for constructors the recursor's computation rule, in chunks of
/// a fixed number of constants. Each chunk is a set.mm extension of its own: it includes set.mm and defines everything
/// its constants use, so chunks verify independently and in parallel. A constant the model refuses is reported with
/// the reason, and the run goes on.
/// </summary>
public sealed class DefineAll(Terms t, Environment env, string setmmPath, bool compress = true)
{
    /// <summary>What happened to one constant.</summary>
    public sealed record Outcome(string Name, string Kind, string Status, int EqSteps, string Iota, int IotaSteps, string Reason, double Seconds);

    /// <summary>The constants the run targets, in export order: everything but theorems, axioms and unsafe constants.</summary>
    public List<ConstInfo> Targets() => env.All
        .Where(c => c.Kind is ConstKind.Definition or ConstKind.Opaque or ConstKind.Inductive or ConstKind.Constructor or ConstKind.Recursor)
        .Where(c => !c.Unsafe)
        .ToList();

    private string? _setmm;
    private readonly object _read = new();

    /// <summary>The time budget for one constant: its equation and computation rule together.</summary>
    public double BudgetSeconds { get; init; } = 600;

    /// <summary>Constants slower than this are listed as the run goes.</summary>
    public double SlowSeconds { get; init; } = 5;

    /// <summary>
    /// Write one chunk: chunk-NNNN.mm, and chunk-NNNN.tsv with one line per constant. Returns the outcomes.
    /// The model and its copy of set.mm's database are fresh per chunk, so one chunk's refusals can't leak into another.
    /// </summary>
    public List<Outcome> Chunk(int index, IReadOnlyList<ConstInfo> constants, string outDir)
    {
        lock (_read)
        {
            _setmm ??= File.ReadAllText(setmmPath);
        }
        var db = new Database();
        db.Extend(_setmm);
        var pr = new Prover(db);
        var model = new Model(t, env, pr);
        string name = $"chunk-{index:D4}";
        var theorems = new Writer(Path.GetFileName(setmmPath),
            $"tenet-zfc define-all, {name}: {constants.Count} Lean constants translated by the model of docs/milestone3.md, with their equations and computation rules",
            compress ? db : null);
        var proved = new List<(string Label, Metamath.Expr Statement, List<string> Proof, string[] Distinct, string Comment)>();
        var outcomes = new List<Outcome>();
        foreach (ConstInfo c in constants)
        {
            var sw = Stopwatch.StartNew();
            string kind = c.Kind.ToString().ToLowerInvariant();
            pr.Deadline = DateTime.UtcNow.AddSeconds(BudgetSeconds);
            // What is running now, for watching a long run: chunk-NNNN.progress names the constant in hand.
            File.WriteAllText(Path.Combine(outDir, name + ".progress"), $"{outcomes.Count + 1}/{constants.Count} {c.Name}\n");
            try
            {
                var (stmt, proof, distinct) = model.Equation(c.Name);
                proved.Add(($"lean-{c.Name}-eq", stmt, proof, distinct, $"The definitional equation of {c.Name}."));
                string iota = "-", reason = "";
                int iotaSteps = 0;
                if (c.Kind == ConstKind.Constructor)
                {
                    try
                    {
                        var (istmt, iproof, idistinct) = model.Iota(c.Name);
                        proved.Add(($"lean-{c.Name}-iota", istmt, iproof, idistinct, $"The computation rule of the recursor on {c.Name}."));
                        iota = "ok";
                        iotaSteps = iproof.Count;
                    }
                    catch (Model.Refused e) when (e.Message.Contains("only into Prop"))
                    {
                        iota = "none-needed";
                    }
                    catch (Exception e)
                    {
                        iota = e is Model.Refused ? "refused" : "error";
                        reason = Why(e);
                    }
                }
                outcomes.Add(new($"{c.Name}", kind, "ok", proof.Count, iota, iotaSteps, reason, sw.Elapsed.TotalSeconds));
            }
            catch (Exception e)
            {
                outcomes.Add(new($"{c.Name}", kind, e is Model.Refused ? "refused" : "error", 0, "-", 0, Why(e), sw.Elapsed.TotalSeconds));
            }
        }
        pr.Deadline = null;
        foreach (Outcome o in outcomes.Where(o => o.Seconds > SlowSeconds))
        {
            Console.WriteLine($"  {name} slow: {o.Name} {o.Seconds:F0}s ({o.EqSteps} + {o.IotaSteps} steps, {o.Status})");
        }
        theorems.Raw(model.Declarations);
        foreach (var p in proved)
        {
            theorems.Theorem(p.Label, p.Comment, p.Statement, p.Proof, p.Distinct);
        }
        File.WriteAllText(Path.Combine(outDir, name + ".mm"), theorems.ToString());
        var tsv = new StringBuilder("name\tkind\tstatus\teq_steps\tiota\tiota_steps\tseconds\treason\n");
        foreach (Outcome o in outcomes)
        {
            tsv.Append($"{o.Name}\t{o.Kind}\t{o.Status}\t{o.EqSteps}\t{o.Iota}\t{o.IotaSteps}\t{o.Seconds:F2}\t{o.Reason}\n");
        }
        File.WriteAllText(Path.Combine(outDir, name + ".tsv"), tsv.ToString());
        File.Delete(Path.Combine(outDir, name + ".progress"));
        return outcomes;
    }

    private static string Why(Exception e)
    {
        string why = e is Model.Refused ? e.Message : $"{e.GetType().Name}: {e.Message}";
        if (e is TimeoutException && e.StackTrace is string st)
        {
            // Where the budget ran out: the innermost few methods, for finding what is slow.
            var at = st.Split('\n').Select(l => Regex.Match(l, @"at TenetZfc\.([\w.]+)\(").Groups[1].Value).Where(m => m != "").Distinct().Take(4);
            why += " (in " + string.Join(" < ", at) + ")";
        }
        return why.Replace('\t', ' ').Replace('\n', ' ');
    }

    /// <summary>A refusal's reason with the constant's own name taken out, so that equal reasons count together.</summary>
    public static string Category(string reason)
    {
        string r = Regex.Replace(reason, @"^\S+ is (not|a|an) ", "X is $1 ");
        r = Regex.Replace(r, @"^\S+: the name has", "X: the name has");
        r = Regex.Replace(r, @"^\S+ (is a mutual|is a recursive|is an indexed)", "X $1");
        r = Regex.Replace(r, @"\(.*\)$", "");
        r = Regex.Replace(r, @"lean\.\S+", "lean.X");
        return r.Length > 160 ? r[..160] + "…" : r.Trim();
    }
}
