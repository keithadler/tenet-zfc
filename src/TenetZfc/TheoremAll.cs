using System.Diagnostics;
using System.Text;
using System.Text.RegularExpressions;
using TenetZfc.Metamath;

namespace TenetZfc;

/// <summary>
/// Theorems at scale (docs/milestone3.md, "Theorems across Init"): every theorem of an export, or every Nth, proved
/// through the generic model from its proof term (TheoremTranslator), in chunks of a fixed number of theorems. Each
/// chunk is a set.mm extension of its own, like define-all's: it includes set.mm and writes every definition and lemma
/// its theorems use, so chunks verify independently (scripts/verify-all). Within a chunk the theorems share their
/// lemmas, so a chunk is proved in export order, where a theorem's dependencies come first. A refusal or failure is
/// recorded per theorem with its reason, and the run goes on.
/// </summary>
public sealed class TheoremAll(Terms t, Environment env, string setmmPath, bool compress = true)
{
    /// <summary>
    /// What happened to one theorem. Status: proved, refused, timeout (over the budget), error (a bug: an exception other
    /// than a refusal, or a proof whose replay fails), or crash (it ended the process on an earlier run; see Chunk).
    /// Steps: the theorem's proof, flat; Lemmas and LemmaSteps: the lemmas it was the first in its chunk to need.
    /// </summary>
    public sealed record Outcome(string Name, string Status, long Steps, int Lemmas, long LemmaSteps, string Reason, double Seconds, double Cpu = 0);

    /// <summary>Every theorem of the export that isn't unsafe, in export order; with every > 1, every Nth of them.</summary>
    public List<ConstInfo> Targets(int every = 1) => env.All
        .Where(c => c.Kind == ConstKind.Theorem && !c.Unsafe && c.Value is not null)
        .Where((_, i) => i % every == 0)
        .ToList();

    private string? _setmm;
    private readonly object _read = new();

    /// <summary>The time budget for one theorem, with the lemmas it is the first to need.</summary>
    public double BudgetSeconds { get; init; } = 120;

    /// <summary>The wall-time cap on one theorem, as a multiple of its CPU budget.</summary>
    public double WallFactor { get; init; } = 10;

    /// <summary>
    /// Prove one chunk: chunk-NNNN.mm, and chunk-NNNN.tsv with one line per theorem. Returns the outcomes.
    /// The translator, its model and its copy of set.mm's database are fresh per chunk.
    ///
    /// While it runs, chunk-NNNN.progress names the theorem in hand. A crash that ends the process (a stack overflow,
    /// running out of memory) leaves that file behind; the next run of the chunk records that theorem as a crash and
    /// skips it, so a resumed run gets past it.
    /// </summary>
    public List<Outcome> Chunk(int index, IReadOnlyList<ConstInfo> theorems, string outDir)
    {
        lock (_read)
        {
            _setmm ??= File.ReadAllText(setmmPath);
        }
        string name = $"chunk-{index:D4}";
        string progress = Path.Combine(outDir, name + ".progress");
        var crashed = new HashSet<string>();
        if (File.Exists(progress))
        {
            // Earlier crashes, carried in the file so that a chunk crashing twice skips both.
            crashed.UnionWith(File.ReadAllLines(progress).Where(l => l.StartsWith("crashed ", StringComparison.Ordinal)).Select(l => l[8..]));
            if (File.ReadAllLines(progress).FirstOrDefault(l => l.StartsWith("now ", StringComparison.Ordinal)) is string now)
            {
                crashed.Add(now[4..]);
            }
        }
        var db = new Database();
        db.Extend(_setmm);
        var pr = new Prover(db);
        var translator = new TheoremTranslator(t, env, pr);
        var w = new Writer(Path.GetFileName(setmmPath),
            $"tenet-zfc theorem-all, {name}: {theorems.Count} Lean theorems proved through the model of docs/milestone3.md",
            compress ? db : null);
        var proved = new List<(string Label, string Name, Metamath.Expr Statement, List<string> Proof, IEnumerable<string> Distinct)>();
        var outcomes = new List<Outcome>();
        foreach (ConstInfo c in theorems)
        {
            string n = $"{c.Name}";
            if (crashed.Contains(n))
            {
                outcomes.Add(new(n, "crash", 0, 0, 0, "ended the process on an earlier run (a stack overflow or out of memory)", 0));
                continue;
            }
            File.WriteAllText(progress, $"now {n}\n{string.Join("", crashed.Select(x => $"crashed {x}\n"))}{outcomes.Count + 1}/{theorems.Count}\n");
            var sw = Stopwatch.StartNew();
            int lemmasBefore = translator.LemmaSteps.Count;
            long stepsBefore = translator.LemmaSteps.Values.Sum();
            // The budget is CPU time of this thread, so that a loaded machine doesn't time out what a quiet one proves;
            // wall time is capped too, at WallFactor times the budget. Without a thread clock, the budget is wall time.
            pr.Deadline = DateTime.UtcNow.AddSeconds(BudgetSeconds);
            if (ThreadCpu.Seconds() is double cpu0)
            {
                DateTime cap = DateTime.UtcNow.AddSeconds(BudgetSeconds * WallFactor);
                pr.BudgetLeft = () => Math.Min(BudgetSeconds - (ThreadCpu.Seconds() ?? double.MaxValue) + cpu0, (cap - DateTime.UtcNow).TotalSeconds);
            }
            double cpuStart = ThreadCpu.Seconds() ?? 0;
            try
            {
                var (stmt, proof) = translator.Prove(c.Name);
                // Replayed here (every step's hypotheses, and the $d conditions), so a broken proof is recorded as an
                // error instead of failing the chunk in a checker.
                var dv = DistinctVars.Required(db, proof);
                proved.Add(($"lean-thm-{Model.LabelOf(c.Name)}", n, stmt, proof, dv.Select(p => $"{p.Item1} {p.Item2}").ToList()));
                outcomes.Add(new(n, "proved", db.Shared.Size(proof), translator.LemmaSteps.Count - lemmasBefore,
                    translator.LemmaSteps.Values.Sum() - stepsBefore, "", sw.Elapsed.TotalSeconds, (ThreadCpu.Seconds() ?? 0) - cpuStart));
            }
            catch (Exception e)
            {
                string status = e switch { Model.Refused => "refused", TimeoutException => "timeout", _ => "error" };
                outcomes.Add(new(n, status, 0, translator.LemmaSteps.Count - lemmasBefore,
                    translator.LemmaSteps.Values.Sum() - stepsBefore, Why(e), sw.Elapsed.TotalSeconds, (ThreadCpu.Seconds() ?? 0) - cpuStart));
            }
            pr.Deadline = null;
            pr.BudgetLeft = null;
        }
        w.Assumptions(translator.Model.Assumptions());
        w.Raw(translator.Declarations);
        foreach (var p in proved)
        {
            var proofOut = w.Compressed ? p.Proof : db.Shared.Expand(p.Proof);
            w.Theorem(p.Label, $"The Lean theorem {p.Name}, proved through the model from its proof term.", p.Statement, proofOut, p.Distinct);
        }
        File.WriteAllText(Path.Combine(outDir, name + ".mm"), w.ToString());
        var tsv = new StringBuilder("name\tstatus\tsteps\tlemmas\tlemma_steps\tseconds\tcpu_seconds\treason\n");
        foreach (Outcome o in outcomes)
        {
            tsv.Append($"{o.Name}\t{o.Status}\t{o.Steps}\t{o.Lemmas}\t{o.LemmaSteps}\t{o.Seconds:F2}\t{o.Cpu:F2}\t{o.Reason}\n");
        }
        // The .tsv last: its presence marks the chunk done, for resuming.
        File.WriteAllText(Path.Combine(outDir, name + ".tsv"), tsv.ToString());
        File.Delete(progress);
        return outcomes;
    }

    private static string Why(Exception e)
    {
        string why = e is Model.Refused ? e.Message : $"{e.GetType().Name}: {e.Message}";
        if (e is not Model.Refused && e.StackTrace is string st)
        {
            // Where it happened: the innermost few methods, for finding what is slow or broken.
            var at = st.Split('\n').Select(l => Regex.Match(l, @"at TenetZfc\.([\w.]+)\(").Groups[1].Value).Where(m => m != "").Distinct().Take(4);
            why += " (in " + string.Join(" < ", at) + ")";
        }
        why = why.Replace('\t', ' ').Replace('\n', ' ');
        return why.Length > 2000 ? why[..2000] + "…" : why;
    }
}
