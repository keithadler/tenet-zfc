using System.Diagnostics;
using TenetZfc;

const string Usage = """
    tenet-zfc - Lean 4 proofs to ZFC (see docs/spec.md)

    usage:
      tenet-zfc replay <export.ndjson> <trace.ndjson>   re-derive the steps of a Tenet trace, without Tenet
      tenet-zfc emit <export.ndjson> <trace.ndjson> <set.mm> <out.mm>
                                                         replay, then write set.mm theorems for the theorems the
                                                         emitter covers (Nat arithmetic equations, and induction
                                                         on lists like List.length_append)
      tenet-zfc define <export.ndjson> <set.mm> <out.mm> <name>...
                                                         milestone 3: translate definitions by the generic model,
                                                         each with its definitional equation as a theorem
      tenet-zfc bridge <set.mm> <out.mm>                 milestone 3: the bridge lemmas recursive types rest on
      tenet-zfc nat-bridge <export.ndjson> <set.mm> <out.mm> [<n>...]
                                                         milestone 3: prove that the model's Nat is NN0 (zero, succ,
                                                         Nat.add and literals, each numeral n given), from an export
                                                         with Nat.add (docs/bridges.md)
      tenet-zfc survey <export.ndjson>                   how many theorem statements the translator covers, and
                                                         which constants block the rest

    emit, define, bridge and nat-bridge write proofs in Metamath's compressed format, sharing every repeated subproof;
    add --uncompressed (anywhere) for flat label lists.

    make a trace with Tenet (github.com/keithadler/tenet, main):
      tenet check <export.ndjson> --trace <trace.ndjson>

    exit status: 0 no step failed, 1 some step failed, 2 usage or file error
    """;

// Compressed proofs unless --uncompressed: the Writer compresses against the database the proofs were made against.
bool uncompressed = args.Contains("--uncompressed");
args = args.Where(a => a != "--uncompressed").ToArray();
TenetZfc.Metamath.Database? CompressAgainst(TenetZfc.Metamath.Database db) => uncompressed ? null : db;

if (args.Length == 5 && args[0] == "emit")
{
    return Emit(args[1], args[2], args[3], args[4], uncompressed);
}
if (args.Length >= 5 && args[0] == "define")
{
    // Milestone 3: definitions through the generic model, each with its definitional equation.
    var dt = new Terms();
    TenetZfc.Environment denv = Reader.ReadExport(dt, args[1]);
    var dpr = new TenetZfc.Metamath.Prover(TenetZfc.Metamath.Database.Read(args[2]));
    var model = new Model(dt, denv, dpr);
    var theorems = new TenetZfc.Metamath.Writer(Path.GetFileName(args[2]), "Lean definitions translated by tenet-zfc's model (docs/milestone3.md)", CompressAgainst(dpr.Database));
    var proved = new List<(string Label, TenetZfc.Metamath.Expr Statement, List<string> Proof, string[] Distinct, string Name)>();
    int status = 0;
    foreach (string name in args[4..])
    {
        try
        {
            var (stmt, proof, distinct) = model.Equation(dt.Of(name));
            proved.Add(($"lean-{name}-eq", stmt, proof, distinct, $"The definitional equation of {name}."));
            Console.WriteLine($"{name}: {stmt} ({proof.Count} proof steps)");
            if (name == "Quot.lift")
            {
                // The quotient's computation rule: Quot.lift f h (Quot.mk r a) = f a.
                var (qstmt, qproof, qdistinct) = model.QuotLiftIota();
                proved.Add(($"lean-{name}-iota", qstmt, qproof, qdistinct, "The computation rule of the quotient: Quot.lift f h (Quot.mk r a) = f a."));
                Console.WriteLine($"{name} (computation rule): {qstmt} ({qproof.Count} proof steps)");
            }
            if (name == "Classical.choice")
            {
                // Choice picks an element of α, given a well-ordering of the universe.
                var (cstmt, cproof, cdistinct) = model.ChoiceSpec();
                proved.Add(($"lean-{name}-spec", cstmt, cproof, cdistinct, "Classical.choice picks an element of a nonempty type, given a well-ordering W of the universe."));
                Console.WriteLine($"{name} (picks an element): {cstmt} ({cproof.Count} proof steps)");
            }
            if (denv.Find(dt.Of(name))?.Kind == ConstKind.Constructor)
            {
                // A constructor also has its computation rule: the recursor on it reduces to its minor premise.
                try
                {
                    var (istmt, iproof, idistinct) = model.Iota(dt.Of(name));
                    proved.Add(($"lean-{name}-iota", istmt, iproof, idistinct, $"The computation rule of the recursor on {name}."));
                    Console.WriteLine($"{name} (computation rule): {istmt} ({iproof.Count} proof steps)");
                }
                catch (Model.Refused e) when (e.Message.Contains("only into Prop"))
                {
                    Console.WriteLine($"{name} (computation rule): none needed: {e.Message}");
                }
            }
        }
        catch (Model.Refused e)
        {
            Console.WriteLine($"{name}: refused: {e.Message}");
            status = 1;
        }
    }
    theorems.Raw(model.Declarations);
    foreach (var p in proved)
    {
        theorems.Theorem(p.Label, p.Name, p.Statement, p.Proof, p.Distinct);
    }
    File.WriteAllText(args[3], theorems.ToString());
    return status;
}
if (args.Length == 3 && args[0] == "bridge")
{
    // Milestone 3: the bridge lemmas recursive types rest on, written as set.mm theorems.
    var bdb = TenetZfc.Metamath.Database.Read(args[1]);
    var bpr = new TenetZfc.Metamath.Prover(bdb);
    var rb = new Recursion(bpr);
    var (stmt, proof, distinct) = rb.RankFr();
    Console.WriteLine($"lean-rankfr: {stmt} ({proof.Count} proof steps)");
    var bw = new TenetZfc.Metamath.Writer(Path.GetFileName(args[1]), "tenet-zfc bridge lemmas for recursive types (docs/milestone3.md)", CompressAgainst(bdb));
    bw.Theorem("lean-rankfr", "Smaller rank is a well-founded relation on any class.", stmt, proof, distinct);
    File.WriteAllText(args[2], bw.ToString());
    return 0;
}
if (args.Length >= 4 && args[0] == "nat-bridge")
{
    // Milestone 3: bridge theorems from the model's Nat to set.mm's NN0 (docs/bridges.md).
    try
    {
        var numerals = args[4..].Select(System.Numerics.BigInteger.Parse).ToList();
        var (text, proved) = NatBridge.Emit(args[1], args[2], numerals, compress: !uncompressed);
        foreach (var th in proved)
        {
            Console.WriteLine($"{th.Label}: {th.Statement} ({th.Proof.Count} proof steps)");
        }
        File.WriteAllText(args[3], text);
    }
    catch (Model.Refused e)
    {
        Console.Error.WriteLine($"refused: {e.Message}");
        return 1;
    }
    return 0;
}
if (args.Length == 2 && args[0] == "model-survey")
{
    // Milestone 3: which definitions the generic model translates, and the first thing that stops each of the others.
    var mt = new Terms();
    TenetZfc.Environment menv = Reader.ReadExport(mt, args[1]);
    var reasons = new Dictionary<string, int>();
    var blockers = new Dictionary<string, int>();
    int ok = 0, total = 0;
    foreach (ConstInfo c in menv.All.Where(c => c.Kind == ConstKind.Definition))
    {
        total++;
        try
        {
            // A fresh model per definition: each counts on its own, dependencies included.
            new Model(mt, menv, new TenetZfc.Metamath.Prover(new TenetZfc.Metamath.Database()), dryRun: true).Define(c.Name);
            ok++;
        }
        catch (Model.Refused e)
        {
            string first = e.Message.Split(' ')[0];
            if (e.Message.Contains("an inductive type")) blockers[first] = blockers.GetValueOrDefault(first) + 1;
            string why = System.Text.RegularExpressions.Regex.Replace(e.Message, @"^\S+ is not", "X is not");
            why = System.Text.RegularExpressions.Regex.Replace(why, @"\(.*\)$", "");
            reasons[why] = reasons.GetValueOrDefault(why) + 1;
        }
    }
    // The inductive types, by shape: what the model must handle, and in what order.
    var shapes = new Dictionary<string, int>();
    foreach (ConstInfo c in menv.All.Where(c => c.Kind == ConstKind.Inductive))
    {
        Expr ty = c.Type;
        while (ty is Binder { IsPi: true } pb) ty = pb.Body;
        bool prop = ty is Sort { Level: LZero };
        int types = c.BlockMembers.Count(m => menv.Find(m)?.Kind == ConstKind.Inductive);
        string shape = string.Join(", ", new[] { prop ? "Prop" : "Type", c.NumIndices > 0 ? "indexed" : "", types > 1 ? "mutual" : "",
            c.NumNested > 0 ? "nested" : "", c.IsRec ? "recursive" : "" }.Where(x => x != ""));
        shapes[shape] = shapes.GetValueOrDefault(shape) + 1;
    }
    Console.WriteLine("inductive types by shape:");
    foreach (var kv in shapes.OrderByDescending(kv => kv.Value)) Console.WriteLine($"  {kv.Value,7}  {kv.Key}");
    Console.WriteLine($"definitions: {total}, translated with all they use: {ok}");
    foreach (var kv in reasons.OrderByDescending(kv => kv.Value).Take(25)) Console.WriteLine($"  {kv.Value,7}  {kv.Key}");
    Console.WriteLine("the inductive type that stops each definition first:");
    foreach (var kv in blockers.OrderByDescending(kv => kv.Value).Take(25)) Console.WriteLine($"  {kv.Value,7}  {kv.Key}");
    return 0;
}
if (args.Length == 2 && args[0] == "survey")
{
    // How much of an export the translator covers, and what to add next.
    var st0 = new Terms();
    var r = new Survey(st0, Reader.ReadExport(st0, args[1])).Run();
    Console.WriteLine($"theorems: {r.Theorems}");
    Console.WriteLine($"statements translated by the table: {r.StatementsTranslated}");
    Console.WriteLine("why the others aren't:");
    foreach ((string why, int n) in r.Reasons) Console.WriteLine($"  {n,7}  {why}");
    Console.WriteLine("constants outside the table, by the number of statements (and statements with proofs) that mention them:");
    foreach ((Name c, int s, int f) in r.Blockers) Console.WriteLine($"  {s,7} {f,7}  {c}");
    Console.WriteLine("theorems whose constants are all covered, after adding the top k of that ranking:");
    Console.WriteLine("        k  statements  with proofs");
    foreach ((int k, int s, int f) in r.Curve) Console.WriteLine($"  {k,7}  {s,10}  {f,11}");
    return 0;
}
if (args.Length >= 4 && args[0] == "mm-parse")
{
    // Diagnostics: how long set.mm takes to read, and to parse one expression into its syntax proof.
    var sw0 = Stopwatch.StartNew();
    var db0 = TenetZfc.Metamath.Database.Read(args[1]);
    Console.WriteLine($"read set.mm in {sw0.Elapsed.TotalSeconds:F2}s");
    var pr0 = new TenetZfc.Metamath.Prover(db0);
    sw0.Restart();
    var proof0 = pr0.SyntaxProof(new TenetZfc.Metamath.Expr(args[2], args[3..].SelectMany(x => x.Split(' ', StringSplitOptions.RemoveEmptyEntries)).ToList()));
    Console.WriteLine($"parsed in {sw0.Elapsed.TotalMilliseconds:F0}ms: {string.Join(' ', proof0)}");
    return 0;
}
if (args.Length != 3 || args[0] != "replay")
{
    Console.Error.WriteLine(Usage);
    return 2;
}
try
{
    var sw = Stopwatch.StartNew();
    var terms = new Terms();
    TenetZfc.Environment env = Reader.ReadExport(terms, args[1]);
    List<DeclTrace> traces = Reader.ReadTrace(terms, args[2]);
    ReplayReport report = new Replayer(terms, env).Replay(traces);
    Console.Write(report.Format());
    Console.WriteLine();
    int open = report.Count(Verdict.Unsupported) + report.Count(Verdict.NotYet);
    Console.WriteLine($"{(report.Ok ? "OK" : "FAILED")} in {sw.Elapsed.TotalSeconds:F1}s. "
        + (report.Ok && open == 0 ? "Every step replayed." : $"{open} steps not replayed; see docs/trace-format.md.")
        + (report.BlocksChecked > 0 ? $" {report.BlocksChecked} inductive blocks checked, recursors derived." : "")
        + (report.BlocksTypesChecked > 0 ? $" {report.BlocksTypesChecked} inductive blocks: only types checked." : "")
        + (report.BlocksNested > 0 ? $" {report.BlocksNested} nested inductive blocks not replayed." : "")
        + (report.BlocksNotTraced > 0 ? $" {report.BlocksNotTraced} blocks not concluded." : ""));
    return report.Ok ? 0 : 1;
}
catch (Exception e) when (e is IOException or TenetZfc.FormatException or System.Text.Json.JsonException)
{
    Console.Error.WriteLine("tenet-zfc: " + e.Message);
    return 2;
}

// Replay a trace, then emit set.mm theorems for the theorems whose trace replayed in full and that the emitter covers.
static int Emit(string export, string tracePath, string setmm, string output, bool uncompressed)
{
    var terms = new Terms();
    TenetZfc.Environment env = Reader.ReadExport(terms, export);
    List<DeclTrace> traces = Reader.ReadTrace(terms, tracePath);
    ReplayReport report = new Replayer(terms, env).Replay(traces);
    var failed = new HashSet<string>(report.Failures.Select(f => $"{f.Decl}").Concat(report.Unsupported.Select(f => $"{f.Decl}")));
    Console.WriteLine($"replayed {report.Declarations} declarations, {report.Steps} steps, {report.Failures.Count} failures");

    var db = TenetZfc.Metamath.Database.Read(setmm);
    var pr = new TenetZfc.Metamath.Prover(db);
    var emitter = new Emitter(terms, pr, new Bridge(pr, db));
    var w = new TenetZfc.Metamath.Writer(Path.GetFileName(setmm), $"Generated by tenet-zfc emit from {Path.GetFileName(export)}.", uncompressed ? null : db);
    int emitted = 0, matched = 0;
    var statements = new StatementTranslator(terms);
    var listInduction = new ListInduction(terms, env, pr);
    foreach (DeclTrace d in traces)
    {
        if (env.Find(d.Decl) is not { Kind: ConstKind.Theorem } thm)
        {
            continue;
        }
        if (failed.Contains($"{d.Decl}"))
        {
            Console.WriteLine($"  {d.Decl}: not emitted, its trace did not replay in full");
            continue;
        }
        string label = "lean-" + new string($"{d.Decl}".Select(c => char.IsAsciiLetterOrDigit(c) || c is '.' or '_' or '-' ? c : '_').ToArray());
        (var proof, string? why) = emitter.EmitEquation(thm, d);
        if (proof is (List<string> steps, TenetZfc.Metamath.Expr proves))
        {
            w.Theorem(label, $"The Lean theorem {d.Decl}, from its replayed trace. Its statement is translated by the Nat arithmetic table of docs/interpretation.md.", proves, steps);
            Console.WriteLine($"  {d.Decl}: {proves}  ({steps.Count} proof steps, from the trace)");
            emitted++;
            continue;
        }
        // A proof by induction on a list: translated from the proof term (both cases) and assembled through wrdind.
        if (thm.Value is not null && TryListInduction(listInduction, thm) is (List<string> ls, TenetZfc.Metamath.Expr lp))
        {
            w.Theorem(label, $"The Lean theorem {d.Decl}, translated from its proof term: both cases of its List.rec, assembled through wrdind on reversed words.", lp, ls, ListInduction.Distinct);
            Console.WriteLine($"  {d.Decl}: {lp}  ({ls.Count} proof steps, from its proof term)");
            emitted++;
            continue;
        }
        // Not provable by the arithmetic emitter: translate the statement and look for a set.mm theorem it instantiates.
        // Such a theorem is a cross-check of the translation, with set.mm's proof, not a translation of Lean's.
        if (statements.Statement(thm.Type) is not string stmt)
        {
            Console.WriteLine($"  {d.Decl}: not emitted, {why}; statement: {statements.Why}");
            continue;
        }
        var target = TenetZfc.Metamath.Expr.Of(stmt);
        if (pr.FindInstance(target) is not (string match, var subst))
        {
            Console.WriteLine($"  {d.Decl}: not emitted; statement {stmt} has no instance in set.mm (proof translation not built yet)");
            continue;
        }
        var inst = pr.Apply(match, subst);
        w.Theorem(label, $"The statement of the Lean theorem {d.Decl}, translated by docs/interpretation.md. CROSS-CHECK: the proof is set.mm's {match}, not a translation of Lean's proof.", inst.Proves, inst.Proof);
        Console.WriteLine($"  {d.Decl}: {inst.Proves}  (statement found in set.mm as {match}; proof not translated)");
        matched++;
    }
    File.WriteAllText(output, w.ToString());
    Console.WriteLine($"{emitted} theorems proved from their traces or proof terms and {matched} statements cross-checked against set.mm, written to {output}. Check them with both verifiers.");
    return report.Ok ? 0 : 1;
}

// The list-induction translation, or null when the theorem's proof is not of the shape it handles.
static (List<string>, TenetZfc.Metamath.Expr)? TryListInduction(ListInduction li, ConstInfo thm)
{
    try
    {
        (var proof, string? _) = li.Prove(thm);
        return proof;
    }
    catch (InvalidOperationException)
    {
        return null;   // a term or step outside what the translator covers
    }
}
