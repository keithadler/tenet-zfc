using System.Diagnostics;
using TenetZfc;
using TenetZfc.Cli;

const string Usage = """
    tenet-zfc - Lean 4 proofs to ZFC, checked by Metamath verifiers (github.com/keithadler/tenet-zfc)

    usage:
      tenet-zfc run <Module | File.lean | export.ndjson> [--out <dir>] [options]
                                                         export, trace, translate and verify in one command, with a
                                                         report on each declaration (tenet-zfc run --help)
      tenet-zfc verify <out.mm>...                       check outputs with metamath-exe, mmverify.py and mmj2
      tenet-zfc --version
      tenet-zfc replay <export.ndjson> <trace.ndjson>   re-derive the steps of a Tenet trace, without Tenet
      tenet-zfc emit <export.ndjson> <trace.ndjson> <set.mm> <out.mm>
                                                         replay, then write set.mm theorems for the theorems the
                                                         emitter covers (Nat arithmetic equations, and induction
                                                         on lists like List.length_append)
      tenet-zfc define <export.ndjson> <set.mm> <out.mm> <name>...
                                                         milestone 3: translate definitions by the generic model,
                                                         each with its definitional equation as a theorem; universe
                                                         parameters at 0 unless the name gives levels (Eq.{1})
      tenet-zfc define-all <export.ndjson> <set.mm> <outdir> [--chunk-size N] [--chunks a,b-c,…] [--jobs N] [--budget seconds]
                                                         milestone 3 at scale: every constant the model handles, with
                                                         equations and computation rules, as chunk-NNNN.mm files that
                                                         verify independently (scripts/verify-all); refusals are listed
                                                         per constant in chunk-NNNN.tsv
      tenet-zfc theorem-all <export.ndjson> <set.mm> <outdir> [--every N] [--chunk-size N] [--chunks a,b-c,…] [--jobs N] [--budget seconds] [--redo]
                                                         every theorem (or every Nth) proved through the model, as
                                                         chunk-NNNN.mm files that share lemmas within a chunk and verify
                                                         independently; outcomes per theorem in chunk-NNNN.tsv; resumes
                                                         where it stopped (scripts/summarize-all for the totals)
      tenet-zfc library <export.ndjson> <set.mm> <out.mm> <name | lean-ty-label | @file>... [--budget seconds]
                                                         a library of typing lemmas, each proved once, for theorem and
                                                         theorem-all to cite with --library instead of proving them in
                                                         every run; with --library itself, a layer on another library
      tenet-zfc bridge <set.mm> <out.mm>                 milestone 3: the bridge lemmas recursive types rest on
      tenet-zfc theorem <export.ndjson> <set.mm> <out.mm> <name>...
                                                         milestone 3: prove Lean theorems through the generic model
                                                         (tower mode), |- ( hypotheses -> (/) e. [statement] )
      tenet-zfc nat-bridge <export.ndjson> <set.mm> <out.mm> [<n>|<theorem>...]
                                                         milestone 3: prove that the model's Nat is NN0 (zero, succ,
                                                         Nat.add and literals, each numeral n given), from an export
                                                         with Nat.add (docs/bridges.md); each theorem named (such as
                                                         Nat.add_zero) is proved through the model and restated in
                                                         set.mm's arithmetic; with --lowered, in a tower of weak
                                                         universes that ZFC proves exists, so each restated theorem
                                                         also comes out in plain ZFC (docs/milestone4.md)
      tenet-zfc list-bridge <export.ndjson> <set.mm> <out.mm> [<theorem>...] [--bridge-only]
                                                         prove that the model's List A is Word A (nil, cons, length,
                                                         append), with the Nat bridge; each theorem named (such as
                                                         List.length_append) is proved through the model and restated
                                                         in set.mm's words (docs/bridges.md, docs/demo.md)
      tenet-zfc survey <export.ndjson>                   how many theorem statements the translator covers, and
                                                         which constants block the rest

    emit, define, define-all, bridge and nat-bridge write proofs in Metamath's compressed format, sharing every repeated subproof;
    add --uncompressed (anywhere) for flat label lists.

    theorem, theorem-all and library take --library <lib.mm> (anywhere): a library written by tenet-zfc library, beside
    set.mm. Its lemmas are cited, not proved again, and the output includes the library by name (docs/milestone3.md).

    the model interprets universes as a tower of Grothendieck universes, one per level, so that structurally
    recursive definitions mean what Lean means; add --single-universe (anywhere) for the old model with one universe
    for every level, under which they collapse (docs/milestone3.md). Each output's header states its assumptions.

    make a trace with Tenet (github.com/keithadler/tenet, main):
      tenet check <export.ndjson> --trace <trace.ndjson>

    exit status: 0 no step failed, 1 some step failed, 2 usage or file error
    """;

if (args.Length >= 1 && args[0] == "run")
{
    return RunCommand.Execute(args[1..]);
}
if (args.Length >= 1 && args[0] == "verify")
{
    return VerifyCommand.Execute(args[1..]);
}
if (args.Length == 1 && args[0] is "--version" or "version")
{
    Console.WriteLine($"tenet-zfc {BuildInfo.Version}");
    return 0;
}
if (args.Length == 1 && args[0] is "--help" or "-h" or "help")
{
    Console.WriteLine(Usage);
    return 0;
}

// Compressed proofs unless --uncompressed: the Writer compresses against the database the proofs were made against.
bool uncompressed = args.Contains("--uncompressed");
args = args.Where(a => a != "--uncompressed").ToArray();
TenetZfc.Metamath.Database? CompressAgainst(TenetZfc.Metamath.Database db) => uncompressed ? null : db;

if (args.Length == 5 && args[0] == "emit")
{
    return Emit(args[1], args[2], args[3], args[4], uncompressed);
}
// The model's universes: a tower of Grothendieck universes, one per level (the default), or with --single-universe one
// universe for every level, under which structurally recursive definitions collapse (docs/milestone3.md). --tower is
// accepted for scripts written when the tower was opt-in.
bool singleUniverse = args.Contains("--single-universe");
// Universe elimination (docs/milestone4.md): a tower of weak universes, which ZFC proves exists, instead of Grothendieck universes.
bool lowered = args.Contains("--lowered");
args = args.Where(a => a is not "--single-universe" and not "--tower" and not "--lowered").ToArray();
// A library of typing lemmas (tenet-zfc library) for theorem, theorem-all and library itself to cite: a .mm file beside
// set.mm that includes it. Outputs then include the library by name, as they otherwise include set.mm.
string? library = null;
if (Array.IndexOf(args, "--library") is int li and >= 0 && li + 1 < args.Length)
{
    library = args[li + 1];
    args = args.Where((_, i) => i != li && i != li + 1).ToArray();
}
if (args.Length >= 5 && args[0] == "define")
{
    // Milestone 3: definitions through the generic model, each with its definitional equation. In tower mode the
    // universe argument is a tower of universes and constants are monomorphized first (docs/milestone3.md).
    var dt = new Terms();
    TenetZfc.Environment denv = Reader.ReadExport(dt, args[1]);
    Monomorph? mono = null;
    if (!singleUniverse)
    {
        mono = new Monomorph(dt, denv);
        denv = mono.Env;
    }
    var dpr = new TenetZfc.Metamath.Prover(TenetZfc.Metamath.Database.Read(args[2]));
    var model = new Model(dt, denv, dpr, tower: !singleUniverse);
    var theorems = new TenetZfc.Metamath.Writer(Path.GetFileName(args[2]), "Lean definitions translated by tenet-zfc's model (docs/milestone3.md)", CompressAgainst(dpr.Database));
    var proved = new List<(string Label, TenetZfc.Metamath.Expr Statement, List<string> Proof, string[] Distinct, string Name)>();
    int status = 0;
    foreach (string given in args[4..])
    {
        string name = given;
        try
        {
            // Each universe parameter at level 0, written c.{0,…}, unless the name gives the levels (Eq.{1}); a
            // recursor keeps its motive level. The Name itself is kept: reparsing its text loses numeric parts.
            Name nm = mono is not null ? InstanceOf(dt, mono, given) : NameOf(dt, denv, given);
            name = $"{nm}";
            var (stmt, proof, distinct) = model.Equation(nm);
            proved.Add(($"lean-{Model.LabelOf(nm)}-eq", stmt, proof, distinct, $"The definitional equation of {name}."));
            Console.WriteLine($"{name}: {stmt} ({proof.Count} proof steps)");
            string baseOf = System.Text.RegularExpressions.Regex.Replace(name, @"\.\{[0-9,]+\}$", "");
            if (baseOf == "Quot.lift" && QuotMkFor(dt, mono, name) is Name mkInst)
            {
                // The quotient's computation rule: Quot.lift f h (Quot.mk r a) = f a (in the tower, Quot.lift.{k,l}
                // with Quot.mk.{k}; at level 0 one of them is a proof and there is nothing to compute).
                var (qstmt, qproof, qdistinct) = model.QuotLiftIota(nm, mkInst);
                proved.Add(($"lean-{Model.LabelOf(nm)}-iota", qstmt, qproof, qdistinct, "The computation rule of the quotient: Quot.lift f h (Quot.mk r a) = f a."));
                Console.WriteLine($"{name} (computation rule): {qstmt} ({qproof.Count} proof steps)");
            }
            if (baseOf == "Classical.choice" && name != "Classical.choice.{0}")
            {
                // Choice picks an element of α, given a well-ordering of the universe (of the tower's union).
                var (cstmt, cproof, cdistinct) = model.ChoiceSpec(nm);
                proved.Add(($"lean-{Model.LabelOf(nm)}-spec", cstmt, cproof, cdistinct, $"{name} picks an element of a nonempty type, given a well-ordering W of the universe{(singleUniverse ? "" : "s' union")}."));
                Console.WriteLine($"{name} (picks an element): {cstmt} ({cproof.Count} proof steps)");
            }
            if (denv.Find(nm)?.Kind == ConstKind.Constructor)
            {
                // A constructor also has its computation rule: the recursor on it reduces to its minor premise.
                try
                {
                    var (istmt, iproof, idistinct) = model.Iota(nm);
                    proved.Add(($"lean-{Model.LabelOf(nm)}-iota", istmt, iproof, idistinct, $"The computation rule of the recursor on {name}."));
                    Console.WriteLine($"{name} (computation rule): {istmt} ({iproof.Count} proof steps)");
                }
                catch (Model.Refused e) when (e.Message.Contains("only into Prop"))
                {
                    Console.WriteLine($"{name} (computation rule): none needed: {e.Message}");
                }
            }
            if (System.Text.RegularExpressions.Regex.IsMatch(name, @"\.rec_[0-9]+$"))
            {
                // A nested block's auxiliary recursor (Rose.rec_1, on List (Rose α)): the computation rule on each of the
                // nested type's constructors (List.nil, List.cons).
                foreach (var (ctor, istmt, iproof, idistinct) in model.RecursorIotas(nm))
                {
                    // "--" never occurs in an escaped name, so these labels can't meet a constructor's lean-c-iota.
                    proved.Add(($"lean-{Model.LabelOf(nm)}--{Model.LabelOf(ctor)}-iota", istmt, iproof, idistinct, $"The computation rule of {name} on {ctor}."));
                    Console.WriteLine($"{name} on {ctor} (computation rule): {istmt} ({iproof.Count} proof steps)");
                }
            }
        }
        catch (Model.Refused e)
        {
            Console.WriteLine($"{name}: refused: {e.Message}");
            status = 1;
        }
    }
    theorems.Assumptions(model.Assumptions());
    theorems.Raw(model.Declarations);
    foreach (var p in proved)
    {
        theorems.Theorem(p.Label, p.Name, p.Statement, p.Proof, p.Distinct);
    }
    File.WriteAllText(args[3], theorems.ToString());
    return status;
}
if (args.Length >= 4 && args[0] == "define-all")
{
    return DefineAllCommand(args[1], args[2], args[3], args[4..], uncompressed, singleUniverse);
}
if (args.Length >= 4 && args[0] == "theorem-all")
{
    return TheoremAllCommand(args[1], args[2], args[3], args[4..], uncompressed, library);
}
if (args.Length >= 5 && args[0] == "theorem")
{
    // Milestone 3: Lean theorems proved through the generic model, in its tower mode (docs/milestone3.md).
    var tt = new Terms();
    TenetZfc.Environment tenv = Reader.ReadExport(tt, args[1]);
    var tpr = new TenetZfc.Metamath.Prover(TenetZfc.Metamath.Database.ReadChain(library ?? args[2]));
    var translator = new TheoremTranslator(tt, tenv, tpr);
    var tw = new TenetZfc.Metamath.Writer(Path.GetFileName(library ?? args[2]), "Lean theorems proved through tenet-zfc's model (docs/milestone3.md)", CompressAgainst(tpr.Database));
    var done = new List<(string Label, TenetZfc.Metamath.Expr Statement, List<string> Proof, string Name)>();
    int tstatus = 0;
    foreach (string name in args[4..])
    {
        var sw1 = Stopwatch.StartNew();
        int lemmasBefore = translator.LemmaSteps.Count;
        long stepsBefore = translator.LemmaSteps.Values.Sum();
        try
        {
            var (stmt, proof) = translator.Prove(tt.Of(name));
            // Replayed here (every step's hypotheses, and the $d conditions), so a broken proof fails on its own.
            _ = TenetZfc.Metamath.DistinctVars.Required(tpr.Database, proof);
            done.Add(($"lean-thm-{Model.LabelOf(tt.Of(name))}", stmt, proof, name));
            Console.WriteLine($"{name}: {stmt} ({tpr.Database.Shared.Size(proof)} proof steps, {sw1.Elapsed.TotalSeconds:F1}s)");
            Console.WriteLine($"{name}: {translator.LemmaSteps.Count - lemmasBefore} new lemmas ({translator.LemmaSteps.Values.Sum() - stepsBefore} flat steps)");
            // A universe-polymorphic theorem is proved at one instance, every parameter at level 0 (for a Sort u
            // parameter that is Prop): say which, so a report doesn't read it as the theorem at every level.
            if (tenv.Find(tt.Of(name)) is { LevelParams.Length: > 0 } poly)
            {
                Console.WriteLine($"{name}: at {name}.{{{string.Join(",", poly.LevelParams.Select(_ => "0"))}}}, universe parameters {string.Join(", ", poly.LevelParams.Select(l => $"{l}"))} at level 0");
            }
        }
        catch (Model.Refused e)
        {
            Console.WriteLine($"{name}: refused: {e.Message}");
            if (System.Environment.GetEnvironmentVariable("TENET_DEBUG") is not null)
            {
                Console.Error.WriteLine(e.StackTrace);
            }
            tstatus = 1;
        }
        catch (InvalidOperationException e)
        {
            // A proof step that doesn't check: a bug in the translator, reported, and the other theorems go on.
            Console.WriteLine($"{name}: failed: {e.Message}");
            if (System.Environment.GetEnvironmentVariable("TENET_DEBUG") is not null)
            {
                Console.Error.WriteLine(e.StackTrace);
            }
            tstatus = 1;
        }
    }
    tw.Assumptions(translator.Model.Assumptions());
    tw.Raw(translator.Declarations);
    foreach (var d in done)
    {
        var dv = TenetZfc.Metamath.DistinctVars.Required(tpr.Database, d.Proof);
        var proofOut = tw.Compressed ? d.Proof : tpr.Database.Shared.Expand(d.Proof);
        tw.Theorem(d.Label, $"The Lean theorem {d.Name}, proved through the model from its proof term.", d.Statement, proofOut, dv.Select(p => $"{p.Item1} {p.Item2}"));
    }
    File.WriteAllText(args[3], tw.ToString());
    if (library is not null)
    {
        Console.WriteLine($"library {Path.GetFileName(library)}: {translator.LibraryLemmas} typing lemmas cited, not proved again");
    }
    return tstatus;
}
if (args.Length >= 5 && args[0] == "library")
{
    // A library of typing lemmas, each proved once (docs/milestone3.md, "A library of lemmas"). Every chunk of
    // theorem-all used to prove the lemmas of the constants its theorems use from nothing; with --library it cites
    // these. The constants are named as theorem names them, or by a lemma's label (lean-ty-Nat.le_trans), or listed
    // one per line in @file. With --library itself, this library is built on another and includes it.
    int lbudget = 600;
    if (Array.IndexOf(args, "--budget") is int bi and >= 0 && bi + 1 < args.Length && int.TryParse(args[bi + 1], out int lb) && lb > 0)
    {
        lbudget = lb;
        args = args.Where((_, i) => i != bi && i != bi + 1).ToArray();
    }
    var lt = new Terms();
    TenetZfc.Environment lenv = Reader.ReadExport(lt, args[1]);
    var lpr = new TenetZfc.Metamath.Prover(TenetZfc.Metamath.Database.ReadChain(library ?? args[2]));
    var ltr = new TheoremTranslator(lt, lenv, lpr);
    var wanted = args[4..].SelectMany(a => a.StartsWith('@') ? File.ReadAllLines(a[1..]).Select(l => l.Trim()).Where(l => l != "" && !l.StartsWith('#')) : [a]).ToList();
    int lproved = 0, lcited = 0;
    foreach (string given in wanted)
    {
        var lsw = Stopwatch.StartNew();
        int citedBefore = ltr.LibraryLemmas, lemmasBefore = ltr.LemmaSteps.Count;
        lpr.Deadline = DateTime.UtcNow.AddSeconds(lbudget);
        try
        {
            string label = ltr.TypeConstant(given);
            bool cited = ltr.LemmaSteps.Count == lemmasBefore && ltr.LibraryLemmas > citedBefore;
            if (cited) lcited++; else lproved++;
            Console.WriteLine($"{given}: {label} ({(cited ? "already in the library" : $"{ltr.LemmaSteps.Count - lemmasBefore} new lemmas")}, {lsw.Elapsed.TotalSeconds:F1}s)");
        }
        catch (Model.Refused e)
        {
            Console.WriteLine($"{given}: refused: {e.Message}");
        }
        catch (TimeoutException)
        {
            Console.WriteLine($"{given}: timeout: over the {lbudget}s budget");
        }
        catch (InvalidOperationException e)
        {
            // A proof step that doesn't check: a bug in the translator, reported, and the others go on.
            Console.WriteLine($"{given}: failed: {e.Message}");
        }
        lpr.Deadline = null;
    }
    var lw = new TenetZfc.Metamath.Writer(Path.GetFileName(library ?? args[2]), "A library of typing lemmas for tenet-zfc's model, each proved once (docs/milestone3.md)", CompressAgainst(lpr.Database));
    lw.Assumptions(ltr.Model.Assumptions());
    lw.Raw(ltr.Declarations);
    File.WriteAllText(args[3], lw.ToString());
    Console.WriteLine($"library {Path.GetFileName(args[3])}: {ltr.LemmaSteps.Count} lemmas written for {lproved} of {wanted.Count} constants"
        + (lcited > 0 ? $", {lcited} already in {Path.GetFileName(library!)}" : ""));
    return lproved + lcited == wanted.Count ? 0 : 1;
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
    var (sstmt, sproof, sdistinct) = rb.RankSe();
    Console.WriteLine($"{Recursion.RankSeLabel}: {sstmt} ({sproof.Count} proof steps)");
    bw.Theorem(Recursion.RankSeLabel, "Smaller rank is a set-like relation on every set.", sstmt, sproof, sdistinct);
    File.WriteAllText(args[2], bw.ToString());
    return 0;
}
if (args.Length >= 4 && args[0] == "nat-bridge")
{
    // Milestone 3: bridge theorems from the model's Nat to set.mm's NN0 (docs/bridges.md).
    try
    {
        // Numerals get F ( n ) = n; names are theorems to prove through the model and restate in NN0 (tower mode).
        var numerals = args[4..].Where(a => System.Numerics.BigInteger.TryParse(a, out _)).Select(System.Numerics.BigInteger.Parse).ToList();
        var restate = args[4..].Where(a => !System.Numerics.BigInteger.TryParse(a, out _)).ToList();
        if (singleUniverse && restate.Count > 0)
        {
            Console.Error.WriteLine("nat-bridge: restating theorems needs the tower model");
            return 2;
        }
        var (text, proved) = NatBridge.Emit(args[1], args[2], numerals, compress: !uncompressed, tower: !singleUniverse, restate: restate, lowered: lowered);
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
if (args.Length >= 4 && args[0] == "list-bridge")
{
    // The List/Word bridge, and Lean theorems about List restated in set.mm's words (docs/bridges.md, docs/demo.md).
    try
    {
        bool bridgeOnly = args.Contains("--bridge-only");
        var names = args[4..].Where(a => !a.StartsWith("--", StringComparison.Ordinal)).ToList();
        var (text, proved) = ListBridge.Emit(args[1], args[2], names, compress: !uncompressed, bridgeOnly: bridgeOnly, log: m => Console.Error.WriteLine(m));
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
    TenetZfc.Environment orig = menv;
    var reasons = new Dictionary<string, int>();
    var blockers = new Dictionary<string, int>();
    int ok = 0, total = 0;
    foreach (ConstInfo c in orig.All.Where(c => c.Kind == ConstKind.Definition).ToList())
    {
        total++;
        try
        {
            // A fresh model per definition: each counts on its own, dependencies included. In tower mode, over a fresh
            // monomorphization, with the definition's universe parameters at 0.
            var spr = new TenetZfc.Metamath.Prover(new TenetZfc.Metamath.Database());
            if (singleUniverse)
            {
                new Model(mt, orig, spr, dryRun: true, tower: false).Define(c.Name);
            }
            else
            {
                var smono = new Monomorph(mt, orig);
                Name inst = smono.Instance(c.Name, c.LevelParams.Select(_ => mt.Zero).ToArray());
                new Model(mt, smono.Env, spr, dryRun: true, tower: true).Define(inst);
            }
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
if (args.Length >= 3 && args[0] == "show")
{
    // Diagnostics: a constant's kind, type and value, as the export has them.
    var sht = new Terms();
    TenetZfc.Environment shenv = Reader.ReadExport(sht, args[1]);
    foreach (string name in args[2..])
    {
        ConstInfo? c = shenv.Find(sht.Of(name));
        Console.WriteLine(c is null ? $"{name}: not in the export"
            : $"{name} ({c.Kind}, params {c.NumParams}, fields {c.NumFields})\n  type:  {c.Type}\n  value: {c.Value ?? c.OpaqueValue}\n");
    }
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

// Milestone 3 at scale: every constant the model handles, in chunks that verify independently (scripts/verify-all).
static int DefineAllCommand(string export, string setmm, string outDir, string[] opts, bool uncompressed, bool singleUniverse)
{
    int chunkSize = 100, jobs = 1, budget = 600;
    string? only = null;
    for (int i = 0; i < opts.Length; i++)
    {
        switch (opts[i])
        {
            case "--chunk-size" when i + 1 < opts.Length && int.TryParse(opts[i + 1], out int n) && n > 0:
                chunkSize = n; i++; break;
            case "--budget" when i + 1 < opts.Length && int.TryParse(opts[i + 1], out int b) && b > 0:
                budget = b; i++; break;
            case "--jobs" when i + 1 < opts.Length && int.TryParse(opts[i + 1], out int j) && j > 0:
                // chunks translated in parallel: they share the export (read once) but each has its own model and database
                jobs = j; i++; break;
            case "--chunks" when i + 1 < opts.Length:
                // chunk indices and ranges, a,b-c,… (inclusive): to resume a run, or redo some of it
                only = opts[++i];
                break;
            default:
                Console.Error.WriteLine($"tenet-zfc define-all: unknown option {opts[i]}");
                return 2;
        }
    }
    var sw = Stopwatch.StartNew();
    var terms = new Terms();
    TenetZfc.Environment env = Reader.ReadExport(terms, export);
    Directory.CreateDirectory(outDir);
    var run = new DefineAll(terms, env, setmm, compress: !uncompressed) { BudgetSeconds = budget, Tower = !singleUniverse };
    List<ConstInfo> targets = run.Targets();
    int chunks = (targets.Count + chunkSize - 1) / chunkSize;
    Console.WriteLine($"read {export} in {sw.Elapsed.TotalSeconds:F0}s: {targets.Count} constants to translate, in {chunks} chunks of {chunkSize}");
    List<int> todo = only is null ? Enumerable.Range(0, chunks).ToList()
        : only.Split(',').SelectMany(part => part.Split('-') is [string a, string b]
            ? Enumerable.Range(int.Parse(a), int.Parse(b) - int.Parse(a) + 1) : [int.Parse(part)]).Where(k => k >= 0 && k < chunks).Distinct().ToList();
    var results = new List<DefineAll.Outcome>[todo.Count];
    // Each chunk on a thread of its own with a large stack: the prover recurses over terms, and a stack overflow can't be
    // caught, so on a default-sized stack one deep term would end the whole run.
    int next = 0;
    var workers = Enumerable.Range(0, Math.Min(jobs, todo.Count)).Select(_ => new Thread(() =>
    {
        for (int i; (i = Interlocked.Increment(ref next) - 1) < todo.Count;)
        {
            RunChunk(i, todo[i]);
        }
    }, 256 * 1024 * 1024)).ToList();
    workers.ForEach(w => w.Start());
    workers.ForEach(w => w.Join());
    void RunChunk(int i, int k)
    {
        var csw = Stopwatch.StartNew();
        List<DefineAll.Outcome> outcomes = run.Chunk(k, targets.Skip(k * chunkSize).Take(chunkSize).ToList(), outDir);
        results[i] = outcomes;
        long size = new FileInfo(Path.Combine(outDir, $"chunk-{k:D4}.mm")).Length;
        Console.WriteLine($"chunk-{k:D4}: {outcomes.Count(o => o.Status == "ok")} of {outcomes.Count} translated, "
            + $"{outcomes.Count(o => o.Iota == "ok")} computation rules, {size / 1024} KiB, {csw.Elapsed.TotalSeconds:F0}s");
    }
    List<DefineAll.Outcome> all = results.SelectMany(r => r).ToList();
    // The summary of this invocation: counts by kind and status, and the reasons for refusals.
    var s = new System.Text.StringBuilder();
    s.AppendLine($"constants: {all.Count}, in {todo.Count} chunks of {chunkSize}, {jobs} at a time, {sw.Elapsed.TotalSeconds:F0}s");
    foreach (var g in all.GroupBy(o => o.Kind).OrderByDescending(g => g.Count()))
    {
        s.AppendLine($"  {g.Key,-12} {g.Count(),6}: {g.Count(o => o.Status == "ok"),6} translated with their equations, "
            + $"{g.Count(o => o.Status == "refused"),6} refused, {g.Count(o => o.Status == "error"),6} errors");
    }
    s.AppendLine($"computation rules: {all.Count(o => o.Iota == "ok")} proved, {all.Count(o => o.Iota == "none-needed")} none needed (into Prop), "
        + $"{all.Count(o => o.Iota == "refused")} refused, {all.Count(o => o.Iota == "error")} errors");
    s.AppendLine($"proof steps: {all.Sum(o => (long)o.EqSteps)} in equations, {all.Sum(o => (long)o.IotaSteps)} in computation rules");
    s.AppendLine("why the others aren't translated (refusals, errors, and refused computation rules):");
    foreach (var g in all.Where(o => o.Reason != "").GroupBy(o => DefineAll.Category(o.Reason)).OrderByDescending(g => g.Count()).Take(40))
    {
        s.AppendLine($"  {g.Count(),7}  {g.Key}  (e.g. {g.First().Name})");
    }
    s.AppendLine("slowest constants:");
    foreach (var o in all.OrderByDescending(o => o.Seconds).Take(10))
    {
        s.AppendLine($"  {o.Seconds,8:F1}s  {o.Name} ({o.EqSteps} + {o.IotaSteps} steps)");
    }
    Console.Write(s);
    File.WriteAllText(Path.Combine(outDir, "define-all.txt"), s.ToString());
    return 0;
}

// Theorems at scale: every theorem (or every Nth) through the model, in chunks that verify independently.
static int TheoremAllCommand(string export, string setmm, string outDir, string[] opts, bool uncompressed, string? library)
{
    int chunkSize = 50, jobs = 1, budget = 120, every = 1;
    string? only = null;
    bool redo = false;
    for (int i = 0; i < opts.Length; i++)
    {
        switch (opts[i])
        {
            case "--chunk-size" when i + 1 < opts.Length && int.TryParse(opts[i + 1], out int n) && n > 0:
                chunkSize = n; i++; break;
            case "--budget" when i + 1 < opts.Length && int.TryParse(opts[i + 1], out int b) && b > 0:
                budget = b; i++; break;
            case "--jobs" when i + 1 < opts.Length && int.TryParse(opts[i + 1], out int j) && j > 0:
                jobs = j; i++; break;
            case "--every" when i + 1 < opts.Length && int.TryParse(opts[i + 1], out int e) && e > 0:
                // a sample: every Nth theorem in export order
                every = e; i++; break;
            case "--chunks" when i + 1 < opts.Length:
                only = opts[++i];
                break;
            case "--redo":
                // prove chunks again even if their .tsv is there
                redo = true;
                break;
            default:
                Console.Error.WriteLine($"tenet-zfc theorem-all: unknown option {opts[i]}");
                return 2;
        }
    }
    var sw = Stopwatch.StartNew();
    var terms = new Terms();
    TenetZfc.Environment env = Reader.ReadExport(terms, export);
    Directory.CreateDirectory(outDir);
    var run = new TheoremAll(terms, env, setmm, compress: !uncompressed) { BudgetSeconds = budget, Library = library };
    List<ConstInfo> targets = run.Targets(every);
    int chunks = (targets.Count + chunkSize - 1) / chunkSize;
    // The run's parameters, so that a resumed run can't silently mix chunks of different shapes.
    string shape = $"export {Path.GetFileName(export)}, every {every}, chunk size {chunkSize}: {targets.Count} theorems in {chunks} chunks"
        + (library is null ? "" : $", library {Path.GetFileName(library)}");
    string shapeFile = Path.Combine(outDir, "theorem-all.shape");
    if (File.Exists(shapeFile) && File.ReadAllText(shapeFile).Trim() != shape)
    {
        Console.Error.WriteLine($"tenet-zfc theorem-all: {outDir} holds a run of another shape ({File.ReadAllText(shapeFile).Trim()}); use another folder");
        return 2;
    }
    File.WriteAllText(shapeFile, shape + "\n");
    List<int> todo = (only is null ? Enumerable.Range(0, chunks)
        : only.Split(',').SelectMany(part => part.Split('-') is [string a, string b]
            ? Enumerable.Range(int.Parse(a), int.Parse(b) - int.Parse(a) + 1) : [int.Parse(part)]).Where(k => k >= 0 && k < chunks).Distinct())
        .Where(k => redo || !File.Exists(Path.Combine(outDir, $"chunk-{k:D4}.tsv"))).ToList();
    Console.WriteLine($"read {export} in {sw.Elapsed.TotalSeconds:F0}s: {shape}; {todo.Count} chunks to prove, {jobs} at a time, {budget}s per theorem");
    int next = 0;
    var workers = Enumerable.Range(0, Math.Min(jobs, todo.Count)).Select(_ => new Thread(() =>
    {
        for (int i; (i = Interlocked.Increment(ref next) - 1) < todo.Count;)
        {
            int k = todo[i];
            var csw = Stopwatch.StartNew();
            List<TheoremAll.Outcome> outcomes = run.Chunk(k, targets.Skip(k * chunkSize).Take(chunkSize).ToList(), outDir);
            long size = new FileInfo(Path.Combine(outDir, $"chunk-{k:D4}.mm")).Length;
            Console.WriteLine($"chunk-{k:D4}: {outcomes.Count(o => o.Status == "proved")} of {outcomes.Count} proved, "
                + string.Join(", ", outcomes.Where(o => o.Status != "proved").GroupBy(o => o.Status).Select(g => $"{g.Count()} {g.Key}"))
                + $"; {size / 1024} KiB, {csw.Elapsed.TotalSeconds:F0}s");
        }
    }, 256 * 1024 * 1024)).ToList();
    workers.ForEach(w => w.Start());
    workers.ForEach(w => w.Join());
    Console.WriteLine($"done in {sw.Elapsed.TotalSeconds:F0}s; totals over every chunk so far: scripts/summarize-all {outDir}");
    return 0;
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

// A constant's name as given on the command line: as Lean prints it (Nat.add), or as its token or escaped name
// (lean.List.map-q, hint._-a.Init.Hints.1215944719._hyg.3), for names with numeric parts or characters a shell mangles.
static Name NameOf(Terms t, TenetZfc.Environment env, string given)
{
    Name plain = t.Of(given);
    if (env.Find(plain) is not null)
    {
        return plain;
    }
    try
    {
        Name escaped = NameEscape.Unescape(t, given.StartsWith("lean.", StringComparison.Ordinal) ? given[5..] : given);
        return env.Find(escaped) is not null ? escaped : plain;
    }
    catch (System.FormatException)
    {
        return plain;
    }
}

// The instance of a constant at the levels its name gives (c.{1,0}), or with every universe parameter at 0. A recursor's
// motive level may be left out: c.rec.{1} is the recursor of c.{1}.
// The Quot.mk that Quot.lift's computation rule is about: Quot.mk, or in the tower Quot.mk.{k} for Quot.lift.{k,l}; null
// at level 0, where Quot.mk or Quot.lift is a proof and there is nothing to compute.
static Name? QuotMkFor(Terms t, Monomorph? mono, string lift)
{
    if (mono is null)
    {
        return t.Of("Quot.mk");
    }
    var m = System.Text.RegularExpressions.Regex.Match(lift, @"\.\{([0-9]+),([0-9]+)\}$");
    if (!m.Success || m.Groups[1].Value == "0" || m.Groups[2].Value == "0")
    {
        return null;
    }
    return InstanceOf(t, mono, $"Quot.mk.{{{m.Groups[1].Value}}}");
}

static Name InstanceOf(Terms t, Monomorph mono, string given)
{
    var m = System.Text.RegularExpressions.Regex.Match(given, @"^(.*)\.\{([0-9]+(?:,[0-9]+)*)\}$");
    string baseName = m.Success ? m.Groups[1].Value : given;
    ConstInfo c = mono.Env.Find(NameOf(t, mono.Env, baseName)) ?? throw new Model.Refused($"{baseName} is not in the export");
    if (!m.Success)
    {
        return mono.Instance(c.Name, c.LevelParams.Select(_ => t.Zero).ToArray());
    }
    Level Lv(int k) => k == 0 ? t.Zero : t.Succ(Lv(k - 1));
    var levels = m.Groups[2].Value.Split(',').Select(x => Lv(int.Parse(x))).ToList();
    if (c.Kind == ConstKind.Recursor && levels.Count == c.LevelParams.Length - 1)
    {
        levels.Insert(0, t.Zero);
    }
    if (levels.Count != c.LevelParams.Length)
    {
        throw new Model.Refused($"{baseName} has {c.LevelParams.Length} universe parameters, given {levels.Count}");
    }
    return mono.Instance(c.Name, levels.ToArray());
}
