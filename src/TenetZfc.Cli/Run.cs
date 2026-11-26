using System.Text.Json;
using TenetZfc;

namespace TenetZfc.Cli;

/// <summary>
/// `tenet-zfc run`: from a Lean module (or a .lean file, or an export) to checked set.mm output, in one command.
/// Export with leanout; trace theorems with Tenet where it can help; translate theorems with the trace-based
/// translator or through the model, and everything else with `define`; check every output with metamath-exe,
/// mmverify.py and mmj2's definitionCheck; report each declaration as proved, refused (with the reason) or failed.
/// </summary>
public static class RunCommand
{
    public const string Usage = """
        usage: tenet-zfc run <Module | File.lean | export.ndjson> [options]

          Exports the module's declarations with leanout, traces its theorems with Tenet (when found), translates
          them (theorems with `theorem` or from their trace, everything else with `define`), checks every output with
          metamath-exe, mmverify.py and mmj2's definitionCheck, and reports each declaration as proved, refused or
          failed.

          <Module>          a module LEAN_PATH reaches (in a Lake project, run under `lake env`)
          <File.lean>       a single file, compiled first with `lean -o`; it may import what LEAN_PATH reaches
          <export.ndjson>   an existing export; name the declarations with --decl

        options:
          --out <dir>        where outputs, logs and report.json go (default: tenet-zfc-out)
          --decl <names>     only these declarations (comma-separated, or repeated)
          --all              include the declarations Lean generates (casesOn, noConfusion, sizeOf_spec, …)
          --timeout <s>      time limit for each translation (default 1800; 0 for none)
          --no-trace         don't use Tenet, even if it is found
          --no-verify        translate only; don't run the checkers
          --uncompressed     flat proofs instead of Metamath's compressed format

        tools (each a flag, else an environment variable, else the PATH):
          --setmm     TENET_ZFC_SETMM      set.mm, or its directory                          (always needed)
          --metamath  TENET_ZFC_METAMATH   metamath-exe                                      (to verify)
          --mmverify  TENET_ZFC_MMVERIFY   mmverify.py                                       (to verify)
          --python    TENET_ZFC_PYTHON     python3, for mmverify.py                          (to verify)
          --java      TENET_ZFC_JAVA       Java 11, for mmj2                                 (to verify)
          --mmj2      TENET_ZFC_MMJ2       a directory with mmj2.jar and macros/             (to verify)
          --leanout   TENET_ZFC_LEANOUT    leanout                                           (for a module or file)
          --lean      TENET_ZFC_LEAN       lean; by default elan's, at leanout's toolchain   (for a module or file)
          --tenet     TENET_ZFC_TENET      Tenet, tenet or tenet.dll                         (optional)

        exit status: 0 every declaration proved (with --no-verify: translated), 1 some refused or failed, 2 a usage, tool or file error
        """;

    private sealed record Decl(string Name, string Kind)
    {
        public string Status { get; set; } = "pending";   // proved, translated, refused, failed
        public string Route { get; set; } = "";
        public string? File { get; set; }
        public string Detail { get; set; } = "";
    }

    public static int Execute(string[] args)
    {
        try
        {
            return Run(args);
        }
        catch (ToolError e)
        {
            Console.Error.WriteLine($"tenet-zfc run: {e.Message}");
            return 2;
        }
    }

    private static int Run(string[] args)
    {
        if (args.Length == 0 || args.Contains("--help") || args.Contains("-h"))
        {
            Console.WriteLine(Usage);
            return args.Length == 0 ? 2 : 0;
        }
        var (values, switches, positional) = Tools.Parse(args, ["--out", "--decl", "--timeout"], ["--all", "--no-trace", "--no-verify", "--uncompressed"]);
        if (positional.Count != 1) throw new ToolError($"give exactly one module, .lean file or export (got {positional.Count})\n\n{Usage}");
        string input = positional[0];
        var tools = new Tools(values);
        string outDir = Path.GetFullPath(values.GetValueOrDefault("--out", "tenet-zfc-out"));
        int timeoutSeconds = values.TryGetValue("--timeout", out string? ts) ? int.TryParse(ts, out int t) && t >= 0 ? t : throw new ToolError("--timeout takes a number of seconds") : 1800;
        TimeSpan? timeout = timeoutSeconds > 0 ? TimeSpan.FromSeconds(timeoutSeconds) : null;
        bool verify = !switches.Contains("--no-verify");
        bool compress = !switches.Contains("--uncompressed");
        var given = values.TryGetValue("--decl", out string? dl) ? dl.Split(',', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries).ToList() : null;

        bool isExport = input.EndsWith(".ndjson", StringComparison.OrdinalIgnoreCase) || input.EndsWith(".ndjson.gz", StringComparison.OrdinalIgnoreCase);
        bool isFile = input.EndsWith(".lean", StringComparison.OrdinalIgnoreCase);
        if (isExport && given is null) throw new ToolError("an export doesn't say which module each declaration comes from: name the declarations with --decl");
        if ((isExport || isFile) && !File.Exists(input)) throw new ToolError($"{input} doesn't exist");

        // Every tool up front, so a missing one is reported before minutes of work, and all missing ones at once.
        var missing = new List<string>();
        string Need(Func<string> find)
        {
            try { return find(); }
            catch (ToolError e) { missing.Add(e.Message); return ""; }
        }
        string setmm = Need(() => tools.RequireSetMm("to translate"));
        string leanout = "", lean = "";
        var leanEnv = new Dictionary<string, string?>();
        if (!isExport)
        {
            leanout = Need(() => Path.GetFullPath(tools.Require(Tools.LeanOut, "to export Lean declarations")));
            lean = Need(() => tools.Require(Tools.Lean, "to compile the file and list the module's declarations"));
        }
        Checkers? checkers = null;
        if (verify)
        {
            string mm = Need(() => tools.Require(Tools.Metamath, "to verify (or pass --no-verify)"));
            string py = Need(() => tools.Require(Tools.Python, "to run mmverify.py (or pass --no-verify)"));
            string mv = Need(() => tools.Require(Tools.MmVerify, "to verify (or pass --no-verify)"));
            string java = Need(() => tools.Require(Tools.Java, "for mmj2's definition check (or pass --no-verify)"));
            string mmj2 = Need(() => tools.RequireMmj2("for the definition check (or pass --no-verify)"));
            checkers = new Checkers(mm, py, mv, java, mmj2);
        }
        if (missing.Count > 0) throw new ToolError(string.Join("\n", missing));

        Directory.CreateDirectory(outDir);
        string logDir = Path.Combine(outDir, "logs");
        Directory.CreateDirectory(logDir);
        // Outputs include set.mm by name, so a link to it (or a copy) sits beside them.
        string localSetMm = Path.Combine(outDir, Path.GetFileName(setmm));
        if (Path.GetFullPath(localSetMm) != setmm)
        {
            var fi = new FileInfo(localSetMm);
            if (fi.LinkTarget is not null) fi.Delete();
            else if (fi.Exists && fi.Length != new FileInfo(setmm).Length) throw new ToolError($"{localSetMm} exists and isn't {setmm}; remove it or choose another --out");
            Links.FileOrCopy(setmm, localSetMm);
        }

        string module = isExport ? Path.GetFileNameWithoutExtension(input) : isFile ? Path.GetFileNameWithoutExtension(input) : input;
        string shownOut = Path.GetRelativePath(System.Environment.CurrentDirectory, outDir) is string rel && !rel.StartsWith("..", StringComparison.Ordinal) && !Path.IsPathRooted(rel) ? rel : outDir;
        Console.WriteLine($"tenet-zfc run: {input} -> {shownOut}");

        // 1. Export.
        string export;
        if (isExport)
        {
            export = Path.GetFullPath(input);
            Console.WriteLine($"  export     given: {export}");
        }
        else
        {
            if (Path.IsPathRooted(lean) || lean.Contains(Path.DirectorySeparatorChar))
            {
                // leanout finds Lean's own library through `lean`: the same one, first on its PATH.
                string bin = Path.GetDirectoryName(Path.GetFullPath(lean))!;
                leanEnv["PATH"] = bin + Path.PathSeparator + System.Environment.GetEnvironmentVariable("PATH");
            }
            if (tools.Source(Tools.Lean) == "the PATH" && System.Environment.GetEnvironmentVariable("ELAN_TOOLCHAIN") is null && LeanOutToolchain(leanout) is string tc)
            {
                // elan's lean, at the toolchain leanout was built with: the one whose .olean files it can read.
                leanEnv["ELAN_TOOLCHAIN"] = tc;
            }
            string leanPath = System.Environment.GetEnvironmentVariable("LEAN_PATH") ?? "";
            if (isFile)
            {
                string build = Path.Combine(outDir, "build");
                Directory.CreateDirectory(build);
                leanPath = build + (leanPath == "" ? "" : Path.PathSeparator + leanPath);
                leanEnv["LEAN_PATH"] = leanPath;
                // Lean wants the file inside its root directory, the working directory: the file's own, so the module is its name.
                string src = Path.GetFullPath(input);
                var c = Proc.Run(lean, ["-o", Path.Combine(build, module + ".olean"), Path.GetFileName(src)], Path.GetDirectoryName(src), leanEnv);
                if (c.ExitCode != 0)
                {
                    string hint = c.Output.Contains("no default toolchain") ? "\n  elan has no toolchain to use: pass --lean <toolchain>/bin/lean, or set ELAN_TOOLCHAIN" : "";
                    throw new ToolError($"lean couldn't compile {input}:\n{c.Tail()}{hint}");
                }
                Console.WriteLine($"  compile    lean: {input} -> build/{module}.olean ({c.Elapsed.TotalSeconds:F1}s)");
            }
            export = Path.Combine(outDir, "export.ndjson");
            var e = Proc.Run(leanout, [module, "--module", module, "-o", export], outDir, leanEnv);
            if (e.ExitCode != 0)
            {
                throw new ToolError($"leanout couldn't export {module}:\n{e.Tail()}\n  leanout must run under the toolchain that built the .olean files, with LEAN_PATH reaching them (in a Lake project, `lake env tenet-zfc run …`).");
            }
            Console.WriteLine($"  export     leanout: {module} -> export.ndjson ({e.Elapsed.TotalSeconds:F1}s)");
        }

        // The declarations: given, or the ones the module declares itself.
        List<string> names;
        if (given is not null)
        {
            names = given;
        }
        else
        {
            string script = Path.Combine(outDir, "ModuleDecls.lean");
            using (Stream s = typeof(RunCommand).Assembly.GetManifestResourceStream("ModuleDecls.lean")!)
            using (FileStream f = File.Create(script))
            {
                s.CopyTo(f);
            }
            var argv = new List<string> { "--run", script, module };
            if (switches.Contains("--all")) argv.Add("--all");
            var d = Proc.Run(lean, argv, outDir, leanEnv);
            if (d.ExitCode != 0) throw new ToolError($"couldn't list the declarations of {module}:\n{d.Tail()}");
            names = d.Stdout.Replace("\r", "").Split('\n', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries).ToList();
        }
        var terms = new Terms();
        TenetZfc.Environment env;
        try
        {
            env = Reader.ReadExport(terms, export);
        }
        catch (Exception ex) when (ex is IOException or TenetZfc.FormatException or JsonException)
        {
            throw new ToolError($"couldn't read the export {export}: {ex.Message}");
        }
        var decls = new List<Decl>();
        foreach (string n in names)
        {
            ConstInfo? c = env.Find(terms.Of(n));
            if (c is null) throw new ToolError($"{n} isn't in the export {export}");
            decls.Add(new Decl(n, c.Kind.ToString().ToLowerInvariant()));
        }
        if (decls.Count == 0) throw new ToolError($"{module} declares nothing to translate (pass --all to include generated declarations)");
        Console.WriteLine($"  select     {Count(decls.Count, "declaration")}: {Count(decls.Count(d => d.Kind == "theorem"), "theorem")}, {Count(decls.Count(d => d.Kind != "theorem"), "other")}");

        var theorems = decls.Where(d => d.Kind == "theorem").ToList();
        var others = decls.Where(d => d.Kind != "theorem").ToList();
        var files = new List<(string File, List<Decl> Decls)>();

        // 2. Trace: Tenet re-checks the theorems and records its derivations, which this tool replays without Tenet and
        // which the milestone 2 translator turns into set.mm proofs in set.mm's own vocabulary, when it covers them.
        if (theorems.Count > 0 && !switches.Contains("--no-trace"))
        {
            string? tenet = tools.Find(Tools.Tenet);
            if (tenet is null)
            {
                Console.WriteLine($"  trace      skipped: Tenet not found ({Tools.Tenet.Flag} or {Tools.Tenet.Env}); theorems go through the model only, which is slower");
            }
            else
            {
                string trace = Path.Combine(outDir, "trace.ndjson");
                var r = Proc.Run(tenet, ["check", export, "--only", string.Join(",", theorems.Select(d => d.Name)), "--trace", trace], outDir, timeout: timeout);
                File.WriteAllText(Path.Combine(logDir, "tenet.log"), r.Output);
                if (r.ExitCode != 0 || !File.Exists(trace))
                {
                    Console.WriteLine($"  trace      Tenet didn't accept every theorem, or couldn't trace (exit {r.ExitCode}; logs/tenet.log); theorems go through the model\n{r.Tail(4)}");
                }
                else
                {
                    Console.WriteLine($"  trace      tenet: {Count(theorems.Count, "theorem")} re-checked -> trace.ndjson ({r.Elapsed.TotalSeconds:F1}s)");
                    string traceOut = Path.Combine(outDir, "trace-theorems.mm");
                    var covered = TraceTheorems(terms, env, trace, localSetMm, traceOut, theorems, compress);
                    if (covered.Count > 0) files.Add((traceOut, covered));
                }
            }
        }

        // 3. Translate: theorems the trace didn't cover go through the model, each in its own process with a time limit.
        foreach (Decl d in theorems.Where(d => d.Status == "pending"))
        {
            string file = Path.Combine(outDir, $"theorem-{FileName(d.Name)}.mm");
            Console.WriteLine($"  translate  theorem {d.Name} through the model{(timeout is null ? "" : $" (time limit {timeoutSeconds}s)")} …");
            var argv = new List<string> { "theorem", export, localSetMm, file, d.Name };
            if (!compress) argv.Add("--uncompressed");
            var (elapsed, _) = Translate(argv, [d], timeout, logDir, $"theorem-{FileName(d.Name)}");
            if (d.Status == "translated")
            {
                d.Route = "model";
                d.File = file;
                files.Add((file, [d]));
            }
            else if (File.Exists(file)) File.Delete(file);
            Console.WriteLine($"             {d.Status}{(d.Detail == "" ? "" : $": {d.Detail}")} ({elapsed.TotalSeconds:F1}s)");
        }
        if (others.Count > 0)
        {
            string file = Path.Combine(outDir, "definitions.mm");
            var pending = others.ToList();
            // A crash or a time-out loses the whole batch: set aside the declaration it happened on, and run the rest again.
            while (pending.Count > 0)
            {
                foreach (Decl d in pending) { d.Status = "pending"; d.Detail = ""; }
                var argv = new List<string> { "define", export, localSetMm, file };
                argv.AddRange(pending.Select(d => d.Name));
                if (!compress) argv.Add("--uncompressed");
                if (!Translate(argv, pending, timeout, logDir, "definitions").Crashed) break;
                pending = pending.Where(d => d.Detail == SetAside).ToList();
            }
            var translated = others.Where(d => d.Status == "translated").ToList();
            foreach (Decl d in translated) { d.Route = "model"; d.File = file; }
            if (translated.Count > 0) files.Add((file, translated));
            else if (File.Exists(file)) File.Delete(file);
            Console.WriteLine($"  translate  define: {translated.Count} of {others.Count} -> definitions.mm");
        }

        // 4. Verify every output with all three checkers.
        foreach (var (file, inFile) in files)
        {
            if (checkers is null) break;
            var outcomes = checkers.Check(file, logDir);
            Console.WriteLine($"  verify     {Path.GetFileName(file)}: " + string.Join(", ", outcomes.Select(o => $"{o.Checker} {(o.Ok ? "ok" : "FAILED")} ({o.Elapsed.TotalSeconds:F0}s)")));
            var bad = outcomes.Where(o => !o.Ok).ToList();
            foreach (Decl d in inFile)
            {
                if (bad.Count == 0) d.Status = "proved";
                else { d.Status = "failed"; d.Detail = string.Join("; ", bad.Select(o => $"{o.Checker}: {o.Message.Split('\n')[0]}")); }
            }
            foreach (var o in bad) Console.WriteLine($"             {o.Checker}: {o.Message}");
        }

        // 5. Report.
        Console.WriteLine();
        int w = Math.Clamp(decls.Max(d => d.Name.Length), "declaration".Length, 48);
        Console.WriteLine($"  {"declaration".PadRight(w)}  {"kind",-11}  {"result",-10}  output / reason");
        foreach (Decl d in decls)
        {
            string where = d.Status is "proved" or "translated" ? $"{Path.GetFileName(d.File)} ({(d.Route == "trace" ? "from its trace" : "through the model")})" : d.Detail;
            if (d.Status is "proved" or "translated" && d.Detail != "") where += $"  {d.Detail}";
            Console.WriteLine($"  {d.Name.PadRight(w)}  {d.Kind,-11}  {d.Status,-10}  {where}");
        }
        int proved = decls.Count(d => d.Status == "proved"), refused = decls.Count(d => d.Status == "refused"), failed = decls.Count(d => d.Status == "failed");
        int unverified = decls.Count(d => d.Status == "translated");
        Console.WriteLine();
        Console.WriteLine($"  {proved} proved, {refused} refused, {failed} failed" + (unverified > 0 ? $", {unverified} translated but not verified (--no-verify)" : "")
            + $". Outputs, logs and report.json are in {shownOut}.");
        if (proved > 0)
        {
            Console.WriteLine($"  proved: translated, and its output passed metamath-exe, mmverify.py and mmj2's definitionCheck against {setmm}.");
        }
        var report = new
        {
            tool = "tenet-zfc",
            version = BuildInfo.Version,
            input,
            module,
            setmm,
            verified = verify,
            declarations = decls.Select(d => new { name = d.Name, kind = d.Kind, status = d.Status, route = d.Route, file = d.File is null ? null : Path.GetFileName(d.File), detail = d.Detail }),
            summary = new { proved, refused, failed, translated = unverified },
        };
        File.WriteAllText(Path.Combine(outDir, "report.json"), JsonSerializer.Serialize(report, new JsonSerializerOptions { WriteIndented = true }) + "\n");
        // With --no-verify nothing can be proved: success is then every declaration translated.
        return proved + unverified == decls.Count ? 0 : 1;
    }

    /// <summary>
    /// Runs a `define` or `theorem` subprocess on <paramref name="batch"/> and reads each declaration's result from its
    /// output line: `name: |- …` translated, `name: refused: why` refused. A crash or time-out is pinned on the first
    /// declaration without a result, which is set aside; the caller runs the rest again.
    /// </summary>
    private const string SetAside = "(set aside while another declaration crashed)";

    private static (TimeSpan Elapsed, bool Crashed) Translate(List<string> argv, List<Decl> batch, TimeSpan? timeout, string logDir, string log)
    {
        var (self, pre) = Proc.Self();
        var r = Proc.Run(self, pre.Concat(argv), timeout: timeout is null ? null : timeout * Math.Max(1, batch.Count));
        File.WriteAllText(Path.Combine(logDir, $"{log}.log"), r.Output);
        var lines = r.Stdout.Replace("\r", "").Split('\n');
        foreach (Decl d in batch)
        {
            string? line = lines.FirstOrDefault(l => l.StartsWith(d.Name + ": ", StringComparison.Ordinal));
            if (line is null) continue;
            string rest = line[(d.Name.Length + 2)..];
            if (rest.StartsWith("refused: ", StringComparison.Ordinal)) { d.Status = "refused"; d.Detail = rest["refused: ".Length..]; }
            else d.Status = "translated";
        }
        bool crashed = r.TimedOut || r.ExitCode is not (0 or 1);
        if (crashed)
        {
            Decl? culprit = batch.FirstOrDefault(d => d.Status == "pending");
            string first = r.Stderr.Replace("\r", "").Split('\n').FirstOrDefault(l => l.Trim() != "")?.Trim() ?? $"exit status {r.ExitCode}";
            if (culprit is not null)
            {
                if (r.TimedOut) { culprit.Status = "refused"; culprit.Detail = $"translation timed out after {r.Elapsed.TotalSeconds:F0}s (raise --timeout)"; }
                else { culprit.Status = "failed"; culprit.Detail = $"translator error: {first}"; }
            }
            // The output file is written only at the end, so the others' results are lost: mark them to run again.
            foreach (Decl d in batch.Where(d => d != culprit && d.Status != "refused"))
            {
                d.Status = "failed";
                d.Detail = SetAside;
            }
        }
        else
        {
            foreach (Decl d in batch.Where(d => d.Status == "pending"))
            {
                d.Status = "failed";
                d.Detail = $"no result from the translator (exit {r.ExitCode}; see logs/{log}.log)";
            }
        }
        return (r.Elapsed, crashed);
    }

    /// <summary>
    /// Replays Tenet's trace without Tenet, then proves each theorem the milestone 2 translator covers: arithmetic
    /// equations from their traces, and induction on lists from their proof terms. Returns the theorems it proved,
    /// written to <paramref name="output"/>; the rest stay pending, for the model.
    /// </summary>
    private static List<Decl> TraceTheorems(Terms terms, TenetZfc.Environment env, string tracePath, string setmm, string output, List<Decl> theorems, bool compress)
    {
        var done = new List<Decl>();
        List<DeclTrace> traces;
        ReplayReport report;
        try
        {
            traces = Reader.ReadTrace(terms, tracePath);
            report = new Replayer(terms, env).Replay(traces);
        }
        catch (Exception e) when (e is IOException or TenetZfc.FormatException or JsonException)
        {
            Console.WriteLine($"  replay     couldn't read the trace: {e.Message}");
            return done;
        }
        var failed = new HashSet<string>(report.Failures.Select(f => $"{f.Decl}").Concat(report.Unsupported.Select(f => $"{f.Decl}")));
        Console.WriteLine($"  replay     {Count(report.Declarations, "declaration")}, {Count(report.Steps, "step")} re-derived without Tenet, {Count(report.Failures.Count, "failure")}");
        var db = TenetZfc.Metamath.Database.Read(setmm);
        var pr = new TenetZfc.Metamath.Prover(db);
        var emitter = new Emitter(terms, pr, new Bridge(pr, db));
        var listInduction = new ListInduction(terms, env, pr);
        var w = new TenetZfc.Metamath.Writer(Path.GetFileName(setmm), "Lean theorems proved from their Tenet traces by tenet-zfc run (milestone 2's translator).", compress ? db : null);
        foreach (Decl t in theorems)
        {
            DeclTrace? d = traces.FirstOrDefault(x => $"{x.Decl}" == t.Name);
            if (d is null || failed.Contains(t.Name) || env.Find(terms.Of(t.Name)) is not { Kind: ConstKind.Theorem } thm) continue;
            string label = "lean-" + new string(t.Name.Select(c => char.IsAsciiLetterOrDigit(c) || c is '.' or '_' or '-' ? c : '_').ToArray());
            try
            {
                if (emitter.EmitEquation(thm, d).Proof is (List<string> steps, TenetZfc.Metamath.Expr proves))
                {
                    w.Theorem(label, $"The Lean theorem {t.Name}, from its replayed trace.", proves, steps);
                    t.Detail = $"{proves}";
                }
                else if (thm.Value is not null && listInduction.Prove(thm).Item1 is (List<string> ls, TenetZfc.Metamath.Expr lp))
                {
                    w.Theorem(label, $"The Lean theorem {t.Name}, from its proof term, by induction on lists.", lp, ls, ListInduction.Distinct);
                    t.Detail = $"{lp}";
                }
                else continue;
            }
            catch (Exception)
            {
                continue;   // outside what the milestone 2 translator covers: the model will try
            }
            t.Status = "translated";
            t.Route = "trace";
            t.File = output;
            done.Add(t);
        }
        if (done.Count > 0) File.WriteAllText(output, w.ToString());
        Console.WriteLine($"  translate  from traces: {done.Count} of {Count(theorems.Count, "theorem")} -> {(done.Count > 0 ? Path.GetFileName(output) : "none")}");
        return done;
    }

    /// <summary>The toolchain leanout was built with, from the lean-toolchain file of its Lake project, if it has one.</summary>
    private static string? LeanOutToolchain(string leanout)
    {
        // leanout is usually <project>/.lake/build/bin/leanout.
        var dir = new FileInfo(leanout).Directory;
        for (int i = 0; i < 4 && dir is not null; i++, dir = dir.Parent)
        {
            string f = Path.Combine(dir.FullName, "lean-toolchain");
            if (File.Exists(f)) return File.ReadAllText(f).Trim();
        }
        return null;
    }

    private static string Count(int n, string noun) => $"{n} {noun}{(n == 1 ? "" : "s")}";

    private static string FileName(string name) => new(name.Select(c => char.IsAsciiLetterOrDigit(c) || c is '.' or '_' or '-' ? c : '_').ToArray());
}
