using System.Text.RegularExpressions;

namespace TenetZfc.Cli;

/// <summary>
/// The three independent checks every output must pass: metamath-exe (C), mmverify.py (Python), and mmj2's
/// definitionCheck, the check set.mm applies to its own definitions. Each output .mm includes set.mm by file name, so
/// it must sit in the same directory as set.mm (or a link to it).
/// </summary>
public sealed class Checkers(string metamath, string python, string mmverify, string java, string mmj2)
{
    public sealed record Outcome(string Checker, bool Ok, string Message, TimeSpan Elapsed);

    /// <summary>Runs the three checkers on <paramref name="file"/> at once, and writes each one's log beside it.</summary>
    public List<Outcome> Check(string file, string logDir)
    {
        Directory.CreateDirectory(logDir);
        var tasks = new[]
        {
            Task.Run(() => Metamath(file, logDir)),
            Task.Run(() => MmVerify(file, logDir)),
            Task.Run(() => DefinitionCheck(file, logDir)),
        };
        Task.WaitAll(tasks);
        return tasks.Select(t => t.Result).ToList();
    }

    public Outcome Metamath(string file, string logDir)
    {
        string dir = Path.GetDirectoryName(Path.GetFullPath(file))!, name = Path.GetFileName(file);
        var r = Proc.Run(metamath, ["set scroll continuous", $"read {name}", "verify proof *", "exit"], dir);
        File.WriteAllText(Path.Combine(logDir, $"{name}.metamath.log"), r.Output);
        // metamath-exe exits 0 even on errors; a ?Error line is the failure, as in CI.
        var errors = r.Output.Replace("\r", "").Split('\n').Where(l => l.Contains("?Error")).ToList();
        bool ok = r.ExitCode == 0 && errors.Count == 0 && r.Output.Contains("verified", StringComparison.Ordinal);
        string msg = ok ? "every proof verified" : errors.Count > 0 ? $"{errors.Count} ?Error line(s), first: {errors[0].Trim()}" : $"didn't verify (exit {r.ExitCode}):\n{r.Tail()}";
        return new("metamath-exe", ok, msg, r.Elapsed);
    }

    public Outcome MmVerify(string file, string logDir)
    {
        string dir = Path.GetDirectoryName(Path.GetFullPath(file))!, name = Path.GetFileName(file);
        var r = Proc.Run(python, ["-I", Path.GetFullPath(mmverify), name], dir);
        File.WriteAllText(Path.Combine(logDir, $"{name}.mmverify.log"), r.Output);
        return new("mmverify.py", r.ExitCode == 0, r.ExitCode == 0 ? "exit status 0" : $"exit status {r.ExitCode}:\n{r.Tail()}", r.Elapsed);
    }

    /// <summary>
    /// mmj2's definitionCheck, as scripts/check-definitions runs it: every new $a with |- must be a conservative
    /// definition, and the new syntax must keep set.mm's grammar unambiguous. Any error or warning fails it. A file with
    /// no df-lean definitions (theorems in set.mm's own vocabulary) has nothing to check, and passes.
    /// </summary>
    public Outcome DefinitionCheck(string file, string logDir)
    {
        var sw = System.Diagnostics.Stopwatch.StartNew();
        string full = Path.GetFullPath(file), dir = Path.GetDirectoryName(full)!, name = Path.GetFileName(full);
        if (!File.ReadLines(full).Any(l => l.TrimStart().StartsWith("df-lean.", StringComparison.Ordinal)))
        {
            return new("mmj2 definitionCheck", true, "no definitions to check", sw.Elapsed);
        }
        string macros = Path.Combine(dir, "macros");
        if (!Directory.Exists(macros))
        {
            Links.DirectoryOrCopy(Path.Combine(mmj2, "macros"), macros);
        }
        string tag = $"{System.Environment.ProcessId}-{Guid.NewGuid():N}"[..20];
        string paramsFile = Path.Combine(dir, $"tenet-zfc-runparams-{tag}.txt");
        File.WriteAllText(paramsFile, $"LoadFile,{name}\nSetParser,mmj.verify.LRParser\nVerifyProof,*\nParse,*\nRunMacro,definitionCheck,ax-*,df-bi,df-clab,df-cleq,df-clel\n");
        Proc.Result r;
        try
        {
            r = Proc.Run(java, ["-Xms512M", "-Xmx2048M", "-jar", Path.Combine(mmj2, "mmj2.jar"), Path.GetFileName(paramsFile)], dir);
        }
        finally
        {
            File.Delete(paramsFile);
        }
        File.WriteAllText(Path.Combine(logDir, $"{name}.mmj2.log"), r.Output);
        var problems = r.Output.Replace("\r", "").Split('\n')
            .Where(l => Regex.IsMatch(l, @"Exception|.-..-[0-9]{4}") && !Regex.IsMatch(l, "I-UT-0015|I-MA-0001")).ToList();
        if (problems.Count > 0)
        {
            return new("mmj2 definitionCheck", false, $"{problems.Count} problem(s), first: {problems[0].Trim()}", sw.Elapsed);
        }
        if (!r.Output.Contains("RunMacro,definitionCheck", StringComparison.Ordinal))
        {
            return new("mmj2 definitionCheck", false, $"mmj2 didn't run definitionCheck:\n{r.Tail()}", sw.Elapsed);
        }
        return new("mmj2 definitionCheck", true, "every definition passes", sw.Elapsed);
    }
}

/// <summary>Links, falling back to copies where links aren't allowed (Windows without developer mode).</summary>
public static class Links
{
    public static void FileOrCopy(string target, string link)
    {
        if (File.Exists(link) || Directory.Exists(link)) return;
        try
        {
            File.CreateSymbolicLink(link, target);
        }
        catch (Exception e) when (e is IOException or UnauthorizedAccessException or PlatformNotSupportedException)
        {
            File.Copy(target, link);
        }
    }

    public static void DirectoryOrCopy(string target, string link)
    {
        try
        {
            Directory.CreateSymbolicLink(link, target);
        }
        catch (Exception e) when (e is IOException or UnauthorizedAccessException or PlatformNotSupportedException)
        {
            Directory.CreateDirectory(link);
            foreach (string f in Directory.GetFiles(target)) File.Copy(f, Path.Combine(link, Path.GetFileName(f)), overwrite: true);
        }
    }
}

/// <summary>`tenet-zfc verify`: the three checkers on existing outputs, with the same tool flags as `run`.</summary>
public static class VerifyCommand
{
    public const string Usage = """
        usage: tenet-zfc verify <out.mm>... [--setmm <set.mm>] [--metamath …] [--mmverify …] [--python …] [--java …] [--mmj2 …]

          Checks each file with metamath-exe, mmverify.py and mmj2's definitionCheck. A file includes set.mm by name;
          when set.mm isn't beside it, --setmm (or TENET_ZFC_SETMM) says where it is, and a link to it is made there.
          Logs go to a logs/ directory beside each file. Exit status: 0 all pass, 1 some check failed, 2 a tool error.
        """;

    public static int Execute(string[] args)
    {
        try
        {
            if (args.Contains("--help") || args.Contains("-h")) { Console.WriteLine(Usage); return 0; }
            var (values, _, files) = Tools.Parse(args, [], []);
            if (files.Count == 0) { Console.Error.WriteLine(Usage); return 2; }
            var tools = new Tools(values);
            var checkers = new Checkers(tools.Require(Tools.Metamath, "to verify"), tools.Require(Tools.Python, "to run mmverify.py"),
                tools.Require(Tools.MmVerify, "to verify"), tools.Require(Tools.Java, "for mmj2's definition check"), tools.RequireMmj2("for the definition check"));
            int status = 0;
            foreach (string f in files)
            {
                if (!File.Exists(f)) throw new ToolError($"{f} doesn't exist");
                string dir = Path.GetDirectoryName(Path.GetFullPath(f))!;
                string? include = File.ReadLines(f).Select(l => System.Text.RegularExpressions.Regex.Match(l, @"^\s*\$\[\s*(\S+)\s*\$\]")).FirstOrDefault(m => m.Success)?.Groups[1].Value;
                if (include is not null && !File.Exists(Path.Combine(dir, include)))
                {
                    string setmm = tools.RequireSetMm($"because {f} includes {include}, which isn't beside it");
                    Links.FileOrCopy(setmm, Path.Combine(dir, include));
                }
                var outcomes = checkers.Check(f, Path.Combine(dir, "logs"));
                foreach (var o in outcomes) Console.WriteLine($"{f}: {o.Checker}: {(o.Ok ? "ok" : "FAILED")}: {o.Message} ({o.Elapsed.TotalSeconds:F0}s)");
                if (outcomes.Any(o => !o.Ok)) status = 1;
            }
            return status;
        }
        catch (ToolError e)
        {
            Console.Error.WriteLine($"tenet-zfc verify: {e.Message}");
            return 2;
        }
    }
}
