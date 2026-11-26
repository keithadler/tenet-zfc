using System.Diagnostics;
using System.Reflection;
using System.Runtime.InteropServices;

namespace TenetZfc.Cli;

/// <summary>A tool or input the user hasn't provided, or one that doesn't work. Reported as a message, exit status 2.</summary>
public sealed class ToolError(string message) : Exception(message);

/// <summary>
/// Where `run` and `verify` find the external tools: a command-line flag first, then an environment variable, then
/// (for programs) the PATH. Each tool has a hint saying where to get it, shown when it is missing.
/// </summary>
public sealed class Tools
{
    public sealed record Spec(string Flag, string Env, string[] PathNames, string What, string Hint);

    public static readonly Spec SetMm = new("--setmm", "TENET_ZFC_SETMM", [], "set.mm (the file, or the directory holding it)",
        "download it from https://github.com/metamath/set.mm (CI pins the commit in .github/workflows/ci.yml)");
    public static readonly Spec Metamath = new("--metamath", "TENET_ZFC_METAMATH", ["metamath"], "metamath-exe",
        "build it from https://github.com/metamath/metamath-exe: cc -O2 -o metamath src/*.c");
    public static readonly Spec MmVerify = new("--mmverify", "TENET_ZFC_MMVERIFY", [], "mmverify.py",
        "clone https://github.com/david-a-wheeler/mmverify.py and give the path to mmverify.py");
    public static readonly Spec Python = new("--python", "TENET_ZFC_PYTHON", ["python3", "python"], "Python 3 (for mmverify.py)",
        "install Python 3 from https://www.python.org");
    public static readonly Spec Java = new("--java", "TENET_ZFC_JAVA", ["java"], "Java 11 (for mmj2)",
        "install a JDK 11 with Nashorn, e.g. Zulu 11; mmj2's definitionCheck macro needs it");
    public static readonly Spec Mmj2 = new("--mmj2", "TENET_ZFC_MMJ2", [], "mmj2 (a directory with mmj2.jar and macros/)",
        "download mmj2jar/mmj2.jar and mmj2jar/macros/{definitionCheck,init}.js from https://github.com/digama0/mmj2");
    public static readonly Spec LeanOut = new("--leanout", "TENET_ZFC_LEANOUT", ["leanout"], "leanout",
        "build it from https://github.com/keithadler/leanout with `lake build`, under the toolchain of your Lean code");
    public static readonly Spec Lean = new("--lean", "TENET_ZFC_LEAN", ["lean"], "lean",
        "install elan (https://github.com/leanprover/elan) or give the toolchain's bin/lean");
    public static readonly Spec Tenet = new("--tenet", "TENET_ZFC_TENET", ["tenet"], "Tenet",
        "install it from https://github.com/keithadler/tenet (main), e.g. `dotnet tool install -g tenet`, or give the path to tenet or tenet.dll");

    public static readonly Spec[] All = [SetMm, Metamath, MmVerify, Python, Java, Mmj2, LeanOut, Lean, Tenet];

    private readonly Dictionary<string, string> flags;

    public Tools(Dictionary<string, string> flags) => this.flags = flags;

    /// <summary>The tool's path from its flag or environment variable, or a program on the PATH; null when none.</summary>
    public string? Find(Spec s)
    {
        if (flags.TryGetValue(s.Flag, out string? f)) return f;
        string? e = System.Environment.GetEnvironmentVariable(s.Env);
        if (!string.IsNullOrEmpty(e)) return e;
        foreach (string name in s.PathNames)
        {
            if (OnPath(name) is string p) return p;
        }
        return null;
    }

    /// <summary>The tool's path, or a ToolError saying how to provide it.</summary>
    public string Require(Spec s, string neededFor)
    {
        string? p = Find(s);
        if (p is null)
        {
            string path = s.PathNames.Length > 0 ? $", or put `{s.PathNames[0]}` on the PATH" : "";
            throw new ToolError($"{s.What} is needed {neededFor}, and wasn't found. Pass {s.Flag} <path> or set {s.Env}{path}.\n  To get it: {s.Hint}.");
        }
        // A bare program name (TENET_ZFC_JAVA=java) is looked up on the PATH.
        if (!File.Exists(p) && !Directory.Exists(p) && p.IndexOfAny(['/', '\\']) < 0 && OnPath(p) is string onPath)
        {
            p = onPath;
        }
        if (!File.Exists(p) && !Directory.Exists(p))
        {
            throw new ToolError($"{s.What}: {p} (from {Source(s)}) doesn't exist.\n  To get it: {s.Hint}.");
        }
        return p;
    }

    /// <summary>Where a tool's path came from, for messages.</summary>
    public string Source(Spec s) => flags.ContainsKey(s.Flag) ? s.Flag : !string.IsNullOrEmpty(System.Environment.GetEnvironmentVariable(s.Env)) ? s.Env : "the PATH";

    /// <summary>set.mm itself: the flag or variable may name the file or the directory holding it.</summary>
    public string RequireSetMm(string neededFor)
    {
        string p = Require(SetMm, neededFor);
        if (Directory.Exists(p)) p = Path.Combine(p, "set.mm");
        if (!File.Exists(p)) throw new ToolError($"set.mm: {p} doesn't exist.\n  To get it: {SetMm.Hint}.");
        return Path.GetFullPath(p);
    }

    /// <summary>mmj2's directory: it must hold mmj2.jar and macros/definitionCheck.js.</summary>
    public string RequireMmj2(string neededFor)
    {
        string p = Path.GetFullPath(Require(Mmj2, neededFor));
        if (!File.Exists(Path.Combine(p, "mmj2.jar")) || !File.Exists(Path.Combine(p, "macros", "definitionCheck.js")))
        {
            throw new ToolError($"mmj2: {p} should hold mmj2.jar and macros/definitionCheck.js (and macros/init.js).\n  To get it: {Mmj2.Hint}.");
        }
        return p;
    }

    public static string? OnPath(string name)
    {
        string[] exts = RuntimeInformation.IsOSPlatform(OSPlatform.Windows) ? [".exe", ".cmd", ".bat", ""] : [""];
        foreach (string dir in (System.Environment.GetEnvironmentVariable("PATH") ?? "").Split(Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries))
        {
            foreach (string ext in exts)
            {
                string p = Path.Combine(dir, name + ext);
                if (File.Exists(p)) return p;
            }
        }
        return null;
    }

    /// <summary>
    /// Splits <paramref name="args"/> into tool flags (each followed by a value), the given value flags, boolean flags,
    /// and positional arguments.
    /// </summary>
    public static (Dictionary<string, string> Values, HashSet<string> Switches, List<string> Positional) Parse(
        string[] args, IEnumerable<string> valueFlags, IEnumerable<string> switches)
    {
        var takesValue = new HashSet<string>(All.Select(s => s.Flag).Concat(valueFlags));
        var isSwitch = new HashSet<string>(switches);
        var values = new Dictionary<string, string>();
        var on = new HashSet<string>();
        var pos = new List<string>();
        for (int i = 0; i < args.Length; i++)
        {
            string a = args[i];
            if (takesValue.Contains(a))
            {
                if (i + 1 >= args.Length) throw new ToolError($"{a} needs a value");
                string v = args[++i];
                // --decl may be given more than once; the values accumulate, comma-separated.
                values[a] = values.TryGetValue(a, out string? old) && a == "--decl" ? $"{old},{v}" : v;
            }
            else if (isSwitch.Contains(a)) on.Add(a);
            else if (a.StartsWith("--", StringComparison.Ordinal)) throw new ToolError($"unknown option {a}");
            else pos.Add(a);
        }
        return (values, on, pos);
    }
}

/// <summary>Runs a program and collects its output, with an optional time limit.</summary>
public static class Proc
{
    public sealed record Result(int ExitCode, string Stdout, string Stderr, bool TimedOut, TimeSpan Elapsed)
    {
        public string Output => Stdout + Stderr;

        /// <summary>The last few lines of the output, for a message.</summary>
        public string Tail(int lines = 12)
        {
            var all = Output.Replace("\r", "").Split('\n', StringSplitOptions.RemoveEmptyEntries);
            return string.Join("\n", all.Skip(Math.Max(0, all.Length - lines)).Select(l => "    " + (l.Length > 300 ? l[..300] + "…" : l)));
        }
    }

    public static Result Run(string program, IEnumerable<string> args, string? workingDirectory = null,
        IDictionary<string, string?>? env = null, TimeSpan? timeout = null)
    {
        var psi = new ProcessStartInfo(program)
        {
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            RedirectStandardInput = true,
            UseShellExecute = false,
            WorkingDirectory = workingDirectory ?? System.Environment.CurrentDirectory,
        };
        // A .dll is a .NET program: run it with the dotnet host (e.g. Tenet built from source).
        if (program.EndsWith(".dll", StringComparison.OrdinalIgnoreCase))
        {
            psi.FileName = DotnetHost();
            psi.ArgumentList.Add(program);
        }
        foreach (string a in args) psi.ArgumentList.Add(a);
        if (env is not null)
        {
            foreach (var kv in env)
            {
                if (kv.Value is null) psi.Environment.Remove(kv.Key);
                else psi.Environment[kv.Key] = kv.Value;
            }
        }
        var sw = Stopwatch.StartNew();
        using var p = new Process { StartInfo = psi };
        var stdout = new System.Text.StringBuilder();
        var stderr = new System.Text.StringBuilder();
        p.OutputDataReceived += (_, e) => { if (e.Data is not null) lock (stdout) stdout.AppendLine(e.Data); };
        p.ErrorDataReceived += (_, e) => { if (e.Data is not null) lock (stderr) stderr.AppendLine(e.Data); };
        try
        {
            p.Start();
        }
        catch (System.ComponentModel.Win32Exception e)
        {
            throw new ToolError($"couldn't start {psi.FileName}: {e.Message}");
        }
        p.StandardInput.Close();
        p.BeginOutputReadLine();
        p.BeginErrorReadLine();
        bool timedOut = false;
        if (timeout is TimeSpan t && t > TimeSpan.Zero)
        {
            if (!p.WaitForExit(t))
            {
                timedOut = true;
                try { p.Kill(entireProcessTree: true); } catch (InvalidOperationException) { }
            }
        }
        p.WaitForExit();
        lock (stdout) lock (stderr)
            return new Result(timedOut ? -1 : p.ExitCode, stdout.ToString(), stderr.ToString(), timedOut, sw.Elapsed);
    }

    /// <summary>The program and leading arguments that run this tenet-zfc again, as a subprocess.</summary>
    public static (string Program, List<string> Args) Self()
    {
        string exe = System.Environment.ProcessPath ?? throw new ToolError("can't find the tenet-zfc executable to run translations in");
        string name = Path.GetFileNameWithoutExtension(exe);
        if (name.Equals("dotnet", StringComparison.OrdinalIgnoreCase))
        {
            // Run as `dotnet tenet-zfc.dll`: run the same assembly again.
            string dll = Path.Combine(AppContext.BaseDirectory, "tenet-zfc.dll");
            if (!File.Exists(dll)) throw new ToolError($"can't find {dll} to run translations in");
            return (exe, [dll]);
        }
        return (exe, []);
    }

    private static string DotnetHost()
    {
        string? root = System.Environment.GetEnvironmentVariable("DOTNET_ROOT");
        string exe = RuntimeInformation.IsOSPlatform(OSPlatform.Windows) ? "dotnet.exe" : "dotnet";
        if (root is not null && File.Exists(Path.Combine(root, exe))) return Path.Combine(root, exe);
        return Tools.OnPath("dotnet") ?? "dotnet";
    }
}

/// <summary>The version this build carries (0.1.0-dev until a release sets it from the tag).</summary>
public static class BuildInfo
{
    public static string Version
    {
        get
        {
            string v = typeof(BuildInfo).Assembly.GetCustomAttribute<AssemblyInformationalVersionAttribute>()?.InformationalVersion ?? "unknown";
            // The SDK appends +<commit>; keep a short one.
            int plus = v.IndexOf('+');
            return plus >= 0 && v.Length > plus + 8 ? v[..(plus + 8)] : v;
        }
    }
}
