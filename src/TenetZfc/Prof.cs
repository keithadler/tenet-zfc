using System.Diagnostics;

namespace TenetZfc;

/// <summary>
/// Where the time goes, when TENET_PROFILE is set: inclusive time and calls per named section, printed to stderr at
/// exit. Costs nothing measurable when unset.
/// </summary>
public static class Prof
{
    public static readonly bool On = System.Environment.GetEnvironmentVariable("TENET_PROFILE") is not null;
    private static readonly Dictionary<string, (long Ticks, long Calls)> Totals = new();
    private static readonly Dictionary<string, int> Active = new();

    static Prof()
    {
        if (On)
        {
            AppDomain.CurrentDomain.ProcessExit += (_, _) => Report();
        }
    }

    public readonly struct Section : IDisposable
    {
        private readonly string? _name;
        private readonly long _start;

        internal Section(string name)
        {
            _name = name;
            _start = Stopwatch.GetTimestamp();
            Active[name] = Active.GetValueOrDefault(name) + 1;
        }

        public void Dispose()
        {
            if (_name is null)
            {
                return;
            }
            int depth = --Active[_name];
            var (t, c) = Totals.GetValueOrDefault(_name);
            // Only the outermost of nested sections of one name counts its time.
            Totals[_name] = (depth == 0 ? t + Stopwatch.GetTimestamp() - _start : t, c + 1);
        }
    }

    /// <summary>Count something (its total shows as the calls column).</summary>
    public static void Add(string name, long n)
    {
        var (t, c) = Totals.GetValueOrDefault(name);
        Totals[name] = (t, c + n);
    }

    public static Section Time(string name) => On ? new Section(name) : default;

    public static void Report()
    {
        foreach (var kv in Totals.OrderByDescending(kv => kv.Value.Ticks))
        {
            Console.Error.WriteLine($"[profile] {kv.Key,-28} {kv.Value.Ticks / (double)Stopwatch.Frequency,9:F1}s {kv.Value.Calls,12:N0} calls");
        }
    }
}
