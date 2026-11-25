using System.Diagnostics;
using TenetZfc;

const string Usage = """
    tenet-zfc - Lean 4 proofs to ZFC (design stage; see docs/spec.md)

    usage:
      tenet-zfc replay <export.ndjson> <trace.ndjson>   re-derive the steps of a Tenet trace, without Tenet

    make a trace with Tenet (github.com/keithadler/tenet, main):
      tenet check <export.ndjson> --trace <trace.ndjson>

    exit status: 0 no step failed, 1 some step failed, 2 usage or file error
    """;

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
        + (report.BlocksChecked > 0 ? $" {report.BlocksChecked} inductive blocks checked, recursors not derived." : "")
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
