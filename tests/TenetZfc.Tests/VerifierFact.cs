using Xunit;

namespace TenetZfc.Tests;

/// <summary>
/// A test that needs the verifiers or set.mm: skipped, and reported as skipped, unless every named environment variable
/// is set (TENET_ZFC_SETMM, TENET_ZFC_METAMATH, TENET_ZFC_MMVERIFY, TENET_ZFC_JAVA, TENET_ZFC_MMJ2). Without this a
/// test that returned early on a missing tool passed, so a run without the tools looked like a full pass.
/// </summary>
public sealed class VerifierFactAttribute : FactAttribute
{
    public VerifierFactAttribute(params string[] variables)
    {
        var missing = variables.Where(v => string.IsNullOrEmpty(System.Environment.GetEnvironmentVariable(v))).ToList();
        if (missing.Count > 0)
        {
            Skip = $"needs {string.Join(", ", missing)} (see CONTRIBUTING.md)";
        }
    }
}
