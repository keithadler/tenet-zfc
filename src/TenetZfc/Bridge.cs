using TenetZfc.Metamath;
using MmExpr = TenetZfc.Metamath.Expr;
using Proof = (System.Collections.Generic.List<string> Proof, TenetZfc.Metamath.Expr Proves);

namespace TenetZfc;

/// <summary>
/// Bridge lemmas generated as set.mm proofs. This first set covers literal arithmetic on Nat, the target of the
/// replay's NatLitOp steps: a numeral n is ⟦n⟧ = suc applied n times to (/), and Nat.add is ordinal addition +o,
/// whose set.mm theorems nna0 and nnasuc are exactly Nat.add's defining equations. See docs/interpretation.md.
/// </summary>
public sealed class Bridge(Prover pr)
{
    private readonly Dictionary<long, Proof> _inOmega = new();

    /// <summary>⟦n⟧: suc applied n times to the empty set.</summary>
    public static string Numeral(long n) => string.Concat(Enumerable.Repeat("suc ", (int)n)) + "(/)";

    private static Dictionary<string, string> S(params (string Var, string Value)[] xs) => xs.ToDictionary(x => x.Var, x => x.Value);

    /// <summary>|- ⟦n⟧ e. _om, from peano1 and peano2.</summary>
    public Proof InOmega(long n)
    {
        if (_inOmega.TryGetValue(n, out Proof known))
        {
            return known;
        }
        Proof r = n == 0
            ? (["peano1"], MmExpr.Of("|- (/) e. _om"))
            : pr.Apply("ax-mp", S(("ph", $"{Numeral(n - 1)} e. _om"), ("ps", $"{Numeral(n)} e. _om")),
                InOmega(n - 1), pr.Apply("peano2", S(("A", Numeral(n - 1)))));
        _inOmega[n] = r;
        return r;
    }

    /// <summary>|- ( ⟦a⟧ +o ⟦b⟧ ) = ⟦a + b⟧, by nnasuc b times and then nna0.</summary>
    public Proof Add(long a, long b)
    {
        string A = Numeral(a);
        if (b == 0)
        {
            return pr.Apply("ax-mp", S(("ph", $"{A} e. _om"), ("ps", $"( {A} +o (/) ) = {A}")),
                InOmega(a), pr.Apply("nna0", S(("A", A))));
        }
        string K = Numeral(b - 1), sum = $"( {A} +o {K} )";
        // ( A +o suc K ) = suc ( A +o K )
        Proof both = pr.Apply("pm3.2i", S(("ph", $"{A} e. _om"), ("ps", $"{K} e. _om")), InOmega(a), InOmega(b - 1));
        Proof step = pr.Apply("ax-mp", S(("ph", $"( {A} e. _om /\\ {K} e. _om )"), ("ps", $"( {A} +o suc {K} ) = suc {sum}")),
            both, pr.Apply("nnasuc", S(("A", A), ("B", K))));
        // suc ( A +o K ) = suc ⟦a + b - 1⟧
        Proof rec = Add(a, b - 1);
        Proof sucRec = pr.Apply("ax-mp", S(("ph", $"{sum} = {Numeral(a + b - 1)}"), ("ps", $"suc {sum} = {Numeral(a + b)}")),
            rec, pr.Apply("suceq", S(("A", sum), ("B", Numeral(a + b - 1)))));
        return pr.Apply("eqtri", S(("A", $"( {A} +o {Numeral(b)} )"), ("B", $"suc {sum}"), ("C", Numeral(a + b))), step, sucRec);
    }
}
