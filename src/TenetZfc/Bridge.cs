using TenetZfc.Metamath;
using MmExpr = TenetZfc.Metamath.Expr;
using Proof = (System.Collections.Generic.List<string> Proof, TenetZfc.Metamath.Expr Proves);

namespace TenetZfc;

/// <summary>
/// Bridge lemmas generated as set.mm proofs. This first set covers literal arithmetic on Nat, the target of the
/// replay's NatLitOp steps. Nat is set.mm's NN0 (the natural numbers inside the complex numbers, where Word, #
/// and decimal numerals live), Nat.add is +, and a literal is a decimal numeral: a digit, or ; A B for 10 A + B.
/// See docs/interpretation.md.
/// </summary>
public sealed class Bridge(Prover pr, Database db)
{
    /// <summary>⟦n⟧: set.mm's decimal numeral.</summary>
    public static string Numeral(long n) => n < 10 ? n.ToString() : $"; {Numeral(n / 10)} {n % 10}";

    private static Dictionary<string, string> S(params (string Var, string Value)[] xs) => xs.ToDictionary(x => x.Var, x => x.Value);

    private bool Has(string label) => db.Statements.ContainsKey(label);

    /// <summary>|- ⟦n⟧ e. CC for a digit: set.mm's 0cn, ax-1cn, 2cn, … 9cn.</summary>
    private static Proof InCC(long n) => ([n == 1 ? "ax-1cn" : $"{n}cn"], MmExpr.Of($"|- {n} e. CC"));

    /// <summary>|- ( ⟦a⟧ + ⟦b⟧ ) = ⟦a + b⟧ for single-digit a and b, from set.mm's addition table; null beyond it.</summary>
    public Proof? Add(long a, long b)
    {
        if (a is < 0 or > 9 || b is < 0 or > 9)
        {
            return null;   // multi-digit sums need set.mm's decadd toolkit: not built yet
        }
        string A = Numeral(a), B = Numeral(b);
        string table = $"{a}p{b}e{a + b}";
        if (Has(table))
        {
            return ([table], db[table].Expr);
        }
        if (b == 0)
        {
            // ( A + 0 ) = A
            return pr.Apply("ax-mp", S(("ph", $"{A} e. CC"), ("ps", $"( {A} + 0 ) = {A}")),
                InCC(a), pr.Apply("addrid", S(("A", A))));
        }
        if (a == 0)
        {
            return pr.Apply("ax-mp", S(("ph", $"{B} e. CC"), ("ps", $"( 0 + {B} ) = {B}")),
                InCC(b), pr.Apply("addlid", S(("A", B))));
        }
        string swapped = $"{b}p{a}e{a + b}";
        if (!Has(swapped))
        {
            return null;
        }
        // ( A + B ) = ( B + A ) = ⟦a + b⟧
        Proof comm = pr.Apply("addcomi", S(("A", A), ("B", B)), InCC(a), InCC(b));
        return pr.Apply("eqtri", S(("A", $"( {A} + {B} )"), ("B", $"( {B} + {A} )"), ("C", Numeral(a + b))), comm, ([swapped], db[swapped].Expr));
    }
}
