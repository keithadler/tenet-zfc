using TenetZfc.Metamath;
using MmExpr = TenetZfc.Metamath.Expr;
using Proof = (System.Collections.Generic.List<string> Proof, TenetZfc.Metamath.Expr Proves);

namespace TenetZfc;

/// <summary>
/// Definitional equations as theorems of the model: for Lean terms l ≡ r over free variables a : T1, b : T2, …,
///
///   |- ( ( ( U e. lean.-tower /\ A e. ⟦T1⟧ ) /\ B e. ⟦T2⟧ ) … -> ⟦l⟧ = ⟦r⟧ )
///
/// proved by the theorem translator's conversion steps (beta, delta, iota, projections, congruence). This is how a
/// structurally recursive definition's computation rules (Nat.add's n + 0 = n and n + succ m = succ (n + m)) become
/// theorems in tower mode, where they hold; the bridge theorems (docs/bridges.md) then need no hypotheses.
/// </summary>
public sealed partial class Model
{
    /// <summary>
    /// ( hypotheses -> ⟦l⟧ = ⟦r⟧ ) for (l, r) = sides(the free variables), over binders of the given closed types,
    /// whose texts are A, B, C, …. Tower mode only, on a monomorphized environment.
    /// </summary>
    public (MmExpr Statement, List<string> Proof) ProveDefEq(IReadOnlyList<Expr> binderTypes, Func<IReadOnlyList<Expr>, (Expr L, Expr R)> sides) =>
        ProveDefEq(binderTypes.Select(b => (Func<IReadOnlyList<Expr>, Expr>)(_ => b)).ToList(), sides);

    /// <summary>
    /// As <see cref="ProveDefEq(IReadOnlyList{Expr}, Func{IReadOnlyList{Expr}, ValueTuple{Expr, Expr}})"/>, with each binder's
    /// type computed from the free variables before it (List.length's α : Type, then l : List α).
    /// </summary>
    public (MmExpr Statement, List<string> Proof) ProveDefEq(IReadOnlyList<Func<IReadOnlyList<Expr>, Expr>> binderTypes, Func<IReadOnlyList<Expr>, (Expr L, Expr R)> sides)
    {
        if (!tower)
        {
            throw new Refused("definitional equations are proved in tower mode only");
        }
        _typing.Reduce = LeanWhnf;
        EnsureTowerLemmas();
        var c = new PCtx { Ph = UHyp };
        var hyps = new List<string> { UHyp };
        var pending = new List<(ulong Id, string Hyp)>();
        var fvs = new List<Expr>();
        for (int k = 0; k < binderTypes.Count; k++)
        {
            Expr fv = t.FVar(_fresh++);
            ulong id = ((FVar)fv).Id;
            Expr ty = binderTypes[k](fvs);
            string dom = TrIn(c, ty);
            c.Types[id] = ty;
            c.Vars[id] = ClassVars[k];
            hyps.Add($"{ClassVars[k]} e. {dom}");
            pending.Add((id, $"{ClassVars[k]} e. {dom}"));
            c.Ph = Conj(hyps);
            fvs.Add(fv);
        }
        foreach (var (id, h) in pending)
        {
            c.Mems[id] = (Hyp(c.Ph, h)!.Value, h[(h.IndexOf(" e. ", StringComparison.Ordinal) + 4)..]);
        }
        var (l, r) = sides(fvs);
        Proof p = Conv(c, l, r);
        return (p.Proves, p.Proof);
    }
}

public sealed partial class TheoremTranslator
{
    public Terms Terms => _t;

    /// <summary>The model this translator proves through (tower mode, over the monomorphized environment).</summary>
    public Model Model => _model;

    /// <summary>The instance of a constant with every universe parameter at level 0, as a term.</summary>
    public Expr Const0(string name)
    {
        ConstInfo c = _mono.Env.Find(_t.Of(name)) ?? throw new Model.Refused($"{name} is not in the export");
        return _t.Const(_mono.Instance(c.Name, c.LevelParams.Select(_ => _t.Zero).ToArray()), []);
    }

    /// <summary>The type of a constant's instance with every universe parameter at level 0.</summary>
    public Expr Type0(string name) => _mono.Env.Find(((Const)Const0(name)).Name)!.Type;

    /// <summary>( hypotheses -> ⟦l⟧ = ⟦r⟧ ) for a definitional equation, as <see cref="Model.ProveDefEq"/>.</summary>
    public (MmExpr Statement, List<string> Proof) ProveDefEq(IReadOnlyList<Expr> binderTypes, Func<IReadOnlyList<Expr>, (Expr L, Expr R)> sides) =>
        _model.ProveDefEq(binderTypes, sides);

    /// <summary>As <see cref="Model.ProveDefEq(IReadOnlyList{Func{IReadOnlyList{Expr}, Expr}}, Func{IReadOnlyList{Expr}, ValueTuple{Expr, Expr}})"/>: dependent binder types.</summary>
    public (MmExpr Statement, List<string> Proof) ProveDefEq(IReadOnlyList<Func<IReadOnlyList<Expr>, Expr>> binderTypes, Func<IReadOnlyList<Expr>, (Expr L, Expr R)> sides) =>
        _model.ProveDefEq(binderTypes, sides);
}

public sealed partial class Model
{
    /// <summary>|- a = b for two class texts that differ only in the names of their bound variables (Alpha.cs).</summary>
    public Proof AlphaEq(string a, string b) => AlphaClosed(a, b);
}
