namespace TenetZfc;

// The quotient block. The kernel does not derive Quot, Quot.mk, Quot.lift and Quot.ind; it builds them in, with fixed
// types, once Eq is declared. So there is nothing in a trace to replay: the check is that the export's four constants
// have exactly the built-in types, and that the Eq they mention is the standard one.

public sealed partial class Replayer
{
    /// <summary>Null when the export's quotient constants and Eq are the kernel's; otherwise the first difference.</summary>
    public string? CheckQuotients()
    {
        Expr prop = _t.Sort(_t.Zero);
        Expr B(int i) => _t.BVar(i);
        Expr Pi(Expr d, Expr b) => _t.Binding(true, Name.Anonymous, BinderKind.Default, d, b);
        Expr Ap(Expr f, params Expr[] xs) => _t.MkApp(f, xs);

        // Eq.{w} : {α : Sort w} → α → α → Prop, with Eq.refl.{w} : {α : Sort w} → (a : α) → Eq a a.
        if (_env.Find(_t.Of("Eq")) is not { Kind: ConstKind.Inductive, LevelParams: [Name w], NumParams: 2, NumIndices: 1, Ctors: [Name refl] } eq
            || !ReferenceEquals(refl, _t.Of("Eq.refl")))
        {
            return "Eq is not the standard inductive type";
        }
        Level lw = _t.Param(w);
        if (!ReferenceEquals(eq.Type, Pi(_t.Sort(lw), Pi(B(0), Pi(B(1), prop)))))
        {
            return "Eq does not have the standard type";
        }
        if (_env.Find(refl) is not { LevelParams: [Name w2] } reflInfo
            || !ReferenceEquals(reflInfo.Type, Pi(_t.Sort(_t.Param(w2)), Pi(B(0), Ap(_t.Const(_t.Of("Eq"), [_t.Param(w2)]), B(1), B(0), B(0))))))
        {
            return "Eq.refl does not have the standard type";
        }

        ConstInfo? Get(string n, int levels) =>
            _env.Find(_t.Of(n)) is { Kind: ConstKind.Quot } c && c.LevelParams.Length == levels ? c : null;
        if (Get("Quot", 1) is not ConstInfo quot || Get("Quot.mk", 1) is not ConstInfo mk
            || Get("Quot.lift", 2) is not ConstInfo lift || Get("Quot.ind", 1) is not ConstInfo ind)
        {
            return "the export does not declare the four quotient constants with their universe parameters";
        }

        // r : α → α → Prop, written where α is bound variable 0.
        Expr rel = Pi(B(0), Pi(B(1), prop));

        // Quot.{u} : {α : Sort u} → (α → α → Prop) → Sort u
        Level u = _t.Param(quot.LevelParams[0]);
        if (!ReferenceEquals(quot.Type, Pi(_t.Sort(u), Pi(rel, _t.Sort(u)))))
        {
            return "Quot does not have the built-in type";
        }

        // Quot.mk.{u} : {α : Sort u} → (r : α → α → Prop) → α → Quot r
        u = _t.Param(mk.LevelParams[0]);
        Expr quotU = _t.Const(quot.Name, [u]);
        if (!ReferenceEquals(mk.Type, Pi(_t.Sort(u), Pi(rel, Pi(B(1), Ap(quotU, B(2), B(1)))))))
        {
            return "Quot.mk does not have the built-in type";
        }

        // Quot.lift.{u, v} : {α : Sort u} → {r : α → α → Prop} → {β : Sort v} → (f : α → β)
        //   → (∀ a b : α, r a b → f a = f b) → Quot r → β
        u = _t.Param(lift.LevelParams[0]);
        Level v = _t.Param(lift.LevelParams[1]);
        quotU = _t.Const(quot.Name, [u]);
        Expr sound = Pi(B(3), Pi(B(4), Pi(Ap(B(4), B(1), B(0)),
            Ap(_t.Const(eq.Name, [v]), B(4), _t.App(B(3), B(2)), _t.App(B(3), B(1))))));
        Expr liftType = Pi(_t.Sort(u), Pi(rel, Pi(_t.Sort(v), Pi(Pi(B(2), B(1)), Pi(sound, Pi(Ap(quotU, B(4), B(3)), B(3)))))));
        if (!ReferenceEquals(lift.Type, liftType))
        {
            return "Quot.lift does not have the built-in type";
        }

        // Quot.ind.{u} : {α : Sort u} → {r : α → α → Prop} → {β : Quot r → Prop}
        //   → (∀ a, β (Quot.mk r a)) → ∀ q, β q
        u = _t.Param(ind.LevelParams[0]);
        quotU = _t.Const(quot.Name, [u]);
        Expr mkU = _t.Const(mk.Name, [u]);
        Expr indType = Pi(_t.Sort(u), Pi(rel, Pi(Pi(Ap(quotU, B(1), B(0)), prop),
            Pi(Pi(B(2), _t.App(B(1), Ap(mkU, B(3), B(2), B(0)))), Pi(Ap(quotU, B(3), B(2)), _t.App(B(2), B(0)))))));
        if (!ReferenceEquals(ind.Type, indType))
        {
            return "Quot.ind does not have the built-in type";
        }
        return null;
    }
}
