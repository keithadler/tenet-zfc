using TenetZfc.Metamath;
using Proof = (System.Collections.Generic.List<string> Proof, TenetZfc.Metamath.Expr Proves);

namespace TenetZfc;

/// <summary>Small helpers for typing propositions in the theorem translator (PropRecursors.cs).</summary>
public sealed partial class Model
{
    /// <summary>The context with one more hypothesis, the memberships weakened to it.</summary>
    private PCtx Extend(PCtx c, string hyp)
    {
        var d = c.Clone();
        d.Ph = $"( {c.Ph} /\\ {hyp} )";
        foreach (var kv in c.Mems)
        {
            d.Mems[kv.Key] = (pr.Apply("adantr", S(("ph", c.Ph), ("ps", _d.Split(kv.Value.P.Proves).X), ("ch", hyp)), kv.Value.P), kv.Value.Ty);
        }
        return d;
    }

    private string KidOf(string type, string text, string v)
    {
        SyntaxTree n = pr.Parse(type, text.Split(' ')) ?? throw new Refused($"does not parse: {text}");
        var vars = n.Rule.Hyps.Where(h => h.Kind == 'f').Select(h => h.Var!).ToList();
        int i = vars.IndexOf(v);
        return i >= 0 ? pr.Render(n.Children[i]) : throw new Refused($"{n.Rule.Label} has no {v}: {text}");
    }

    private string LabelOfText(string type, string text) =>
        (pr.Parse(type, text.Split(' ')) ?? throw new Refused($"does not parse: {text}")).Rule.Label;

    /// <summary>( ph -> c ) from ( ph -> B e. if ( c , 1o , (/) ) ).</summary>
    private Proof CondOfMember(string ph, Proof inIf, string b, string c)
    {
        string d = $"if ( {c} , 1o , (/) )";
        Proof nz = _d.Syl(inIf, pr.Apply("n0i", S(("B", b), ("A", d))));
        return _d.Syl(nz, pr.Apply("con1i", S(("ph", c), ("ps", $"{d} = (/)")), pr.Apply("iffalse", S(("ph", c), ("A", "1o"), ("B", "(/)")))));
    }

    /// <summary>( ph -> (/) e. if ( c , 1o , (/) ) ) from ( ph -> c ).</summary>
    private Proof MemberOfCond(string ph, Proof holds, string c)
    {
        string d = $"if ( {c} , 1o , (/) )";
        Proof isOne = pr.Apply("iftrued", S(("ph", ph), ("ch", c), ("A", "1o"), ("B", "(/)")), holds);
        Proof bi = pr.Apply("eleq2d", S(("ph", ph), ("A", d), ("B", "1o"), ("C", "(/)")), isOne);
        return pr.Apply("mpbird", S(("ph", ph), ("ps", $"(/) e. {d}"), ("ch", "(/) e. 1o")), _d.Lift(ph, pr.Apply("0lt1o", S())), bi);
    }
}
