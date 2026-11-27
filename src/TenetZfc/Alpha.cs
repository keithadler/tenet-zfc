using TenetZfc.Metamath;
using Proof = (System.Collections.Generic.List<string> Proof, TenetZfc.Metamath.Expr Proves);

namespace TenetZfc;

/// <summary>
/// Alpha-equivalence: |- ( T. -> A = B ) (or <-> for formulas) for two texts that differ only in the names of bound
/// variables. The model's translation of a term after a substitution can name its binders differently from the
/// translation of the substituted term; the two are the same class, by renaming (cbvmptv, cbvixpv, cbviunv,
/// cbvralvw, cbvrexvw) and congruence.
/// </summary>
public sealed partial class Model
{
    /// <summary>
    /// The text with the free occurrences of the set variable x replaced by with: like Subst, but an inner binder
    /// that shadows x keeps its own occurrences.
    /// </summary>
    private string SubstFree(string text, string x, string with)
    {
        using var prof = Prof.Time("SubstFree");
        if (!text.Split(' ').Contains(x))
        {
            return text;
        }
        if (!BoundIn(text).Contains(x))
        {
            return Subst(text, x, with);
        }
        SyntaxTree n = pr.Parse("class", text.Split(' ')) ?? pr.Parse("wff", text.Split(' ')) ?? throw new Refused($"does not parse: {text}");
        string Go(SyntaxTree m)
        {
            if (m.Rule.Kind == 'f')
            {
                return m.Rule.Var == x ? with : m.Rule.Var!;
            }
            var vars = m.Rule.Hyps.Where(h => h.Kind == 'f').Select(h => h.Var!).ToList();
            int sv = m.Rule.Hyps.Where(h => h.Kind == 'f').ToList().FindIndex(h => h.Expr.Type == "setvar");
            bool shadows = sv >= 0 && m.Rule.Label is not ("cv" or "wel" or "weq") && pr.Render(m.Children[sv]) == x;
            var kids = m.Children.Select((k, i) => shadows && (i == sv || IsScope(m.Rule.Label, vars[i])) ? pr.Render(k) : Go(k)).ToList();
            return string.Join(' ', m.Rule.Expr.Symbols.Select(sym => vars.IndexOf(sym) is int vi and >= 0 ? kids[vi] : sym));
        }
        return Go(n);
    }

    /// <summary>An alpha-variant of the text whose binders avoid the given variables (renamed to fresh ones).</summary>
    private string RenameApart(string text, ISet<string> avoid, params string[] alsoAvoid)
    {
        using var prof = Prof.Time("RenameApart");
        var used = new HashSet<string>(text.Split(' ').Concat(avoid).Concat(alsoAvoid.SelectMany(a => a.Split(' '))));
        SyntaxTree n = pr.Parse("class", text.Split(' ')) ?? pr.Parse("wff", text.Split(' ')) ?? throw new Refused($"does not parse: {text}");
        string Go(SyntaxTree m)
        {
            if (m.Rule.Kind == 'f')
            {
                return m.Rule.Var!;
            }
            var hs = m.Rule.Hyps.Where(h => h.Kind == 'f').ToList();
            var vars = hs.Select(h => h.Var!).ToList();
            int sv = hs.FindIndex(h => h.Expr.Type == "setvar");
            var kids = m.Children.Select(k => pr.Render(k)).ToList();
            if (sv >= 0 && m.Rule.Label is not ("cv" or "wel" or "weq") && avoid.Contains(kids[sv]))
            {
                string old = kids[sv];
                string y = FirstVar(v => !used.Contains(v));
                used.Add(y);
                for (int i = 0; i < kids.Count; i++)
                {
                    if (i != sv && IsScope(m.Rule.Label, vars[i]))
                    {
                        kids[i] = SubstFree(kids[i], old, y);
                    }
                }
                kids[sv] = y;
                string re = string.Join(' ', m.Rule.Expr.Symbols.Select(sym => vars.IndexOf(sym) is int vi and >= 0 ? kids[vi] : sym));
                m = (pr.Parse(m.Rule.Expr.Type, re.Split(' ')) ?? throw new Refused($"does not parse: {re}"));
            }
            var done = m.Children.Select((k, i) => k.Rule.Kind == 'f' ? pr.Render(k) : Go(k)).ToList();
            return string.Join(' ', m.Rule.Expr.Symbols.Select(sym => vars.IndexOf(sym) is int vi and >= 0 ? done[vi] : sym));
        }
        return Go(n);
    }

    private Deduction Hook(Deduction d)
    {
        d.RenameApart = (h, avoid, also) =>
        {
            string h2 = RenameApart(h, avoid, also);
            if (h2 == h)
            {
                return null;
            }
            Proof bi = pr.Apply("mptru", S(("ph", $"( {h} <-> {h2} )")), Alpha("wff", h, h2) ?? throw new Refused($"not alpha-equivalent: {h}  vs  {h2}"));
            return (h2, pr.Apply("biimpi", S(("ph", h), ("ps", h2)), bi), pr.Apply("biimpri", S(("ph", h), ("ps", h2)), bi));
        };
        return d;
    }

    /// <summary>The variables of a substitution's argument a body's binders must avoid: all of the argument's.</summary>
    private HashSet<string> ArgVars(string arg) => arg.Split(' ').Where(v => SetVars.Contains(v)).ToHashSet();

    /// <summary>
    /// |- ( x = v -> B = B[v] ) (or <-> for a formula), the substitution hypothesis of fvmptd3, cbvmptv and the like;
    /// h is "x = v" (given as that text, or as v alone).
    /// </summary>
    private Proof SubstEq(string type, string body, string x, string h)
    {
        using var prof = Prof.Time("SubstEq");
        string v = h.StartsWith($"{x} = ", StringComparison.Ordinal) ? h[(x.Length + 3)..] : h;
        string hyp = $"{x} = {v}";
        string ctx = SubstFree(body, x, "Z");
        if (!ctx.Split(' ').Contains("Z"))
        {
            return type == "class"
                ? pr.Apply("a1i", S(("ph", $"{body} = {body}"), ("ps", hyp)), pr.Apply("eqid", S(("A", body))))
                : pr.Apply("a1i", S(("ph", $"( {body} <-> {body} )"), ("ps", hyp)), pr.Apply("biid", S(("ph", body))));
        }
        return _d.Congruence(type, ctx, "Z", pr.Apply("id", S(("ph", hyp))));
    }

    /// <summary>|- a = b for alpha-equivalent class texts.</summary>
    private Proof AlphaClosed(string a, string b) =>
        a == b ? pr.Apply("eqid", S(("A", a))) : pr.Apply("mptru", S(("ph", $"{a} = {b}")), Alpha("class", a, b)!.Value);

    /// <summary>( ph -> x = y ) for alpha-equivalent class texts.</summary>
    private Proof AlphaIn(string ph, string x, string y)
    {
        using var prof = Prof.Time("AlphaIn");
        if (x == y)
        {
            return _d.Refl(ph, x);
        }
        Proof t = Alpha("class", x, y) ?? throw new Refused($"not alpha-equivalent: {x}  vs  {y}");
        return _d.Lift(ph, pr.Apply("mptru", S(("ph", $"{x} = {y}")), t));
    }

    /// <summary>( T. -> a = b ) or ( T. -> ( a <-> b ) ), or null when the texts are equal.</summary>
    private Proof? Alpha(string type, string a, string b)
    {
        using var prof = Prof.Time("Alpha");
        if (a == b)
        {
            return null;
        }
        SyntaxTree na = pr.Parse(type, a.Split(' ')) ?? throw new Refused($"does not parse: {a}");
        SyntaxTree nb = pr.Parse(type, b.Split(' ')) ?? throw new Refused($"does not parse: {b}");
        if (na.Rule.Label != nb.Rule.Label)
        {
            throw new Refused($"not alpha-equivalent: {a}  vs  {b}");
        }
        var vars = na.Rule.Hyps.Where(h => h.Kind == 'f').ToList();
        string KidA(int i) => pr.Render(na.Children[i]);
        string KidB(int i) => pr.Render(nb.Children[i]);
        int Idx(string v) => vars.FindIndex(h => h.Var == v);

        // A binder named differently: rename a's to b's first.
        int sv = vars.FindIndex(h => h.Expr.Type == "setvar");
        if (sv >= 0 && KidA(sv) != KidB(sv))
        {
            string xa = KidA(sv), xb = KidB(sv);
            if (a.Split(' ').Contains(xb))
            {
                // b's name occurs in a: only as an inner binder, or a and b aren't alpha-equivalent. Rename those
                // inner binders apart first, then a's binder.
                var bound = BoundIn(a);
                bound.Remove(xa);
                if (!bound.Contains(xb))
                {
                    throw new Refused($"not alpha-equivalent ({xb} is free in one): {a}  vs  {b}");
                }
                string mid = RenameApart(a, new HashSet<string> { xb }, b);
                if (mid == a)
                {
                    throw new Refused($"can't rename {xb} apart in {a}");
                }
                Proof p1 = Alpha(type, a, mid) ?? throw new Refused("renaming apart changed nothing");
                Proof? p2 = Alpha(type, mid, b);
                return p2 is Proof q ? TransT(type, p1, q) : p1;
            }
            int di = na.Rule.Label is "wral" or "wrex" or "crab" ? 2 : na.Rule.Label is "cmpt" or "cixp" or "ciun" ? 1 : -1;
            if (di >= 0 && KidA(di).Split(' ').Any(tok => tok == xa || tok == xb))
            {
                // The renaming lemma needs both names out of the domain, where they can occur only bound: rename the
                // domain's own binders apart first (the binder's domain is outside its scope).
                string dom2 = RenameApart(KidA(di), new HashSet<string> { xa, xb }, a, b);
                var kids = na.Children.Select(k => pr.Render(k)).ToList();
                kids[di] = dom2;
                var hv = vars.Select(h => h.Var!).ToList();
                string mid = string.Join(' ', na.Rule.Expr.Symbols.Select(sym => hv.IndexOf(sym) is int vi and >= 0 ? kids[vi] : sym));
                Proof p1 = Alpha(type, a, mid) ?? throw new Refused("renaming a domain apart changed nothing");
                Proof? p2 = Alpha(type, mid, b);
                return p2 is Proof q ? TransT(type, p1, q) : p1;
            }
            Proof r = RenameProof(type, na, sv, xb);
            Proof? rest = Alpha(type, RenameBinder(na, sv, xb), b);
            return rest is Proof q2 ? TransT(type, r, q2) : r;
        }
        switch (na.Rule.Label)
        {
            case "cmpt":
            case "cixp":
            case "ciun":
                {
                    string x = KidA(0);
                    Proof pa = Alpha("class", KidA(1), KidB(1)) ?? _d.Refl("T.", KidA(1));
                    Proof pb = Alpha("class", KidA(2), KidB(2)) ?? _d.Refl("T.", KidA(2));
                    return na.Rule.Label switch
                    {
                        "cmpt" => pr.Apply("mpteq12dv", S(("ph", "T."), ("x", x), ("A", KidA(1)), ("B", KidA(2)), ("C", KidB(1)), ("D", KidB(2))), pa, pb),
                        "cixp" => pr.Apply("ixpeq12dv", S(("ph", "T."), ("x", x), ("A", KidA(1)), ("B", KidB(1)), ("C", KidA(2)), ("D", KidB(2))), pa, pb),
                        _ => pr.Apply("iuneq12d", S(("ph", "T."), ("x", x), ("A", KidA(1)), ("B", KidB(1)), ("C", KidA(2)), ("D", KidB(2))), pa, pb),
                    };
                }
            case "wral":
            case "wrex":
                {
                    // children: ph, x, A
                    string x = KidA(1);
                    Proof pa = Alpha("class", KidA(2), KidB(2)) ?? _d.Refl("T.", KidA(2));
                    Proof pp = Alpha("wff", KidA(0), KidB(0)) ?? _d.BiRefl("T.", KidA(0));
                    return pr.Apply(na.Rule.Label == "wral" ? "raleqbidv" : "rexeqbidv",
                        S(("ph", "T."), ("x", x), ("A", KidA(2)), ("B", KidB(2)), ("ps", KidA(0)), ("ch", KidB(0))), pa, pp);
                }
            case "wal":
            case "wex":
                {
                    // children: ph, x
                    Proof pp = Alpha("wff", KidA(0), KidB(0)) ?? _d.BiRefl("T.", KidA(0));
                    return pr.Apply(na.Rule.Label == "wal" ? "albidv" : "exbidv", S(("ph", "T."), ("x", KidA(1)), ("ps", KidA(0)), ("ch", KidB(0))), pp);
                }
            case "cif":
                {
                    Proof pc = Alpha("wff", KidA(0), KidB(0)) ?? _d.BiRefl("T.", KidA(0));
                    Proof p1 = Alpha("class", KidA(1), KidB(1)) ?? _d.Refl("T.", KidA(1));
                    Proof p2 = Alpha("class", KidA(2), KidB(2)) ?? _d.Refl("T.", KidA(2));
                    return pr.Apply("ifbieq12d", S(("ph", "T."), ("ps", KidA(0)), ("ch", KidB(0)), ("A", KidA(1)), ("B", KidA(2)), ("C", KidB(1)), ("D", KidB(2))), pc, p1, p2);
                }
            case "wceq":
            case "wcel":
                {
                    Proof p1 = Alpha("class", KidA(0), KidB(0)) ?? _d.Refl("T.", KidA(0));
                    Proof p2 = Alpha("class", KidA(1), KidB(1)) ?? _d.Refl("T.", KidA(1));
                    return pr.Apply(na.Rule.Label == "wceq" ? "eqeq12d" : "eleq12d",
                        S(("ph", "T."), ("A", KidA(0)), ("B", KidB(0)), ("C", KidA(1)), ("D", KidB(1))), p1, p2);
                }
            case "wa":
            case "wi":
            case "wo":
                {
                    Proof p1 = Alpha("wff", KidA(0), KidB(0)) ?? _d.BiRefl("T.", KidA(0));
                    Proof p2 = Alpha("wff", KidA(1), KidB(1)) ?? _d.BiRefl("T.", KidA(1));
                    string lab = na.Rule.Label switch { "wa" => "anbi12d", "wi" => "imbi12d", _ => "orbi12d" };
                    return pr.Apply(lab, S(("ph", "T."), ("ps", KidA(0)), ("ch", KidB(0)), ("th", KidA(1)), ("ta", KidB(1))), p1, p2);
                }
            case "wn":
                return pr.Apply("notbid", S(("ph", "T."), ("ps", KidA(0)), ("ch", KidB(0))), Alpha("wff", KidA(0), KidB(0))!.Value);
        }
        if (vars.Any(h => h.Expr.Type != "class"))
        {
            throw new Refused($"no alpha rule for {na.Rule.Label} ({a})");
        }
        // A node of class children (a class, or a formula such as A C_ B or A R B): one child at a time, by the
        // congruence prover.
        var cur = na.Children.Select(k => pr.Render(k)).ToList();
        Proof? acc = null;
        for (int i = 0; i < vars.Count; i++)
        {
            if (Alpha("class", KidA(i), KidB(i)) is not Proof pi)
            {
                continue;
            }
            var holed = cur.ToList();
            holed[i] = "ZZH";
            string ctx = string.Join(' ', na.Rule.Expr.Symbols.Select(sym => Idx(sym) is int vi and >= 0 ? holed[vi] : sym));
            Proof step = _d.Congruence(type, ctx.Replace("ZZH", "Z", StringComparison.Ordinal), "Z", pi);
            acc = acc is Proof a1 ? TransT(type, a1, step) : step;
            cur[i] = KidB(i);
        }
        return acc;
    }

    private Proof TransT(string type, Proof p, Proof q) => type == "class"
        ? _d.Trans(p, q)
        : pr.Apply("bitrd", S(("ph", "T."), ("ps", _d.Sides(_d.Split(p.Proves).X).L), ("ch", _d.Sides(_d.Split(p.Proves).X).R), ("th", _d.Sides(_d.Split(q.Proves).X).R)), p, q);

    /// <summary>The node with its binder (child sv) renamed to y, throughout its scope.</summary>
    private string RenameBinder(SyntaxTree n, int sv, string y)
    {
        string x = pr.Render(n.Children[sv]);
        var vars = n.Rule.Hyps.Where(h => h.Kind == 'f').ToList();
        var kids = n.Children.Select(k => pr.Render(k)).ToList();
        kids[sv] = y;
        for (int i = 0; i < kids.Count; i++)
        {
            // The binder's scope: its body (the class or formula after it); the domain is outside.
            if (i != sv && IsScope(n.Rule.Label, vars[i].Var!))
            {
                kids[i] = SubstFree(kids[i], x, y);
            }
        }
        return string.Join(' ', n.Rule.Expr.Symbols.Select(sym => vars.FindIndex(h => h.Var == sym) is int vi and >= 0 ? kids[vi] : sym));
    }

    private static bool IsScope(string label, string var) => (label, var) switch
    {
        ("cmpt" or "cixp" or "ciun", "B") => true,
        ("wral" or "wrex", "ph") => true,
        ("cab" or "crab", "ph") => true,
        ("wal" or "wex", "ph") => true,
        _ => false,
    };

    /// <summary>( T. -> n = n' ) (or <->), n' the node with its binder renamed to y: cbvmptv, cbvixpv, cbviunv, cbvralvw, cbvrexvw, cbvabv, cbvrabv.</summary>
    private Proof RenameProof(string type, SyntaxTree n, int sv, string y)
    {
        string x = pr.Render(n.Children[sv]);
        string label = n.Rule.Label;
        Proof closed;
        if (label is "cmpt" or "cixp" or "ciun")
        {
            string dom = pr.Render(n.Children[1]), body = pr.Render(n.Children[2]);
            Proof sub = body.Split(' ').Contains(x)
                ? SubstEq("class", body, x, $"{x} = {y}")
                : pr.Apply("a1i", S(("ph", $"{body} = {body}"), ("ps", $"{x} = {y}")), pr.Apply("eqid", S(("A", body))));
            string lemma = label switch { "cmpt" => "cbvmptv", "cixp" => "cbvixpv", _ => "cbviunv" };
            closed = pr.Apply(lemma, S(("x", x), ("y", y), ("A", dom), ("B", body), ("C", SubstFree(body, x, y))), sub);
        }
        else if (label is "wral" or "wrex")
        {
            string body = pr.Render(n.Children[0]), dom = pr.Render(n.Children[2]);
            Proof sub = body.Split(' ').Contains(x)
                ? SubstEq("wff", body, x, $"{x} = {y}")
                : pr.Apply("a1i", S(("ph", $"( {body} <-> {body} )"), ("ps", $"{x} = {y}")), pr.Apply("biid", S(("ph", body))));
            closed = pr.Apply(label == "wral" ? "cbvralvw" : "cbvrexvw", S(("x", x), ("y", y), ("A", dom), ("ph", body), ("ps", SubstFree(body, x, y))), sub);
        }
        else if (label is "wal" or "wex")
        {
            string body = pr.Render(n.Children[0]);
            Proof sub = body.Split(' ').Contains(x)
                ? SubstEq("wff", body, x, $"{x} = {y}")
                : pr.Apply("a1i", S(("ph", $"( {body} <-> {body} )"), ("ps", $"{x} = {y}")), pr.Apply("biid", S(("ph", body))));
            closed = pr.Apply(label == "wal" ? "cbvalvw" : "cbvexvw", S(("x", x), ("y", y), ("ph", body), ("ps", SubstFree(body, x, y))), sub);
        }
        else if (label is "cab" or "crab")
        {
            // { x | ph } and { x e. A | ph }: cbvabv, cbvrabv (children ph, x and, for crab, A).
            string body = pr.Render(n.Children[0]);
            Proof sub = body.Split(' ').Contains(x)
                ? SubstEq("wff", body, x, $"{x} = {y}")
                : pr.Apply("a1i", S(("ph", $"( {body} <-> {body} )"), ("ps", $"{x} = {y}")), pr.Apply("biid", S(("ph", body))));
            var s = S(("x", x), ("y", y), ("ph", body), ("ps", SubstFree(body, x, y)));
            if (label == "crab")
            {
                s["A"] = pr.Render(n.Children[2]);
            }
            closed = pr.Apply(label == "cab" ? "cbvabv" : "cbvrabv", s, sub);
        }
        else
        {
            throw new Refused($"no renaming rule for {label}");
        }
        return _d.Lift("T.", closed);
    }

    /// <summary>
    /// ( ph -> A e. D ) from a hypothesis A e. D' among <paramref name="hyps"/> whose D' differs from D only in the names
    /// of bound variables: a field's type, written once for the constructor and once inside the type, names its binders
    /// independently (Bind.mk's field ( a e. U |-> … )). Null when there is none.
    /// </summary>
    private Proof? HypUpToRenaming(string ph, string h, IEnumerable<string> hyps)
    {
        int at = h.IndexOf(" e. ", StringComparison.Ordinal);
        if (at < 0)
        {
            return null;
        }
        string a = h[..at], d = h[(at + 4)..];
        foreach (string g in hyps.Where(g => g.StartsWith(a + " e. ", StringComparison.Ordinal) && g != h))
        {
            string d2 = g[(a.Length + 4)..];
            if (Hyp(ph, g) is not Proof hg)
            {
                continue;
            }
            try
            {
                Proof eq = AlphaIn(ph, d2, d);
                return pr.Apply("eleqtrd", S(("ph", ph), ("A", a), ("B", d2), ("C", d)), hg, eq);
            }
            catch (Refused)
            {
            }
        }
        return null;
    }
}
