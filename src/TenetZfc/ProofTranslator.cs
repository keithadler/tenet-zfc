using TenetZfc.Metamath;
using MmExpr = TenetZfc.Metamath.Expr;
using Proof = (System.Collections.Generic.List<string> Proof, TenetZfc.Metamath.Expr Proves);

namespace TenetZfc;

/// <summary>
/// Translates Lean proof terms into set.mm deductions |- ( H -> ⟦P⟧ ), for the fragment List.length_append's proof
/// uses: lists and their lengths, Nat addition, equality, and the logic lemmas below. A proof is translated by what
/// each of its subterms proves (computed from the constants' types), not by mirroring the term:
///
/// - of_eq_true, Eq.trans (on propositions or values) and eq_self become fixed set.mm steps.
/// - A tree of congrArg, congr and congrFun' proves L = R from the equations at its leaves; it becomes a chain of
///   rewrites of ⟦L⟧ by those equations, each by the congruence prover, ending at ⟦R⟧.
/// - Lean's definitional unfolding (len nil to 0, nil ++ l to l, len (a :: l) to len l + 1, …) becomes rewriting by
///   set.mm equations (hash0, ccatlid, ccatass, ccatlen with s1len), applied until both sides agree.
/// - Nat.zero_add and Nat.succ_add are bridged by set.mm facts about +, not by translating their Lean proofs.
///
/// Induction (List.rec) is not translated here; the two cases of an induction are, each under its own hypotheses.
/// </summary>
public sealed class ProofTranslator
{
    private readonly Terms _t;
    private readonly Ops _ops;
    private readonly Environment _env;
    private readonly Prover _pr;
    private readonly Deduction _d;
    private readonly StatementTranslator _st;

    private readonly Name _ofEqTrue, _eqTrans, _eqSelf, _congrArg, _congr, _congrFun, _zeroAdd, _succAdd, _eq;

    private string _h = "";
    private readonly List<string> _hyps = new();
    private readonly Dictionary<ulong, Expr> _localTypes = new();
    private readonly Dictionary<ulong, int> _localHyp = new();   // a local proof (like ih) → its hypothesis index
    private string _elem = "A";                                // the element class of the lists in play

    public ProofTranslator(Terms t, Environment env, Prover pr)
    {
        _t = t;
        _ops = new Ops(t);
        _env = env;
        _pr = pr;
        _d = new Deduction(pr);
        _st = new StatementTranslator(t);
        _ofEqTrue = t.Of("of_eq_true");
        _eqTrans = t.Of("Eq.trans");
        _eqSelf = t.Of("eq_self");
        _congrArg = t.Of("congrArg");
        _congr = t.Of("congr");
        _congrFun = t.Of("congrFun'");
        _zeroAdd = t.Of("Nat.zero_add");
        _succAdd = t.Of("Nat.succ_add");
        _eq = t.Of("Eq");
    }

    private static Dictionary<string, string> S(params (string Var, string Value)[] xs) => xs.ToDictionary(x => x.Var, x => x.Value);

    // ---- context ----

    /// <summary>
    /// Start a deduction: each local is a free variable translated as a class variable; each has a hypothesis (its
    /// membership, or for a proof, its proposition). H is the hypotheses joined by /\, nested to the left.
    /// </summary>
    public void Begin(IEnumerable<(Expr Local, string Name)> typeVars, string elementClass, IEnumerable<(Expr Local, string Name, Expr Type, bool IsProof)> locals)
    {
        _st.Reset();
        _hyps.Clear();
        _localTypes.Clear();
        _localHyp.Clear();
        _elem = elementClass;
        foreach ((Expr x, string name) in typeVars)
        {
            _st.Bind(x, name);
        }
        foreach ((Expr x, string name, Expr type, bool isProof) in locals)
        {
            _localTypes[((FVar)x).Id] = type;
            if (isProof)
            {
                _localHyp[((FVar)x).Id] = _hyps.Count;
                _hyps.Add(_st.Wff(Beta(type)) ?? throw new InvalidOperationException($"a hypothesis outside the table: {_st.Why}"));
            }
            else
            {
                _st.Bind(x, name);
                _hyps.Add($"{name} e. {_st.Class(type) ?? throw new InvalidOperationException($"a type outside the table: {_st.Why}")}");
            }
        }
        _h = _hyps.Skip(1).Aggregate(_hyps[0], (acc, h) => $"( {acc} /\\ {h} )");
    }

    public string H => _h;

    /// <summary>The first n hypotheses joined by /\, nested to the left.</summary>
    private string Prefix(int n) => _hyps.Take(n).Skip(1).Aggregate(_hyps[0], (acc, h) => $"( {acc} /\\ {h} )");

    /// <summary>|- ( H -> h_i ).</summary>
    private Proof Hyp(int i) => HypIn(_hyps.Count, i);

    /// <summary>|- ( Prefix(n) -> h_i ), for i &lt; n.</summary>
    private Proof HypIn(int n, int i)
    {
        if (n == 1)
        {
            return _pr.Apply("id", S(("ph", _hyps[0])));
        }
        if (i == n - 1)
        {
            return _pr.Apply("simpr", S(("ph", Prefix(n - 1)), ("ps", _hyps[n - 1])));
        }
        return _d.Syl(_pr.Apply("simpl", S(("ph", Prefix(n - 1)), ("ps", _hyps[n - 1]))), HypIn(n - 1, i));
    }

    // ---- typing ----

    /// <summary>|- ( H -> c e. X ) for a translated term c: NN0 for lengths, sums and numerals, Word A for lists, A for elements.</summary>
    public Proof Member(string c)
    {
        SyntaxTree n = _pr.Parse("class", c.Split(' ')) ?? throw new InvalidOperationException($"not a class: {c}");
        if (n.Rule.Kind == 'f')
        {
            int i = _hyps.FindIndex(h => h.StartsWith(c + " e. ", StringComparison.Ordinal));
            return i >= 0 ? Hyp(i) : throw new InvalidOperationException($"no hypothesis for {c}");
        }
        switch (n.Rule.Label)
        {
            case "cc0":
                return _d.Lift(_h, (["0nn0"], MmExpr.Of("|- 0 e. NN0")));
            case "c1":
                return _d.Lift(_h, (["1nn0"], MmExpr.Of("|- 1 e. NN0")));
            case "c0":   // (/), the empty word
                return _d.Lift(_h, _pr.Apply("wrd0", S(("S", _elem))));
            case "cfv" when Var(n, "F") == "#":
                {
                    string w = Var(n, "A");
                    return _d.Syl(Member(w), _pr.Apply("lencl", S(("W", w), ("S", _elem))));
                }
            case "co" when Var(n, "F") == "+":
                return _pr.Apply("nn0addcld", S(("ph", _h), ("A", Var(n, "A")), ("B", Var(n, "B"))), Member(Var(n, "A")), Member(Var(n, "B")));
            case "co" when Var(n, "F") == "++":
                {
                    string a = Var(n, "A"), b = Var(n, "B");
                    return _pr.Apply("syl2anc", S(("ph", _h), ("ps", $"{a} e. Word {_elem}"), ("ch", $"{b} e. Word {_elem}"), ("th", $"( {a} ++ {b} ) e. Word {_elem}")),
                        Member(a), Member(b), _pr.Apply("ccatcl", S(("S", a), ("T", b), ("B", _elem))));
                }
            case "cs1":
                return _pr.Apply("s1cld", S(("ph", _h), ("A", Var(n, "A")), ("B", _elem)), Member(Var(n, "A")));
        }
        throw new InvalidOperationException($"no typing rule for {c}");
    }

    private string Var(SyntaxTree n, string v)
    {
        var vars = n.Rule.Hyps.Where(x => x.Kind == 'f').Select(x => x.Var!).ToList();
        return _pr.Render(n.Children[vars.IndexOf(v)]);
    }

    private Proof InCC(string c) => _d.Syl(Member(c), _pr.Apply("nn0cn", S(("A", c))));

    // ---- definitional unfolding, on the set.mm side ----

    /// <summary>The normal form of a translated term under the unfolding rules, and |- ( H -> c = nf ).</summary>
    public (string Nf, Proof Eq) Normalize(string c)
    {
        Proof eq = _d.Refl(_h, c);
        string cur = c;
        for (int round = 0; round < 64; round++)
        {
            if (Step(cur) is not (string next, Proof step))
            {
                return (cur, eq);
            }
            eq = _d.Trans(eq, step);
            cur = next;
        }
        throw new InvalidOperationException($"unfolding did not stop: {c}");
    }

    /// <summary>One unfolding step anywhere in the term (innermost first), or null when none applies.</summary>
    private (string, Proof)? Step(string c)
    {
        SyntaxTree n = _pr.Parse("class", c.Split(' ')) ?? throw new InvalidOperationException($"not a class: {c}");
        // Children first: rewrite inside, then lift by congruence.
        var vars = n.Rule.Hyps.Where(x => x.Kind == 'f').Select(x => x.Var!).ToList();
        for (int i = 0; i < n.Children.Count; i++)
        {
            if (n.Children[i].Rule.Expr.Type != "class" || vars[i] == "F")
            {
                continue;
            }
            string child = _pr.Render(n.Children[i]);
            if (Step(child) is (string nextChild, Proof inner))
            {
                // The context: this node with child i replaced by a fresh hole.
                string hole = Hole(c);
                var ctxSyms = vars.Select((v, k) => k == i ? hole : _pr.Render(n.Children[k])).ToList();
                string context = string.Join(' ', n.Rule.Expr.Symbols.Select(s => vars.IndexOf(s) is int j and >= 0 ? ctxSyms[j] : s));
                Proof lifted = _d.Congruence("class", context, hole, inner);
                return (_d.Sides(_d.Split(lifted.Proves).X).R, lifted);
            }
        }
        return Root(n, c);
    }

    private static string Hole(string c) => "ABCDEFGHIJKLMNOPQRSTUVWXYZ".Select(ch => ch.ToString()).Reverse().First(v => !c.Split(' ').Contains(v));

    private (string, Proof)? Root(SyntaxTree n, string c)
    {
        // ( # ` (/) ) = 0
        if (n.Rule.Label == "cfv" && Var(n, "F") == "#" && Var(n, "A") == "(/)")
        {
            return ("0", _d.Lift(_h, (["hash0"], MmExpr.Of("|- ( # ` (/) ) = 0"))));
        }
        if (n.Rule.Label == "co" && Var(n, "F") == "++")
        {
            string a = Var(n, "A"), b = Var(n, "B");
            // ( (/) ++ L ) = L
            if (a == "(/)")
            {
                return (b, _d.Syl(Member(b), _pr.Apply("ccatlid", S(("S", b), ("B", _elem)))));
            }
            // ( ( <" x "> ++ L ) ++ M ) = ( <" x "> ++ ( L ++ M ) )
            SyntaxTree an = _pr.Parse("class", a.Split(' '))!;
            if (an.Rule.Label == "co" && Var(an, "F") == "++" && _pr.Parse("class", Var(an, "A").Split(' '))!.Rule.Label == "cs1")
            {
                string s1 = Var(an, "A"), l = Var(an, "B");
                Proof three = _pr.Apply("3jca", S(("ph", _h), ("ps", $"{s1} e. Word {_elem}"), ("ch", $"{l} e. Word {_elem}"), ("th", $"{b} e. Word {_elem}")),
                    Member(s1), Member(l), Member(b));
                Proof ass = _d.Syl(three, _pr.Apply("ccatass", S(("S", s1), ("T", l), ("U", b), ("B", _elem))));
                return ($"( {s1} ++ ( {l} ++ {b} ) )", ass);
            }
        }
        // ( # ` ( <" x "> ++ L ) ) = ( ( # ` L ) + 1 )
        if (n.Rule.Label == "cfv" && Var(n, "F") == "#")
        {
            SyntaxTree w = _pr.Parse("class", Var(n, "A").Split(' '))!;
            if (w.Rule.Label == "co" && Var(w, "F") == "++" && _pr.Parse("class", Var(w, "A").Split(' '))!.Rule.Label == "cs1")
            {
                string s1 = Var(w, "A"), l = Var(w, "B"), x = Var(_pr.Parse("class", s1.Split(' '))!, "A");
                // ( # ` ( s1 ++ L ) ) = ( ( # ` s1 ) + ( # ` L ) )
                Proof len = _pr.Apply("syl2anc", S(("ph", _h), ("ps", $"{s1} e. Word {_elem}"), ("ch", $"{l} e. Word {_elem}"),
                        ("th", $"( # ` ( {s1} ++ {l} ) ) = ( ( # ` {s1} ) + ( # ` {l} ) )")),
                    Member(s1), Member(l), _pr.Apply("ccatlen", S(("S", s1), ("T", l), ("A", _elem), ("B", _elem))));
                // ( ( # ` s1 ) + ( # ` L ) ) = ( 1 + ( # ` L ) )
                Proof one = _d.Lift(_h, _pr.Apply("s1len", S(("A", x))));
                Proof plus = _pr.Apply("oveq1d", S(("ph", _h), ("A", $"( # ` {s1} )"), ("B", "1"), ("C", $"( # ` {l} )"), ("F", "+")), one);
                // ( 1 + ( # ` L ) ) = ( ( # ` L ) + 1 )
                Proof comm = _pr.Apply("addcomd", S(("ph", _h), ("A", "1"), ("B", $"( # ` {l} )")),
                    _d.Lift(_h, (["ax-1cn"], MmExpr.Of("|- 1 e. CC"))), InCC($"( # ` {l} )"));
                return ($"( ( # ` {l} ) + 1 )", _d.Trans(_d.Trans(len, plus), comm));
            }
        }
        return null;
    }

    /// <summary>From |- ( H -> L = R ): |- ( H -> L' = R' ) when L, L' and R, R' have the same normal forms.</summary>
    private Proof ConvertEq(Proof lr, string l2, string r2)
    {
        (string l, string r, _) = _d.Sides(_d.Split(lr.Proves).X);
        if (l == l2 && r == r2)
        {
            return lr;
        }
        (string nl, Proof pl) = Normalize(l);
        (string nl2, Proof pl2) = Normalize(l2);
        (string nr, Proof pr) = Normalize(r);
        (string nr2, Proof pr2) = Normalize(r2);
        if (nl != nl2 || nr != nr2)
        {
            throw new InvalidOperationException($"not the same up to unfolding: {l} = {r} and {l2} = {r2}");
        }
        // L' = nl = L = R = nr = R'
        Proof l2l = _d.Trans(pl2, _d.Symm(pl));
        Proof rr2 = _d.Trans(pr, _d.Symm(pr2));
        return _d.Trans(_d.Trans(l2l, lr), rr2);
    }

    /// <summary>From |- ( H -> P ): |- ( H -> P' ) for equations P, P' with the same sides up to unfolding.</summary>
    private Proof ConvertWff(Proof p, string target)
    {
        string have = _d.Split(p.Proves).X;
        if (have == target)
        {
            return p;
        }
        (string l2, string r2, _) = _d.Sides(target);
        return ConvertEq(p, l2, r2);
    }

    // ---- proof terms ----

    private Expr Beta(Expr e)
    {
        if (e.LooseBVarRange > 0 && e is not Binder && e is not App)
        {
            return e;
        }
        Expr head = Ops.Spine(e, out List<Expr> args);
        if (head is Binder { IsPi: false } && args.Count > 0)
        {
            Expr body = head;
            int m = 0;
            while (body is Binder { IsPi: false } lam && m < args.Count)
            {
                body = lam.Body;
                m++;
            }
            var subst = new List<Expr>();
            for (int i = m - 1; i >= 0; i--)
            {
                subst.Add(args[i]);
            }
            return Beta(_t.MkApp(_ops.Instantiate(body, subst), args.Skip(m)));
        }
        return e switch
        {
            App => _t.MkApp(Beta(head), args.Select(Beta)),
            Binder b => _t.Binding(b.IsPi, b.BinderName, b.Info, Beta(b.Domain), Beta(b.Body)),
            _ => e,
        };
    }

    /// <summary>What a proof term proves: its head's type, instantiated by its arguments.</summary>
    public Expr TypeOf(Expr p)
    {
        Expr head = Ops.Spine(p, out List<Expr> args);
        Expr ty = head switch
        {
            FVar f when _localTypes.TryGetValue(f.Id, out Expr? lt) => lt,
            Const c when _env.Find(c.Name) is ConstInfo info => _ops.InstantiateLevels(info.Type, info.LevelParams, c.Levels),
            _ => throw new InvalidOperationException($"cannot type the proof {p}"),
        };
        foreach (Expr a in args)
        {
            ty = Beta(ty);
            ty = ty is Binder { IsPi: true } pi ? _ops.Instantiate(pi.Body, [a]) : throw new InvalidOperationException($"too many arguments in {p}");
        }
        return Beta(ty);
    }

    private bool IsPropEq(Expr ty, out Expr l, out Expr r)
    {
        l = r = ty;
        if (Ops.Spine(ty, out List<Expr> a) is Const c && ReferenceEquals(c.Name, _eq) && a.Count == 3 && a[0] is Sort { Level: LZero })
        {
            (l, r) = (a[1], a[2]);
            return true;
        }
        return false;
    }

    private string WffOf(Expr prop) => _st.Wff(Beta(prop)) ?? throw new InvalidOperationException($"a proposition outside the table: {_st.Why}");
    private string ClassOf(Expr term) => _st.Class(Beta(term)) ?? throw new InvalidOperationException($"a term outside the table: {_st.Why}");

    /// <summary>|- ( H -> ⟦P⟧ ) for a proof p : P, where P is a proposition; |- ( H -> ( ⟦P⟧ <-> ⟦Q⟧ ) ) for p : P = Q in Prop.</summary>
    public Proof Prove(Expr p)
    {
        p = Beta(p);
        Expr head = Ops.Spine(p, out List<Expr> a);
        if (head is FVar f && _localHyp.TryGetValue(f.Id, out int hi) && a.Count == 0)
        {
            return Hyp(hi);
        }
        if (head is not Const c)
        {
            throw new InvalidOperationException($"a proof whose head is not a constant: {p}");
        }
        Name n = c.Name;
        if (ReferenceEquals(n, _ofEqTrue) && a.Count == 2)
        {
            // of_eq_true P h : P, from h : P = True
            Proof h = Prove(a[1]);
            (string lhs, _, _) = _d.Sides(_d.Split(h.Proves).X);
            Proof got = _pr.Apply("mpbiri", S(("ph", _h), ("ps", lhs), ("ch", "T.")), (["tru"], MmExpr.Of("|- T.")), h);
            return ConvertWff(got, WffOf(a[0]));
        }
        if (ReferenceEquals(n, _eqSelf) && a.Count == 2)
        {
            // eq_self a : (a = a) = True
            string x = ClassOf(a[1]);
            Proof refl = _pr.Apply("eqid", S(("A", x)));
            Proof bi = _pr.Apply("mpbi", S(("ph", $"{x} = {x}"), ("ps", $"( {x} = {x} <-> T. )")), refl, _pr.Apply("tbtru", S(("ph", $"{x} = {x}"))));
            return _d.Lift(_h, bi);
        }
        if (ReferenceEquals(n, _eqTrans) && a.Count == 6)
        {
            Proof h1 = Prove(a[4]), h2 = Prove(a[5]);
            if (a[0] is Sort)
            {
                // Propositions: ( P <-> Q ), ( Q <-> R ) give ( P <-> R ). The middle may differ by unfolding.
                (string pp, string q1, _) = _d.Sides(_d.Split(h1.Proves).X);
                (string q2, string rr, _) = _d.Sides(_d.Split(h2.Proves).X);
                if (q1 != q2)
                {
                    throw new InvalidOperationException($"Eq.trans in Prop with different middles: {q1} and {q2}");
                }
                return _pr.Apply("bitrd", S(("ph", _h), ("ps", pp), ("ch", q1), ("th", rr)), h1, h2);
            }
            return _d.Trans(h1, h2);
        }
        if (ReferenceEquals(n, _congrArg) || ReferenceEquals(n, _congr) || ReferenceEquals(n, _congrFun))
        {
            return Congruence(p);
        }
        if (ReferenceEquals(n, _zeroAdd) && a.Count == 1)
        {
            // 0 + n = n, from addlid and nn0cn: a set.mm fact, not Lean's proof of Nat.zero_add.
            string x = ClassOf(a[0]);
            return _d.Syl(InCC(x), _pr.Apply("addlid", S(("A", x))));
        }
        if (ReferenceEquals(n, _succAdd) && a.Count == 2)
        {
            // ( ( n + 1 ) + m ) = ( ( n + m ) + 1 ), from associativity and commutativity: a set.mm fact.
            string x = ClassOf(a[0]), y = ClassOf(a[1]);
            Proof cx = InCC(x), cy = InCC(y), c1 = _d.Lift(_h, (["ax-1cn"], MmExpr.Of("|- 1 e. CC")));
            Proof left = _pr.Apply("addassd", S(("ph", _h), ("A", x), ("B", "1"), ("C", y)), cx, c1, cy);           // ( ( x + 1 ) + y ) = ( x + ( 1 + y ) )
            Proof swap = _pr.Apply("addcomd", S(("ph", _h), ("A", "1"), ("B", y)), c1, cy);                         // ( 1 + y ) = ( y + 1 )
            Proof inner = _pr.Apply("oveq2d", S(("ph", _h), ("A", $"( 1 + {y} )"), ("B", $"( {y} + 1 )"), ("C", x), ("F", "+")), swap);
            Proof right = _pr.Apply("addassd", S(("ph", _h), ("A", x), ("B", y), ("C", "1")), cx, cy, c1);           // ( ( x + y ) + 1 ) = ( x + ( y + 1 ) )
            return _pr.Apply("eqtr4d", S(("ph", _h), ("A", $"( ( {x} + 1 ) + {y} )"), ("B", $"( {x} + ( {y} + 1 ) )"), ("C", $"( ( {x} + {y} ) + 1 )")),
                _d.Trans(left, inner), right);
        }
        throw new InvalidOperationException($"no translation rule for {n}");
    }

    /// <summary>|- ( H -> ⟦expected⟧ ) from a proof whose own type equals the expected proposition up to unfolding.</summary>
    public Proof ProveAs(Expr p, Expr expected) => ConvertWff(Prove(p), WffOf(expected));

    /// <summary>
    /// A tree of congrArg / congr / congrFun' proving L = R: rewrite ⟦L⟧ with the equations at the tree's leaves, in
    /// order, until it reaches ⟦R⟧ (up to unfolding).
    /// </summary>
    private Proof Congruence(Expr p)
    {
        Expr ty = TypeOf(p);
        var leaves = new List<Expr>();
        CollectLeaves(p, leaves);
        bool prop = IsPropEq(ty, out Expr pl, out Expr prr);
        if (!prop)
        {
            Ops.Spine(ty, out List<Expr> ea);
            (pl, prr) = (ea[1], ea[2]);
        }
        string type = prop ? "wff" : "class";
        string start = prop ? WffOf(pl) : ClassOf(pl);
        string goal = prop ? WffOf(prr) : ClassOf(prr);
        (string cur, Proof acc) = NormalizeAny(type, start);
        foreach (Expr leaf in leaves)
        {
            Proof e = Prove(leaf);
            (string a, string b, _) = _d.Sides(_d.Split(e.Proves).X);
            (string na, Proof pa) = Normalize(a);
            (string nb, Proof pb) = Normalize(b);
            Proof norm = _d.Trans(_d.Trans(_d.Symm(pa), e), pb);   // na = nb
            string hole = Hole(cur + " " + na + " " + nb);
            string context = Replace(type, cur, na, hole) ?? throw new InvalidOperationException($"{na} does not occur in {cur}");
            Proof step = _d.Congruence(type, context, hole, norm);
            acc = Chain(type, acc, step);
            cur = _d.Sides(_d.Split(step.Proves).X).R;
        }
        (string ng, Proof pg) = NormalizeAny(type, goal);
        if (ng != cur)
        {
            throw new InvalidOperationException($"the rewrites end at {cur}, not at {ng}");
        }
        return Chain(type, acc, Flip(type, pg));
    }

    private void CollectLeaves(Expr p, List<Expr> leaves)
    {
        Expr head = Ops.Spine(p, out List<Expr> a);
        if (head is Const c && (ReferenceEquals(c.Name, _congrArg) || ReferenceEquals(c.Name, _congr) || ReferenceEquals(c.Name, _congrFun)))
        {
            // The proof arguments are the ones whose type is an equation: the last for congrArg, the last two for
            // congr, the first proof argument for congrFun'.
            Info(c.Name, a, out var proofArgs);
            foreach (Expr x in proofArgs)
            {
                CollectLeaves(x, leaves);
            }
            return;
        }
        leaves.Add(p);
    }

    private void Info(Name n, List<Expr> a, out List<Expr> proofArgs)
    {
        if (ReferenceEquals(n, _congrArg))
        {
            proofArgs = [a[^1]];   // congrArg {α β} {a₁ a₂} (f) (h)
        }
        else if (ReferenceEquals(n, _congr))
        {
            proofArgs = [a[^2], a[^1]];   // congr {α β} {f₁ f₂} {a₁ a₂} (h₁) (h₂)
        }
        else
        {
            proofArgs = [a[^2]];   // congrFun' {α β} {f g} (h) (a)
        }
    }

    /// <summary>The term with every occurrence of a subterm replaced by the hole, or null when it does not occur.</summary>
    private string? Replace(string type, string whole, string sub, string hole)
    {
        SyntaxTree t = _pr.Parse(type, whole.Split(' '))!;
        bool found = false;
        string Go(SyntaxTree n)
        {
            string r = _pr.Render(n);
            if (n.Rule.Expr.Type == "class" && r == sub)
            {
                found = true;
                return hole;
            }
            if (n.Rule.Kind == 'f')
            {
                return r;
            }
            var vars = n.Rule.Hyps.Where(x => x.Kind == 'f').Select(x => x.Var!).ToList();
            var kids = n.Children.Select(Go).ToList();
            return string.Join(' ', n.Rule.Expr.Symbols.Select(s => vars.IndexOf(s) is int i and >= 0 ? kids[i] : s));
        }
        string res = Go(t);
        return found ? res : null;
    }

    private (string, Proof) NormalizeAny(string type, string x)
    {
        if (type == "class")
        {
            return Normalize(x);
        }
        // A formula: normalize both sides of its equation (the only formulas a rewrite chain meets here).
        (string l, string r, _) = _d.Sides(x);
        (string nl, Proof pl) = Normalize(l);
        (string nr, Proof prr) = Normalize(r);
        // ( l = r <-> nl = nr ) via eqeq12d
        Proof bi = _pr.Apply("eqeq12d", S(("ph", _h), ("A", l), ("B", nl), ("C", r), ("D", nr)), pl, prr);
        return ($"{nl} = {nr}", bi);
    }

    private Proof Chain(string type, Proof a, Proof b) =>
        type == "class" ? _d.Trans(a, b) : _pr.Apply("bitrd", S(("ph", _h), ("ps", _d.Sides(_d.Split(a.Proves).X).L),
            ("ch", _d.Sides(_d.Split(a.Proves).X).R), ("th", _d.Sides(_d.Split(b.Proves).X).R)), a, b);

    private Proof Flip(string type, Proof a)
    {
        if (type == "class")
        {
            return _d.Symm(a);
        }
        (string l, string r, _) = _d.Sides(_d.Split(a.Proves).X);
        return _pr.Apply("bicomd", S(("ph", _h), ("ps", l), ("ch", r)), a);
    }
}
