using TenetZfc.Metamath;
using MmExpr = TenetZfc.Metamath.Expr;
using Proof = (System.Collections.Generic.List<string> Proof, TenetZfc.Metamath.Expr Proves);

namespace TenetZfc;

/// <summary>
/// Lean theorems proved through the generic model (docs/milestone3.md, "Theorems through the model").
///
/// The model is sound for Lean's typing: if Γ ⊢ e : T then ⟦e⟧ ∈ ⟦T⟧. A theorem's proof p : P is then a proof that
/// (/) ∈ ⟦P⟧, its statement holding in the model. The translator proves exactly that, by following the typing of p:
/// each typing step becomes a membership step (an application by fvixp or ffvelcdmd, a λ by mptelixpg or fmptd, a
/// proof of a Π-proposition by ralrimiva and rspcdv), and each conversion T ≡ T' becomes an equation ⟦T⟧ = ⟦T'⟧ of
/// the model, by its beta (fvmptd3), delta (the definitions), iota (the computation rules) and projection (op1st,
/// op2nd) steps. Constants are typed once each, by lemmas written into the output.
///
/// It runs on the model's tower mode, after monomorphization (Universes.cs, Monomorph.cs).
/// </summary>
public sealed class TheoremTranslator
{
    private readonly Terms _t;
    private readonly Monomorph _mono;
    private readonly Model _model;

    public TheoremTranslator(Terms t, Environment env, Prover pr)
    {
        _t = t;
        pr.Sharing = true;
        _mono = new Monomorph(t, env);
        _model = new Model(t, _mono.Env, pr, tower: true);
    }

    /// <summary>The declarations and lemmas written so far, in order.</summary>
    public string Declarations => _model.Declarations;

    /// <summary>
    /// The theorem as |- ( hypotheses -> (/) e. ⟦statement⟧ ), its leading binders opened as hypotheses: U e. lean.-tower,
    /// then A e. ⟦T⟧ for each data binder and (/) e. ⟦P⟧ for each hypothesis. Its universe parameters are set to 0.
    /// </summary>
    public (MmExpr Statement, List<string> Proof) Prove(Name theorem)
    {
        ConstInfo c = _mono.Env.Find(theorem) ?? throw new Model.Refused($"{theorem} is not in the export");
        if (c.Kind != ConstKind.Theorem || c.Value is null)
        {
            throw new Model.Refused($"{theorem} is not a theorem");
        }
        Name inst = _mono.Instance(theorem, c.LevelParams.Select(_ => _t.Zero).ToArray());
        return _model.ProveTheorem(_mono.Env.Find(inst)!);
    }
}

public sealed partial class Model
{
    // ---- lemmas written into the output ------------------------------------------------------------------------

    /// <summary>Write |- statement as a $p with its proof and exactly the $d conditions the proof needs; teach it to the prover.</summary>
    private void EmitLemma(string label, string comment, Proof p)
    {
        SharedProofs sh = pr.Database.Shared;
        long size = sh.Size(p.Proof);
        Debug($"lemma {label}: {size} steps");
        comment = new string(comment.Where(ch => ch < 128).ToArray());
        p = RenameInternal(p);
        var dv = DistinctVars.Required(pr.Database, p.Proof);
        // Written compressed straight from the shared proof (it is never expanded).
        var mandatory = pr.Database.MandatoryHyps(p.Proves).Select(h => h.Label).ToList();
        (List<string> labels, string letters) = CompressedProof.Compress(p.Proof, mandatory,
            l => pr.Database[l] is { Kind: 'a' or 'p' } st ? st.Hyps.Count : 0, sh);
        var proofText = new System.Text.StringBuilder();
        Writer.AppendCompressed(proofText, "    ", labels, letters);
        string text = $"""
            $( {comment} $)
            {"${"}
              {string.Join(" ", dv.Select(d => $"$d {d.Item1} {d.Item2} $."))}
              {label} $p {p.Proves} $=
            {proofText} $.
            {"$}"}

            """;
        _out.AppendLine(text);
        pr.Database.Extend(text);
        LemmaSteps[label] = size;
        LemmaShared[label] = sh.Reachable(p.Proof).Count + p.Proof.Count;
    }

    /// <summary>
    /// The proof with its internal set variables (those its statement doesn't mention) renamed to letters from the far
    /// end of the alphabet that the proof doesn't use. A consistent renaming of variables keeps a proof valid, and it
    /// keeps the lemma's $d conditions away from the variables a context binds (which come from the front).
    /// </summary>
    private Proof RenameInternal(Proof p)
    {
        var inStmt = p.Proves.Symbols.ToHashSet();
        var used = new HashSet<string>();
        foreach (string l in pr.Database.Shared.Labels(p.Proof))
        {
            if (pr.Database.Statements.TryGetValue(l, out Statement? st) && st.Kind == 'f' && st.Expr.Type == "setvar")
            {
                used.Add(st.Var!);
            }
        }
        var internals = used.Where(v => !inStmt.Contains(v)).ToList();
        var free = Enumerable.Reverse(QuantLetters).Where(v => !used.Contains(v) && !inStmt.Contains(v)).ToList();
        var map = new Dictionary<string, string>();
        var vars = new Dictionary<string, string>();
        foreach (string v in internals)
        {
            if (free.Count == 0)
            {
                break;
            }
            // Only move a variable that sits at the front, where contexts take theirs.
            if (Array.IndexOf(QuantLetters, v) >= 13 || !QuantLetters.Contains(v))
            {
                continue;
            }
            map[pr.Database.FloatOf(v)!.Label] = pr.Database.FloatOf(free[0])!.Label;
            vars[v] = free[0];
            free.RemoveAt(0);
        }
        return map.Count == 0 ? p : (pr.Database.Shared.Rename(p.Proof, map, vars), p.Proves);
    }

    /// <summary>The proof size of each lemma written, by label.</summary>
    public Dictionary<string, long> LemmaSteps { get; } = new();

    /// <summary>The number of distinct shared steps each lemma's proof is built from, by label.</summary>
    public Dictionary<string, long> LemmaShared { get; } = new();

    private bool Has(string label) => pr.Database.Statements.ContainsKey(label);

    /// <summary>Facts about the tower U, proved once from the definition of lean.-tower.</summary>
    private void EnsureTowerLemmas()
    {
        EnsureTower();
        if (Has("lean-tw"))
        {
            return;
        }
        const string tw = "{ f | ( ( f : _om --> Univ /\\ _om e. ( f ` (/) ) ) /\\ A. n e. _om ( f ` n ) e. ( f ` suc n ) ) }";
        const string body = "( ( U : _om --> Univ /\\ _om e. ( U ` (/) ) ) /\\ A. n e. _om ( U ` n ) e. ( U ` suc n ) )";
        const string h = "U e. lean.-tower";
        // lean-tw: what U e. lean.-tower says.
        {
            Proof df = Cite("df-lean.-tower");
            Proof iff1 = pr.Apply("eleq2i", S(("C", "U"), ("A", TowerToken), ("B", tw)), df);
            Proof inAb = _d.Syl(pr.Apply("id", S(("ph", h))), Bi1(iff1));
            string inner = "( ( f : _om --> Univ /\\ _om e. ( f ` (/) ) ) /\\ A. n e. _om ( f ` n ) e. ( f ` suc n ) )";
            Proof sub = _d.Congruence("wff", Subst(inner, "f", "Z"), "Z", pr.Apply("id", S(("ph", "f = U"))));
            Proof elab = pr.Apply("elabg", S(("x", "f"), ("ph", inner), ("ps", body), ("A", "U"), ("V", "_V")), sub);
            Proof isSet = pr.Apply("elex", S(("A", "U"), ("B", TowerToken)));
            Proof bi = _d.Syl(isSet, elab);
            Proof r = pr.Apply("mpbid", S(("ph", h), ("ps", $"U e. {tw}"), ("ch", body)), inAb, bi);
            EmitLemma("lean-tw", "What U e. lean.-tower says.", r);
        }
        string ph = $"( {h} /\\ K e. _om )";
        Proof tw0 = _d.Syl(Hyp(ph, h)!.Value, ApplyId("lean-tw", S(("U", "U"))));
        Proof f = pr.Apply("simpld", S(("ph", ph), ("ps", "U : _om --> Univ"), ("ch", "_om e. ( U ` (/) )")),
            pr.Apply("simpld", S(("ph", ph), ("ps", "( U : _om --> Univ /\\ _om e. ( U ` (/) ) )"), ("ch", "A. n e. _om ( U ` n ) e. ( U ` suc n )")), tw0));
        EmitLemma("lean-tw-u", "Each level of a tower is a Grothendieck universe.",
            pr.Apply("ffvelcdmd", S(("ph", ph), ("F", "U"), ("A", "_om"), ("B", "Univ"), ("C", "K")), f, Hyp(ph, "K e. _om")!.Value));
        {
            Proof all = pr.Apply("simprd", S(("ph", ph), ("ps", "( U : _om --> Univ /\\ _om e. ( U ` (/) ) )"), ("ch", "A. n e. _om ( U ` n ) e. ( U ` suc n )")), tw0);
            Proof sub = _d.Congruence("wff", "( U ` Z ) e. ( U ` suc Z )", "Z", pr.Apply("simpr", S(("ph", ph), ("ps", "n = K"))));
            Proof r = pr.Apply("rspcdv", S(("ph", ph), ("x", "n"), ("A", "K"), ("B", "_om"), ("ps", "( U ` n ) e. ( U ` suc n )"), ("ch", "( U ` K ) e. ( U ` suc K )")),
                Hyp(ph, "K e. _om")!.Value, sub);
            EmitLemma("lean-tw-s", "Each level of a tower is a member of the next.", pr.Apply("mpd", S(("ph", ph), ("ps", "A. n e. _om ( U ` n ) e. ( U ` suc n )"), ("ch", "( U ` K ) e. ( U ` suc K )")), all, r));
        }
        {
            Proof t0 = ApplyId("lean-tw", S(("U", "U")));
            Proof a = pr.Apply("simpld", S(("ph", h), ("ps", "( U : _om --> Univ /\\ _om e. ( U ` (/) ) )"), ("ch", "A. n e. _om ( U ` n ) e. ( U ` suc n )")), t0);
            EmitLemma("lean-tw-om", "The first level of a tower contains omega.",
                pr.Apply("simprd", S(("ph", h), ("ps", "U : _om --> Univ"), ("ch", "_om e. ( U ` (/) )")), a));
        }
        // lean-prop: a proposition holds exactly when (/) is in it.
        {
            const string p = "( (/) e. if ( ph , 1o , (/) ) <-> ph )";
            Proof t1 = pr.Apply("iftrue", S(("ph", "ph"), ("A", "1o"), ("B", "(/)")));
            Proof e1 = pr.Apply("eleq2d", S(("ph", "ph"), ("A", "if ( ph , 1o , (/) )"), ("B", "1o"), ("C", "(/)")), t1);
            Proof back = pr.Apply("mpbiri", S(("ph", "ph"), ("ps", "(/) e. if ( ph , 1o , (/) )"), ("ch", "(/) e. 1o")), pr.Apply("0lt1o", S()), e1);
            Proof f1 = pr.Apply("iffalse", S(("ph", "ph"), ("A", "1o"), ("B", "(/)")));
            Proof e2 = pr.Apply("eleq2d", S(("ph", "-. ph"), ("A", "if ( ph , 1o , (/) )"), ("B", "(/)"), ("C", "(/)")), f1);
            Proof no = pr.Apply("mtbiri", S(("ph", "-. ph"), ("ps", "(/) e. if ( ph , 1o , (/) )"), ("ch", "(/) e. (/)")), pr.Apply("noel", S(("A", "(/)"))), e2);
            Proof fwd = pr.Apply("con4i", S(("ph", "ph"), ("ps", "(/) e. if ( ph , 1o , (/) )")), no);
            Proof r = pr.Apply("impbii", S(("ph", "(/) e. if ( ph , 1o , (/) )"), ("ps", "ph")), fwd, back);
            _ = p;
            EmitLemma("lean-prop", "A proposition of the model, if ( ph , 1o , (/) ), holds exactly when (/) is in it.", r);
        }
    }

    /// <summary>Apply an assertion, substituting each variable the substitution doesn't mention by itself (bound variables).</summary>
    private Proof ApplyId(string label, Dictionary<string, string> subst, params Proof[] hyps)
    {
        foreach (Statement h in pr.Database[label].Hyps.Where(h => h.Kind == 'f'))
        {
            subst.TryAdd(h.Var!, h.Var!);
        }
        return pr.Apply(label, subst, hyps);
    }

    /// <summary>An assertion with each variable substituted by itself.</summary>
    private Proof Cite(string label)
    {
        Statement st = pr.Database[label];
        return pr.Apply(label, st.Hyps.Where(h => h.Kind == 'f').ToDictionary(h => h.Var!, h => h.Var!));
    }

    private Proof Bi1(Proof iff)
    {
        // |- ( a <-> b )  gives  |- ( a -> b )
        SyntaxTree n = pr.Parse("wff", iff.Proves.Symbols)!;
        return pr.Apply("biimpi", S(("ph", pr.Render(n.Children[0])), ("ps", pr.Render(n.Children[1]))), iff);
    }

    // ---- proof contexts ---------------------------------------------------------------------------------------

    /// <summary>
    /// A context of a proof in deduction form ( ph -> … ): the Lean locals, each with its text (a class variable, a
    /// set variable bound by an enclosing λ, or (/) for a proof) and the proof of its membership under ph.
    /// </summary>
    private sealed class PCtx
    {
        public string Ph = "";
        public Dictionary<ulong, string> Vars { get; } = new();
        public Dictionary<ulong, Expr> Types { get; } = new();
        public Dictionary<ulong, (Proof P, string Ty)> Mems { get; } = new();
        public List<string> Binders { get; } = new();
        public ulong LastFv;

        /// <summary>
        /// Memberships already proved in this context, by term (terms are hash-consed): a term typed twice, as Lean's
        /// kernel caches inferred types, is proved once. Each is kept with the hypotheses it was proved under.
        /// </summary>
        public Dictionary<Expr, (string Ph, Typed T)> Memo { get; } = new(ReferenceEqualityComparer.Instance);

        public PCtx Clone()
        {
            var c = new PCtx { Ph = Ph };
            foreach (var kv in Vars) c.Vars[kv.Key] = kv.Value;
            foreach (var kv in Types) c.Types[kv.Key] = kv.Value;
            foreach (var kv in Mems) c.Mems[kv.Key] = kv.Value;
            c.Binders.AddRange(Binders);
            return c;
        }
    }

    private Scope ScopeIn(PCtx c)
    {
        var sc = new Scope("U");
        foreach (var kv in c.Vars) sc.Vars[kv.Key] = kv.Value;
        foreach (var kv in c.Types) sc.Types[kv.Key] = kv.Value;
        // A new binder avoids the enclosing ones. (Where ralrimiva needs it out of the hypotheses too, it is renamed.)
        foreach (string v in c.Binders.Distinct())
        {
            sc.Active.Add(v);
        }
        return sc;
    }

    private string TrIn(PCtx c, Expr e) => Tr(e, ScopeIn(c));

    private Expr InferIn(PCtx c, Expr e)
    {
        try
        {
            return _typing.Infer(e, c.Types);
        }
        catch (Typing.Stuck s)
        {
            throw new Refused($"can't infer a type: {s.Message}");
        }
    }

    private bool IsProofIn(PCtx c, Expr e) => _typing.IsProof(e, c.Types) == true;

    /// <summary>The context extended by a binder x : A whose text is the set variable x, with hypothesis x e. D.</summary>
    private (PCtx C, Expr Fv) Enter(PCtx c, Expr domain, string x, string dom)
    {
        var d = c.Clone();
        string hyp = $"{x} e. {dom}";
        d.Ph = $"( {c.Ph} /\\ {hyp} )";
        foreach (var kv in c.Mems)
        {
            d.Mems[kv.Key] = (pr.Apply("adantr", S(("ph", c.Ph), ("ps", _d.Split(kv.Value.P.Proves).X), ("ch", hyp)), kv.Value.P), kv.Value.Ty);
        }
        Expr fv = t.FVar(_fresh++);
        ulong id = ((FVar)fv).Id;
        d.Types[id] = domain;
        d.LastFv = id;
        d.Binders.Add(x);
        Proof inD = pr.Apply("simpr", S(("ph", c.Ph), ("ps", hyp)));
        if (_typing.IsProposition(domain, c.Types) == true)
        {
            // A proof: its text is (/), and (/) is in the proposition, since x is (lean-pf).
            d.Vars[id] = "(/)";
            Proof isProp = Weaken(FixMem(c.Ph, MemOf(c, domain).P, dom, "2o"), hyp);
            EnsurePf();
            d.Mems[id] = (_d.Syl(_d.Jca(isProp, inD), ApplyId("lean-pf", S(("A", dom), ("B", x)))), dom);
        }
        else
        {
            d.Vars[id] = x;
            d.Mems[id] = (inD, dom);
        }
        return (d, fv);
    }

    private Proof Weaken(Proof p, string hyp)
    {
        (string ph, string x) = _d.Split(p.Proves);
        return pr.Apply("adantr", S(("ph", ph), ("ps", x), ("ch", hyp)), p);
    }

    /// <summary>lean-pf: a member of a proposition makes it hold. |- ( ( A e. 2o /\ B e. A ) -> (/) e. A ).</summary>
    private void EnsurePf()
    {
        if (Has("lean-pf"))
        {
            return;
        }
        const string ph = "( A e. 2o /\\ B e. A )";
        // A e. 2o gives A = (/) or A = 1o (df2o3, elpri). Not (/): B is in it. So 1o, which has (/).
        Proof a2 = pr.Apply("simpl", S(("ph", "A e. 2o"), ("ps", "B e. A")));
        Proof df = pr.Apply("df2o3", S());
        Proof inPr = pr.Apply("eleqtrd", S(("ph", ph), ("A", "A"), ("B", "2o"), ("C", "{ (/) , 1o }")), a2, _d.Lift(ph, df));
        Proof cases = _d.Syl(inPr, pr.Apply("elpri", S(("A", "A"), ("B", "(/)"), ("C", "1o"))));
        // A = (/) is impossible: B e. A.
        Proof bIn = pr.Apply("simpr", S(("ph", "A e. 2o"), ("ps", "B e. A")));
        Proof notEmpty = _d.Syl(bIn, pr.Apply("ne0i", S(("B", "B"), ("A", "A"))));
        Proof notZero = pr.Apply("neneqd", S(("ph", ph), ("A", "A"), ("B", "(/)")), notEmpty);
        Proof isOne = pr.Apply("ord", S(("ph", ph), ("ps", "A = (/)"), ("ch", "A = 1o")), cases);
        Proof one = pr.Apply("mpd", S(("ph", ph), ("ps", "-. A = (/)"), ("ch", "A = 1o")), notZero, isOne);
        Proof r = pr.Apply("eleqtrrd", S(("ph", ph), ("A", "(/)"), ("B", "1o"), ("C", "A")), _d.Lift(ph, pr.Apply("0lt1o", S())), one);
        EmitLemma("lean-pf", "A member of a proposition of the model makes it hold.", r);
    }

    /// <summary>lean-pf0: a member of a proposition of the model is (/). |- ( ( A e. 2o /\ B e. A ) -> B = (/) ).</summary>
    private void EnsurePf0()
    {
        if (Has("lean-pf0"))
        {
            return;
        }
        const string ph = "( A e. 2o /\\ B e. A )";
        // As lean-pf: A is (/) or 1o, not (/) since B is in it; so B e. 1o, and the only member of 1o is (/) (el1o).
        Proof a2 = pr.Apply("simpl", S(("ph", "A e. 2o"), ("ps", "B e. A")));
        Proof inPr = pr.Apply("eleqtrd", S(("ph", ph), ("A", "A"), ("B", "2o"), ("C", "{ (/) , 1o }")), a2, _d.Lift(ph, pr.Apply("df2o3", S())));
        Proof cases = _d.Syl(inPr, pr.Apply("elpri", S(("A", "A"), ("B", "(/)"), ("C", "1o"))));
        Proof bIn = pr.Apply("simpr", S(("ph", "A e. 2o"), ("ps", "B e. A")));
        Proof notZero = pr.Apply("neneqd", S(("ph", ph), ("A", "A"), ("B", "(/)")), _d.Syl(bIn, pr.Apply("ne0i", S(("B", "B"), ("A", "A")))));
        Proof one = pr.Apply("mpd", S(("ph", ph), ("ps", "-. A = (/)"), ("ch", "A = 1o")), notZero,
            pr.Apply("ord", S(("ph", ph), ("ps", "A = (/)"), ("ch", "A = 1o")), cases));
        Proof bIn1 = pr.Apply("eleqtrd", S(("ph", ph), ("A", "B"), ("B", "A"), ("C", "1o")), bIn, one);
        EmitLemma("lean-pf0", "A member of a proposition of the model is (/).",
            pr.Apply("sylib", S(("ph", ph), ("ps", "B e. 1o"), ("ch", "B = (/)")), bIn1, pr.Apply("el1o", S(("A", "B")))));
    }

    // ---- membership: ( ph -> ⟦e⟧ e. ⟦T⟧ ) ---------------------------------------------------------------------

    /// <summary>A membership proof ( ph -> X e. Ty ), with the Lean type whose translation Ty is.</summary>
    private sealed record Typed(Proof P, string Ty, Expr LTy);

    private int _depth;

    private Typed MemOf(PCtx c, Expr e)
    {
        if (++_depth > 400)
        {
            _depth = 0;
            throw new Refused("typing recursion too deep");
        }
        if (c.Memo.TryGetValue(e, out var known) && known.Ph == c.Ph)
        {
            _depth--;
            return known.T;
        }
        try
        {
            Typed m = MemCore(c, e);
            string elem = pr.Render(pr.Parse("wff", _d.Split(m.P.Proves).X.Split(' '))!.Children[0]);
            if (elem != "(/)" && TrIn(c, e) == "(/)")
            {
                // A proof reached through data (a field of a structure): a member of a proposition makes (/) one.
                EnsurePf();
                Proof isProp = Check(c, m.LTy, InferIn(c, m.LTy), "2o");
                m = m with { P = _d.Syl(_d.Jca(isProp, m.P), pr.Apply("lean-pf", S(("A", m.Ty), ("B", elem)))) };
            }
            c.Memo[e] = (c.Ph, m);
            return m;
        }
        finally
        {
            _depth--;
        }
    }

    private Typed MemCore(PCtx c, Expr e)
    {
        switch (e)
        {
            case FVar f:
                {
                    var (p, ty) = c.Mems.TryGetValue(f.Id, out var m) ? m : throw new Refused("a local with no hypothesis");
                    return new Typed(p, ty, c.Types[f.Id]);
                }
            case Let l:
                return MemOf(c, _ops.Instantiate(l.Body, [l.Value]));
            case Const k:
                return ConstMem(c, k);
            case Sort s:
                return SortMem(c, s);
            case Binder { IsPi: false } lam:
                return LamMem(c, lam);
            case Binder { IsPi: true } pi:
                return PiMem(c, pi);
            case App:
                {
                    Expr head = Ops.Spine(e, out List<Expr> args);
                    Typed m = MemOf(c, head);
                    Expr cur = head;
                    foreach (Expr a in args)
                    {
                        m = ApplyArg(c, m, cur, a);
                        cur = t.App(cur, a);
                    }
                    return m;
                }
            case NatLit lit:
                return LitMem(c, lit);
            case Proj p:
                return ProjMem(c, p);
        }
        throw new Refused($"no typing rule yet for {e.GetType().Name}");
    }

    /// <summary>( ph -> ⟦e⟧ e. target ), converting the inferred type to the target when they differ.</summary>
    private Proof Check(PCtx c, Expr e, Expr target, string targetText)
    {
        Typed m = MemOf(c, e);
        if (m.Ty == targetText)
        {
            return m.P;
        }
        if (targetText.StartsWith("( U. ran U ^m ", StringComparison.Ordinal) && !m.Ty.StartsWith("( U. ran U ^m ", StringComparison.Ordinal))
        {
            // A motive into a level of the tower, where a recursor expects one into the whole tower.
            return Cumulate(c.Ph, TrIn(c, e), m.Ty, targetText, m.P);
        }
        Proof eq = ConvText(c, m.LTy, m.Ty, target, targetText);
        return pr.Apply("eleqtrd", S(("ph", c.Ph), ("A", TrIn(c, e)), ("B", m.Ty), ("C", targetText)), m.P, eq);
    }

    /// <summary>Apply a function of type m to the argument a.</summary>
    private Typed ApplyArg(PCtx c, Typed m, Expr f, Expr a)
    {
        string fText = TrIn(c, f), aText = TrIn(c, a);
        for (int attempt = 0; attempt < 50; attempt++)
        {
            SyntaxTree n = pr.Parse("class", m.Ty.Split(' ')) ?? throw new Refused($"does not parse: {m.Ty}");
            Expr lty = m.LTy;
            Binder? pi = WhnfType(c, lty) as Binder;
            switch (n.Rule.Label)
            {
                case "cixp" when pi is { IsPi: true }:
                    {
                        string x = pr.Render(n.Children[0]), dom = pr.Render(n.Children[1]), body = pr.Render(n.Children[2]);
                        if (aText.Split(' ').Contains(x) || fText.Split(' ').Contains(x))
                        {
                            // fvixp needs x distinct from the function and the argument: rename the product's variable (cbvixpv).
                            string y = FreshFor(aText, fText, body, dom, c.Ph);
                            string bodyY = SubstFree(body, x, y);
                            string ty2 = $"X_ {y} e. {dom} {bodyY}";
                            Proof ren = dom.Split(' ').Contains(x)
                                ? AlphaClosed(m.Ty, ty2)   // x bound in the domain too: cbvixpv can't, alpha-equivalence renames it apart
                                : pr.Apply("cbvixpv", S(("x", x), ("y", y), ("A", dom), ("B", body), ("C", bodyY)), SubstEq("class", body, x, $"{x} = {y}"));
                            m = m with { P = pr.Apply("eleqtrd", S(("ph", c.Ph), ("A", fText), ("B", m.Ty), ("C", ty2)), m.P, _d.Lift(c.Ph, ren)), Ty = ty2 };
                            (x, body) = (y, bodyY);
                        }
                        if (BoundIn(body).Overlaps(ArgVars(aText)))
                        {
                            // The body's binders must avoid the argument's variables (the substitution's congruence
                            // passes under them with the argument in its hypothesis).
                            string body2 = RenameApart(body, ArgVars(aText), c.Ph);
                            string ty2 = $"X_ {x} e. {dom} {body2}";
                            m = m with { P = pr.Apply("eleqtrd", S(("ph", c.Ph), ("A", fText), ("B", m.Ty), ("C", ty2)), m.P, AlphaIn(c.Ph, m.Ty, ty2)), Ty = ty2 };
                            body = body2;
                        }
                        RefuseCapture(aText, body, x);
                        Proof aIn = Check(c, a, pi.Domain, dom);
                        string inst = SubstFree(body, x, aText);
                        Proof sub = body.Split(' ').Contains(x)
                            ? SubstEq("class", body, x, $"{x} = {aText}")
                            : pr.Apply("a1i", S(("ph", $"{body} = {body}"), ("ps", $"{x} = {aText}")), pr.Apply("eqid", S(("A", body))));
                        Proof r = _d.Syl(_d.Jca(m.P, aIn), pr.Apply("fvixp", S(("F", fText), ("x", x), ("A", dom), ("B", body), ("C", aText), ("D", inst)), sub));
                        return new Typed(r, inst, _ops.Instantiate(pi.Body, [a]));
                    }
                case "co" when pr.Render(n.Children[2]) == "^m" && pi is { IsPi: true }:
                    {
                        string cod = pr.Render(n.Children[0]), dom = pr.Render(n.Children[1]);
                        Proof aIn = Check(c, a, pi.Domain, dom);
                        Proof fn = _d.Syl(m.P, pr.Apply("elmapi", S(("A", fText), ("B", cod), ("C", dom))));
                        Proof r = pr.Apply("ffvelcdmd", S(("ph", c.Ph), ("F", fText), ("A", dom), ("B", cod), ("C", aText)), fn, aIn);
                        return new Typed(r, cod, _ops.Instantiate(pi.Body, [a]));
                    }
                case "cif" when pi is { IsPi: true } && n.Children[0].Rule.Label == "wral":
                    {
                        // A proof of a Π-proposition, applied: rspcdv on its A. x e. D (/) e. B.
                        (Proof r, string inst) = TextApplyProp(c.Ph, m.P, m.Ty, aText, dom => Check(c, a, pi.Domain, dom));
                        string ty = inst.StartsWith("(/) e. ", StringComparison.Ordinal) ? inst[7..] : throw new Refused($"expected (/) e. …, got {inst}");
                        return new Typed(r, ty, _ops.Instantiate(pi.Body, [a]));
                    }
            }
            // Not visibly a function type: reduce the Lean type one step and carry the membership along.
            Expr ltyN = WhnfType(c, lty);
            if (ReferenceEquals(ltyN, lty) && ConvStep(c, lty) is not (Expr, Proof))
            {
                throw new Refused($"applying something whose type isn't a function type: {m.Ty}");
            }
            (Expr next, Proof step) = ConvStep(c, lty) ?? throw new Refused($"can't reduce the type {m.Ty}");
            Proof eq = _d.Trans(AlphaTo(c, m.Ty, TrIn(c, lty)), step);
            m = new Typed(pr.Apply("eleqtrd", S(("ph", c.Ph), ("A", fText), ("B", m.Ty), ("C", Rhs(eq))), m.P, eq), Rhs(eq), next);
        }
        throw new Refused("too many conversions applying a function");
    }

    /// <summary>
    /// From ( ph -> (/) e. if ( A. x e. D ψ , 1o , (/) ) ) and the argument's membership in D: ( ph -> ψ[x := a] ),
    /// by lean-prop and rspcdv (renaming the quantifier's variable away from the argument and the hypotheses first).
    /// </summary>
    private (Proof, string) TextApplyProp(string ph, Proof m, string ifText, string aText, Func<string, Proof> aInDom)
    {
        SyntaxTree n = pr.Parse("class", ifText.Split(' ')) ?? throw new Refused($"does not parse: {ifText}");
        if (n.Rule.Label != "cif" || n.Children[0].Rule.Label != "wral")
        {
            throw new Refused($"not a Π-proposition: {ifText}");
        }
        SyntaxTree all = n.Children[0];
        string allText = pr.Render(all);
        string x = pr.Render(all.Children[1]), dom = pr.Render(all.Children[2]), psi = pr.Render(all.Children[0]);
        EnsureTowerLemmas();
        Proof holds = _d.Syl(m, Bi1(ApplyId("lean-prop", S(("ph", allText)))));
        if (aText.Split(' ').Contains(x) || ph.Split(' ').Contains(x))
        {
            string y = FreshFor(aText, psi, dom, ph);
            string psiY = SubstFree(psi, x, y);
            string all2 = $"A. {y} e. {dom} {psiY}";
            Proof ren = dom.Split(' ').Any(tok => tok == x || tok == y)
                ? pr.Apply("mptru", S(("ph", $"( {allText} <-> {all2} )")), Alpha("wff", allText, all2)!.Value)
                : pr.Apply("cbvralvw", S(("x", x), ("y", y), ("A", dom), ("ph", psi), ("ps", psiY)), SubstEq("wff", psi, x, $"{x} = {y}"));
            holds = pr.Apply("sylib", S(("ph", ph), ("ps", allText), ("ch", all2)), holds, ren);
            (x, psi, allText) = (y, psiY, all2);
        }
        if (BoundIn(psi).Overlaps(ArgVars(aText)))
        {
            string psi2 = RenameApart(psi, ArgVars(aText), ph);
            string all3 = $"A. {x} e. {dom} {psi2}";
            Proof ren = pr.Apply("mptru", S(("ph", $"( {allText} <-> {all3} )")), Alpha("wff", allText, all3)!.Value);
            holds = pr.Apply("sylib", S(("ph", ph), ("ps", allText), ("ch", all3)), holds, ren);
            (psi, allText) = (psi2, all3);
        }
        RefuseCapture(aText, psi, x);
        Proof aIn = aInDom(dom);
        string inst = SubstFree(psi, x, aText);
        Proof sub = pr.Apply("adantl", S(("ph", $"{x} = {aText}"), ("ps", $"( {psi} <-> {inst} )"), ("ch", ph)), SubstEq("wff", psi, x, $"{x} = {aText}"));
        Proof imp = pr.Apply("rspcdv", S(("ph", ph), ("x", x), ("A", aText), ("B", dom), ("ps", psi), ("ch", inst)), aIn, sub);
        return (pr.Apply("mpd", S(("ph", ph), ("ps", allText), ("ch", inst)), holds, imp), inst);
    }

    /// <summary>The Lean type in weak head normal form (Lean side only, for reading off a Π's domain).</summary>
    private Expr WhnfType(PCtx c, Expr ty)
    {
        try
        {
            return _typing.Whnf(ty);
        }
        catch (Typing.Stuck)
        {
            return ty;
        }
    }

    /// <summary>A set variable in none of the given texts.</summary>
    private string FreshFor(params string[] texts)
    {
        var taken = texts.SelectMany(x => x.Split(' ')).ToHashSet();
        return FirstVar(v => !taken.Contains(v));
    }

    private void RefuseCapture(string arg, string body, string x)
    {
        // Substituting arg for x in body must not put a variable of arg under one of body's binders.
        var bound = BoundIn(arg);
        var argVars = arg.Split(' ').Where(s => SetVars.Contains(s) && !bound.Contains(s)).ToHashSet();
        if (argVars.Count > 0 && body.Split(' ').Contains(x) && BoundIn(body).Any(argVars.Contains))
        {
            throw new Refused($"substituting {arg} for {x} would capture a variable");
        }
    }

    /// <summary>The set variables a class or formula binds anywhere inside it.</summary>
    private HashSet<string> BoundIn(string text)
    {
        var r = new HashSet<string>();
        SyntaxTree? n = pr.Parse("class", text.Split(' ')) ?? pr.Parse("wff", text.Split(' '));
        void Go(SyntaxTree m)
        {
            if (m.Rule.Kind == 'f' || m.Rule.Label is "cv" or "wel" or "weq")
            {
                return;
            }
            foreach (SyntaxTree k in m.Children)
            {
                if (k.Rule.Kind == 'f' && k.Rule.Expr.Type == "setvar")
                {
                    r.Add(k.Rule.Var!);
                }
                Go(k);
            }
        }
        if (n is not null)
        {
            Go(n);
        }
        return r;
    }

    private Typed LamMem(PCtx c, Binder lam)
    {
        Expr lty = InferIn(c, lam);
        string tyText = TrIn(c, lty);
        string lamText = TrIn(c, lam);
        bool proof = lamText == "(/)";
        SyntaxTree n = pr.Parse("class", tyText.Split(' '))!;
        string x, dom, body;
        if (proof)
        {
            if (n.Rule.Label != "cif" || n.Children[0].Rule.Label != "wral")
            {
                throw new Refused($"a proof λ whose type isn't a Π-proposition: {tyText}");
            }
            SyntaxTree all = n.Children[0];
            x = pr.Render(all.Children[1]);
            dom = pr.Render(all.Children[2]);
            body = pr.Render(all.Children[0]);   // (/) e. B
        }
        else
        {
            SyntaxTree l = pr.Parse("class", lamText.Split(' '))!;
            x = pr.Render(l.Children[0]);
            dom = pr.Render(l.Children[1]);
            body = pr.Render(l.Children[2]);
        }
        if (proof)
        {
            string tyOrig = tyText;
            if (c.Ph.Split(' ').Contains(x) || c.Binders.Contains(x) || dom.Split(' ').Contains(x))
            {
                // ralrimiva needs the binder out of the hypotheses: rename the quantifier's variable.
                string y = FreshFor(c.Ph, tyText, string.Join(' ', c.Binders));
                body = SubstFree(body, x, y);
                x = y;
                tyText = $"if ( A. {x} e. {dom} {body} , 1o , (/) )";
            }
            (PCtx d, Expr fv) = Enter(c, lam.Domain, x, dom);
            Expr inner = _ops.Instantiate(lam.Body, [fv]);
            Expr innerTy = ((Binder)_typing.Whnf(lty)).Body is var bt ? _ops.Instantiate(bt, [fv]) : throw new Refused("no body type");
            string want = body[7..];
            Proof p = Check(d, inner, innerTy, want);
            Proof all = pr.Apply("ralrimiva", S(("ph", c.Ph), ("ps", body), ("x", x), ("A", dom)), p);
            EnsureTowerLemmas();
            string cond = $"A. {x} e. {dom} {body}";
            Proof r = _d.Syl(all, Bi2(ApplyId("lean-prop", S(("ph", cond)))));
            return new Typed(FixMem(c.Ph, r, "(/)", tyOrig), tyOrig, lty);
        }
        Proof r2 = MapMem(c, lamText, lty, tyText, 1, (d2, _, bodyTy, target) => Check(d2, inner2(d2), bodyTy, target));
        return new Typed(r2, tyText, lty);

        Expr inner2(PCtx d2) => _ops.Instantiate(lam.Body, [t.FVar(d2.LastFv)]);
    }

    private Proof Bi2(Proof iff)
    {
        SyntaxTree n = pr.Parse("wff", iff.Proves.Symbols)!;
        return pr.Apply("biimpri", S(("ph", pr.Render(n.Children[0])), ("ps", pr.Render(n.Children[1]))), iff);
    }

    /// <summary>A sort, or a Π-type, as a member of the universe of its sort.</summary>
    private Typed SortMem(PCtx c, Expr s)
    {
        Expr ty = InferIn(c, s);
        string g = TrIn(c, ty);
        return new Typed(UnivMem(c, TrIn(c, s), g), g, ty);
    }

    private Typed PiMem(PCtx c, Binder pi) => SortMem(c, pi);

    private Typed LitMem(PCtx c, NatLit lit) => LitMemImpl(c, lit);

    private Typed ProjMem(PCtx c, Proj p)
    {
        Expr sTy = _typing.Whnf(InferIn(c, p.Struct));
        if (Ops.Spine(sTy, out _) is not Const sc0 || env.Find(sc0.Name) is not { Kind: ConstKind.Inductive })
        {
            // The structure's type may need iota to show (Nat.below at a successor is a PProd).
            sTy = WhnfFull(c, InferIn(c, p.Struct)).Item1;
        }
        if (Ops.Spine(sTy, out List<Expr> ps) is not Const sc || env.Find(sc.Name) is not { Kind: ConstKind.Inductive, Ctors.Length: 1 } ind)
        {
            throw new Refused($"a projection out of something that isn't a structure ({p})");
        }
        string label = ProjLemma(ind, p.Idx);
        var args = new List<(string, Expr, Expr)>();
        List<Expr> doms = PiDomains(ind.Type, ps);
        for (int i = 0; i < ps.Count; i++)
        {
            args.Add((ClassVars[i], ps[i], doms[i]));
        }
        args.Add((ClassVars[ps.Count], p.Struct, sTy));
        Proof r = InstLemma(c, label, args);
        string ty = pr.Render(pr.Parse("wff", _d.Split(r.Proves).X.Split(' '))!.Children[1]);
        return new Typed(r, ty, InferIn(c, p));
    }

    /// <summary>
    /// ( c.Ph -> conclusion ) from a lemma |- ( ( ( U e. … /\ A e. D1 ) /\ … ) -> conclusion ), its class variables
    /// given by Lean terms (with their expected types), its hypotheses proved by typing them.
    /// </summary>
    private Proof InstLemma(PCtx c, string label, List<(string Var, Expr E, Expr Ty)> args)
    {
        Statement st = pr.Database[label];
        var sub = new Dictionary<string, string> { ["U"] = "U" };
        var orig = new Dictionary<string, string> { ["U"] = "U" };
        foreach (var a in args)
        {
            // The lemma may need its own bound variables distinct from this class variable: rename the term's
            // binders apart from them (and come back by alpha-equivalence below).
            string text = TrIn(c, a.E);
            var avoid = st.Distinct.Where(d => d.Item1 == a.Var || d.Item2 == a.Var).Select(d => d.Item1 == a.Var ? d.Item2 : d.Item1)
                .Where(v => SetVars.Contains(v)).ToHashSet();
            orig[a.Var] = text;
            sub[a.Var] = avoid.Count > 0 && text.Split(' ').Any(avoid.Contains) ? RenameApart(text, avoid, c.Ph) : text;
            if (sub[a.Var].Split(' ').Any(avoid.Contains))
            {
                // A free variable of the term is one the lemma binds: use an alpha-variant of the lemma that binds
                // another one instead.
                var clash = sub[a.Var].Split(' ').Where(avoid.Contains).ToHashSet();
                return InstLemma(c, VariantLemma(label, clash, string.Join(' ', args.Select(x => TrIn(c, x.E)))), args);
            }
        }
        foreach (Statement h in st.Hyps.Where(h => h.Kind == 'f'))
        {
            sub.TryAdd(h.Var!, h.Var!);
            orig.TryAdd(h.Var!, h.Var!);
        }
        Proof inst = pr.Apply(label, sub);
        (string ante, _) = _d.Split(inst.Proves);
        var proofs = new List<Proof>();
        (string lante, _) = _d.Split(st.Expr);
        foreach (string h in Conjuncts(lante).Reverse())
        {
            string hi = string.Join(' ', h.Split(' ').Select(tok => sub.TryGetValue(tok, out string? v) && pr.Parse("class", [tok]) is { Rule.Kind: 'f' } ? v : tok));
            string v0 = h.Split(' ')[0];
            var arg = args.FirstOrDefault(a => a.Var == v0);
            if (h == UHyp || arg.E is null)
            {
                proofs.Add(HypIn(c, hi));
                continue;
            }
            string dom = hi[(sub[v0].Length + 4)..];
            Proof chk = Check(c, arg.E, arg.Ty, dom);
            if (sub[v0] != orig[v0])
            {
                chk = pr.Apply("eqeltrrd", S(("ph", c.Ph), ("A", orig[v0]), ("B", sub[v0]), ("C", dom)), AlphaIn(c.Ph, orig[v0], sub[v0]), chk);
            }
            proofs.Add(chk);
        }
        Proof all = proofs.Skip(1).Aggregate(proofs[0], (acc, q) => _d.Jca(acc, q));
        if (_d.Split(all.Proves).X != ante)
        {
            throw new Refused($"{label}'s hypotheses came out as {_d.Split(all.Proves).X}, not {ante}");
        }
        Proof r = _d.Syl(all, inst);
        if (sub.Any(kv => orig[kv.Key] != kv.Value))
        {
            // Back to the terms as given.
            (_, string lconcl) = _d.Split(st.Expr);
            string concl = _d.Split(r.Proves).X;
            string want = string.Join(' ', lconcl.Split(' ').Select(tok => orig.TryGetValue(tok, out string? v) && pr.Parse("class", [tok]) is { Rule.Kind: 'f' } ? v : tok));
            Proof bi = pr.Apply("mptru", S(("ph", $"( {concl} <-> {want} )")), Alpha("wff", concl, want)!.Value);
            r = pr.Apply("sylib", S(("ph", c.Ph), ("ps", concl), ("ch", want)), r, bi);
        }
        return r;
    }

    /// <summary>
    /// An alpha-variant of a lemma whose statement binds none of the given variables (or the ones in avoidText),
    /// proved from the lemma by alpha-equivalence of its hypotheses and conclusion, and written once.
    /// </summary>
    private string VariantLemma(string label, HashSet<string> clash, string avoidText)
    {
        string key = label + "|" + string.Join(' ', clash.OrderBy(v => v, StringComparer.Ordinal));
        if (_variantOf.TryGetValue(key, out string? known) && !pr.Database[known].Expr.Symbols.Any(avoidText.Split(' ').Where(v => SetVars.Contains(v)).Contains))
        {
            return known;
        }
        Statement st = pr.Database[label];
        (string ante, string concl) = _d.Split(st.Expr);
        string ante2 = RenameApart(ante, clash, avoidText, concl), concl2 = RenameApart(concl, clash, avoidText, ante, ante2);
        string vlabel = $"{label}-a{_variants++}";
        _variantOf[key] = vlabel;
        Proof orig = ApplyId(label, new Dictionary<string, string>());
        Proof toAnte = ante2 == ante ? pr.Apply("id", S(("ph", ante)))
            : Bi1(pr.Apply("mptru", S(("ph", $"( {ante2} <-> {ante} )")), Alpha("wff", ante2, ante)!.Value));
        Proof p = _d.Syl(toAnte, orig);
        if (concl2 != concl)
        {
            p = _d.Syl(p, Bi1(pr.Apply("mptru", S(("ph", $"( {concl} <-> {concl2} )")), Alpha("wff", concl, concl2)!.Value)));
        }
        EmitLemma(vlabel, $"{label} with its bound variables renamed.", p);
        return vlabel;
    }

    private int _variants;
    private readonly Dictionary<string, string> _variantOf = new();

    /// <summary>
    /// lean-proj-S-i: field i of a member of the structure S is in its field's type,
    /// |- ( ( ( U e. lean.-tower /\ A e. D1 ) … /\ X e. ⟦S A …⟧ ) -> field_i ( X ) e. T_i ), by eliun down the
    /// structure's set to X = its tuple (elsni), and the field's hypothesis there.
    /// </summary>
    private string ProjLemma(ConstInfo ind, int i)
    {
        string label = $"lean-proj-{LabelPart($"{ind.Name}")}-{i}";
        if (Has(label))
        {
            return label;
        }
        Define(ind.Name);
        ConstInfo ctor = env.Find(ind.Ctors[0])!;
        string itok = Token(ind.Name)!, ctok = Token(ctor.Name)!;
        int np = ind.NumParams, nf = ctor.NumFields;
        var ps = ClassVars.Take(np).ToList();
        string x = ClassVars[np];
        List<string> pdoms = Domains(itok, ps, np);
        string iapp = ps.Aggregate($"( {itok} ` U )", (acc, a) => $"( {acc} ` {a} )");
        string small = Conj(new[] { UHyp }.Concat(ps.Select((a, k) => $"{a} e. {pdoms[k]}")).Append($"{x} e. {iapp}"));
        (Proof eqT, _, _) = Unfold(small, itok, ps, (k, dom) => Hyp(small, $"{ps[k]} e. {dom}") ?? throw new Refused($"no hypothesis {ps[k]} e. {dom}"));
        string set = Rhs(eqT);
        Proof xIn = pr.Apply("eleqtrd", S(("ph", small), ("A", x), ("B", iapp), ("C", set)), Hyp(small, $"{x} e. {iapp}")!.Value, eqT);
        var fieldOf = Enumerable.Range(0, nf).Select(j => Field($"( 2nd ` {x} )", j)).ToList();
        List<string> cdoms = Domains(ctok, ps.Concat(fieldOf).ToList(), np + nf);
        string goalTy = cdoms[np + i];
        string goal = $"{fieldOf[i]} e. {goalTy}";
        var vars = new List<string>();
        // ( ctx -> ( X e. node -> goal ) ), down the unions (rexlimdva, with X e. … kept out of ctx: it binds the
        // inner unions' variables) to the singleton.
        Proof Descend(string ctx, string node)
        {
            SyntaxTree n = pr.Parse("class", node.Split(' '))!;
            if (n.Rule.Label == "ciun")
            {
                string a = pr.Render(n.Children[0]), dom = pr.Render(n.Children[1]), body = pr.Render(n.Children[2]);
                if (ctx.Split(' ').Contains(a))
                {
                    throw new Refused($"{ind.Name}'s field variable {a} occurs in the hypotheses");
                }
                vars.Add(a);
                string ctx2 = $"( {ctx} /\\ {a} e. {dom} )";
                Proof inner = Descend(ctx2, body);
                Proof lim = pr.Apply("rexlimdva", S(("ph", ctx), ("x", a), ("A", dom), ("ps", $"{x} e. {body}"), ("ch", goal)), inner);
                return pr.Apply("biimtrid", S(("ph", $"{x} e. {node}"), ("ps", $"E. {a} e. {dom} {x} e. {body}"), ("ch", ctx), ("th", goal)),
                    pr.Apply("eliun", S(("A", x), ("x", a), ("B", dom), ("C", body))), lim);
            }
            if (n.Rule.Label != "csn")
            {
                throw new Refused($"{ind.Name}'s set isn't unions of a singleton: {node}");
            }
            string tuple = pr.Render(n.Children[0]);
            string ctx3 = $"( {ctx} /\\ {x} e. {node} )";
            Proof isTuple = _d.Syl(Hyp(ctx3, $"{x} e. {node}")!.Value, pr.Apply("elsni", S(("A", x), ("B", tuple))));
            // field_j ( X ) = a_j for each j, by X = tuple and the simplifier.
            Proof FieldIs(int j)
            {
                Proof cong = _d.Congruence("class", Field("( 2nd ` Z )", j), "Z", isTuple);
                return Simp(ctx3, Rhs(cong)) is Proof sp ? _d.Trans(cong, sp) : cong;
            }
            string ai = vars[i];
            string aDom = Conjuncts(ctx3).First(h => h.StartsWith($"{ai} e. ", StringComparison.Ordinal))[(ai.Length + 4)..];
            Proof aIn = Hyp(ctx3, $"{ai} e. {aDom}")!.Value;
            // The field's type in terms of the a_j, rewritten to the fields of X.
            Proof tyEq = _d.Refl(ctx3, aDom);
            for (int j = 0; j < i; j++)
            {
                if (Rhs(tyEq).Split(' ').Contains(vars[j]))
                {
                    tyEq = _d.Trans(tyEq, _d.Congruence("class", Subst(Rhs(tyEq), vars[j], "Z"), "Z", _d.Symm(FieldIs(j))));
                }
            }
            if (Rhs(tyEq) != goalTy)
            {
                throw new Refused($"{ind.Name}'s field {i} type came out as {Rhs(tyEq)}, not {goalTy}");
            }
            Proof fi = FieldIs(i);
            Proof inA = pr.Apply("eqeltrd", S(("ph", ctx3), ("A", fieldOf[i]), ("B", ai), ("C", aDom)), fi, aIn);
            Proof done = pr.Apply("eleqtrd", S(("ph", ctx3), ("A", fieldOf[i]), ("B", aDom), ("C", goalTy)), inA, tyEq);
            return pr.Apply("ex", S(("ph", ctx), ("ps", $"{x} e. {node}"), ("ch", goal)), done);
        }
        // The set is the tag <. (/) , … >. over the fields: one constructor.
        Proof r = pr.Apply("mpd", S(("ph", small), ("ps", $"{x} e. {set}"), ("ch", goal)), xIn, Descend(small, set));
        EmitLemma(label, $"Field {i} of a member of the structure {ind.Name} is in its type.", r);
        return label;
    }


    // ---- maps and Π-propositions, binder by binder ---------------------------------------------------------------

    /// <summary>
    /// ( c.Ph -> map e. ty ) for a map of depth nested binders and a Π-type of the same shape (X_ or ^m at each level):
    /// enter each binder, prove the body's membership with inner, and close with ralrimiva and mptelixpg or fmpt.
    /// </summary>
    private Proof MapMem(PCtx c, string map, Expr piLean, string ty, int depth, Func<PCtx, string, Expr, string, Proof> inner)
    {
        if (depth == 0)
        {
            return inner(c, map, piLean, ty);
        }
        SyntaxTree l = pr.Parse("class", map.Split(' ')) ?? throw new Refused($"does not parse: {map}");
        SyntaxTree n = pr.Parse("class", ty.Split(' ')) ?? throw new Refused($"does not parse: {ty}");
        if (l.Rule.Label != "cmpt")
        {
            throw new Refused($"expected a map, got {map}");
        }
        string x = pr.Render(l.Children[0]), dom = pr.Render(l.Children[1]), body = pr.Render(l.Children[2]);
        bool clash = n.Rule.Label == "cixp"
            ? pr.Render(n.Children[1]).Split(' ').Contains(x) || BoundIn(pr.Render(n.Children[2])).Contains(x)
            : ty.Split(' ').Contains(x);
        if (clash || c.Ph.Split(' ').Contains(x) || c.Binders.Contains(x) || dom.Split(' ').Contains(x))
        {
            // ralrimiva needs the binder out of the hypotheses: rename the map's variable first.
            string y = FreshFor(c.Ph, map, ty, string.Join(' ', c.Binders));
            string map2 = $"( {y} e. {dom} |-> {SubstFree(body, x, y)} )";
            Proof in2 = MapMem(c, map2, piLean, ty, depth, inner);
            return pr.Apply("eqeltrd", S(("ph", c.Ph), ("A", map), ("B", map2), ("C", ty)), AlphaIn(c.Ph, map, map2), in2);
        }
        // A type whose domain is the map's up to bound names: rewrite it to the map's first.
        int di = n.Rule.Label == "cixp" ? 1 : n.Rule.Label == "co" ? 1 : -1;
        if (di >= 0 && pr.Render(n.Children[di]) != dom)
        {
            string ty2 = n.Rule.Label == "cixp" ? $"X_ {pr.Render(n.Children[0])} e. {dom} {pr.Render(n.Children[2])}" : $"( {pr.Render(n.Children[0])} {pr.Render(n.Children[2])} {dom} )";
            Proof eq = AlphaIn(c.Ph, ty, ty2);
            Proof inner2 = MapMem(c, map, piLean, ty2, depth, inner);
            return pr.Apply("eleqtrrd", S(("ph", c.Ph), ("A", map), ("B", ty2), ("C", ty)), inner2, eq);
        }
        string tyBody;
        bool dependent = n.Rule.Label == "cixp";
        if (dependent)
        {
            if (pr.Render(n.Children[1]) != dom)
            {
                throw new Refused($"a map's domain {dom} differs from its type's {pr.Render(n.Children[1])}");
            }
            string px = pr.Render(n.Children[0]);
            RefuseCapture(x, pr.Render(n.Children[2]), px);
            tyBody = Subst(pr.Render(n.Children[2]), px, x);
        }
        else if (n.Rule.Label == "co" && pr.Render(n.Children[2]) == "^m" && pr.Render(n.Children[1]) == dom)
        {
            tyBody = pr.Render(n.Children[0]);
        }
        else
        {
            throw new Refused($"a map whose type isn't a matching function type: {map} in {ty}");
        }
        var pi = _typing.Whnf(piLean) as Binder ?? throw new Refused("a map whose Lean type isn't a Π");
        (PCtx d, Expr fv) = Enter(c, pi.Domain, x, dom);
        Proof q = FixMem(d.Ph, MapMem(d, body, _ops.Instantiate(pi.Body, [fv]), tyBody, depth - 1, inner), body, tyBody);
        Proof ral = pr.Apply("ralrimiva", S(("ph", c.Ph), ("ps", $"{body} e. {tyBody}"), ("x", x), ("A", dom)), q);
        if (dependent)
        {
            Proof bi = _d.Syl(Exists(c.Ph, dom), pr.Apply("mptelixpg", S(("x", x), ("I", dom), ("J", body), ("K", tyBody), ("V", "_V"))));
            string tyX = $"X_ {x} e. {dom} {tyBody}";
            Proof inX = pr.Apply("mpbird", S(("ph", c.Ph), ("ps", $"{map} e. {tyX}"), ("ch", $"A. {x} e. {dom} {body} e. {tyBody}")), ral, bi);
            return tyX == ty ? inX : pr.Apply("eleqtrd", S(("ph", c.Ph), ("A", map), ("B", tyX), ("C", ty)), inX, AlphaIn(c.Ph, tyX, ty));
        }
        Proof fmap = pr.Apply("fmpt", S(("x", x), ("A", dom), ("C", body), ("B", tyBody), ("F", map)), pr.Apply("eqid", S(("A", map))));
        Proof fn = pr.Apply("sylib", S(("ph", c.Ph), ("ps", $"A. {x} e. {dom} {body} e. {tyBody}"), ("ch", $"{map} : {dom} --> {tyBody}")), ral, fmap);
        Proof bi2 = pr.Apply("elmapd", S(("ph", c.Ph), ("A", tyBody), ("B", dom), ("C", map), ("V", "_V"), ("W", "_V")), Exists(c.Ph, tyBody), Exists(c.Ph, dom));
        return pr.Apply("mpbird", S(("ph", c.Ph), ("ps", $"{map} e. {ty}"), ("ch", $"{map} : {dom} --> {tyBody}")), fn, bi2);
    }

    /// <summary>From ( ph -> E e. T ): ( ph -> e e. t ) for e, t alpha-equivalent to E, T.</summary>
    private Proof FixMem(string ph, Proof q, string e, string ty)
    {
        SyntaxTree n = pr.Parse("wff", _d.Split(q.Proves).X.Split(' '))!;
        string e0 = pr.Render(n.Children[0]), t0 = pr.Render(n.Children[1]);
        if (e0 != e)
        {
            q = pr.Apply("eqeltrd", S(("ph", ph), ("A", e), ("B", e0), ("C", t0)), AlphaIn(ph, e, e0), q);
        }
        if (t0 != ty)
        {
            q = pr.Apply("eleqtrd", S(("ph", ph), ("A", e), ("B", t0), ("C", ty)), q, AlphaIn(ph, t0, ty));
        }
        return q;
    }

    /// <summary>( c.Ph -> (/) e. ⟦ty⟧ ) for a Π-proposition ty: enter its binders, prove the body with inner, close them.</summary>
    private Proof IntroPiProp(PCtx c, Expr ty, Func<PCtx, Expr, Proof> inner)
    {
        string tyText = TrIn(c, ty);
        SyntaxTree n = pr.Parse("class", tyText.Split(' '))!;
        if (n.Rule.Label != "cif" || n.Children[0].Rule.Label != "wral")
        {
            return inner(c, ty);
        }
        SyntaxTree all = n.Children[0];
        string x = pr.Render(all.Children[1]), dom = pr.Render(all.Children[2]), psi = pr.Render(all.Children[0]);
        string allText = pr.Render(all);
        if (c.Ph.Split(' ').Contains(x) || c.Binders.Contains(x) || dom.Split(' ').Contains(x))
        {
            string y = FreshFor(c.Ph, tyText, string.Join(' ', c.Binders));
            psi = SubstFree(psi, x, y);
            x = y;
            allText = $"A. {x} e. {dom} {psi}";
        }
        var pi = (Binder)_typing.Whnf(ty);
        (PCtx d, Expr fv) = Enter(c, pi.Domain, x, dom);
        Expr body = _ops.Instantiate(pi.Body, [fv]);
        Proof q = IntroPiProp(d, body, inner);
        if (_d.Split(q.Proves).X != psi)
        {
            q = pr.Apply("eleqtrd", S(("ph", d.Ph), ("A", "(/)"), ("B", _d.Split(q.Proves).X[7..]), ("C", psi[7..])), q, AlphaTo(d, _d.Split(q.Proves).X[7..], psi[7..]));
        }
        Proof ral = pr.Apply("ralrimiva", S(("ph", c.Ph), ("ps", psi), ("x", x), ("A", dom)), q);
        EnsureTowerLemmas();
        Proof r = _d.Syl(ral, Bi2(ApplyId("lean-prop", S(("ph", allText)))));
        return FixMem(c.Ph, r, "(/)", tyText);
    }

    /// <summary>( d.Ph -> (/) e. ⟦I params indices⟧ ) by constructor j of the proposition I, its proof fields in the context.</summary>
    private Proof HoldsCtor(PCtx d, Expr body, ConstInfo ind, int j)
    {
        Expr head = Ops.Spine(body, out List<Expr> args);
        if (head is not Const ic || !ReferenceEquals(ic.Name, ind.Name))
        {
            throw new Refused($"a constructor of {ind.Name} whose type isn't {ind.Name}");
        }
        string tok = Token(ind.Name)!;
        List<Expr> doms = PiDomains(ind.Type, args);
        var texts = args.Select(a => TrIn(d, a)).ToList();
        (Proof eqT, _, _) = Unfold(d.Ph, tok, texts, (i, dom) => Check(d, args[i], doms[i], dom));
        string iff = Rhs(eqT);
        SyntaxTree n = pr.Parse("class", iff.Split(' '))!;
        if (n.Rule.Label != "cif")
        {
            throw new Refused($"{ind.Name} doesn't unfold to a proposition: {iff}");
        }
        string cond = pr.Render(n.Children[0]);
        // The proof fields' propositions hold: (/) e. P for each, from the context.
        var need = d.Mems.Where(kv => d.Vars.TryGetValue(kv.Key, out string? v) && v == "(/)").Select(kv => kv.Value).ToList();
        var facts = need.Select(m => _d.Split(m.P.Proves).X).Distinct().ToList();
        Proof holds;
        if (facts.Count == 0)
        {
            holds = _d.Lift(d.Ph, pr.Apply("mptru", S(("ph", cond)), ProveCase("T.", cond, j, ind.Ctors.Length)));
        }
        else
        {
            string ph2 = Conj(facts);
            Proof Fact(string f) => need.First(m => _d.Split(m.P.Proves).X == f).P;
            Proof all = facts.Skip(1).Aggregate(Fact(facts[0]), (acc, f) => _d.Jca(acc, Fact(f)));
            holds = _d.Syl(all, ProveCase(ph2, cond, j, ind.Ctors.Length));
        }
        Proof isOne = pr.Apply("iftrued", S(("ph", d.Ph), ("ch", cond), ("A", "1o"), ("B", "(/)")), holds);
        Proof toOne = _d.Trans(eqT, isOne);
        Proof inOne = _d.Lift(d.Ph, pr.Apply("0lt1o", S()));
        Proof bi = pr.Apply("eleq2d", S(("ph", d.Ph), ("A", Lhs(eqT)), ("B", "1o"), ("C", "(/)")), toOne);
        return pr.Apply("mpbird", S(("ph", d.Ph), ("ps", $"(/) e. {Lhs(eqT)}"), ("ch", "(/) e. 1o")), inOne, bi);
    }

    /// <summary>The domains of a Π-type's binders, each instantiated with the arguments before it.</summary>
    private List<Expr> PiDomains(Expr ty, List<Expr> args)
    {
        var r = new List<Expr>();
        foreach (Expr a in args)
        {
            var pi = _typing.Whnf(ty) as Binder ?? throw new Refused("more arguments than binders");
            r.Add(pi.Domain);
            ty = _ops.Instantiate(pi.Body, [a]);
        }
        return r;
    }

    private (Proof TagIn, List<string> Extra)? _ctorIn;

    /// <summary>
    /// lean-in-c: a constructor's tagged tuple is in its type, |- ( ( ( U e. lean.-tower /\ A e. D1 ) … ) -> tag e. ⟦I A …⟧ ),
    /// with the parameters and fields as class variables. For a recursive type, the model's computation-rule proof
    /// proves it on the way (step 1 of RecursiveIota).
    /// </summary>
    private string CtorInLemma(ConstInfo ctor)
    {
        string label = $"lean-in-{LabelPart($"{ctor.Name}")}";
        if (Has(label))
        {
            return label;
        }
        ConstInfo ind = env.Find(ctor.Induct!)!;
        string itok = Token(ind.Name)!, ctok = Token(ctor.Name)!;
        Proof tagIn;
        if (_recursive.ContainsKey(itok))
        {
            _ctorIn = null;
            Iota(ctor.Name);
            tagIn = _ctorIn?.TagIn ?? throw new Refused($"no membership proof for {ctor.Name}");
        }
        else
        {
            int np = ind.NumParams, nf = ctor.NumFields;
            var ps = ClassVars.Take(np).ToList();
            var fields = ClassVars.Skip(np).Take(nf).ToList();
            var ctorArgs = ps.Concat(fields).ToList();
            List<string> cdoms = Domains(ctok, ctorArgs, np + nf);
            string small = Conj(new[] { UHyp }.Concat(ctorArgs.Select((a, i) => $"{a} e. {cdoms[i]}")));
            Proof Pick(int _, string h) => Hyp(small, h) ?? throw new Refused($"no hypothesis {h}");
            (Proof eqV, _, _) = Unfold(small, ctok, ctorArgs, (i, dom) => Pick(i, $"{ctorArgs[i]} e. {dom}"));
            (Proof eqT, _, _) = Unfold(small, itok, ps, (i, dom) => Pick(i, $"{ps[i]} e. {dom}"));
            int j = Array.FindIndex(ind.Ctors, x => ReferenceEquals(x, ctor.Name));
            Proof inSet = MemberUnion(small, Rhs(eqV), Rhs(eqT), ind.Ctors.Length, j, fields, Pick);
            tagIn = pr.Apply("eleqtrrd", S(("ph", small), ("A", Rhs(eqV)), ("B", Rhs(eqT)), ("C", Lhs(eqT))), inSet, eqT);
        }
        EmitLemma(label, $"The value of the constructor {ctor.Name} is in its type.", tagIn);
        return label;
    }

    /// <summary>
    /// ( d.Ph -> body e. target ) from a lemma |- ( ( ( U e. … /\ A e. D1 ) /\ … ) -> X e. Y ): its class variables
    /// matched against body and target, its hypotheses discharged from the context.
    /// </summary>
    private Proof UseLemma(PCtx d, string label, string body, string target)
    {
        Statement st = pr.Database[label];
        (string ante, string concl) = _d.Split(st.Expr);
        var hyps = Conjuncts(ante).Reverse().ToList();
        var sub = new Dictionary<string, string> { ["U"] = "U" };
        // Match the conclusion's class variables against body e. target.
        if (!Match(concl, $"{body} e. {target}", sub))
        {
            throw new Refused($"{label} doesn't match {body} e. {target}");
        }
        foreach (Statement h in st.Hyps.Where(h => h.Kind == 'f'))
        {
            sub.TryAdd(h.Var!, h.Var!);
        }
        Proof inst = pr.Apply(label, sub);
        var proofs = new List<Proof>();
        foreach (string h in hyps)
        {
            string hi = string.Join(' ', h.Split(' ').Select(tok => sub.TryGetValue(tok, out string? v) && pr.Parse("class", [tok]) is { Rule.Kind: 'f' } ? v : tok));
            proofs.Add(HypIn(d, hi));
        }
        Proof all = proofs.Skip(1).Aggregate(proofs[0], (acc, q) => _d.Jca(acc, q));
        return _d.Syl(all, inst);
    }

    /// <summary>( d.Ph -> h ) for a hypothesis the context has: a conjunct, or a local's membership.</summary>
    private Proof HypIn(PCtx d, string h)
    {
        if (Hyp(d.Ph, h) is Proof p)
        {
            return p;
        }
        foreach (var m in d.Mems.Values)
        {
            if (_d.Split(m.P.Proves).X == h)
            {
                return m.P;
            }
        }
        throw new Refused($"no hypothesis {h}");
    }

    /// <summary>Match a pattern's class variables (single tokens that are class variables) against a text.</summary>
    private bool Match(string pattern, string text, Dictionary<string, string> sub)
    {
        SyntaxTree? p = pr.Parse("wff", pattern.Split(' ')), x = pr.Parse("wff", text.Split(' '));
        return p is not null && x is not null && MatchTree(p, x, sub);
    }

    private bool MatchTree(SyntaxTree p, SyntaxTree x, Dictionary<string, string> sub)
    {
        if (p.Rule.Kind == 'f' && p.Rule.Expr.Type == "class")
        {
            string v = p.Rule.Var!, xs = pr.Render(x);
            if (sub.TryGetValue(v, out string? had))
            {
                return had == xs;
            }
            sub[v] = xs;
            return true;
        }
        if (p.Rule.Kind == 'f')
        {
            return x.Rule.Kind == 'f' && x.Rule.Var == p.Rule.Var;
        }
        return p.Rule.Label == x.Rule.Label && p.Children.Count == x.Children.Count && p.Children.Zip(x.Children).All(z => MatchTree(z.First, z.Second, sub));
    }

    // ---- constants: typed once each, by a lemma ---------------------------------------------------------------

    private readonly Dictionary<Name, (string Label, string Ty)> _constTy = new(ReferenceEqualityComparer.Instance);
    private readonly HashSet<Name> _typing_ = new(ReferenceEqualityComparer.Instance);

    private Typed ConstMem(PCtx c, Const k)
    {
        using var prof = Prof.Time("ConstMem");
        if (env.Find(k.Name) is { Kind: ConstKind.Recursor } rk && rk.LevelParams.Length > 0 && TrIn(c, k) == "(/)")
        {
            // A recursor into Prop: induction (lean-ind-I).
            (string il, string ity) = PropRecLemma(k);
            Proof ir = _d.Syl(Hyp(c.Ph, UHyp) ?? throw new Refused("no universe hypothesis"), ApplyId(il, S(("U", "U"))));
            return new Typed(ir, ity, _ops.InstantiateLevels(rk.Type, rk.LevelParams, k.Levels));
        }
        (string label, string ty) = ConstTyLemma(k.Name);
        Proof inst = ApplyId(label, S(("U", "U")));
        Proof r = _d.Syl(Hyp(c.Ph, UHyp) ?? throw new Refused("no universe hypothesis"), inst);
        ConstInfo ci = env.Find(k.Name)!;
        return new Typed(r, ty, _ops.InstantiateLevels(ci.Type, ci.LevelParams, k.Levels));
    }

    /// <summary>lean-ty-c: |- ( U e. lean.-tower -> ⟦c⟧ e. ⟦type of c⟧ ), proved once.</summary>
    private (string Label, string Ty) ConstTyLemma(Name n)
    {
        if (_constTy.TryGetValue(n, out var done))
        {
            return done;
        }
        if (!_typing_.Add(n))
        {
            throw new Refused($"typing {n} needs itself");
        }
        try
        {
            return ConstTyLemmaCore(n);
        }
        finally
        {
            // Done, or refused: either way no longer in progress (a later theorem may try it again).
            _typing_.Remove(n);
        }
    }

    private (string Label, string Ty) ConstTyLemmaCore(Name n)
    {
        ConstInfo ci = env.Find(n) ?? throw new Refused($"{n} is not in the export");
        EnsureTowerLemmas();
        var c = new PCtx { Ph = UHyp };
        Expr self = t.Const(n, ci.LevelParams.Select(p => t.Param(p)).ToArray());
        string text = TrIn(c, self);
        string ty = TrIn(c, ci.Type);
        Proof p;
        switch (ci.Kind)
        {
            case ConstKind.Definition or ConstKind.Theorem or ConstKind.Opaque when (ci.Value ?? ci.OpaqueValue) is Expr v:
                {
                    Proof inV = Check(c, v, ci.Type, ty);
                    if (text == "(/)")
                    {
                        p = inV;   // a proof: its value's text is (/) too
                    }
                    else
                    {
                        Proof unfold = DeltaEq(c.Ph, Token(n)!);
                        string vText = TrIn(c, v);
                        if (Rhs(unfold) != vText)
                        {
                            throw new Refused($"{n}'s definition reads {Rhs(unfold)}, its value translates to {vText}");
                        }
                        p = pr.Apply("eqeltrd", S(("ph", c.Ph), ("A", text), ("B", vText), ("C", ty)), unfold, inV);
                    }
                    break;
                }
            case ConstKind.Inductive:
                {
                    // A type (or proposition): its sets, at any parameters and indices, are in the universe of its sort.
                    Proof unfold = DeltaEq(c.Ph, Token(n)!);
                    Proof inMap = MapMem(c, Rhs(unfold), ci.Type, ty, ci.NumParams + ci.NumIndices, (d, body, _, target) => UnivMem(d, body, target));
                    p = pr.Apply("eqeltrd", S(("ph", c.Ph), ("A", text), ("B", Rhs(unfold)), ("C", ty)), unfold, inMap);
                    break;
                }
            case ConstKind.Recursor when text != "(/)":
                {
                    // A recursor: at every member of the type, in the motive there (lean-recty-I).
                    Name iname = n is StrName { Value: "rec" } rn ? rn.Prefix : throw new Refused($"{n} isn't a type's recursor");
                    ConstInfo ind = env.Find(iname)!;
                    Define(iname);
                    string rl = RecTyLemma(ind);
                    string rtok = Token(n)!;
                    Proof unfold = DeltaEq(c.Ph, rtok);
                    int nb = ind.NumParams + ci.NumMotives + ci.NumMinors;
                    Proof inMap = MapMem(c, Rhs(unfold), ci.Type, ty, nb + 1, (d, body, bodyLean, target) =>
                    {
                        var vs = d.Binders.TakeLast(nb + 1).ToList();
                        string tv = vs[^1];
                        var others = vs.Take(nb).ToList();
                        (Proof eqB, _, _) = Unfold(d.Ph, rtok, vs, (i, dom) => HypIn(d, $"{vs[i]} e. {dom}"));
                        var sub = new Dictionary<string, string> { ["U"] = "U" };
                        for (int i = 0; i < nb; i++)
                        {
                            sub[ClassVars[i]] = others[i];
                        }
                        Proof li = ApplyId(rl, sub);
                        (string ante, string ss) = _d.Split(li.Proves);
                        var hs = Conjuncts(ante).Reverse().ToList();
                        Proof allH = hs.Skip(1).Aggregate(HypIn(d, hs[0]), (acc, h) => _d.Jca(acc, HypIn(d, h)));
                        Proof sub1 = _d.Syl(allH, li);
                        SyntaxTree sn = pr.Parse("wff", ss.Split(' '))!;
                        string iapp = pr.Render(sn.Children[0]), q = pr.Render(sn.Children[1]);
                        Proof tIn = pr.Apply("sseld", S(("ph", d.Ph), ("A", iapp), ("B", q), ("C", tv)), sub1);
                        Proof tQ = pr.Apply("mpd", S(("ph", d.Ph), ("ps", $"{tv} e. {iapp}"), ("ch", $"{tv} e. {q}")), HypIn(d, $"{tv} e. {iapp}"), tIn);
                        SyntaxTree qn = pr.Parse("class", q.Split(' '))!;
                        string qv = pr.Render(qn.Children[1]), qb = pr.Render(qn.Children[0]);
                        string pt = Subst(qb, qv, tv);
                        Proof subst = _d.Congruence("wff", Subst(qb, qv, "Z"), "Z", pr.Apply("id", S(("ph", $"{qv} = {tv}"))));
                        Proof bi = _d.Syl(Exists(d.Ph, tv), pr.Apply("elabg", S(("x", qv), ("ph", qb), ("ps", pt), ("A", tv), ("V", "_V")), subst));
                        Proof holds = pr.Apply("mpbid", S(("ph", d.Ph), ("ps", $"{tv} e. {q}"), ("ch", pt)), tQ, bi);
                        string folded = Lhs(eqB);
                        if (pt != $"{folded} e. {target}")
                        {
                            throw new Refused($"{n}'s typing came out as {pt}, not {folded} e. {target}");
                        }
                        return pr.Apply("eqeltrrd", S(("ph", d.Ph), ("A", folded), ("B", body), ("C", target)), eqB, holds);
                    });
                    p = pr.Apply("eqeltrd", S(("ph", c.Ph), ("A", text), ("B", Rhs(unfold)), ("C", ty)), unfold, inMap);
                    break;
                }
            case ConstKind.Constructor when text == "(/)":
                {
                    // A constructor of a proposition: under its binders, the proposition holds at its indices.
                    ConstInfo ind = env.Find(ci.Induct!)!;
                    int j = Array.FindIndex(ind.Ctors, x => ReferenceEquals(x, n));
                    p = IntroPiProp(c, ci.Type, (d, body) => HoldsCtor(d, body, ind, j));
                    break;
                }
            case ConstKind.Constructor:
                {
                    // A constructor of a type: its map's body, the tagged tuple, is in the type (lean-in-c).
                    string cin = CtorInLemma(ci);
                    Proof unfold = DeltaEq(c.Ph, Token(n)!);
                    Proof inMap = MapMem(c, Rhs(unfold), ci.Type, ty, ci.NumParams + ci.NumFields, (d, body, _, target) => UseLemma(d, cin, body, target));
                    p = pr.Apply("eqeltrd", S(("ph", c.Ph), ("A", text), ("B", Rhs(unfold)), ("C", ty)), unfold, inMap);
                    break;
                }
            case ConstKind.Axiom when $"{n}" == "propext":
                p = PropextTyping(c, ci.Type);
                break;
            default:
                throw new Refused($"no typing lemma yet for {n} (a {ci.Kind.ToString().ToLowerInvariant()})");
        }
        string label = $"lean-ty-{LabelPart($"{n}")}";
        EmitLemma(label, $"The type of {n} in the model.", p);
        _constTy[n] = (label, ty);
        return (label, ty);
    }

    /// <summary>( ph -> ( lean.c ` U ) = value[u := U] ), by the definition and fvmptd3.</summary>
    private Proof DeltaEq(string ph, string tok)
    {
        Statement dfa = pr.Database["df-" + LabelPart(tok)];
        Proof df = pr.Apply(dfa.Label, dfa.Hyps.Where(h => h.Kind == 'f').ToDictionary(h => h.Var!, h => h.Var!));
        return Beta(ph, df, UniverseVar, UniverseDomain, _values[tok], "U", Hyp(ph, UHyp) ?? throw new Refused("no universe hypothesis"), tok);
    }


    /// <summary>Model.Beta for a body that binds its own variable again inside: substitute only the free occurrences.</summary>
    private Proof BetaShadowed(string ph, Proof fIsMap, string x, string dom, string body, string arg, Proof argIn, string f)
    {
        if (arg.Split(' ').Contains(x))
        {
            string y = FreshFor(arg, body, dom, ph);
            string bodyY = SubstFree(body, x, y);
            Proof ren = pr.Apply("cbvmptv", S(("x", x), ("y", y), ("A", dom), ("B", body), ("C", bodyY)),
                SubstEq("class", body, x, $"{x} = {y}"));
            fIsMap = pr.Apply("eqtri", S(("A", f), ("B", $"( {x} e. {dom} |-> {body} )"), ("C", $"( {y} e. {dom} |-> {bodyY} )")), fIsMap, ren);
            (x, body) = (y, bodyY);
        }
        if (BoundIn(body).Overlaps(ArgVars(arg)))
        {
            string body2 = RenameApart(body, ArgVars(arg), ph, x);
            fIsMap = pr.Apply("eqtri", S(("A", f), ("B", $"( {x} e. {dom} |-> {body} )"), ("C", $"( {x} e. {dom} |-> {body2} )")), fIsMap,
                AlphaClosed($"( {x} e. {dom} |-> {body} )", $"( {x} e. {dom} |-> {body2} )"));
            body = body2;
        }
        string result = SubstFree(body, x, arg);
        string h = $"{x} = {arg}";
        Proof sub = result != body
            ? SubstEq("class", body, x, h)
            : pr.Apply("a1i", S(("ph", $"{body} = {body}"), ("ps", h)), pr.Apply("eqid", S(("A", body))));
        return pr.Apply("fvmptd3", S(("ph", ph), ("x", x), ("A", arg), ("B", body), ("C", result), ("D", dom), ("F", f), ("V", "_V")),
            fIsMap, sub, argIn, Exists(ph, result));
    }

    // ---- conversion: ( ph -> ⟦a⟧ = ⟦b⟧ ) ------------------------------------------------------------------------

    /// <summary>( ph -> at = bt ), where at and bt are a's and b's translations up to the names of bound variables.</summary>
    private Proof ConvText(PCtx c, Expr a, string at, Expr b, string bt)
    {
        using var prof = Prof.Time("ConvText");
        Proof p1 = AlphaTo(c, at, TrIn(c, a));
        // Each conversion the typing asks for gets its own fuel (conversions nest through the typing of binders).
        if (_convDepth == 0)
        {
            _convFuel = 0;
        }
        _convDepth++;
        Proof p2;
        try
        {
            p2 = Conv(c, a, b);
        }
        finally
        {
            _convDepth--;
        }
        Proof p3 = AlphaTo(c, TrIn(c, b), bt);
        return _d.Trans(_d.Trans(p1, p2), p3);
    }

    /// <summary>( ph -> x = y ) for texts equal up to the names of bound variables.</summary>
    private Proof AlphaTo(PCtx c, string x, string y)
    {
        using var prof = Prof.Time("AlphaTo");
        return AlphaIn(c.Ph, x, y);
    }

    private int _convFuel, _convDepth;

    /// <summary>( ph -> ⟦a⟧ = ⟦b⟧ ) for definitionally equal a and b.</summary>
    private Proof Conv(PCtx c, Expr a, Expr b)
    {
        string ta = TrIn(c, a), tb = TrIn(c, b);
        if (ta == tb)
        {
            return _d.Refl(c.Ph, ta);
        }
        if (++_convFuel > 20000)
        {
            throw new Refused("conversion ran out of fuel");
        }
        Debug($"conv #{_convFuel}: {a}  ==  {b}");
        if (TryCongr(c, a, b) is Proof cong)
        {
            return cong;
        }
        if (ConvStep(c, a) is (Expr a2, Proof pa))
        {
            return _d.Trans(pa, Conv(c, a2, b));
        }
        if (ConvStep(c, b) is (Expr b2, Proof pb))
        {
            return _d.Trans(Conv(c, a, b2), _d.Symm(pb));
        }
        // A literal against a constructor: the literal as Nat.zero or Nat.succ.
        if (a is NatLit la && b is not NatLit)
        {
            (Expr ca, Proof pla) = LitToCtor(c, la.Value);
            return _d.Trans(pla, Conv(c, ca, b));
        }
        if (b is NatLit lb && a is not NatLit)
        {
            (Expr cb, Proof plb) = LitToCtor(c, lb.Value);
            return _d.Trans(Conv(c, a, cb), _d.Symm(plb));
        }
        throw new Refused($"can't show {ta} = {tb}");
    }

    /// <summary>Two Π-types: their domains, then their bodies under the binder (ixpeq2dva, or ralbidva for propositions).</summary>
    private Proof? ConvPi(PCtx c, Binder a, Binder b)
    {
        string ta = TrIn(c, a), tb = TrIn(c, b);
        bool prop = ta.StartsWith("if ( A. ", StringComparison.Ordinal);
        if (prop != tb.StartsWith("if ( A. ", StringComparison.Ordinal))
        {
            return null;
        }
        string Dom(string tx)
        {
            SyntaxTree n = pr.Parse("class", tx.Split(' '))!;
            return n.Rule.Label switch
            {
                "cixp" => pr.Render(n.Children[1]),
                "co" => pr.Render(n.Children[1]),
                "cif" => pr.Render(n.Children[0].Children[2]),
                _ => throw new Refused($"not a Π-type: {tx}"),
            };
        }
        string da = Dom(ta), db = Dom(tb);
        Proof pre = _d.Refl(c.Ph, ta);
        if (da != db)
        {
            // The domains first: rewrite a's to b's inside a's translation.
            Proof pd = Conv(c, a.Domain, b.Domain);
            pd = _d.Trans(_d.Trans(AlphaIn(c.Ph, da, Lhs(pd)), pd), AlphaIn(c.Ph, Rhs(pd), db));
            SyntaxTree n = pr.Parse("class", ta.Split(' '))!;
            string holed = n.Rule.Label switch
            {
                "cixp" => $"X_ {pr.Render(n.Children[0])} e. Z {pr.Render(n.Children[2])}",
                "co" => $"( {pr.Render(n.Children[0])} ^m Z )",
                _ => $"if ( A. {pr.Render(n.Children[0].Children[1])} e. Z {pr.Render(n.Children[0].Children[0])} , 1o , (/) )",
            };
            pre = _d.Congruence("class", holed, "Z", pd);
            ta = Rhs(pre);
            da = db;
        }
        string v = FreshFor(c.Ph, ta, tb, string.Join(' ', c.Binders));
        // Once the domains are rewritten, the binder ranges over b's (its text is da now).
        (PCtx d, Expr fv) = Enter(c, Dom(TrIn(c, a)) == da ? a.Domain : b.Domain, v, da);
        Proof pb = Conv(d, _ops.Instantiate(a.Body, [fv]), _ops.Instantiate(b.Body, [fv]));
        string ba = Lhs(pb), bb = Rhs(pb);
        Proof Side(string tx, string body)
        {
            // ( ph -> tx = the X_ (or if A.) form over v )
            string xf = prop ? $"if ( A. {v} e. {da} (/) e. {body} , 1o , (/) )" : $"X_ {v} e. {da} {body}";
            SyntaxTree n = pr.Parse("class", tx.Split(' '))!;
            if (n.Rule.Label == "co")
            {
                Proof k = _d.Syl(_d.Jca(Exists(d.Ph, da) is var _ ? Exists(c.Ph, da) : default, Exists(c.Ph, body)),
                    pr.Apply("ixpconstg", S(("x", v), ("A", da), ("B", body), ("V", "_V"), ("W", "_V"))));
                return _d.Trans(AlphaIn(c.Ph, tx, $"( {body} ^m {da} )"), _d.Symm(k));
            }
            return AlphaIn(c.Ph, tx, xf);
        }
        Proof mid = prop
            ? pr.Apply("ifbid", S(("ph", c.Ph), ("ps", $"A. {v} e. {da} (/) e. {ba}"), ("ch", $"A. {v} e. {da} (/) e. {bb}"), ("A", "1o"), ("B", "(/)")),
                pr.Apply("ralbidva", S(("ph", c.Ph), ("x", v), ("A", da), ("ps", $"(/) e. {ba}"), ("ch", $"(/) e. {bb}")),
                    pr.Apply("eleq2d", S(("ph", d.Ph), ("A", ba), ("B", bb), ("C", "(/)")), pb)))
            : pr.Apply("ixpeq2dva", S(("ph", c.Ph), ("x", v), ("A", da), ("B", ba), ("C", bb)), pb);
        return _d.Trans(pre, _d.Trans(_d.Trans(Side(ta, ba), mid), _d.Symm(Side(tb, bb))));
    }

    /// <summary>Same head and argument count: the arguments pairwise. Null when that doesn't work out.</summary>
    private Proof? TryCongr(PCtx c, Expr a, Expr b)
    {
        if (a is Binder { IsPi: true } pa && b is Binder { IsPi: true } pb)
        {
            try
            {
                return ConvPi(c, pa, pb);
            }
            catch (Refused e)
            {
                Debug($"ConvPi: {e.Message}");
                return null;
            }
        }
        Expr ha = Ops.Spine(a, out List<Expr> xs), hb = Ops.Spine(b, out List<Expr> ys);
        if (ha is Proj pa2 && hb is Proj pb2 && pa2.Idx == pb2.Idx && xs.Count == ys.Count && !IsProofIn(c, a))
        {
            // The same field of convertible structures, at convertible arguments.
            try
            {
                Proof ps = Conv(c, pa2.Struct, pb2.Struct);
                Proof cur0 = _d.Congruence("class", Field("( 2nd ` Z )", pa2.Idx), "Z", ps);
                cur0 = _d.Trans(cur0, AlphaIn(c.Ph, Rhs(cur0), TrIn(c, pb2)));
                for (int i = 0; i < xs.Count; i++)
                {
                    Proof pi = Conv(c, xs[i], ys[i]);
                    cur0 = pr.Apply("fveq12d", S(("ph", c.Ph), ("F", Lhs(cur0)), ("G", Rhs(cur0)), ("A", Lhs(pi)), ("B", Rhs(pi))), cur0, pi);
                }
                return _d.Trans(AlphaIn(c.Ph, TrIn(c, a), Lhs(cur0)), cur0);
            }
            catch (Refused e)
            {
                Debug($"TryCongr (projection): {e.Message}");
                return null;
            }
        }
        bool same = (ha, hb) switch
        {
            (Const p, Const q) => ReferenceEquals(p.Name, q.Name),
            (FVar p, FVar q) => p.Id == q.Id,
            _ => false,
        };
        if (!same || xs.Count != ys.Count || xs.Count == 0)
        {
            return null;
        }
        int saved = _out.Length;
        try
        {
            Proof cur = _d.Refl(c.Ph, TrIn(c, ha));
            Expr ea = ha, eb = ha;
            for (int i = 0; i < xs.Count; i++)
            {
                Proof pi = Conv(c, xs[i], ys[i]);
                string fa = TrIn(c, ea), fb = Rhs(cur);
                string xa = TrIn(c, xs[i]), xb = Rhs(pi);
                cur = pr.Apply("fveq12d", S(("ph", c.Ph), ("F", fa), ("G", fb), ("A", xa), ("B", xb)), cur, pi);
                ea = t.App(ea, xs[i]);
            }
            return cur;
        }
        catch (Refused e)
        {
            Debug($"TryCongr: {e.Message}");
            return null;
        }
    }

    private static readonly bool Debugging = System.Environment.GetEnvironmentVariable("TENET_DEBUG") is not null;

    private static void Debug(string msg)
    {
        if (Debugging)
        {
            Console.Error.WriteLine("[debug] " + (msg.Length > 600 ? msg[..600] + "…" : msg));
        }
    }

    /// <summary>One reduction step of e, with ( ph -> ⟦e⟧ = ⟦e'⟧ ), or null when e is in weak head normal form.</summary>
    private (Expr, Proof)? ConvStep(PCtx c, Expr e)
    {
        using var prof = Prof.Time("ConvStep");
        if (IsProofIn(c, e))
        {
            return null;
        }
        Expr head = Ops.Spine(e, out List<Expr> args);
        switch (head)
        {
            case Let l:
                {
                    Expr r = t.MkApp(_ops.Instantiate(l.Body, [l.Value]), args);
                    return (r, _d.Refl(c.Ph, TrIn(c, e)));
                }
            case Binder { IsPi: false } lam when args.Count > 0:
                {
                    // Beta on the first argument, then the rest by congruence.
                    string lamText = TrIn(c, lam);
                    SyntaxTree n = pr.Parse("class", lamText.Split(' '))!;
                    if (n.Rule.Label != "cmpt")
                    {
                        throw new Refused($"a λ that doesn't translate to a map: {lamText}");
                    }
                    string x = pr.Render(n.Children[0]), dom = pr.Render(n.Children[1]), body = pr.Render(n.Children[2]);
                    string arg = TrIn(c, args[0]);
                    RefuseCapture(arg, body, x);
                    Proof argIn = Check(c, args[0], lam.Domain, dom);
                    Proof beta = Beta(c.Ph, pr.Apply("eqid", S(("A", lamText))), x, dom, body, arg, argIn, lamText);
                    Expr r = t.MkApp(_ops.Instantiate(lam.Body, [args[0]]), args.Skip(1));
                    return (r, Reconcile(c, AppCong(c, beta, args.Skip(1)), r));
                }
            case Const k when env.Find(k.Name) is { Kind: ConstKind.Recursor } rci && args.Count > rci.MajorIdx:
                return IotaStep(c, e, k, rci, args);
            case Proj pj:
                return ProjStep(c, pj, args);
            case Const k when env.Find(k.Name) is { Kind: ConstKind.Definition or ConstKind.Opaque } ci && (ci.Value ?? ci.OpaqueValue) is Expr v:
                {
                    Define(k.Name);
                    Proof delta = DeltaEq(c.Ph, Token(k.Name)!);
                    Expr r = t.MkApp(_ops.InstantiateLevels(v, ci.LevelParams, k.Levels), args);
                    return (r, Reconcile(c, AppCong(c, delta, args), r));
                }
        }
        return null;
    }

    /// <summary>From ( ph -> F = G ): ( ph -> ( F ` a1 ) … = ( G ` a1 ) … ).</summary>
    private Proof AppCong(PCtx c, Proof fg, IEnumerable<Expr> args)
    {
        Proof cur = fg;
        foreach (Expr a in args)
        {
            cur = pr.Apply("fveq1d", S(("ph", c.Ph), ("A", TrIn(c, a)), ("F", Lhs(cur)), ("G", Rhs(cur))), cur);
        }
        return cur;
    }

    /// <summary>A step's result, brought to the translation of the Lean reduct (up to bound names).</summary>
    private Proof Reconcile(PCtx c, Proof step, Expr reduct) => _d.Trans(step, AlphaTo(c, Rhs(step), TrIn(c, reduct)));

    // ---- theorems ----------------------------------------------------------------------------------------------

    /// <summary>The theorem's statement with its leading binders opened as hypotheses, and its proof.</summary>
    public (MmExpr Statement, List<string> Proof) ProveTheorem(ConstInfo thm)
    {
        _typing.Reduce = LeanWhnf;
        EnsureTowerLemmas();
        var c = new PCtx { Ph = UHyp };
        Expr ty = thm.Type, proof = thm.Value!;
        int k = 0;
        var hyps = new List<string> { UHyp };
        var pending = new List<(ulong Id, string Hyp)>();
        while (ty is Binder { IsPi: true } b)
        {
            Expr fv = t.FVar(_fresh++);
            ulong id = ((FVar)fv).Id;
            string dom = TrIn(c, b.Domain);
            c.Types[id] = b.Domain;
            bool isProof = _typing.IsProposition(b.Domain, c.Types) == true;
            string text = isProof ? "(/)" : ClassVars[k++];
            c.Vars[id] = text;
            hyps.Add($"{text} e. {dom}");
            pending.Add((id, $"{text} e. {dom}"));
            c.Ph = Conj(hyps);
            ty = _ops.Instantiate(b.Body, [fv]);
            proof = proof is Binder { IsPi: false } lam ? _ops.Instantiate(lam.Body, [fv]) : t.App(proof, fv);
        }
        foreach (var (id, h) in pending)
        {
            c.Mems[id] = (Hyp(c.Ph, h)!.Value, h[(h.IndexOf(" e. ", StringComparison.Ordinal) + 4)..]);
        }
        string goal = TrIn(c, ty);
        Proof p = Check(c, proof, ty, goal);
        return (p.Proves, p.Proof);
    }
}
