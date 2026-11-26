using TenetZfc.Metamath;
using Proof = (System.Collections.Generic.List<string> Proof, TenetZfc.Metamath.Expr Proves);

namespace TenetZfc;

/// <summary>
/// The type of a recursor (docs/milestone3.md, "Theorems through the model"): I.rec params motive minors t is in
/// motive t, for every t in I params. For a recursive type that is induction over its stages: with
/// Q = { t | ( R ` t ) e. ( B ` t ) }, R the recursor at everything but the major premise and B the motive, each stage
/// is a subset of Q (finds2). The empty one is; the next one is the last one with each constructor's tuples over it,
/// and a tuple is in Q by the constructor's computation rule, its minor premise's type, and the last stage for its
/// recursive fields. For a type that isn't recursive, the type is the constructors' tuples alone.
/// </summary>
public sealed partial class Model
{
    /// <summary>lean-iota-c: the computation rule of a constructor, written into the output once.</summary>
    private string IotaLemma(Name ctor)
    {
        string label = $"lean-iota-{LabelPart($"{ctor}")}";
        if (!Has(label))
        {
            var (stmt, proof, _) = Iota(ctor);
            EmitLemma(label, $"The computation rule of the recursor on {ctor}.", (proof, stmt));
        }
        return label;
    }

    /// <summary>
    /// lean-recty-I: |- ( ( U e. lean.-tower /\ params, motive, minors in their domains ) -> ⟦I params⟧ C_ Q ),
    /// Q = { t | ( R ` t ) e. ( B ` t ) }.
    /// </summary>
    private string RecTyLemma(ConstInfo ind)
    {
        string label = $"lean-recty-{LabelPart($"{ind.Name}")}";
        if (Has(label))
        {
            return label;
        }
        ConstInfo rec = env.Find(t.Str(ind.Name, "rec")) ?? throw new Refused($"{ind.Name}.rec is not in the export");
        if (rec.NumMotives != 1 || ind.NumIndices > 0)
        {
            throw new Refused($"{ind.Name}: typing a recursor with indices or several motives isn't supported yet");
        }
        string itok = Token(ind.Name)!, rtok = Token(rec.Name)!;
        int np = ind.NumParams, nrec = np + rec.NumMotives + rec.NumMinors;
        var recArgs = ClassVars.Take(nrec).ToList();
        var ps = recArgs.Take(np).ToList();
        string motive = recArgs[np];
        List<string> rdoms = Domains(rtok, recArgs, nrec);
        string ph = Conj(new[] { UHyp }.Concat(recArgs.Select((a, i) => $"{a} e. {rdoms[i]}")));
        string r = recArgs.Aggregate($"( {rtok} ` U )", (acc, a) => $"( {acc} ` {a} )");
        (Proof eqT, _, _) = Unfold(ph, itok, ps, (i, dom) => Hyp(ph, $"{ps[i]} e. {dom}") ?? throw new Refused($"no hypothesis {ps[i]} e. {dom}"));
        string iapp = Lhs(eqT), set = Rhs(eqT);
        // The quantified variables are taken from the end of the alphabet, away from the definitions' own.
        var taken = new HashSet<string>((ph + " " + set + " " + r).Split(' '));
        string Pick() { string v = Enumerable.Reverse(SetVars).First(x => !taken.Contains(x)); taken.Add(v); return v; }
        string tv = Pick();
        string P(string at) => $"( {r} ` {at} ) e. ( {motive} ` {at} )";
        string q = $"{{ {tv} | {P(tv)} }}";

        // ( ctx -> P ( tag ) ), for constructor j's tuple over the fields, its recursive fields in S C_ Q.
        Proof CtorStep(string ctx, int j, List<string> fields, string tag, string s, Func<string, Proof> rInI, Func<string, Proof> rInS)
        {
            ConstInfo ctor = env.Find(ind.Ctors[j])!;
            string ctok = Token(ctor.Name)!;
            List<int> rf = _recursive.TryGetValue(itok, out RecursiveInfo? info) ? info.RecFields[j] : [];
            var ctorArgs = ps.Concat(fields).ToList();
            List<string> cdoms = Domains(ctok, ctorArgs, np + fields.Count);
            Proof FieldIn(int k)
            {
                if (rf.Contains(k))
                {
                    return rInI(fields[k]);
                }
                string h = Conjuncts(ctx).FirstOrDefault(c => c.StartsWith($"{fields[k]} e. ", StringComparison.Ordinal)) ?? throw new Refused($"no hypothesis for {fields[k]}");
                Proof p = Hyp(ctx, h)!.Value;
                string have = h[(fields[k].Length + 4)..], want = cdoms[np + k];
                return have == want ? p : pr.Apply("eleqtrd", S(("ph", ctx), ("A", fields[k]), ("B", have), ("C", want)), p, AlphaIn(ctx, have, want));
            }
            (Proof eqV, _, _) = Unfold(ctx, ctok, ctorArgs, (i, dom) => i < np ? Hyp(ctx, $"{ps[i]} e. {dom}")!.Value : FieldIn(i - np));
            if (Rhs(eqV) != tag)
            {
                throw new Refused($"{ctor.Name}'s value came out as {Rhs(eqV)}, not {tag}");
            }
            string ctorApp = Lhs(eqV);
            // The computation rule, at these fields.
            string il = IotaLemma(ctor.Name);
            var sub = new Dictionary<string, string> { ["U"] = "U" };
            foreach (string a in recArgs)
            {
                sub[a] = a;
            }
            for (int k = 0; k < fields.Count; k++)
            {
                sub[ClassVars[nrec + k]] = fields[k];
            }
            Proof iotaI = ApplyId(il, sub);
            (string ante, string iotaEq) = _d.Split(iotaI.Proves);
            var hyps = Conjuncts(ante).Reverse().ToList();
            Proof all = hyps.Skip(1).Aggregate(Discharge(hyps[0]), (acc, h) => _d.Jca(acc, Discharge(h)));
            Proof Discharge(string h)
            {
                if (Hyp(ctx, h) is Proof p)
                {
                    return p;
                }
                int k = fields.FindIndex(f => h.StartsWith($"{f} e. ", StringComparison.Ordinal));
                return k >= 0 ? FieldIn(k) : throw new Refused($"can't discharge {h}");
            }
            Proof iota = _d.Syl(all, iotaI);
            string rhs = _d.Sides(iotaEq).R;
            // The minor premise applied to the fields, then to the recursion at each recursive field.
            string minor = recArgs[np + rec.NumMotives + j];
            Proof m = Hyp(ctx, $"{minor} e. {rdoms[np + rec.NumMotives + j]}")!.Value;
            string f0 = minor, ty = rdoms[np + rec.NumMotives + j];
            for (int k = 0; k < fields.Count; k++)
            {
                (m, ty) = ApplyText(ctx, m, f0, ty, fields[k], FieldIn(k));
                f0 = $"( {f0} ` {fields[k]} )";
            }
            foreach (int k in rf)
            {
                string rv = fields[k];
                Proof inQ = pr.Apply("sseld", S(("ph", ctx), ("A", s), ("B", q), ("C", rv)), rInS(rv));
                Proof inQ2 = pr.Apply("mpd", S(("ph", ctx), ("ps", $"{rv} e. {s}"), ("ch", $"{rv} e. {q}")), Hyp(ctx, $"{rv} e. {s}") ?? throw new Refused($"no {rv} e. {s}"), inQ);
                Proof sub2 = _d.Congruence("wff", P("Z"), "Z", pr.Apply("id", S(("ph", $"{tv} = {rv}"))));
                Proof bi = _d.Syl(Exists(ctx, rv), pr.Apply("elabg", S(("x", tv), ("ph", P(tv)), ("ps", P(rv)), ("A", rv), ("V", "_V")), sub2));
                Proof prv = pr.Apply("mpbid", S(("ph", ctx), ("ps", $"{rv} e. {q}"), ("ch", P(rv))), inQ2, bi);
                string arg = $"( {r} ` {rv} )";
                (m, ty) = ApplyText(ctx, m, f0, ty, arg, prv);
                f0 = $"( {f0} ` {arg} )";
            }
            if (f0 != rhs)
            {
                throw new Refused($"{ctor.Name}'s minor premise applied came out as {f0}, not {rhs}");
            }
            string want = $"( {motive} ` {ctorApp} )";
            Proof tyEq = AlphaIn(ctx, ty, want);
            Proof rhsIn = pr.Apply("eleqtrd", S(("ph", ctx), ("A", rhs), ("B", ty), ("C", want)), m, tyEq);
            // Back to the tuple: ( R ` tag ) = ( R ` ctorApp ) = rhs, and ( B ` ctorApp ) = ( B ` tag ).
            Proof e1 = pr.Apply("fveq2d", S(("ph", ctx), ("A", tag), ("B", ctorApp), ("F", r)), _d.Symm(eqV));
            Proof lhsIn = pr.Apply("eqeltrd", S(("ph", ctx), ("A", $"( {r} ` {tag} )"), ("B", rhs), ("C", want)), _d.Trans(e1, iota), rhsIn);
            Proof e3 = pr.Apply("fveq2d", S(("ph", ctx), ("A", ctorApp), ("B", tag), ("F", motive)), eqV);
            return pr.Apply("eleqtrd", S(("ph", ctx), ("A", $"( {r} ` {tag} )"), ("B", want), ("C", $"( {motive} ` {tag} )")), lhsIn, e3);
        }

        // ( ctx -> part C_ Q ), part = U_ f1 e. D1 … { tag } for constructor j.
        Proof PartSub(string ctx, string part, int j, List<string> fields, string s, Func<string, Proof> rInI, Func<string, Proof> rInS)
        {
            SyntaxTree n = pr.Parse("class", part.Split(' '))!;
            if (n.Rule.Label == "csn")
            {
                string tag = pr.Render(n.Children[0]);
                Proof ptag = CtorStep(ctx, j, fields, tag, s, rInI, rInS);
                Proof sub2 = _d.Congruence("wff", P("Z"), "Z", pr.Apply("id", S(("ph", $"{tv} = {tag}"))));
                Proof inQ = pr.Apply("elabd", S(("ph", ctx), ("x", tv), ("A", tag), ("V", "_V"), ("ps", P(tv)), ("ch", P(tag))), Exists(ctx, tag), ptag, sub2);
                return pr.Apply("snssd", S(("ph", ctx), ("A", tag), ("B", q)), inQ);
            }
            if (n.Rule.Label != "ciun")
            {
                throw new Refused($"a constructor's part isn't unions of a singleton: {part}");
            }
            string f = pr.Render(n.Children[0]), dom = pr.Render(n.Children[1]), body = pr.Render(n.Children[2]);
            if (ctx.Split(' ').Contains(f))
            {
                throw new Refused($"a field variable {f} occurs in the hypotheses");
            }
            string ctx2 = $"( {ctx} /\\ {f} e. {dom} )";
            Proof Weak(Proof p) => pr.Apply("adantr", S(("ph", ctx), ("ps", _d.Split(p.Proves).X), ("ch", $"{f} e. {dom}")), p);
            Proof inner = PartSub(ctx2, body, j, fields.Append(f).ToList(), s, v => v == f ? RecIn(ctx2, f, s, w => Weak(rInI(w))) : Weak(rInI(v)), v => Weak(rInS(v)));
            return pr.Apply("iunssd", S(("ph", ctx), ("x", f), ("A", dom), ("B", body), ("C", q)), inner);
        }

        // A recursive field f e. S is in ⟦I params⟧.
        Proof RecIn(string ctx2, string f, string s, Func<string, Proof> rInI0)
        {
            Proof sI = rInI0("*stage*");
            Proof imp = pr.Apply("sseld", S(("ph", ctx2), ("A", s), ("B", iapp), ("C", f)), sI);
            return pr.Apply("mpd", S(("ph", ctx2), ("ps", $"{f} e. {s}"), ("ch", $"{f} e. {iapp}")), Hyp(ctx2, $"{f} e. {s}") ?? throw new Refused($"no {f} e. {s}"), imp);
        }

        // ( ctx -> parts C_ Q ) for the left-nested union of the constructors' parts.
        Proof PartsSub(string ctx, string parts, int count, string s, Func<string, Proof> rInI, Func<string, Proof> rInS)
        {
            if (count == 1)
            {
                return PartSub(ctx, parts, 0, [], s, rInI, rInS);
            }
            SyntaxTree n = pr.Parse("class", parts.Split(' '))!;
            string left = pr.Render(n.Children[0]), right = pr.Render(n.Children[1]);
            Proof l = count == 2 ? PartSub(ctx, left, 0, [], s, rInI, rInS) : PartsSub(ctx, left, count - 1, s, rInI, rInS);
            Proof rr = PartSub(ctx, right, count - 1, [], s, rInI, rInS);
            return pr.Apply("unssd", S(("ph", ctx), ("A", left), ("B", right), ("C", q)), l, rr);
        }

        Proof result;
        if (!_recursive.ContainsKey(itok))
        {
            Proof sub0 = PartsSub(ph, set, ind.Ctors.Length, "(/)", _ => throw new Refused("no recursive fields"), _ => throw new Refused("no recursive fields"));
            result = pr.Apply("eqsstrd", S(("ph", ph), ("A", iapp), ("B", set), ("C", q)), eqT, sub0);
        }
        else
        {
            string k = Part(set, "x"), stageBody = Part(set, "B");
            string Stage(string b) => Subst(stageBody, k, b);
            string stepf = Part(Part(Stage("(/)"), "F"), "F");
            string y = Pick();
            string Phi(string at) => $"{Stage(at)} C_ {q}";
            Proof Sub(string to) => _d.Congruence("wff", Phi("Z"), "Z", pr.Apply("id", S(("ph", $"{k} = {to}"))));
            // The base: the empty stage.
            Proof r0 = _d.Lift(ph, pr.Apply("rdg0", S(("F", stepf), ("A", "(/)")), pr.Apply("0ex", S())));
            Proof baseP = pr.Apply("eqsstrd", S(("ph", ph), ("A", Stage("(/)")), ("B", "(/)"), ("C", q)), r0, _d.Lift(ph, pr.Apply("0ss", S(("A", q)))));
            // The step.
            string sY = Stage(y);
            string ctx3 = $"( ( {ph} /\\ {y} e. _om ) /\\ {Phi(y)} )";
            Proof yOm = Hyp(ctx3, $"{y} e. _om")!.Value;
            Proof suc = _d.Syl(_d.Syl(yOm, pr.Apply("nnon", S(("A", y)))), pr.Apply("rdgsuc", S(("B", y), ("F", stepf), ("A", "(/)"))));
            Proof eqS = _d.Trans(suc, ApplyStep(ctx3, stepf, sY));
            string un = Rhs(eqS);
            SyntaxTree unN = pr.Parse("class", un.Split(' '))!;
            if (unN.Rule.Label != "cun" || pr.Render(unN.Children[0]) != sY)
            {
                throw new Refused($"the next stage came out as {un}");
            }
            string fs = pr.Render(unN.Children[1]);
            // The stage is in ⟦I params⟧ (ssiun2s, then the type's equation), and in Q (the hypothesis).
            Proof stageSub = _d.Syl(yOm, pr.Apply("ssiun2s", S(("x", k), ("A", "_om"), ("B", stageBody), ("C", y), ("D", sY)),
                _d.Congruence("class", Subst(stageBody, k, "Z"), "Z", pr.Apply("id", S(("ph", $"{k} = {y}"))))));
            Proof eqT3 = _d.Syl(Restrict(ctx3, ph), eqT);
            Proof sInI = pr.Apply("sseqtrrd", S(("ph", ctx3), ("A", sY), ("B", set), ("C", iapp)), stageSub, eqT3);
            Proof sInQ = Hyp(ctx3, Phi(y))!.Value;
            Proof fsSub = PartsSub(ctx3, fs, ind.Ctors.Length, sY, _ => sInI, _ => sInQ);
            Proof unSub = pr.Apply("unssd", S(("ph", ctx3), ("A", sY), ("B", fs), ("C", q)), sInQ, fsSub);
            Proof stepIn = pr.Apply("eqsstrd", S(("ph", ctx3), ("A", Stage($"suc {y}")), ("B", un), ("C", q)), eqS, unSub);
            Proof ex1 = pr.Apply("ex", S(("ph", $"( {ph} /\\ {y} e. _om )"), ("ps", Phi(y)), ("ch", Phi($"suc {y}"))), stepIn);
            Proof ex2 = pr.Apply("ex", S(("ph", ph), ("ps", $"{y} e. _om"), ("ch", $"( {Phi(y)} -> {Phi($"suc {y}")} )")), ex1);
            Proof stepP = pr.Apply("com12", S(("ph", ph), ("ps", $"{y} e. _om"), ("ch", $"( {Phi(y)} -> {Phi($"suc {y}")} )")), ex2);
            Proof every = pr.Apply("finds2", S(("x", k), ("y", y), ("ph", Phi(k)), ("ps", Phi("(/)")), ("ch", Phi(y)), ("th", Phi($"suc {y}")), ("ta", ph)),
                Sub("(/)"), Sub(y), Sub($"suc {y}"), baseP, stepP);
            Proof all = pr.Apply("ralrimiv", S(("ph", ph), ("x", k), ("A", "_om"), ("ps", Phi(k))),
                pr.Apply("com12", S(("ph", $"{k} e. _om"), ("ps", ph), ("ch", Phi(k))), every));
            Proof unionSub = pr.Apply("sylibr", S(("ph", ph), ("ps", $"A. {k} e. _om {Phi(k)}"), ("ch", $"{set} C_ {q}")), all,
                pr.Apply("iunss", S(("x", k), ("A", "_om"), ("B", stageBody), ("C", q))));
            result = pr.Apply("eqsstrd", S(("ph", ph), ("A", iapp), ("B", set), ("C", q)), eqT, unionSub);
        }
        EmitLemma(label, $"The recursor of {ind.Name} is in its motive, at every member of the type (induction over the stages).", result);
        return label;
    }

    /// <summary>
    /// Apply a function by its type's text: from ( ph -> F e. T ) and ( ph -> A e. D ), where T is X_ x e. D B or
    /// ( B ^m D ): ( ph -> ( F ` A ) e. B[A] ), with the new type.
    /// </summary>
    private (Proof, string) ApplyText(string ph, Proof fIn, string f, string ty, string a, Proof aIn)
    {
        SyntaxTree n = pr.Parse("class", ty.Split(' ')) ?? throw new Refused($"does not parse: {ty}");
        if (n.Rule.Label == "cixp")
        {
            string x = pr.Render(n.Children[0]), dom = pr.Render(n.Children[1]), body = pr.Render(n.Children[2]);
            if (a.Split(' ').Contains(x) || f.Split(' ').Contains(x))
            {
                string y = FreshFor(a, f, body, dom, ph);
                string bodyY = SubstFree(body, x, y);
                Proof ren = pr.Apply("cbvixpv", S(("x", x), ("y", y), ("A", dom), ("B", body), ("C", bodyY)),
                    _d.Congruence("class", SubstFree(body, x, "Z"), "Z", pr.Apply("id", S(("ph", $"{x} = {y}")))));
                string ty2 = $"X_ {y} e. {dom} {bodyY}";
                fIn = pr.Apply("eleqtrd", S(("ph", ph), ("A", f), ("B", ty), ("C", ty2)), fIn, _d.Lift(ph, ren));
                (x, body, ty) = (y, bodyY, ty2);
            }
            if (BoundIn(body).Overlaps(ArgVars(a)))
            {
                string body2 = RenameApart(body, ArgVars(a), ph);
                string ty3 = $"X_ {x} e. {dom} {body2}";
                fIn = pr.Apply("eleqtrd", S(("ph", ph), ("A", f), ("B", ty), ("C", ty3)), fIn, AlphaIn(ph, ty, ty3));
                (body, ty) = (body2, ty3);
            }
            string inst = SubstFree(body, x, a);
            Proof sub = body.Split(' ').Contains(x)
                ? _d.Congruence("class", SubstFree(body, x, "Z"), "Z", pr.Apply("id", S(("ph", $"{x} = {a}"))))
                : pr.Apply("a1i", S(("ph", $"{body} = {body}"), ("ps", $"{x} = {a}")), pr.Apply("eqid", S(("A", body))));
            Proof r = _d.Syl(_d.Jca(fIn, aIn), pr.Apply("fvixp", S(("F", f), ("x", x), ("A", dom), ("B", body), ("C", a), ("D", inst)), sub));
            return (r, inst);
        }
        if (n.Rule.Label == "co" && pr.Render(n.Children[2]) == "^m")
        {
            string cod = pr.Render(n.Children[0]), dom = pr.Render(n.Children[1]);
            Proof fn = _d.Syl(fIn, pr.Apply("elmapi", S(("A", f), ("B", cod), ("C", dom))));
            return (pr.Apply("ffvelcdmd", S(("ph", ph), ("F", f), ("A", dom), ("B", cod), ("C", a)), fn, aIn), cod);
        }
        throw new Refused($"applying something whose type isn't a function type: {ty}");
    }
}
