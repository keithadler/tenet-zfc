# Milestone 3: from a definition table to the whole kernel

Milestone 3's gate is that all of Lean core translates and verifies. This document measures how far the milestone 2 translator is from that, and says what has to change. Step 1 of the order of work is built, so is step 2's definition checker, and step 3 has begun with non-recursive inductive types (see the end). The rest isn't yet.

## The survey

`tenet-zfc survey <export>` runs the statement translator on every theorem in an export. It reports why each refused statement was refused, and ranks the constants outside the table by how many theorems mention them. On `Init` from Lean 4.36.0 (exported by leanout):

| | Theorems |
|---|---|
| In `Init` | 45,588 |
| Statement translated by the milestone 2 table | 119 |
| Refused: a constant outside the table | 35,943 |
| Refused: a bound variable or λ applied to arguments | 7,520 |
| Refused: a proposition form outside the table (∧, ∨, ¬, ↔, ∃, ∀ over a dependent type, a predicate) | 2,006 |

The most common constants outside the table are `<` and `≤` on `Nat`, `Bool`, `Int`, `Not`, `Iff`, `Array`, `False`, subtraction, `Option`, `BitVec` and `String.Slice`.

Adding constants to the table in that order, one at a time, covers this many theorems:

| Constants added | Statements covered | Statements and proofs covered |
|---|---|---|
| 0 | 309 | 7 |
| 100 | 5,660 | 21 |
| 1,000 | 24,165 | 1,457 |
| 5,000 | 43,049 | 6,996 |
| all 37,118 | 45,588 | 45,588 |

("Covered" here means only that every constant has an entry. It's an upper bound on what would translate.)

## What this means

**The hand table can't reach the gate.** Proofs use far more constants than statements do. Even with 5,000 hand-written entries, only 6,996 theorems would have every constant in their proof translated, out of 45,588. Each entry is a claim that someone checks by hand, so tens of thousands of entries would also defeat the point of the spec's trust story ("a small, hand-checked table").

**So the translation must be generic.** Every Lean definition, inductive type and recursor gets its set-theoretic meaning computed from its own definition, following Carneiro's model, rather than looked up. That is how the spec's feature table already reads ("each Lean feature has a fixed set-theoretic meaning"); milestone 2 took the shallow shortcut because two theorems didn't need more.

**The table stays, with a different job.** An entry like `Nat.add ↦ +` becomes a proved theorem in the output, `|- ⟦Nat.add⟧ = ( x e. NN0 , y e. NN0 |-> ( x + y ) )`, rather than an assumption. Headline statements are then restated in `set.mm`'s own vocabulary through those theorems, and `set.mm`'s own versions are cross-checked against them, as `ccatlen` was. The trusted part shrinks to the definitions of the model itself.

## Design

1. **The model, once.** A `set.mm` section (written once, checked by both verifiers) that interprets the kernel's type theory:
   - `Prop` as `2o`, proofs as `(/)`;
   - Π-types as `X_` and λ as maps-to;
   - universes as `( R1 ` A )` for a limit ordinal `A` fixed per output, with the reflection argument of milestone 4 deciding `A`.
   This is the bridge library the spec's milestone 2 described in general.
2. **Inductive types as least fixed points.** Each inductive block becomes the least set closed under its constructors, built by `set.mm`'s well-founded recursion (`df-recs`/`df-rdg`). Its recursor becomes the function defined by recursion on that set, and its computation rules (the replayer's iota steps) become theorems about it. Nested and mutual blocks go through the same reduction the replayer already uses (`Nested.cs`).
3. **Definitions as definitions.** Each Lean definition `c := v` becomes a `set.mm` definition `df-lean.c $a |- lean.c = ⟦v⟧`. Unfolding a definition everywhere it is used instead would blow the output up exponentially; that is the spec's "sharing" requirement.
4. **Proofs from the trace.** Each replayed step becomes one `set.mm` step:
   - reductions and definitional equalities become equalities of interpretations, by the model's beta, delta, iota, eta and proof-irrelevance lemmas;
   - typing judgments become membership facts.
   The milestone 2 proof translator becomes the special case where every constant had a table entry.
5. **Quotients and choice.**
   - `Quot` becomes the set of equivalence classes of the smallest equivalence relation containing the given relation.
   - `Classical.choice` becomes a fixed global choice function from `set.mm`'s axiom of choice.
   Both are theorems about the model, proved once.

## The decision this needs

**Step 3 changes the output's trust story.** Milestone 2's outputs add only `$p` theorems to `set.mm`. Interpretation.md says no new definitions "until a definition checker is part of the pipeline".

Generic translation needs that checker. A definition `$a` is safe only if it is conservative: a new constant, defined once, not circular, with no free variables on the right. `set.mm` checks its own `df-` axioms this way in CI, with mmj2's `definitionCheck` macro (by Mario Carneiro).

The plan is therefore to add a third check to the pipeline: every `$a` the translator writes must pass a definition checker. It should be one the translator doesn't share code with. The candidates are mmj2's `definitionCheck`, which `set.mm` already trusts, or a small independent checker for the restricted form the translator writes: `df-lean.c $a |- lean.c = <class term over earlier constants> $.`

## Order of work

1. The model section, with its beta, Π, λ and application lemmas. Gate: `id`, `Function.comp` and `Function.const`, with their definitional equations, verify.
2. Definitions with the definition checker in CI. Gate: every non-recursive definition in `Init.Prelude` translates.
3. Inductive types and recursors. Gate: `Nat`, `Bool`, `List`, `Option` and `Prod` with their iota rules; then all inductive blocks in `Init`.
4. Proofs from traces, generically. Gate: `List.length_append` again, now through `lean.List.length` and a proved `⟦List.length⟧ = #` bridge instead of the table.
5. Quotients, choice, literals and `String`. Gate: the milestone's own, all of `Init`.

`survey` is rerun after each step and its counts recorded here.

## Step 1: the model (built)

`src/TenetZfc/Model.cs` translates any Lean term built from λ, Π, application, sorts, `let` and constants:

| Lean | `set.mm` |
|---|---|
| `fun x : A => b` | `( x e. ⟦A⟧ |-> ⟦b⟧ )` |
| `f a` | `( ⟦f⟧ ` ⟦a⟧ )` |
| `A → B` (non-dependent) | `( ⟦B⟧ ^m ⟦A⟧ )`, the functions from `⟦A⟧` to `⟦B⟧` |
| `(x : A) → B` | `X_ x e. ⟦A⟧ ⟦B⟧` |
| `Prop` | `2o` |
| any other sort | the universe `U` |
| a constant `c` | `( lean.c ` U )` |

Each definition becomes a new constant, with a syntax axiom and a definition that makes it a function of the universe:

```
$c lean.Function.comp $.
clean.Function.comp $a class lean.Function.comp $.
df-lean.Function.comp $a |- lean.Function.comp = ( u e. Univ |-> ( x e. u |-> ( y e. u |-> ( z e. u |->
    ( w e. ( z ^m y ) |-> ( v e. ( y ^m x ) |-> ( t e. x |-> ( w ` ( v ` t ) ) ) ) ) ) ) ) ) $.
```

The constants a definition uses are defined before it. Each binder gets its own set variable, so substitution never captures one, and the definition's set variables are declared distinct.

Each definition also gets its **definitional equation**, proved by one `fvmptd` step per argument. The rewriting inside a map uses the congruence prover, which now handles `|->` and functions under application (`mpteq12dv`, `fveq1d`, `fveq12d`). `tenet-zfc define` writes the definitions and their equations:

- `id`: `|- ( ( ( U e. Univ /\ A e. U ) /\ B e. A ) -> ( ( ( lean.id ` U ) ` A ) ` B ) = B )`, 716 steps;
- `Function.comp`: `( ( ( ( ( ( ( lean.Function.comp ` U ) ` A ) ` B ) ` C ) ` D ) ` E ) ` F ) = ( D ` ( E ` F ) )`, for `D e. ( C ^m B )`, `E e. ( B ^m A )` and `F e. A`, 8,274 steps;
- `Function.const`: `( ( ( ( ( lean.Function.const ` U ) ` A ) ` B ) ` C ) ` D ) = C`, 2,741 steps.

Both verifiers accept all three, and CI translates and verifies them again on every push. That meets step 1's gate.

**What step 1 leaves open:**
- **One universe for every level.** Every sort but `Prop` is the same `U`. That's sound for definitional equations, which only apply functions to their arguments. It can't state `Type u : Type (u+1)`, which needs `U e. U`; milestone 4 separates the levels.
- **What the theorems assume.** The equations assume `U e. Univ`: they hold in every Grothendieck universe, as hypotheses, with no new axiom. ZFC proves such universes exist, for example `( R1 ` om )`, the hereditarily finite sets (`set.mm`'s `omina` with `inagrud`). ZFC doesn't prove that one containing `ω` exists, so a theorem about `Nat` will need the bounded universes of milestone 4.
- **Not yet in the model:** inductive types, recursors, projections, literals, and Π-types into `Prop`, which should be propositions rather than sets of functions. Each of these is refused with its reason.

## Step 2: the definition checker (built); definitions across `Init.Prelude` (not yet)

The `df-lean.*` axioms are new `$a` statements, which both verifiers take on trust. `scripts/check-definitions` runs mmj2's `definitionCheck` on every output, the same check `set.mm`'s CI runs on its own definitions. It accepts a definition only if it is conservative:
- the symbol is new, defined once, and used by nothing earlier;
- no variable is free on the right that isn't on the left;
- every dummy variable is distinct from the others.

The script also loads the output with mmj2's LR parser, which checks that the new syntax keeps `set.mm`'s grammar unambiguous. Any error or warning fails the run.

It was checked against bad input before being trusted. Three definitions it must refuse, it refused, each for the right reason:
- a free variable, `lean.bad = ( y e. Univ |-> x )`;
- dummy variables without their `$d` conditions;
- a definition that uses its own symbol.

A test repeats the first of these, together with the translator's real output, whenever `TENET_ZFC_JAVA` and `TENET_ZFC_MMJ2` are set. CI runs the check on the model's output on every push, with mmj2 pinned to commit `c8dd055` and Java 11. The macro needs Java's Nashorn engine, which later JDKs dropped.

With this, what an output asks you to trust is the two verifiers, `set.mm`, and mmj2's definition checker. Beyond those, a translated theorem means what its Lean statement means only through the definitions, and those are now computed from Lean's own definitions rather than written by hand.

**Still to do for step 2's gate:** every non-recursive definition in `Init.Prelude` translates. That needs Π-types into `Prop` and projections at least, and it needs inductive types for most definitions, which use them.

## Step 3, first part: non-recursive inductive types (built)

`tenet-zfc model-survey` tries the model on every definition in an export and reports the first thing that stops each one. On `Init`, before this part, 48 of 17,590 definitions translated with everything they use. 13,999 stopped first at an inductive type and 1,998 at a constructor.

`Init`'s 606 inductive types break down like this:

| Shape | Count |
|---|---|
| Non-recursive, unindexed types (structures, enumerations, classes) | 392 |
| Non-recursive propositions | 140 |
| Indexed propositions (40 of them recursive) | 55 |
| Recursive types | 18 |
| Nested types | 1 |

So the first class built is the 392.

**The encoding.** A value of such a type is a tagged tuple:
- **Fields:** `a1 … ak` become nested pairs, `<. a1 , <. a2 , … <. ak , (/) >. … >. >.`.
- **Tag:** constructor *i* puts `<. 1o , … >.` around that *i* times, then `<. (/) , … >.`. Two constructors are then told apart by `1o =/= (/)` alone.
- **The type:** the union over its constructors of `U_ a1 e. T1 … { tag(a1, …) }`. It is a set by `iunexg` and `snex`, with no universe closure lemmas.
- **The recursor:** case analysis on the tag, `if ( ( 1st ` t ) = (/) , minor0 fields , if ( … ) )`, with fields read back by `1st` and `2nd`.

```
df-lean.Option $a |- lean.Option = ( u e. Univ |-> ( x e. u |->
    ( { <. (/) , (/) >. } u. U_ y e. x { <. 1o , <. (/) , <. y , (/) >. >. >. } ) ) ) $.
df-lean.Option.some $a |- lean.Option.some = ( u e. Univ |-> ( x e. u |-> ( y e. x |->
    <. 1o , <. (/) , <. y , (/) >. >. >. ) ) ) $.
```

**The computation rules.** Each constructor's computation rule (Lean's iota reduction) is a theorem: `I.rec params motive minors (c params fields) = minor_c fields`. It is proved in four steps:
1. unfold the recursor and the constructor;
2. show the constructor's tagged tuple is in the type, through the union with `elun1`/`elun2` and down its indexed unions with `ssiun2s` and `snidg`;
3. evaluate the case analysis with a small simplifier: `1st` and `2nd` of an explicit pair by `op1stg` and `op2ndg`, and an `if` on a tag by `iftrued`, or by `iffalsed` with `1n0`;
4. check that the result is exactly the minor premise applied to the fields.

For `Bool`, `Prod` and `Option`, the type, constructor and recursor definitions pass mmj2's definition check, and both verifiers accept all five computation rules and every definitional equation. CI checks them on every push.

**A `$d` problem the verifiers caught.** The first version substituted under the theorem's hypotheses. A hypothesis like `D e. X_ w e. A …` mentions the bound variable `w`, and rewriting inside a value that binds `w` needs `w` disjoint from the context. Both verifiers rejected it. Substitution now goes through `fvmptd3`, whose substitution hypothesis is closed (`x = A` alone). Sethood is proved under only the hypotheses the term uses.

**The effect.** On `Init`, 1,468 definitions now translate with everything they use, up from 48. That is translation only; proofs are made and checked per theorem.

| What stops a definition next | Definitions |
|---|---|
| `Nat` (recursive) | 5,190 |
| `List` (recursive) | 3,243 |
| `Eq` (indexed proposition) | 758 |
| `Lean.Syntax` (recursive) | 674 |
| projections | 649 |
| `Lean.ParserDescr` (recursive) | 647 |
| a structure field whose type binds a variable (`Functor.mk`) | 476 |
| `False` (proposition) | 304 |

## Step 3, second part: proofs, propositions, projections (built)

**Proof irrelevance.** Every proof now translates to `(/)`. Telling a proof from data needs a term's type, so the model has a small type inferencer of its own (`Typing.cs`): structural inference, with types normalized by beta, delta and zeta. The replayer only checks the types the trace records.

The inferencer isn't trusted. A wrong answer changes what a translated definition says, and its equations then fail to verify; it can't make a verifier accept a false theorem. Whether a definition means what the Lean one means is a separate question. It is checked, for the constants a headline statement uses, by bridge theorems such as `⟦Nat.add⟧ = +`.

A side effect: theorems used inside definitions become `(/)`, so they never need translating.

**Inductive propositions**, indexed or not, if they aren't recursive:
- **The proposition:** `( params |-> ( indices |-> if ( φ , 1o , (/) ) ) )`, where φ says some constructor applies, `E. fields ( indices = the constructor's indices )`. So `Eq α a b` is `if ( b = a , 1o , (/) )`, `And p q` is `if ( E. z e. p E. w e. q T. , 1o , (/) )`, and `False` is `(/)`.
- **Constructors:** proofs, so `(/)`.
- **A recursor that eliminates only into `Prop`:** `(/)`. Both sides of its computation rule are proofs, so there is nothing to prove.
- **A recursor that eliminates into any sort** (`Eq`, `HEq`, `And`, `True`: one constructor whose fields are proofs): the minor premise applied to `(/)` for each field. With no constructor (`False`), it is `(/)`.

Its computation rule is proved in three steps:
1. unfold the recursor at the constructor's indices;
2. show `(/)` is in the proposition by proving the constructor's case of φ (`rspcedvd` with witness `(/)`, `trud`, `eqidd`, `orcd`/`olcd`), then `iftrued` and `0lt1o`;
3. check that the result is the minor premise.

For `Eq.refl`, `HEq.refl`, `True.intro` and `And.intro`, both verifiers accept the computation rule. Every definition passes the definition check.

**Projections** out of a structure read field *i* from its tagged tuple: `1st` after *i* applications of `2nd`, on `( 2nd ` s )`.

**Also:**
- Opaque constants are defined by their checked value. Lean can't unfold them, so a Lean theorem about one uses only its type, and any value of that type is faithful.
- Binders in sibling scopes may share a set variable. A binder must still differ from every enclosing binder, which keeps substitution capture-free, and from every variable in its own domain. `mptexd`, `fvmptd3`, `iunexg` and `ixpexg` need the latter, and all three checkers caught a first version that missed it.
- Fields whose types bind variables are refused only where it matters, in the computation rule, which matches hypotheses as text.

**The effect on `Init`:** 5,362 of 17,590 definitions now translate with everything they use. That's up from 1,468 after the first part and 48 before step 3. Nearly every blocker left is a recursive type:

| What stops a definition next | Definitions |
|---|---|
| `Nat` | 4,747 |
| `List` | 2,888 |
| `Lean.Syntax` | 686 |
| `Lean.ParserDescr` | 647 |
| `Lean.Name` | 237 |
| `Nat` literals | 187 |
| `Acc` | 113 |

**Next: recursive types.** set.mm has what's needed to build a recursive type's set: `rec ( F , A )` with `rdg0` and `rdgsuc`, `frfnom`, and `omex`. The type would be the union of an ω-chain of stages, `U_ n e. om ( rec ( G , (/) ) ` n )` with `G = ( X e. _V |-> ( X u. F ( X ) ) )`. It is a set by `iunexg` and `omex`.

The recursor is the real work. Its computation rules need induction, which comes down to the recursion theorem for the type: a function on the fixed point satisfying the constructor equations exists, and it is unique. The plan is to prove that once, in a general form that each recursive type instantiates, rather than generating an induction proof per type.

## Step 3, third part: recursive types (built for finitary types)

**The recursion theorem is already in `set.mm`.** `frr2` is well-founded recursion: for a relation R that is well-founded (`Fr`) and set-like (`Se`) on A, `F = frecs ( R , A , G )` satisfies `( F ` X ) = ( X G ( F |` Pred ( R , A , X ) ) )`. So a recursive type's recursor will be `frecs` over the relation "has smaller rank":

`RankLt = { <. x , y >. | ( rank ` x ) e. ( rank ` y ) }`.

- **Se:** `exse` gives it for any set.
- **Predecessors:** a recursive field sits inside nested ordered pairs of its value, and each layer raises rank (`opi1`/`opi2`, `snid`/`prid2`, `rankelb`). So a recursive field is always a predecessor of its value, and each computation rule follows from `frr2`.
- **Fr:** a one-time lemma, proved by `tenet-zfc bridge` and checked by both verifiers in CI.

**The one-time lemma (built):**

`lean-rankfr $p |- { <. x , y >. | ( rank ` x ) e. ( rank ` y ) } Fr A`, in 1,307 steps.

The proof, for a nonempty `w`:
1. The ranks of its elements, `( rank " w )`, are a nonempty set of ordinals (`imassrn`, `rankf`, `fnimaeq0`).
2. So they have a least one (`onint`).
3. Some `v e. w` has it (`fvelimab`).
4. No `s e. w` has smaller rank (`onnmin`), so `v` is minimal.
5. `df-fr` turns that into `Fr`.

**Recursive types (built)** apply to finitary types, whose recursive fields are the type itself at its own parameters. The computation rules are proved for constructors with any number of recursive fields (trees too: see below).

| Lean | `set.mm` |
|---|---|
| the type | `U_ k e. _om ( rec ( ( X e. _V |-> ( lean.I.-step ` <. P , X >. ) ) , (/) ) ` k )`, the union of an ω-chain of stages; a set by `iunexg` and `omex` |
| the step | `X u.` every constructor's tagged tuple whose recursive fields are in `X` |
| constructors | tagged tuples, as before |
| the recursor | `( frecs ( RankLt , ⟦I params⟧ , ( a e. _V , f e. _V |-> ( lean.I.-case ` <. <. Q , a >. , f >. ) ) ) ` t )` |

**The constants on a packed argument.** The step and the case analysis are constants of their own, each a single map over a packed argument. P packs the universe and the parameters; Q packs those plus the motive and the minor premises.
- **They have no universe layer.** A definition may be a proper class, but a function value can't be. A map over `_V` reached as the value of a constant would be `(/)`. The checkers didn't flag this. Writing the proof did: it needed the step's value at the parameters to be a set.
- **They are constants at all because of `$d`.** Inline, their bound variables would land inside their own scope when a stage, or the recursion function, is substituted back in.
- **Renaming.** Where a stage or the recursion function is substituted, the wrapper's variable is renamed first (`cbvmptv`, `cbvmpov`).
- **The simplifier** reads the packed parts back with `op1stg` and `op2ndg`, including inside unions and indexed unions.

**The computation rule** of each constructor follows the plan above:
1. The value is in the type. Unfold the step at a stage, show the tagged tuple is in the next stage (`rdgsuc`), then in the union (`ssiun2s`, `peano2`). For a recursive field, take the stage it is in (`eliun`, `rexlimdva2`, with the union's variable renamed by `cbviunv`). With several, take each one's stage `m_i` and put them all in the stage `( m_1 u. m_2 u. … )` (`omun`, `ssun1`/`ssun2`, and `lean-stagess` below). This runs under only the parameters' and fields' hypotheses.
2. `frr2` unfolds the recursion once, with `lean-rankfr` for `Fr` and `exse` for `Se`.
3. `ovmpog` applies the case analysis, and the simplifier evaluates it on the tag.
4. The recursion at a recursive field is the recursor there. The field is a predecessor of the value (`elpredg`, `brabga`), since it has smaller rank (`dfopg`, `snidg`/`prid2g`, `rankelb`, `ontr1`), so `fvres` applies.

**The output** states exactly Lean's computation rules:

```
lean-Nat.succ-iota |- ( … ) -> ( ( ( ( ( lean.Nat.rec ` U ) ` A ) ` B ) ` C ) ` ( ( lean.Nat.succ ` U ) ` D ) )
                            = ( ( C ` D ) ` ( ( ( ( ( lean.Nat.rec ` U ) ` A ) ` B ) ` C ) ` D ) )
lean-List.cons-iota |- ( … ) -> ( … lean.List.rec … ` ( ( ( ( lean.List.cons ` U ) ` A ) ` E ) ` F ) )
                             = ( ( ( D ` E ) ` F ) ` ( ( ( ( ( ( lean.List.rec ` U ) ` A ) ` B ) ` C ) ` D ) ` F ) )
```

Both verifiers accept them, and the definitions pass the definition check. The proofs are long: 55,000 steps for `Nat.zero`, 122,000 for `Nat.succ` and 311,000 for `List.cons`, because the text repeats every subterm. Compressed proofs now share the repeats (see [Proof size](#proof-size-compressed-proofs-with-sharing)): `List.cons`'s rule is 5,539 steps.

**The effect on `Init`:** 6,481 of 17,590 definitions now translate with everything they use, up from 5,362.

| What stops a definition next | Definitions |
|---|---|
| recursive inductive propositions (`Nat.le` 5,634, `Acc` 124, `List.Mem` 49, …) | 5,950 |
| `Nat` literals | 2,087 |
| the nested type `Lean.Syntax` | 785 |
| running out of set variables (set.mm has 26 lowercase ones) | 222 |

### Trees: constructors with several recursive fields (built)

A constructor's value is in the stage after the one holding its recursive fields. With one recursive field that is the field's own stage. With several, say the two subtrees of a binary tree, each field is in a stage of its own, so the proof needs a common one. The stages only grow, so the union of the fields' stages holds them all. That is a second one-time lemma, written into an output the first time a constructor needs it:

```
lean-stagess.1 $e |- ( ph -> z C_ ( F ` z ) ) $.
lean-stagess $p |- ( ( ( M e. _om /\ N e. _om ) /\ N C_ M ) -> ( ph -> ( rec ( F , A ) ` N ) C_ ( rec ( F , A ) ` M ) ) ) $.
```

- **The hypothesis:** in context `ph`, the step's values contain their argument. A stage function `( X e. _V |-> ( lean.I.-step ` <. P , X >. ) )` has this, since its value at `z` is `( z u. … )` (`ssun1`). The context is the parameters' and fields' hypotheses.
- **The proof** is induction from `N` (`findsg`) on `( ph -> stage N C_ stage x )`. At `N` it is `ssid`. From `y` to `suc y`: `stage suc y` is `F` at `stage y` (`rdgsuc`), which contains `stage y` (the hypothesis at `stage y`, by `vtocl`), and `sstrd` chains the two. 1,481 steps.
- **In the computation rule:** each recursive field `r_i` is in some stage `m_i` (`eliun`). Under all of these, `b = ( ( m_1 u. m_2 ) u. … )` is in `_om` (`omun`), each `m_i C_ b` (`ssun1`, `ssun2`, `sstri`), so each `r_i` is in stage `b` (`lean-stagess`, `sseld`). The tagged tuple is then in stage `suc b` as before, and `rexlimdva2` discharges the `m_i` one at a time, innermost first.
- **The rest of the rule needs no change.** The case analysis already passes the recursion at every recursive field, and each field is a predecessor of the value on its own.

**The fixture** is `Tree.lean`, a binary tree exported with leanout (`tests/fixtures/tree.ndjson`):

```lean
inductive Tree (α : Type u) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α
```

Its computation rules, with both recursive calls:

```
lean-Tree.leaf-iota |- ( … ) -> ( … lean.Tree.rec … ` ( ( lean.Tree.leaf ` U ) ` A ) ) = C
lean-Tree.node-iota |- ( … ) -> ( … lean.Tree.rec … ` ( ( ( ( ( lean.Tree.node ` U ) ` A ) ` E ) ` F ) ` G ) )
                             = ( ( ( ( ( D ` E ) ` F ) ` G ) ` ( ( ( ( ( ( lean.Tree.rec ` U ) ` A ) ` B ) ` C ) ` D ) ` E ) )
                                                         ` ( ( ( ( ( ( lean.Tree.rec ` U ) ` A ) ` B ) ` C ) ` D ) ` G ) )
```

Both verifiers accept them, and the definitions pass the definition check. Uncompressed, `Tree.leaf` takes 132,000 steps and `Tree.node` 798,000.

## Step 3, fourth part: recursive propositions and `Nat` literals (built)

**Recursive propositions.** A recursive proposition, like a recursive type, is a least fixed point. Here it is the least set of index tuples closed under the constructors, built in the same stages. The proposition is true at indices whose tuple is in that set:

```
df-lean.Nat.le $a |- lean.Nat.le = ( u e. Univ |-> ( x e. ( lean.Nat ` u ) |-> ( y e. ( lean.Nat ` u ) |->
    if ( <. y , (/) >. e. U_ z e. _om ( rec ( ( v e. _V |-> ( lean.Nat.le.-step ` <. <. u , <. x , (/) >. >. , v >. ) ) , (/) ) ` z ) , 1o , (/) ) ) ) ) $.
```

- **The step** adds each constructor's result indices over its fields. A recursive premise `I params e⃗` ranges over `if ( <. e⃗ >. e. X , 1o , (/) )`, so it holds when its own indices were in the last stage. For `Nat.le n`, the step adds `<. n , (/) >.` (`refl`), and `succ y` for each `y` already present (`step`).
- **Recursors** of recursive propositions eliminating only into `Prop` are `(/)`, and their computation rules need no proof.
- **Not yet handled:** large elimination of a recursive proposition, and premises that are functions into the proposition (`Acc`).

**`Nat` literals.** A literal is `( lean.Nat.-lit ` ( lean.Nat.-ofnum ` n ) )`, with n as `set.mm`'s decimal numeral:
- **`-ofnum`** inverts `set.mm`'s standard isomorphism from `_om` onto `NN0`, `( rec ( ( y e. _V |-> ( y + 1 ) ) , 0 ) |` _om )`.
- **`-lit`** takes the ordinal k to `Nat.succ` applied k times to `Nat.zero`, in the model's encoding.

So a literal stays as short as its decimal digits: `UInt8.size` is `… ( lean.Nat.-lit ` ( lean.Nat.-ofnum ` ; ; 2 5 6 ) ) …`. `Nat` arithmetic on literals (the kernel's GMP steps) will need bridge theorems relating `-lit` to `+` on `NN0`, as the spec planned.

**Checked:** `Nat.le`, its constructors and recursor, `Nat.lt` and `UInt8.size`. Their definitions pass the definition check, and both verifiers accept their equations, in a test and in CI.

**The effect on `Init`:** 11,780 of 17,590 definitions now translate with everything they use, up from 6,481 (two thirds of `Init`).

| What stops a definition next | Definitions |
|---|---|
| the nested type `Lean.Syntax` | 1,483 |
| running out of set variables (set.mm has 26) | 1,058 |
| string literals | 339 |
| `Acc` (a premise that is a function into `Acc`) | 325 |
| axioms (`propext`, `Classical.choice`, …) and quotients | 109 |

**Next:**
- **Nested types** (`Lean.Syntax`), through the replayer's existing reduction to a mutual block.
- **Strings**, as lists of characters.
- **Axioms**, which are milestone 3's last item: `propext` holds in the model, and `Classical.choice` comes from `set.mm`'s choice.

## Step 3, fifth part: extra set variables (built)

set.mm has 26 set variables, the lowercase letters, and 1,058 definitions in `Init` needed more: a structure with many fields, such as `Lean.Grind.Config`, binds one variable per field in its recursor, inside the motive's and the minor premise's binders.

**The output declares its own,** `xx1`, `xx2`, …, after the letters are used up. No token of `set.mm` is `xx` followed by digits. Each is declared once, at the top level, before the first definition or proof that uses it:

```
$v xx1 $.
vxx1 $f setvar xx1 $.
```

- A `$v` and a `$f` add a variable, not an axiom, so nothing new can be proved about sets.
- The prover learns each one through `Database.Extend`, as it learns the definitions.
- The rules for the letters hold for the new variables too. A binder's variable differs from every enclosing binder's and from its own domain's variables, and the `$d` lists name every set variable a definition binds.
- `frr2` and `exse` reserve none of the new variables, since no `set.mm` proof uses them, so the recursion may take them after its own pool.

**Checked:** `Lean.Grind.Config.casesOn` binds 27 new variables. Its definitional equation states them too: the minor premise ranges over a Π-type of 27 fields. `Lean.Meta.Simp.Config.zeta` binds 10. Both verifiers accept their equations (235,000 proof steps for `casesOn`), and the definitions pass the definition check, in a test and in CI (`tests/fixtures/setvars.ndjson`).

**The effect on `Init`:** 12,178 of 17,590 definitions now translate with everything they use, up from 11,780. 398 of them use the new variables, at most 77 in one definition. No definition stops for lack of set variables any more. The other 660 of the 1,058 now stop at the next blocker in their dependencies, mostly string literals.

| What stops a definition next | Definitions |
|---|---|
| the nested type `Lean.Syntax` | 1,483 |
| string literals | 996 |
| names with characters a `set.mm` token can't have (`'`, `?`, `₂`) | 750 or more |
| `Acc` (a premise that is a function into `Acc`) | 325 |
| axioms and quotients | 112 |

## Proof size: compressed proofs with sharing (built)

The writer used to write each proof as a flat list of labels, so every repeated subterm was proved again in full. It now writes Metamath's compressed format (the Metamath book, appendix B) by default:

```
lean-two_add_two $p |- ( 2 + 2 ) = 4 $=
  ( c2 c4 caddc eqid 2p2e4 co eqtr4i eqtri oveq12i ) AACFZBBJJBAAAACADZKIEHBD
  G $.
```

- **The format.** The labels in parentheses are numbered after the theorem's mandatory hypotheses. The letters are step numbers, with `A`–`T` as a last digit and `U`–`Y` as earlier digits. `Z` saves the step just made, and later steps refer to it by number.
- **The sharing.** `CompressedProof.Compress` (in `Metamath.cs`) turns the flat proof into a tree, with equal subproofs as one node. A subproof the written proof meets twice is saved with `Z` the first time and referred to after that. A subproof that repeats only inside a saved one is written once already, so it is not saved. Single steps are not saved, since a reference costs as much as the label. The labels are ordered most-used first, so they get the shortest numbers.
- **Where.** `emit`, `define` and `bridge` compress. `--uncompressed`, anywhere on the command line, writes flat proofs as before. Theorems inside the model's declarations, like `lean-rankfr`, are compressed by `Writer.Raw`.
- **Checked:** both verifiers and the definition check accept every CI output in compressed form. A test checks the step numbers against the book's table and that `Expand` inverts `Compress`. Another test checks that both verifiers accept compressed proofs and reject the same file with one letter changed.

**Sizes** of the CI outputs (bytes), flat and compressed:

| Output | Flat | Compressed | Ratio |
|---|---:|---:|---:|
| `gate` | 385 | 344 | 1.1× |
| `lenapp` | 59,251 | 3,759 | 16× |
| `model` | 54,360 | 5,159 | 11× |
| `ind` | 711,916 | 36,431 | 20× |
| `props` | 624,426 | 43,748 | 14× |
| `rec` | 2,687,598 | 66,101 | 41× |
| `natle` | 156,074 | 16,267 | 9.6× |
| `bridge` | 5,200 | 1,202 | 4.3× |

The largest proofs gain the most, because their repeats are the longest. In `rec`, steps written (labels and references to saved steps):

| Theorem | Flat steps | Compressed steps | Saved subproofs |
|---|---:|---:|---:|
| `lean-rankfr` | 1,307 | 296 | 42 |
| `lean-Nat.zero-iota` | 55,416 | 2,742 | 318 |
| `lean-Nat.succ-iota` | 121,929 | 3,935 | 453 |
| `lean-List.nil-iota` | 98,655 | 3,771 | 428 |
| `lean-List.cons-iota` | 310,983 | 5,539 | 623 |
| `lean-Nat.rec-eq` | 13,332 | 1,115 | 135 |
| `lean-List.rec-eq` | 24,459 | 1,578 | 192 |

Sharing in the text makes the proofs short, but the proof search still builds the flat proof first. The next size step is to share inside the prover too: prove a repeated equality once, as a lemma or a saved step, instead of building it again.

## Step 5, first part: strings, axioms, quotients and choice (built)

**String literals.** The kernel expands a literal to `String.ofList` applied to the list of its characters, each `Char.ofNat` of its code point (`StringToCtor` in the replayer). The model translates it to exactly that, with one helper so it stays short:

```
df-lean.String.-cons $a |- lean.String.-cons = ( u e. Univ |-> ( x e. NN0 |-> ( y e. ( ( lean.List ` u ) ` ( lean.Char ` u ) ) |->
    ( ( ( ( lean.List.cons ` u ) ` ( lean.Char ` u ) ) ` ( ( lean.Char.ofNat ` u ) ` ( lean.Nat.-lit ` ( lean.Nat.-ofnum ` x ) ) ) ) ` y ) ) ) ) $.
```

A literal is then `( ( lean.String.ofList ` u ) ` … )` over one `-cons` per character, each code point a decimal numeral as for `Nat` literals: `"leanprover/lean4"` begins `( ( ( lean.String.-cons ` u ) ` ; ; 1 0 8 ) ` …` and ends in `( ( lean.List.nil ` u ) ` ( lean.Char ` u ) )`. In Lean 4.36 `String` is a structure over UTF-8 bytes, so `String.ofList` brings in `List.utf8Encode` and `ByteArray`; all of it translates.

**Axioms.** `Define` handles `ConstKind.Axiom` and the quotient's built-in constants:
- An axiom whose type is a proposition is a proof, so its value is `(/)`: `lean.propext = ( u e. Univ |-> (/) )`. So is `Quot.ind`, and `Quot.sound` when an export has it.
- `Classical.choice` is defined relative to a well-ordering of the universe (see below).

**Quotients.** `Quot α r` is the set of classes of the least equivalence relation on `⟦α⟧` containing `r`. That relation is a helper constant: the intersection of every equivalence relation on `x` containing the pairs `r` relates, cut down to `x X. x`.

```
df-lean.Quot.-eqv $a |- lean.Quot.-eqv = ( u e. Univ |-> ( x e. u |-> ( y e. ( ( 2o ^m x ) ^m x ) |->
    ( ( x X. x ) i^i |^| { a e. ~P ( x X. x ) | ( { <. b , c >. | ( ( b e. x /\ c e. x ) /\ (/) e. ( ( y ` b ) ` c ) ) } C_ a /\ a Er x ) } ) ) ) ) $.
```

| Lean | `set.mm` |
|---|---|
| `Quot r` | `( x /. E )`, the classes |
| `Quot.mk r a` | `[ a ] E`, the class of `a` |
| `Quot.lift f h` | `ran ( p e. x |-> <. [ p ] E , ( f ` p ) >. )`, set.mm's function lift (`qliftval`): `f` on a representative |

None of it uses choice. `Quot.lift f h` is a function on the classes only when `f` respects `E`, which `h` ensures.

**The computation rule** `Quot.lift f h (Quot.mk r a) = f a` is a theorem, in 100,610 steps:

```
lean-Quot.lift-iota |- ( ( … /\ D e. ( C ^m A ) ) /\ E e. X_ v e. A X_ t e. A ( ( ( ( ( lean.Eq ` U ) ` C ) ` ( D ` v ) ) ` ( D ` t ) ) ^m ( ( B ` v ) ` t ) ) ) /\ F e. A )
    -> ( ( ( ( ( ( ( lean.Quot.lift ` U ) ` A ) ` B ) ` C ) ` D ) ` E ) ` ( ( ( ( lean.Quot.mk ` U ) ` A ) ` B ) ` F ) ) = ( D ` F ) )
```

1. Unfold `Quot.lift` and `Quot.mk`, then apply `qliftval`. It needs two facts.
2. **`E` is an equivalence relation.** It is an intersection of them, inside `x X. x` (`riiner`, with `intiin`).
3. **The lift is a function** (`qliftfund`), because `f` is constant on `E`'s classes. The kernel of `f`, `( `' f o. f )`, is an equivalence relation (`fcoinver`). It contains `r`, so it is one of those intersected, and `E` is inside it (`intss1`, `fcoinvbr`).
4. **The kernel contains `r` because of `h`.** For `r b c`, `h` at `b` and `c` (`fvixp`) maps `(/)` into `Eq β (f b) (f c)`, which is therefore nonempty. That `Eq` unfolds to `if ( ( f ` c ) = ( f ` b ) , 1o , (/) )` (`n0i`, `iffalse`).

The congruence prover learned the forms these definitions use: `/.`, `[ A ] R`, `ran`, `|^|`, `~P`, `i^i`, `X.`, `{ x e. A | }`, `{ <. x , y >. | }`, `C_`, `Er` and `-.`. Sethood learned `i^i`, `X.`, `ran`, `/.` and `[ A ] R`.

**Checked:** `Lean.origin`, `String.instInhabited` and `instToStringBool`; `propext`, `Quot`, `Quot.mk`, `Quot.ind` and `Quot.lift`; `Classical.choice`, `Classical.choose` and `Classical.propDecidable`; the quotient's computation rule; and the theorem that choice picks an element. Their definitions pass the definition check, and both verifiers accept the equations and the rule, in a test and in CI.

**`Classical.choice` takes a well-ordering of the universe.** The plan above said choice "becomes a fixed global choice function from `set.mm`'s axiom of choice". That can't be a `set.mm` definition:
- ZFC proves that choice functions exist, but no class term defines one. It is consistent with ZFC that no definable well-ordering of `V`, or even of `~P om`, exists.
- `set.mm` says as much at `gblacfnacd`, and its emulation of Hilbert's ε (`hta`) is relative to a well-ordering `R`.

So the well-ordering is a parameter, the way `hta` says to translate HOL's ε. A constant whose value uses choice, directly or through another constant, gets a second layer after the universe's:

```
df-lean.Classical.choice $a |- lean.Classical.choice = ( u e. Univ |-> ( v e. ~P ( u X. u ) |->
    ( x e. u |-> ( y e. ( ( lean.Nonempty ` u ) ` x ) |-> ( iota_ z e. x A. w e. x -. w v z ) ) ) ) ) $.
df-lean.Classical.propDecidable $a |- lean.Classical.propDecidable = ( u e. Univ |-> ( y e. ~P ( u X. u ) |->
    ( x e. 2o |-> ( ( ( ( lean.Classical.choice ` u ) ` y ) ` ( ( lean.Decidable ` u ) ` x ) ) ` (/) ) ) ) ) $.
```

- **`choice α h`** is `α`'s least element in the well-ordering `v`, Hilbert's ε as `hta` emulates it.
- **Using it.** A constant that depends on choice translates to `( ( lean.c ` u ) ` v )`, passing its own well-ordering on. One that doesn't is `( lean.c ` u )` as before, so nothing that avoids choice changes.
- **Equations** take the well-ordering as `W`, with the hypothesis `W e. ~P ( U X. U )`.
- **Choice picks an element.** This is a theorem, `lean-Classical.choice-spec`, in 7,179 steps:

  ```
  |- ( ( … /\ B e. ( ( lean.Nonempty ` U ) ` A ) ) /\ W We U ) -> ( ( ( ( lean.Classical.choice ` U ) ` W ) ` A ) ` B ) e. A )
  ```

  `α` is in the universe, so inside it (`grutr`, `trss`). It is nonempty, since `Nonempty α`'s condition holds (`n0i`, `iffalse`, `rexn0`). So `W` has a unique least element on it (`wereu`), and the definition picks that element (`riotacl`).

The trust story doesn't change: no new axiom, and the definitions pass the definition check. A theorem that uses choice holds for every well-ordering of the universe. ZFC proves that one exists (`weth`), so a closed statement can discharge `W We U` the way `hta`'s comment describes.

Not yet handled: an inductive type, or a packed helper (a recursive type's step or case analysis), whose definition depends on choice. Each is refused with the reason.

**The effect on `Init`:** 12,145 of 17,590 definitions now translate with everything they use, up from 11,780. String literals, axioms, quotients and choice no longer stop any definition.

| What stops a definition next | Definitions |
|---|---|
| the nested type `Lean.Syntax` | 1,513 |
| running out of set variables (set.mm has 26) | 1,059 |
| `Acc` (a premise that is a function into `Acc`) | 328 |
| a name a `set.mm` token can't hold (`'`, `?`, `₂`), over the 25 most common reasons | at least 786 |

Names with `'` or `?` were hidden behind string literals before. They need an escaping scheme for tokens, a small change to `Model.Token`.

**With the extra set variables too** (step 3, fifth part, merged after this part): 13,192 of 17,590 definitions translate with everything they use. No definition stops for lack of set variables or at a string literal.

| What stops a definition next | Definitions |
|---|---|
| the nested type `Lean.Syntax` | 1,513 |
| a name a `set.mm` token can't hold (`'`, `?`, `₂`), over the 25 most common reasons | at least 804 |
| `Acc` (a premise that is a function into `Acc`) | 328 |

## Step 3, sixth part: mutual and nested inductive types (built)

Before this part, 1,483 definitions in `Init` stopped at "`Lean.Syntax` is a mutual or nested inductive type". `Lean.Syntax` holds an `Array Syntax`, so it is nested.

**A block is one least fixed point over a tagged sum.** The types of a mutual block, `I_0 … I_n-1`, are built together. A nested block first goes through the kernel's reduction to a mutual block, the one the replayer already checks (`Nested.cs`, now exposed as `Replayer.AuxiliaryBlock`). For `Rose α`, which holds a `List (Rose α)`, that block is `Rose` and an auxiliary type standing for `List (Rose α)`. `Lean.Syntax`'s block has three types: `Syntax`, `Array Syntax` and `List Syntax`.

- **Elements** of the fixed point are pairs `<. ix , v >.`. Here `ix` is the type's index (`(/)`, `1o`, `2o`, `suc 2o`, …), and `v` is a tagged tuple, as for any inductive type.
- **The step**, `lean.I_0.-mstep`, adds `<. ix , tag(fields) >.` for every constructor of every type. A recursive field of type `t` ranges over `( X " { ix_t } )`, the values of type `t` in the last stage.
- **Each original type is its slice.** The fixed point is the union of its ω-chain of stages, as before:

  ```
  df-lean.Tm $a |- lean.Tm = ( u e. Univ |-> ( x e. u |->
      ( U_ y e. _om ( rec ( ( r e. _V |-> ( lean.Tm.-mstep ` <. <. u , <. x , (/) >. >. , r >. ) ) , (/) ) ` y ) " { (/) } ) ) ) $.
  ```

- **Constructors** build tagged tuples. An auxiliary type's constructors are the nested type's own (`List.nil`, `List.cons`), so a value of `List (Rose α)` is the same set whichever way it is read.
- **The recursors are one recursion.** `frecs ( RankLt , _V , H )` runs over every set. Its value at `a` is the tuple of every type's case analysis on `a`, `<. case_0 , <. case_1 , … (/) >. >.`, computed by `lean.I_0.-mcase`. `I_t.rec`, and a nested block's `I.rec_k`, read component `t` at the major premise. A recursive field `r` of type `t'` gets component `t'` of the recursion at `r`.
- **Why every set.** The recursion runs over `_V` rather than the block, so its computation rules need no membership in it: `frr2` only needs `X e. _V`. That takes one new lemma, besides `lean-rankfr`:

  `lean-rankse $p |- { <. x , y >. | ( rank ` x ) e. ( rank ` y ) } Se _V`, in 550 steps. The sets of smaller rank than `z` all lie in `( R1 ` ( rank ` z ) )` (`rankr1ag`), which is a set.

**The computation rules** follow the recursive types' four steps:
1. **The value is in the major premise's type.**
   - For an original type, `<. ix , tag >.` is in a stage after every recursive field's (`eliun`, `lean-stagess`, the step, `rdgsuc`), and `elimasng` reads it back as a member of the slice.
   - For an auxiliary type, the value is the nested type's own constructor, in the nested type itself (`List.cons s l` in `List (Rose α)`), as for any recursive or non-recursive type.
2. **`frr2`** unfolds the recursion once, with `lean-rankfr` and `lean-rankse` on `_V`.
3. **The case analysis** is evaluated on the tag, and component `t` of the tuple is read off by the simplifier.
4. **The recursion at each recursive field** is component `t'` of the recursion there, which is `I_t'.rec` at it, since it has smaller rank (`elpredg`, `fvres`).

**Nested fields need a bridge.** `Rose.node a l` takes `l` in the real `List (Rose α)`, but the fixed point's step takes it from the auxiliary type's slice. So step 1 proves that every value of the nested type is a value of its auxiliary type: `⟦List (Rose α)⟧ C_ ( Fix " { 1o } )`.
- For a recursive nested type like `List`, this is induction over its stages (`finds`). Stage `(/)` is empty (`rdg0`). If stage `y` is in the slice, so is stage `suc y`: it is the step at stage `y` (`rdgsuc`), each constructor's part is in the slice (`iunssd`, `snssd`), and its recursive fields range over stage `y`.
- For a non-recursive one like `Array`, the constructors' parts are in the slice directly, and `Array Syntax`'s field of type `List Syntax` uses that type's bridge.
- The nested type's parameter (`Rose α`) is in `U`, because the field's type is the nested type applied to it (`elfvdm`, `dmmptss`). So these rules need no hypothesis beyond Lean's own.
- The block's bound variables are chosen apart from the nested types' definitions, so substituting their fields into the block's step never captures a variable.

**Checked** (`tests/fixtures/Mutual.lean`, exported to `mutual.ndjson`), in a test and in CI:
- the mutual block `Tm`/`Args`: the computation rules of `Tm.var`, `Tm.app`, `Args.nil` and `Args.cons`. `Tm.app`'s fields recurse into both types, through `Tm.rec` and `Args.rec`.
- the nested type `Rose`: `Rose.node` (through the bridge for `List (Rose α)`), and `Rose.rec_1` on `List.nil` and `List.cons`. `List.cons`'s head recurses through `Rose.rec` and its tail through `Rose.rec_1`.

Both verifiers accept them, and every definition passes the definition check. The flat proofs are long, from 319,000 steps (`Args.nil`) to 1,643,000 (`Rose.rec_1` on `List.cons`); compressed, `mutual.mm` is 267 KB. Generating them takes about 25 minutes of CPU, mostly in the prover's flat proof search. `Lean.Syntax`'s types, constructors and recursors are defined the same way (a test checks them, from `syntax.ndjson`).

**A fix on the way.** The recursors' definitional equations exposed a `$d` bug in the sethood prover. When two minor premises both bind `w` (`X_ w e. …`), a hypothesis mentioning `w` was carried under `ralrimivw` over `w`. It now drops hypotheses the term doesn't use before going under a binder.

**Not yet handled:** mutual or nested inductive propositions and indexed families, nested occurrences inside a nested type that is itself mutual, nested types with more than one parameter in computation rules (the bridge needs each parameter in `U`), and nested types that contain each other. Each is refused with the reason.

**The effect on `Init`:** 13,953 of 17,590 definitions now translate with everything they use, up from 13,192 on the same code without this part (all of PRs #1–#4 merged). No inductive type stops any definition any more. Of the 1,513 definitions `Lean.Syntax` stopped, 761 now translate; most of the others stop next at a name a token can't hold, such as `Lean.Syntax.getPos?`.

| What stops a definition next | Definitions |
|---|---|
| a name a `set.mm` token can't hold (`'`, `?`, `₂`) | at least 1,494, over the 25 most common reasons (the largest: `BitVec.extractLsb'` 373, `Lean.Syntax.getPos?` 296) |
| `Acc` (a premise that is a function into `Acc`) | 334 |

## Bridge theorems: the model's `Nat` is `NN0` (built)

`tenet-zfc nat-bridge` proves that `F = ( `' lean.Nat.-ofnum o. `' lean.Nat.-lit )` is a bijection from the model's `Nat` onto `NN0`. It takes zero to `0`, `succ` to `+ 1` and each literal to its numeral. Any function with `Nat.add`'s computation rules is `+` through `F`. Lean's `2 + 2 = 4`, read in the model, is proved equivalent to `set.mm`'s `( 2 + 2 ) = 4`. Milestone 2's table entries for `Nat` become these theorems. All three checkers accept the output, and CI runs them.

**A limit found on the way.** In the one-universe model, `⟦Nat.below⟧` is `(/)` everywhere. Its motive returns `U`, and `U e. U` is impossible. So `⟦Nat.add⟧`, compiled through `brecOn`, doesn't satisfy its own computation rules, and neither does any other structurally recursive definition. Both the motive lemma and the collapse of `Nat.below` are proved, and the bridge for `Nat.add` takes the rules as hypotheses until milestone 4 separates universe levels. See [bridges.md](bridges.md).

## Theorems through the model (built: `Nat.add_zero` and `Nat.zero_add`)

Until now no Lean theorem was proved through the generic model; milestone 2's `2 + 2 = 4` and `List.length_append` went through a hand-written table. `tenet-zfc theorem <export> <set.mm> <out.mm> <name>…` (`TheoremTranslator.cs`) now proves Lean theorems from their proof terms, in the model's own terms.

### First, a gap in the model: one universe makes `Nat.add` empty

Every function `Init` defines by structural recursion went to `(/)` in the model. So `Nat.add_zero` (`n + 0 = n`) was false there for `n ≠ 0`, and `⟦Nat.add⟧ = +` couldn't be proved.

- Structural recursion compiles to `Nat.brecOn`, whose functional takes an argument of type `Nat.below motive t`.
- `Nat.below` is `Nat.rec` at the motive `fun _ => Sort (max 1 u)`, which translates to `( z e. ( lean.Nat ` u ) |-> u )`.
- The recursor's motives range over `( u ^m ( lean.Nat ` u ) )`. That motive is in it only if `u e. u`, which is false. So `⟦Nat.below⟧` is a map applied outside its domain, `(/)`.
- From there `Nat.brecOn.go`'s motive is `(/)` everywhere, its minor premise can't be in it, and `⟦Nat.brecOn …⟧ = ( 1st ` ( 2nd ` (/) ) ) = (/)`.

The cause is the one universe for every level: large elimination into `Sort (u+1)` needs `Sort u ∈ Sort (u+1)`.

### Tower mode (`Universes.cs`, `Monomorph.cs`)

The fix is opt-in (`new Model(…, tower: true)`, `define --tower`), so default outputs don't change:

- **A tower of universes.** The universe argument ranges over `lean.-tower`, a new definition:

  ```
  df-lean.-tower $a |- lean.-tower = { f | ( ( f : _om --> Univ /\ _om e. ( f ` (/) ) ) /\ A. n e. _om ( f ` n ) e. ( f ` suc n ) ) } $.
  ```

  An increasing ω-sequence of Grothendieck universes, the first containing ω. `Prop` is `2o`, and `Sort (k+1)` is `( U ` k )` for a concrete level `k`.
- **Monomorphization.** Each constant used at concrete levels becomes its own constant, `c.{l1,l2}` (labels write it `c.ul1_l2`, since labels can't hold braces). A recursor's motive level stays a parameter, and it means the whole tower, `U. ran U`. It occurs only as the motive's codomain, so one recursor per type instance serves every elimination level.
- **Π-types into `Prop` are propositions**, `if ( A. x e. ⟦A⟧ (/) e. ⟦B⟧ , 1o , (/) )`, rather than sets of functions. A proof, `(/)`, is then in a Π-proposition exactly when it holds, as it is in any other proposition.

`Nat.below.{1}`'s motive is now `( z e. ( lean.Nat ` u ) |-> ( u ` (/) ) )`, in `( U. ran u ^m ( lean.Nat ` u ) )`. The definitions pass the definition check, and the definitional equations and computation rules verify as before.

**What a theorem assumes.** `U e. lean.-tower`. ZFC doesn't prove that such a tower exists (it needs inaccessible cardinals), so, as before, a theorem holds in every model of the hypotheses. It adds no axiom.

### How a theorem is proved

The model is meant to be sound for Lean's typing: if `Γ ⊢ e : T` then `⟦e⟧ ∈ ⟦T⟧`. A proof `p : P` translates to `(/)`, so translating the typing of `p` proves `(/) e. ⟦P⟧`: the statement holds in the model. The output is

```
|- ( ( U e. lean.-tower /\ A e. ⟦T1⟧ /\ … ) -> (/) e. ⟦statement⟧ )
```

with the statement's leading binders opened as hypotheses: `A e. ⟦T⟧` for data, `(/) e. ⟦P⟧` for a hypothesis.

**Typing becomes membership.**

| Lean | `set.mm` step |
|---|---|
| `f a`, `f : (x : A) → B` | `fvixp`, or `elmapi` and `ffvelcdmd` for a non-dependent arrow |
| `h a`, `h` a proof of a Π-proposition | `lean-prop` (below), then `rspcdv` |
| `fun x => b` | `ralrimiva`, then `mptelixpg` or `fmpt` and `elmapd` |
| a proof `fun x => b` | `ralrimiva`, then `lean-prop` |
| `s.i` | `lean-proj-S-i`: down the structure's unions (`eliun`, `rexlimdva`) to `s = tuple` (`elsni`) |
| a constant `c` | `lean-ty-c`, a typing lemma proved once (below) |
| a sort, a type as an argument | `UniverseMembership.cs`: closure of `( U ` k )` under pairs, singletons, unions and function spaces (`gruop`, `grusn`, `gruun`, `gruiun`, `grumap`) |
| a literal `n` | as `Nat.zero` or `Nat.succ (n-1)` (below) |

**Conversions become equations.** Where Lean checks `T ≡ T'`, the translator proves `( ph -> ⟦T⟧ = ⟦T'⟧ )` by normalizing both sides:
- beta: `fvmptd3`, with the argument's membership in the domain;
- delta: the constant's definition;
- iota: the constructor's computation rule, `lean-iota-c`;
- projections: the constructor's equation, then `op1stg` and `op2ndg`;
- Nat literals: `( lean.Nat.-lit ` ( lean.Nat.-ofnum ` 0 ) ) = ( lean.Nat.zero ` U )`, and so on, through `set.mm`'s isomorphism of `_om` and `NN0` (`om2uzf1oi`, `f1ocnvfv`, `frsuc`);
- congruence on applications, projections and Π-types (`fveq12d`, `ixpeq2dva`, `ralbidva`, `ixpconstg`).

Texts that differ only in the names of bound variables are equal by `Alpha.cs` (`cbvmptv`, `cbvixpv`, `cbviunv`, `cbvralvw` and congruence).

**Each constant is typed once**, by a lemma in the output:
- **definitions and theorems:** their value, typed;
- **constructors:** their tuple is in the type (`lean-in-c`, the first step of the computation rule's proof);
- **inductive types:** their sets are in the universe of their sort. A recursive type's stages are, by induction over ω (`finds2`);
- **recursors:** `lean-recty-I`, `⟦I params⟧ C_ { t | ( R ` t ) e. ( B ` t ) }` for the recursor `R` and motive `B`. Each stage is a subset by `finds2`; a constructor's tuple is in it by its computation rule and its minor premise's type;
- **recursors into `Prop`** (induction): `lean-ind-I`, from `lean-recty-I` with each minor premise, a proof, replaced by a witness of its data type: the map that is `(/)` everywhere. It is in that type because each motive value it lands in holds, by the minor premise;
- **`Eq.rec` into `Prop`** (substitution): `lean-subst-Eq`. The major premise holds, so `b = a`, and the motive at `b` is the motive at `a`.

Three small lemmas are proved once per output: `lean-tw` (what the tower hypothesis says) with `lean-tw-u`, `lean-tw-s` and `lean-tw-om`; `lean-prop`, `|- ( (/) e. if ( ph , 1o , (/) ) <-> ph )`; and `lean-pf`, `|- ( ( A e. 2o /\ B e. A ) -> (/) e. A )`, so that a member of a proposition makes it hold.

**Distinct variables.** Each lemma carries exactly the `$d` conditions its proof needs, computed by replaying the proof (`Distinct.cs`). A blanket `$d` over all its variables would stop the lemma being used with a term that binds one of them. Where a lemma needs a bound variable distinct from a class variable, the term is renamed apart first and brought back by alpha-equivalence. The replay also checks every step's hypotheses, so a broken proof fails where it is made, not in a verifier.

### Results

`tests/fixtures/theorems.ndjson` is `leanout Init -- Nat.add_zero Nat.zero_add Nat.succ_add List.length_append` (Lean 4.36.0).

| Theorem | Proof term | Lemmas (flat steps) | Theorem (flat steps) | Output (compressed) | Time |
|---|---|---|---|---|---|
| `Nat.add_zero` | `rfl`, so `n + 0` is unfolded to `n` through `Nat.add`, `Nat.brecOn`, `Nat.rec` and the literal `0` | 45 (1,147,634) | 1,665,317 | 383 KB | 6 min |
| `Nat.zero_add` | `Nat.brecOn` into `Prop`, a matcher, `congrArg`, `rfl` | 61 (22,854,344) | 69,124 | 678 KB | 15 min |

Both pass metamath-exe, mmverify.py and mmj2's `definitionCheck`, each on its own and together. CI proves both into one output (863 KB, 13 minutes here; the second reuses the first's lemmas) and runs all three checks on it.

**`Nat.succ_add` and `List.length_append` aren't proved yet.** Both get past every construct they use: induction on `Nat` and on `List α`, `Eq.rec`, `congrArg`, `congrFun'`, `propext`, `eq_self`, the literal `1`. Both then run out of `set.mm`'s 26 set variables, in the typing of `Nat.succ_add._f` and `List.append._f`, whose matchers nest binders deeper than that. PR #2 (extra set variables) lifts that limit; the translator already takes its quantified variables from set.mm's letters, so it merges with #2 as it is.

`propext` holds in the model and is typed by a lemma (`Propext.cs`): a proposition is `(/)` or `1o` (`lean-2oif`, `|- ( A e. 2o -> A = if ( (/) e. A , 1o , (/) ) )`), so two that hold together are equal.

**Refused, with the reason:** a constant that isn't a theorem; universe levels above 4; Nat literals above 10; recursors with indices or several motives (other than one-constructor propositions like `Eq`, by substitution); axioms other than `propext`; nested and mutual types (left to the model).

`Nat.add_zero`'s statement, as proved:

```
|- ( ( U e. lean.-tower /\ A e. ( lean.Nat ` U ) ) -> (/) e. ( ( ( ( lean.Eq.{1} ` U ) ` ( lean.Nat ` U ) ) `
     ( ( ( ( ( ( ( lean.HAdd.hAdd.{0,0,0} ` U ) ` ( lean.Nat ` U ) ) ` ( lean.Nat ` U ) ) ` ( lean.Nat ` U ) ) `
         ( ( ( lean.instHAdd.{0} ` U ) ` ( lean.Nat ` U ) ) ` ( lean.instAddNat ` U ) ) ) ` A ) `
       ( ( ( ( lean.OfNat.ofNat.{0} ` U ) ` ( lean.Nat ` U ) ) ` ( lean.Nat.-lit ` ( lean.Nat.-ofnum ` 0 ) ) ) `
         ( ( lean.instOfNatNat ` U ) ` ( lean.Nat.-lit ` ( lean.Nat.-ofnum ` 0 ) ) ) ) ) ) ` A ) )
```

That is, `A + 0 = A` in the model, with `+` as Lean defines it. Restating it as `( A + 0 ) = A` in `set.mm`'s arithmetic needs the bridge theorem `⟦Nat.add⟧ = +`, now possible in tower mode.

**Where the size goes.** Most of the steps are typing lemmas for the constants structural recursion goes through: `Nat.brecOn.go` (361,529 steps), `Nat.add._f` (289,688), the computation rules. `Nat.zero_add._f` alone is 20.9 million flat steps: its matcher's motive carries the whole statement, and each typing step repeats it. Compression shares the repeats (678 KB), but proving takes 15 minutes. Sharing types between steps, as Lean's kernel does, is the obvious next optimization.
