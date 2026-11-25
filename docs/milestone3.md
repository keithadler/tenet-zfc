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
