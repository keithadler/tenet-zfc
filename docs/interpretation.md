# Interpretation: Lean terms as `set.mm` classes (milestone 2 design)

Milestone 2 turns replayed traces into `set.mm` proofs. This document fixes how each Lean term becomes a set-theoretic term, which `set.mm` definitions it uses, and what a translated theorem states. Nothing here is implemented yet. The labels are from `set.mm` on its `develop` branch as of 2026-11-25.

## Tools

- `set.mm`, 52 MB, CC0. Both verifiers accept all of it: `metamath-exe` in 3.5 s, `mmverify.py` in 17 s.
- Verifier 1: `metamath-exe` (C), built from source.
- Verifier 2: `mmverify.py` (Python), written independently of the first.

Both were checked on a small database to accept a correct proof and reject a wrong one. A check that has only ever been seen to pass proves nothing. One quirk: `metamath-exe` prints `All proofs in the database were verified` even after it has printed `?Error`, so automation must fail on any `?Error` line. `mmverify.py` exits with status 1 on failure.

## A correction to the spec: universes

The spec said level-0 types would live in `Vω`, the hereditarily finite sets. That's wrong: `ℕ` itself isn't hereditarily finite, so `Nat : Type` has no home in `Vω`. In Carneiro's model each universe `Type u` is interpreted as a set closed under everything Lean can build at that level, including Π-types over infinite sets, so it has to be a Grothendieck universe. That's what makes Lean's logic stronger than ZFC.

Plain ZFC is reachable in two ways, and the translator will use both:

1. **Shallow translation of what a theorem mentions.** A constant applied to all its arguments is translated as a class term built from its arguments, not as a set-function on a universe. `@Eq Nat a b` becomes `if ( A = B , 1o , (/) )`, not an element of `X_ α ∈ U ...`. Most statements and most proofs about ordinary mathematics then never need `⟦Type⟧` as a set.
2. **Bounded universes where one is needed.** When a proof really quantifies over types, `⟦Type 0⟧` becomes `( R1 ` A )` for a limit ordinal `A` large enough for that proof (the reflection argument of milestone 4). Only when no such bound can be found does the output use `set.mm`'s Grothendieck axiom (`ax-groth`) and say so in its header.

Milestone 2's gate theorems (`2 + 2 = 4`, `List.length_append`) need only the first.

## The interpretation

⟦e⟧ is a `set.mm` class term. Free variables of Lean terms (the trace's locals) become `set.mm` set variables, with a hypothesis `x e. ⟦T⟧` for each local `x : T`.

| Lean | `set.mm` | Labels |
|---|---|---|
| `Prop` | `2o`, which is `{ (/) , 1o }`, when a proposition is used as a value | `df-2o`, `df2o3` |
| a proposition `p` in a statement | a wff (see step 5 of the plan) | |
| any proof of a proposition | `(/)` (proof irrelevance holds by construction) | |
| `Nat` | `NN0`, the natural numbers inside the complex numbers | `df-n0`, `nn0ind` |
| `Nat.zero` | `0` | |
| `Nat.succ n` | `( ⟦n⟧ + 1 )` | |
| a literal `n` | a decimal numeral: a digit, or `; A B` for 10A + B | `df-dec` |
| `Nat.add a b` | `( ⟦a⟧ + ⟦b⟧ )` | `2p2e4` and the digit table, `decadd` |
| `Nat.rec` | recursion on `NN0` | `seq`, `om2uzrdg` |
| `List α` | `Word ⟦α⟧`, finite sequences | `df-word` |
| `List.nil` | `(/)` | `ccatlid` |
| `List.cons a l` | `( <" ⟦a⟧ "> ++ ⟦l⟧ )` | `df-s1`, `df-concat` |
| `List.length l` | `( # ` ⟦l⟧ )` | `lencl`, `hashs1` |
| `l ++ m` | `( ⟦l⟧ ++ ⟦m⟧ )` | `ccatlen`, `ccatass` |
| `(x : A) → B` | `X_ x e. ⟦A⟧ ⟦B⟧` | `df-ixp`, `elixp` |
| `fun x : A => b` | `( x e. ⟦A⟧ |-> ⟦b⟧ )` | `df-mpt`, `fvmpt` |
| `f a` | `( ⟦f⟧ ` ⟦a⟧ )` | `df-fv` |
| `@Eq α a b` | `if ( ⟦a⟧ = ⟦b⟧ , 1o , (/) )` | `df-if` |
| `Type u` where needed | `( R1 ` A )` for a large enough limit `A`, or a Grothendieck universe | `df-r1`, `df-gru`, `ax-groth` |

**Why `NN0` and not `ω`.** The first version mapped `Nat` to the finite ordinals `ω`, with `+o` for addition, because `nna0` and `nnasuc` are exactly `Nat.add`'s defining equations. Two things favour `set.mm`'s `NN0` instead:
- **Lists.** `set.mm`'s theory of finite sequences (`Word`, `++`, `#`) measures lengths in `NN0`, so `List.length` lands there anyway.
- **Numerals.** `NN0` has decimal numerals and a decimal-arithmetic toolkit, which the spec otherwise had to build. With `ω`, `7 + 5` took 1,924 proof steps over iterated `suc`; on `NN0` it is the table theorem `7p5e12`.

`Nat.add` is mapped to `+`, not to its compiled body unfolded into recursors. Tenet checks, once per environment, that `Nat.add` satisfies `x + 0 = x` and `x + succ y = succ (x + y)`, and those equations hold of `+` on `NN0` (`addrid`, `addass`). That correspondence is a lemma to prove once per primitive, and it is where the replay's "Nat operations mean what their names say" assumption gets discharged.

## What a translated theorem says

For a Lean theorem `t : P` with `P : Prop`, the output is a `set.mm` theorem `|- ⟦P⟧ = 1o`. If `P` mentions locals, it is guarded by their hypotheses. For `P` an equation `@Eq α a b`, that simplifies to `|- ⟦a⟧ = ⟦b⟧`. For `2 + 2 = 4` the output is `|- ( 2 + 2 ) = 4`. That is word for word `set.mm`'s own theorem `2p2e4`, the kind of cross-check the spec asks for. Whether a translated statement means what a mathematician means is the job of the definition table (spec, "Testing and trust"). Here the table entry is `HAdd.hAdd Nat Nat Nat (instHAdd Nat instAddNat) ↦ +`, justified by the trace unfolding the instance to `Nat.add`.

## Emission

Each replayed step becomes one or more `set.mm` proof steps citing a bridge lemma, as listed in [rule-map.md](rule-map.md):
- a reduction `a ↝ b` becomes `|- ⟦a⟧ = ⟦b⟧`;
- an equality `a ≡ b` becomes `|- ⟦a⟧ = ⟦b⟧`;
- a typing `a : T` becomes `|- ⟦a⟧ e. ⟦T⟧`.

The output is a `.mm` file that includes `set.mm` and adds only `$p` theorems. It has no new axioms, and no new definitions until a definition checker is part of the pipeline. Both verifiers must accept it.

Writing `set.mm` proofs mechanically needs one more piece of infrastructure: every `$p` proof must include the syntax proof of each term it mentions (how the class `( A +o B )` is built from `A`, `B` and `+o`). The emitter therefore parses `set.mm`'s syntax axioms and builds those proofs itself.

## Plan for the milestone 2 gate

1. **Syntax. Done.** `src/TenetZfc/Metamath.cs` reads `set.mm` (121,309 statements and 1,485 syntax axioms, in 0.9 s), parses any class or wff expression with the syntax axioms, and assembles a proof from an assertion, a substitution and the proofs of its hypotheses, filling in every syntax subproof. It refuses a hypothesis that doesn't match before any verifier sees it.
2. **Arithmetic bridge. Done for single digits.** `Bridge.Add(a, b)` proves `|- ( ⟦a⟧ + ⟦b⟧ ) = ⟦a + b⟧` from `set.mm`'s addition table (`2p2e4`, `7p5e12`, …). The other order comes through `addcomi`, and the zero cases through `addrid` and `addlid`. Multi-digit sums need `set.mm`'s `decadd` toolkit, which isn't wired in yet; until then the emitter says so and emits nothing. (An earlier version on `ω` proved `( a +o b ) = a+b` by iterated `nnasuc`, which took 1,924 steps for `7 + 5`.)
3. **Instance plumbing. Done, through the definition table.** The trace unfolds `HAdd.hAdd Nat Nat Nat (instHAdd Nat instAddNat)` through `Add.add Nat instAddNat` to `Nat.add`, and `OfNat.ofNat Nat n (instOfNatNat n)` to the literal `n`. The emitter's table maps each of those forms to the same class term, `+o` and the numeral.
4. **The gate theorem. Done.** `tenet-zfc emit` replays the trace of `theorem two_add_two : 2 + 2 = 4 := rfl` (`tests/fixtures/Gate.lean`, compiled by Lean 4.36.0, exported by leanout, traced by Tenet) and writes
   `lean-two_add_two $p |- ( 2 + 2 ) = 4`
   with a 30-step proof. On the earlier `ω` encoding it was `( suc suc (/) +o suc suc (/) ) = suc suc suc suc (/)` in 369 steps. Both verifiers accept it, and CI checks it again on every push against pinned versions of `set.mm` and both verifiers.
   - **The trace is the licence.** The proof evaluates both sides, and every addition it uses must be a `NatLitOp` step of the declaration's replayed trace. Remove that step and the emitter refuses. Change the statement to `2 + 2 = 5` and it refuses.
   - **What the translation trusts:** the definition table. It's the single place the statement's meaning comes from, and it's small and checkable by hand. The same trace also carries Tenet's check of `Nat.add`'s defining equations over variables, `x + 0 ≡ x` and `x + succ y ≡ succ (x + y)`. Those hold of `+` on `NN0`, which is why `Nat.add` ↦ `+` is the right entry.
5. **`List.length_append`. Done** (see below). Its proof term (Lean 4.36, `Init.Data.List.Basic`) is an induction, `List.rec` into `Prop`, whose cases rewrite with `Nat.zero_add` and `Nat.succ_add` through `congrArg`, `congr`, `Eq.trans`, `eq_self` and `of_eq_true`. The export has 12 theorems, each with its own proof term. Emitting it takes three new pieces:
   - **Propositions as wffs.** A `Prop` in a statement is translated as a `set.mm` wff: `@Eq α a b` becomes `⟦a⟧ = ⟦b⟧`, `∀ x : A, P` becomes `A. x ( x e. ⟦A⟧ -> ⟦P⟧ )`, `True` becomes `T.`, `P → Q` becomes `( ⟦P⟧ -> ⟦Q⟧ )`. A type variable `α : Sort u` becomes a class variable.
   - **Proof terms as deductions.** Natural deduction maps onto `set.mm` directly: `fun x => p` is ∀-introduction, an application `h a` is ∀-elimination with `a`'s typing fact, `Eq.refl` is `eqid`, `Eq.trans` is `eqtr`, `congrArg f` is the equality congruence for `f`'s translation, and `of_eq_true`/`eq_self` relate a wff to `T.`. Each step's typing and definitional equalities come from the replayed trace. A conversion between definitionally equal propositions needs `⟦P⟧ <-> ⟦P'⟧`, assembled from the trace's reduction steps.
   - **Induction on lists.** `List.rec` into `Prop` becomes induction on `Word`. `set.mm`'s `wrdind` adds at the end of a word, while `List.rec` adds at the front, so a cons-style induction lemma is one bridge lemma to prove once.

   `set.mm` already proves `ccatlen`, the translated statement, so the result can be cross-checked as `2 + 2 = 4` was.

### Proof translation of the two cases (built)

`ProofTranslator` translates Lean proof terms into `set.mm` deductions `|- ( H -> ⟦P⟧ )`, where `H` gathers the locals' hypotheses. It covers the fragment `List.length_append`'s proof uses:
- **Fixed steps:** `of_eq_true` (via `tru`, `mpbiri`), `Eq.trans` on propositions (`bitrd`) and on values (`eqtrd`), and `eq_self` (`eqid`, `tbtru`).
- **Rewrite chains:** a tree of `congrArg`, `congr` and `congrFun'` proves `L = R` from the equations at its leaves. It becomes a chain of rewrites of `⟦L⟧` by those equations, each done by the congruence prover (`Deduction.Congruence`), ending at `⟦R⟧`. Function-valued intermediate equalities, such as `congrArg (HAdd.hAdd x) ih`, are never translated themselves; only their leaves are.
- **Definitional unfolding on the `set.mm` side:** `len nil` ↦ `0` (`hash0`), `nil ++ l` ↦ `l` (`ccatlid`), `(a :: l) ++ m` ↦ `a :: (l ++ m)` (`ccatass`), and `len (a :: l)` ↦ `len l + 1` (`ccatlen`, `s1len`, `addcomd`). These are applied until both sides agree, wherever Lean's proof relies on unfolding silently.
- **Typing:** membership facts for every term a lemma is applied to (`lencl`, `ccatcl`, `s1cld`, `nn0addcld`, `wrd0`).
- **Lemma bridges:** `Nat.zero_add` and `Nat.succ_add` come from `set.mm` facts about `+` (`addlid`, `addassd`, `addcomd`), not from translating their Lean proofs, which use `Nat.brecOn`.

Both cases of `List.length_append`'s induction are translated from its actual proof term, and both verifiers accept them:
- nil: `|- ( C e. Word A -> ( # ` ( (/) ++ C ) ) = ( ( # ` (/) ) + ( # ` C ) ) )`, 780 proof steps;
- cons: from the induction hypothesis `( # ` ( E ++ C ) ) = ( ( # ` E ) + ( # ` C ) )`, under `C e. Word A`, `D e. A` and `E e. Word A`, it proves `( # ` ( ( <" D "> ++ E ) ++ C ) ) = ( ( # ` ( <" D "> ++ E ) ) + ( # ` C ) )`, 5,722 proof steps.

The proofs are longer than they need to be: the normalizer chains a reflexivity and a transitivity step per rewrite.

### The induction, and the whole theorem (built)

`ListInduction` joins the two cases. Lean's `List.rec` adds at the front of a list and `set.mm`'s `wrdind` adds at the end of a word, so `wrdind` is applied to the motive composed with word reversal: `ψ(x) := ( C e. Word A -> φ(reverse x) )`. A general cons-induction lemma isn't needed.
- **Base:** `ψ((/))`, from the translated nil case and `rev0`.
- **Step:** `( ( y e. Word A /\ z e. A ) -> ( ψ(y) -> ψ(( y ++ <" z "> )) ) )`, from the translated cons case run with head `z` and tail `( reverse ` y )`, plus `revccat`, `revs1` and `revcl`, then reshuffled into `wrdind`'s form with `ex`.
- **Substitution hypotheses:** `( x = T -> ( ψ(x) <-> ψ(T) ) )`, from the congruence prover.
- **Conclusion:** `wrdind` at `reverse B` gives `ψ(reverse B)`, and `revrev` turns it into `φ(B)`.

The proof's conclusion must be the theorem's own statement, translated; a test that changes the stated type checks this is refused. The emitted theorem carries `$d x y z A`, `$d x y z B` and `$d x y z C` for the dummy set variables.

`tenet-zfc emit` on `List.length_append` writes

`lean-List.length_append $p |- ( ( B e. Word A /\ C e. Word A ) -> ( # ` ( B ++ C ) ) = ( ( # ` B ) + ( # ` C ) ) )`

with a 13,268-step proof translated from Lean's proof term. Both verifiers accept it, and CI emits and verifies it again on every push. That completes milestone 2's gate: both gate theorems come out of Lean as ZFC theorems that two independent verifiers accept.

**What this rests on, beyond the two verifiers and `set.mm`:**
- the definition table (`List` ↦ `Word`, `length` ↦ `#`, `++` ↦ `++`, `Nat` ↦ `NN0`, `+` ↦ `+`), cross-checked here by `ccatlen`, which states the same theorem;
- `Nat.zero_add` and `Nat.succ_add`, which come from `set.mm` facts about `+` rather than from translating their Lean proofs (those use `Nat.brecOn`);
- the translator handles this proof's fragment and this shape of induction (two lists over one type, induction on the first). Other proofs are refused with a reason.

### Statement cross-check (built)

`StatementTranslator` translates a theorem's statement into a `set.mm` statement:
- a bound variable becomes a class variable;
- a variable of type T becomes a hypothesis `x e. ⟦T⟧`;
- a type variable becomes a class variable with no hypothesis;
- a propositional premise becomes an antecedent.

`Prover.FindInstance` then searches `set.mm` for a theorem whose statement becomes the translated one under a substitution of its variables. It filters on constant symbols, then matches syntax trees, and never substitutes a term for a set variable. When it finds one, `emit` writes the translated statement with that theorem's proof. The comment says **CROSS-CHECK: the proof is set.mm's …, not a translation of Lean's proof**, and the summary counts these apart from theorems proved from their traces.

On `List.length_append` and its dependencies:

| Lean theorem | Translated statement | Found in `set.mm` |
|---|---|---|
| `List.length_append` | `( ( B e. Word A /\ C e. Word A ) -> ( # ` ( B ++ C ) ) = ( ( # ` B ) + ( # ` C ) ) )` | `ccatlen` |
| `trivial` | `T.` | `tru` |
| `Nat.zero_add` | `( A e. NN0 -> ( 0 + A ) = A )` | no (`addlid` says it over `CC`) |
| `Nat.succ_add` | `( ( A e. NN0 /\ B e. NN0 ) -> ( ( A + 1 ) + B ) = ( ( A + B ) + 1 ) )` | no |
| `Eq.symm`, `Eq.trans` | with membership hypotheses for their type variable | no (`set.mm` has no such hypotheses) |

Both verifiers accept the two cross-checked theorems. A cross-check shows the translation turns `List.length_append` into the statement a set theorist would write. Its proof is `set.mm`'s, so it says nothing about translating Lean's proof. That is still the next step: proof-term translation, which would also cover the four rows `set.mm` doesn't state in exactly this form.
