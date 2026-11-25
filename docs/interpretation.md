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
| `Prop` | `2o`, which is `{ (/) , 1o }` | `df-2o`, `df2o3` |
| a proposition `p` | `1o` if `p` holds, `(/)` if not | |
| any proof of a proposition | `(/)` (proof irrelevance holds by construction) | |
| `Nat` | `_om` | `df-om`, `omex` |
| `Nat.zero` | `(/)` | `peano1` |
| `Nat.succ n` | `suc ⟦n⟧` | `df-suc`, `peano2` |
| a literal `n` | `suc` applied n times to `(/)` (the decimal library later) | |
| `Nat.add a b` | `( ⟦a⟧ +o ⟦b⟧ )` | `df-oadd`, `nna0`, `nnasuc` |
| `Nat.rec` with a constant motive | finite recursion | `df-rdg`, `fr0g`, `frsuc` |
| `(x : A) → B` | `X_ x e. ⟦A⟧ ⟦B⟧` | `df-ixp`, `elixp` |
| `fun x : A => b` | `( x e. ⟦A⟧ |-> ⟦b⟧ )` | `df-mpt`, `fvmpt` |
| `f a` | `( ⟦f⟧ ` ⟦a⟧ )` | `df-fv` |
| `@Eq α a b` | `if ( ⟦a⟧ = ⟦b⟧ , 1o , (/) )` | `df-if` |
| `Type u` where needed | `( R1 ` A )` for a large enough limit `A`, or a Grothendieck universe | `df-r1`, `df-gru`, `ax-groth` |

`Nat.add` is mapped to `+o`, not to `Nat.add`'s compiled body unfolded into recursors. Tenet already treats `Nat.add` as a primitive that satisfies `x + 0 = x` and `x + succ y = succ (x + y)`, and `nna0` and `nnasuc` are exactly those equations in `set.mm`. That correspondence is a lemma to prove once, per primitive, and it is also where the replay's "Nat operations mean what their names say" assumption gets discharged.

## What a translated theorem says

For a Lean theorem `t : P` with `P : Prop`, the output is a `set.mm` theorem `|- ⟦P⟧ = 1o`. If `P` mentions locals, it is guarded by their hypotheses. For `P` an equation `@Eq α a b`, that simplifies to `|- ⟦a⟧ = ⟦b⟧`. For `2 + 2 = 4` the output is `|- ( 2 +o 2 ) = 4`, with numerals as iterated `suc`. Whether that is the statement a mathematician means is the job of the definition table (spec, "Testing and trust"). Here the table entry is `HAdd.hAdd Nat Nat Nat instHAdd ↦ +o`, justified by unfolding the instance to `Nat.add`.

## Emission

Each replayed step becomes one or more `set.mm` proof steps citing a bridge lemma, as listed in [rule-map.md](rule-map.md):
- a reduction `a ↝ b` becomes `|- ⟦a⟧ = ⟦b⟧`;
- an equality `a ≡ b` becomes `|- ⟦a⟧ = ⟦b⟧`;
- a typing `a : T` becomes `|- ⟦a⟧ e. ⟦T⟧`.

The output is a `.mm` file that includes `set.mm` and adds only `$p` theorems. It has no new axioms, and no new definitions until a definition checker is part of the pipeline. Both verifiers must accept it.

Writing `set.mm` proofs mechanically needs one more piece of infrastructure: every `$p` proof must include the syntax proof of each term it mentions (how the class `( A +o B )` is built from `A`, `B` and `+o`). The emitter therefore parses `set.mm`'s syntax axioms and builds those proofs itself.

## Plan for the milestone 2 gate

1. **Syntax.** Parse `set.mm`'s syntax axioms and turn any class or wff term into its syntax proof. Gate: a generated theorem with a non-trivial statement passes both verifiers.
2. **Arithmetic bridge.** `|- ( A e. _om -> ( A +o (/) ) = A )` and the successor case, already `nna0` and `nnasuc`. Lemmas computing `suc`-numerals, so a `NatLitOp` step `2 + 2 ↝ 4` becomes a short chain.
3. **Instance plumbing. Done, through the definition table.** The trace unfolds `HAdd.hAdd Nat Nat Nat (instHAdd Nat instAddNat)` through `Add.add Nat instAddNat` to `Nat.add`, and `OfNat.ofNat Nat n (instOfNatNat n)` to the literal `n`. The emitter's table maps each of those forms to the same class term, `+o` and the numeral.
4. **The gate theorem. Done.** `tenet-zfc emit` replays the trace of `theorem two_add_two : 2 + 2 = 4 := rfl` (`tests/fixtures/Gate.lean`, compiled by Lean 4.36.0, exported by leanout, traced by Tenet) and writes
   `lean-two_add_two $p |- ( suc suc (/) +o suc suc (/) ) = suc suc suc suc (/)`
   with a 369-step proof. Both verifiers accept it, and CI checks it again on every push against pinned versions of `set.mm` and both verifiers.
   - **The trace is the licence.** The proof evaluates both sides, and every addition it uses must be a `NatLitOp` step of the declaration's replayed trace. Remove that step and the emitter refuses. Change the statement to `2 + 2 = 5` and it refuses.
   - **What the translation trusts:** the definition table. It's the single place the statement's meaning comes from, and it's small and checkable by hand. The same trace also carries Tenet's check of `Nat.add`'s defining equations over variables, `x + 0 ≡ x` and `x + succ y ≡ succ (x + y)`. Those are `set.mm`'s `nna0` and `nnasuc`, which is why `Nat.add` ↦ `+o` is the right entry.
5. **`List.length_append`.** This needs `List` as an inductive, `List.rec`, and the first induction proof: the start of milestone 3's fixed-point encoding.
