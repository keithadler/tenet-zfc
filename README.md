# tenet-zfc

**Lean 4 proofs, translated into plain ZFC set theory and checked by Metamath.**

Lean's foundation is a type theory, chosen because it is pleasant to work in. This project asks what happens if you don't care about the user: take a theorem Lean has already accepted, and produce a proof of the same statement from ZFC's axioms alone, in Metamath's [`set.mm`](https://github.com/metamath/set.mm), where verifiers a few hundred lines long can check it.

It is built on [Tenet](https://github.com/keithadler/tenet), an independent Lean 4 kernel that already re-checks all of Mathlib. Tenet does the checking; this project records each step it takes and prints the step as set theory.

> **Status: milestones 1 and 2 met.** Tenet records the derivation behind each declaration it accepts, and this repository replays it without Tenet: all of Lean 4.36.0's `Init` (64,045 declarations, 86 million steps) re-derives with 0 failures. Both of milestone 2's gate theorems come out of Lean as ZFC theorems in `set.mm` that `metamath-exe` and `mmverify.py` both accept, rechecked in CI on every push:
> - `2 + 2 = 4`, from its trace, as `|- ( 2 + 2 ) = 4`;
> - `List.length_append`, from its proof term (induction on lists, through `set.mm`'s word induction), as `|- ( ( B e. Word A /\ C e. Word A ) -> ( # ` ( B ++ C ) ) = ( ( # ` B ) + ( # ` C ) ) )`.
>
> The translation so far covers the fragment those proofs use; milestone 3 is the rest of Lean's kernel. `tenet-zfc survey` measures the gap: the milestone 2 table translates 119 of `Init`'s 45,588 theorem statements, and their proofs mention 37,118 constants. So milestone 3 replaces the table with a generic translation of every definition. Its first step is in: `tenet-zfc define` translates `id`, `Function.comp` and `Function.const` by the generic model, and both verifiers accept their definitional equations. The new definitions pass mmj2's definition checker, the one `set.mm` uses on its own. Non-recursive inductive types and inductive propositions followed (`Bool`, `Prod`, `Option`, `Eq`, `And`, `False`, …), with proof irrelevance, and their computation rules are verified. Recursive types followed (`Nat`, `List`), their recursors by `set.mm`'s well-founded recursion, with verified computation rules such as `Nat.rec … (succ n) = s n (Nat.rec … n)`. 6,481 of `Init`'s 17,590 definitions now translate; recursive propositions (`Nat.le`) and `Nat` literals are next. See [docs/interpretation.md](docs/interpretation.md) and [docs/milestone3.md](docs/milestone3.md).

## Why

- **Confidence.** A result accepted by Lean, by Tenet, and by Metamath has passed two unrelated foundations and several independently written checkers.
- **"But does it hold in ZFC?"** Lean's logic is stronger than ZFC (Carneiro, *The Type Theory of Lean*, 2019). Most mathematics doesn't use the extra strength. The translator says, for each theorem, whether its proof goes through in plain ZFC or needs extra universes, and if so which declarations forced them.

## What it does and doesn't show

A Metamath check proves *the translated statement*. Whether that statement is the theorem you care about is a separate question, and the harder one.

The translator doesn't need anyone to write the Riemann Hypothesis in ZFC's language by hand. It unfolds Lean's own definitions of ℕ, ℝ, ℂ, ζ and the rest into sets, mechanically. What it can't do automatically is show that the resulting formula is the RH a mathematician means, or that it matches `set.mm`'s independent definitions. So each headline theorem comes with a hand-checked table mapping Lean's definitions to `set.mm`'s, and a `set.mm` proof that the two statements are equivalent. Until that table exists for a theorem, the output says only "Lean's statement, transported to ZFC". See [Testing and trust](docs/spec.md#testing-and-trust).

## Pipeline

1. **Export.** Lean writes the theorem and its dependencies in kernel export format.
2. **Universe analysis.** Instantiate universe variables at 0 and find which higher universes the proof really uses.
3. **Traced checking.** Tenet re-checks the proof and records every step ([trace format](docs/trace-format.md)).
4. **Interpretation.** Lean terms become sets: types are sets, functions are set-theoretic functions, `Prop` is {∅, {∅}}.
5. **Emission.** Each step becomes a `set.mm` proof step, using a fixed bridge library with one lemma per kernel rule ([rule map](docs/rule-map.md)).
6. **Independent check.** Two Metamath verifiers, written in different languages, must both accept the output.

The core translator uses no AI. AI may draft bridge lemmas, shrink proofs or look for universe-free arguments, but anything it produces goes through the verifiers.

## Try it

```bash
tenet check Foo.ndjson --trace Foo.trace.ndjson                   # Tenet, from its main branch
dotnet run --project src/TenetZfc.Cli -- replay Foo.ndjson Foo.trace.ndjson
dotnet run --project src/TenetZfc.Cli -- emit Foo.ndjson Foo.trace.ndjson set.mm out.mm
```

`emit` writes a `.mm` file that includes `set.mm` and adds a theorem for each Lean theorem it covers. Check the file with a Metamath verifier, such as `metamath "read out.mm" "verify proof *"`.

## Documents

- [docs/spec.md](docs/spec.md): the full specification, including goals, milestones and risks
- [docs/rule-map.md](docs/rule-map.md): each of Tenet's kernel rules and the bridge lemma it needs
- [docs/trace-format.md](docs/trace-format.md): the trace format, and what replay checks so far

## Milestones

| # | Stage | Gate |
|---|---|---|
| 1 | Trace | Replaying the trace re-derives every check Tenet made, on all of Lean core |
| 2 | Bridge library | `2 + 2 = 4` and `List.length_append` translate and both verifiers accept them |
| 3 | Full kernel | All of Lean core translates and verifies |
| 4 | Universe elimination | Mathlib's `Nat` and `Int` files come out in plain ZFC |
| 5 | Headline result | A famous theorem end to end in plain ZFC, with outputs and counts published |

## License

Apache-2.0. See [LICENSE](LICENSE).
