# tenet-zfc

**Lean 4 proofs, translated into plain ZFC set theory and checked by Metamath.**

Lean's foundation is a type theory, chosen because it is pleasant to work in. This project asks what happens if you don't care about the user: take a theorem Lean has already accepted, and produce a proof of the same statement from ZFC's axioms alone, in Metamath's [`set.mm`](https://github.com/metamath/set.mm), where verifiers a few hundred lines long can check it.

It is built on [Tenet](https://github.com/keithadler/tenet), an independent Lean 4 kernel that already re-checks all of Mathlib. Tenet does the checking; this project records each step it takes and prints the step as set theory.

> **Status: milestone 1, in progress.** Tenet records the derivation behind each declaration it accepts (`tenet check --trace`, on Tenet's main branch). This repository replays those traces without Tenet. On every committed fixture, every step re-derives (reductions, equalities, typings), and every definition and theorem is concluded by its trace. Not yet: inductive blocks as one conclusion, a full Lean-core run, and any ZFC output. See [docs/trace-format.md](docs/trace-format.md#replay).

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
```

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
