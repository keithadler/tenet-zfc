# tenet-zfc

[![CI](https://github.com/keithadler/tenet-zfc/actions/workflows/ci.yml/badge.svg)](https://github.com/keithadler/tenet-zfc/actions/workflows/ci.yml)
[![License: Apache-2.0](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

**Lean 4 proofs, turned into ZFC proofs that two independent Metamath verifiers check.**

Lean checks proofs in a dependent type theory. Most mathematicians name ZFC set theory as the foundation of mathematics. tenet-zfc connects the two mechanically: it takes a theorem Lean has accepted and produces a proof of the same statement from the axioms of ZFC, in Metamath's [`set.mm`](https://github.com/metamath/set.mm). There, verifiers a few hundred lines long, written in different languages, can check every step.

The translator itself is not trusted. If it makes a mistake, the verifiers reject the output.

```
lean-two_add_two $p |- ( 2 + 2 ) = 4 $=
  ( c2 c4 caddc eqid 2p2e4 co eqtr4i eqtri oveq12i ) AACFZBBJJBAAAACADZKIEHBD
  G $.
```

*Lean's `theorem two_add_two : 2 + 2 = 4 := rfl`, from its kernel trace, as a `set.mm` theorem. metamath-exe and mmverify.py both accept it, in CI, on every push.*

---

## Why it matters

- **A proof checked by Lean is not yet a ZFC proof.** Lean's logic is stronger than ZFC (Carneiro, [*The Type Theory of Lean*](https://github.com/digama0/lean-type-theory), 2019). tenet-zfc produces an explicit ZFC derivation for each theorem.
- **The trusted part becomes small and independent.** You don't have to trust Lean's kernel, [Tenet](https://github.com/keithadler/tenet), or this translator. A result is accepted when two Metamath verifiers (C and Python) accept the proof, and mmj2's definition checker accepts every definition it introduces.
- **"How much of mathematics needs more than ZFC?"** becomes a measurement. Each result will be reported as plain ZFC, or as ZFC plus a universe along with the declarations that needed it.

## Status

About 40% of the way to the goal. The parts done so far:

| | Milestone | Gate | Status |
|---|---|---|---|
| 1 | **Trace** | Replaying Tenet's trace re-derives every check it made, on all of Lean core | ✅ 64,045 declarations, 86 million steps, 0 failures |
| 2 | **Bridge library** | `2 + 2 = 4` and `List.length_append` translate, and both verifiers accept them | ✅ verified in CI |
| 3 | **Full kernel** | All of Lean core translates and verifies | 🚧 in progress |
| 4 | **Universe elimination** | Mathlib's `Nat` and `Int` files come out in plain ZFC | not started |
| 5 | **Headline result** | A famous theorem end to end in plain ZFC, with outputs and counts published | not started |

**Milestone 3 so far.** A generic model gives every Lean constant a `set.mm` definition computed from Lean's own definition, with no hand-written table. Every definition passes [mmj2](https://github.com/digama0/mmj2)'s `definitionCheck`, the same check `set.mm` applies to its own definitions.

| Lean | ZFC (`set.mm`) | Verified |
|---|---|---|
| `fun x => b`, application, Π-types | `( x e. A |-> B )`, `( F ` A )`, `X_ x e. A B` | definitional equations |
| `Prop`; proofs | `2o`; every proof is `(/)` (proof irrelevance) | |
| structures, enumerations (`Bool`, `Prod`, `Option`) | tagged tuples | computation rules |
| inductive propositions (`Eq`, `And`, `False`) | `if ( constructor applies , 1o , (/) )` | computation rules |
| recursive types (`Nat`, `List`, trees) | least fixed points: unions of ω-chains of stages | computation rules, e.g. `Nat.rec … (succ n) = s n (Nat.rec … n)` |
| recursors | `set.mm`'s well-founded recursion (`frecs`) over smaller rank | via `frr2` and a one-time lemma that rank is well-founded |
| recursive propositions (`Nat.le`) | least sets of index tuples | |
| `Nat` literals | decimal numerals, through `_om` | |
| more than 26 bound variables | set variables the output declares itself (`$v`, `$f setvar`), which add no axiom | definitional equations |

On Lean 4.36's `Init`, **13,953 of 17,590 definitions** translate together with everything they use. Proofs are written in Metamath's compressed format, sharing repeated subproofs. The largest outputs shrink by up to about 40 times compared with flat proofs.

**Bridge theorems** prove that the model's `Nat` is `set.mm`'s `NN0`, from the model's definitions:
- a bijection `F` takes zero to `0`, `succ` to `+ 1` and each literal to its numeral;
- any function with `Nat.add`'s computation rules is `+` through `F`;
- Lean's `2 + 2 = 4`, read in the model, is proved equivalent to `set.mm`'s `( 2 + 2 ) = 4`.

They also prove a limit of the current one-universe model: `Nat.below` is empty, so `Nat.add` and other structurally recursive definitions don't yet satisfy their computation rules. Until milestone 4 fixes that, those rules are hypotheses. See [docs/bridges.md](docs/bridges.md).

**In progress:** strings, axioms and quotients (`Classical.choice`, `Quot`), nested and mutual types, bridge theorems for `List` and `Word`, proving Init's theorems through the model, and verifying all of Init. See [docs/milestone3.md](docs/milestone3.md) for the full design and the numbers.

## How it works

```
 Lean ──export──▶ Tenet ──trace──▶ replay ──▶ model ──▶ set.mm proof ──▶ metamath-exe ✓
                (kernel)          (no Tenet)  (ZFC)     (.mm file)    ──▶ mmverify.py ✓
                                                                      ──▶ mmj2 definitionCheck ✓
```

1. **Export.** [leanout](https://github.com/keithadler/leanout) writes a Lean theorem and everything it depends on in kernel export format.
2. **Trace.** [Tenet](https://github.com/keithadler/tenet), an independent Lean 4 kernel, re-checks the proof and records every step: each reduction, definitional equality and typing judgment. See [the trace format](docs/trace-format.md).
3. **Replay.** This repository re-derives every recorded step from its rule, sharing no code with Tenet.
4. **Model.** Lean terms become sets, following Carneiro's model: types are sets, functions are set-theoretic functions, `Prop` is `{ (/) , 1o }`. Each Lean definition becomes a `set.mm` definition, and its equations and computation rules become theorems. See [interpretation](docs/interpretation.md) and [milestone 3](docs/milestone3.md).
5. **Emit.** The output is a `.mm` file that includes `set.mm` and adds definitions and `$p` theorems only. It adds no axioms.
6. **Check.** Both verifiers and the definition checker must accept the file.

**What you trust:** a Metamath verifier, `set.mm`'s axioms, mmj2's definition checker, and the claim that the model means what Lean means. That last part is a small set of definitions, checked against `set.mm`'s own vocabulary by bridge theorems.

**What you don't trust:** Lean, Tenet, this translator, and its type inference. A bug in any of them produces a proof the verifiers reject, not a false theorem. During development, the verifiers have caught real mistakes, including a modelling error and several distinct-variable violations.

## What it does and doesn't show

A Metamath check proves *the translated statement*. Whether that statement is the theorem you care about is a separate question, and often the harder one.

The translator unfolds Lean's own definitions of ℕ, ℝ, ζ and the rest into sets mechanically, so nobody has to write the Riemann Hypothesis in ZFC by hand. What it can't decide automatically is whether the resulting formula is the statement a mathematician means. Bridge theorems in `set.mm` answer that question for headline results: for example, that the model's `Nat` and its addition are `set.mm`'s `NN0` and `+`. See [Testing and trust](docs/spec.md#testing-and-trust).

## Limits

- **Never supported:** `sorry`, and `native_decide`, which trusts compiled code rather than a kernel proof. A project's own axioms can only appear as hypotheses.
- **Not plain ZFC:** theorems whose proofs genuinely need a higher universe come out as "ZFC plus a Grothendieck universe", and the output says which declarations forced it. Today every output assumes a universe; removing that assumption is milestone 4.
- **Impractical:** computation-heavy proofs such as large `decide` calls translate in principle, but each kernel evaluation step becomes explicit proof steps.
- **Not readable:** the outputs are machine-checked certificates, not mathematics to read.

## Quick start

Requirements: [.NET](https://dotnet.microsoft.com) 8 or 10, plus [`set.mm`](https://github.com/metamath/set.mm), [metamath-exe](https://github.com/metamath/metamath-exe) and [mmverify.py](https://github.com/david-a-wheeler/mmverify.py) to check outputs. Java 11 and [mmj2](https://github.com/digama0/mmj2) are needed for the definition check. CI pins exact versions of all of them; see [`.github/workflows/ci.yml`](.github/workflows/ci.yml).

```bash
# The milestone 2 gate: 2 + 2 = 4 from its trace
dotnet run --project src/TenetZfc.Cli -- emit tests/fixtures/gate.ndjson tests/fixtures/gate.trace.ndjson set.mm gate.mm
metamath "read gate.mm" "verify proof *" exit      # fail on any ?Error line
python3 mmverify.py gate.mm
```

```bash
# The generic model: Nat, its constructors and recursor, and their computation rules
dotnet run --project src/TenetZfc.Cli -- define tests/fixtures/recursive.ndjson set.mm rec.mm Nat Nat.zero Nat.succ Nat.rec
scripts/check-definitions java path/to/mmj2 rec.mm
```

| Command | What it does |
|---|---|
| `replay <export> <trace>` | Re-derives every step of a Tenet trace, without Tenet |
| `emit <export> <trace> <set.mm> <out.mm>` | Writes `set.mm` theorems for the theorems the milestone 2 translator covers |
| `define <export> <set.mm> <out.mm> <name>…` | Translates constants through the generic model, with their equations and computation rules |
| `bridge <set.mm> <out.mm>` | Writes the one-time lemmas recursive types rest on |
| `nat-bridge <export> <set.mm> <out.mm> [n…]` | Proves that the model's `Nat` is `NN0` (zero, successor, literals, `Nat.add`), with `F ( n ) = n` for each numeral given |
| `survey <export>`, `model-survey <export>` | Measure how much of an export translates, and what blocks the rest |

To make a trace, run `tenet check <export.ndjson> --trace <trace.ndjson>` with [Tenet](https://github.com/keithadler/tenet). To make an export, run `leanout <Module> -o <out.ndjson>` with [leanout](https://github.com/keithadler/leanout).

## Repository

```
src/TenetZfc/          the replayer, the generic model, the Metamath prover and writer
  Replay.cs …          re-derives Tenet's traces (milestone 1)
  Model.cs             the generic set-theoretic model of Lean's kernel (milestone 3)
  Recursion.cs         one-time lemmas for recursive types
  NatBridge.cs         bridge theorems: the model's Nat is NN0
  ProofKit.cs          a small tactic layer for writing set.mm proofs in C#
  Typing.cs            type inference, for proof irrelevance
  Metamath.cs          reads set.mm, parses its syntax, assembles and compresses proofs
src/TenetZfc.Cli/      the tenet-zfc command
tests/                 unit tests and fixtures exported from Lean 4.36.0
scripts/               check-definitions (mmj2's definitionCheck)
docs/                  spec, design and status
```

## Documents

- [docs/spec.md](docs/spec.md): goals, architecture, milestones and risks
- [docs/milestone3.md](docs/milestone3.md): the generic model, step by step, with measurements
- [docs/bridges.md](docs/bridges.md): bridge theorems from the model to `set.mm`'s vocabulary
- [docs/interpretation.md](docs/interpretation.md): milestone 2's interpretation and the universe question
- [docs/trace-format.md](docs/trace-format.md): Tenet's trace format, and what replay checks
- [docs/rule-map.md](docs/rule-map.md): each kernel rule and the bridge lemma it needs

## Related work

- **Mario Carneiro, *The Type Theory of Lean*** (2019): the set-theoretic model followed here, and the proof that Lean's logic is consistent relative to ZFC plus inaccessible cardinals.
- **[Metamath](https://us.metamath.org) and `set.mm`:** the ZFC library and the verifiers this project targets.
- **[Dedukti](https://deducteam.github.io) and Logipedia:** translations between proof systems through the λΠ-calculus modulo rewriting, rather than into set theory.

## License

Apache-2.0. See [LICENSE](LICENSE).
