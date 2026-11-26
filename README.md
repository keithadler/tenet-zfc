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

**About 45% of the way to the goal.** The first real Lean theorems now come out of the generic model as ZFC proofs that both verifiers accept.

| | Milestone | Gate | Status |
|---|---|---|---|
| 1 | **Trace** | Replaying Tenet's trace re-derives every check it made, on all of Lean core | ✅ 64,045 declarations, 86 million steps, 0 failures |
| 2 | **Bridge library** | `2 + 2 = 4` and `List.length_append` translate, and both verifiers accept them | ✅ verified in CI |
| 3 | **Full kernel** | All of Lean core translates and verifies | 🚧 definitions mostly done; theorems started |
| 4 | **Universe elimination** | Mathlib's `Nat` and `Int` files come out in plain ZFC | 🚧 started: a universe tower (the default), and each output states the universes it uses |
| 5 | **Headline result** | A famous theorem end to end in plain ZFC, with outputs and counts published | not started |

### What works today

**Definitions.** A generic model gives every Lean constant a `set.mm` definition computed from Lean's own, with no hand-written table. Every definition passes [mmj2](https://github.com/digama0/mmj2)'s `definitionCheck`, the check `set.mm` applies to its own definitions.

| Lean | ZFC (`set.mm`) | Verified |
|---|---|---|
| `fun x => b`, application, Π-types | `( x e. A |-> B )`, `( F ` A )`, `X_ x e. A B` | definitional equations |
| `Prop`; proofs | `2o`; every proof is `(/)` (proof irrelevance) | |
| structures, enumerations (`Bool`, `Prod`, `Option`) | tagged tuples | computation rules |
| inductive propositions (`Eq`, `And`, `False`) | `if ( constructor applies , 1o , (/) )` | computation rules |
| recursive types (`Nat`, `List`, trees) | least fixed points: unions of ω-chains of stages | computation rules, e.g. `Nat.rec … (succ n) = s n (Nat.rec … n)` |
| mutual and nested types (`Lean.Syntax`) | one least fixed point over a tagged sum | computation rules |
| recursors | `set.mm`'s well-founded recursion (`frecs`) over smaller rank | via `frr2` and a one-time lemma that rank is well-founded |
| recursive propositions (`Nat.le`) | least sets of index tuples | |
| `Nat` and string literals | decimal numerals, through `_om`; lists of characters | |
| quotients, `propext`, `Classical.choice` | equivalence classes; `set.mm`'s choice | `Quot.lift`'s computation rule |
| more than 26 bound variables | set variables the output declares itself (`$v`, `$f setvar`), which add no axiom | definitional equations |

On Lean 4.36's `Init`, **13,958 of 17,590 definitions (79%)** translate together with everything they use, up from 48 when milestone 3 began.

**Theorems.** `tenet-zfc theorem` proves Lean theorems from their own proof terms, through the model. A proof's typing becomes membership, `(/) e. ⟦P⟧`, and each conversion becomes an equation.

| Theorem | Proof term | Output (compressed) | Time |
|---|---|---|---|
| `Nat.add_zero` | `rfl`, unfolding `n + 0` through `Nat.add`, `Nat.brecOn` and `Nat.rec` | 383 KB | 6 min |
| `Nat.zero_add` | `Nat.brecOn` into `Prop`, a matcher, `congrArg` | 678 KB | 15 min |

**Bridges.** The model's `Nat` is proved to be `set.mm`'s `NN0`: zero to `0`, `succ` to `+ 1`, literals to numerals, and `⟦Nat.add⟧` to `+`, with no hypotheses but the universe tower's. Lean's `Nat.add_zero` and `Nat.zero_add`, proved through the model, come out as `( A + 0 ) = A` and `( 0 + A ) = A` in `set.mm`'s arithmetic. Lean's `2 + 2 = 4`, read in the model, is proved equivalent to `set.mm`'s `( 2 + 2 ) = 4`. See [docs/bridges.md](docs/bridges.md).

**Proof size.** Proofs are written in Metamath's compressed format, sharing repeated subproofs. The largest outputs shrink by up to about 40 times compared with flat proofs.

**Universes.** With a single universe, `Nat.below` is empty, so `Nat.add` and every other function defined by structural recursion collapse in the model. The model's default is therefore a tower: an increasing sequence of Grothendieck universes, one per level, under the hypothesis `U e. lean.-tower`. ZFC doesn't prove such a tower exists, so every result holds in the models of ZFC that have one; no axiom is added. Each output's header states this, how many levels it uses and which declarations use each. `--single-universe` keeps the old model, which quotients and choice still need. See [docs/milestone3.md](docs/milestone3.md#tower-mode-as-the-default).

## Road to the first release (v0.1)

v0.1 is the first version someone else can install and use to get independently checked ZFC proofs from their own Lean code, on a stated, tested fragment.

**Definitions**
- [x] A generic model for every kind of Lean declaration: definitions, inductive types, recursors, quotients and axioms
- [x] More set variables than `set.mm`'s 26, declared by the output
- [ ] Translate the rest of `Init`'s definitions. The blockers left include `Acc`, whose premises are functions into the type, so its stages must go beyond ω.
- [ ] Verify every translated `Init` definition with all three checkers, and publish the counts ([#7](https://github.com/keithadler/tenet-zfc/pull/7), running)

**Theorems**
- [x] Prove theorems from their proof terms through the model: `Nat.add_zero`, `Nat.zero_add`
- [ ] `Nat.succ_add` and `List.length_append` through the model, replacing milestone 2's hand table. They are unblocked by the extra set variables, and next to try.
- [ ] A starter library of Init theorems about `Nat` and `List`, all verified, with sizes and times published
- [ ] Share types between proof steps, as Lean's kernel does, so that proofs take minutes, not hours

**Soundness and trust**
- [x] Tower mode as the default, so that structurally recursive definitions mean what Lean means. Quotients and choice still need `--single-universe`.
- [x] The bridge `⟦Nat.add⟧ = +` proved without hypotheses, and `Nat.add_zero`/`Nat.zero_add` restated as `( A + 0 ) = A` and `( 0 + A ) = A`
- [ ] The same for `List`/`Word`, `length`/`#` and `++`, with `List.length_append` restated as `ccatlen`
- [x] Each output's header states its assumptions: which universes it uses, and which declarations need them
- [ ] Quotients and choice in the tower model

**Release engineering**
- [x] CI on Linux, macOS and Windows; every fixture checked by metamath-exe, mmverify.py and mmj2
- [x] The full test suite passing on macOS: one test overflowed the stack there, fixed by [#2](https://github.com/keithadler/tenet-zfc/pull/2)
- [ ] One command from a Lean module to checked output: export, trace, translate, verify
- [ ] A packaged CLI (a `dotnet tool` or prebuilt binaries) and a tagged release with the verified outputs attached

**After v0.1:** universe lowering, so that results come out in plain ZFC (milestone 4); then a headline theorem end to end (milestone 5).

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
| `define <export> <set.mm> <out.mm> <name>…` | Translates constants through the generic model, with their equations and computation rules; universe parameters at 0 unless the name gives levels (`Eq.{1}`) |
| `bridge <set.mm> <out.mm>` | Writes the one-time lemmas recursive types rest on |
| `theorem <export> <set.mm> <out.mm> <name>…` | Proves Lean theorems from their proof terms, through the model, in tower mode |
| `nat-bridge <export> <set.mm> <out.mm> [n…] [theorem…]` | Proves that the model's `Nat` is `NN0` (zero, successor, literals, `Nat.add`), with `F ( n ) = n` for each numeral given; proves each theorem given through the model and restates it in `NN0` |
| `survey <export>`, `model-survey <export>` | Measure how much of an export translates, and what blocks the rest |

The model uses a tower of universes, one per level; add `--single-universe` anywhere for the old one-universe model. Proofs are compressed; add `--uncompressed` for flat ones.

To make a trace, run `tenet check <export.ndjson> --trace <trace.ndjson>` with [Tenet](https://github.com/keithadler/tenet). To make an export, run `leanout <Module> -o <out.ndjson>` with [leanout](https://github.com/keithadler/leanout).

## Repository

```
src/TenetZfc/          the replayer, the generic model, the Metamath prover and writer
  Replay.cs …          re-derives Tenet's traces (milestone 1)
  Model.cs             the generic set-theoretic model of Lean's kernel (milestone 3)
  Recursion.cs         one-time lemmas for recursive types
  Universes.cs …       the universe tower, monomorphization (Monomorph.cs), and each output's stated assumptions
  TheoremTranslator.cs theorems through the model; DefEq.cs: definitional equations as theorems
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
