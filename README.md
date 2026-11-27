# tenet-zfc

[![CI](https://github.com/keithadler/tenet-zfc/actions/workflows/ci.yml/badge.svg)](https://github.com/keithadler/tenet-zfc/actions/workflows/ci.yml)
[![Release](https://img.shields.io/github/v/release/keithadler/tenet-zfc)](https://github.com/keithadler/tenet-zfc/releases/latest)
[![License: Apache-2.0](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

**Lean 4 proofs, turned into ZFC proofs that two independent Metamath verifiers check.**

Lean checks proofs in a dependent type theory. Most mathematicians name ZFC set theory as the foundation of mathematics. tenet-zfc connects the two mechanically: it takes a theorem Lean has accepted and produces a proof of the same statement from the axioms of ZFC, in Metamath's [`set.mm`](https://github.com/metamath/set.mm). There, verifiers a few hundred lines long, written in different languages, can check every step.

The translator itself is not trusted. If it makes a mistake, the verifiers reject the output.

**Where it stands** (v0.1.0, released 27 November 2026; about 60% of the way to the goal):

- **80% of the definitions in Lean core's `Init`** (14,091 of 17,590) translate together with everything they use.
- **28 Lean theorems** about `Nat` and `List` are proved from their own proof terms, and all three checkers accept every one.
- **Lean's `List.length_append` comes out as `set.mm`'s `ccatlen`**, next to `set.mm`'s hand-written proof of the same statement.
- **Two theorems are in plain ZFC** so far. Everything else still assumes a tower of universes as a hypothesis ([Limits](#limits)).
- **Next:** the infinitude of primes, end to end ([examples/Primes.lean](examples/Primes.lean)).

```
lean-two_add_two $p |- ( 2 + 2 ) = 4 $=
  ( c2 c4 caddc eqid 2p2e4 co eqtr4i eqtri oveq12i ) AACFZBBJJBAAAACADZKIEHBD
  G $.
```

*Lean's `theorem two_add_two : 2 + 2 = 4 := rfl`, from its kernel trace, as a `set.mm` theorem. metamath-exe and mmverify.py both accept it, in CI, on every push.*

### The headline demo: one statement, two independent proofs

Lean's `List.length_append`, translated from its proof term through tenet-zfc's model and the proved `List`/`Word` bridge, comes out as `set.mm`'s own theorem `ccatlen`, which `set.mm` proves by hand:

```
lean-ccatlen        $p |- ( ( U e. lean.-tower /\ ( A e. ( U ` (/) ) /\ B e. ( U ` (/) ) ) ) ->
                          ( ( S e. Word A /\ T e. Word B ) -> ( # ` ( S ++ T ) ) = ( ( # ` S ) + ( # ` T ) ) ) )
lean-ccatlen-setmm  $p   (the same statement, from set.mm's ccatlen)
ccatlen             $p |- ( ( S e. Word A /\ T e. Word B ) -> ( # ` ( S ++ T ) ) = ( ( # ` S ) + ( # ` T ) ) )
```

metamath-exe, mmverify.py and mmj2 accept both proofs. A corrupted proof step, `+` changed to `x.` in the statement, and a broken Lean proof are each rejected. `scripts/demo` runs it all, from the Lean source to the checkers' verdicts, in about 10 minutes; [docs/demo.md](docs/demo.md) has the commands and output. The hypotheses are the universe tower's, which every tower-mode theorem has (see [Limits](#limits)).

---

## Why it matters

- **A proof checked by Lean is not yet a ZFC proof.** Lean's logic is stronger than ZFC (Carneiro, [*The Type Theory of Lean*](https://github.com/digama0/lean-type-theory), 2019). tenet-zfc produces an explicit ZFC derivation for each theorem.
- **The trusted part becomes small and independent.** You don't have to trust Lean's kernel, [Tenet](https://github.com/keithadler/tenet), or this translator. A result is accepted when two Metamath verifiers (C and Python) accept the proof, and mmj2's definition checker accepts every definition it introduces.
- **Carneiro's model, run on real proofs.** The thesis proves on paper that Lean's type theory has a model in ZFC with a tower of inaccessible cardinals. tenet-zfc carries that construction out on Lean's actual library, one declaration at a time, and has independent verifiers check each result. This is case-by-case evidence, not a proof of the general theorem: a place where the model was unsound would show up as a Lean theorem whose translation the verifiers reject. So far every rejection has been a bug in the translator or a construct it doesn't cover.
- **"How much of mathematics needs more than ZFC?"** becomes a measurement. Each result will be reported as plain ZFC, or as ZFC plus a universe along with the declarations that needed it.

## Status

**About 60% of the way to the goal.** [v0.1.0](https://github.com/keithadler/tenet-zfc/releases/tag/v0.1.0) is released: the first version someone else can install and run on their own Lean code. Milestones 1 and 2 are done. Milestone 3 has most of Lean core's definitions and a first library of theorems; what it lacks is a measurement of how many of core's theorems go through. Milestones 4 and 5 are started.

| | Milestone | Gate | Status |
|---|---|---|---|
| 1 | **Trace** | Replaying Tenet's trace re-derives every check it made, on all of Lean core | ✅ 64,045 declarations, 86 million steps, 0 failures |
| 2 | **Bridge library** | `2 + 2 = 4` and `List.length_append` translate, and both verifiers accept them | ✅ verified in CI |
| 3 | **Full kernel** | All of Lean core translates and verifies | 🚧 about 75%: 80% of `Init`'s definitions translate; 28 `Init` theorems proved through the model; the share of `Init`'s 45,588 theorems that goes through is not measured yet |
| 4 | **Universe elimination** | Mathlib's `Nat` and `Int` files come out in plain ZFC | 🚧 about 15%: the first plain-ZFC theorems, `Nat.add_zero` and `Nat.zero_add` as `( A + 0 ) = A` and `( 0 + A ) = A`, from Lean's proof with no universe hypothesis and no `ax-groth` ([docs/milestone4.md](docs/milestone4.md)) |
| 5 | **Headline result** | A famous theorem end to end in plain ZFC, with outputs and counts published | 🚧 about 10%: the candidate is written, the infinitude of primes in core Lean ([examples/Primes.lean](examples/Primes.lean)); all 169 definitions it uses translate; a first run through the model found two translator gaps, and none of its theorems is proved yet |

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
| `Acc` and well-founded recursion | the intersection of every closed set (stages would need to go beyond ω); `Acc.rec` by `frecs` over it | definitional equations |
| `Nat` and string literals | decimal numerals, through `_om`; lists of characters | |
| quotients, `propext`, `Classical.choice` | equivalence classes at each level of the tower; choice from a well-ordering of the tower's union | `Quot.lift`'s computation rule, also as a conversion step; `Quot.ind`, `Quot.mk` and `Quot.lift` typed for theorems |
| more than 26 bound variables | set variables the output declares itself (`$v`, `$f setvar`), which add no axiom | definitional equations |
| more than 20 arguments | class variables the output declares itself (`AA1`, …) | computation rules |
| names with `'`, `?`, `₂`, `_@`, `«»` | escaped one-to-one into tokens and labels: `List.map'` is `lean.List.map-q` | |

On Lean 4.36's `Init`, `model-survey` counts **14,091 of 17,590 definitions (80%)** translating together with everything they use, in the tower model with quotients and choice, up from 48 when milestone 3 began. Since names are escaped and `Acc` is in the model, the latest Init-wide run translated, emitted and verified **16,565 of the 17,000 constants** in the 34 of its 40 chunks that finished, up from 13,553 in the same chunks. That includes **14,366 of 14,769 definitions (97%)** and 653 computation rules, and 33 of the 34 chunks pass all three checkers ([docs/milestone3.md](docs/milestone3.md#the-init-wide-run-again-built)).

> **A caveat on these counts.** A code review after v0.1.0 found that the script totalling a run could count a theorem in a *failed* chunk as verified ([#17](https://github.com/keithadler/tenet-zfc/pull/17) fixes it). Chunks that passed all three checkers are counted correctly, which is 33 of the 34 here. The totals will be re-run with the fixed script and all 40 chunks, and replaced.

**Theorems.** `tenet-zfc theorem` proves Lean theorems from their own proof terms, through the model. A proof's typing becomes membership, `(/) e. ⟦P⟧`, and each conversion becomes an equation.

A starter library of **28 `Init` theorems about `Nat` and `List`** is proved this way, and all three checkers accept every one. Proving all 28 takes about 8 minutes of CPU in one run, which shares their lemmas.

| | Theorems | Proof terms |
|---|---|---|
| `Nat` | `add_zero`, `zero_add`, `succ_add`, `add_succ`, `add_one`, `succ_eq_add_one`, `add_comm`, `add_assoc`, `add_left_comm`, `add_right_comm`, `pred_succ`, `pred_zero`, `sub_zero`, `succ_sub_succ`, `mul_zero`, `mul_succ`, `zero_mul` | `rfl` through `Nat.add`, `Nat.sub`, `Nat.mul` and literals; structural induction (`Nat.brecOn`, matchers); rewriting (`Eq.mpr`, `congrArg`) |
| `List` | `length_nil`, `length_cons`, `length_append`, `nil_append`, `cons_append`, `append_nil`, `append_assoc`, `map_nil`, `map_cons`, `length_map`, `reverse_nil` | `rfl` through `List.length`, `List.append`, `List.map`, `List.reverse`; induction (`List.rec`) with `simp`'s proofs (`of_eq_true`, `eq_self`, `congr`) |

Two are refused, each with its reason: `Nat.succ_ne_zero` and `Nat.le_refl`. Sizes, times and reasons are in [docs/milestone3.md](docs/milestone3.md#results-a-starter-library).

**Bridges.** The model's `List A` is proved to be `set.mm`'s `Word A`, by a bijection taking nil to `(/)` and `cons a l` to `( <" a "> ++ l )`, with `List.length` as `#` and `List.append` (Lean's `++`) as `set.mm`'s `++`; through it, Lean's `List.length_append` is `set.mm`'s `ccatlen` (above). The model's `Nat` is proved to be `set.mm`'s `NN0`: zero to `0`, `succ` to `+ 1`, literals to numerals, and `⟦Nat.add⟧` to `+`, with no hypotheses but the universe tower's. Lean's `Nat.add_zero` and `Nat.zero_add`, proved through the model, come out as `( A + 0 ) = A` and `( 0 + A ) = A` in `set.mm`'s arithmetic. Lean's `2 + 2 = 4`, read in the model, is proved equivalent to `set.mm`'s `( 2 + 2 ) = 4`. See [docs/bridges.md](docs/bridges.md).

**Proof size.** Proofs are written in Metamath's compressed format, sharing repeated subproofs. The largest outputs shrink by up to about 40 times compared with flat proofs.

**Universes.** With a single universe, `Nat.below` is empty, so `Nat.add` and every other function defined by structural recursion collapse in the model. The model's default is therefore a tower: an increasing sequence of Grothendieck universes, one per level, under the hypothesis `U e. lean.-tower`. ZFC doesn't prove such a tower exists, so every result holds in the models of ZFC that have one; no axiom is added. Each output's header states this, how many levels it uses and which declarations use each. Quotients and `Classical.choice` are in the tower too; an output that uses choice also states that it takes a well-ordering of the tower's union as a parameter. `--single-universe` keeps the old model for comparison. See [docs/milestone3.md](docs/milestone3.md#tower-mode-as-the-default) and [quotients and choice in the tower](docs/milestone3.md#quotients-and-choice-in-the-tower-built).

## Roadmap

### Next: toward the headline theorem

The work between here and a famous theorem end to end, in order:

- [x] **Pick the theorem and write it for the translator.** The infinitude of primes (Euclid) in core Lean, with no mathlib, structural recursion only, and no `omega`, `decide` or `simp`: [examples/Primes.lean](examples/Primes.lean). `set.mm` proves the same fact by hand (`infpn`), so the result can meet an independent proof, as `ccatlen` does. Its cone is 169 definitions, all of which translate, and 146 theorems ([examples/README.md](examples/README.md)).
- [ ] **Prove its theorems through the model.** A workflow runs `tenet-zfc run` on the file on GitHub's runners and reports each theorem as proved, refused or failed. The first run (27 November): both definitions verify; the four lemmas stop at one translator bug, a distinct-variable clash when rewriting under a quantifier; the main theorem is refused because eliminating an existential (`Exists.rec`) has no typing lemma yet. Those two are the work list.
- [ ] **Measure theorem coverage on all of `Init`.** 28 hand-picked theorems go through; the share of all 45,588 is unknown, and it decides the timeline.
- [ ] **More bridges**, so results land in `set.mm`'s own vocabulary: `Nat.mul` to `x.`, order to `<_` and `<`, `∣` to `||`, `Prime` to the statement in `infpn`; `Int` to `ZZ`.
- [ ] **Plain ZFC for theorems in general** (milestone 4, below): `ccatlen` first, then the headline theorem, with no universe hypothesis.
- [ ] **Finish `Init`'s definitions**: all 40 chunks now finish on GitHub's runners, and **17,329 of 17,590 definitions (98.5%)** translate with verified equations ([docs/milestone3.md](docs/milestone3.md#the-init-wide-run-on-githubs-runners-built)). Left: 256 definitions too large for mmj2's check, 11 witness `$d` refusals, and `Acc.rec`'s computation rule.

Runs of this size happen on GitHub's runners: `.github/workflows/init-run.yml` translates and checks all of `Init` across parallel jobs ([#16](https://github.com/keithadler/tenet-zfc/pull/16)).

### v0.1.0 (released)

v0.1 is the first version someone else can install and use to get independently checked ZFC proofs from their own Lean code, on a stated, tested fragment. [Release notes and binaries](https://github.com/keithadler/tenet-zfc/releases/tag/v0.1.0).

**Definitions**
- [x] A generic model for every kind of Lean declaration: definitions, inductive types, recursors, quotients and axioms
- [x] More set variables than `set.mm`'s 26, declared by the output
- [x] Every Lean name as a `set.mm` token: `'`, `?`, Unicode, `_@` and `«»` escaped one-to-one (3,397 constants were refused for their names alone)
- [x] `Acc` and well-founded recursion: least fixed points as the intersection of the closed sets, `Acc.rec` by `frecs` over them (its computation rule is not done yet)
- [ ] Translate the rest of `Init`'s definitions (carried over to the list above). In the 34 of 40 chunks of the latest run, 14,366 of 14,769 definitions (97%) translate with verified equations. What is left: chunks 33 and 35–39; definitions too large for mmj2's check (218); choice and quotients in chunks translated before they came to the tower (200); time-outs (28) ([docs/milestone3.md](docs/milestone3.md#the-init-wide-run-again-built))
- [x] Verify every translated `Init` definition with all three checkers, and publish the counts: 15,958 equations and 471 computation rules verified, none rejected ([docs/milestone3.md](docs/milestone3.md#the-init-wide-run-built))

**Theorems**
- [x] Prove theorems from their proof terms through the model: `Nat.add_zero`, `Nat.zero_add`
- [x] `Nat.succ_add` and `List.length_append` through the model, replacing milestone 2's hand table
- [x] A starter library of Init theorems about `Nat` and `List`, all verified, with sizes and times published: 28 theorems, in [docs/milestone3.md](docs/milestone3.md#results-a-starter-library)
- [x] Share types between proof steps, as Lean's kernel does, so that proofs take minutes, not hours: shared subproofs, memoized typing and a faster parser (`Nat.add_zero` 209 s → 6 s)

**Soundness and trust**
- [x] Tower mode as the default, so that structurally recursive definitions mean what Lean means
- [x] The bridge `⟦Nat.add⟧ = +` proved without hypotheses, and `Nat.add_zero`/`Nat.zero_add` restated as `( A + 0 ) = A` and `( 0 + A ) = A`
- [x] The same for `List`/`Word`, `length`/`#` and `++`, with `List.length_append` restated as `ccatlen`: two independent proofs of one ZFC statement, and sabotage checks ([docs/demo.md](docs/demo.md))
- [x] Each output's header states its assumptions: which universes it uses, and which declarations need them
- [x] Quotients and choice in the tower model, so every output uses one model: `Quot.{k}` at each level, choice from one well-ordering of the tower's union, stated in the header ([docs/milestone3.md](docs/milestone3.md#quotients-and-choice-in-the-tower-built))

**Release engineering**
- [x] CI on Linux, macOS and Windows; every fixture checked by metamath-exe, mmverify.py and mmj2
- [x] The full test suite passing on macOS: one test overflowed the stack there, fixed by [#2](https://github.com/keithadler/tenet-zfc/pull/2)
- [x] One command from a Lean module to checked output: `tenet-zfc run` exports, traces, translates and verifies, and reports on each declaration
- [x] A packaged CLI (a `dotnet tool` and prebuilt binaries for Linux, macOS and Windows), and a release workflow that attaches the verified outputs; [CHANGELOG.md](CHANGELOG.md) and [CONTRIBUTING.md](CONTRIBUTING.md)
- [x] v0.1.0 tagged and released, with the package, binaries for three platforms and the verified outputs attached

### Later milestones

- Milestone 4, universe elimination ([docs/milestone4.md](docs/milestone4.md)):
  - [x] A lowered tower of weak universes, proved in ZFC to exist (`lean-wit-tw`), and the first plain-ZFC theorem, `Nat.add_zero`, with `scripts/check-axioms` in CI
  - [ ] Recursive types with parameters, then `List.length_append` as `ccatlen` in plain ZFC
  - [ ] `--lowered` for `theorem`, `define` and `define-all`, with a survey of what lowers
  - [ ] The reflection schema in `set.mm`, for unions over type families; lowering as the default, with the tower as a reported fallback
  - [ ] Gate: mathlib's `Nat` and `Int` files in plain ZFC
- Milestone 5: the headline theorem end to end in plain ZFC, with its outputs and counts published.

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

**What the verifiers can't catch** is a definition that is well-formed but doesn't mean what Lean means, or a report that counts wrongly. Those are found by reading. An independent code review after v0.1.0 found one of each: a recursor that passed the wrong argument for one rare kind of inductive proposition, with a computation rule that verified only because its hypothesis was false, and totals that could count a theorem in a failed chunk as verified. Both are fixed in [#17](https://github.com/keithadler/tenet-zfc/pull/17); the affected construct is now refused until it is modelled properly.

## What it does and doesn't show

A Metamath check proves *the translated statement*. Whether that statement is the theorem you care about is a separate question, and often the harder one.

The translator unfolds Lean's own definitions of ℕ, ℝ, ζ and the rest into sets mechanically, so nobody has to write the Riemann Hypothesis in ZFC by hand. What it can't decide automatically is whether the resulting formula is the statement a mathematician means. Bridge theorems in `set.mm` answer that question for headline results: for example, that the model's `Nat` and its addition are `set.mm`'s `NN0` and `+`. See [Testing and trust](docs/spec.md#testing-and-trust).

## Limits

- **Never supported:** `sorry`, and `native_decide`, which trusts compiled code rather than a kernel proof. A project's own axioms can only appear as hypotheses.
- **Mostly not plain ZFC, yet:** by default every output assumes a tower of Grothendieck universes, `U e. lean.-tower`, as a hypothesis. No axiom is added, and each output's header says how many levels it uses, which declarations need them, and whether any theorem is plain ZFC. What uses `Classical.choice` also takes a well-ordering `W` of the tower's union as a parameter, and a theorem that needs choice to pick an element has the hypothesis `W We U. ran U`, which ZFC can discharge (`weth`). With `--lowered` (milestone 4, [docs/milestone4.md](docs/milestone4.md)) the tower is made of weak universes, which ZFC proves exist, and the hypothesis is discharged: so far for `nat-bridge`, where `Nat.add_zero` comes out as `|- ( A e. NN0 -> ( A + 0 ) = A )`, checked by `scripts/check-axioms` to use no `ax-groth`. Recursive types with parameters (`List α`), unions over type families, and statements over all types aren't lowered yet. Theorems whose proofs genuinely need a universe will stay "ZFC plus universes".
- **Refused, with a reason:** what the model doesn't cover yet is reported per declaration, never translated approximately. Examples: an inductive proposition with a data field that eliminates into data; a proposition with several constructors that eliminates into any sort; universe levels above 4.
- **Not measured yet:** how much of Lean core's *theorems* go through. The 80% figure is definitions.
- **Impractical:** computation-heavy proofs such as large `decide` calls translate in principle, but each kernel evaluation step becomes explicit proof steps.
- **Not readable:** the outputs are machine-checked certificates, not mathematics to read.

## Quick start

### Install

Requirements: [.NET](https://dotnet.microsoft.com) 8 or 10 for the `dotnet tool` (the prebuilt binaries need nothing), plus the checkers: [`set.mm`](https://github.com/metamath/set.mm), [metamath-exe](https://github.com/metamath/metamath-exe), [mmverify.py](https://github.com/david-a-wheeler/mmverify.py) with Python 3, and [mmj2](https://github.com/digama0/mmj2) with Java 11. To start from Lean code you also need Lean through [elan](https://github.com/leanprover/elan), and [leanout](https://github.com/keithadler/leanout); [Tenet](https://github.com/keithadler/tenet) is optional. [CONTRIBUTING.md](CONTRIBUTING.md#set-up-the-checkers) sets them up at the versions CI pins.

```bash
# From a release: the .nupkg (or a binary for linux-x64, osx-arm64 or win-x64) is attached to each GitHub Release
dotnet tool install -g tenet-zfc --add-source <directory holding tenet-zfc.<version>.nupkg> --version <version>

# Or from source
dotnet run --project src/TenetZfc.Cli -c Release -f net10.0 -- --version
```

### One command: a Lean file to checked ZFC proofs

[`tests/fixtures/Example.lean`](tests/fixtures/Example.lean) declares an enumeration, a function on it, a polymorphic definition and a theorem:

```lean
inductive Color where
  | red | green | blue

def Color.next : Color → Color
  | .red => .green
  | .green => .blue
  | .blue => .red

def twice (f : α → α) (x : α) : α := f (f x)

theorem two_add_two : 2 + 2 = 4 := rfl
```

Tell `tenet-zfc` where the tools are, with flags or environment variables (`tenet-zfc run --help` lists them; programs on the PATH are found by themselves), and run it:

```bash
export TENET_ZFC_SETMM=~/mm/setmm TENET_ZFC_METAMATH=~/mm/metamath TENET_ZFC_MMVERIFY=~/mm/mmverify/mmverify.py \
       TENET_ZFC_MMJ2=~/mm/mmj2 TENET_ZFC_LEANOUT=~/leanout/.lake/build/bin/leanout TENET_ZFC_TENET=~/tenet/tenet
tenet-zfc run tests/fixtures/Example.lean --out example-out
```

```
tenet-zfc run: tests/fixtures/Example.lean -> example-out
  compile    lean: tests/fixtures/Example.lean -> build/Example.olean (2.7s)
  export     leanout: Example -> export.ndjson (0.8s)
  select     8 declarations: 1 theorem, 7 others
  trace      tenet: 1 theorem re-checked -> trace.ndjson (0.2s)
  replay     1 declaration, 271 steps re-derived without Tenet, 0 failures
  translate  from traces: 1 of 1 theorem -> trace-theorems.mm
  translate  define: 7 of 7 -> definitions.mm
  verify     trace-theorems.mm: metamath-exe ok (2s), mmverify.py ok (7s), mmj2 definitionCheck ok (0s)
  verify     definitions.mm: metamath-exe ok (2s), mmverify.py ok (9s), mmj2 definitionCheck ok (40s)

  declaration  kind         result      output / reason
  Color        inductive    proved      definitions.mm (through the model)
  Color.blue   constructor  proved      definitions.mm (through the model)
  Color.green  constructor  proved      definitions.mm (through the model)
  Color.next   definition   proved      definitions.mm (through the model)
  Color.rec    recursor     proved      definitions.mm (through the model)
  Color.red    constructor  proved      definitions.mm (through the model)
  twice        definition   proved      definitions.mm (through the model)
  two_add_two  theorem      proved      trace-theorems.mm (from its trace)  |- ( 2 + 2 ) = 4

  8 proved, 0 refused, 0 failed. Outputs, logs and report.json are in example-out.
  proved: translated, and its output passed metamath-exe, mmverify.py and mmj2's definitionCheck against ~/mm/setmm/set.mm.
```

What each step does:

1. **Compile and export.** `lean` compiles the file; leanout exports the module and everything it uses. `run` lists the declarations the module itself declares, leaving out what Lean generates around them (`casesOn`, `noConfusion`, …; `--all` keeps them, `--decl a,b` picks).
2. **Trace.** When Tenet is found, it re-checks the theorems and records its derivations; `tenet-zfc` replays them without Tenet.
3. **Translate.** Theorems the milestone 2 translator covers are proved from their traces, as statements in `set.mm`'s own vocabulary. Other theorems go through the model (`tenet-zfc theorem`), each under a time limit (`--timeout`, 30 minutes by default). Everything else goes through `define`: for a definition, its definitional equation is proved; for an inductive type, its constructors' computation rules. The model is the tower of universes by default, and each output's header states what it assumes; `--single-universe` picks the one-universe model.
4. **Verify.** Every output must pass metamath-exe, mmverify.py and mmj2's definitionCheck. The verifiers check the proofs the output adds, as `scripts/verify-all` does; `set.mm`'s own proofs are checked once, apart (CI checks `set.mm` itself with both).
5. **Report.** Each declaration is **proved** (translated, and the output passed all three checks), **refused** (outside what the translator covers, with the reason), or **failed** (a checker rejected the output, or the translator crashed: a bug to report). `report.json`, the outputs and every tool's log are in the `--out` directory. The exit status is 0 only when every declaration was proved (with `--no-verify`, translated).

For a module in a Lake project, run it under `lake env` so that `LEAN_PATH` reaches the project's `.olean` files: `lake env tenet-zfc run MyProject.Basic`. An existing export works too: `tenet-zfc run export.ndjson --decl Nat.add`.

### The commands underneath

```bash
# The milestone 2 gate: 2 + 2 = 4 from its trace
tenet-zfc emit tests/fixtures/gate.ndjson tests/fixtures/gate.trace.ndjson set.mm gate.mm
tenet-zfc verify gate.mm        # or: metamath "read gate.mm" "verify proof *" exit; python3 mmverify.py gate.mm

# The generic model: Nat, its constructors and recursor, and their computation rules
tenet-zfc define tests/fixtures/recursive.ndjson set.mm rec.mm Nat Nat.zero Nat.succ Nat.rec
scripts/check-definitions java path/to/mmj2 rec.mm
```

| Command | What it does |
|---|---|
| `run <Module \| File.lean \| export>` | Export, trace, translate and verify in one command, with a report on each declaration |
| `verify <out.mm>…` | Checks outputs with metamath-exe, mmverify.py and mmj2's definitionCheck |
| `replay <export> <trace>` | Re-derives every step of a Tenet trace, without Tenet |
| `emit <export> <trace> <set.mm> <out.mm>` | Writes `set.mm` theorems for the theorems the milestone 2 translator covers |
| `define <export> <set.mm> <out.mm> <name>…` | Translates constants through the generic model, with their equations and computation rules; universe parameters at 0 unless the name gives levels (`Eq.{1}`) |
| `bridge <set.mm> <out.mm>` | Writes the one-time lemmas recursive types rest on |
| `theorem <export> <set.mm> <out.mm> <name>…` | Proves Lean theorems from their proof terms, through the model, in tower mode; universe parameters are 0 unless a name gives levels (`'Quot.inductionOn.{1}'`) |
| `nat-bridge <export> <set.mm> <out.mm> [n…] [theorem…]` | Proves that the model's `Nat` is `NN0` (zero, successor, literals, `Nat.add`), with `F ( n ) = n` for each numeral given; proves each theorem given through the model and restates it in `NN0`; with `--lowered`, also in plain ZFC, with no universe hypothesis |
| `list-bridge <export> <set.mm> <out.mm>` | Proves that the model's `List A` is `Word A`, with `List.length` as `#` and `List.append` as `++`, and restates `List.length_append` as `ccatlen` |
| `survey <export>`, `model-survey <export>` | Measure how much of an export translates, and what blocks the rest |

The model uses a tower of universes, one per level; add `--single-universe` anywhere for the old one-universe model. Proofs are compressed; add `--uncompressed` for flat ones.

The lower-level commands take an export and, for `emit` and `replay`, a trace. To make an export, run `leanout <Module> -o <out.ndjson>` with [leanout](https://github.com/keithadler/leanout); to make a trace, run `tenet check <export.ndjson> --trace <trace.ndjson>` with [Tenet](https://github.com/keithadler/tenet).

## Repository

```
src/TenetZfc/          the replayer, the generic model, the Metamath prover and writer
  Replay.cs …          re-derives Tenet's traces (milestone 1)
  Model.cs             the generic set-theoretic model of Lean's kernel (milestone 3)
  Recursion.cs         one-time lemmas for recursive types
  Universes.cs …       the universe tower, monomorphization (Monomorph.cs), and each output's stated assumptions
  TheoremTranslator.cs theorems through the model; DefEq.cs: definitional equations as theorems
  NatBridge.cs         bridge theorems: the model's Nat is NN0; ListBridge.cs: its List is Word
  DefineAll.cs         a whole export in chunks, for runs over all of Init
  ProofKit.cs          a small tactic layer for writing set.mm proofs in C#
  Typing.cs            type inference, for proof irrelevance
  Metamath.cs          reads set.mm, parses its syntax, assembles and compresses proofs
src/TenetZfc.Cli/      the tenet-zfc command; Run.cs is `tenet-zfc run`, Checkers.cs the three checkers
tests/                 unit tests and fixtures exported from Lean 4.36.0
examples/              Primes.lean: the candidate headline theorem, the infinitude of primes in core Lean
scripts/               check-definitions (mmj2's definitionCheck), check-axioms (plain ZFC), verify-all and
                       summarize-all (Init-wide runs), demo (the ccatlen demo with its sabotage checks)
.github/workflows/     ci.yml (every push), release.yml (on a v* tag), headline.yml (the primes proof through the model)
docs/                  spec, design and status
```

## Documents

- [docs/spec.md](docs/spec.md): goals, architecture, milestones and risks
- [docs/milestone3.md](docs/milestone3.md): the generic model, step by step, with measurements
- [docs/milestone4.md](docs/milestone4.md): universe elimination: what the outputs use from universes, and the plain-ZFC route
- [docs/demo.md](docs/demo.md): the headline demo, `List.length_append` as `ccatlen`, with sabotage checks
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
