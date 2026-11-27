# Changelog

All notable changes to tenet-zfc. The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and versions follow [Semantic Versioning](https://semver.org). Until v0.1.0 is tagged, builds carry the version `0.1.0-dev`.

## Unreleased (after 0.1.0)

### Theorems across Init (milestone 3)

- **`theorem-all`**: every theorem of an export, or every Nth, through the model, in chunks with an outcome per theorem, CPU-time budgets and resuming ([docs/milestone3.md](docs/milestone3.md#theorems-across-init-built-theorem-all-measured-on-a-sample)).
- Fixes for the first blockers of the Init sample: Nat literals as arguments and of any size (`lean-litnat`); constructors of recursive propositions (`Nat.le.refl`, `Nat.le.step`); `Decidable`'s proof field in its recursor's typing; `$d` traps under binders in congruence and in instantiating a Π-proposition. Computation rules and equations declare every `$d` pair their proofs need.
- CI: `tests/fixtures/blockers.ndjson`, 32 theorems that must all prove.

### Universe elimination (milestone 4, started)

- **`--lowered`** (for `nat-bridge`): the model's universe tower is `lean.-wtower`, an increasing ω-sequence of reflecting weak universes (`lean.-wuni`), instead of Grothendieck universes. Indexed unions, which weak universes aren't closed under, are bounded: by a product for tuples, and by the reflection step `lean-wu-r` for a recursive type's stages.
- **`lean-wit-tw`**: ZFC proves a lowered tower exists (R1 at ω²·(n+1)), so a theorem whose statement doesn't mention `U` is discharged to plain ZFC. First ones: `lean-zfc-Nat.add_zero`, `|- ( A e. NN0 -> ( A + 0 ) = A )`, and `lean-zfc-Nat.zero_add`, from Lean's proofs.
- **`scripts/check-axioms`**: metamath-exe's `trace_back /axioms`, failing on `ax-groth` or a universe left in the statement; in CI.
- Each output's header says whether its theorems are plain ZFC. Design and plan: [docs/milestone4.md](docs/milestone4.md).

## [0.1.0] - unreleased

The first version meant for someone else to install and use: independently checked ZFC proofs from their own Lean code, on a stated, tested fragment. Everything below exists on `main` today; the release is tagged when the rest of the v0.1 roadmap in the README is done.

### Release engineering

- **`tenet-zfc run`**: one command from a Lean module, a `.lean` file or an export to checked output. It compiles the file with `lean`, exports with [leanout](https://github.com/keithadler/leanout), has [Tenet](https://github.com/keithadler/tenet) re-check and trace the theorems when Tenet is found, translates (theorems from their traces or through the model, everything else with `define`), checks every output with metamath-exe, mmverify.py and mmj2's definitionCheck, and reports each declaration as proved, refused (with the reason) or failed. Tools come from flags, environment variables or the PATH, with a message saying where to get each missing one. It writes `report.json` beside the outputs.
- **`tenet-zfc verify`**: the three checkers on existing outputs.
- **`tenet-zfc --version`**.
- **Packaging**: a `dotnet tool` package (`tenet-zfc`, for .NET 8 and 10), and self-contained single-file binaries for linux-x64, osx-arm64 and win-x64.
- **Release workflow** (`.github/workflows/release.yml`): on a `v*` tag, runs all of CI, builds the package and binaries, and creates a GitHub Release with them, the verified fixture outputs and the worked example's run attached.
- **CI**: the tool is packed, installed and run on Linux, macOS and Windows; the README's worked example (`tests/fixtures/Example.lean`) runs end to end, Lean to checked output.
- `CHANGELOG.md` and `CONTRIBUTING.md`.

### The headline demo: `List.length_append` as `ccatlen`

- **The `List`/`Word` bridge** (`tenet-zfc list-bridge`, [docs/bridges.md](docs/bridges.md#list-and-word)): a proved bijection `W` from the model's `List A` onto `set.mm`'s `Word A`, nil to `(/)` and `cons a l` to `( <" a "> ++ ( W ` l ) )`; `List.length` is `#` and `List.append` and `HAppend.hAppend` are `++` through it, with `List.length`'s and `List.append`'s computation rules proved from their definitions.
- **Two independent proofs of one ZFC statement**: Lean's `List.length_append`, proved through the model from its proof term and restated through the bridges, is `lean-ccatlen`, whose consequent is `set.mm`'s `ccatlen` token for token; `lean-ccatlen-setmm` proves the same statement from `set.mm`'s hand-written `ccatlen`. All three checkers accept both.
- **`scripts/demo`** ([docs/demo.md](docs/demo.md)) runs it end to end with sizes and times, plus sabotage checks (a corrupted proof step, `+` changed to `x.`, a broken Lean proof), each rejected. CI runs it weekly and by hand (job `demo`); the bijection alone is checked on every push.

### Milestone 3: the full kernel (in progress)

**The generic model** (`src/TenetZfc/Model.cs`, [docs/milestone3.md](docs/milestone3.md)) gives every Lean constant a `set.mm` definition computed from Lean's own, with no hand-written table, and proves its equations and computation rules. Every definition passes mmj2's `definitionCheck`.

- λ-abstraction, application and Π-types as `( x e. A |-> B )`, `( F ` A )` and `X_ x e. A B`; `Prop` as `2o`, every proof as `(/)`.
- Structures and enumerations as tagged tuples; inductive propositions as `if ( constructor applies , 1o , (/) )`.
- Recursive types (`Nat`, `List`) as least fixed points, unions of ω-chains of stages; trees, whose constructors have several recursive fields, through a one-time lemma that the stages only grow.
- Mutual and nested inductive types (`Lean.Syntax`) as one least fixed point over a tagged sum.
- Recursors through `set.mm`'s well-founded recursion (`frecs`) over smaller rank, resting on bridge lemmas that rank is well-founded and set-like (`tenet-zfc bridge`).
- Recursive propositions (`Nat.le`) as least sets of index tuples.
- `Nat` literals as decimal numerals, through `_om`; string literals as lists of characters.
- Quotients as equivalence classes, with `Quot.lift`'s computation rule; `propext` as a proof; `Classical.choice` from `set.mm`'s choice.
- Every Lean name as a token and a label: `'`, `?`, `!`, `@`, Unicode, numeric parts and `«»` are escaped one-to-one (`List.map'` → `lean.List.map-q`, `a₂` → `lean.a-u2082`); `define` takes escaped names too.
- `Acc` and other propositions whose premises are functions into them, as least fixed points (the intersection of the closed sets), with recursors into any sort by well-founded recursion over them: `WellFounded.fix` and well-founded definitions translate.
- More than 20 arguments: class variables the output declares itself (`AA1`, `AA2`, …), like the extra set variables.
- More than 26 bound variables: set variables each output declares itself (`$v`, `$f setvar`), which add no axiom.
- Proofs in Metamath's compressed format, sharing every repeated subproof: the largest outputs shrink by up to about 40 times (`--uncompressed` keeps flat proofs).
- **Universes: a tower by default.** With one universe `Nat.below` is empty, and structurally recursive functions such as `Nat.add` collapse. The model's default is an increasing sequence of Grothendieck universes, one per level, under the hypothesis `U e. lean.-tower`; no axiom is added. Each output's header states this, how many levels it uses and which declarations use each. `--single-universe` keeps the one-universe model, which quotients and choice still need.
- Coverage, measured with `tenet-zfc model-survey`: 14,105 of the 17,590 definitions in Lean 4.36's `Init` (80%) translate together with everything they use, in the tower model (13,958 in the one-universe model).
- **At scale:** `tenet-zfc define-all` translates every definition of an export in chunks (`--jobs`, `--budget` per constant, `--chunks` to resume), and `scripts/verify-all` checks every chunk with all three checkers.

**Bridges** ([docs/bridges.md](docs/bridges.md)): the model's `Nat` is proved to be `set.mm`'s `NN0`, zero to `0`, `succ` to `+ 1`, literals to numerals, and `⟦Nat.add⟧` to `+`, with no hypotheses but the tower's (`tenet-zfc nat-bridge`). Lean's `Nat.add_zero` and `Nat.zero_add`, proved through the model, are restated as `( A + 0 ) = A` and `( 0 + A ) = A`. Lean's `2 + 2 = 4`, read in the model, is proved equivalent to `set.mm`'s `( 2 + 2 ) = 4`.

**First theorems through the model** (`tenet-zfc theorem`): Lean theorems proved from their own proof terms, a proof's typing becoming membership `(/) e. ⟦P⟧` and each conversion an equation. `Nat.add_zero` and `Nat.zero_add` verify.

### Milestone 2: the bridge library

- `tenet-zfc emit` replays a Tenet trace and writes `set.mm` theorems for the theorems its translator covers: `Nat` arithmetic equations from their traces (Lean's `2 + 2 = 4` becomes `|- ( 2 + 2 ) = 4`), and induction on lists from proof terms (`List.length_append`, through `wrdind`). Statements it can't prove are cross-checked against `set.mm`, and labelled as such.
- Both verifiers accept the gate theorems in CI, on every push.

### Milestone 1: the trace

- `tenet-zfc replay` re-derives every step of a Tenet derivation trace from its rule, sharing no code with Tenet: reductions, definitional equalities, typing judgments, inductive blocks and their recursors. On all of Lean core it replays 64,045 declarations, 86 million steps, with no failures. See [docs/trace-format.md](docs/trace-format.md).
- `tenet-zfc survey` measures how much of an export the milestone 2 translator covers.

### Infrastructure

- CI on Linux, macOS and Windows, with .NET 8 and 10; set.mm, metamath-exe, mmverify.py and mmj2 pinned to exact commits, and every fixture output checked by all three.
- `scripts/check-definitions` runs mmj2's `definitionCheck` the way `set.mm`'s own scripts do.
