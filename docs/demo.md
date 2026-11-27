# The headline demo: `List.length_append` is `ccatlen`

Lean's `List.length_append` says that the length of `as ++ bs` is the length of `as` plus the length of `bs`. `set.mm`, Metamath's library of ZFC set theory, has the same fact for its words (finite sequences), as `ccatlen`, proved by hand.

tenet-zfc takes Lean's proof term of `List.length_append` and translates it to a ZFC proof through its model of Lean's type theory. It then restates the result through two proved bridges: the model's `List A` is `set.mm`'s `Word A`, and the model's `Nat` is `set.mm`'s `NN0`. What comes out is `set.mm`'s own statement:

```
lean-ccatlen        $p |- ( ( U e. lean.-tower /\ ( A e. ( U ` (/) ) /\ B e. ( U ` (/) ) ) ) ->
                          ( ( S e. Word A /\ T e. Word B ) -> ( # ` ( S ++ T ) ) = ( ( # ` S ) + ( # ` T ) ) ) )
lean-ccatlen-setmm  $p   (the same statement, from set.mm's ccatlen)
ccatlen             $p |- ( ( S e. Word A /\ T e. Word B ) -> ( # ` ( S ++ T ) ) = ( ( # ` S ) + ( # ` T ) ) )
```

The consequent of `lean-ccatlen` is `ccatlen`'s statement, token for token. So the output holds **one ZFC statement with two independent proofs**:
- `lean-ccatlen`, from Lean's proof, through the model and the bridges;
- `lean-ccatlen-setmm`, from `set.mm`'s hand-written `ccatlen`.

Neither proof uses the other. metamath-exe (C), mmverify.py (Python) and mmj2's definition check (Java) all accept the file.

The demo also checks the trust story the other way. Three sabotaged versions, a corrupted proof step, a changed statement and a broken Lean proof, are each rejected.

## The hypotheses

`U e. lean.-tower` says that `U` is a tower of Grothendieck universes, one for each of Lean's universe levels. Every theorem tenet-zfc proves through the model has this hypothesis. Lean's logic is stronger than ZFC: ZFC can't prove that such a tower exists, because that needs inaccessible cardinals. So `lean-ccatlen` holds in every model of ZFC that has a tower, and no axiom is added. `A e. ( U ` (/) )` and `B e. ( U ` (/) )` say that the alphabets are types of Lean's `Type`, members of the tower's first universe. See [milestone3.md](milestone3.md#tower-mode-universescs-monomorphcs) and the README's Limits.

## Run it

```bash
export TENET_ZFC_SETMM=/path/to/set.mm             # set.mm at CI's pinned commit
export TENET_ZFC_METAMATH=/path/to/metamath        # metamath-exe
export TENET_ZFC_MMVERIFY=/path/to/mmverify.py
export TENET_ZFC_JAVA=/path/to/java                # Java 11, for mmj2
export TENET_ZFC_MMJ2=/path/to/mmj2                # mmj2.jar and macros/
```

```bash
scripts/demo /tmp/demo
```

The script builds tenet-zfc (or runs `$TENET_ZFC`), translates, checks and sabotages, then prints sizes and times. It exits 0 only if the real proof passes all three checkers and every sabotaged one is rejected. Its files stay in the directory given: `demo.mm`, the three sabotaged inputs, and each checker's log.

It uses `tests/fixtures/library.ndjson`, which is `leanout Init` on Lean 4.36.0 with `List.length_append` and its dependencies. Set `TENET_ZFC_LEANOUT` to export it again from your own Lean.

The steps it runs are:

```bash
tenet-zfc list-bridge tests/fixtures/library.ndjson set.mm demo.mm List.length_append
tenet-zfc verify demo.mm
```

CI runs the demo weekly and by hand (the `demo` job in `.github/workflows/ci.yml`), and uploads its log and `demo.mm`. On every push, CI proves the bijection alone (`list-bridge --bridge-only`, a few seconds) and checks it.

## Output

From a run on an Apple-silicon Mac shared with other jobs, so the times are high; an earlier run on a quieter machine took 495 s to translate, 63 s to check and 636 s in all:

```
$ scripts/demo /tmp/demo

== 1. Lean's theorem
Lean 4.36.0, src/lean/Init/Data/List/Basic.lean:

  @[simp, grind =] theorem length_append {as bs : List α} : (as ++ bs).length = as.length + bs.length := by
    induction as with
    | nil => simp
    | cons _ as ih => simp [ih, Nat.succ_add]

export: tests/fixtures/library.ndjson (leanout Init, Lean 4.36.0), 230622 bytes

== 2. Translate: Lean's proof term -> ZFC, through the model and the List/Word bridge
  [   2.9s] read the export and set.mm
  [   5.4s] the bijection W from the model's List onto Word
  [   6.1s] the Nat bridge F
  [  16.8s] Nat.add's computation rules, so F takes Nat.add to +
  [  57.4s] List.length, List.append and HAppend.hAppend through W
  [ 600.2s] List.length_append through the model, restated in set.mm's words
  [ 651.2s] written
  output: demo.mm, 6928689 bytes, 247 theorems, 652.2 s

== 3. The restated theorem, next to set.mm's own
  lean-ccatlen        (from Lean's proof)    |- ( ( U e. lean.-tower /\ ( A e. ( U ` (/) ) /\ B e. ( U ` (/) ) ) ) -> ( ( S e. Word A /\ T e. Word B ) -> ( # ` ( S ++ T ) ) = ( ( # ` S ) + ( # ` T ) ) ) )
  lean-ccatlen-setmm  (from set.mm's proof)  |- ( ( U e. lean.-tower /\ ( A e. ( U ` (/) ) /\ B e. ( U ` (/) ) ) ) -> ( ( S e. Word A /\ T e. Word B ) -> ( # ` ( S ++ T ) ) = ( ( # ` S ) + ( # ` T ) ) ) )
  ccatlen             (set.mm)               |- ( ( S e. Word A /\ T e. Word B ) -> ( # ` ( S ++ T ) ) = ( ( # ` S ) + ( # ` T ) ) )
  -> one statement, two proofs; its consequent is ccatlen's statement, token for token

== 4. Check: metamath-exe, mmverify.py, mmj2 definitionCheck
  demo.mm: metamath-exe: ok: every proof verified (247 theorems) (31s)
  demo.mm: mmverify.py: ok: exit status 0 (131s)
  demo.mm: mmj2 definitionCheck: ok: every definition passes (279s)
  (279.4 s)

== 5. Sabotage: each must be rejected
(a) one proof step of lean-ccatlen changed
  metamath-exe: REJECTED: "lean-ccatlen": The hypotheses of statement "syl" at proof step 197 cannot be unified.
  mmverify.py:  REJECTED: MMError: Proof stack entry does not match essential hypothesis.
  -> rejected
(b) lean-ccatlen's statement changed from + to x.
  metamath-exe: REJECTED: "lean-ccatlen": The result of the proof (step 246) does not match the statement being proved.
  mmverify.py:  REJECTED: MMError: Stack entry does not match proved assertion.
  -> rejected
(c) List.length_append's proof term replaced by List.append_nil's
  tenet-zfc: List.length_append: refused: applying something whose type isn't a function type: ( ( ( ( lean.Eq.{1} ` U ) ` ( ( lean.List.{0} ` U ) ` A ) ) ` ( ( ( ( ( ( ( le
  -> rejected: no proof is produced, so there is nothing for the checkers to accept

== Summary
  translate: 652.2 s; check (three checkers): 279.4 s; demo total: 1101.4 s
  demo.mm: 6928689 bytes
  PASS: the real proof is accepted by all three checkers, and each sabotage is rejected
```

## What each part shows

**1–2. Translation.** `list-bridge` proves the following, in order, into one file:
- the bijection `W` from the model's `List A` onto `Word A`;
- the `Nat` bridge `F`, and `Nat.add`'s computation rules, so that `F` takes `Nat.add` to `+`;
- `List.length`'s and `List.append`'s computation rules, so that `W` and `F` take them to `#` and `++`;
- `List.length_append` from its proof term, through the model, as `tenet-zfc theorem` does;
- the restatement.

The theorems and how each is proved are in [bridges.md](bridges.md#list-and-word). Most of the time goes to `List.length_append`'s own proof through the model. Its proof term is 664 million steps written flat, and it is never written flat: the output is compressed and shares subproofs.

**3. One statement.** The demo compares the texts. `lean-ccatlen` and `lean-ccatlen-setmm` have the same statement, and its consequent is exactly `ccatlen`'s line in `set.mm`.

**4. The checkers.** `tenet-zfc verify` runs three checks:
- metamath-exe on every `lean-*` theorem;
- mmverify.py on every theorem from the file's first;
- mmj2's `definitionCheck` on every definition the file adds. Each definition must be conservative: a new symbol, defined once, with no free variables.

`set.mm`'s own proofs are checked once, apart, as CI does. The file adds no axiom: its only `$a` statements are definitions (`df-lean.*`) and their syntax.

**5. Sabotage.**
- **(a) A corrupted proof step.** One letter of `lean-ccatlen`'s compressed proof is changed, so one step refers to a different earlier step. Both verifiers find the step whose hypotheses no longer unify.
- **(b) A changed statement.** `+` becomes `x.` in `lean-ccatlen`'s statement, and its proof is left as it was. The proof still proves `+`, so both verifiers report that its result doesn't match the statement. A translator that wrote a wrong statement over a right proof would be caught the same way.
- **(c) A broken Lean proof.** In the export, `List.length_append`'s proof term is replaced by `List.append_nil`'s, a proof of something else. The translator builds its ZFC proof by following the typing of the proof term against the theorem's statement. This term doesn't have that type, so the translator refuses it and produces no proof. The checkers are not needed here. Had the translator produced output from it, that output would fail as in (a) or (b): the checkers never trust the translator.

## Sizes and times

| | |
|---|---|
| Lean export (`library.ndjson`) | 230,622 bytes |
| `demo.mm` | 6,928,689 bytes, 247 theorems |
| translate (`list-bridge`) | 495–652 s; about 85% of it is `List.length_append`'s own proof through the model |
| check (three checkers, at once) | 63–279 s; mmj2 is the slowest |
| the whole demo, sabotage included | 636–1,101 s |
| the bijection alone (`--bridge-only`) | 5 s to prove, 33 theorems, 61 KB |
