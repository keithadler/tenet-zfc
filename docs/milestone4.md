# Milestone 4: universe elimination

Every output of milestone 3 holds under a hypothesis, `U e. lean.-tower`: `U` is an increasing ω-sequence of Grothendieck universes, the first containing ω. ZFC doesn't prove that such a tower exists (it needs inaccessible cardinals), so the results are "ZFC plus universes", not ZFC. Milestone 4 removes the hypothesis from theorems that don't really need it ([spec](spec.md#universe-elimination)).

This document says which universe facts the outputs use, which of them plain ZFC proves, how the tower is replaced by sets ZFC proves exist, and how the final theorem is stated with no hypothesis. The first part is built: **`Nat.add_zero` and `Nat.zero_add` come out in plain ZFC**, as

```
lean-zfc-Nat.add_zero $p |- ( A e. NN0 -> ( A + 0 ) = A ) $= … $.
lean-zfc-Nat.zero_add $p |- ( A e. NN0 -> ( 0 + A ) = A ) $= … $.
```

proved from Lean's proof term through the model, with no universe hypothesis and no `ax-groth`, accepted by metamath-exe, mmverify.py and mmj2's `definitionCheck` (`nat-bridge --lowered`, below).

## What the outputs use

The tower enters a proof in one place: membership in a level, `( ph -> X e. ( U ` K ) )`, which `UniverseMembership.cs` proves by recursion on `X`. The levels themselves are used only through three lemmas proved from the tower's definition. Tracing `lean-nn0-Nat.add_zero` back with metamath-exe (`show trace_back … /essential`) lists exactly these:

| Universe fact | `set.mm` (Grothendieck) | Where the translator needs it | ZF proves it for weak universes? |
|---|---|---|---|
| each level is a universe | `lean-tw-u`: `( U ` K ) e. Univ` | every closure step below | `( U ` K ) e. WUni` |
| `Type k : Type (k+1)` | `lean-tw-s`: `( U ` K ) e. ( U ` suc K )` | a sort used as a term; motives into `Sort` (`Nat.below`) | yes, if the tower says so |
| ω is small | `lean-tw-om`: `_om e. ( U ` (/) )` | `Nat`, literals | yes, if the tower says so |
| membership is transitive | `gruel` | a member of a type that is in the universe | `wunelss` |
| pairs, tagged tuples | `gruop` | constructors' tuples | `wunop` |
| singletons, binary unions | `grusn`, `gruun` | the stages of an inductive type | `wunsn`, `wunun` |
| function spaces | `grumap` | arrow types, motive types `( G ^m T )` | `wunmap` |
| power sets | (`grupw`, inside the lemmas above) | none directly | `wunpw` |
| **indexed unions** | **`gruiun`** | a structure's product (`PProd`: `U_ z e. x U_ w e. y { tuple }`); a recursive type's union of stages (`U_ k e. _om ( rec ( F , (/) ) ` k )`) | **no** |
| motive levels | none | a recursor's motive ranges over the whole tower, `U. ran U` (`fnfvelrn`, `elssuni`); never needs to be a member of anything | not needed |

Everything in the table but indexed unions holds in a **weak universe** (`df-wun`: a transitive nonempty set closed under `U.`, `~P` and pairs), and ZF proves weak universes exist: `( R1 ` A )` is one for every limit ordinal `A` (`r1limwun`), and every set is in one (`wunex`, `wunex3`). None of this uses `ax-groth`.

What weak universes lack is closure under replacement: from `A e. W` and `A. x e. A B e. W`, `U_ x e. A B e. W` doesn't follow. A set closed under that too is a Grothendieck universe, `R1` at an inaccessible. So `gruiun` is the whole difference between what the outputs use and what ZFC proves, and lowering is about replacing each indexed union by an argument that a weak universe supports.

In `Nat.add_zero`'s proof (with Lean's `Nat`, `PProd`, `Eq`, `HAdd`, `Add`, `OfNat`, `instHAdd`, `instAddNat`, `instOfNatNat`, `Nat.below`, `Nat.brecOn`, `Nat.add.match_1`, `outParam`), `gruiun` is used twice: `lean-ty-Nat` (the union of `Nat`'s stages) and `lean-ty-PProd.u1_1` (`PProd`'s pairs).

## Replacing the tower

### The lowered tower (built)

Two definitions, both checked by mmj2's `definitionCheck`:

```
df-lean.-wuni   $a |- lean.-wuni = { w e. WUni | A. x e. w ( R1 ` ( ( rank ` x ) +o _om ) ) e. w } $.
df-lean.-wtower $a |- lean.-wtower = { f | ( ( f : _om --> lean.-wuni /\ _om e. ( f ` (/) ) )
                                          /\ A. n e. _om ( f ` n ) e. ( f ` suc n ) ) } $.
```

`lean.-wtower` is `lean.-tower` with `Univ` replaced by `lean.-wuni`: **reflecting weak universes**, weak universes that contain, with each member `x`, the weak universe `( R1 ` ( ( rank ` x ) +o _om ) )` that `wunex3` builds around `x`. With `--lowered`, the model's universe argument ranges over `lean.-wtower` instead of `lean.-tower`; every definition, equation and lemma is otherwise the same text. The three tower lemmas are proved from the new definition word for word, with `lean.-wuni` for `Univ`, and two more say what a level is:

- `lean-wu-w`: `|- ( W e. lean.-wuni -> W e. WUni )`;
- `lean-wu-r`: `|- ( ( W e. lean.-wuni /\ X e. W ) -> ( R1 ` ( ( rank ` X ) +o _om ) ) e. W )`, the reflection step.

### Closure in a weak universe (built)

`UniverseMembership.cs` takes the weak-universe lemma for each Grothendieck one: `wunop`, `wunsn`, `wunun`, `wunxp`, `wunmap`, `wunelss` (transitivity), `wun0` and `wunom` (finite ordinals). They are in deduction form, `( ph -> U e. WUni ) ⇒ …`, so no context juggling is needed. The two kinds of indexed union are bounded instead (`BoundedIun`):

- **A union of tuples**, `U_ z e. A U_ w e. B { <. c , <. z , w >. >. }`, as structures and the constructor steps of inductive types are built. Each tuple lies in the product of its components' sets, so the union is a subset of `( { c } X. ( A X. B ) )` (`opelxpd`, `snssd`, `iunssd`). That product is a member of the level (`wunxp`, `wunsn`), and so is every subset of a member (`wunss`). No replacement: the bound is computed from the term.
- **A recursive type's union of stages**, `U_ k e. _om ( rec ( F , (/) ) ` k )`. The stages grow with `k`, and no fixed product bounds them; this is where reflection comes in. Each stage is a member of the small weak universe `( R1 ` ( ( rank ` (/) ) +o _om ) )`, by the same induction over ω as before (`finds2`), with that weak universe for the level. So the union is a subset of it (`wunelss`, `iunssd`), and it is a member of every level (`lean-wu-r` at `(/)`). So the union is a member of the level (`wunss`).

The second case is built for types without parameters, such as `Nat`. A type with parameters (`List α`) needs a weak universe containing them: `lean-wu-r` at `{ α }` (or at the tuple of the parameters) gives `( R1 ` ( ( rank ` { α } ) +o _om ) )`, which contains `α` (`wunex3`), and the same induction works inside it. That is the next step; until then such a union is refused with the reason.

### ZFC proves a lowered tower exists (built)

`TowerWitness.cs` proves, once per output,

```
lean-wit-tw $p |- lean.-wit e. lean.-wtower $= … $.
```

for a third definition,

```
df-lean.-wit $a |- lean.-wit = ( n e. _om |-> ( R1 ` ( _om .o ( _om .o suc n ) ) ) ) $.
```

`R1` at the limit ordinals ω·(ω·(n+1)) = ω²·(n+1), written with `set.mm`'s ordinal multiplication. The lemmas:

| Lemma | Statement | From |
|---|---|---|
| `lean-wit-lim1` | `( N e. _om -> Lim ( _om .o suc N ) )` | `omsuc`, `oalimcl` |
| `lean-wit-lim` | `( N e. _om -> Lim ( _om .o ( _om .o suc N ) ) )` | `omlimcl` |
| `lean-wit-add` | `( ( ( C e. V /\ Lim C ) /\ B e. ( _om .o C ) ) -> ( B +o _om ) e. ( _om .o C ) )` | `omlim`, `eliun`, `oawordri`, `omordi`, `ontr2` |
| `lean-wit-fv` | `( N e. _om -> ( lean.-wit ` N ) = ( R1 ` ( _om .o ( _om .o suc N ) ) ) )` | `fvmpt` |
| `lean-wit-wu` | `( N e. _om -> ( R1 ` ( _om .o ( _om .o suc N ) ) ) e. lean.-wuni )` | `r1limwun`, `rankr1ai`, `lean-wit-add`, `r1ord` |
| `lean-wit-f` | `lean.-wit : _om --> lean.-wuni` | `fmpt` |
| `lean-wit-om` | `_om e. ( lean.-wit ` (/) )` | `lean-wit-add` at `(/)`, `oa0r`, `onssr1` |
| `lean-wit-s` | `A. n e. _om ( lean.-wit ` n ) e. ( lean.-wit ` suc n )` | `omordi` twice, `r1ord` |
| `lean-wit-tw` | `lean.-wit e. lean.-wtower` | `elabg` |

The one real step is `lean-wit-add`: below ω·C, for C a limit, adding ω stays below. A member `B` of `( _om .o C ) = U_ x e. C ( _om .o x )` is below some `ω·x` with `x ∈ C`, so `B + ω ⊆ ω·x + ω = ω·suc x`, and `suc x ∈ C`. Applied to `rank x`, it says that `R1 ( rank x + ω )` is a member of `R1 ( λ )` for each `x` in it: each level is reflecting.

### The theorem with no hypothesis (built)

A lowered theorem has the form `|- ( ( U e. lean.-wtower /\ ph ) -> ps )`. `U` is a class variable, so the theorem holds with `lean.-wit` for `U`; with `lean-wit-tw` and `mpan` it becomes `|- ( ph -> ps )` (`TowerWitness.Discharge`). When `U` occurs in neither `ph` nor `ps`, that is a statement of plain ZFC about `set.mm`'s own objects. `nat-bridge` already restates `Nat.add_zero` in `NN0`, `( ( U e. lean.-wtower /\ A e. NN0 ) -> ( A + 0 ) = A )`, so:

```
$ tenet-zfc nat-bridge tests/fixtures/theorems.ndjson set.mm natbridge-zfc.mm 2 Nat.add_zero --lowered
…
lean-wit-tw: |- lean.-wit e. lean.-wtower
lean-zfc-Nat.add_zero: |- ( A e. NN0 -> ( A + 0 ) = A )
```

When `U` does occur in the statement (`A e. ( lean.Nat ` U )`), discharging still gives a theorem of ZFC, about the model at `lean.-wit`; the bridges are what turn it into a statement in `set.mm`'s vocabulary. The plain theorem doesn't depend on which witness is used: any lowered tower gives the same statement.

### Checking for `ax-groth`

`scripts/check-axioms <metamath> <out.mm> <label>…` runs metamath-exe's `show trace_back <label> /axioms`, which lists every axiom a theorem rests on through every theorem it uses, so a use of `ax-groth` anywhere below (through `grothtsk`, `inaex`, …) shows as `ax-groth`. It fails if `ax-groth` is listed, or if the statement still mentions `U`, `lean.-tower`, `lean.-wtower`, `Univ` or `WUni`. CI runs it on `lean-zfc-Nat.add_zero`, and with `--axioms-only` on `lean-wit-tw` (which names the tower by design). It also checks the check: it must fail on `lean-nn0-Nat.add_zero` (the restatement before the discharge, which has the hypothesis) and on `set.mm`'s `inaex` (proved from `ax-groth`). For `lean-zfc-Nat.add_zero` the list is

```
ax-1 ax-10 ax-11 ax-12 ax-1cn ax-1ne0 ax-1rid ax-2 ax-3 ax-4 ax-5 ax-6 ax-7 ax-8 ax-9 ax-addass ax-addcl ax-addrcl ax-cnex ax-cnre ax-distr ax-ext ax-gen ax-i2m1 ax-icn ax-inf2 ax-mp ax-mulass ax-mulcl ax-mulcom ax-mulrcl ax-nul ax-pow ax-pr ax-pre-ltadd ax-pre-lttri ax-pre-lttrn ax-pre-mulgt0 ax-reg ax-rep ax-resscn ax-rnegex ax-rrecex ax-sep ax-un
```

the axioms of ZF as `set.mm` states them (not even choice, `ax-ac`), and the complex-number axioms (`ax-1cn` …, which `set.mm` proves from ZFC's construction of the reals: they are theorems `axcnex`, `ax1cn`… restated as axioms for convenience); no `ax-groth`.

Note that the tower outputs never used `ax-groth` either: the tower was a hypothesis, not an axiom. What changes is that the hypothesis is now discharged.

## Where reflection is needed

The two bounded shapes cover structures and parameter-free recursive types. Three kinds of indexed union remain, and each needs more of the reflection principle.

1. **Recursive types with parameters** (`List α`, `Option α` nested in a recursive type): as above, `lean-wu-r` at the parameters. No new principle; next to build.
2. **Unions over a type family**, as Σ-types and dependent Π-types are built: `U_ a e. A ( B ` a )` with `B : A → Type u`. Each `( B ` a )` is in the level, but nothing bounds them uniformly: in `R1 ( ω² )` the family `n ↦ R1 ( ω·n )` over `ω` has no bound below ω². This is a genuine use of replacement. ZF proves the reflection principle for any one class function `F`: there are arbitrarily large limit ordinals `λ` with `F ( x ) ∈ R1 ( λ )` for every `x ∈ R1 ( λ )` (iterate `x ↦ sup { rank F ( y ) + 1 : y ∈ R1 ( x ) }` ω times). In `set.mm` this is one schematic theorem, with `F` a class variable in which `x` may occur free, proved once by hand: ZF proves each instance, and `set.mm`'s class variables make the instance a substitution. Per theorem, the translator then collects the finitely many families its proof unions over (each `x ↦ U_ a e. x ( B ` a )` with its parameters tupled into `x`), and chooses the levels bottom-up, `λ_0` closed under the level-0 families, `λ_1 > λ_0` under the level-1 families, and so on. A level-k family mentions only levels below k, so the choice is not circular. Then `lean-wit` becomes a per-theorem witness, still proved in ZF.
3. **Statements that quantify over a universe**, such as `List.length_append` for every `α : Type` (`lean-ccatlen` has the hypothesis `A e. ( U ` (/) )`). In a lowered tower this says "for every `α` in the first level". To state it for every set, the witness must start above a given set: `R1` at `ω·( ω·suc n +o rank A )`-style levels, so that `A e. ( lean.-wit ` (/) )`, and `Discharge` then gives `|- ( ( A e. V /\ … ) -> … )`. This is the reflection argument in its simplest form, and the route to `lean-ccatlen` in plain ZFC.

What reflection can't lower is a proof that uses a universe as a set closed under replacement *for every function on it*, not just for the ones the proof names: a proof that `Type` is a model of something (a category of all small sets with all its limits, or the consistency of ZFC itself). Those stay ZFC plus universes, and the report names them.

## The per-output report

Each output's header (from milestone 3) now says whether its theorems are plain ZFC. A lowered output says that its lemmas assume `U e. lean.-wtower`, that ZFC proves a lowered tower exists (`lean-wit-tw`), how indexed unions were bounded, and lists the plain-ZFC theorems. The header of `nat-bridge … Nat.add_zero Nat.zero_add --lowered` (then the levels used, by declaration, as in milestone 3):

```
Assumptions (the universe analysis of docs/spec.md).
Universes: lowered (docs/milestone4.md). Lemmas have the hypothesis U e. lean.-wtower: U is an increasing
omega-sequence of reflecting weak universes (lean.-wuni: weak universes containing, with each member x, the
weak universe R1 at rank x + omega), the first containing omega, and Lean's Sort (k+1) is ( U ` k ). ZFC
proves such a tower exists: lean-wit-tw, for lean.-wit = R1 at the limit ordinals omega^2 (n + 1). So a
theorem whose statement doesn't mention U holds outright: the universe hypothesis is discharged.
No ax-groth: weak universes are closed under pairs, unions, power sets and function spaces, which ZF proves;
indexed unions, which they lack, were bounded (by a product of the components' sets, or, for a recursive
type's stages, by R1 at rank 0 + omega, a member of every level: the reflection step).
Plain ZFC (no universe hypothesis, no ax-groth; scripts/check-axioms checks both): 
  lean-zfc-Nat.add_zero (Nat.add_zero), lean-zfc-Nat.zero_add (Nat.zero_add).
```

A Grothendieck-tower output says instead that none of its theorems is plain ZFC, and points to `--lowered`. A lowered run that meets an indexed union it can't bound is refused with the declaration and the union, for example `no bound yet for the union body … in a weak universe (milestone 4: an indexed union needs reflection)`: that is the list of declarations that need a universe, and why.

## Measurements

On an Apple-silicon Mac shared with other long jobs (so wall times are inflated; CPU times are the comparable figure):

| Run | `$p` statements | Output | CPU |
|---|---|---|---|
| `nat-bridge … 2 4 256 Nat.add_zero` (Grothendieck tower) | 101 | 0.79 MB | 17 s |
| `nat-bridge … 2 Nat.add_zero --lowered` | 111 | 0.80 MB | 17 s |
| `nat-bridge … 2 4 256 Nat.add_zero Nat.zero_add --lowered` | 135 | 1.30 MB | 37 s (0.39 GB peak) |

Lowering costs nothing measurable: the closure lemmas swap one for one, and the two bounded unions are a few steps each. The witness lemmas are proved once per output, nine theorems of 1 to 31 steps each before sharing. `Nat.zero_add` (induction through `Nat.brecOn` into `Prop`) lowered with no further change, as `lean-zfc-Nat.zero_add`: `|- ( A e. NN0 -> ( 0 + A ) = A )`. All three outputs pass metamath-exe, mmverify.py and mmj2's `definitionCheck`.

## Order of work

1. **Done:** the lowered tower, weak-universe closure, the two bounded unions, the ZFC witness, `Discharge`, `check-axioms` in CI, the header; `Nat.add_zero` and `Nat.zero_add` in plain ZFC.
2. Recursive types with parameters (`lean-wu-r` at the parameters), then `list-bridge --lowered`: `List.length_append` as `ccatlen`, with a witness above the alphabet (case 3 above).
3. `--lowered` for `theorem`, `define` and `define-all`, and a survey: how many of `Init`'s definitions and of the 28 library theorems lower, and the first reasons for the rest.
4. The reflection theorem schema, proved once in `set.mm`, and per-theorem witnesses for unions over type families (case 2).
5. Make lowering the default once it covers what the tower covers, with the tower as the fallback for declarations that need it, reported per declaration.

The gate stays the spec's: mathlib's `Nat` and `Int` files in plain ZFC.
