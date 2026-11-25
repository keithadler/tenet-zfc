# Lean-to-ZFC Proof Translator: Specification

2026-11-24 · Keith Adler

## Summary

A tool that takes a Lean 4 theorem, already checked by Lean, and produces a proof of the same statement in plain ZFC set theory that a tiny independent checker (Metamath) can verify.

It is built on [Tenet](https://github.com/keithadler/tenet), which already reads Lean's kernel export and checks definitional equality. The new work is recording every step Tenet takes and printing it as set-theory proof steps.

Why it matters: a Lean result accepted by two unrelated systems on two different foundations is about as trustworthy as a formal proof gets. And it answers mathematicians who ask "but does this hold in ZFC?"

## Goals and non-goals

v1 translates mathlib theorems about ordinary mathematics (numbers, algebra, analysis) into Metamath ZFC proofs that check.

**Goals**

1. Fully mechanical. The core translator uses no AI, and the same input always gives the same output.
2. Every output is checked by an independent Metamath verifier. If the verifier rejects it, the translation failed. A wrong proof can never be reported as success.
3. Plain ZFC whenever the proof allows. When it doesn't, the output says exactly how many inaccessible cardinals it used, and why.
4. Reuse Tenet's kernel input and its definitional-equality engine rather than writing a new checker.
5. Handle any declaration Tenet can check, including Lean's three standard axioms: `propext`, `Quot.sound` and `Classical.choice`.

**Non-goals**

- Readable ZFC proofs. The output is for machines. Shrinking it and making it readable are later work.
- Translating ZFC back into Lean.
- Proofs that use `native_decide` or `Lean.trustCompiler`. They rely on compiled code, not a kernel proof, so there's nothing to translate.

## Target foundation

The target is Metamath's `set.mm` database, which states ZFC directly and is checked by verifiers a few hundred lines long. Several independent verifiers exist, in different languages.

Lean's logic is stronger than ZFC. Carneiro's thesis, *The Type Theory of Lean* (2019), shows it is equiconsistent with ZFC plus one inaccessible cardinal for each universe level. So there are two output levels:

| Output | When | Axioms used |
|---|---|---|
| Plain ZFC | The proof needs no universe above the lowest one (most ordinary mathematics) | `set.mm`'s ZFC axioms only |
| ZFC + n universes | The proof really uses n higher universe levels | ZFC plus `set.mm`'s Grothendieck-universe axiom, used n times, stated in the output's header |

The translated statement must mean the same as the Lean statement. For each translated theorem, a hand-checked table maps Lean's definitions (ℕ, ℝ, groups and so on) to `set.mm`'s, with a proof that the two agree.

## Architecture

The pipeline has six stages. Only stages 3 to 5 are new code. The rest is Tenet or existing tools.

1. **Export.** Lean writes the theorem and everything it depends on in kernel export format, the input Tenet already reads.
2. **Universe analysis.** Find which universe levels the proof really needs, and instantiate everything else at level 0 (see Universe elimination).
3. **Traced checking.** Tenet re-checks the proof with tracing on. Every definitional-equality step (beta, delta, iota, zeta, eta, proof irrelevance, `Nat` literal arithmetic) is written out as a step in a certificate file. See [trace-format.md](trace-format.md).
4. **Interpretation.** Each Lean term becomes a set-theoretic term, following Carneiro's model: types become sets, functions become set-theoretic functions, and `Prop` becomes {∅, {∅}}.
5. **Emission.** Each typing judgment and each traced equality becomes a `set.mm` theorem, using a fixed library of about 200 to 400 bridge lemmas, one per Lean typing rule and reduction rule. The bridge library is written and checked once, by hand. See [rule-map.md](rule-map.md).
6. **Independent check.** Run `metamath-exe`, plus a second Metamath verifier written in a different language, on the output. Success means both accept it.

Tenet's existing parallelism carries over: independent declarations are translated on separate cores.

## How each Lean feature is translated

Every feature of Lean's kernel has a fixed set-theoretic meaning. The bridge library proves that each one behaves correctly once.

| Lean feature | Meaning in ZFC | Difficulty |
|---|---|---|
| `Sort u` / `Type u` | The u-th universe set (Vω at level 0, or a Grothendieck universe above it) | Low |
| `Prop` | {∅, {∅}}: false and true | Low |
| Proofs (inhabitants of a `Prop`) | All identified with ∅, which gives proof irrelevance for free | Low |
| Dependent functions (Π types) | Sets of set-theoretic functions | Low |
| Lambda and application | Function construction and evaluation | Low |
| Inductive types (incl. mutual and nested) | Least fixed points of a monotone operator, built by transfinite recursion | High |
| Recursors and large elimination | Functions defined by well-founded recursion on those fixed points | High |
| Structure eta, function eta | Extensionality lemmas | Medium |
| Quotients (`Quot`, `Quot.sound`) | Equivalence classes under the smallest equivalence relation | Medium |
| `propext` | Holds automatically: equivalent propositions are equal elements of {∅, {∅}} | Low |
| `Classical.choice` | ZFC's axiom of choice, via a fixed global choice function | Medium |
| `Nat` and `String` literals, kernel GMP arithmetic | Unfolded into `set.mm`'s natural-number arithmetic, with a verified decimal-arithmetic library to keep it short | Medium |
| Definitions and `let` | Unfolded where the trace says they were unfolded | Low |

## Universe elimination

Most mathlib theorems are stated for any universe `u` only for generality. Their proofs never need a universe above the lowest one, so they translate to plain ZFC.

1. **Instantiate.** Set every universe variable in the theorem to 0 when translating it.
2. **Collect.** Walk the proof and its dependencies and record every universe level actually used after instantiation (for example a `Type 1` built inside a proof).
3. **Lower.** For each higher level found, try to lower it: replace a quantification over "all types in `Type 1`" by one over a set large enough for the specific objects used. This is a standard reflection argument, automated for common patterns such as categories of small objects.
4. **Report.** If anything can't be lowered, emit the ZFC + n universes version, and list each declaration that forced a universe, so a person (or an AI, see below) can look for a proof without it.

This stage decides whether the result is "proved in ZFC" or "proved in ZFC plus universes", so it is reported in the header of every output.

## Size and performance

The main cost is blowup: every computation step Lean's kernel does silently becomes an explicit proof step in ZFC.

- **Sharing.** Each repeated subterm and each repeated reduction becomes one `set.mm` lemma, proved once and cited everywhere. Without this the output grows exponentially. With it, it should grow roughly linearly in Tenet's trace length.
- **Arithmetic.** Big `Nat` computations (kernel GMP arithmetic, `decide`) use a verified decimal-arithmetic library rather than unary successor steps.
- **Streaming.** The output is written as it is produced, and checked in parallel chunks by declaration.

Until the first measurements, these are working targets:

| Measure | Target |
|---|---|
| Output size vs Tenet trace size | Within 10x |
| Translation time vs Tenet check time | Within 20x |
| A mid-size mathlib file (about 100 theorems) | Translated and verified in under 1 hour on 8 cores |

## Where AI helps

AI stays out of the trusted path. Anything it produces is checked by the Metamath verifiers, so a bad AI output simply fails.

1. **Universe lowering.** When a proof really needs a higher universe, an AI looks for a different argument that stays in plain ZFC, and that argument goes through the translator again.
2. **Shrinking.** It finds shorter `set.mm` proofs for large translated lemmas, which are kept only if they verify.
3. **Bridge lemmas.** It drafts the roughly 200 to 400 bridge lemmas in `set.mm`, which are then reviewed and verified.
4. **Readable summaries.** Optionally, it writes a human-readable outline of what a translated proof does, for mathematicians who want to read it.

## Testing and trust

What you have to trust shrinks to two small things: a Metamath verifier, and the hand-checked table saying the ZFC statement means the same as the Lean one.

1. **Two verifiers.** Every output is checked by two Metamath verifiers written in different languages.
2. **Bad input must fail.** Feed the translator broken Lean proofs, mutated like the tenet-sat fuzzer does. If Tenet rejects them, either no output is produced, or the output fails Metamath. Any pass is a critical bug.
3. **Statement check.** For each headline theorem, compare the translated statement against `set.mm`'s own version of it (for example the infinitude of primes), and prove the two equivalent in `set.mm`.
4. **Corpus.** Start with Lean core, then mathlib's `Nat` and `Int` files, then a larger mathlib slice. Publish pass and fail counts per file, including the failures.
5. **Same-result cross-check.** Theorems that `set.mm` already proves independently (for example the irrationality of √2) must translate to statements equivalent to `set.mm`'s own theorems.

## Milestones

There are five stages, each with a gate that must pass before the next starts.

1. **Trace (2 to 3 weeks).** Add tracing to Tenet. Every definitional-equality step is written out and replayable.
   - Gate: replaying the trace re-derives every check Tenet made, on all of Lean core.
2. **Bridge library (4 to 6 weeks).** Write the `set.mm` bridge lemmas for functions, Prop, proof irrelevance and simple inductives (`Nat`, `Bool`, `List`).
   - Gate: `2 + 2 = 4` and `List.length_append` translate, and both Metamath verifiers accept them.
3. **Full kernel (2 to 3 months).** Mutual and nested inductives, large elimination, quotients, choice, literals.
   - Gate: all of Lean core translates and verifies.
4. **Universe elimination (1 to 2 months).** Instantiation, collection and automatic lowering.
   - Gate: mathlib's `Nat` and `Int` files come out in plain ZFC, with no universe axiom.
5. **Headline result.** Translate a famous theorem end to end in plain ZFC (for example quadratic reciprocity or the infinitude of primes) and publish the outputs and the counts.

## Risks and open questions

The biggest risk is output size. If sharing doesn't keep it near linear, large mathlib proofs become impractical to verify.

| Risk | Impact | Mitigation |
|---|---|---|
| Output blows up on computation-heavy proofs | Gigabytes per theorem, too slow to check | Sharing, the decimal-arithmetic library, and skipping `decide`-heavy proofs in v1 |
| Inductive types are hard to encode in `set.mm` | Stage 3 slips | Start with simple inductives, and build mutual and nested ones on top of a single general fixed-point construction |
| Statement mismatch (the ZFC statement doesn't mean the same as the Lean one) | A "proof" of the wrong thing | Hand-checked definition table and equivalence proofs against `set.mm`'s own definitions |
| Universe lowering fails often | Many results only in ZFC + universes | Report those honestly, and use AI to search for proofs that avoid them |
| Lean's export format changes between versions | Breakage | Pin the Lean version, as leanzempic does |

**Open questions**

- [ ] Is anyone already building a Lean-to-Metamath translator? Check Mario Carneiro's Metamath Zero work first, to build on it rather than duplicate it.
- [ ] Target `set.mm` directly, or Metamath Zero, which is designed for exactly this kind of machine-generated proof?
- [ ] Which headline theorem to aim for first?
