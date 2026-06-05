# Formalization Blueprint: `analysis/L2/ana_gen_L2_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Source Inventory Summary

The source document has no section headings and contains two named items:

1. `line-17` — Definition `[MeromorphicAt]`, `docs/source.tex` lines 17-22.
2. `line-24` — Lemma `[AnalyticAt.meromorphicAt]`, `docs/source.tex` statement lines 24-26, with proof at lines 29-35.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the source-backed definition `MeromorphicAt` and lemma skeleton `AnalyticAt.meromorphicAt`.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so the generated target is covered by the root project build.

No file split is currently useful because the source has one definition and one elementary lemma.

## Import Plan

Direct imports in `ShadowBench/Source/Main.lean`:

```lean
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
```

These are the imports supplied by `docs/instructions.md`. They provide `AnalyticAt`, scalar powers, normed-space infrastructure, and the formalization-rule context used by the candidate skeletons.

## Suggested Search Modules

- `Mathlib.Analysis.Analytic.Basic` and `Mathlib.Analysis.Analytic.Constructions` for `AnalyticAt` facts and simplification of analytic expressions.
- `Mathlib.Analysis.Meromorphic.Basic` as a reference only: Mathlib already has declarations named `MeromorphicAt` and `AnalyticAt.meromorphicAt` with the same mathematical content, but importing this module into the generated file would collide with the required top-level ShadowBench declaration names.

## Candidate Skeletons

- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` all propose the same definition and theorem shape with explicit variables `(K) (E)` and assumptions `[NormedField K] [Nontrivial K]`.
- `docs/skeletons/Skeleton4.lean` uses `[NontriviallyNormedField 𝕜]`, matching the source phrase "nontrivially normed field" more directly.
- Adopted shape: Skeleton4's class choice and source formula, with the field parameter inferred from `f : 𝕜 → E` rather than carried as an explicit argument to `MeromorphicAt`; the proof of the lemma is left as `by sorry` for the prover phase.

## Required Names

- `MeromorphicAt`
- `AnalyticAt.meromorphicAt`

## Source Statement Inventory

### line-17

- Planned Lean declarations: `MeromorphicAt`
- Source item: Definition `[MeromorphicAt]`.
- Source locator: `docs/source.tex`, definition `[MeromorphicAt]`, lines 17-22.
- Source statement: Let `𝕜` be a nontrivially normed field and let `E` be a normed vector space over `𝕜`. For `f : 𝕜 → E` and `x : 𝕜`, `f` is meromorphic at `x` iff there exists `n : ℕ` such that `z ↦ (z - x)^n f z` is analytic at `x`.
- Skeleton candidate used: Skeleton4 for the `NontriviallyNormedField` binder; Skeleton1-3 agree on the core formula.
- Dependencies: `AnalyticAt`, natural powers in the scalar field, scalar multiplication of the scalar `(z - x)^n` on the vector `f z`.
- Formal statement review: Lean uses `def MeromorphicAt {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (f : 𝕜 → E) (x : 𝕜) : Prop := ∃ n : ℕ, AnalyticAt 𝕜 (fun z => (z - x) ^ n • f z) x`. This is definitionally the source predicate, with source juxtaposition `(z - x)^n f(z)` represented by scalar multiplication `•` because `f z : E`.
- Source qualifiers: mathematical object class = nontrivially normed field `𝕜` and normed vector space `E`; quantifier order = field, space, function, point, then existence of `n : ℕ`; parameter domain = `𝕜`; output codomain = `E`; side condition = analyticity at `x` of the weighted function; equality/image condition = none beyond the defining iff-by-definition; follow-on claims = none.
- Lean coverage: all source qualifiers are represented in the definition's binders and body.
- Scope changes: none. Notation is translated from scalar-valued multiplication in prose to Lean scalar multiplication `•`, the intended representation bridge for an `E`-valued function.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: This is a definition, so there is no proof. Future proofs should unfold `MeromorphicAt` and produce a natural number witness.

### line-24

- Planned Lean declarations: `AnalyticAt.meromorphicAt`
- Source item: Lemma `[AnalyticAt.meromorphicAt]`.
- Source locator: `docs/source.tex`, lemma `[AnalyticAt.meromorphicAt]`, statement lines 24-26, proof lines 29-35.
- Source statement: For `f : 𝕜 → E` and `x : 𝕜`, if `f` is analytic at `x`, then `f` is meromorphic at `x`.
- Complete source proof text: "Assume that `f` is analytic at `x`. Choose `n = 0`. Then `(z - x)^0 f(z) = f(z)`, which is analytic at `x` by assumption. Hence `f` is meromorphic at `x` by definition."
- Skeleton candidate used: Skeleton4 for the implicit binders and the exact required name; Skeleton1-3 contain the same proposition with explicit `(f) (x)` parameters.
- Dependencies: definition `MeromorphicAt`; hypothesis `hf : AnalyticAt 𝕜 f x`; simplifications `pow_zero` and `one_smul` after choosing witness `0`.
- Formal statement review: Lean uses `lemma AnalyticAt.meromorphicAt {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E} {x : 𝕜} (hf : AnalyticAt 𝕜 f x) : MeromorphicAt f x := by sorry`. This preserves the source field, space, function, point, and implication. The function and point are implicit because the source quantifies them universally and the theorem is intended for term rewriting/application.
- Source qualifiers: mathematical object class = nontrivially normed field and normed vector space; quantifier order = field, space, function, point, analytic hypothesis; parameter domain = `𝕜`; output codomain = `E`; side condition = `AnalyticAt 𝕜 f x`; conclusion = `MeromorphicAt f x`; follow-on claims = none.
- Lean coverage: all source qualifiers are represented in the binders, hypothesis, and conclusion. The definition entry supplies the bridge from prose multiplication to scalar multiplication.
- Scope changes: none. Universally quantified parameters are represented as implicit Lean binders.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: Unfold `MeromorphicAt`, use witness `0`, then simplify `(z - x)^0 • f z` to `f z` with `pow_zero` and `one_smul`; the remaining goal is exactly `hf`. A likely proof term is `⟨0, by simpa only [pow_zero, one_smul] using hf⟩`, but the planner draft intentionally leaves `by sorry` for the later `/prove` workflow.

## Handoff Notes

- Definition and statement construction gaps: none; the definition is fully implemented and the only intended proof obligation is the lemma `AnalyticAt.meromorphicAt`.
- [ ] Run independent statement/source verification review and apply corrections.
- [ ] Mark stable theorem/lemma/example `sorry` declarations ready for a user-started prove workflow.
- Suggested proof command after review: `/prove ShadowBench/Source/Main.lean AnalyticAt.meromorphicAt`.
