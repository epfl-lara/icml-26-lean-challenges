# Formalization Blueprint: `analysis/L2/ana_gen_L2_002`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Source Read Summary

- `docs/source.tex` was inspected directly and by `formalization_document_inspect`; extraction status: ok.
- Preflight manifest read from `.epflemma/workflow-state/formalization/docs-source/manifest.json`.
- No bibliography files, labels, references, figures, PDFs, or other local assets were listed in the manifest.
- `docs/instructions.md` requires the declaration name `young_inequality_of_nonneg` and lists the starting import block below.

## Generated File Layout

Single-file layout retained.

- Decision: no split. The source has one theorem, no separate definitions or constructions, and the generated Lean scope consists of one source-backed theorem declaration plus the existing root import file. A multi-file split would add import indirection without improving organization.
- `ShadowBench/Source/Main.lean`: contains the source-backed Young inequality theorem skeleton `young_inequality_of_nonneg` and its source-aware proof notes.
- `ShadowBench/Source.lean`: root project module importing `ShadowBench.Source.Main`, so plain project builds check the generated formalization.

## Candidate Skeletons

- Dataset: `Lemmy00/ShadowBench-skeletons-prod`.
- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` give the same implicit-argument Real statement with assumptions `0 ≤ a`, `0 ≤ b`, `0 < p`, `0 < q`, and `1 / p + 1 / q = 1`.
- `docs/skeletons/Skeleton4.lean` gives the same Real statement with explicit arguments and the requested name.
- Adopted shape: explicit Real-variable theorem, matching Skeleton4's source-oriented explicit quantification, but ordered as `a b p q` to follow the source text before listing the hypotheses. This preserves the source domains and conclusion.

## Import Plan

Direct Lean imports used by `ShadowBench/Source/Main.lean`:

```lean
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Real.ConjExponents
```

## Suggested Search Modules

These are proof-search hints, not current direct imports:

- `Mathlib.Analysis.MeanInequalities`
- `Real.young_inequality_of_nonneg`
- `Real.HolderConjugate` / `Real.HolderTriple`
- `geom_mean_le_arith_mean2_weighted`

## Required Names

- `young_inequality_of_nonneg`

## Statement Inventory

### Source theorem: Young's inequality

- Planned Lean declaration: `young_inequality_of_nonneg`
- Source locator: `docs/source.tex`, lines 17--27.
- Skeleton candidate used: Skeleton4 for explicit argument style, with Skeleton1--3 confirming the same mathematical statement. The final statement uses explicit variables `(a b p q : ℝ)` in source order.
- Dependencies: Real powers and division over `ℝ`; positivity and nonnegativity hypotheses; conjugate-exponent identity `1 / p + 1 / q = 1`; source proof uses weighted AM-GM. Mathlib proof search should consider `Mathlib.Analysis.MeanInequalities` and `Real.young_inequality_of_nonneg`.
- Lean declaration:

```lean
theorem young_inequality_of_nonneg
    (a b p q : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : 0 < p) (hq : 0 < q)
    (hpq : 1 / p + 1 / q = 1) :
    a * b ≤ a ^ p / p + b ^ q / q := by
  sorry
```

- Formal statement review: The source states that non-negative real numbers `a,b` and positive real numbers `p,q` with `1/p + 1/q = 1` satisfy `ab ≤ a^p/p + b^q/q`. The Lean statement quantifies all four variables over `ℝ`, includes the nonnegativity and positivity hypotheses, includes the same conjugacy equation using real division, and concludes the same real inequality with real exponentiation notation.
- Source qualifiers:
  - Mathematical object class: real numbers `a`, `b`, `p`, `q`.
  - Quantifier order: `a`, `b`, then `p`, `q`.
  - Parameter domain: `0 ≤ a`, `0 ≤ b`, `0 < p`, `0 < q`.
  - Equality condition: `1 / p + 1 / q = 1`.
  - Output codomain: proposition over real inequality.
  - Inequality conclusion: `a * b ≤ a ^ p / p + b ^ q / q`.
  - Proof dependency/follow-on note: weighted AM-GM applied to `(a^p, b^q)` with weights `(p⁻¹, q⁻¹)`.
- Lean coverage:
  - `(a b p q : ℝ)` covers the real-number object class and codomain.
  - `(ha : 0 ≤ a)` and `(hb : 0 ≤ b)` cover non-negative `a,b`.
  - `(hp : 0 < p)` and `(hq : 0 < q)` cover positive `p,q`.
  - `(hpq : 1 / p + 1 / q = 1)` covers the conjugate-exponent equation.
  - The theorem conclusion is exactly the source inequality in Lean notation.
- Scope changes: none for the theorem statement. The misspelling "inequility" in the source title is normalized only in prose. No separate formal theorem is introduced for weighted AM-GM because it is a proof dependency, not a named source statement.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text:

```text
Since p^{-1} + q^{-1} = 1, by the weighted AM-GM inequality, we have
{a^p}^{p^{-1}}{b^q}^{q^{-1}} ≤ p^{-1}a^p + q^{-1} b^q
which is equivalent to
ab ≤ a^p/p + b^q/q.
```

- Source proof / prover notes: The source proof is a one-step weighted AM-GM argument with weights `p⁻¹` and `q⁻¹`. In Mathlib, a likely short proof is to import/search `Mathlib.Analysis.MeanInequalities`, build `hpq' : p.HolderConjugate q` from `hp`, `hq`, and `hpq` using the `HolderTriple` fields (`inv_add_inv_eq_inv`, `left_pos`, `right_pos`), and then apply `Real.young_inequality_of_nonneg ha hb hpq'`. The conversion from `1 / p` to `p⁻¹` should be handled by `simpa [one_div] using hpq`.

## Handoff Notes

- The theorem proof is intentionally left as `by sorry` for the later `/prove` workflow after independent statement/source verification.
- Suggested next command after review approval: `/prove ShadowBench/Source/Main.lean young_inequality_of_nonneg`.
