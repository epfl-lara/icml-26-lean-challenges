# Formalization Blueprint: `geometry/L3/geo_gen_L3_002`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the source-backed definitions, bridge structure, and theorem skeleton for `ballRnDiffeomorph`.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`.

No split into additional generated files is currently justified; the source has one theorem and one explicit pair of maps.

## Import Plan

```lean
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Data.Real.StarOrdered
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Sheaf.Basic
```

These are the direct imports used by `ShadowBench/Source/Main.lean`, matching the allowed starting block from `docs/instructions.md`.

## Suggested Search Modules

These are non-gating search/proof hints, not additional required imports:

- `Mathlib.Analysis.Normed.Module.Ball.Homeomorph`: unit-ball homeomorphism facts such as `Homeomorph.unitBall` and its apply lemmas.
- `Mathlib.Analysis.InnerProductSpace.Calculus`: smoothness facts for the unit-ball homeomorphism and squared norm.
- `Mathlib.Analysis.SpecialFunctions.Sqrt`: differentiability and smoothness facts for `Real.sqrt` away from zero.

## Candidate Skeletons

- Dataset: `Lemmy00/ShadowBench-skeletons-prod`
- `docs/skeletons/Skeleton1.lean`
- `docs/skeletons/Skeleton2.lean`
- `docs/skeletons/Skeleton3.lean`
- `docs/skeletons/Skeleton4.lean`

All four skeletons propose the same high-level formula shape for `F` and `G`, but they are not copied verbatim. The skeletons contain ill-scoped variables in inverse clauses, put a `sorry` inside the construction of the subtype-valued map `G`, and use a dubious `≃ᵈ` notation. The final draft keeps the source formulas and theorem name, but replaces those fragile clauses by explicit ambient formulas, a subtype-valued `G` built from a theorem-level landing proof, and a source-local bridge structure `BallRnDiffeomorphismData` bundling smoothness and inverse identities.

## Required Names

- `ballRnDiffeomorph`

## Source Statement Inventory

### line-17

- Source locator: `docs/source.tex`, theorem environment lines 17-26; proof environment lines 28-53.
- Source statement: For the open unit ball $\mathbb{B}^n$ and Euclidean space $\mathbb{R}^n$, the maps $F(x) = x/\sqrt{1 - |x|^2}$ and $G(y) = y/\sqrt{1 + |y|^2}$ are smooth inverse maps, hence diffeomorphisms, so $\mathbb{B}^n$ is diffeomorphic to $\mathbb{R}^n$.
- Planned Lean declarations: `ballRnF`, `ballRnG`, `ballRnFOnBall`, `BallRnDiffeomorphismData`, `ballRnDiffeomorph`
- Declaration descriptions:
  - `BallRnSpace`: abbreviation for Euclidean space of dimension `n` over `ℝ`.
  - `BallRnUnitBall`: subtype of points whose norm is less than `1`, representing $\mathbb{B}^n$.
  - `ballRnF`: ambient formula for `F`, written as scalar multiplication by the inverse square-root denominator.
  - `ballRnG`: ambient formula for `G`, written as scalar multiplication by the inverse square-root denominator.
  - `ballRnFOnBall`: source-domain version of `F` from the open unit ball to Euclidean space.
  - `BallRnDiffeomorphismData`: bridge structure bundling an ambient map on the ball, an inverse map landing in the unit ball, smoothness, and inverse identities.
  - `ballRnDiffeomorph`: theorem skeleton asserting that `ballRnG` lands in the unit ball, the subtype-valued maps are inverse, both formulas are smooth on their stated domains, and the bridge structure exists for these formulas.
- Skeleton candidate used: formula and name cues from Skeletons 1-4; inverse and diffeomorphism clauses redrafted for well-scoped Lean and to avoid construction `sorry` outside theorem proof obligations.
- Dependencies:
  - Euclidean-space and norm notation from `Mathlib.Analysis.InnerProductSpace.Calculus`.
  - Smoothness predicates `ContDiffOn` and `ContDiff`.
  - `Real.sqrt` for the denominator formulas.
  - `Function.LeftInverse` and `Function.RightInverse` from core/Mathlib.
- Formal statement review:
  - The Lean theorem quantifies over `n : ℕ`, matching the source's arbitrary dimension `n`.
  - The Lean unit ball is the open norm ball represented by a subtype of Euclidean space. This is the standard finite-dimensional representation of $\mathbb{B}^n \subset \mathbb{R}^n$.
  - The source formulas are represented as scalar multiplication by inverse square-root denominators, equivalent to vector division by those scalar denominators in a real vector space.
  - The source codomain condition `G : ℝ^n → 𝔹^n` is represented by the theorem-level witness `hG : ∀ y, ‖ballRnG n y‖ < 1` and the subtype-valued local map `G`.
  - The follow-on statement “therefore diffeomorphic” is represented by `BallRnDiffeomorphismData`, which bundles the exact smooth inverse data used in the source proof. This is a source-local bridge rather than Mathlib's manifold `Diffeomorph` object.
- Source qualifiers:
  - Mathematical object class: finite-dimensional Euclidean space $\mathbb{R}^n$ and its open unit ball $\mathbb{B}^n$.
  - Quantifier order: arbitrary dimension `n`, then explicit maps `F` and `G` with formulas fixed by the theorem.
  - Parameter domain: `F` is used on points with norm less than `1`; `G` is used on all Euclidean points.
  - Output codomain: `F` outputs Euclidean points; `G` lands in the open unit ball.
  - Equality/image condition: `G (F x) = x` for ball points and `F (G y) = y` for all Euclidean points.
  - Side conditions: positivity/nonvanishing of square-root denominators under the respective domain hypotheses; smoothness on the open ball for `F` and globally for `G`.
  - Follow-on claim: the smooth inverse data witnesses diffeomorphism between the ball and Euclidean space.
- Lean coverage:
  - `BallRnSpace` and `BallRnUnitBall` cover the object class and domain/codomain representation.
  - `ballRnF`, `ballRnG`, and `ballRnFOnBall` cover the two formulas and the domain restriction for `F`.
  - `hG` in `ballRnDiffeomorph` covers the codomain claim for `G`.
  - The `ContDiffOn` and `ContDiff` clauses in `ballRnDiffeomorph` cover the smoothness claims.
  - `Function.LeftInverse G F` and `Function.RightInverse G F` cover the two inverse computations.
  - `∃ D : BallRnDiffeomorphismData n, D.toFun = ballRnF n ∧ D.invFun = ballRnG n` records the diffeomorphism-data bridge.
- Scope changes: none
- Representation bridge: the source's “diffeomorphism” claim is encoded by the explicit source-local smooth-inverse-data structure `BallRnDiffeomorphismData` rather than by a Mathlib manifold `Diffeomorph` value. Smoothness of the source maps with ball domain/codomain is encoded through ambient `ContDiffOn`/`ContDiff` clauses plus the subtype landing and inverse clauses. This is an explicit representation bridge, not an omitted source qualifier; there is no mathematical weakening, strengthening, or omission.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text:

  ```latex
  To show that $F$ and $G$ are inverses, we first compute $|F(x)|^2$ for $x \in \mathbb{B}^n$:
  \[
  |F(x)|^2 = \frac{|x|^2}{1 - |x|^2}.
  \]
  Then, substituting $F(x)$ into $G$, we have:
  \[
  G(F(x)) = \frac{F(x)}{\sqrt{1 + |F(x)|^2}} = \frac{\frac{x}{\sqrt{1 - |x|^2}}}{\sqrt{1 + \frac{|x|^2}{1 - |x|^2}}} = \frac{\frac{x}{\sqrt{1 - |x|^2}}}{\sqrt{\frac{1 - |x|^2 + |x|^2}{1 - |x|^2}}} = \frac{\frac{x}{\sqrt{1 - |x|^2}}}{\frac{1}{\sqrt{1 - |x|^2}}} = x.
  \]

  Similarly, for $y \in \mathbb{R}^n$, we compute $|G(y)|^2$:
  \[
  |G(y)|^2 = \frac{|y|^2}{1 + |y|^2}.
  \]
  Substituting $G(y)$ into $F$, we have:
  \[
  F(G(y)) = \frac{G(y)}{\sqrt{1 - |G(y)|^2}} = \frac{\frac{y}{\sqrt{1 + |y|^2}}}{\sqrt{1 - \frac{|y|^2}{1 + |y|^2}}} = \frac{\frac{y}{\sqrt{1 + |y|^2}}}{\sqrt{\frac{1 + |y|^2 - |y|^2}{1 + |y|^2}}} = \frac{\frac{y}{\sqrt{1 + |y|^2}}}{\frac{1}{\sqrt{1 + |y|^2}}} = y.
  \]

  Next, we address smoothness:
  \begin{itemize}
      \item $F$ is smooth on $\mathbb{B}^n$ because the function $|x|^2 = \sum (x^i)^2$ is smooth, and the denominator $\sqrt{1 - |x|^2}$ is smooth and strictly positive for all $|x| < 1$.
      \item $G$ is smooth on $\mathbb{R}^n$ because the denominator $\sqrt{1 + |y|^2}$ is smooth and satisfies $\sqrt{1 + |y|^2} \ge 1$ for all $y \in \mathbb{R}^n$, so it never vanishes.
  \end{itemize}
  Since $F$ and $G$ are smooth maps and $G = F^{-1}$, both are diffeomorphisms.
  ```

- Source proof / prover notes: The source proof computes `‖F x‖^2 = ‖x‖^2 / (1 - ‖x‖^2)` for `‖x‖ < 1`, substitutes this into `G` to get `G (F x) = x`, computes `‖G y‖^2 = ‖y‖^2 / (1 + ‖y‖^2)`, substitutes this into `F` to get `F (G y) = y`, and proves smoothness from smooth squared norm plus positive square-root denominators.
- Detailed prover notes:
  - Prove `hG` using `norm_smul`, positivity of `Real.sqrt (1 + ‖y‖ ^ 2)`, and the inequality `‖y‖ ^ 2 / (1 + ‖y‖ ^ 2) < 1`.
  - For inverse identities, reduce subtype equality with `Subtype.ext`, unfold `ballRnF` and `ballRnG`, use the two norm-square computations from the source, and simplify square roots using positivity from `‖x‖ < 1` or `0 ≤ ‖y‖ ^ 2`.
  - For smoothness, search for `OpenPartialHomeomorph.contDiff_univUnitBall`, `OpenPartialHomeomorph.contDiffOn_univUnitBall_symm`, and sqrt/`ContDiff` composition lemmas. If those do not match directly, prove smoothness by composing smooth squared norm, subtraction/addition, `Real.sqrt` away from zero, inverse, and scalar multiplication.

## Handoff Checklist

- [x] Source document inspected with theorem-like block `line-17` recorded.
- [x] Candidate skeletons compared against the source and not copied blindly.
- [x] Blueprint source inventory has declaration names, dependencies, statement-fidelity review, source qualifiers, Lean coverage, scope notes, and prover notes.
- [x] Root project module imports the generated target path through `ShadowBench.lean` and `ShadowBench/Source.lean`.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [x] Proof-ready handoff accepted for the later prove workflow by formalization PASS and 2026-06-05 audit.
