# Formalization Blueprint: `geometry/L2/geo_gen_L2_016`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Source Inventory

- `line-17`: source theorem `hyperbolic_set_convex`, Lean theorem `hyperbolic_set_convex`, source `docs/source.tex` theorem block lines 17-20 with proof environment lines 22-33.

## Source Statement Inventory

### line-17

- Planned Lean declarations: `hyperbolicSet`, `hyperbolic_set_convex`.
- Declaration mapping: `hyperbolicSet` implements the displayed set `S`; `hyperbolic_set_convex` states its convexity.
- Source locator: `docs/source.tex`, label `line-17`, theorem block lines 17-20; proof environment lines 22-33, proof body lines 23-32.
- Source title/name: `hyperbolic_set_convex`.
- Source statement: Show that the hyperbolic set `S = {x ∈ ℝ_+^n | ∏_{i=1}^n x_i ≥ 1}` is convex. Hint: if `a, b ≥ 0` and `0 ≤ θ ≤ 1`, then `a^θ b^(1-θ) ≤ θ a + (1-θ)b`.
- Lean statement: `hyperbolic_set_convex : (n : ℕ) → Convex ℝ (hyperbolicSet n)`.
- Skeleton candidate used: Skeletons 1-3 supplied the basic `Fin n → ℝ` and `Convex ℝ` shape. They used strict positivity `0 < x i`; the source proof and hint use nonnegativity (`x_i ≥ 0`, `a,b ≥ 0`), so the final draft uses `0 ≤ x i`. Skeleton4 is malformed and was not used.
- Dependencies:
  - Direct imports: `Mathlib.Analysis.InnerProductSpace.Basic`, `Mathlib.Analysis.MeanInequalities`.
  - Mathematical proof dependencies expected later: unfolding `Convex`, coordinatewise linear-combination nonnegativity, finite product monotonicity over nonnegative factors, and weighted AM-GM for nonnegative reals.
- Source qualifiers:
  - Mathematical object class: the hyperbolic set in the finite-dimensional nonnegative orthant `ℝ_+^n`.
  - Quantifier order: for an arbitrary finite dimension `n`, define the set `S` of vectors satisfying the displayed coordinate predicates, then assert that this set is convex.
  - Parameter domain: `n` is an arbitrary natural dimension; the source does not state a separate positivity hypothesis for `n`.
  - Output codomain: the theorem is a proposition asserting convexity of a subset of real coordinate vectors.
  - Lean representation bridge: vectors in `ℝ_+^n` are represented by functions `Fin n → ℝ` satisfying `∀ i, 0 ≤ x i`.
  - Equality/image condition: `S` is exactly the displayed set `{x | x ∈ ℝ_+^n ∧ ∏ᵢ xᵢ ≥ 1}`; there is no additional image or equality claim.
  - Side conditions: set membership requires coordinatewise nonnegativity and finite coordinate product at least `1`; convexity is over real scalars and the real vector-space structure on `Fin n → ℝ`.
  - Follow-on claims: the weighted AM-GM sentence is explicitly labelled as a hint and is proof guidance, not a separate theorem claim that must be exported as another declaration.
- Lean coverage: exact. The companion definition `hyperbolicSet (n : ℕ) : Set (Fin n → ℝ)` records the representation bridge and both source membership predicates, and `hyperbolic_set_convex (n : ℕ) : Convex ℝ (hyperbolicSet n)` asserts convexity of the whole displayed set, not merely closure under one fixed convex combination.
- Scope changes: none. The source does not impose `n > 0`; Lean's `n : ℕ` formalizes the arbitrary finite-dimensional parameter and includes the vacuous empty-dimensional case rather than omitting any source case.
- Formal statement review: the Lean definition records both source predicates (`x ∈ ℝ_+^n` and `∏ x_i ≥ 1`), and the Lean theorem states `Convex ℝ` of exactly that set.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text:

  ```text
  Let $x, y \in S$ and let $\theta \in [0, 1]$. We need to show that $z = \theta x + (1-\theta)y \in S$.
  Since $x_i \ge 0$ and $y_i \ge 0$ for all $i$, it is clear that $z_i = \theta x_i + (1-\theta)y_i \ge 0$.

  Now we evaluate the product condition. According to the weighted AM-GM inequality (the hint provided):
  \[ x_i^\theta y_i^{1-\theta} \le \theta x_i + (1-\theta)y_i, \quad \forall i = 1, \dots, n. \]
  Taking the product over all $i$:
  \[ \prod_{i=1}^n (\theta x_i + (1-\theta)y_i) \ge \prod_{i=1}^n \left( x_i^\theta y_i^{1-\theta} \right) = \left( \prod_{i=1}^n x_i \right)^\theta \left( \prod_{i=1}^n y_i \right)^{1-\theta}. \]
  Since $x, y \in S$, we have $\prod x_i \ge 1$ and $\prod y_i \ge 1$. Substituting these into the inequality:
  \[ \prod_{i=1}^n z_i \ge (1)^\theta (1)^{1-\theta} = 1. \]
  Thus $z \in S$, which proves that the set $S$ is convex.
  ```
- Prover notes: unfold `hyperbolicSet` and `Convex`. For a convex combination `a • x + b • y` with `a,b ≥ 0` and `a+b=1`, prove each coordinate nonnegative by `nlinarith`/positivity. For the product condition, use the weighted AM-GM hint coordinatewise or pass to nonnegative reals and use `NNReal.geom_mean_le_arith_mean_weighted`; then multiply the inequalities and combine with the membership product bounds. The proof may need lemmas about `Real.rpow`, nonnegative finite products, and `Finset.prod_le_prod`/`Finset.prod_nonneg`.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the bridge definition `hyperbolicSet` and theorem skeleton `hyperbolic_set_convex` with source-aware doc comments.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`, so the root library includes the generated target module.
- `ShadowBench.lean`: imports `ShadowBench.Source`.

## Import Plan

```lean
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MeanInequalities
```

## Suggested Search Modules

These are proof-search hints only and are not direct imports unless a later prover run needs them and Lean verification justifies the change.

- `Mathlib.Analysis.Convex.Basic`
- `Mathlib.Analysis.Convex.Jensen`
- `Mathlib.Analysis.Convex.SpecificFunctions.Basic`
- `Mathlib.Analysis.MeanInequalities`

## Required Names

- `hyperbolic_set_convex`

## Statement/Source Review Checklist

- [x] Source document and preflight manifest inspected.
- [x] Companion instructions and candidate skeletons read.
- [x] Blueprint source inventory includes `line-17` with source proof and prover notes.
- [x] Target Lean draft contains the required declaration name and a source-aware doc comment.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [x] Proof-ready handoff accepted for the later prove workflow by formalization PASS and 2026-06-05 audit.

## Formalization Rules Snapshot

```text
open Finset Real

/-
Formalize in Lean the Theorem (hyperbolic_set_convex) from Text.

The theorem must be named `hyperbolic_set_convex`.
   Matched text (candidate 0, theorem, label=hyperbolic_set_convex): \begin{theorem}[hyperbolic_set_convex] Show that the hyperbolic set $S = \{x \in
                                                                     \mathbb{R}_+^n \mid \prod_{i=1}^n x_i \ge 1\}$ is convex. \textit{Hint:} If $a, b \ge 0$ and
                                                                     $0 \le \theta \le 1$, then $a^\theta b^{1-\theta} \le \theta a + (1-\theta)b$. \end{theorem}
-/
```
