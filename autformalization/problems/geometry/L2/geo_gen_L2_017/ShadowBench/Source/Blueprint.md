# Formalization Blueprint: `geometry/L2/geo_gen_L2_017`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Source Statement Inventory

### line-17

- Source inventory entry: `line-17`
- Source kind/title: theorem `convex_partialSum`.
- Source locator: `docs/source.tex`, theorem environment lines 17-22; proof lines 24-56.
- Source statement: if S₁ and S₂ are convex subsets of ℝ^(m+n), then their partial sum
  S = {(x, y₁ + y₂) | x ∈ ℝ^m, y₁, y₂ ∈ ℝ^n, (x, y₁) ∈ S₁, (x, y₂) ∈ S₂}
  is convex.
- Planned Lean declarations:
  - `productCoordinatesEquiv`: implemented bridge for the source's standard identification of a vector in `ℝ^(m+n)` with a pair of coordinate blocks in `ℝ^m × ℝ^n`.
  - `partialSum`: implemented bridge definition for the source partial-sum set in product coordinates.
  - `convex_partialSum`: theorem stating convexity of `partialSum S₁ S₂`.
- Skeleton candidate used: `docs/skeletons/Skeleton1.lean` shaped the final statement. Skeletons 2 and 3 are materially the same statement with fewer explicit imports. Skeleton4 is malformed and was not used. The final Lean draft factors the inline `let S := ...` set into the implemented definition `partialSum` so the source's named partial sum can be referenced directly, and adds `productCoordinatesEquiv` to record the ambient-coordinate bridge.
- Dependencies:
  - `Mathlib.Logic.Equiv.Fin.Basic` for `Fin.appendEquiv`, the coordinate-block equivalence `productCoordinatesEquiv`.
  - `Mathlib.Analysis.InnerProductSpace.PiL2` for the finite-coordinate Euclidean spaces `Fin m → ℝ` and `Fin n → ℝ`.
  - `Mathlib.Analysis.Convex.Basic` for `Convex` and the convex-combination API likely used by the prover.
  - Search notes: `convex_iff_add_mem` is the expected proof entry point; convexity of `S₁` and `S₂` supplies membership of the two coordinatewise convex combinations.
- Formal statement review:
  - Quantifies explicitly over `m n : ℕ`, then over `S₁ S₂ : Set ((Fin m → ℝ) × (Fin n → ℝ))`, then assumes `Convex ℝ S₁` and `Convex ℝ S₂`.
  - `productCoordinatesEquiv m n : (Fin m → ℝ) × (Fin n → ℝ) ≃ (Fin (m + n) → ℝ)` records the standard equivalence between the product-coordinate Lean statement and the source phrase `ℝ^(m+n)`.
  - The set `partialSum S₁ S₂` contains exactly those pairs `p` for which there exist `x : Fin m → ℝ` and `y₁ y₂ : Fin n → ℝ` with `(x, y₁) ∈ S₁`, `(x, y₂) ∈ S₂`, and `p = (x, y₁ + y₂)`.
  - The conclusion is `Convex ℝ (partialSum S₁ S₂)`.
- Source qualifiers:
  - Mathematical object class: convex subsets of a finite-dimensional real vector space written in the source as `ℝ^(m+n)` and immediately used in split coordinates `(x, y)` with `x ∈ ℝ^m` and `y ∈ ℝ^n`.
  - Quantifier order: dimensions `m n`, sets `S₁ S₂`, convexity assumptions, then convexity conclusion for the defined partial sum.
  - Parameter domain: `m n : ℕ`; points represented by functions `Fin m → ℝ` and `Fin n → ℝ` for the two coordinate blocks.
  - Output codomain: a subset of the same ambient split product space as `S₁` and `S₂`.
  - Equality/image condition: membership in the partial sum is expressed by `p = (x, y₁ + y₂)` with both witnesses using the same `x` and with `(x, y₁) ∈ S₁`, `(x, y₂) ∈ S₂`.
  - Side conditions: no nonemptiness, closedness, boundedness, positivity, or restrictions on `m n` appear in the source or Lean statement.
  - Follow-on claims: the only source conclusion is convexity of `S`.
- Lean coverage: `productCoordinatesEquiv` records the standard `Fin (m+n)`/product-coordinate equivalence; `convex_partialSum (m n : ℕ) (S₁ S₂ : Set ((Fin m → ℝ) × (Fin n → ℝ)))` preserves the source dimensions and set parameters; hypotheses `(h₁ : Convex ℝ S₁)` and `(h₂ : Convex ℝ S₂)` match the source convexity assumptions; `partialSum` uses exactly the witnesses `x y₁ y₂`, the same first coordinate `x`, memberships in `S₁` and `S₂`, and equality `p = (x, y₁ + y₂)`; the conclusion is `Convex ℝ (partialSum S₁ S₂)` with no extra side conditions or follow-on conclusions.
- Scope changes: none
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text:

```text
To show that $S$ is convex, let $z, z' \in S$ and let $\theta \in [0, 1]$. We need to show that $\theta z + (1 - \theta)z' \in S$.

By the definition of $S$, we can write:
\begin{itemize}
    \item $z = (x, y_1 + y_2)$ where $(x, y_1) \in S_1$ and $(x, y_2) \in S_2$.
    \item $z' = (x', y'_1 + y'_2)$ where $(x', y'_1) \in S_1$ and $(x', y'_2) \in S_2$.
\end{itemize}

Now, consider the convex combination:
\begin{align*}
\theta z + (1 - \theta)z' &= \theta(x, y_1 + y_2) + (1 - \theta)(x', y'_1 + y'_2) \\
&= (\theta x + (1 - \theta)x', \theta(y_1 + y_2) + (1 - \theta)(y'_1 + y'_2)) \\
&= (\theta x + (1 - \theta)x', (\theta y_1 + (1 - \theta)y'_1) + (\theta y_2 + (1 - \theta)y'_2)).
\end{align*}

Let $\bar{x} = \theta x + (1 - \theta)x'$, $\bar{y}_1 = \theta y_1 + (1 - \theta)y'_1$, and $\bar{y}_2 = \theta y_2 + (1 - \theta)y'_2$.
Then we have $\theta z + (1 - \theta)z' = (\bar{x}, \bar{y}_1 + \bar{y}_2)$.

To verify that this point is in $S$, we check the conditions on $(\bar{x}, \bar{y}_1)$ and $(\bar{x}, \bar{y}_2)$:
\begin{enumerate}
    \item Since $S_1$ is convex and $(x, y_1), (x', y'_1) \in S_1$, it follows that:
    \[
    \theta(x, y_1) + (1 - \theta)(x', y'_1) = (\theta x + (1 - \theta)x', \theta y_1 + (1 - \theta)y'_1) = (\bar{x}, \bar{y}_1) \in S_1.
    \]
    \item Since $S_2$ is convex and $(x, y_2), (x', y'_2) \in S_2$, it follows that:
    \[
    \theta(x, y_2) + (1 - \theta)(x', y'_2) = (\theta x + (1 - \theta)x', \theta y_2 + (1 - \theta)y'_2) = (\bar{x}, \bar{y}_2) \in S_2.
    \]
\end{enumerate}

Since $(\bar{x}, \bar{y}_1) \in S_1$ and $(\bar{x}, \bar{y}_2) \in S_2$, the vector $(\bar{x}, \bar{y}_1 + \bar{y}_2)$ satisfies the definition of $S$. Thus, $\theta z + (1 - \theta)z' \in S$, which proves that $S$ is a convex set.
```

- Prover notes:
  - Unfold `partialSum` and use `convex_iff_add_mem` or the defining `Convex`/`StarConvex` API.
  - For `z` and `z'` in `partialSum S₁ S₂`, destruct witnesses as `⟨x, y₁, y₂, hy₁, hy₂, rfl⟩` and `⟨x', y₁', y₂', hy₁', hy₂', rfl⟩`.
  - Use convexity of `S₁` on `(x, y₁)` and `(x', y₁')`, and convexity of `S₂` on `(x, y₂)` and `(x', y₂')`.
  - Provide witnesses `θ • x + (1 - θ) • x'`, `θ • y₁ + (1 - θ) • y₁'`, and `θ • y₂ + (1 - θ) • y₂'` for the resulting point. Coordinate simplification in products and Pi spaces should close the final equality with extensionality/simp plus module algebra.

## Import Plan

```lean
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Basic
```

## Suggested Search Modules

- `Mathlib.Logic.Equiv.Fin.Basic` — `Fin.appendEquiv` and coordinate splitting/joining facts.
- `Mathlib.Analysis.Convex.Basic` — `Convex`, `convex_iff_add_mem`, convex-combination lemmas.
- `Mathlib.Analysis.InnerProductSpace.PiL2` — finite-coordinate real vector space instances.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: imports the direct dependencies above, defines `productCoordinatesEquiv` and `partialSum`, and declares `convex_partialSum` with a proof placeholder for the prover workflow.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`.
- No file split is currently needed because the source has one theorem and two small bridge definitions.

## Required Names

- `convex_partialSum`

## Statement/Source Review Gate

- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [ ] After that approval, the prover workflow may run `/prove ShadowBench/Source/Main.lean convex_partialSum`.
