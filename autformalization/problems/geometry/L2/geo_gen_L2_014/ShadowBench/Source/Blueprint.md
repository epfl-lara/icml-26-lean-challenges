# Formalization Blueprint: `geometry/L2/geo_gen_L2_014`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: full source-backed formalization draft for `partial_x_ne_partial_xtilde_at_p`.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`.

The root module already reaches the generated target module.

## Import Plan

```lean
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.Diffeomorph
```

These are the direct Lean imports used by `ShadowBench/Source/Main.lean`, matching the starting imports allowed in `docs/instructions.md`.

## Suggested Search Modules

Non-gating search hints for later proof work only:

- `Mathlib.Analysis.Calculus.FDeriv.Basic` for `fderiv` facts and evaluation of Fréchet derivatives.
- `Mathlib.Analysis.Calculus.ContDiff.Operations` for smoothness of coordinate polynomials and product maps.
- `Mathlib.Geometry.Manifold.Diffeomorph` for diffeomorphism/global-coordinate vocabulary.

## Required Names

- `partial_x_ne_partial_xtilde_at_p`

## Detected Theorem-Like Blocks

1. `line-17` (theorem, lines 17--23) - partial_x_ne_partial_xtilde_at_p

## Definition and Bridge Inventory

The source theorem is written in informal differential-geometric notation. The Lean draft records the representation bridge explicitly:

- `Plane`: abbreviation for the standard coordinate model `ℝ × ℝ` of `ℝ²`.
- `standardX`, `standardY`: standard coordinate functions `x` and `y`.
- `tildeX`, `tildeY`: transformed coordinate functions `x̃ = x` and `ỹ = y + x^3`.
- `tildeCoord`: global coordinate map `p ↦ (x̃ p, ỹ p)`.
- `tildeCoordInv`: explicit inverse coordinate map `(u, v) ↦ (u, v - u^3)`.
- `sourcePoint`: the point `p = (1, 0)` in standard coordinates.
- `IsGlobalSmoothCoord`: bridge predicate for “global smooth coordinates”, asserting two-sided inverse equations and `C^∞` smoothness of the coordinate map and its inverse.
- `standardPartialXAt`: formalizes `∂/∂x|_p` as the Fréchet directional derivative along the standard vector `(1, 0)`.
- `tildePartialXAt`: formalizes `∂/∂x̃|_p` with `ỹ` held fixed, i.e. the Fréchet directional derivative along the standard tangent vector `(1, -3 * p.1^2)` obtained by differentiating the inverse coordinate map.

No definition, structure, class, or instance construction is left as a `sorry` stub.

## Source Inventory Entries

- Source inventory entry `line-17`
- Source inventory entry `line-17`: theorem `partial_x_ne_partial_xtilde_at_p`, source `docs/source.tex:17-23`, Lean declaration `partial_x_ne_partial_xtilde_at_p`.
- Source inventory entry: `line-17`.
- Source inventory entry: line-17.
- Source inventory label: `line-17`.
- Source block label: `line-17`.

## Source Statement Inventory

### line-17

- Source inventory entry: `line-17`
- Source label: `line-17`
- Source block id: `line-17`
- Kind: theorem.
- Source title: `partial_x_ne_partial_xtilde_at_p`.
- Source locator: `docs/source.tex`, theorem block lines 17--23, title `partial_x_ne_partial_xtilde_at_p`.
- Source statement:
  ```text
  Let $(x,y)$ denote the standard coordinates on $\mathbb{R}^2$. Verify that $(\tilde{x}, \tilde{y})$ are global smooth coordinates on $\mathbb{R}^2$, where
  \[ \tilde{x} = x, \quad \tilde{y} = y + x^3. \]
  Let $p$ be the point $(1,0) \in \mathbb{R}^2$ (in standard coordinates), and show that
  \[ \frac{\partial}{\partial x}\bigg|_p \neq \frac{\partial}{\partial \tilde{x}}\bigg|_p, \]
  even though the coordinate functions $x$ and $\tilde{x}$ are identically equal.
  ```
- Planned Lean declarations: `partial_x_ne_partial_xtilde_at_p`.
- Lean statement:
  ```lean
  theorem partial_x_ne_partial_xtilde_at_p :
      IsGlobalSmoothCoord tildeCoord tildeCoordInv ∧
        (∀ q : Plane, standardX q = tildeX q) ∧
        standardPartialXAt sourcePoint ≠ tildePartialXAt sourcePoint := by
    sorry
  ```
- Dependencies:
  - `Plane`, `standardX`, `standardY`, `tildeX`, `tildeY`.
  - `tildeCoord`, `tildeCoordInv`, `sourcePoint`.
  - `IsGlobalSmoothCoord`, `standardPartialXAt`, `tildePartialXAt`.
  - Mathlib notions: `Function.LeftInverse`, `Function.RightInverse`, `ContDiff`, `fderiv`.
- Skeleton candidate used: skeletons 1--3 were used only as hints for introducing coordinate functions, the coordinate map, and directional-derivative operators. They were not copied verbatim: their statement used an undeveloped `IsDiffeomorph` placeholder and inline `let` comments inside the theorem. Skeleton 4 is malformed by an extra proof terminator, so it was not copied. The final statement follows the source theorem directly and adds an explicit bridge predicate for the informal “global smooth coordinates” phrase.
- Formal statement review:
  - The source has three explicit claims: the transformed coordinates are global smooth coordinates; the coordinate functions `x` and `x̃` are identical; the two coordinate partial-derivative operators at `p = (1,0)` are unequal.
  - The Lean theorem preserves these as a conjunction. The first conjunct uses `IsGlobalSmoothCoord tildeCoord tildeCoordInv`; the second is `∀ q, standardX q = tildeX q`; the third is the function-operator inequality `standardPartialXAt sourcePoint ≠ tildePartialXAt sourcePoint`.
  - The Lean derivative operators act on scalar functions `Plane → ℝ`, matching the usual derivation interpretation of coordinate vector fields at a point.
- Source qualifiers:
  - Mathematical object class: the source is about the standard smooth coordinate model of `ℝ²`; the Lean draft uses the explicit model `Plane = ℝ × ℝ`.
  - Quantifier order: first fix the displayed coordinate functions and transformed coordinate map, then fix the distinguished point `p = (1,0)`, then assert the global-coordinate claim, the identity of first coordinate functions for all points, and the inequality of the two partial-derivative operators at that point.
  - Parameter domain: all points of `ℝ²`, represented as all `q : Plane`, for coordinate functions and coordinate maps; scalar test functions for derivations have domain `Plane`.
  - Output codomain: `ℝ` for coordinate functions, `Plane = ℝ × ℝ` for coordinate maps, and `ℝ` for scalar directional derivatives/functionals.
  - Equality/image condition: `x̃ = x`, `ỹ = y + x^3`, the map `(x,y) ↦ (x, y + x^3)` is a global coordinate map with inverse `(u,v) ↦ (u, v - u^3)`, and `x` and `x̃` are pointwise identical.
  - Distinguished point: `p = (1,0)` in standard coordinates.
  - Side condition for `∂/∂x̃`: vary the first transformed coordinate while holding `ỹ` fixed; via the inverse coordinate formula this gives the standard-coordinate tangent vector `(1,-3)` at `p`.
  - Follow-on claim: the first coordinate functions are identical even though the coordinate partial-derivative operators at `p` differ.
- Lean coverage:
  - `Plane`, `standardX`, `standardY`, `tildeX`, and `tildeY` implement the standard-coordinate representation and the equations `x̃ = x`, `ỹ = y + x^3`.
  - `tildeCoord` and `tildeCoordInv` implement the displayed coordinate map and inverse map on the full domain/codomain `Plane`.
  - `sourcePoint` implements the source point `(1,0)` in standard coordinates.
  - `IsGlobalSmoothCoord tildeCoord tildeCoordInv` covers the “global smooth coordinates” claim by asserting two-sided inverse equations and `C^∞` smoothness for the map and inverse.
  - `(∀ q : Plane, standardX q = tildeX q)` covers the follow-on claim that `x` and `x̃` are identically equal.
  - `standardPartialXAt sourcePoint ≠ tildePartialXAt sourcePoint` covers the asserted inequality of the two partial-derivative operators, with these operators represented as Fréchet directional-derivative functionals on scalar functions `Plane → ℝ`.
- Scope changes: none
- Representation bridge note: the source's differential-geometric notation is represented by explicit bridge declarations (`Plane`, `IsGlobalSmoothCoord`, `standardPartialXAt`, and `tildePartialXAt`), so no source claim is omitted, weakened, or strengthened.
- Complete source proof text: no proof is provided in `docs/source.tex`.
- Source proof / prover notes:
  - To prove the global-coordinate conjunct, use the explicit inverse `tildeCoordInv`; algebra shows `tildeCoordInv (tildeCoord p) = p` and `tildeCoord (tildeCoordInv q) = q`. Smoothness follows from smoothness of projections, addition, subtraction, and the polynomial `u^3`.
  - To prove coordinate equality, unfold `standardX` and `tildeX`.
  - To prove operator inequality, use function extensionality contradiction or exhibit the witness `standardY`: `standardPartialXAt sourcePoint standardY = 0`, while `tildePartialXAt sourcePoint standardY = -3` because the `x̃`-coordinate vector at `p` is `(1,-3)`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.

## Formalization Rules Snapshot

```text
open Manifold Function

Formalize in Lean the Theorem (partial_x_ne_partial_xtilde_at_p) from Text.
The theorem must be named `partial_x_ne_partial_xtilde_at_p`.
```

## Review Checklist

- [ ] Source document inspected and source entry recorded.
- [ ] Direct import plan matches `ShadowBench/Source/Main.lean`.
- [ ] Root project module imports the generated target module path.
- [ ] Definitions and representation bridges have concrete Lean implementations, not construction `sorry`s.
- [ ] Source theorem has a stable Lean declaration name and source-aware prover notes.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
