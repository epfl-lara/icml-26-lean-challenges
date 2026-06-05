# Formalization Blueprint: `geometry/L2/geo_gen_L2_003`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the source theorem skeleton `erdos_mordell_inequality`.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so the generated target module is covered by the project root target.

## Import Plan

```lean
import Mathlib.Geometry.Euclidean.Projection
import Mathlib.Analysis.InnerProductSpace.PiL2
```

## Suggested Search Modules

- `Mathlib.Geometry.Euclidean.Projection`: `EuclideanGeometry.orthogonalProjection`, distance to affine subspaces, projection lemmas.
- `Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional`: `Collinear`, `affineSpan`, finite-dimensional affine geometry.
- `Mathlib.Analysis.InnerProductSpace.PiL2`: `EuclideanSpace` model for `ℝ²`.
- Possible proof-search hints: Erdős--Mordell can be reduced to known Euclidean inequalities after expressing side distances as distances to orthogonal projections onto the side lines.

## Required Names

- `erdos_mordell_inequality`

## Source Statement Inventory

- Source inventory entry `thm:erdos_mordell`: theorem `[erdos_mordell_inequality]` in `docs/source.tex`.
- Source inventory entry: `thm:erdos_mordell`
- Source inventory label: `thm:erdos_mordell`

### thm:erdos_mordell

- Source label: `thm:erdos_mordell`.
- Source title/kind: theorem `[erdos_mordell_inequality]`.
- Source locator: `docs/source.tex`, lines 17--23, theorem environment titled `erdos_mordell_inequality`, label `thm:erdos_mordell`.
- Source statement: In Euclidean geometry, for any triangle `ABC` and point `P` inside `ABC`, if `PL`, `PM`, `PN` are the perpendiculars from `P` to the sides `BC`, `CA`, `AB`, then `PA + PB + PC ≥ 2(PL + PM + PN)`.
- Complete source proof text: no proof is supplied in the source document.
- Planned Lean declarations: `erdos_mordell_inequality`.
- Skeleton candidate used: based on `docs/skeletons/Skeleton4.lean` for the use of `orthogonalProjection` onto affine side lines, with the variable-shadowing issue corrected; compared against `Skeleton1`--`Skeleton3`, which use an unresolved `projection` name and omit the explicit noncollinearity assumption required by “triangle”.
- Dependencies:
  - `EuclideanSpace ℝ (Fin 2)` for the ambient Euclidean plane.
  - `¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2)))` to express the nondegenerate triangle condition.
  - Positive barycentric coordinates `u v w` with `u + v + w = 1` to express that `P` is strictly inside the triangle.
  - `EuclideanGeometry.orthogonalProjection (affineSpan ℝ ({B, C} : Set _)) P`, and analogues for `CA` and `AB`, to represent the feet of perpendiculars on the side lines.
- Formal statement review:
  - Source object class: a nondegenerate Euclidean-plane triangle and an interior point.
  - Lean object class: points `A B C P : EuclideanSpace ℝ (Fin 2)`, with `¬ Collinear ℝ {A,B,C}` and a strict positive barycentric witness for `P`.
  - Source side distances `PL`, `PM`, `PN` are represented as distances from `P` to the orthogonal projections of `P` onto the affine spans of the corresponding side pairs; this is the formal perpendicular-foot bridge used by Mathlib.
  - The inequality direction and factor are preserved exactly as `dist P A + dist P B + dist P C ≥ 2 * (...)`.
- Source qualifiers:
  - Mathematical object class: Euclidean plane geometry; triangle `ABC`.
  - Quantifier order: choose `A B C P`, assume nondegenerate triangle and `P` inside, conclude the inequality.
  - Parameter domain: all four points lie in `EuclideanSpace ℝ (Fin 2)`.
  - Side conditions: `A,B,C` are not collinear; `P` has strictly positive barycentric coordinates relative to `A,B,C` summing to `1`.
  - Output codomain: proposition over real-valued metric distances.
  - Equality/image condition: perpendicular feet are represented by orthogonal projections onto the affine side lines.
  - Follow-on claims: none in the source beyond the displayed inequality.
- Lean coverage:
  - Euclidean plane covered by `EuclideanSpace ℝ (Fin 2)`.
  - Triangle covered by `¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2)))`.
  - Interior point covered by `∃ u v w : ℝ, 0 < u ∧ 0 < v ∧ 0 < w ∧ u + v + w = 1 ∧ P = u • A + v • B + w • C`.
  - Perpendicular-foot representation and distances to sides covered by the three `dist P (orthogonalProjection (affineSpan ℝ side) P)` terms; no separate foot-point variables are needed because the source only uses the segment lengths `PL`, `PM`, and `PN` in the inequality.
  - The displayed Erdős--Mordell inequality covered by the theorem conclusion.
- Scope changes:
  - No semantic weakening or strengthening is intended.
  - The source describes perpendicular segments `PL`, `PM`, `PN`; the Lean statement names no separate foot points and instead uses Mathlib orthogonal projections onto the side lines. This is a representation change, not an intended weakening.
  - The source says “point `P` inside `ABC`”; the Lean statement makes this explicit as strict positive barycentric coordinates.
  - The source's Euclidean-geometry setting is formalized in the standard Euclidean plane `EuclideanSpace ℝ (Fin 2)`, matching the plane-triangle reading of the statement.
- Source proof / prover notes:
  - No source proof is provided. A prover should use the classical Erdős--Mordell argument: express `PL`, `PM`, `PN` as distances to the corresponding side lines, use angle/triangle-distance estimates for each vertex-side pair, and sum the resulting three inequalities to obtain the factor `2`.
  - Useful Mathlib search targets include `EuclideanGeometry.orthogonalProjection_mem`, `EuclideanGeometry.dist_orthogonalProjection_eq_infDist`, affine-span membership lemmas for two-point side lines, and real linear arithmetic for the final sum.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.

## Handoff Checklist

- [x] Source document inspected with `formalization_document_inspect`.
- [x] Preflight manifest and workflow context read.
- [x] Instructions and all candidate skeletons read and compared.
- [x] Local/Mathlib search performed for projection, affine span, collinearity, and Euclidean-space declarations.
- [x] Root project module imports the generated target module through `ShadowBench.lean` and `ShadowBench/Source.lean`.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [x] Proof-ready handoff accepted for the later prove workflow by formalization PASS and 2026-06-05 audit.
