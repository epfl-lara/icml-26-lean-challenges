# Formalization Blueprint: `geometry/L3/geo_gen_L3_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: point-based Euclidean-plane formalization of Morley's trisector theorem, including helper predicates and the source theorem skeleton.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`.

No split into additional Lean files is currently planned; the source has one theorem and the supporting predicates are short.

## Import Plan

```lean
import Mathlib.Analysis.Normed.Affine.Simplex
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
```

These are the direct imports used by `ShadowBench/Source/Main.lean`, matching `docs/instructions.md`. The root project module already reaches the generated target through `ShadowBench.lean -> ShadowBench/Source.lean -> ShadowBench/Source/Main.lean`.

## Suggested Search Modules

- `Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine`: `EuclideanGeometry.angle` and notation `∠` for point angles.
- `Mathlib.Geometry.Euclidean.Angle.Oriented.Affine`: oriented-angle facts and non-collinearity/angle lemmas if the proof needs them.
- `Mathlib.Geometry.Euclidean.Triangle`: angle-sum, angle/distance comparison, and Euclidean triangle lemmas.
- `Mathlib.Analysis.Normed.Affine.Simplex`: `Affine.Simplex.Equilateral` and triangle equilateral distance characterizations.

## Local and Mathlib Search Record

- Candidate skeletons all used the required name `morleys_trisector_theorem`, the imports from `docs/instructions.md`, `EuclideanSpace ℝ (Fin 2)`, a non-collinearity predicate for triangles, and a distance-equality predicate for equilateral triangles. Skeletons were not copied verbatim because their intersection-point definitions use `sorry`, which would create construction gaps outside the theorem queue.
- `lean_search` found `EuclideanGeometry.angle` in `Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine` for point angles and `Collinear` for affine collinearity.
- `lean_search` found `Affine.Simplex.Equilateral` and `Affine.Triangle.equilateral_iff_dist_01_eq_02_and_dist_01_eq_12`; the draft keeps a direct point predicate instead of packaging `X,Y,Z` as an `Affine.Triangle` because the source statement names three points directly.

## Required Names

- `morleys_trisector_theorem`

## Companion Declarations

- `PlanePoint`: abbreviation for the Euclidean plane `EuclideanSpace ℝ (Fin 2)`.
- `IsTriangle A B C`: non-collinearity of the three plane points.
- `IsEquilateralTriangle X Y Z`: `X,Y,Z` are non-collinear and their three side lengths are equal.
- `OnInternalAngleTrisectorAdjacent P V S T`: point `P` lies on the internal angle trisector ray at vertex `V` adjacent to side/ray `VS` in angle `SVT`, encoded by angle-add containment inside the angle plus `3 * ∠ S V P = ∠ S V T`.
- `IsAdjacentTrisectorIntersection P U V W`: `P` is the common point of the adjacent internal trisectors at vertices `U` and `V` that are adjacent to side `UV` in triangle `UVW`.
- `IsFirstMorleyTriangle A B C X Y Z`: `X,Y,Z` are the three adjacent-trisector intersection points corresponding respectively to sides `AB`, `BC`, and `CA`.

## Source Inventory

- Source inventory entry: `thm:morley_trisector`
  - Source kind: theorem.
  - Source title/name: `morleys_trisector_theorem`.
  - Source locator: `docs/source.tex`, lines 17-21.
  - Planned Lean declarations: `morleys_trisector_theorem`.

## Source Statement Inventory

### thm:morley_trisector

- Source kind: theorem.
- Source title/name: `morleys_trisector_theorem`.
- Source locator: `docs/source.tex`, lines 17-21, label `thm:morley_trisector`.
- Planned Lean declarations: `morleys_trisector_theorem`.
- Skeleton candidate used: candidates 1-3 shaped the plane-point, triangle, and equilateral-distance vocabulary; none was adopted verbatim because all introduce `IntersectionOfTrisectors...` construction functions with `sorry` bodies. Candidate 4 is malformed by an extra theorem terminator and was rejected.
- Dependencies: `PlanePoint`, `IsTriangle`, `IsEquilateralTriangle`, `OnInternalAngleTrisectorAdjacent`, `IsAdjacentTrisectorIntersection`, `IsFirstMorleyTriangle`, `EuclideanGeometry.angle`, `Collinear`, `dist`.
- Source statement: In plane geometry, Morley's trisector theorem states that in any triangle, the three points of intersection of the adjacent angle trisectors form an equilateral triangle, called the first Morley triangle. Formally, let `X, Y, Z` be the intersections of the adjacent internal angle trisectors of a triangle `ABC`. Then the triangle `XYZ` is equilateral.
- Source proof text: no proof block is present in `docs/source.tex`.
- Source qualifiers:
  - Mathematical object class: plane Euclidean geometry.
  - Quantifier order: for a triangle `ABC`, with `X,Y,Z` the adjacent internal angle-trisector intersections, conclude a property of triangle `XYZ`.
  - Parameter domain: points `A B C X Y Z` in the Euclidean plane.
  - Side conditions: `ABC` is a nondegenerate triangle; `X,Y,Z` are adjacent internal angle-trisector intersections.
  - Output/codomain: proposition that `XYZ` is an equilateral triangle.
  - Equality/image condition: all three side lengths of `XYZ` are equal.
  - Follow-on claim: the triangle `XYZ` is the first Morley triangle.
- Lean coverage:
  - Plane geometry is represented by `PlanePoint = EuclideanSpace ℝ (Fin 2)`.
  - The triangle assumption is represented by `hABC : IsTriangle A B C`, i.e. non-collinearity.
  - The statement explicitly quantifies the selected points `X Y Z`; their role as adjacent internal trisector intersections is represented by `hMorley : IsFirstMorleyTriangle A B C X Y Z`.
  - Internal adjacent trisectors are encoded by angle-containment and one-third-angle equations in `OnInternalAngleTrisectorAdjacent` using `∠`.
  - Equilateral triangle is represented by `IsEquilateralTriangle X Y Z`, which includes non-collinearity of `XYZ` plus equality of the three pairwise distances.
  - The name `first Morley triangle` is represented by the predicate `IsFirstMorleyTriangle`; no separate object-valued construction is introduced.
- Scope changes:
  - Representation change: the Lean theorem takes `X,Y,Z` as explicit selected points satisfying `IsFirstMorleyTriangle`, rather than defining total construction functions for the trisector intersections. This avoids non-theorem `sorry` construction stubs.
  - Existence and uniqueness of the three intersection points are not separately formalized in this draft. If independent source review treats existence/uniqueness as part of the required statement, add a companion theorem or change `morleys_trisector_theorem` to an existential formulation before proof search.
  - The cyclic assignment is fixed as `X` on side `AB`, `Y` on side `BC`, and `Z` on side `CA`, following the skeleton convention; the LaTeX source names the three points but does not specify this ordering.
- Formal statement review: The draft is a conditional point-based formulation of the source theorem. It preserves the plane, nondegenerate input triangle, adjacent internal trisector hypotheses, and equilateral conclusion, while recording the explicit-point representation change above.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: The source supplies no proof. A classical Morley proof shows that the adjacent internal trisectors cut the angles of `ABC` into thirds; the small triangles around `XYZ` then have matching angle data leading to equal side lengths `dist X Y = dist Y Z = dist Z X` and non-collinearity of `X,Y,Z`. In Lean, start by unfolding `IsFirstMorleyTriangle`, `IsAdjacentTrisectorIntersection`, `OnInternalAngleTrisectorAdjacent`, and `IsEquilateralTriangle`; likely useful libraries are `EuclideanGeometry.angle` facts, triangle angle-sum facts, and distance/angle lemmas from `Mathlib.Geometry.Euclidean.Triangle`. The proof is intentionally left as `by sorry` for the prover queue after statement/source review.

## Formalization Rules

```text
open Module

Formalize in Lean the Theorem (morleys_trisector_theorem) from Text.
The theorem must be named `morleys_trisector_theorem`.
Matched text: \begin{theorem}[morleys_trisector_theorem]\label{thm:morley_trisector} ... Morley's trisector theorem ...
```

## Handoff Checklist

- [x] Source document inspected with theorem label `thm:morley_trisector`.
- [x] Companion instructions and candidate skeletons read and compared against the source.
- [x] Local project and Mathlib search performed before drafting declarations.
- [x] Blueprint source inventory entry replaces the preflight placeholder.
- [x] Direct Lean imports recorded under `## Import Plan`.
- [x] Root project module imports the generated target module path.
- [x] Lean doc comment above the source theorem contains compact source proof/prover notes.
- [ ] Statement/source verification approved by an independent review pass.
- [x] Proof-ready handoff accepted for the later prove workflow by formalization PASS and 2026-06-05 audit.
