# Formalization Blueprint: `geometry/L2/geo_gen_L2_006`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Source Document Inventory

- Source kind: LaTeX article, extraction status `ok`.
- Detected theorem-like environments: two theorems, no separate proof environments.
- Labels:
  - `thm:napoleon_inner`, title `napoleons_theorem_inner`, source lines 17--22.
  - `thm:napoleon_outer`, title `napoleons_theorem_outer`, source lines 24--29.
- No sections, references, citations, bibliography files, PDFs, figures, or other support files were listed in the preflight manifest.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: all generated definitions and the two source theorem skeletons.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so the generated target is covered by the project root module.

## Import Plan

```lean
import Mathlib.Analysis.Normed.Affine.Simplex
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Mathlib.Geometry.Euclidean.Circumcenter
```

## Suggested Search Modules

These are search hints for the prover and are not direct imports unless a later Lean check requires them.

- `Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional` for `Collinear` facts.
- `Mathlib.Analysis.InnerProductSpace.PiL2` for `EuclideanSpace` coordinate facts.
- `Mathlib.LinearAlgebra.AffineSpace.Centroid` and `Mathlib.LinearAlgebra.AffineSpace.Simplex.Centroid` for centroid API alternatives.
- `Mathlib.Analysis.Normed.Affine.Simplex` for Mathlib equilateral simplex/triangle predicates.
- `Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation` for a rotation-based proof of the sixty-degree construction.

## Required Names

- `napoleons_theorem_inner`
- `napoleons_theorem_outer`

## Supporting Lean Declarations

- `Plane`: abbreviation for `EuclideanSpace ℝ (Fin 2)`, the two-dimensional Euclidean plane.
- `twiceSignedArea`: coordinate determinant giving twice the signed area/orientation of an ordered triangle.
- `SameSide`: open same-side predicate for two points relative to a directed line, encoded by a positive product of signed areas.
- `OppositeSide`: open opposite-side predicate for two points relative to a directed line, encoded by a negative product of signed areas.
- `EquilateralTriangle`: metric predicate `dist P Q = dist Q R ∧ dist Q R = dist R P`.
- `TriangleCentroid`: centroid of three points, encoded in vector coordinates as `(1 / 3 : ℝ) • (P + Q + R)`.
- `InternalNapoleonConfiguration`: three equilateral side triangles plus same-side conditions matching the source's internal construction.
- `ExternalNapoleonConfiguration`: three equilateral side triangles plus opposite-side conditions matching the source's external construction.

## Candidate Skeleton Review

- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` are identical for the relevant declarations. They suggested the `Plane` abbreviation, the required theorem names, the non-collinearity assumption, a metric equilateral condition, and vector-average centroids. Those portions were adopted after comparison with the source.
- The same skeletons did not encode the source qualifiers "internally" and "externally"; they quantify over equilateral third vertices without side/orientation conditions. That statement would not distinguish the two source theorems and is not faithful enough, so the final Lean draft adds internal/external configuration predicates.
- `docs/skeletons/Skeleton4.lean` has the same fidelity issue and also contains a malformed trailing proof marker; it was not adopted.

## Source Statement Inventory

- `thm:napoleon_inner`: theorem `[napoleons_theorem_inner]` in `docs/source.tex`, lines 17--22, Lean declaration `napoleons_theorem_inner` in `ShadowBench/Source/Main.lean`.
- `thm:napoleon_outer`: theorem `[napoleons_theorem_outer]` in `docs/source.tex`, lines 24--29, Lean declaration `napoleons_theorem_outer` in `ShadowBench/Source/Main.lean`.

### thm:napoleon_inner

- Source label: `thm:napoleon_inner`.

- Source title/name: `napoleons_theorem_inner`.
- Planned Lean declaration: `napoleons_theorem_inner` in `ShadowBench/Source/Main.lean`.
- Source locator: `docs/source.tex`, theorem environment lines 17--22, label `thm:napoleon_inner`.
- Source statement: Let `A,B,C` be non-collinear points in the plane. On each side of `△ ABC`, construct an equilateral triangle internally (all three on the same "inner" side). Let `X,Y,Z` be the centroids of the equilateral triangles on `AB,BC,CA`, respectively. Then `△ XYZ` is equilateral.
- Complete source proof text: none supplied in `docs/source.tex`.
- Skeleton candidate used: `Skeleton1`/`Skeleton2`/`Skeleton3` only for the plane, non-collinearity, metric equilateral, and vector centroid shape; internal side conditions were added for source fidelity.
- Dependencies: `Plane`, `EquilateralTriangle`, `TriangleCentroid`, `twiceSignedArea`, `SameSide`, `InternalNapoleonConfiguration`, Mathlib `Collinear`, `dist`, and `EuclideanSpace` operations.
- Formal statement review: The Lean theorem universally quantifies over `A B C : Plane`, assumes `¬ Collinear ℝ ({A, B, C} : Set Plane)`, then universally quantifies over third vertices `D E F : Plane` satisfying `InternalNapoleonConfiguration A B C D E F`. The conclusion states that the centroids of `ABD`, `BCE`, and `CAF` form an `EquilateralTriangle`.
- Source qualifiers:
  - Mathematical object class: points in the Euclidean plane.
  - Quantifier order: choose non-collinear `A B C`; construct one third vertex on each side; define three centroids; conclude equilateral output triangle.
  - Parameter domain: `A B C D E F : Plane`.
  - Side conditions: `A,B,C` non-collinear; `ABD`, `BCE`, `CAF` equilateral; each constructed third vertex lies on the internal side of the corresponding side of `ABC`.
  - Equality/image condition: centroids are those of the three side triangles, and distances among the three centroids are equal.
  - Output codomain: proposition that the centroid triangle is equilateral.
  - Follow-on claims: none beyond equilateralness of `XYZ`.
- Lean coverage:
  - Plane points are covered by `Plane := EuclideanSpace ℝ (Fin 2)`.
  - Non-collinearity is covered by `h_noncol : ¬ Collinear ℝ ({A, B, C} : Set Plane)`.
  - Equilateral side triangles are covered by the three `EquilateralTriangle` conjuncts in `InternalNapoleonConfiguration`.
  - The internal side qualifier is covered by `SameSide A B D C`, `SameSide B C E A`, and `SameSide C A F B`.
  - Centroids are covered by `TriangleCentroid A B D`, `TriangleCentroid B C E`, and `TriangleCentroid C A F`.
  - The final equilateral triangle is covered by the conclusion `EquilateralTriangle ...`.
- Scope changes: The informal construction is represented as a universal theorem over third vertices `D E F` satisfying a precise configuration predicate. The phrase "same inner side" is formalized by open same-side signed-area predicates relative to the opposite original vertex. This is an explicit representation bridge, not an intended weakening of the source claim.
- Source proof / prover notes: The source gives no proof. A prover should use the standard coordinate or complex-plane proof of Napoleon's theorem. With a consistent internal orientation, express each third vertex as a sixty-degree rotation of the corresponding side vector, expand the centroid differences, and use that the rotation is an isometry to show the three centroid distances are equal. The `twiceSignedArea` side predicates are proof obligations tying the chosen rotation sign to the internal construction.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.

### thm:napoleon_outer

- Source label: `thm:napoleon_outer`.
- Source title/name: `napoleons_theorem_outer`.
- Planned Lean declaration: `napoleons_theorem_outer` in `ShadowBench/Source/Main.lean`.
- Source locator: `docs/source.tex`, theorem environment lines 24--29, label `thm:napoleon_outer`.
- Source statement: Let `A,B,C` be non-collinear points in the plane. On each side of `△ ABC`, construct an equilateral triangle externally (all three on the same "outer" side). Let `X,Y,Z` be the centroids of the equilateral triangles on `AB,BC,CA`, respectively. Then `△ XYZ` is equilateral.
- Complete source proof text: none supplied in `docs/source.tex`.
- Skeleton candidate used: `Skeleton1`/`Skeleton2`/`Skeleton3` only for the plane, non-collinearity, metric equilateral, and vector centroid shape; external side conditions were added for source fidelity.
- Dependencies: `Plane`, `EquilateralTriangle`, `TriangleCentroid`, `twiceSignedArea`, `OppositeSide`, `ExternalNapoleonConfiguration`, Mathlib `Collinear`, `dist`, and `EuclideanSpace` operations.
- Formal statement review: The Lean theorem universally quantifies over `A B C : Plane`, assumes `¬ Collinear ℝ ({A, B, C} : Set Plane)`, then universally quantifies over third vertices `D E F : Plane` satisfying `ExternalNapoleonConfiguration A B C D E F`. The conclusion states that the centroids of `ABD`, `BCE`, and `CAF` form an `EquilateralTriangle`.
- Source qualifiers:
  - Mathematical object class: points in the Euclidean plane.
  - Quantifier order: choose non-collinear `A B C`; construct one third vertex on each side; define three centroids; conclude equilateral output triangle.
  - Parameter domain: `A B C D E F : Plane`.
  - Side conditions: `A,B,C` non-collinear; `ABD`, `BCE`, `CAF` equilateral; each constructed third vertex lies on the external side of the corresponding side of `ABC`.
  - Equality/image condition: centroids are those of the three side triangles, and distances among the three centroids are equal.
  - Output codomain: proposition that the centroid triangle is equilateral.
  - Follow-on claims: none beyond equilateralness of `XYZ`.
- Lean coverage:
  - Plane points are covered by `Plane := EuclideanSpace ℝ (Fin 2)`.
  - Non-collinearity is covered by `h_noncol : ¬ Collinear ℝ ({A, B, C} : Set Plane)`.
  - Equilateral side triangles are covered by the three `EquilateralTriangle` conjuncts in `ExternalNapoleonConfiguration`.
  - The external side qualifier is covered by `OppositeSide A B D C`, `OppositeSide B C E A`, and `OppositeSide C A F B`.
  - Centroids are covered by `TriangleCentroid A B D`, `TriangleCentroid B C E`, and `TriangleCentroid C A F`.
  - The final equilateral triangle is covered by the conclusion `EquilateralTriangle ...`.
- Scope changes: The informal construction is represented as a universal theorem over third vertices `D E F` satisfying a precise configuration predicate. The phrase "same outer side" is formalized by open opposite-side signed-area predicates relative to the opposite original vertex. This is an explicit representation bridge, not an intended weakening of the source claim.
- Source proof / prover notes: The source gives no proof. A prover should use the standard coordinate or complex-plane proof of Napoleon's theorem with the opposite common orientation from the internal theorem. Express each third vertex by the other sixty-degree rotation sign, expand centroid differences, and use rotation isometry or direct coordinate algebra to prove equal distances.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.

## Handoff Checklist

- [x] Source document inspected with `formalization_document_inspect`.
- [x] Preflight manifest and workflow context read.
- [x] Instructions and all candidate skeletons read and compared.
- [x] Local/Mathlib search performed for collinearity, Euclidean plane, centroids, and equilateral-triangle declarations.
- [x] Root project module imports the generated target module through `ShadowBench.lean` and `ShadowBench/Source.lean`.
- [x] Project-level Lean verification passed with the two intended theorem proof skeletons.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [x] Proof-ready handoff accepted for the later prove workflow by formalization PASS and 2026-06-05 audit.
