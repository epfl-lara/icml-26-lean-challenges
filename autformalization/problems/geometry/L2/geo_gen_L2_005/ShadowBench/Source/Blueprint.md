# Formalization Blueprint: `geometry/L2/geo_gen_L2_005`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: one-file draft containing the plane/circle vocabulary, the required definition `EuclideanGeometry.external_homothetic_center`, and the required theorem skeleton `EuclideanGeometry.monges_circle_theorem`.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`.

The one-file layout is intentional for this small source document. No split into auxiliary files is currently needed.

## Import Plan

```lean
import Mathlib
```

## Suggested Search Modules

These are proof-search hints only, not direct imports required by the current draft:

- `Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional` for `Collinear` and affine-span collinearity lemmas.
- `Mathlib.LinearAlgebra.AffineSpace.AffineMap` for `AffineMap.lineMap` if the prover uses affine-line parametrizations.
- `Mathlib.Geometry.Euclidean.Sphere.Basic` and `Mathlib.Geometry.Euclidean.Sphere.Tangent` if the tangent-line bridge is later expanded with Mathlib sphere tangency APIs.

## Required Names

- `EuclideanGeometry.external_homothetic_center`
- `EuclideanGeometry.monges_circle_theorem`

## Candidate Skeleton Review

- `Skeleton1.lean` and `Skeleton3.lean` introduce custom points, lines, tangency, and external tangency but leave definition bodies as `sorry`; this is not acceptable for handoff because construction stubs are not theorem queue items.
- `Skeleton2.lean` additionally duplicates the required names after opening `namespace EuclideanGeometry`, producing malformed/nonfaithful declarations such as a `Prop`-valued `external_homothetic_center`.
- `Skeleton4.lean` best preserves the required declaration names and theorem shape, but still uses `sorry` in definitions and encodes lines by coefficients rather than using Mathlib affine geometry. The final draft keeps the same high-level theorem shape while replacing construction stubs by implemented algebraic definitions over the Euclidean affine plane `EuclideanSpace ℝ (Fin 2)`.

## Source Inventory Entries

- Source inventory entry `thm:monge`: theorem `monges_circle_theorem`, source `docs/source.tex:17-23`, Lean declaration `EuclideanGeometry.monges_circle_theorem` in `ShadowBench/Source/Main.lean`.
- Source inventory entry `instruction:external_homothetic_center`: source-backed definition required by `docs/instructions.md:39-44`, Lean declaration `EuclideanGeometry.external_homothetic_center` in `ShadowBench/Source/Main.lean`.

## Source Statement Inventory

### instruction:external_homothetic_center

Definition `EuclideanGeometry.external_homothetic_center`

- Source inventory entry: `instruction:external_homothetic_center`
- Source kind: definition required by companion instructions.
- Planned Lean declarations: `EuclideanGeometry.external_homothetic_center`
- Source locator: `docs/instructions.md` lines 39-44; related explanatory text in `docs/source.tex` theorem `thm:monge`, lines 21-23.
- Source text: "For any two circles in a plane, an external tangent is a line that is tangent to both circles but does not pass between them. Each such pair has a unique intersection point in the extended Euclidean plane." The theorem text then restricts to pairwise distinct radii so the relevant intersection points are finite affine points.
- Skeleton candidate used: shaped by `docs/skeletons/Skeleton4.lean` for the required name and two-circle argument order, but the implementation is algebraic rather than a `sorry` construction.
- Dependencies: `EuclideanGeometry.Point`, `EuclideanGeometry.Circle`, real scalar multiplication on `EuclideanSpace ℝ (Fin 2)`.
- Formal statement review: the Lean definition sends two formal circles to the affine point
  `(r₁ - r₂)⁻¹ • (r₁ • center₂ - r₂ • center₁)`, the usual external homothety center formula. This is the finite affine representative of the external tangent intersection when `r₁ ≠ r₂`. It is a representation definition, not a separate construction of the two tangent lines.
- Source qualifiers:
  - Mathematical object class: an ordered pair of circles in a real Euclidean affine plane.
  - Quantifier order: first circle `c₁`, then second circle `c₂`.
  - Parameter domain: circle centers are points of `EuclideanSpace ℝ (Fin 2)`; radii are nonnegative real numbers stored in `Circle`.
  - Output codomain: finite affine point of the same plane.
  - Equality/image condition: the returned point is definitionally the formula-based finite representative of the source's external-tangent intersection point.
  - Side conditions: the theorem supplies pairwise distinct radii; the definition is total in Lean and returns a value even in the excluded equal-radius case.
  - Follow-on claims: the instructions/source text mention external tangent lines, two such lines, and a unique extended-plane intersection point; this draft uses the standard finite affine formula as that point in the distinct-radius case and does not prove the line-existence/uniqueness facts.
  - Representation bridge: the external tangent intersection is represented by the external homothety-center coordinate formula.
- Lean coverage: partial relative to the full synthetic tangent-line/extended-plane text, and exact for the finite affine representative used by Monge's theorem. It does not separately construct the two external tangent lines or prove their intersection property.
- Scope changes: the extended Euclidean plane and points at infinity are omitted because the source explicitly requests the pairwise-distinct-radius affine-plane case. Explicit tangent-line existence/uniqueness is recorded as an intentional representation omission rather than a construction stub.
- Complete source proof text: no proof is present in `docs/source.tex` or `docs/instructions.md` for this definition/representation choice.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: no source proof is provided. If a later proof needs the bridge, show that for distinct radii the displayed affine formula is the fixed point of the homothety taking one circle to the other, hence it is the common intersection of the external tangent lines.

### thm:monge

Theorem `EuclideanGeometry.monges_circle_theorem`

- Source inventory entry: `thm:monge`
- Source label: `thm:monge`
- Source block id: `thm:monge`
- Source kind: theorem.
- Planned Lean declarations: `EuclideanGeometry.monges_circle_theorem`
- Source locator: `docs/source.tex`, theorem environment `[monges_circle_theorem]`, label `thm:monge`, lines 17-23.
- Complete source statement: "Monge's theorem states that for any three circles in a plane, none of which is completely inside one of the others, the intersection points of each of the three pairs of external tangent lines are collinear. In this formalization, we consider the affine-plane case where the three radii are pairwise distinct, so that these intersection points are finite points rather than points at infinity. Degenerate circles of radius zero are allowed, provided the radii remain pairwise distinct. For any two circles in a plane, an external tangent is a line that is tangent to both circles but does not pass between them. There are two such external tangent lines for any two circles satisfying the above non-containment assumptions. Monge's theorem states that the three such points given by the three pairs of circles lie on a straight line."
- Skeleton candidate used: shaped by `docs/skeletons/Skeleton4.lean` for argument order and required declaration name; modified to use `EuclideanSpace ℝ (Fin 2)`, a nonnegative-radius `Circle`, Mathlib `Collinear`, and implemented definitions.
- Dependencies: `EuclideanGeometry.Circle`, `EuclideanGeometry.Circle.NotCompletelyInside`, `EuclideanGeometry.CirclesPairwiseNotCompletelyInside`, `EuclideanGeometry.RadiiPairwiseDistinct`, `EuclideanGeometry.external_homothetic_center`, Mathlib `Collinear`.
- Formal statement review: the Lean theorem quantifies over three formal circles `c₁ c₂ c₃`; assumes no ordered containment among the three circles; assumes the three radii are pairwise distinct; and concludes that the three affine external homothetic centers for pairs `(c₁,c₂)`, `(c₂,c₃)`, `(c₁,c₃)` form a collinear set.
- Source qualifiers:
  - Mathematical object class: three real Euclidean affine-plane circles.
  - Quantifier order: circles first, then non-containment assumption, then pairwise-distinct-radius assumption.
  - Parameter domain: centers in `EuclideanSpace ℝ (Fin 2)`, nonnegative real radii; radius `0` is allowed by `Circle.radius_nonneg`.
  - Output/equality condition: collinearity of exactly the three pairwise external-center points.
  - Side conditions: no circle is completely inside another, and radii are pairwise distinct.
  - Follow-on claims: external tangents exist in the intended geometry and meet at the `external_homothetic_center`; the current theorem uses the algebraic center as the representation of those intersections.
- Lean coverage: partial relative to the full synthetic tangent-line statement, and exact for the affine, finite-point Monge statement for the algebraic external homothety centers under the source side conditions.
- Scope changes: the Lean theorem does not quantify over arbitrary coordinate-free planes, extended Euclidean points at infinity, or explicit external tangent lines. These are intentionally represented by the standard plane `EuclideanSpace ℝ (Fin 2)` and the formula-based `external_homothetic_center`; tangent-line existence, the two-tangent assertion, and the proof that those tangents meet at the formula point are recorded representation omissions, not hidden construction stubs.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: no proof is present in `docs/source.tex`.
- Source proof / prover notes: no source proof is supplied. Prove the collinearity algebraically. Write `Oᵢ` for centers and `rᵢ` for radii. The three points are
  `X₁₂ = (r₁ O₂ - r₂ O₁)/(r₁-r₂)`, `X₂₃ = (r₂ O₃ - r₃ O₂)/(r₂-r₃)`, and `X₁₃ = (r₁ O₃ - r₃ O₁)/(r₁-r₃)`. A coordinate determinant for `(X₁₂, X₂₃, X₁₃)` vanishes, or equivalently each lies on the Monge axis obtained from the affine relation among weighted center coordinates. The non-containment hypothesis is source-fidelity data for the external tangents; the algebraic collinearity proof itself should only need distinct radii.

## Proof-Handoff Notes

- The only theorem/lemma proof obligation intentionally left for a later `/prove` workflow is `EuclideanGeometry.monges_circle_theorem`.
- There are no `def`, `structure`, `class`, or `instance` construction stubs in the planned Lean draft.
- Do not start proof search until an independent statement/source review checks the blueprint, doc-comment proof notes, and Lean theorem statement.

Suggested proof command after review:

```text
/prove ShadowBench/Source/Main.lean EuclideanGeometry.monges_circle_theorem
```
