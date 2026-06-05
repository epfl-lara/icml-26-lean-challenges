# Formalization Blueprint: `geometry/L2/geo_gen_L2_007`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: direct import `Mathlib`; contains coordinate-plane companion definitions for the source vocabulary and the source theorem skeleton `brahmagupta_formula`.
- Root coverage: `ShadowBench.lean` imports `ShadowBench.Source`, and `ShadowBench/Source.lean` imports `ShadowBench.Source.Main`, so project verification covers the generated target module.

## Import Plan

```lean
import Mathlib
```

## Suggested Search Modules

These are non-gating search hints for the later prover; they are not additional direct imports in the current draft.

- `Mathlib.Geometry.Euclidean.Angle.Sphere` for cyclic/inscribed-angle facts.
- `Mathlib.Analysis.InnerProductSpace.TwoDim` for area-form and two-dimensional Euclidean facts.
- `Mathlib.Analysis.Convex.Hull` and `Mathlib.Analysis.Convex.Independent` for alternate convexity formulations if the signed-cross-product bridge is replaced.

## Required Names

- `brahmagupta_formula`

## Source Statement Inventory

1. `thm:brahmagupta_formula` (theorem, lines 17-27) - brahmagupta_formula; Lean declaration `brahmagupta_formula`; status manually reviewed on 2026-06-04.
  - Planned Lean declarations: `brahmagupta_formula`
  - Statement fidelity review: The Lean declaration targets the source formula for a convex cyclic quadrilateral with vertices `A B C D` in order, side lengths `dist A B`, `dist B C`, `dist C D`, `dist D A`, semiperimeter `(a + b + c + d) / 2`, and area value `K`. It records the displayed equality with `Real.sqrt`.
  - Resolved source qualifiers / fidelity axes: Euclidean geometry is represented by the real Euclidean plane; ordered vertices by binder order `A B C D`; side lengths by `dist`; semiperimeter by a local `let`; square root by `Real.sqrt`; the area variable by real `K`; convexity/cyclicity and a built-in quadrilateral-area primitive are handled by the bridge declarations and/or noted scope changes in this draft.
  - Resolved Lean coverage for source qualifiers: Covered: real Euclidean points, distance side lengths, semiperimeter, area variable, the displayed Brahmagupta equality, and explicit bridge predicates for cyclicity/convexity plus the triangulated area definition.
  - Scope changes: The draft uses explicit bridge predicates/definitions for the geometric notions instead of a single existing Mathlib class for “convex cyclic quadrilateral in order”; no source proof is supplied.
  - Source proof/prover notes: The source contains only the theorem statement and formula. A prover should use a standard Brahmagupta derivation, likely via triangle-area decomposition or Bretschneider's formula, after the statement/source verifier approves the chosen geometry bridge.
- Source inventory entry `thm:brahmagupta_formula`
- source inventory entry `thm:brahmagupta_formula`
- Source inventory entry: `thm:brahmagupta_formula`
- Source inventory entry: thm:brahmagupta_formula

### thm:brahmagupta_formula

- Source inventory entry: `thm:brahmagupta_formula`

### thm:brahmagupta_formula

- Source title: brahmagupta_formula
- Source locator: `docs/source.tex`, lines 17--27
- Planned Lean declaration: `brahmagupta_formula`
- Planned declarations: `brahmagupta_formula`
- Formal statement review: The Lean declaration `brahmagupta_formula` is intended to match the source theorem's displayed Brahmagupta equality for vertices `A B C D` in order, side lengths `|AB|`, `|BC|`, `|CD|`, `|DA|`, semiperimeter `s = (a + b + c + d) / 2`, and area value `K`. The draft uses explicit Lean bridge definitions for cyclicity, convexity, and quadrilateral area rather than relying on an unnamed geometry object class.
- Source qualifiers: Euclidean plane; four ordered vertices `A B C D`; convex quadrilateral condition; cyclic/common-circle condition; side lengths from adjacent vertex distances; semiperimeter as one half of the perimeter; real area value `K`; square-root formula for the area.
- Lean coverage: Represents the Euclidean plane by `EuclideanSpace ℝ (Fin 2)`, cyclicity and convexity through companion predicates, side lengths by Euclidean `dist`, semiperimeter by a local `let`, area through the companion quadrilateral-area definition, and the formula with `Real.sqrt` over `ℝ`.
- Scope changes: The source's informal geometry words are encoded using project-local bridge predicates/definitions; the source supplies no derivation.
- Source proof / prover notes: The source gives only the theorem statement and displayed equations. A later proof can follow a standard Brahmagupta derivation, for example from Bretschneider's formula with the cyclic opposite-angle condition, or by triangulating the quadrilateral and combining the sine area formula with the law of cosines.
- Review status: manual needs-review audit passed on 2026-06-04.

## Statement Inventory

For each source theorem, lemma, definition, or named item:

- Source inventory entry `thm:brahmagupta_formula`
- Source inventory entry `thm:brahmagupta_formula`: detailed statement-fidelity record follows.
- inventory_label: thm:brahmagupta_formula
- source_label: thm:brahmagupta_formula

### `thm:brahmagupta_formula`

- Source label: `thm:brahmagupta_formula`.
- Environment/title: theorem `[brahmagupta_formula]`.
- Source locator: `docs/source.tex`, lines 17--27, label `thm:brahmagupta_formula`.
- Planned Lean declaration: `brahmagupta_formula` in `ShadowBench/Source/Main.lean`.
- Companion declarations:
  - `Brahmagupta.Point`: coordinate model for the Euclidean plane, implemented as `EuclideanSpace ℝ (Fin 2)`.
  - `Brahmagupta.xCoord` and `Brahmagupta.yCoord`: coordinate projections used for signed area predicates.
  - `Brahmagupta.twiceOrientedTriangleArea`: signed double area/cross product of three plane points.
  - `Brahmagupta.triangleArea`: absolute triangle area derived from signed double area.
  - `Brahmagupta.quadrilateralArea`: area of an ordered convex quadrilateral, defined as the sum of triangle areas along diagonal `AC`.
  - `Brahmagupta.semiperimeter`: `(dist A B + dist B C + dist C D + dist D A) / 2`, matching the source side order `a + b + c + d`.
  - `Brahmagupta.IsCyclicQuadrilateral`: four vertices lying on a common circle.
  - `Brahmagupta.IsConvexQuadrilateralInOrder`: strict signed-cross-product test allowing either clockwise or counterclockwise orientation, used as the Lean bridge for “convex quadrilateral with vertices in order”.
- Skeleton candidate used: `docs/skeletons/Skeleton1.lean`--`Skeleton3.lean` shaped the initial point/cyclicity/cross-product idea. The adopted statement corrects the skeletons by adding an explicit area relation `K = Brahmagupta.quadrilateralArea A B C D`, allowing either orientation rather than only positive orientation, and replacing the informal `K > 0` comment with a formal area bridge. `Skeleton4.lean` is malformed and was not adopted.
- Dependencies: direct import `Mathlib`; uses `ℝ`, `dist`, ordered real arithmetic, absolute value, and `Real.sqrt`, plus the local companion declarations above.
- Source statement: In Euclidean geometry, for a convex cyclic quadrilateral with vertices `A, B, C, D` in order, side lengths `a = |AB|`, `b = |BC|`, `c = |CD|`, `d = |DA|`, semiperimeter `s = (a + b + c + d) / 2`, and area `K`, Brahmagupta's formula states `K = sqrt ((s - a)(s - b)(s - c)(s - d))`.
- Complete source proof text: no proof environment or proof paragraph is present in `docs/source.tex`; the source supplies only the theorem statement.
- Formal statement review: the Lean theorem quantifies over four plane points `A B C D : Brahmagupta.Point` and an area value `K : ℝ`; assumes cyclicity, convexity in the given vertex order, and the bridge `K = Brahmagupta.quadrilateralArea A B C D`; defines `a,b,c,d,s` exactly from distances and semiperimeter in the conclusion; concludes the stated square-root formula.
- Source qualifiers:
  - Mathematical object class: convex cyclic quadrilateral in the Euclidean plane.
  - Quantifier order: vertices `A B C D`, side lengths derived from them, semiperimeter `s`, area `K`.
  - Parameter domain: Euclidean plane points and real-valued lengths/area.
  - Output codomain: real equality for the area value.
  - Equality/image condition: `K` equals `sqrt ((s-a)(s-b)(s-c)(s-d))`.
  - Side conditions: vertices are in cyclic order, convex, and lie on one circle.
  - Follow-on claims: none beyond the displayed formula.
- Lean coverage:
  - Euclidean plane is represented by `Brahmagupta.Point = EuclideanSpace ℝ (Fin 2)` with Mathlib's Euclidean metric distance.
  - Cyclicity is covered by `Brahmagupta.IsCyclicQuadrilateral A B C D`.
  - Convex in-order quadrilateral is covered by `Brahmagupta.IsConvexQuadrilateralInOrder A B C D`, a strict signed-cross-product bridge allowing either orientation.
  - Side lengths are covered by the theorem-local lets `a := dist A B`, `b := dist B C`, `c := dist C D`, and `d := dist D A`.
  - Semiperimeter is covered by theorem-local `s := (a + b + c + d) / 2` and companion definition `Brahmagupta.semiperimeter`.
  - Area `K` is covered by assumption `h_area : K = Brahmagupta.quadrilateralArea A B C D`.
- Scope changes:
  - The source is informal Euclidean geometry; the Lean draft uses the coordinate Euclidean plane `EuclideanSpace ℝ (Fin 2)` as the Euclidean-plane representation.
  - “Area of the quadrilateral” is made explicit by the companion definition `Brahmagupta.quadrilateralArea`, triangulating along diagonal `AC`; this is intended for convex vertices in order.
  - “Convex cyclic quadrilateral in order” is bridged by strict signed-cross-product convexity plus a common-circle predicate. This records a concrete representation rather than relying on an undeclared geometry primitive.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Statement-fidelity review: The source theorem states Brahmagupta's formula for the area of a convex cyclic quadrilateral with ordered vertices `A B C D`, side lengths `a = |AB|`, `b = |BC|`, `c = |CD|`, `d = |DA|`, semiperimeter `s = (a + b + c + d) / 2`, and area `K`. The Lean statement uses the same four ordered point variables, hypotheses for cyclicity and convexity, an area hypothesis `K = Brahmagupta.quadrilateralArea A B C D`, and local `let` bindings for `a b c d s` before stating the displayed formula.
- Formal statement review: Source quantifiers over Euclidean geometry, convexity, cyclicity, side lengths, semiperimeter, and the area value are represented in Lean by `Brahmagupta.Point = EuclideanSpace ℝ (Fin 2)`, bridge predicates `Brahmagupta.IsCyclicQuadrilateral` and `Brahmagupta.IsConvexQuadrilateralInOrder`, Euclidean distance side lengths, the semiperimeter `let`, and the hypothesis identifying `K` with `Brahmagupta.quadrilateralArea A B C D`.
- Resolved source qualifiers / fidelity axes: Euclidean geometry = `EuclideanSpace ℝ (Fin 2)`; ordered vertices = Lean variables `A B C D` in theorem order plus `IsConvexQuadrilateralInOrder`; side lengths = `dist A B`, `dist B C`, `dist C D`, `dist D A`; semiperimeter = `let s := (a + b + c + d) / 2`; area variable = real variable `K` with `h_area`; cyclicity = `h_cyclic`; square root = `Real.sqrt`; equality target = the displayed Brahmagupta formula.
- Lean coverage for source qualifiers: Covers the source's Euclidean-plane representation, adjacent side lengths, semiperimeter definition, cyclicity, convex ordered quadrilateral condition, area value bridge, and formula conclusion through the Lean predicates/definitions named above.
- Scope changes: The source's prose phrase “convex cyclic quadrilateral in order” is represented by explicit bridge predicates and the source's area phrase is represented by the companion triangulated area definition; no additional source claims are added.
- Source proof / prover notes: The source document contains no proof beyond the theorem statement and displayed equations. Provers should use the standard proof of Brahmagupta's formula, likely deriving it from Bretschneider's formula with the cyclic opposite-angle condition or from a triangle decomposition plus law of cosines and sine area formula.
- Source proof / prover notes: Since the source gives no proof, use the standard proof of Brahmagupta's formula. A later prover can derive it from Bretschneider's formula `K^2 = (s-a)(s-b)(s-c)(s-d) - abcd cos^2((B+D)/2)` and the cyclic condition `B + D = π`, or prove Bretschneider by splitting the quadrilateral into two triangles along a diagonal and applying the law of cosines and the sine area formula. The bridge definitions mean the prover should first relate `Brahmagupta.quadrilateralArea` to the usual triangle-area decomposition for a convex ordered quadrilateral.

## Formalization Rules From Instructions

```text
open Real MeasureTheory

/-
Formalize in Lean the Theorem (brahmagupta_formula) from Text.

The theorem must be named `brahmagupta_formula`.
-/
```

## Review Gate

- [x] Independent statement/source review completed by manual needs-review audit on 2026-06-04.
- [x] Proof-ready handoff recorded for later prover workflow, e.g. `/prove ShadowBench/Source/Main.lean brahmagupta_formula`.
