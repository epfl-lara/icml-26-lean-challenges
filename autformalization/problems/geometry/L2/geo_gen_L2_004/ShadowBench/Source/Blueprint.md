# Formalization Blueprint: `geometry/L2/geo_gen_L2_004`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Generated Lean module: `ShadowBench/Source/Main.lean` (single self-contained file).
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.
- 2026-06-05 CONSOLIDATION: all declarations were merged into a single `ShadowBench/Source/Main.lean` and the previous split files (`Basic.lean`, `Constructions.lean`, `Theorems.lean`) were removed. Rationale: the Codabench submission exports only `Main.lean` as `formal_proof`, so every required declaration (`EuclideanGeometry.external_tangent_length`, `EuclideanGeometry.circlePoint`, `EuclideanGeometry.caseys_theorem`) plus all supporting bridge defs (`sqDist`, `pointDistance`, `ptolemyEquality`, `orientation`, `strictlyCyclicallyOrdered`, `radialContactPoint`, `caseyInOrder`, `liesInsideAndTangentTo`, `nonintersectingCircles`, `fourCirclesNonintersecting`) and the degenerate-Ptolemy bridge theorem must live in `Main.lean`. The three Mathlib `import` lines from `Basic.lean` are preserved at the top of `Main.lean`. Verified: `lake env lean Main.lean` exit 0 (sorry-only), `lake build` succeeds, and all three required names resolve via `import ShadowBench; #check`.

## Source Artifacts Inspected

- `docs/source.tex` inspected directly and with `formalization_document_inspect`.
- Preflight context read: `.epflemma/workflow-state/formalization/docs-source/context.md`.
- Preflight manifest read: `.epflemma/workflow-state/formalization/docs-source/manifest.json`.
- Companion instructions read: `docs/instructions.md`.
- Candidate skeleton guide read: `docs/skeletons/README.md`.
- Candidate skeletons read: `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, `Skeleton3.lean`, `Skeleton4.lean`.
- Manifest and project search report no project-local PDFs, bibliography files, figures, citations, or references requiring `read_pdf` extraction.
- Local/Mathlib search checked relevant names and proof hints: Mathlib has `EuclideanGeometry.mul_dist_add_mul_dist_eq_mul_dist_of_cospherical` in `Mathlib.Geometry.Euclidean.Sphere.Ptolemy`; Mathlib sphere tangent/power APIs exist but are left as search hints rather than direct imports.

## Review Corrections Applied

- The internal tangency and nonintersection predicates were changed from strict positive inner radii to nonnegative inner radii. This keeps ordinary positive circles covered while allowing the source's explicit degenerate zero-radius point case.
- Added `EuclideanGeometry.pointDistance` and `EuclideanGeometry.ptolemyEquality` as the analytic Ptolemy-side representation.
- Added `EuclideanGeometry.caseys_theorem_degenerate_ptolemy_bridge` to cover the source follow-on claim that the zero-radius specialization is exactly Ptolemy's theorem.
- Proofs remain `by sorry`; no proof search was performed in this review pass.

## Source Inventory Entries

- Source inventory entry `thm:casey`: theorem `caseys_theorem`, source `docs/source.tex:17-23`, Lean declaration `EuclideanGeometry.caseys_theorem` in `ShadowBench/Source/Main.lean`.
- Source inventory entry `external_tangent_length`: source-backed definition of `tᵢⱼ`, source `docs/source.tex:18-21`, Lean declaration `EuclideanGeometry.external_tangent_length` in `ShadowBench/Source/Main.lean`.
- Source inventory entry `circlePoint`: source-backed circle point-set bridge, source `docs/source.tex:17-19`, Lean declaration `EuclideanGeometry.circlePoint` in `ShadowBench/Source/Main.lean`.
- Source inventory entry `thm:casey/degenerate-ptolemy-note`: source follow-on note, source `docs/source.tex:22`, Lean declarations `EuclideanGeometry.pointDistance` and `EuclideanGeometry.ptolemyEquality` in `ShadowBench/Source/Main.lean`, and `EuclideanGeometry.caseys_theorem_degenerate_ptolemy_bridge` in `ShadowBench/Source/Main.lean`.

## Source Statement Inventory

### thm:casey

- Source inventory entry: `thm:casey`
- Source label: `thm:casey`
- Source block id: `thm:casey`
- Source kind: theorem.
- Source locator: `docs/source.tex`, theorem environment `thm:casey`, lines 17-23, title `caseys_theorem`.
- Planned Lean declarations: `EuclideanGeometry.caseys_theorem`, with companion bridge `EuclideanGeometry.caseys_theorem_degenerate_ptolemy_bridge` for the Ptolemy note.
- Source statement: "Let `O` be a circle of radius `R`. Let `O₁, O₂, O₃, O₄` be (in that order) four non-intersecting circles that lie inside `O` and tangent to it. Denote by `tᵢⱼ` the length of the exterior common bitangent of the circles `Oᵢ, Oⱼ`. Then `t₁₂ * t₃₄ + t₁₄ * t₂₃ = t₁₃ * t₂₄`. Note that in the degenerate case, where all four circles reduce to points, this is exactly Ptolemy's theorem."
- Complete source proof text: no proof is included in `docs/source.tex`.
- Statement-fidelity review: the Lean theorem uses an analytic center/radius model for the same Euclidean-plane circle configuration, keeps the source quantifier order, includes positive outer radius, nonnegative inner radii, internal tangency, pairwise nonintersection, cyclic order, and states exactly the Casey bitangent-length equality. The source's Ptolemy note is covered by a companion bridge declaration.
- Formal statement review: analytic center/radius version of Casey's theorem with explicit hypotheses for outer-radius positivity, internal tangency, pairwise nonintersection, cyclic order, the exact bitangent-length equality, and the zero-radius Ptolemy follow-on bridge.
- Source qualifiers: Euclidean-plane circles; outer radius `R`; four inner circles `O₁ O₂ O₃ O₄` in cyclic order; pairwise nonintersection; inside and tangent to `O`; `tᵢⱼ` exterior common bitangent lengths; Casey equality; degeneracy note identifying the zero-radius specialization with Ptolemy.
- Lean coverage: the main equality is stated by `EuclideanGeometry.caseys_theorem`; circles are represented by center/radius data in `ℝ × ℝ` with `circlePoint` as the set bridge; the order condition is represented by strict cyclic order of radial contact points; bitangent length is represented by the standard analytic formula; zero-radius radii are allowed; the Ptolemy follow-on is covered by `pointDistance`, `ptolemyEquality`, and `caseys_theorem_degenerate_ptolemy_bridge`.
- Scope changes: analytic `ℝ × ℝ` model rather than Mathlib sphere objects; tangent-line construction replaced by the length formula; strict pairwise disk disjointness is used for “non-intersecting”; no source proof is available.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: no proof is supplied in the source. Suggested proof route is Ptolemy on the four contact points, using the scaling relation between contact-point chords and exterior tangent lengths.

## Import Plan

Direct imports used by the single generated Lean file `ShadowBench/Source/Main.lean`:

```lean
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Real.Sqrt
```

## Suggested Search Modules

These are prover search hints only, not direct imports in the planner draft:

- `Mathlib.Geometry.Euclidean.Sphere.Ptolemy` for `EuclideanGeometry.mul_dist_add_mul_dist_eq_mul_dist_of_cospherical` and the Ptolemy proof route.
- `Mathlib.Geometry.Euclidean.Sphere.Basic` for Mathlib sphere/cospherical language if a later proof chooses to bridge from the analytic plane model.
- `Mathlib.Geometry.Euclidean.Sphere.Tangent` and `Mathlib.Geometry.Euclidean.Sphere.Power` for tangent-line facts if a later proof refines the bitangent bridge.
- `Mathlib.Data.Real.Sqrt` lemmas such as `Real.sqrt_mul`, `Real.sqrt_sq_eq_abs`, and nonnegativity lemmas for exterior tangent lengths.

## Generated File Layout

Final organization decision: split into focused modules. The draft now has more than twelve generated declarations and naturally separates analytic definitions, Casey configuration predicates, and source theorem statements.

- `ShadowBench/Source/Main.lean`: the single self-contained file holding the analytic point model, circle point-set bridge, squared distance, exterior tangent length, point-distance/Ptolemy equality bridge, orientation/cyclic-order primitives, the radial contact point, Casey order predicate, internal tangency predicate, pairwise nonintersection predicates, the source theorem `EuclideanGeometry.caseys_theorem`, and the companion bridge `EuclideanGeometry.caseys_theorem_degenerate_ptolemy_bridge`, with source/prover doc comments preserved.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so the generated target module remains covered by the root project module and plain `lake build` checks the generated formalization.

## Candidate Skeleton Review

- `Skeleton1.lean` and `Skeleton2.lean` provide the expected names and a center/radius statement shape, but leave all definitions as `sorry` stubs and do not encode the source's order condition as a mathematical predicate.
- `Skeleton3.lean` uses the same shape with `by sorry` definition stubs.
- `Skeleton4.lean` is malformed because it places a comment before imports and ends with an extra `:= by sorry`.
- Final draft keeps the required names from the skeletons and instructions, replaces definition stubs with concrete analytic definitions over `ℝ × ℝ`, adds explicit predicates for internal tangency, pairwise nonintersection, and cyclic order, and adds a degenerate Ptolemy bridge for the source note.

## Declaration Map

### Analytic plane support declarations

- `EuclideanGeometry.Point`: analytic point representation, definitionally `ℝ × ℝ`.
- `EuclideanGeometry.sqDist`: squared Euclidean distance in the analytic plane.
- `EuclideanGeometry.circlePoint`: boundary set `{p | sqDist p center = radius^2}` of an analytic circle.
- `EuclideanGeometry.external_tangent_length`: standard analytic exterior common bitangent length formula `sqrt (sqDist c₁ c₂ - (r₁ - r₂)^2)`.
- `EuclideanGeometry.pointDistance`: ordinary analytic point distance `sqrt (sqDist p q)`.
- `EuclideanGeometry.ptolemyEquality`: Ptolemy equality for four points using `pointDistance`.
- `EuclideanGeometry.orientation`: signed area/orientation determinant for three analytic points.
- `EuclideanGeometry.strictlyCyclicallyOrdered`: strict clockwise-or-counterclockwise cyclic order bridge for four points.
- `EuclideanGeometry.radialContactPoint`: the point where an internally tangent inner circle touches the outer circle, expressed by radial projection from the outer center.
- `EuclideanGeometry.caseyInOrder`: source phrase “in that order”, encoded as strict cyclic order of the four radial contact points on the outer circle.
- `EuclideanGeometry.liesInsideAndTangentTo`: source phrase “lie inside `O` and tangent to it”, encoded by nonnegative inner radius, smaller-than-outer radius, and center distance squared equal to `(R - r)^2`; zero radius is allowed for the source's degenerate point case.
- `EuclideanGeometry.nonintersectingCircles`: strict pairwise disjointness of two circular disks, encoded by nonnegative radii and `(r₁ + r₂)^2 < sqDist c₁ c₂`.
- `EuclideanGeometry.fourCirclesNonintersecting`: six pairwise `nonintersectingCircles` conditions for the four inner circles.

### Named item: `EuclideanGeometry.external_tangent_length`

- Source locator: `docs/source.tex`, theorem block `thm:casey`, lines 18-21, phrase “Denote by `t_{ij}` the length of the exterior common bitangent of the circles `O_i, O_j`.”
- Lean declaration: `noncomputable def EuclideanGeometry.external_tangent_length (c₁ c₂ : Point) (r₁ r₂ : ℝ) : ℝ`.
- Dependencies: `EuclideanGeometry.Point`, `EuclideanGeometry.sqDist`, `Real.sqrt`.
- Formal statement review: returns the standard analytic length formula for the segment between tangency points of an exterior common tangent of two circles, `sqrt (sqDist c₁ c₂ - (r₁ - r₂)^2)`.
- Source qualifiers:
  - Mathematical object class: two Euclidean-plane circles, represented by center/radius pairs.
  - Quantifier order: first circle center/radius, second circle center/radius.
  - Parameter domains: centers are analytic plane points; radii are real numbers, with nonnegativity supplied by theorem hypotheses when the source theorem uses the value.
  - Output codomain: `ℝ`, representing a length.
  - Equality/image condition: defines the source notation `tᵢⱼ` used in the Casey equality.
  - Side conditions: the source uses the value under nonintersection hypotheses; the definition itself is total.
  - Follow-on claims: zero-radius values are ordinary point distances via the degenerate bridge declarations.
- Lean coverage: covers the source notation `t_{ij}` by a concrete formula. Existence and uniqueness of tangent lines are not separately constructed; the length value is taken as the standard analytic bridge. The zero-radius conversion is covered by `pointDistance`, `ptolemyEquality`, and `caseys_theorem_degenerate_ptolemy_bridge`.
- Scope changes: analytic center/radius representation over `ℝ × ℝ` rather than an abstract circle object; tangent-line construction omitted in favor of the conventional formula.
- Complete source proof text: no proof is included in `docs/source.tex`.
- Source proof / prover notes: a later proof may need `Real.sqrt` algebra and the relation between this formula and chord lengths of the contact points.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.

### Named item: `EuclideanGeometry.circlePoint`

- Source locator: `docs/source.tex`, theorem block `thm:casey`, lines 17-19, phrases “Let `O` be a circle of radius `R`” and “Let `O₁, O₂, O₃, O₄` be ... circles”.
- Lean declaration: `def EuclideanGeometry.circlePoint (center : Point) (radius : ℝ) : Set Point`.
- Dependencies: `EuclideanGeometry.Point`, `EuclideanGeometry.sqDist`.
- Formal statement review: `circlePoint center radius` is the boundary set `{p | sqDist p center = radius^2}` of a circle in the analytic plane.
- Source qualifiers:
  - Mathematical object class: Euclidean-plane circle.
  - Quantifier order: center first, radius second.
  - Parameter domains: center is an analytic plane point; radius is a real number.
  - Output codomain: `Set Point`.
  - Equality/image condition: membership means squared distance from the center equals `radius^2`.
  - Side conditions: the source theorem supplies positive outer radius and nonnegative inner radii.
  - Follow-on claims: radius-zero circles reduce to point circles in the degenerate note.
- Lean coverage: covers the object-class bridge needed to interpret the source's circles as concrete Lean sets of points. The zero-radius point interpretation is also represented by allowing zero radii in `liesInsideAndTangentTo` and `nonintersectingCircles` and by the Ptolemy bridge declarations.
- Scope changes: analytic `ℝ × ℝ` plane and squared-distance equality are used instead of a Mathlib `Sphere` object; no abstract circle structure is introduced.
- Complete source proof text: no proof is included in `docs/source.tex`.
- Source proof / prover notes: radius-zero cases should unfold `circlePoint` and use nonnegativity of squared distance in the real plane.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.

### Source theorem: `thm:casey` / `EuclideanGeometry.caseys_theorem`

- Source locator: `docs/source.tex`, theorem block `thm:casey`, lines 17-23, title `caseys_theorem`.
- Lean declaration: `theorem EuclideanGeometry.caseys_theorem`.
- Dependencies: `EuclideanGeometry.external_tangent_length`, `EuclideanGeometry.circlePoint`, `EuclideanGeometry.liesInsideAndTangentTo`, `EuclideanGeometry.fourCirclesNonintersecting`, `EuclideanGeometry.caseyInOrder`.
- Complete source statement:

```text
Let O be a circle of radius R. Let O_1, O_2, O_3, O_4 be (in that order) four non-intersecting circles that lie inside O and tangent to it. Denote by t_{ij} the length of the exterior common bitangent of the circles O_i, O_j. Then:
  t_{12} · t_{34} + t_{14} · t_{23} = t_{13} · t_{24}.
Note that in the degenerate case, where all four circles reduce to points, this is exactly Ptolemy's theorem.
```

- Complete source proof text: no proof is included in `docs/source.tex`.
- Lean statement:

```lean
theorem EuclideanGeometry.caseys_theorem
    (O : EuclideanGeometry.Point) (R : ℝ)
    (O₁ O₂ O₃ O₄ : EuclideanGeometry.Point) (r₁ r₂ r₃ r₄ : ℝ)
    (hR : 0 < R)
    (h₁ : EuclideanGeometry.liesInsideAndTangentTo O₁ O r₁ R)
    (h₂ : EuclideanGeometry.liesInsideAndTangentTo O₂ O r₂ R)
    (h₃ : EuclideanGeometry.liesInsideAndTangentTo O₃ O r₃ R)
    (h₄ : EuclideanGeometry.liesInsideAndTangentTo O₄ O r₄ R)
    (hNonintersecting : EuclideanGeometry.fourCirclesNonintersecting O₁ O₂ O₃ O₄ r₁ r₂ r₃ r₄)
    (hOrder : EuclideanGeometry.caseyInOrder O R O₁ O₂ O₃ O₄ r₁ r₂ r₃ r₄) :
    let t₁₂ := EuclideanGeometry.external_tangent_length O₁ O₂ r₁ r₂
    let t₁₃ := EuclideanGeometry.external_tangent_length O₁ O₃ r₁ r₃
    let t₁₄ := EuclideanGeometry.external_tangent_length O₁ O₄ r₁ r₄
    let t₂₃ := EuclideanGeometry.external_tangent_length O₂ O₃ r₂ r₃
    let t₂₄ := EuclideanGeometry.external_tangent_length O₂ O₄ r₂ r₄
    let t₃₄ := EuclideanGeometry.external_tangent_length O₃ O₄ r₃ r₄
    t₁₂ * t₃₄ + t₁₄ * t₂₃ = t₁₃ * t₂₄ := by
  sorry
```

- Formal statement review:
  - Parameters are the outer center `O`, outer radius `R`, four inner centers `O₁ O₂ O₃ O₄`, and four inner radii `r₁ r₂ r₃ r₄`.
  - `hR : 0 < R` records that the source outer radius is positive.
  - Each `hᵢ : liesInsideAndTangentTo Oᵢ O rᵢ R` records that the corresponding circle lies inside the outer circle and is internally tangent to it, with `0 ≤ rᵢ` so the source's zero-radius degenerate case remains included.
  - `hNonintersecting : fourCirclesNonintersecting ...` records the source phrase “four non-intersecting circles” as strict pairwise disk disjointness, also allowing zero radii.
  - `hOrder : caseyInOrder ...` records the source phrase “in that order” as strict cyclic order of the radial contact points.
  - The conclusion uses local `let` bindings for all six `t_{ij}` values and states exactly `t₁₂ * t₃₄ + t₁₄ * t₂₃ = t₁₃ * t₂₄`.
- Source qualifiers:
  - Mathematical object class: circles in a Euclidean plane, represented by center/radius data in `ℝ × ℝ` with the circle set bridge `circlePoint`.
  - Quantifier order: outer circle data first, then the four inner circle data, then geometric hypotheses, then the equation.
  - Parameter domains: centers are analytic plane points; the outer radius is positive; inner radii are nonnegative and smaller than the outer radius under the tangency hypotheses.
  - Output codomain: the theorem conclusion is a `Prop` equality of real-valued lengths.
  - Equality/image condition: the exact Casey equality among exterior common bitangent lengths.
  - Side conditions: inner circles are inside and tangent to `O`; inner circles are pairwise nonintersecting; the four circles are cyclically ordered.
  - Follow-on claim: the degenerate zero-radius case is Ptolemy's theorem.
- Lean coverage:
  - The main Casey equality is fully present in the Lean theorem statement for the analytic model.
  - “Inside and tangent” is represented by `liesInsideAndTangentTo` and now allows the zero-radius degenerate case.
  - “Non-intersecting” is represented as strict pairwise disk disjointness with nonnegative radii.
  - “In that order” is represented by strict cyclic order of radial contact points on the outer circle.
  - The `t_{ij}` notation is represented by `external_tangent_length`.
  - The follow-on Ptolemy note is covered by the companion declarations `pointDistance`, `ptolemyEquality`, and `caseys_theorem_degenerate_ptolemy_bridge`; cyclic/cospherical hypotheses for the zero-radius instance come from the main theorem's `liesInsideAndTangentTo` and `caseyInOrder` hypotheses.
- Scope changes:
  - Uses an analytic `ℝ × ℝ` center/radius model rather than Mathlib's abstract `EuclideanGeometry.Sphere` API; `circlePoint` records the bridge.
  - Exterior bitangent length is defined by the standard formula and does not construct tangent lines.
  - Strict nonintersection excludes pairwise tangency between the inner circles; this matches the source phrase “non-intersecting”.
  - No source proof is available; proof obligations are intentionally left as `by sorry` for later proving.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes:
  - No source proof is present.
  - Standard proof route: let `Pᵢ` be the contact point of `Oᵢ` with `O`. The points `P₁, P₂, P₃, P₄` lie on the outer circle and are in cyclic order. Apply Ptolemy to these four contact points.
  - If `aᵢ = R - rᵢ`, then for two inner circles tangent to the same outer circle, `external_tangent_length Oᵢ Oⱼ rᵢ rⱼ = sqrt (aᵢ * aⱼ) / R * chord(Pᵢ, Pⱼ)` under the positivity/nonnegativity hypotheses. The same factor `sqrt (a₁*a₂*a₃*a₄) / R^2` multiplies every term in Ptolemy, yielding Casey's equality.
  - In the degenerate case `r₁ = r₂ = r₃ = r₄ = 0`, each contact point is the corresponding point circle center and `external_tangent_length Pᵢ Pⱼ 0 0 = pointDistance Pᵢ Pⱼ`, so the statement specializes to Ptolemy.

### Source follow-on bridge: `thm:casey/degenerate-ptolemy-note`

- Source locator: `docs/source.tex`, theorem block `thm:casey`, line 22, sentence “Note that in the degenerate case, where all four circles reduce to points, this is exactly Ptolemy's theorem.”
- Lean declarations: `EuclideanGeometry.pointDistance`, `EuclideanGeometry.ptolemyEquality`, `EuclideanGeometry.caseys_theorem_degenerate_ptolemy_bridge`.
- Dependencies: `EuclideanGeometry.external_tangent_length`, `EuclideanGeometry.sqDist`, `Real.sqrt`.
- Formal statement review: `ptolemyEquality` states the ordinary point-distance Ptolemy equality, and `caseys_theorem_degenerate_ptolemy_bridge` asserts that the raw Casey equality with all radii set to zero is equivalent to that Ptolemy equality.
- Source qualifiers:
  - Mathematical object class: the four degenerate circles are point circles in the same analytic Euclidean plane.
  - Quantifier order: four resulting points, then equivalence between the zero-radius Casey equality and Ptolemy equality.
  - Parameter domains: points are analytic plane points; the zero radii are explicit constants.
  - Output codomain: a `Prop` equivalence.
  - Equality/image condition: exterior bitangent lengths with radii `0,0` become ordinary point distances in the Ptolemy equality.
  - Side conditions: cyclic/cospherical side conditions are supplied when the bridge is used as the zero-radius specialization of `caseys_theorem`.
  - Follow-on claims: this is the follow-on claim itself.
- Lean coverage: covers the source's Ptolemy note as a companion declaration rather than merely a comment. The richer theorem-side hypotheses remain in `caseys_theorem`; this bridge identifies the equality form.
- Scope changes: does not reprove the full Mathlib Ptolemy theorem in this draft; it records the representation/equality bridge needed for the source note.
- Complete source proof text: no proof is included in `docs/source.tex`.
- Source proof / prover notes: unfold `external_tangent_length`, `pointDistance`, and `ptolemyEquality`; simplify `(0 - 0)^2`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.

## Proof Handoff Checklist

- [x] Source document, preflight context, manifest, instructions, and skeletons read.
- [x] Blueprint source inventory includes `thm:casey` and the required named declarations.
- [x] Target Lean file begins with imports before comments/declarations.
- [x] Root project module imports the generated target module path.
- [x] Definition/structure/class construction stubs avoided; only theorem proof obligations use `by sorry` in the planner draft.
- [x] Statement/source verification passed by manual needs-review audit on 2026-06-04.
- [x] Proof-ready handoff recorded for later prover workflow; theorem proofs remain intentionally `by sorry`.
