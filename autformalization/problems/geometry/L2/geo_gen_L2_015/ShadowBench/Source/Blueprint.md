# Formalization Blueprint: `geometry/L2/geo_gen_L2_015`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Document and Support Files Read

- `docs/source.tex` inspected with `formalization_document_inspect`; source label is `line-17`.
- Preflight manifest read from `.epflemma/workflow-state/formalization/docs-source/manifest.json`.
- Planner context read from `.epflemma/workflow-state/formalization/docs-source/context.md`.
- Required ShadowBench support files read: `docs/instructions.md`, `docs/skeletons/README.md`, and `docs/skeletons/Skeleton1.lean` through `Skeleton4.lean`.
- The manifest listed no bibliography files, citations, local PDFs, or figures.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: direct formalization of the single source theorem, plus the companion definition recording the Lean representation of the separating-pair set.
- Root coverage: `ShadowBench.lean` imports `ShadowBench.Source`, and `ShadowBench/Source.lean` imports `ShadowBench.Source.Main`, so a project build reaches the generated target module.

## Import Plan

```lean
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Convex.Cone.Basic
```

## Suggested Search Modules

- `Mathlib.Geometry.Convex.Cone.Basic`: `ConvexCone`, `ConvexCone.Pointed`, `ConvexCone.convex`, closure lemmas.
- `Mathlib.Analysis.InnerProductSpace.PiL2`: finite Euclidean space model `Fin n → ℝ` and scalar/product instances.
- Search notes used during drafting: `ConvexCone`, `ConvexCone.Pointed`, `ConvexCone.add_mem`, `ConvexCone.smul_mem`.

## Required Names

- `separatingHyperplanes_is_pointed`

## Candidate Skeleton Review

- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` all proposed the same theorem shape with `C D : Set (Fin n → ℝ)`, a finite sum for `a^T x`, `Convex ℝ S`, nonnegative scalar closure, and origin membership.
- `docs/skeletons/Skeleton4.lean` contains a malformed duplicated proof delimiter and was not adopted.
- Adopted from the viable skeletons: the finite-coordinate representation `Fin n → ℝ`, the set-comprehension inequalities, the required theorem name, and the direct imports from `docs/instructions.md`.
- Corrected relative to the viable skeletons: origin membership is a top-level conclusion, the source parenthetical singleton claim is represented, and the set `S` is factored into the implemented companion definition `separatingHyperplanesSet` so the `ℝ^{n+1}` representation bridge is explicit.

## Source Statement Inventory

### line-17

- Source label: `line-17`.
- Source kind/title: theorem `[separatingHyperplanes_is_pointed]`.
- Source locator: `docs/source.tex`, theorem lines 17--19; proof lines 21--37.
- Source statement: Suppose that `C` and `D` are disjoint subsets of `ℝ^n`. Consider the set of `(a, b) ∈ ℝ^{n+1}` for which `a^T x ≤ b` for all `x ∈ C`, and `a^T x ≥ b` for all `x ∈ D`. Show that this set is a convex cone containing the origin. The parenthetical says that this set is the singleton `{0}` if there is no hyperplane that separates `C` and `D`.
- Planned Lean declaration: `separatingHyperplanes_is_pointed`.
- Companion Lean declaration: `separatingHyperplanesSet`.
- Planned Lean declarations: `separatingHyperplanesSet`, `separatingHyperplanes_is_pointed`.
- Lean statement summary: the companion definition records the separating coefficient pairs `(a,b)` with `a^T x` represented by `∑ i, a i * x i`; the theorem asserts that this set is the carrier of a Mathlib convex cone containing the origin and also asserts the singleton conclusion under the Lean interpretation of "no separating hyperplane" as every separating pair being zero.
- Dependencies: direct imports in the Import Plan; companion definition `separatingHyperplanesSet`; finite sums over `Fin n`; product scalar/additive instances on `(Fin n → ℝ) × ℝ`; the Mathlib pointed-cone predicate for containing the origin.
- Source qualifiers:
  - Mathematical object class: arbitrary subsets `C D` of Euclidean `ℝ^n`.
  - Quantifier order and parameter domain: for an arbitrary finite dimension `n`, then arbitrary subsets `C D : Set ℝ^n`, assuming `C` and `D` are disjoint.
  - Side condition: `C` and `D` are disjoint.
  - Separating-pair set: coefficient/vector pairs `(a,b)` with all `C`-points satisfying `a^T x ≤ b` and all `D`-points satisfying `a^T x ≥ b`.
  - Output codomain/representation: subset of `ℝ^{n+1}`.
  - Equality/image condition: the set under discussion is exactly the set of those coefficient pairs; the theorem's convex-cone carrier must be equal to that set.
  - Follow-on claim: if there is no separating hyperplane other than the zero coefficient pair, the set is the singleton `{0}`.
- Lean coverage:
  - `ℝ^n` is represented by `Fin n → ℝ`; `ℝ^{n+1}` is represented by `(Fin n → ℝ) × ℝ` via the implemented definition `separatingHyperplanesSet`.
  - `a^T x` is represented by the finite dot-product sum `∑ i, a i * x i`.
  - Disjointness is preserved as hypothesis `h_disjoint : Disjoint C D`, although the algebraic cone proof does not need it.
  - The separating-pair set is exactly the companion definition `separatingHyperplanesSet n C D`; the theorem requires carrier equality `(K : Set _) = separatingHyperplanesSet n C D`.
  - Convex-cone status is expressed by existence of a Mathlib `ConvexCone` with carrier equal to the separating-pair set; containing the origin is expressed by `ConvexCone.Pointed`.
  - The parenthetical is expressed as `(∀ p ∈ separatingHyperplanesSet n C D, p = 0) → separatingHyperplanesSet n C D = {0}`. This is the algebraic coefficient-pair interpretation of "no hyperplane separates".
- Scope changes: no separate geometric hyperplane structure is introduced; the source describes separating hyperplanes through coefficient pairs `(a,b)`, and the Lean statement keeps that representation with the companion definition as the bridge. The phrase "no hyperplane that separates" is recorded as absence of any nonzero pair in the same separating-pair set. The theorem title says `is_pointed`; Mathlib's pointed-cone predicate means contains the origin, matching the source wording "containing the origin" rather than the alternative convex-analysis meaning "salient".
- Formal statement review: drafted to preserve the quantifier order `(n) (C D) (h_disjoint)`, the set of separating coefficient pairs, both inequality directions, convex-cone/origin conclusion, and the singleton follow-on claim under the recorded coefficient-pair interpretation. Needs independent statement/source verification before status can be approved.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: Let `S = { (a, b) ∈ ℝ^n × ℝ | ∀ x ∈ C, a^T x ≤ b and ∀ x ∈ D, a^T x ≥ b }`. Cone property: let `(a,b) ∈ S` and `λ > 0`; multiply the defining inequalities by `λ` to get `(λa)^T x ≤ λb` on `C` and `(λa)^T x ≥ λb` on `D`, hence `λ(a,b) ∈ S`; the `λ=0` case gives `(0,0) ∈ S`. Addition/convexity: if `(a₁,b₁),(a₂,b₂) ∈ S`, add the respective inequalities to get `(a₁+a₂)^T x ≤ b₁+b₂` on `C` and `(a₁+a₂)^T x ≥ b₁+b₂` on `D`, so the sum belongs to `S`. Therefore `S` is a cone, is closed under addition, and contains the origin.
- Prover notes: Construct the `ConvexCone` using the defining set. The scalar step should use nonnegative/positive scalar multiplication on both sides of the inequalities and rewrite the finite sum for `(λ • a)` as `λ * ∑ i, a i * x i`. The addition step should rewrite the finite sum for `a₁ + a₂` using `Finset.sum_add_distrib` and then use `add_le_add` / `add_le_add` in the reversed direction for `D`. Origin membership is by simplifying both inequalities to `0 ≤ 0`. The singleton implication follows by `Set.ext`: membership in `{0}` is exactly equality to `0`, and the reverse inclusion uses the origin membership already proved.

## Verification Plan and Handoff

- Draft readiness checks run: `lean_inspect ShadowBench/Source/Main.lean`; project-level `lean_verify(mode=project)` completed successfully with the intentional theorem `sorry` warning.
- Independent statement/source review must approve or correct `line-17` before proof handoff.
- Suggested next proof command after review approval: `/prove ShadowBench/Source/Main.lean separatingHyperplanes_is_pointed`

## Review Checklist

- [x] Source document and preflight manifest read.
- [x] Candidate skeletons compared against the source.
- [x] Local project and Mathlib searches recorded.
- [x] Blueprint source inventory includes `line-17`.
- [x] Lean declarations drafted with source-aware doc comments.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [x] Proof-ready handoff accepted for the later prove workflow by formalization PASS and 2026-06-05 audit.
