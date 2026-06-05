# Formalization Blueprint: `geometry/L2/geo_gen_L2_009`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Source Documents and Support Files

- Primary source document: `docs/source.tex`
- Preflight manifest: `.epflemma/workflow-state/formalization/docs-source/manifest.json`
- Extracted text cache: `.epflemma/workflow-state/formalization/docs-source/extracted.txt`
- Nearby PDFs/figures/bibliography files: none listed by the manifest.
- Detected theorem-like blocks: `line-17`, theorem `tangentBundleProdDiffeomorph`, source lines 17--19.

## Import Plan

```lean
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
```

## Suggested Search Modules

- `Mathlib.Geometry.Manifold.ContMDiffMFDeriv` for `equivTangentBundleProd`,
  `contMDiff_equivTangentBundleProd`, and `contMDiff_equivTangentBundleProd_symm`.
- `Mathlib.Geometry.Manifold.Diffeomorph` if a later refactor chooses to package the same
  equivalence as a `Diffeomorph` structure instead of an existential equivalence with two
  smoothness fields.

## Generated File Layout

- `ShadowBench.lean` imports `ShadowBench.Source`.
- `ShadowBench/Source.lean` imports `ShadowBench.Source.Main`.
- `ShadowBench/Source/Main.lean` contains the source-backed declaration
  `tangentBundleProdDiffeomorph`.

## Required Names

- `tangentBundleProdDiffeomorph`

## Candidate Skeleton Review

- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` use the required
  theorem name and the starting import, but their statement uses non-elaborating shorthand
  `[Manifold ℝ M]`, `[Manifold ℝ N]`, and `T (M × N)` rather than Mathlib's explicit
  model-with-corners tangent-bundle parameters.
- `docs/skeletons/Skeleton4.lean` duplicates the same candidate and also has an extra
  malformed proof terminator line.
- The final statement keeps the intended source direction `T(M × N) → TM × TN` and the
  required name, but replaces the shorthand with Mathlib's explicit
  `ModelWithCorners`, `ChartedSpace`, `IsManifold`, and `TangentBundle` API.

## Source Statement Inventory

### line-17

- Source locator: `docs/source.tex`, label `line-17`, lines 17--19.
- Source kind/title: theorem `tangentBundleProdDiffeomorph`.
- Source inventory entry: `line-17`.
- Lean declaration: `tangentBundleProdDiffeomorph`.
- Source locator: `docs/source.tex`, lines 17--19.
- Source statement: "Prove that if $M$ and $N$ are smooth manifolds, then
  $T(M \times N)$ is diffeomorphic to $TM \times TN$."
- Scope changes: no weakening of the mathematical conclusion; Lean makes the implicit real
  chart/model data explicit and states the result in Mathlib's model-with-corners API, which
  includes ordinary real smooth manifolds as a special case.
- Source proof / prover notes: the source contains no proof environment or proof text.  The
  prover should use `equivTangentBundleProd I M I' N` and close smoothness with
  `contMDiff_equivTangentBundleProd` and `contMDiff_equivTangentBundleProd_symm`.
- Planned Lean declaration: `tangentBundleProdDiffeomorph` in
  `ShadowBench/Source/Main.lean`.
- Lean statement:

```lean
theorem tangentBundleProdDiffeomorph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H']
    (I' : ModelWithCorners ℝ E' H')
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N] :
    ∃ f : TangentBundle (I.prod I') (M × N) ≃
        (TangentBundle I M × TangentBundle I' N),
      CMDiff ∞ f ∧ CMDiff ∞ f.symm
```

- Source qualifiers:
  - Mathematical object class: real smooth manifolds `M` and `N`, represented in Lean by
    topological spaces with charted-space structures modeled by `I : ModelWithCorners ℝ E H`
    and `I' : ModelWithCorners ℝ E' H'`, with `IsManifold I ∞ M` and
    `IsManifold I' ∞ N`.
  - Quantifier order: the model vector spaces, model spaces, and model-with-corners data are
    made explicit before the manifold types whose structures depend on them.
  - Parameter domain: arbitrary real smooth manifolds in Mathlib's model-with-corners API.
  - Product condition: the product manifold is modeled by `I.prod I'` on `M × N`.
  - Output codomain: the product of tangent bundles `TangentBundle I M × TangentBundle I' N`.
  - Diffeomorphism/equality condition: existence of a bijective equivalence from
    `TangentBundle (I.prod I') (M × N)` to the product tangent bundle whose forward and inverse
    maps are both `CMDiff ∞`.
  - Side conditions: `NormedAddCommGroup`, `NormedSpace ℝ`, `TopologicalSpace`, and
    `ChartedSpace` instances are explicit Lean infrastructure for the source phrase
    "smooth manifolds".
  - Follow-on claims: none in the source.
- Lean coverage: full coverage of the source claim.  The source word "diffeomorphic" is encoded
  as an existential `Equiv` plus `CMDiff ∞` smoothness of the map and inverse; this is the same
  data carried by Mathlib's `Diffeomorph` structure, expressed without adding a direct import of
  `Mathlib.Geometry.Manifold.Diffeomorph`.  The source phrase "smooth manifolds" is covered by
  the explicit `ModelWithCorners`, `ChartedSpace`, and `IsManifold _ ∞` assumptions; ordinary
  real smooth manifolds are included by the standard no-boundary model choice.
- Scope changes: no weakening of the mathematical conclusion.  The source suppresses model-space
  and chart data; Lean makes those structures explicit.  The Lean statement is slightly more
  general in object class because it is phrased for arbitrary real `ModelWithCorners` data,
  including manifolds with boundary/corners as well as ordinary smooth manifolds.  The source does
  not specify a non-real base field, so the statement uses the standard real smooth-manifold
  interpretation of "smooth".  The representation of diffeomorphism as `Equiv` plus bidirectional
  `CMDiff ∞` is a definitional packaging choice, not an omission of a source qualifier.
- Dependencies:
  - Direct import: `Mathlib.Geometry.Manifold.ContMDiffMFDeriv`.
  - Key Mathlib declarations for the eventual proof:
    `equivTangentBundleProd`, `contMDiff_equivTangentBundleProd`, and
    `contMDiff_equivTangentBundleProd_symm`.
- Complete source proof text: the LaTeX source supplies no proof text beyond the theorem
  statement.
- Proof sketch / prover notes: use the canonical equivalence
  `equivTangentBundleProd I M I' N`, which sends a tangent vector over `(x, y)` with velocity
  `(v, w)` to the pair of tangent vectors over `x` and `y`; close the two smoothness goals with
  `contMDiff_equivTangentBundleProd` and `contMDiff_equivTangentBundleProd_symm`.
- Formal statement review: drafted from `docs/source.tex`, compared against all four skeletons,
  and checked for elaboration against the current import plan in a temporary Lean probe.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Proof handoff status: theorem proof is intentionally a later prover obligation for an explicit
  `/prove ShadowBench/Source/Main.lean tangentBundleProdDiffeomorph` workflow after review.

## Handoff Gate

- Source document and manifest inspected.
- Required support files and candidate skeletons read.
- Local/Mathlib search performed before finalizing the statement shape.
- Blueprint source inventory includes `line-17` with qualifiers, coverage, scope, and prover notes.
- Target Lean file begins with imports before comments or declarations.
- Root project module already imports `ShadowBench.Source.Main` via `ShadowBench.Source`.
- External statement/source verification is required before proof handoff; this planner draft
  does not authorize the prover queue.
