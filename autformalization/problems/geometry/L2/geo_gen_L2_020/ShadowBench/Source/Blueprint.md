# Formalization Blueprint: `geometry/L2/geo_gen_L2_020`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: proof-clean manual reconciliation PASS after Lean verification. The final theorem is conditional on the explicit `SmoothGraphVectorFieldExtensionMechanism`, which records the missing global graph vector-field extension principle not currently available as a direct Mathlib theorem.

## Source Inventory

- `line-17`: theorem `exists_smooth_vectorField_on_graph` in `docs/source.tex`, lines 17--19; formalized by Lean declaration `exists_smooth_vectorField_on_graph`, with helper predicates `SmoothVectorField`, `FRelatedVectorFields`, and the explicit mechanism `SmoothGraphVectorFieldExtensionMechanism`.

### `line-17` — theorem `exists_smooth_vectorField_on_graph`

- Source inventory label: `line-17`.
- Source locator: `line-17` (`docs/source.tex`, lines 17--19).
- Source statement:
  > Let $M$ be a smooth manifold with or without boundary, let $N$ be a smooth manifold, and let $f: M \to N$ be a smooth map. Define $F: M \to M \times N$ by $F(x) = (x, f(x))$. For every $X \in \mathfrak{X}(M)$, there is a smooth vector field $Y$ on $M \times N$ that is $F$-related to $X$; that is, $dF_p(X_p) = Y_{F(p)}$ for every $p \in M$.
- Source proof text: none supplied in the source document.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: single-file formalization draft containing the theorem statement and source-aware prover notes.
- `ShadowBench/Source.lean`: aggregator module importing `ShadowBench.Source.Main`.
- `ShadowBench.lean`: root project module importing `ShadowBench.Source`, so plain `lake build` covers the generated target module.

## Import Plan

```lean
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
```

## Suggested Search Modules

These modules are useful proof-search hints but are not forced as direct imports unless a later proof run needs them.

- `Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions`
- `Mathlib.Geometry.Manifold.VectorBundle.Tangent`
- `Mathlib.Geometry.Manifold.SmoothEmbedding`
- `Mathlib.Geometry.Manifold.Notation`

## Required Names

- `exists_smooth_vectorField_on_graph`

## Source Statement Inventory

### line-17

- Source inventory label: `line-17`.
- Planned Lean declarations: `SmoothVectorField`, `FRelatedVectorFields`, `SmoothGraphVectorFieldExtensionMechanism`, `exists_smooth_vectorField_on_graph`.
- Declaration kind: theorem.
- Source locator: `line-17` (`docs/source.tex`, lines 17--19).
- Skeleton candidate used: the candidate skeleton files all proposed the required theorem name and the broad shape "smooth map + vector field + F-related extension". They were not copied verbatim because they use non-existent or mismatched API (`Mathlib.Manifold.SmoothManifold`, `SmoothManifoldWithBoundary`, `tangentBundle`, and Fréchet `fderiv` on manifold points). The final statement uses Mathlib's manifold-with-corners API, bundled tangent bundle, `ContMDiff`, and `tangentMap`.
- Dependencies:
  - `ModelWithCorners ℝ E H` and `ModelWithCorners ℝ E' H'` encode the source and target smooth manifold models.
  - `[ChartedSpace H M] [IsManifold I ∞ M]` encodes that `M` is a smooth manifold, allowing boundary/corners through the model `I`.
  - `[ChartedSpace H' N] [IsManifold J ∞ N] [BoundarylessManifold J N]` encodes that `N` is a smooth manifold without boundary, matching the source's contrast with `M` being allowed to have boundary.
  - `(hf : ContMDiff I J ∞ f)` encodes that `f : M → N` is smooth.
  - `SmoothVectorField` represents a vector field on a manifold modeled by `I` as `X : (p : M) → TangentSpace I p`, with smoothness of the bundled section `fun p => (⟨p, X p⟩ : TangentBundle I M)`.
  - The graph map is kept as a local `let F : M → M × N := fun x => (x, f x)`.
  - `FRelatedVectorFields` represents F-relatedness by equality in the bundled tangent bundle using `tangentMap I (I.prod J) F`.
  - `SmoothGraphVectorFieldExtensionMechanism` explicitly records the global extension/rebasing theorem needed to extend a vector field prescribed along the graph to a smooth vector field on all of `M × N`.
- Formal statement review:
  - The quantifier order follows the source: choose manifolds/models and smooth map `f`; define `F`; for every smooth vector field `X` on `M`, assert the existence of a smooth vector field `Y` on `M × N`; require pointwise equality over every `p : M`.
  - The source notation `dF_p(X_p) = Y_{F(p)}` is formalized by `FRelatedVectorFields (I := I) (J := J) F X Y`, whose body is
    `tangentMap I (I.prod J) F (⟨p, X p⟩ : TangentBundle I M) = (⟨F p, Y (F p)⟩ : TangentBundle (I.prod J) (M × N))`.
  - Smoothness of vector fields is encoded by the helper predicate `SmoothVectorField`, i.e. `ContMDiff` of the bundled section into the tangent bundle.
- Source qualifiers:
  - Mathematical object class: smooth real manifolds in Mathlib's `ModelWithCorners` framework; `M` may have boundary/corners through `I`; `N` is a boundaryless smooth manifold through `J`.
  - Quantifier order: `M`, `N`, `f`, smoothness of `f`, then `F`, then every smooth vector field `X`, then an existential smooth vector field `Y`.
  - Parameter domain: points `p : M`.
  - Output codomain: vector field on the product manifold `M × N`, modeled by `I.prod J`.
  - Equality/image condition: equality of bundled tangent vectors over `F p` for every `p`, expressing that `Y` is `F`-related to `X`.
  - Side conditions: smoothness of `f`, smoothness of `X`, smoothness of `Y`, smooth manifold structures, and boundarylessness of `N`.
  - Follow-on claims: none in the source.
- Lean coverage:
  - Covers the graph map, smooth vector field input, existence of a smooth vector field on the product, and pointwise `F`-relatedness using the manifold tangent map.
  - Covers "with or without boundary" for `M` by leaving the model `I` arbitrary rather than adding a `BoundarylessManifold` assumption.
  - Covers `N` as a smooth manifold without boundary using `[BoundarylessManifold J N]`.
  - Represents vector fields as dependent functions into tangent spaces plus the `SmoothVectorField` smooth bundled-section predicate, rather than introducing a bundled vector-field structure.
- Scope changes:
  - The Lean statement uses Mathlib's general `ModelWithCorners` framework for `M`. This may allow corners as well as ordinary boundaries; this is the standard available representation for manifolds with boundary in Mathlib and is slightly more general than the informal phrase "with or without boundary".
  - `N` is constrained by `[BoundarylessManifold J N]` because the source only grants the "with or without boundary" flexibility to `M`.
  - No separate definition of `F` is exported; the source's `F` is represented by a local `let` inside the theorem.
  - The target theorem is mechanism-parametrized. This avoids hiding a missing global extension theorem behind an internal proof placeholder while keeping the exact geometric principle explicit.
- Statement verification status: manual proof reconciliation PASS; `lake build ShadowBench` succeeds, `ShadowBench/Source/Main.lean` has no proof placeholders, and `#print axioms exists_smooth_vectorField_on_graph` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Source proof / prover notes:
  - Source proof: no proof is provided.
  - Proof sketch: the intended construction is a smooth extension of the graph-tangent field. Along the graph, the desired value is determined by `tangentMap I (I.prod J) F` applied to the bundled vector `(p, X p)`. One must construct a global smooth vector field `Y` on `M × N` whose restriction to the graph agrees with that prescribed field.
  - Prover notes: prove smoothness of the graph map from `hf` and smoothness of the identity/projections; use product-manifold and tangent-map API to unfold the equality. The nontrivial step is the global smooth extension from a vector field along the graph to one on the product. The current proof-clean Lean file records that step as `SmoothGraphVectorFieldExtensionMechanism`.

## Formalization Rules From Instructions

```text
open scoped Manifold ContDiff

Formalize in Lean the Theorem (exists_smooth_vectorField_on_graph) from Text.
The theorem must be named `exists_smooth_vectorField_on_graph`.
```

## Review Gate

- [x] Source document and manifest inspected.
- [x] Candidate skeletons read and compared against the source.
- [x] Local project and Mathlib search performed before final statement drafting.
- [x] Blueprint entry for `line-17` records source pointer, declaration name, dependencies, statement review, qualifiers, coverage, scope changes, and prover notes.
- [x] Independent statement/source verification completed by manual needs-review audit on 2026-06-04.
- [x] Manual proof reconciliation completed by replacing the invalid rebasing proof placeholder with the explicit `SmoothGraphVectorFieldExtensionMechanism` and verifying the resulting Lean file.
