# Formalization Blueprint: `algebraic-geometry/L3/alg_gen_L3_014`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the source theorem formalization and its `by sorry` proof placeholder.
- `ShadowBench/Source.lean`: root project module, already directly imports `ShadowBench.Source.Main`, so the generated target module is covered by plain project builds.

## Import Plan

```lean
import Mathlib
```

The target Lean file currently uses exactly this direct import block.

## Suggested Search Modules

These were useful search hits or likely proof-search locations; they are not part of the direct import plan unless a prover later needs a narrower import set.

- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.AlgebraicGeometry.Restrict`
- `Mathlib.Topology.QuasiSeparated`
- `Mathlib.Topology.Constructible`

## Required Names

- `quasiSeparated_iff_preimage_isQuasiSeparated_of_openCover`

## Source Inventory

- `line-17`: theorem from `docs/source.tex` lines 17--22, formalized as `AlgebraicGeometry.quasiSeparated_iff_preimage_isQuasiSeparated_of_openCover` in `ShadowBench/Source/Main.lean`.

## Source Statement Inventory

### line-17

- Source inventory entry: `line-17`
- Source label: `line-17`
- Kind: theorem
- Source locator: `line-17` (`docs/source.tex` lines 17--22)
- Planned Lean declarations: `quasiSeparated_iff_preimage_isQuasiSeparated_of_openCover`
- Lean file: `ShadowBench/Source/Main.lean`
- Source locator: theorem statement at `docs/source.tex` lines 17--19; proof at lines 19--22.
- Skeleton candidate used: the required declaration name was taken from all four candidate skeletons. Their statement shape was not adopted: the skeletons model schemes as `[Scheme X]` typeclasses on `Type*` and use ordinary functions `X → Y`, while Mathlib represents schemes as objects of `AlgebraicGeometry.Scheme` and morphisms as `X ⟶ Y`. Skeleton 4 also has malformed duplicate proof syntax.
- Dependencies and proof-facing facts:
  - `AlgebraicGeometry.QuasiSeparated` for quasi-separated scheme morphisms.
  - `IsQuasiSeparated` for quasi-separated open subsets/topological subspaces.
  - `IsOpenCover` for an indexed open cover of the underlying topological space.
  - `f ⁻¹ᵁ U` notation for the open preimage of `U : Y.Opens` under a scheme morphism `f : X ⟶ Y`.
  - `AlgebraicGeometry.quasiSeparated_iff_quasiSeparatedSpace` and `AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated` for the bridge between morphisms to quasi-separated bases and quasi-separated source schemes.
  - restriction/base-change instances for `QuasiSeparated`, e.g. restrictions `f ∣_ U` and open-preimage lemmas such as `AlgebraicGeometry.Scheme.Hom.isQuasiSeparated_preimage` for the forward direction.
  - target-locality of `QuasiCompact`/`QuasiSeparated` supplied by the affine-property/local-at-target infrastructure.
- Lean statement:

```lean
theorem quasiSeparated_iff_preimage_isQuasiSeparated_of_openCover
    {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type*} (U : ι → Y.Opens)
    (hUcover : IsOpenCover U) (hUqs : ∀ i, IsQuasiSeparated (U i : Set Y)) :
    QuasiSeparated f ↔ ∀ i, IsQuasiSeparated (f ⁻¹ᵁ U i : Set X) := by
  sorry
```

- Source statement: Let \(f:X\to Y\) be a morphism, and let \((U_\alpha)\) be an open covering of \(Y\) such that each \(U_\alpha\) is quasi-separated. Then, \(f\) is quasi-separated if and only if every \(f^{-1}(U_\alpha)\) is quasi-separated.
- Complete source proof: The inverse image in \(X\times_Y X\) of \(U_\alpha\) is \(X_\alpha\times_{U_\alpha}X_\alpha\), where \(X_\alpha=f^{-1}(U_\alpha)\), and the restriction \(X_\alpha\to X_\alpha\times_{U_\alpha}X_\alpha\) of \(\Delta_f\) is nothing other than \(\Delta_{f_\alpha}\), where \(f_\alpha\) denotes the restriction \(X_\alpha\to U_\alpha\) of \(f\). By Definition of quasi-separated morphisms and the local character of the notion of a quasi-compact morphism, in order for \(f\) to be quasi-separated, it is necessary and sufficient that each of the morphisms \(f_\alpha\) be so. But since, by hypothesis, the morphism \(U_\alpha\to \mathrm{Spec}(\mathbb Z)\) is quasi-separated, it is equivalent to say that \(f_\alpha\) is quasi-separated or that the composite \(X_\alpha\xrightarrow{f_\alpha}U_\alpha\to \mathrm{Spec}(\mathbb Z)\) is quasi-separated. This proves the proposition.
- Source qualifiers:
  - Mathematical object class: schemes `X` and `Y`, with a scheme morphism `f : X ⟶ Y`.
  - Quantifier order: choose schemes `X Y`, a morphism `f`, an index type `ι`, an indexed family of open subsets `U : ι → Y.Opens`, then assumptions that `U` covers `Y` and every member is quasi-separated.
  - Cover condition: `hUcover : IsOpenCover U` represents that the `U i` form an open covering of `Y`.
  - Side condition: `hUqs : ∀ i, IsQuasiSeparated (U i : Set Y)` represents each cover member being quasi-separated.
  - Conclusion: `QuasiSeparated f ↔ ∀ i, IsQuasiSeparated (f ⁻¹ᵁ U i : Set X)` represents quasi-separatedness of `f` iff every inverse-image open subset is quasi-separated.
  - Output codomain/equality condition: no separate equality output; the theorem is an iff proposition.
- Lean coverage: full intended Mathlib coverage. The source's open subschemes `U_α` and `f^{-1}(U_α)` are represented by `Opens` and open-preimage notation, with quasi-separatedness expressed as `IsQuasiSeparated` on the underlying subsets. This is Mathlib's standard bridge to quasi-separated restricted schemes via `isQuasiSeparated_iff_quasiSeparatedSpace`, cited above for the prover.
- Scope changes: none intended. The only representation choice is using `IsQuasiSeparated` for open subsets instead of naming the restricted schemes explicitly; this follows Mathlib's existing equivalence between open-subset quasi-separatedness and the quasi-separated restricted topological/scheme space.
- Formal statement review: the theorem keeps the source morphism class, the open cover, the quasi-separatedness assumption on every cover member, and the iff conclusion about all inverse images. It does not replace the source with the weaker forward-only lemma `Scheme.Hom.isQuasiSeparated_preimage`; that lemma is only a proof dependency for one direction.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: prove the forward direction by restricting a quasi-separated morphism to each open `U i` or by applying `Scheme.Hom.isQuasiSeparated_preimage` to `hUqs i`. For the reverse direction, use that the diagonal of `f` is quasi-compact iff it is quasi-compact after pulling back to the open cover of `Y`; over `U i`, identify the restricted diagonal with the diagonal of the restricted morphism `fᵢ : Xᵢ ⟶ Uᵢ`. Then use the hypothesis that `U i` is quasi-separated and `quasiSeparated_iff_quasiSeparatedSpace` to convert quasi-separatedness of `Xᵢ = f ⁻¹ᵁ U i` into quasi-separatedness of `fᵢ`.

## Statement Verification Checklist

- [x] Source document was inspected with `formalization_document_inspect`.
- [x] Companion instructions and all four candidate skeletons were read.
- [x] Local/Mathlib search was used before finalizing the statement shape.
- [x] Source inventory includes the detected source theorem label `line-17`.
- [x] Lean doc comment for the source theorem includes source proof and prover notes.
- [x] Root module `ShadowBench/Source.lean` imports `ShadowBench.Source.Main`.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [x] Proof-ready handoff accepted for the later prove workflow by formalization PASS and 2026-06-05 audit.

## Theorem Queue for Later `/prove`

- `AlgebraicGeometry.quasiSeparated_iff_preimage_isQuasiSeparated_of_openCover`: theorem proof intentionally left as `by sorry` for the managed prover queue after independent statement/source review.
