# Formalization Blueprint: `algebraic-geometry/L3/alg_gen_L3_003`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench.lean` imports `ShadowBench.Source`.
- `ShadowBench/Source.lean` imports `ShadowBench.Source.Main`.
- `ShadowBench/Source/Main.lean` contains the source-backed theorem skeleton `locallyOfFinitePresentation_isStableUnderBaseChange`.

The existing root project module reaches `ShadowBench/Source/Main.lean`, so a project build of target `ShadowBench` covers the generated formalization file.

## Import Plan

```lean
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
```

This direct import is required for `AlgebraicGeometry.LocallyOfFinitePresentation`, the scheme-level Chevalley theorem `AlgebraicGeometry.Scheme.Hom.isLocallyConstructible_image`, and the transitive constructible-topology and ring-spectrum dependencies used by that theorem.

## Suggested Search Modules

These modules were useful search or source-proof hints but are not listed as direct Lean imports because they are already imported transitively by `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.AlgebraicGeometry.Properties`
- `Mathlib.RingTheory.RingHom.FinitePresentation`
- `Mathlib.RingTheory.Spectrum.Prime.Chevalley`
- `Mathlib.Topology.Constructible`

## Required Names

- `locallyOfFinitePresentation_isStableUnderBaseChange`

## Search Record

- `lean_search` for locally constructible images under finite-presentation scheme morphisms found `AlgebraicGeometry.Scheme.Hom.isLocallyConstructible_image` in `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
- `lean_search` for locally constructible predicates found `Topology.IsLocallyConstructible` in `Mathlib.Topology.Constructible`.
- `lean_search` for affine/spectrum Chevalley support found `PrimeSpectrum.isConstructible_comap_image` in `Mathlib.RingTheory.Spectrum.Prime.Chevalley`.

## Candidate Skeleton Review

- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, `Skeleton3.lean`, and `Skeleton4.lean` all proposed a theorem with invented or non-Mathlib names such as `Scheme X`, `SchemeMorphism`, and a new `LocallyConstructible` predicate. Those candidates do not match current Mathlib scheme APIs and would introduce construction gaps.
- No skeleton was adopted directly. The final Lean statement uses Mathlib's existing scheme morphism type `X ⟶ Y`, `Topology.IsLocallyConstructible`, and Mathlib's documented representation of a morphism of finite presentation as `LocallyOfFinitePresentation` plus `QuasiCompact`.

## Source Inventory

- `line-17` (theorem, `docs/source.tex` lines 17--19; proof lines 19--42) maps to Lean declaration `locallyOfFinitePresentation_isStableUnderBaseChange` in `ShadowBench/Source/Main.lean`.

## Source Statement Inventory

### line-17

- Source inventory entry: `line-17`
- Planned Lean declarations: `locallyOfFinitePresentation_isStableUnderBaseChange`
- Source locator: `line-17`, `docs/source.tex`, theorem block lines 17--19, proof lines 19--42.
- Source statement: Let `f : X → Y` be a morphism of schemes. Assume `f` is of finite presentation. Then the image of a locally constructible subset is locally constructible.
- Lean declaration shape:

```lean
theorem locallyOfFinitePresentation_isStableUnderBaseChange
    {X Y : Scheme} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [QuasiCompact f]
    {E : Set X} (hE : IsLocallyConstructible E) :
    IsLocallyConstructible (f '' E) := by
  sorry
```

- Dependencies:
  - `CategoryTheory` notation for `X ⟶ Y`.
  - `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom` for schemes and morphisms.
  - `AlgebraicGeometry.LocallyOfFinitePresentation` and `AlgebraicGeometry.QuasiCompact` for Mathlib's finite-presentation morphism convention.
  - `Topology.IsLocallyConstructible` for locally constructible subsets.
  - Likely proof theorem: `AlgebraicGeometry.Scheme.Hom.isLocallyConstructible_image`.
- Formal statement review:
  - The source theorem title says `locallyOfFinitePresentation_isStableUnderBaseChange`, but the displayed statement is Chevalley's theorem for images of locally constructible subsets under morphisms of finite presentation. The Lean declaration preserves the required name while formalizing the displayed source statement rather than the misleading title phrase.
  - Mathlib's `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation` module explicitly states that it does not provide a single separate declaration for scheme morphisms "of finite presentation"; instead such a morphism is represented by the two assumptions `LocallyOfFinitePresentation f` and `QuasiCompact f`. The Lean theorem records exactly those two assumptions.
  - The image `f '' E` is the set-theoretic image under the underlying continuous map of the scheme morphism, matching the source phrase `f(E)`.
- Source qualifiers:
  - Mathematical object class: schemes `X` and `Y`.
  - Quantifier order: for all schemes `X Y`, morphisms `f : X ⟶ Y`, and subsets `E : Set X`.
  - Parameter domain: `E` is a subset of the underlying topological space of `X`.
  - Side condition on morphism: `f` is of finite presentation.
  - Side condition on subset: `E` is locally constructible.
  - Output codomain: the image is a subset of the underlying topological space of `Y`.
  - Equality/image condition: output subset is `f '' E`.
  - Conclusion: `f '' E` is locally constructible.
- Lean coverage:
  - Schemes and morphisms are represented by `{X Y : Scheme} (f : X ⟶ Y)`.
  - Finite presentation is covered by `[LocallyOfFinitePresentation f] [QuasiCompact f]`, the Mathlib representation of a finite-presentation scheme morphism.
  - Locally constructible source subset is covered by `{E : Set X} (hE : IsLocallyConstructible E)`.
  - The image and output codomain are covered by `IsLocallyConstructible (f '' E)`.
- Scope changes: none. Representation note only: the single source phrase "of finite presentation" is split into Mathlib's two typeclass assumptions `LocallyOfFinitePresentation f` and `QuasiCompact f`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof text:

```text
Let E ⊂ X be locally constructible. We want to show that f(E) is locally constructible. We will show that f(E) ∩ V is constructible for any affine open V ⊂ Y. Thus we reduce to the case where Y is affine. In this case, X is quasi-compact. Hence, we can write X = U_1 ∪ ⋯ ∪ U_n with each U_i affine open in X. If E ⊂ X is locally constructible, then each E ∩ U_i is constructible. Hence, since f(E) = ∪ f(E ∩ U_i) and since finite unions of constructible sets are constructible, this reduces us to the case where X is affine.

Write X = Spec S and Y = Spec R. Since f is of finite presentation, we can write S = R[x_1,⋯,x_n]/(f_1,⋯,f_m). We may factor R → S as R → R[x_1] → R[x_1,x_2] → ⋯ → R[x_1,⋯,x_{n-1}] → S. Moreover, if S = R[x]/(f_1,⋯,f_m), we can factor the map as R → R[x] → S, and the closed immersion Spec S ↪ Spec R[x] maps constructible subsets to constructible subsets, it suffices to show the case S = R[x]. Now it suffices to show that if T = (∪_{i=1}^n D(f_i)) ∩ V(g_1,⋯,g_m) for f_i,g_j ∈ R[x], then the image of T in Spec(R) is constructible. Since finite unions of constructible sets are constructible, we may assume that n = 1, i.e. T = D(f) ∩ V(g_1,⋯,g_m).

If c ∈ R, then Spec(R) = V(c) ⨿ D(c) = Spec(R/(c)) ⨿ Spec(R_c), and correspondingly Spec(R[x]) = V(c) ⨿ D(c) = Spec(R/(c)[x]) ⨿ Spec(R_c[x]). The intersection of T = D(f) ∩ V(g_1,⋯,g_m) with each part still has the same shape, with f and g_i replaced by their images in R/(c)[x], respectively R_c[x]. The image of T in Spec(R) is the union of the images of T ∩ V(c) and T ∩ D(c). Since D(c) is an open subscheme and V(c) is a closed subscheme, it suffices to prove the images of both parts are constructible in Spec(R/(c)), respectively Spec(R_c).

Assume T = D(f) ∩ V(g_1,⋯,g_m) with deg(g_1) ≤ deg(g_2) ≤ ⋯ ≤ deg(g_m). Use induction on m and on the degrees d_i = deg(g_i). Write g_1 = c x^{d_1} + lower-order terms with c ∈ R non-zero. Cutting R into R/(c) and R_c either lowers the degree of g_1 or reduces to the case where c is invertible. If c is invertible and m > 1, write g_2 = c' x^{d_2} + lower-order terms and set g_2' = g_2 - (c'/c)x^{d_2-d_1} g_1. The ideals (g_1,g_2,⋯,g_m) and (g_1,g_2',g_3,⋯,g_m) are equal, so T is unchanged, but deg(g_2') < deg(g_2), which is covered by induction.

The base cases are (a) T = D(f) ∩ V(g) where the leading coefficient of g is invertible, and (b) T = D(f).

For case (a), write g = u x^d + a_{d-1}x^{d-1} + ⋯ + a_0 with u ∈ Rˣ. The ring A = R[x]/(g) is a finite free R-module with basis the images of 1,x,⋯,x^{d-1}. Let P(T) = T^d + r_{d-1}T^{d-1} + ⋯ + r_0 be the characteristic polynomial of multiplication by f on A. The image of D(f) ∩ V(g) in Spec(R) is ∪_{i=0}^{d-1} D(r_i). Indeed, p ∈ V(r_0,⋯,r_{d-1}) iff multiplication by f is nilpotent on A ⊗_R κ(p). If q ∈ D(f) ∩ V(g) maps to p, then A ⊗_R κ(p) maps nontrivially to κ(q), compatibly with multiplication by f, and f acts as a unit on κ(q), so p is not in V(r_0,⋯,r_{d-1}). Conversely, if some r_i is not in p, multiplication by f is not nilpotent on A ⊗_R κ(p), so there is a prime q̄ of A ⊗_R κ(p) not containing the image of f; its inverse image in R[x] lies in D(f) ∩ V(g) and maps to p.

For case (b), the image of D(f) under Spec(R[x]) → Spec(R) is the image of Spec(R[x]_f) → Spec(R). A prime p ⊂ R is in the image iff R[x]_f ⊗_R κ(p) = κ(p)[x]_{f̄} is nonzero, exactly when f does not map to zero in κ(p)[x]. Hence, if f = a_d x^d + ⋯ + a_0, then the image of D(f) is ∪_{i=0}^d D(a_i).
```

- Prover notes:
  - The intended proof is already available in Mathlib as `AlgebraicGeometry.Scheme.Hom.isLocallyConstructible_image`; after statement/source review, the prover should be able to close the theorem by applying this lemma to `hE`.
  - If proving from source rather than using the existing theorem, follow the affine-cover reductions, the spectrum Chevalley theorem `PrimeSpectrum.isConstructible_comap_image`, and the constructible/local-constructible conversion lemmas in `Topology.Constructible`.
