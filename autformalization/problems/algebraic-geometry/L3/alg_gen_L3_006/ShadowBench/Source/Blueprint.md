# Formalization Blueprint: `algebraic-geometry/L3/alg_gen_L3_006`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the source-backed definition `FiniteType` and theorem skeleton `affineFiniteType_iff_globalSectionsFiniteType`.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so the generated target is covered by a root project build.

## Import Plan

```lean
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.FiniteType
import Mathlib.CategoryTheory.Opposites
```

## Suggested Search Modules

These are non-gating proof-search hints, not required imports unless a proof turn verifies a need.

- `Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`
- `Mathlib.AlgebraicGeometry.AffineScheme`
- `Mathlib.RingTheory.FiniteType`
- `Mathlib.RingTheory.Localization.Basic`

## Required Names

- `FiniteType`
- `affineFiniteType_iff_globalSectionsFiniteType`

## Candidate Skeleton Review

- `Skeleton1.lean`: useful for names and the high-level shape, but it used `X → Y` instead of categorical scheme morphisms `X ⟶ Y`, used a non-mathlib `globalSections` notation, and left the definition as `sorry`.
- `Skeleton2.lean`: same statement idea as Skeleton1 with fewer imports; still uses the wrong morphism/global-sections API and a definition stub.
- `Skeleton3.lean`: same as Skeleton2, with `by sorry` for the definition; rejected because definitions/constructions may not be left as proof obligations.
- `Skeleton4.lean`: syntactically malformed duplicate `:= by sorry`; rejected.
- Adopted shape: the source names and affine-scheme hypotheses from the skeletons were retained, but the Lean API was corrected to `Scheme` morphisms, `Scheme.Hom.appTop`, `RingHom.FiniteType`, and a real definition of `FiniteType`.

## Source Statement Inventory

- Source inventory entry: `line-17` → Lean declaration `FiniteType`.
- Source inventory entry: `line-30` → Lean declaration `affineFiniteType_iff_globalSectionsFiniteType`.

### line-17

- Title: Definition `FiniteType`.
- Source label: `line-17`.
- Source locator: `docs/source.tex`, lines 17-28.
- Source statement: A morphism `f : X → Y` is of finite type if `Y` is the union of affine open subsets `V_α` such that each inverse image `f^{-1}(V_α)` is a finite union of affine open subsets `U_{α i}` and each ring `Γ(U_{α i}, 𝒪_X)` is a finite-type algebra over `Γ(V_α, 𝒪_Y)`. Equivalently, `X` is a finite-type `Y`-scheme.
- Planned Lean declarations: `FiniteType`.
- Lean statement:

```lean
def FiniteType {X Y : Scheme} (f : X ⟶ Y) : Prop :=
  LocallyOfFiniteType f ∧ QuasiCompact f
```
- Skeleton candidate used: Skeleton1/Skeleton2 only for the required name and broad morphism-predicate shape; the body was replaced by the standard Mathlib finite-type bridge.
- Dependencies: `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`, categorical morphism notation from `CategoryTheory`.
- Formal statement review: the source definition describes finite-type morphisms via affine target cover plus finite affine covers of inverse images and finite-type section algebras. Mathlib has the local finite-type algebra condition as `LocallyOfFiniteType`; adjoining `QuasiCompact` records the finite-cover part of the source definition. The Lean definition is a representation bridge rather than an explicit sigma-type of covers.
- Source qualifiers:
  - Object class: schemes `X`, `Y`.
  - Quantifier order: first choose schemes `X`, `Y`, then a morphism `f : X ⟶ Y`.
  - Parameter domain: a scheme morphism `f : X ⟶ Y`; this is the structure map for saying that `X` is over `Y`.
  - Output codomain: a proposition/predicate on the morphism.
  - Equality/image condition: the target is covered by affine opens `V_α`, and each inverse image `f ⁻¹(V_α)` is covered by finitely many affine opens `U_{α i}`.
  - Side conditions: all `V_α` and `U_{α i}` are affine, each inverse-image cover is finite, and each induced coordinate-section map makes `Γ(U_{α i}, 𝒪_X)` a finite-type algebra over `Γ(V_α, 𝒪_Y)`.
  - Follow-on terminology: the same predicate is also phrased as “`X` is a scheme of finite type over `Y`” or a “finite-type `Y`-scheme”.
- Lean coverage: exact mathematical coverage through the standard Mathlib finite-type-morphism bridge `LocallyOfFiniteType f ∧ QuasiCompact f`: `LocallyOfFiniteType` covers the affine-local finite-type coordinate-ring condition, and `QuasiCompact` covers the finite affine-cover/quasi-compact part of the source definition. The Lean definition deliberately does not expose the cover witnesses as data.
- Scope changes: representation change only, not a mathematical weakening or strengthening. The source cover data is encoded by existing Mathlib predicates rather than by a bespoke cover structure.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: this is a definition, so there is no source proof. For future proof work, unfold `FiniteType` to obtain `LocallyOfFiniteType f` and `QuasiCompact f`; use Mathlib's affine-local morphism-property API to move between local affine statements and ring-hom finite type.

### line-30

- Title: Theorem `affineFiniteType_iff_globalSectionsFiniteType`.
- Source label: `line-30`.
- Source locator: `docs/source.tex`, theorem lines 30-32 and proof lines 34-43.
- Source statement: Let `X` and `Y` be affine schemes. Then `X` is of finite type over `Y` iff `Γ(X, 𝒪_X)` is a finite-type algebra over `Γ(Y, 𝒪_Y)`.
- Planned Lean declarations: `affineFiniteType_iff_globalSectionsFiniteType`.
- Lean statement:

```lean
theorem affineFiniteType_iff_globalSectionsFiniteType {X Y : Scheme}
    (hX : IsAffine X) (hY : IsAffine Y) (f : X ⟶ Y) :
    FiniteType f ↔ RingHom.FiniteType f.appTop.hom := by
  sorry
```

- Skeleton candidate used: Skeleton1/Skeleton2/Skeleton3 suggested the theorem name and affine hypotheses. The Lean statement was corrected from `IsFinitelyGeneratedAlgebra (globalSections Y) (globalSections X)` to `RingHom.FiniteType f.appTop`, the Mathlib statement that the induced global-section ring homomorphism is finite type.
- Dependencies: `FiniteType`, `AlgebraicGeometry.IsAffine`, `AlgebraicGeometry.Scheme.Hom.appTop`, `RingHom.FiniteType`.
- Formal statement review: `hX` and `hY` encode the source qualifier that `X` and `Y` are affine. The morphism `f : X ⟶ Y` supplies the `Y`-scheme structure implicit in the text. `RingHom.FiniteType f.appTop.hom` expresses that `Γ(X, 𝒪_X)` is a finite-type algebra over `Γ(Y, 𝒪_Y)` via the underlying ring homomorphism of the induced global-section morphism. The left side uses the source-backed definition `FiniteType f` from `line-17`.
- Source qualifiers:
  - Object class: affine schemes `X` and `Y`.
  - Quantifier order: choose schemes `X`, `Y`, affineness witnesses `hX`, `hY`, then a morphism `f : X ⟶ Y` expressing the otherwise implicit `Y`-scheme structure on `X`.
  - Parameter domain: a scheme morphism from the source scheme `X` to the target scheme `Y`.
  - Output codomain: a proposition, specifically an iff.
  - Equality/image condition: equivalence between the finite-type morphism condition on `f` and finite generation of the induced global-section algebra; the relevant image map is the contravariant map on global sections induced by `f`.
  - Left condition: `X` is finite type over `Y`, encoded as `FiniteType f`.
  - Right condition: `Γ(X, 𝒪_X)` is a finite-type algebra over `Γ(Y, 𝒪_Y)`, encoded as finite type of the induced ring homomorphism `f.appTop.hom : Γ(Y, ⊤) ⟶ Γ(X, ⊤)`.
  - Side conditions: both source and target schemes are affine; no additional hypotheses are present in the source statement.
  - Follow-on claims: none beyond the stated iff.
- Lean coverage: exact relative to the `FiniteType` bridge. `hX : IsAffine X` and `hY : IsAffine Y` cover the affine-scheme object class, `f : X ⟶ Y` makes the over-`Y` structure explicit, and `RingHom.FiniteType f.appTop.hom` is Mathlib’s representation of the finite-type algebra structure on global sections induced by `f`.
- Scope changes: representation change only, not a mathematical weakening or strengthening: the source’s implicit structure morphism is explicit in Lean, and the finite-type algebra condition is expressed as `RingHom.FiniteType` for `f.appTop.hom` rather than by an explicit `Algebra.FiniteType` instance.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text:

```text
The condition is evidently sufficient. Let us prove that it is necessary. Set \(A=\Gamma(Y,\mathcal O_Y)\), \(B=\Gamma(X,\mathcal O_X)\). Since \(X\) is of finite type over \(Y\), there exists an affine open covering \((V_\alpha)\) of \(Y\) such that each \(f^{-1}(V_\alpha)\) is a finite union of affine opens \(U_{\alpha i}\) with \(\Gamma(U_{\alpha i},\mathcal O_X)\) a finite type \(\Gamma(V_\alpha,\mathcal O_Y)\)-algebra.

We first show that every affine open subset \(W\subseteq Y\) has the same property (P). Indeed, let \(W\subseteq Y\) be affine. Since \(Y\) is affine, it is quasi-compact. Hence, \(W\) is quasi-compact as well. Therefore, \(W\) is covered by finitely many distinguished opens \(D(g_i)\subseteq V_{\alpha(i)}\), \( g_i\in \Gamma(V_{\alpha(i)},\mathcal O_Y)\), where each \(V_{\alpha(i)}\) belongs to the covering given by the definition. Fix one such distinguished open \(D(g)\subseteq V_\alpha\). By hypothesis, \(f^{-1}(V_\alpha)=\bigcup_j Z_j\) with \(Z_j\) affine and \(\Gamma(Z_j,\mathcal O_X)\) a finite type \(\Gamma(V_\alpha,\mathcal O_Y)\)-algebra. Let \(\varphi_j:\Gamma(V_\alpha,\mathcal O_Y)\to \Gamma(Z_j,\mathcal O_X)\) be the homomorphism induced by the restriction of \(f\) to \(Z_j\), and put \(g_j=\varphi_j(g)\). Then \(f^{-1}(D(g))\cap Z_j=D(g_j)\), and \(\Gamma(D(g_j),\mathcal O_X) = \Gamma(Z_j,\mathcal O_X)_{g_j} = \Gamma(Z_j,\mathcal O_X)[1/g_j]\). Hence, \(\Gamma(D(g_j),\mathcal O_X)\) is a finite type algebra over \(\Gamma(V_\alpha,\mathcal O_Y)[1/g] = \Gamma(D(g),\mathcal O_Y)\). Thus \(D(g)\) has the property (P). Since the \(D(g_i)\) form a finite affine cover of \(W\), it follows that \(W\) itself has the property \((P)\).

Applying this to the affine scheme \(Y\) itself, we obtain a finite affine open covering \(X=\bigcup_i V_i\) such that each \(\Gamma(V_i,\mathcal O_X)\) is an \(A\)-algebra of finite type. Moreover, since the \(V_i\) are quasi-compact, each \(V_i\) may be covered by finitely many opens of the form \(D(g_{ij})\subseteq V_i\), \(g_{ij}\in B\). If \(\varphi_i:B\to \Gamma(V_i,\mathcal O_X)\) is the homomorphism corresponding to the canonical inclusion \(V_i\hookrightarrow X\), then \(B_{g_{ij}} = \Gamma(V_i,\mathcal O_X)_{\varphi_i(g_{ij})} = \Gamma(V_i,\mathcal O_X)\bigl[1/\varphi_i(g_{ij})\bigr] \).
Thus \(B_{g_{ij}}\) is an \(A\)-algebra of finite type. We may therefore reduce to the case where \(V_i=D(g_i)\) with \(g_i\in B\), and each \(B_{g_i}\) is a finite type \(A\)-algebra.

By hypothesis, for each \(i\), there exist a finite subset \(F_i\subseteq B\) and an integer \(n_i\ge 0\) such that \(B_{g_i}\) is the \(A\)-algebra generated by the elements \(b/g_i^{n_i}\), \(b\in F_i\). Since the \(g_i\) are finite in number, we may moreover suppose that all the \(n_i\) are equal to one and the same integer \(n\). On the other hand, since the \(D(g_i)\) form a covering of \(X\), the ideal generated in \(B\) by the \(g_i\) is equal to \(B\). In other words, there exist \(h_i\in B\) such that \(\sum_i h_i g_i=1\). Let \(F\) be the finite subset of \(B\) obtained by taking the union of the \(F_i\), the set of the \(g_i\), and the set of the \(h_i\). We claim that the \(A\)-subalgebra \(B':=A[F]\) of \(B\) is equal to \(B\). Indeed, let \(b\in B\). For every \(i\), the canonical image of \(b\) in \(B_{g_i}\) is of the form \(b_i'/g_i^{m_i}\), \(b_i'\in B'\). Multiplying the \(b_i'\) by suitable powers of the \(g_i\), we may again suppose that all the \(m_i\) are equal to one and the same integer \(m\). By the definition of localization, there is therefore an integer \(N\) (depending on \(b\)) such that \(N\ge m\) and \(g_i^N b\in B'\), for all \(i\). Now, in the ring \(B'\), the elements \(g_i^N\) generate the unit ideal, since the \(g_i\) already do and the \(h_i\) belong to \(B'\). Hence, there exist \(c_i\in B'\) such that \(\sum_i c_i g_i^N=1\). It follows that \(b=\sum_i c_i g_i^N b\in B'\). Thus \(B=B'\), and therefore \(B\) is a finite type \(A\)-algebra.
```

- Prover notes: prove the forward direction by unfolding `FiniteType`, applying affine-local finite-type morphism API to `f` on the top affine open, and translating to `RingHom.FiniteType f.appTop`; the searched Mathlib facts `Scheme.Hom.finiteType_appLE`, `LocallyOfFiniteType.finiteType_of_affine_subset`, and `HasRingHomProperty.appTop` are likely useful. For the reverse direction, use the global-section finite-type hypothesis to obtain local finite type on affine opens; combine with affineness of `X` over affine `Y` to obtain quasi-compactness. If the exact iff is not already in Mathlib, follow the source localization argument: cover by principal opens `D(g_i)`, use finite generation after localization, common denominators, and the unit-ideal identity `∑ h_i g_i = 1` to descend finite generation from the localizations to `B`.

## Handoff Checklist

- [x] Source document inspected with deterministic tooling.
- [x] Companion instructions, skeletons, and preflight manifest read.
- [x] Local/Mathlib search performed before final statement selection.
- [x] Blueprint inventory contains entries for `line-17` and `line-30`.
- [x] Lean declarations drafted with stable required names.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [x] Proof-ready handoff accepted for the later prove workflow by formalization PASS and 2026-06-05 audit.
