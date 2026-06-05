# Formalization Blueprint: `algebraic-geometry/L3/alg_gen_L3_013`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains all generated declarations for this source document.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main` so the source module is covered by the project root.
- `ShadowBench.lean`: imports `ShadowBench.Source` so a plain project build reaches the generated target.

No split into additional Lean files is planned for this short source document.

## Import Plan

```lean
import Mathlib
```

## Suggested Search Modules

These are non-gating search hints for future proof work; they are not additional direct imports in the generated Lean file unless a proof pass later needs them.

- `Mathlib.AlgebraicGeometry.Scheme`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.ResidueField`
- `Mathlib.RingTheory.LocalRing.ResidueField.Basic`
- `Mathlib.LinearAlgebra.FiniteDimensional.Defs`

## Required Names

- `IsQuasiFiniteModule`
- `isolated_in_fiber_iff_stalk_quasiFinite`

## Candidate Skeletons Reviewed

- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` propose the expected names and the high-level shape but use non-Mathlib identifiers such as `Scheme X`, `SchemeHom`, `Morphism.LocallyOfFiniteType`, `stalk`, `structureSheaf`, and `IsIsolatedPtInFiber`.
- `docs/skeletons/Skeleton4.lean` additionally has malformed Lean syntax after the theorem.
- Final draft adopts the required names and source intent, but replaces the skeleton-specific identifiers by Mathlib's `AlgebraicGeometry.Scheme`, categorical morphisms `X ⟶ Y`, `AlgebraicGeometry.LocallyOfFiniteType`, `X.presheaf.stalk x`, and explicit helper definitions for the two informal predicates.

## Source Statement Inventory

### line-17

- Source kind/title: Definition `IsQuasiFiniteModule`

- Planned Lean declarations: `IsQuasiFiniteModule`
- Source locator: `docs/source.tex`, lines 17--18.
- Source statement: Given a local ring `A` with maximal ideal `𝔪`, an `A`-module `M` is quasi-finite over `A` iff `M / 𝔪 M` has finite rank over the residue field `k = A / 𝔪`.
- Skeleton candidate used: skeletons 1--3 for the required name and parameter intent; the definition body was redrafted to be an implemented Mathlib expression rather than a construction stub.
- Dependencies: `CommRing A`, `IsLocalRing A`, `AddCommGroup M`, `Module A M`, `IsLocalRing.ResidueField A`, tensor product notation, and `FiniteDimensional`.
- Lean declaration shape:
  ```lean
  def IsQuasiFiniteModule (A : Type*) [CommRing A] [IsLocalRing A]
      (M : Type*) [AddCommGroup M] [Module A M] : Prop :=
    FiniteDimensional (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A ⊗[A] M)
  ```
- Formal statement review: the source quotient `M / 𝔪 M` is represented by the standard special-fiber tensor product `κ(A) ⊗[A] M`, where `κ(A) = IsLocalRing.ResidueField A`. The predicate asks that this vector space over the residue field be finite-dimensional, matching finite rank over `k`.
- Source qualifiers:
  - Mathematical object class: local commutative ring `A`; `A`-module `M`.
  - Quantifier/order: first the local ring, then the module over it.
  - Parameter domain: Lean uses arbitrary universe `Type*` for both `A` and `M`, with typeclass assumptions spelling out the algebraic structure.
  - Output codomain: `Prop`.
  - Equality/image condition: quotient by the maximal ideal action is encoded as `κ(A) ⊗[A] M`.
  - Side conditions: `A` is local; `M` is an additive commutative group with `A`-module structure.
  - Follow-on claims: none in the definition.
- Lean coverage: full mathematical coverage of the definition, with the quotient represented by a canonical tensor-product bridge.
- Scope changes: representation bridge from `M / 𝔪 M` to `κ(A) ⊗[A] M`; no weakening of finite-dimensionality/finite-rank content.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: definition only; no proof obligation. Future theorem proofs should unfold this predicate to the finite-dimensionality of the special fiber.

### line-19

- Source kind/title: Theorem `isolated_in_fiber_iff_stalk_quasiFinite`
- Planned Lean declarations: `IsIsolatedInFiber`, `StalkQuasiFiniteOverBase`, `isolated_in_fiber_iff_stalk_quasiFinite`
- Source locator: `docs/source.tex`, theorem lines 19--25; proof lines 25--33.
- Source statement: for a morphism `f : X → Y` locally of finite type and a point `x` of `X`, condition (a) `x` is isolated in its fiber `f⁻¹(f(x))` is equivalent to condition (b) the local ring `𝒪_x` is a quasi-finite `𝒪_{f(x)}`-module.
- Complete source proof text:
  > The question being evidently local on `X` and on `Y`, one may suppose `X = Spec(A)` and `Y = Spec(B)` affine, `A` being a `B`-algebra of finite type. Moreover, one may replace `X` by `X ×_Y Spec(𝒪_{f(x)})` without changing the fiber `f^{-1}(f(x))` nor the local ring `𝒪_x`; thus one may suppose that `B` is a local ring, equal to `𝒪_{f(x)}`.
  >
  > If `𝔫` is the maximal ideal of `B`, then `f^{-1}(f(x))` is an affine scheme with ring `A / 𝔫 A`, of finite type over `k(f(x)) = B / 𝔫`. This being so, if `(a)` holds, one may moreover suppose that `f^{-1}(f(x))` is reduced to the point `x`; hence `A / 𝔫 A` is of finite rank over `B / 𝔫`, in other words `A` is a quasi-finite `B`-module.
  >
  > Conversely, if `(b)` holds, `f^{-1}(f(x))` is an affine Artinian scheme, hence discrete; consequently `x` is isolated in its fiber `f^{-1}(f(x))`.
- Skeleton candidate used: skeletons 1--3 for the expected theorem name and high-level equivalence; redrafted to valid Mathlib scheme and stalk syntax. Skeleton4 not used because it is syntactically malformed.
- Dependencies: `AlgebraicGeometry.Scheme`, categorical morphisms `X ⟶ Y`, `AlgebraicGeometry.LocallyOfFiniteType f`, helper definitions `IsIsolatedInFiber`, `StalkQuasiFiniteOverBase`, and `IsQuasiFiniteModule`.

#### Helper definition `IsIsolatedInFiber`

- Planned Lean declaration: `IsIsolatedInFiber`
- Source role: companion declaration used to make condition (a) of `line-19` explicit.
- Lean declaration shape:
  ```lean
  def IsIsolatedInFiber {X Y : Scheme} (f : X ⟶ Y) (x : X) : Prop :=
    IsOpen ({⟨x, rfl⟩} : Set {x' : X // f x' = f x})
  ```
- Coverage note: this says that the singleton of `x` is open in the subspace topology on the set-theoretic fiber over `f x`, which is the standard topological meaning of being isolated in that fiber.
- Scope changes: none; this is an explicit representation of source condition (a).

#### Helper definition `StalkQuasiFiniteOverBase`

- Planned Lean declaration: `StalkQuasiFiniteOverBase`
- Source role: companion declaration used to make condition (b) of `line-19` explicit.
- Lean declaration shape:
  ```lean
  def StalkQuasiFiniteOverBase {X Y : Scheme} (f : X ⟶ Y) (x : X) : Prop :=
    letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
    IsQuasiFiniteModule (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
  ```
- Coverage note: this equips `𝒪_{X,x}` with its `𝒪_{Y,f(x)}`-module structure via the stalk map induced by the scheme morphism `f`, then applies `IsQuasiFiniteModule`.
- Scope changes: none; this records the module-structure bridge implicit in the source phrase “as a quasi-finite `𝒪_{f(x)}`-module”.

- Lean declaration shape:
  ```lean
  theorem isolated_in_fiber_iff_stalk_quasiFinite {X Y : Scheme} (f : X ⟶ Y)
      [LocallyOfFiniteType f] (x : X) :
      IsIsolatedInFiber f x ↔ StalkQuasiFiniteOverBase f x := by
    sorry
  ```
- Formal statement review: the Lean statement preserves the source quantifier order up to the use of a typeclass for the “locally of finite type” hypothesis: schemes `X Y`, morphism `f`, local finite type hypothesis, then point `x`. The left side is an explicit subspace-topology isolated-point predicate on the fiber over `f x`; the right side is the source stalk-module quasi-finiteness via `f.stalkMap x`.
- Source qualifiers:
  - Mathematical object class: schemes `X` and `Y`; a morphism of schemes `f : X ⟶ Y`; a point `x : X`; local rings/stalks at `x` and `f x`.
  - Quantifier/order: morphism locally of finite type, then point of the source scheme.
  - Parameter domain: Mathlib scheme objects and categorical morphisms.
  - Output codomain: equivalence of propositions.
  - Equality/image condition: fiber is over the exact image point `f x`; stalk module is over `Y.presheaf.stalk (f x)` and target module is `X.presheaf.stalk x`.
  - Side conditions: `LocallyOfFiniteType f` is required.
  - Follow-on claims: both implications of the equivalence.
- Lean coverage: full source-statement coverage through the two companion definitions. The proof is intentionally a `sorry` skeleton for the later `/prove` workflow.
- Scope changes: no intentional weakening or strengthening. Representation bridges are explicit: isolated-in-fiber is singleton openness in the subspace fiber, and stalk module structure is supplied by `f.stalkMap x`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: prove locally on source and target; reduce to an affine finite-type morphism `Spec A → Spec B`; base-change to `Spec 𝒪_{f(x)}` so `B` is local; identify the fiber ring with `A / 𝔫 A`; for the isolated direction shrink/localize so the fiber is the single point and conclude finite-dimensionality over `B / 𝔫`; for the converse use quasi-finiteness to show the fiber is affine Artinian and therefore discrete.

## Handoff Checklist

- [x] Source document inspected with theorem-like blocks recorded.
- [x] Candidate skeletons read and compared against the source.
- [x] Blueprint source inventory contains entries for `line-17` and `line-19`.
- [x] Direct import plan contains only imports used by `ShadowBench/Source/Main.lean`.
- [x] Root project module path imports the generated target through `ShadowBench.lean` and `ShadowBench/Source.lean`.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [ ] Proof handoff to `/prove` authorized by the review gate.
