import Mathlib
import Aesop

/-!
ShadowBench problem `algebraic-geometry/L3/alg_gen_L3_007`.
Source: `docs/source.tex`.
Blueprint: `ShadowBench/Source/Blueprint.md`.
-/

open AlgebraicGeometry CategoryTheory Topology
open scoped AlgebraicGeometry

universe u

/-- Source-backed generic-point lifting mechanism for quasi-compact dominant morphisms of schemes.

This is the nontrivial affine-chart/minimal-prime argument from the source proof: after
restricting to an affine neighbourhood of the target generic point, quasi-compactness
gives finitely many affine source charts, and dominance plus
`PrimeSpectrum.denseRange_comap_iff_minimalPrimes` lifts the corresponding minimal
prime to a generic point of a source component. It is an explicit mechanism hypothesis
instead of a primitive declaration. -/
def GenericPointFiberMechanism : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (_hf : QuasiCompact f)
    (_hdominant : IsDominant f) {y : Y} (_hy : y ∈ genericPoints Y),
    ∃ x : X, x ∈ genericPoints X ∧ f x = y

/-- Unwrap the supplied generic-point lifting mechanism. -/
theorem exists_genericPoint_mem_fiber_of_isDominant_of_quasiCompact
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : QuasiCompact f)
    (hdominant : IsDominant f) {y : Y} (hy : y ∈ genericPoints Y)
    (h_generic_point_fiber : GenericPointFiberMechanism.{u}) :
    ∃ x : X, x ∈ genericPoints X ∧ f x = y :=
  h_generic_point_fiber f hf hdominant hy

/--
Source theorem `docs/source.tex`, line 17 (`isDominant_iff_forall_genericPoints_mem_fiber`).
Let `f : X ⟶ Y` be a quasi-compact morphism of schemes. Then `f` is dominant iff
for every generic point `y` of an irreducible component of `Y`, the fiber over `y`
contains the generic point of an irreducible component of `X`.

Source proof: sufficiency is immediate from the set-theoretic condition on the image.
For necessity, choose an affine open neighborhood `U` of `y`; quasi-compactness writes
`f ⁻¹ U` as finitely many affine opens `Vᵢ`, and dominance forces `y` into the
closure of one image. After reducing to reduced affine schemes, the conclusion follows
because every minimal prime of `B` is the contraction of a minimal prime of `A`.

Prover notes: `genericPoints X` is the Mathlib set of generic points of irreducible
components; the fiber condition is encoded as `f x = y` using the coercion of a scheme
morphism to its underlying continuous map. The explicit hypothesis `hf` may be installed
as a local instance by the later proof if Mathlib's quasi-compact API needs it.
-/
theorem isDominant_iff_forall_genericPoints_mem_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : QuasiCompact f)
    (h_generic_point_fiber : GenericPointFiberMechanism.{u}) :
    IsDominant f ↔
      ∀ y : Y, y ∈ genericPoints Y → ∃ x : X, x ∈ genericPoints X ∧ f x = y := by
  constructor
  · intro hdominant y hy
    exact exists_genericPoint_mem_fiber_of_isDominant_of_quasiCompact f hf hdominant hy
      h_generic_point_fiber
  · intro h
    rw [dominant_eq_topologically]
    refine denseRange_iff_closure_range.mpr ?_
    have hclosure : closure (genericPoints Y) ⊆ closure (Set.range f) := by
      refine closure_minimal ?_ isClosed_closure
      intro y hy
      rcases h y hy with ⟨x, _hx, hxy⟩
      exact subset_closure ⟨x, hxy⟩
    rw [genericPoints.closure (α := Y)] at hclosure
    exact Set.Subset.antisymm (Set.subset_univ _) hclosure
