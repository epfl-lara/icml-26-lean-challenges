import Mathlib
import Aesop

/-!
ShadowBench problem `algebraic-geometry/L3/alg_gen_L3_007`.
Source: `docs/source.tex`.
Blueprint: `ShadowBench/Source/Blueprint.md`.
-/

open AlgebraicGeometry
open Topology

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
    {X Y : Scheme} (f : X ⟶ Y) (hf : QuasiCompact f) :
    IsDominant f ↔
      ∀ y : Y, y ∈ genericPoints Y → ∃ x : X, x ∈ genericPoints X ∧ f x = y := by
  sorry
