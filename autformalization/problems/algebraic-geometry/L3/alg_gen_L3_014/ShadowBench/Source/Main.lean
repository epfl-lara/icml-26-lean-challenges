import Mathlib

/-!
# ShadowBench algebraic-geometry/L3/alg_gen_L3_014

Formalization of `docs/source.tex`.
-/

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

universe u

/--
Source theorem `line-17` (`docs/source.tex`, lines 17--22): for a morphism `f : X ⟶ Y`
and an open cover `(Uᵢ)` of `Y` whose members are quasi-separated, `f` is
quasi-separated iff each inverse-image open subset `f ⁻¹ᵁ Uᵢ` is quasi-separated.

Source proof: identify the inverse image of `Uᵢ` in `X ×[Y] X` with
`Xᵢ ×[Uᵢ] Xᵢ`, where `Xᵢ = f ⁻¹(Uᵢ)`, and identify the restricted diagonal with
`Δ_{fᵢ}`. Then use target-locality of quasi-compactness for the diagonal. Since
`Uᵢ → Spec ℤ` is quasi-separated by hypothesis, `fᵢ` is quasi-separated exactly
when the composite `Xᵢ → Uᵢ → Spec ℤ` is, i.e. when the open subscheme `Xᵢ` is
quasi-separated.

Prover notes: use `AlgebraicGeometry.QuasiSeparated` for morphisms,
`IsQuasiSeparated` for the underlying open subsets, `f ⁻¹ᵁ U` for open preimage,
and the source proof's bridge through `quasiSeparated_iff_quasiSeparatedSpace`,
restriction/base-change of `QuasiSeparated`, and target-locality of
`QuasiCompact`/`QuasiSeparated` available from affine-property infrastructure.
-/
theorem quasiSeparated_iff_preimage_isQuasiSeparated_of_openCover
    {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type*} (U : ι → Y.Opens)
    (hUcover : IsOpenCover U) (hUqs : ∀ i, IsQuasiSeparated (U i : Set Y)) :
    QuasiSeparated f ↔ ∀ i, IsQuasiSeparated (f ⁻¹ᵁ U i : Set X) := by
  constructor
  · intro hf i
    letI : QuasiSeparated f := hf
    exact f.isQuasiSeparated_preimage (hUqs i)
  · intro hpre
    exact IsZariskiLocalAtTarget.of_iSup_eq_top
      (P := @QuasiSeparated) (f := f) U hUcover fun i => by
      haveI : QuasiSeparatedSpace (U i) :=
        (isQuasiSeparated_iff_quasiSeparatedSpace (U i : Set Y) (U i).2).mp (hUqs i)
      haveI : QuasiSeparatedSpace (f ⁻¹ᵁ U i) :=
        (isQuasiSeparated_iff_quasiSeparatedSpace (f ⁻¹ᵁ U i : Set X) (f ⁻¹ᵁ U i).2).mp (hpre i)
      exact (quasiSeparated_iff_quasiSeparatedSpace (f ∣_ U i)).mpr inferInstance

end AlgebraicGeometry

export AlgebraicGeometry (quasiSeparated_iff_preimage_isQuasiSeparated_of_openCover)
