import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.RingTheory.Etale.QuasiFinite
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

open CategoryTheory Limits
open AlgebraicGeometry

universe u

/--
Source theorem `docs/source.tex`, line 17: for a finite-type separated morphism `f : X ⟶ Y`,
let `f.normalization` be the relative normalization of `Y` in `X`, with canonical factorization
`X ⟶ f.normalization ⟶ Y`. There is an open subscheme `U` of the normalization such that the
restricted morphism from its preimage is an isomorphism and that preimage is exactly the
quasi-finite locus of `f`.

Source proof: the quasi-finite locus `U₀ ⊆ X` is open. Around each quasi-finite point `x`, after
an elementary étale neighbourhood of `f x`, split `X` into an open-and-closed finite part containing
`x` and its complement; the normalization then splits as the finite part together with the
normalization of the complement, giving a local open `V` on which the restriction is an isomorphism.
These local opens descend along the étale cover and are glued over all quasi-finite points.

Prover notes: this is the Zariski main theorem statement in Mathlib's
`Mathlib.AlgebraicGeometry.ZariskisMainTheorem`; this file re-exports that theorem under the
required top-level `Scheme.Hom` namespace.
-/
lemma Scheme.Hom.exists_isIso_morphismRestrict_toNormalization
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f] :
    ∃ U : f.normalization.Opens, IsIso (f.toNormalization ∣_ U) ∧
      (f.toNormalization ⁻¹ᵁ U).1 = { x | f.QuasiFiniteAt x } := by
  exact AlgebraicGeometry.Scheme.Hom.exists_isIso_morphismRestrict_toNormalization f
