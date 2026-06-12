import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
# ShadowBench source formalization

This file formalizes the declarations requested by `docs/source.tex` for
`topology/L2/top_gen_L2_016`.  Proofs of theorem statements are intentionally
recorded for the later `/prove` workflow after independent statement/source
review.
-/

open CategoryTheory

universe v u

noncomputable section

/--
Source line-17 (`alternatingFaceMapComplex`).  For a preadditive category `C`,
the alternating face map complex is the functor from simplicial objects in `C`
to nonnegatively indexed chain complexes in `C`.  In degree `n` it has the
simplicial object component `X.obj (op ⦋n⦌)`, its differential is the standard
alternating sum of face maps, and on a simplicial morphism it acts degreewise.

Formalization note: Mathlib already implements exactly this functor as
`AlgebraicTopology.alternatingFaceMapComplex`.  The source display writes the
sign as `(-1)^n`, while the source proof and the standard construction use the
alternating sign `(-1)^i`; the Lean declaration follows the standard Mathlib
construction.
-/
def alternatingFaceMapComplex (C : Type u) [Category.{v} C] [Preadditive C] :
    SimplicialObject C ⥤ ChainComplex C ℕ :=
  AlgebraicTopology.alternatingFaceMapComplex C

/--
Source line-29 (`map_f`).  Source proof: on objects, the alternating differential
squares to zero by expanding `d_{n-1} ∘ d_n` as a double sum and cancelling terms
with the simplicial identity `d_i d_j = d_{j-1} d_i` for `i < j`; on morphisms,
naturality of the simplicial map makes the component maps commute with each face
map, hence with their alternating sum.

Prover notes: after statement/source review this should reduce to the Mathlib
construction.  Unfold `alternatingFaceMapComplex`; use
`AlgebraicTopology.alternatingFaceMapComplex_obj_X`,
`AlgebraicTopology.alternatingFaceMapComplex_obj_d`,
`AlgebraicTopology.AlternatingFaceMapComplex.d_squared`, and
`AlgebraicTopology.alternatingFaceMapComplex_map_f`.
-/
theorem map_f (C : Type u) [Category.{v} C] [Preadditive C] :
    (∀ (X : SimplicialObject C) (n : ℕ),
      ((alternatingFaceMapComplex C).obj X).X n =
        X.obj (Opposite.op (SimplexCategory.mk n))) ∧
    (∀ (X : SimplicialObject C) (n : ℕ),
      ((alternatingFaceMapComplex C).obj X).d (n + 1) n =
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • X.δ i) ∧
    (∀ (X : SimplicialObject C) (n : ℕ),
      AlgebraicTopology.AlternatingFaceMapComplex.objD X (n + 1) ≫
        AlgebraicTopology.AlternatingFaceMapComplex.objD X n = 0) ∧
    (∀ {X Y : SimplicialObject C} (f : X ⟶ Y) (n : ℕ),
      ((alternatingFaceMapComplex C).map f).f n =
        f.app (Opposite.op (SimplexCategory.mk n))) := by
  constructor
  · simp [alternatingFaceMapComplex]
  constructor
  · simp [alternatingFaceMapComplex]
  constructor
  · intro X n
    simpa using AlgebraicTopology.AlternatingFaceMapComplex.d_squared X n
  · simp [alternatingFaceMapComplex]

/--
Source line-44 (`inclusionOfMooreComplex`).  Source proof: for each simplicial
object `X` and degree `n`, include the normalized Moore object into the degree
`n` object of the alternating face map complex; compatibility with differentials
follows because the higher face maps vanish on the normalized Moore complex, and
naturality is componentwise naturality for simplicial morphisms.

Formalization note: the source display writes a union of kernels indexed
`0, ..., n`, but the named normalized Moore complex and the proof sentence
`N_n(X) ⊆ ker d_i` for `i = 1, ..., n` identify the standard intersection of
higher-face kernels.  Mathlib represents this by
`AlgebraicTopology.NormalizedMooreComplex.objX`.

Prover notes: the intended witness is Mathlib's
`AlgebraicTopology.inclusionOfMooreComplex A`.  The final conjunct records the
source's levelwise inclusion formula via
`AlgebraicTopology.NormalizedMooreComplex.objX`; use
`AlgebraicTopology.inclusionOfMooreComplexMap_f` or the definition of the
natural transformation after unfolding `alternatingFaceMapComplex`.
-/
theorem inclusionOfMooreComplex (A : Type u) [Category.{v} A] [Abelian A] :
    ∃ η : AlgebraicTopology.normalizedMooreComplex A ⟶ alternatingFaceMapComplex A,
      (∀ (X : SimplicialObject A) (n : ℕ), Mono ((η.app X).f n)) ∧
        η = AlgebraicTopology.inclusionOfMooreComplex A ∧
          ∀ (X : SimplicialObject A) (n : ℕ),
            (η.app X).f n = (AlgebraicTopology.NormalizedMooreComplex.objX X n).arrow := by
  refine ⟨AlgebraicTopology.inclusionOfMooreComplex A, ?_, rfl, ?_⟩
  · intro X n
    change Mono ((AlgebraicTopology.inclusionOfMooreComplexMap X).f n)
    rw [AlgebraicTopology.inclusionOfMooreComplexMap_f]
    exact CategoryTheory.Subobject.arrow_mono (AlgebraicTopology.NormalizedMooreComplex.objX X n)
  · intro X n
    exact AlgebraicTopology.inclusionOfMooreComplexMap_f X n
