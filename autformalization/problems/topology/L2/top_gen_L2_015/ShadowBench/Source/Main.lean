import Mathlib.AlgebraicTopology.MooreComplex

noncomputable section

open CategoryTheory

universe v u

/--
Source definition (`docs/source.tex`, lines 17--30): for an abelian category `C`, the
normalized Moore complex is the functor from simplicial objects in `C` to non-negative
chain complexes in `C`. Its degree-zero object is `X₀`; in positive degree it is the
intersection of the kernels of the positive face maps; the differential is induced by
the zero-th face map; and morphisms are restricted degreewise.

Lean encoding: Mathlib's `AlgebraicTopology.normalizedMooreComplex` implements exactly
this construction using `Subobject` infima and `ChainComplex C ℕ`.
-/
def normalizedMooreComplex (C : Type u) [Category.{v} C] [Abelian C] :
    SimplicialObject C ⥤ ChainComplex C ℕ :=
  AlgebraicTopology.normalizedMooreComplex C

/--
Source theorem (`docs/source.tex`, lines 31--51): `N_•` is a well-defined functor.

Source proof: the zero-th face map carries each normalized intersection of kernels into
the previous one because the simplicial identity rewrites `dᵢ d₀` as `d₀ dᵢ₊₁`, which
vanishes on `Nₙ(X)`. The same identity with `d₁` gives `d ∘ d = 0`. For a simplicial
morphism, naturality with every positive face map shows each component restricts to a
map between normalized subobjects, giving the functor on morphisms.

Prover notes: the Lean statement records this well-definedness as the identification of
the source-named construction with Mathlib's certified functor. Unfold
`normalizedMooreComplex`; Mathlib's implementation supplies the object, differential,
`d_squared`, morphism factorization, and functor laws. After statement review this proof
should be definitional.
-/
theorem normalizedMooreComplex_objD (C : Type u) [Category.{v} C] [Abelian C] :
    normalizedMooreComplex C = AlgebraicTopology.normalizedMooreComplex C := by
  sorry
