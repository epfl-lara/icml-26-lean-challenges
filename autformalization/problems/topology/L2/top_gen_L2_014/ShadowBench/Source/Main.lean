import Mathlib.AlgebraicTopology.SingularHomology.Basic

open CategoryTheory Limits

noncomputable section

universe w v u

/--
Source `docs/source.tex`, line-17. The source defines the singular chain complex
functor from coefficients in a preadditive category with coproducts and homology
to functors from topological spaces to nonnegative chain complexes; in degree
`n` it is the coproduct over singular `n`-simplices with alternating face-map
differential. This is a source-named alias for Mathlib's singular chain complex
functor.
-/
def singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace
    (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
    [CategoryWithHomology C] :
    C ⥤ TopCat.{w} ⥤ ChainComplex C ℕ :=
  AlgebraicTopology.singularChainComplexFunctor C

/--
Source `docs/source.tex`, line-28. The source defines singular homology by
`H_n(X; R)`, the `n`-th homology object of the singular chain complex
`C_•(X; R)`. Mathlib represents the graded functor as a degree-indexed family of
fixed-degree functors; this source-named alias is that family.
-/
def isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
    [CategoryWithHomology C] :
    ℕ → C ⥤ TopCat.{w} ⥤ C :=
  fun n => AlgebraicTopology.singularHomologyFunctor C n

/--
Source `docs/source.tex`, line-36.
Source proof: the image of a singular simplex is connected, hence a singleton in
a totally disconnected space, so the singular simplicial set is identified
degreewise with the points of `X`; the face maps become identities, and the
singular chain complex is the alternating complex
`R[X] ←0- R[X] ←id- R[X] ←0- ⋯`.
Proof sketch: split the two degree cases. In degree zero, use
`AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace`. In
positive degree, convert `0 < n` to `n ≠ 0` and use
`AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`.
Prover notes: the source writes object equality; the Lean statement uses the
standard categorical formulation, an isomorphism in degree zero and `IsZero` in
positive degree.
-/
theorem singularHomologyFunctorZeroOfTotallyDisconnectedSpace
    (X : TopCat.{w}) [TotallyDisconnectedSpace X]
    (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
    [CategoryWithHomology C] (R : C) (n : ℕ) :
    (n = 0 →
      Nonempty (((isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C n).obj R).obj X ≅
        ∐ fun _ : X ↦ R)) ∧
    (0 < n →
      IsZero (((isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C n).obj R).obj X)) := by
  constructor
  · intro hn
    subst n
    exact ⟨AlgebraicTopology.singularHomologyFunctorZeroOfTotallyDisconnectedSpace C R X⟩
  · intro hpos
    exact
      AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C n R X
        (Nat.ne_of_gt hpos)
