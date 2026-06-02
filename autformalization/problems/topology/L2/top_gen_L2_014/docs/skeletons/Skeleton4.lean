import Mathlib.Algebra.Homology.AlternatingConst
import Mathlib.AlgebraicTopology.SingularSet

open CategoryTheory Limits

def singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace (C : Type*)
    [Category C] [Preadditive C] [HasCoproducts C] [HasHomology C] :
    C ⥤ TopCat ⥤ ChainComplex C ℕ :=
  sorry

def isZero_singularHomologyFunctor_of_totallyDisconnectedSpace (C : Type*)
    [Category C] [Preadditive C] [HasCoproducts C] [HasHomology C] :
    C ⥤ TopCat ⥤ ChainComplex C ℕ :=
  sorry

theorem singularHomologyFunctorZeroOfTotallyDisconnectedSpace (X : TopCat)
    [TotallyDisconnectedSpace X] (C : Type*) [Category C] [Preadditive C]
    [HasCoproducts C] [HasHomology C] (R : C) (n : ℕ) :
    ((singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace.obj R).obj X).homology n =
      if n = 0 then ∐ fun (_ : X) => R else 0 := by
  sorry
