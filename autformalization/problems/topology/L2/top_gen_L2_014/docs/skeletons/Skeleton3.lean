import Mathlib.Algebra.Homology.AlternatingConst
import Mathlib.AlgebraicTopology.SingularSet

open CategoryTheory Limits

-- Definition: singular chain complex functor
def singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace (C : Type*) [Preadditive C] 
    [HasCoproducts C] [HasHomology C] :
    C ⥤ (TopCat → ChainComplex C) := by sorry

-- Definition: singular homology functor  
def isZero_singularHomologyFunctor_of_totallyDisconnectedSpace (C : Type*) [Preadditive C] 
    [HasCoproducts C] [HasHomology C] :
    C ⥤ (TopCat → ChainComplex C) := by sorry

-- Theorem: homology of totally disconnected spaces
theorem singularHomologyFunctorZeroOfTotallyDisconnectedSpace (X : TopCat) (C : Type*) [Preadditive C] 
    (R : C) (hX : IsTotallyDisconnected X) :
    ∀ n : ℕ, 
      singularHomology X R n = 
      if n = 0 then 
        (Set.univ : Set X) ⨆ (fun _ => R) 
      else 
        0 := by sorry
