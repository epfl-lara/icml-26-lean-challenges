import Mathlib.Combinatorics.Matroid.Minor.Delete
import Mathlib.Tactic.TautoSet

open Set

-- Common setup
variable {α : Type*} [DecidableEq α]

-- Definition 1: contraction
/-- Let M be a matroid on a ground set E, and let C ⊆ E.
The contraction of C from M, denoted M / C, is defined by M / C := (M* \ C)* -/
noncomputable def contract (M : Matroid α) (C : Set α) : Matroid α :=
  ((M.dual) \ C).dual

--Alias for intuitive notation
notation M " / " C => contract M C

-- Lemma 1: contract_ground
/-- For any matroid M and set C ⊆ E, E(M / C) = E(M) \ C -/
theorem contract_ground (M : Matroid α) (C : Set α) :
  (M / C).ground = M.ground \ C := by sorry

-- Lemma 2: dual_delete_dual
/-- For any matroid M and set X ⊆ E, (M / X)* = M* \ X, (M \ X)* = M* / X -/
theorem dual_delete_dual (M : Matroid α) (X : Set α) :
  (M / X).dual = M.dual \ X ∧ (M \ X).dual = M.dual / X := by sorry

-- Lemma 3: contract_contract
/-- For any matroid M and sets C₁, C₂ ⊆ E, M / C₁ / C₂ = M / (C₁ ∪ C₂).
In particular, M / C₁ / C₂ = M / C₂ / C₁ -/
theorem contract_contract (M : Matroid α) (C₁ C₂ : Set α) :
  (M / C₁) / C₂ = M / (C₁ ∪ C₂) := by sorry

-- Lemma 4: contract_empty
/-- For any matroid M, M / ∅ = M -/
theorem contract_empty (M : Matroid α) :
  M / ∅ = M := by sorry

-- Lemma 5: contract_eq_contract_iff
/-- For any matroid M and sets C₁, C₂ ⊆ E, M / C₁ = M / C₂ ↔ C₁ ∩ E(M) = C₂ ∩ E(M) -/
theorem contract_eq_contract_iff (M : Matroid α) (C₁ C₂ : Set α) :
  M / C₁ = M / C₂ ↔ C₁ ∩ M.ground = C₂ ∩ M.ground := by sorry

-- Lemma 6: coindep_contract_iff
/-- Let M be a matroid, C ⊆ E(M), and X ⊆ E(M).
Then X is coindependent in M / C ↔ X is coindependent in M and X ∩ C = ∅ -/
theorem coindep_contract_iff (M : Matroid α) (C X : Set α) :
  -- Assuming IsCocodract represents coindependence
  X.IsCocodract (M / C) ↔ X.IsCocodract M ∧ X ∩ C = ∅ := by sorry

-- Lemma 7: contract_isCocircuit_iff
/-- Let M be a matroid and C ⊆ E(M).
A set K is a cocircuit of M / C iff K is a cocircuit of M and K ∩ C = ∅ -/
theorem contract_isCocircuit_iff (M : Matroid α) (C K : Set α) :
  K.IsCocircuit (M / C) ↔ K.IsCocircuit M ∧ K ∩ C = ∅ := by sorry

-- Lemma 8: Indep.contract_isBase_iff
/-- Let M be a matroid and let I ⊆ E(M) be independent.
A set B is a basis of M / I iff B ∪ I is a basis of M and B ∩ I = ∅ -/
theorem Indep.contract_isBase_iff (M : Matroid α) (I B : Set α) (hI : I.IsIndependent M) :
  B.IsBasis (M / I) ↔ (B ∪ I).IsBasis M ∧ B ∩ I = ∅ := by sorry

-- Lemma 9: Indep.contract_indep_iff
/-- Let M be a matroid and let I ⊆ E(M) be independent.
For any set J ⊆ E(M), J is independent in M / I ↔ J ∩ I = ∅ and J ∪ I is independent in M -/
theorem Indep.contract_indep_iff (M : Matroid α) (I J : Set α) (hI : I.IsIndependent M) :
  J.IsIndependent (M / I) ↔ J ∩ I = ∅ ∧ (J ∪ I).IsIndependent M := by sorry

-- Lemma 10: IsNonloop.contractElem_indep_iff
/-- Let M be a matroid and let e be a non-loop element of M.
For any set I, I is independent in M / {e} ↔ e ∉ I and I ∪ {e} is independent in M -/
theorem IsNonloop.contractElem_indep_iff (M : Matroid α) (e : α) (he : ¬ M.IsLoop {e}) (I : Set α) :
  I.IsIndependent (M / {e}) ↔ e ∉ I ∧ (I ∪ {e}).IsIndependent M := by sorry

-- Lemma 11: IsBasis.contract_eq_contract_delete
/-- Let M be a matroid, X ⊆ E(M), and let I be a basis of X.
Then M / X = M / I \ (X \ I) -/
theorem IsBasis.contract_eq_contract_delete (M : Matroid α) (X I : Set α) (hI : I.IsBasis X) :
  M / X = (M / I) \ (X \ I) := by sorry
