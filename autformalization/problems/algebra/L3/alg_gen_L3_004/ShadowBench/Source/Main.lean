import Mathlib.Combinatorics.Matroid.Minor.Contract
import Mathlib.Tactic.TautoSet

open scoped Matroid
open Set

/-- Source `line-17` (`contract`): contraction of `C` from `M` is defined by dual deletion,
`M / C := (M^* \ C)^*`.
Prover notes: this wrapper is the source name around Mathlib's definition; unfold `contract`
or rewrite to `Matroid.contract`/notation `M ／ C` when using Mathlib lemmas. -/
def contract {α : Type*} (M : Matroid α) (C : Set α) : Matroid α := (M✶ ＼ C)✶

/-- Source `line-25` (`contract_ground`): the ground set of the contraction is the original
ground set minus the contracted set.
Source proof: unfold contraction as dual deletion, then use the ground-set facts for deletion
and duality. Prover notes: rewrite the wrapper to Mathlib contraction and use
`Matroid.contract_ground`. -/
theorem contract_ground {α : Type*} (M : Matroid α) (C : Set α) (hC : C ⊆ M.E) :
    (contract M C).E = M.E \ C := by
  sorry

/-- Source `line-38` (`dual_contract`): duality swaps contraction and deletion.
Source proof: both identities follow from `M / X := (M^* \ X)^*` and involutivity of duality.
Prover notes: use `Matroid.dual_contract` for the first conjunct and `Matroid.dual_delete` for
the second, after unfolding `contract`. -/
theorem dual_contract {α : Type*} (M : Matroid α) (X : Set α) (hX : X ⊆ M.E) :
    (contract M X)✶ = M✶ ＼ X ∧ (M ＼ X)✶ = contract M✶ X := by
  sorry

/-- Source `line-52` (`Coindep.coindep_contract_of_disjoint`): iterated contraction combines
by union, and hence contractions commute.
Source proof: via duality, iterated contraction is iterated deletion in the dual; deletion over
unions gives the first equality and union commutativity gives the second. Prover notes: use
`Matroid.contract_contract` and `Matroid.contract_comm` after unfolding `contract`. -/
theorem Coindep.coindep_contract_of_disjoint {α : Type*} (M : Matroid α) (C₁ C₂ : Set α)
    (hC₁ : C₁ ⊆ M.E) (hC₂ : C₂ ⊆ M.E) :
    contract (contract M C₁) C₂ = contract M (C₁ ∪ C₂) ∧
      contract (contract M C₁) C₂ = contract (contract M C₂) C₁ := by
  sorry

/-- Source `line-70` (`contract_empty`): contracting the empty set leaves the matroid unchanged.
Source proof: unfold contraction and use that deleting `∅` has no effect, then dual involutivity.
Prover notes: Mathlib has `Matroid.contract_empty`. -/
theorem contract_empty {α : Type*} (M : Matroid α) :
    contract M ∅ = M := by
  sorry

/-- Source `line-82` (`contract_eq_contract_iff`): two contractions are equal exactly when the
contracted sets have the same intersection with the ground set.
Source proof: translate to the corresponding equality criterion for deletions in the dual.
Prover notes: use `Matroid.contract_eq_contract_iff` after unfolding `contract`. -/
theorem contract_eq_contract_iff {α : Type*} (M : Matroid α) (C₁ C₂ : Set α)
    (hC₁ : C₁ ⊆ M.E) (hC₂ : C₂ ⊆ M.E) :
    contract M C₁ = contract M C₂ ↔ C₁ ∩ M.E = C₂ ∩ M.E := by
  sorry

/-- Source `line-96` (`coindep_contract_iff`): a set is coindependent after contracting `C`
iff it was coindependent before and is disjoint from `C`.
Source proof: rewrite coindependence as independence in the dual and apply the deletion
characterization. Prover notes: Mathlib states this with `Disjoint`; convert to
`X ∩ C = ∅`. -/
theorem coindep_contract_iff {α : Type*} (M : Matroid α) (C X : Set α)
    (hC : C ⊆ M.E) (hX : X ⊆ M.E) :
    (contract M C).Coindep X ↔ M.Coindep X ∧ X ∩ C = ∅ := by
  sorry

/-- Source `line-111` (`contract_isCocircuit_iff`): cocircuits of a contraction are exactly the
old cocircuits disjoint from the contracted set.
Source proof: immediate from the coindependence characterization and the definition of
cocircuits. Prover notes: use `Matroid.contract_isCocircuit_iff` and convert `Disjoint` to
empty intersection. -/
theorem contract_isCocircuit_iff {α : Type*} (M : Matroid α) (C K : Set α)
    (hC : C ⊆ M.E) :
    (contract M C).IsCocircuit K ↔ M.IsCocircuit K ∧ K ∩ C = ∅ := by
  sorry

/-- Source `line-122` (`Indep.contract_isBase_iff`): if `I` is independent, then bases of
`M / I` are exactly the sets `B` for which `B ∪ I` is a basis of `M` and `B ∩ I = ∅`.
Source proof: reduce by duality to the deletion characterization of bases. Prover notes:
use `Matroid.Indep.contract_isBase_iff`, converting `Disjoint B I` to `B ∩ I = ∅`. -/
theorem Indep.contract_isBase_iff {α : Type*} (M : Matroid α) (I B : Set α)
    (hI : M.Indep I) :
    (contract M I).IsBase B ↔ M.IsBase (B ∪ I) ∧ B ∩ I = ∅ := by
  sorry

/-- Source `line-138` (`Indep.contract_indep_iff`): for independent `I`, independence in
`M / I` is equivalent to being disjoint from `I` and having `J ∪ I` independent in `M`.
Source proof: characterize independence by containment in a basis and apply the previous basis
lemma. Prover notes: Mathlib has `Matroid.Indep.contract_indep_iff`, stated with `Disjoint`. -/
theorem Indep.contract_indep_iff {α : Type*} (M : Matroid α) (I J : Set α)
    (hI : M.Indep I) (hJ : J ⊆ M.E) :
    (contract M I).Indep J ↔ J ∩ I = ∅ ∧ M.Indep (J ∪ I) := by
  sorry

/-- Source `line-155` (`IsNonloop.contractElem_indep_iff`): contracting a non-loop element `e`
makes `I` independent exactly when `e ∉ I` and adjoining `e` to `I` was independent in `M`.
Source proof: specialize the previous contraction-independence lemma to `{e}`, using that a
non-loop singleton is independent. Prover notes: Mathlib uses `insert e I`; convert to
`I ∪ {e}` by `simp`/set extensionality. -/
theorem IsNonloop.contractElem_indep_iff {α : Type*} (M : Matroid α) (e : α) (I : Set α)
    (he : M.IsNonloop e) :
    (contract M {e}).Indep I ↔ e ∉ I ∧ M.Indep (I ∪ {e}) := by
  sorry

/-- Source `line-172` (`IsBasis.contract_eq_contract_delete`): contracting a set is equivalent
to contracting a basis for it and deleting the remaining elements.
Source proof: decompose `X` into the basis `I` and `X \ I`; contracting `X` equals contracting
`I` and deleting the rest. Prover notes: use `Matroid.IsBasis.contract_eq_contract_delete` after
unfolding the wrapper `contract`. -/
theorem IsBasis.contract_eq_contract_delete {α : Type*} (M : Matroid α) (X I : Set α)
    (hX : X ⊆ M.E) (hI : M.IsBasis I X) :
    contract M X = (contract M I) ＼ (X \ I) := by
  sorry
