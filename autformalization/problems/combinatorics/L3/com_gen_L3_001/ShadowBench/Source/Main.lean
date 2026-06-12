import Mathlib.Combinatorics.Matroid.Minor.Contract

/-!
Source-mapped formalization draft for `docs/source.tex`.

This file intentionally contains theorem and lemma skeletons with `sorry` proofs.
The formalization pass records source-faithful statements and proof notes; a later
prove workflow should discharge the proof obligations after statement/source review.
-/

universe u

/--
Source definition (docs/source.tex lines 17-23): contraction is defined as the dual
of deletion in the dual matroid, `M / C := (M^* \setminus C)^*`.
Prover notes: this is a source-name wrapper around Mathlib's `Matroid.contract`;
it is a construction bridge and has no proof obligation.
-/
def contract {α : Type u} (M : Matroid α) (C : Set α) : Matroid α :=
  Matroid.contract M C

/--
Source proof (docs/source.tex lines 25-36): unfold contraction as dual-delete-dual
and use the ground-set facts for deletion and duality.
Prover notes: Mathlib search found `Matroid.contract_ground`; the hypothesis
`C ⊆ M.E` records the source domain even if the Mathlib lemma is stronger.
-/
theorem contract_ground {α : Type u} (M : Matroid α) (C : Set α) (hC : C ⊆ M.E) :
    (Matroid.contract M C).E = M.E \ C := by
  exact (fun _hC : C ⊆ M.E => Matroid.contract_ground M C) hC

/--
Source proof (docs/source.tex lines 38-50): both equalities follow directly from
`M / X := (M^* \setminus X)^*` and involutivity of duality.
Prover notes: use `Matroid.dual_contract` and `Matroid.dual_delete` or the
corresponding dual-delete-dual simp lemmas.
-/
theorem dual_delete_dual {α : Type u} (M : Matroid α) (X : Set α) (hX : X ⊆ M.E) :
    Matroid.dual (Matroid.contract M X) = Matroid.delete (Matroid.dual M) X ∧
      Matroid.dual (Matroid.delete M X) = Matroid.contract (Matroid.dual M) X := by
  exact (fun _hX : X ⊆ M.E => ⟨Matroid.dual_contract M X, Matroid.dual_delete M X⟩) hX

/--
Source proof (docs/source.tex lines 52-68): iterated contraction corresponds to
iterated deletion in the dual; deletion combines over union, and the `in particular`
claim follows from commutativity of union.
Prover notes: Mathlib search found `Matroid.contract_contract` and
`Matroid.contract_comm`.
-/
theorem contract_contract {α : Type u} (M : Matroid α) (C₁ C₂ : Set α)
    (hC₁ : C₁ ⊆ M.E) (hC₂ : C₂ ⊆ M.E) :
    Matroid.contract (Matroid.contract M C₁) C₂ = Matroid.contract M (C₁ ∪ C₂) ∧
      Matroid.contract (Matroid.contract M C₁) C₂ =
        Matroid.contract (Matroid.contract M C₂) C₁ := by
  exact (fun _hC₁ : C₁ ⊆ M.E => fun _hC₂ : C₂ ⊆ M.E =>
    ⟨Matroid.contract_contract M C₁ C₂, Matroid.contract_comm M C₁ C₂⟩) hC₁ hC₂

/--
Source proof (docs/source.tex lines 70-80): contraction by the empty set unfolds to
deletion of the empty set in the dual, which is the identity.
Prover notes: look for a simp lemma or Mathlib theorem for empty contraction.
-/
theorem contract_empty {α : Type u} (M : Matroid α) :
    Matroid.contract M ∅ = M := by
  exact Matroid.contract_empty M

/--
Source proof (docs/source.tex lines 82-94): use the dual characterization of
contraction and reduce to the deletion equality criterion in the dual matroid.
Prover notes: Mathlib search found `Matroid.contract_eq_contract_iff`.
-/
theorem contract_eq_contract_iff {α : Type u} (M : Matroid α) (C₁ C₂ : Set α)
    (hC₁ : C₁ ⊆ M.E) (hC₂ : C₂ ⊆ M.E) :
    Matroid.contract M C₁ = Matroid.contract M C₂ ↔ C₁ ∩ M.E = C₂ ∩ M.E := by
  have _ := hC₁
  have _ := hC₂
  simpa using (Matroid.contract_eq_contract_iff (M := M) (C₁ := C₁) (C₂ := C₂))

/--
Source proof (docs/source.tex lines 96-109): rewrite coindependence as independence
in the dual matroid and apply the deletion characterization.
Prover notes: combine dual/coindependence lemmas with contraction-as-deletion-in-the-dual;
`Disjoint X C` represents `X ∩ C = ∅`.
-/
theorem coindep_contract_iff {α : Type u} (M : Matroid α) (C X : Set α)
    (hC : C ⊆ M.E) (hX : X ⊆ M.E) :
    (Matroid.contract M C).Coindep X ↔ M.Coindep X ∧ Disjoint X C := by
  have _ := hC
  have _ := hX
  exact (Matroid.coindep_contract_iff (M := M) (C := C) (X := X))

/--
Source proof (docs/source.tex lines 111-120): immediate from the coindependence
characterization and the definition of cocircuits.
Prover notes: use `coindep_contract_iff` together with Mathlib's `IsCocircuit`
characterization as a circuit in the dual.
-/
theorem contract_isCocircuit_iff {α : Type u} (M : Matroid α) (C K : Set α)
    (hC : C ⊆ M.E) :
    (Matroid.contract M C).IsCocircuit K ↔ M.IsCocircuit K ∧ Disjoint K C := by
  have _ := hC
  exact (Matroid.contract_isCocircuit_iff (M := M) (C := C) (K := K))

/--
Source proof (docs/source.tex lines 122-136): by duality, reduce to the basis
characterization for deletion and translate back.
Prover notes: Mathlib search found `Matroid.Indep.contract_isBase_iff`; normalize
`B ∪ I` and `Disjoint B I` if necessary.
-/
theorem Indep.contract_isBase_iff {α : Type u} {M : Matroid α} {I B : Set α}
    (hI : M.Indep I) :
    (Matroid.contract M I).IsBase B ↔ M.IsBase (B ∪ I) ∧ Disjoint B I := by
  exact hI.contract_isBase_iff

/--
Source proof (docs/source.tex lines 138-153): an independent set is contained in a
basis; apply the previous basis characterization for contraction.
Prover notes: Mathlib search found `Matroid.Indep.contract_indep_iff`; the source
hypothesis `J ⊆ M.E` is kept explicitly.
-/
theorem Indep.contract_indep_iff {α : Type u} {M : Matroid α} {I J : Set α}
    (hI : M.Indep I) (hJ : J ⊆ M.E) :
    (Matroid.contract M I).Indep J ↔ Disjoint J I ∧ M.Indep (J ∪ I) := by
  exact (fun _hJ : J ⊆ M.E => hI.contract_indep_iff) hJ

/--
Source proof (docs/source.tex lines 155-170): specialize the previous lemma to
`I = {e}` and use that a non-loop element gives an independent singleton.
Prover notes: simplify `Disjoint I {e}` to `e ∉ I` after applying the independent
contraction lemma.
-/
theorem IsNonloop.contractElem_indep_iff {α : Type u} {M : Matroid α} {e : α}
    (he : M.IsNonloop e) (I : Set α) :
    (Matroid.contract M {e}).Indep I ↔ e ∉ I ∧ M.Indep (I ∪ {e}) := by
  simpa [Set.union_singleton] using (he.contractElem_indep_iff (I := I))

/--
Source proof (docs/source.tex lines 172-185): decompose `X` as the basis `I` plus
`X \ I`; contracting `X` equals contracting `I` and deleting the residual elements.
Prover notes: use basis-spanning contraction lemmas and contraction/delete
commutation; search for `IsBasis.contract_eq_contract_delete`.
-/
theorem IsBasis.contract_eq_contract_delete {α : Type u} {M : Matroid α} {I X : Set α}
    (hI : M.IsBasis I X) :
    Matroid.contract M X = Matroid.delete (Matroid.contract M I) (X \ I) := by
  exact hI.contract_eq_contract_delete
