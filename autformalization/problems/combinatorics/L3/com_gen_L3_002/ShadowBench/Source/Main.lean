import Mathlib.Combinatorics.Matroid.Minor.Order

open Set

/--
Source `line-17`: a matroid `N` is a minor of `M` if it is obtained from `M` by
contracting some set and then deleting some set. This local name preserves the
ShadowBench-required declaration name while using Mathlib's canonical definition.
-/
def IsMinor {α : Type*} (N M : Matroid α) : Prop :=
  Matroid.IsMinor N M

infix:50 " ≤ₘ " => IsMinor

/--
Source `line-26`: `N` is a strict minor of `M` when `N` is a minor of `M` but
`M` is not a minor of `N`.
-/
def IsStrictMinor {α : Type*} (N M : Matroid α) : Prop :=
  IsMinor N M ∧ ¬ IsMinor M N

infix:50 " <ₘ " => IsStrictMinor

/--
Source proof (`lem:disjoint-contract-delete`): start from arbitrary contraction/deletion
witnesses for `N ≤ₘ M`, restrict them to the ground set of `M`, then replace the
deletion set by its difference with the contraction set so the witnesses are disjoint.
Prover notes: unfold the local wrapper to Mathlib's `Matroid.IsMinor`, use
`Matroid.IsMinor.exists_eq_contract_delete_disjoint`, and convert `Disjoint C D` to
`C ∩ D = ∅`.
-/
theorem IsMinor.exists_eq_contract_delete_disjoint {α : Type*} {N M : Matroid α}
    (h : N ≤ₘ M) :
    ∃ C D : Set α, C ⊆ M.E ∧ D ⊆ M.E ∧ (C ∩ D = ∅) ∧
      (N = Matroid.delete (Matroid.contract M C) D) := by
  change Matroid.IsMinor N M at h
  obtain ⟨C, D, hC, hD, hCD, hN⟩ :=
    Matroid.IsMinor.exists_eq_contract_delete_disjoint h
  refine ⟨C, D, hC, hD, ?_, ?_⟩
  · exact hCD.inter_eq
  · simpa using hN

/--
Source proof (`thm:minor-order`, reflexivity bullet): take the contraction and deletion
sets to be empty, giving `N = N ／ ∅ ＼ ∅`.
Prover notes: unfold the local wrapper and use `Matroid.IsMinor.refl`.
-/
theorem IsMinor.refl {α : Type*} (N : Matroid α) : N ≤ₘ N := by
  simpa [IsMinor] using (Matroid.IsMinor.refl : Matroid.IsMinor N N)

/--
Source proof (`thm:minor-order`, transitivity bullet): choose disjoint contraction and
deletion witnesses for both minor relations, substitute the expression for the middle
matroid, then commute and combine disjoint contractions/deletions into one contraction
and one deletion from the largest matroid.
Prover notes: unfold the local wrapper and use `Matroid.IsMinor.trans`; the source-style
proof uses `Matroid.contract_delete_contract_delete'`.
-/
theorem IsMinor.trans {α : Type*} {N M P : Matroid α} (hNM : N ≤ₘ M) (hMP : M ≤ₘ P) :
    N ≤ₘ P := by
  simpa [IsMinor] using Matroid.IsMinor.trans hNM hMP

/--
Source proof (`thm:minor-order`, antisymmetry bullet): write each direction using
disjoint ground-set contraction/deletion witnesses. The first representation gives
`E(N) ⊆ E(M)`, and the reverse gives `E(M) ⊆ E(N)`. Equality of ground sets forces
the contracted/deleted sets to be empty, so `N = M`.
Prover notes: unfold the local wrapper and use `Matroid.IsMinor.antisymm`; the source
proof can also be followed through `IsMinor.exists_eq_contract_delete_disjoint` and
ground-set inclusions.
-/
theorem IsMinor_antisymm {α : Type*} {N M : Matroid α} (hNM : N ≤ₘ M) (hMN : M ≤ₘ N) :
    N = M := by
  simpa [IsMinor] using Matroid.IsMinor.antisymm hNM hMN
