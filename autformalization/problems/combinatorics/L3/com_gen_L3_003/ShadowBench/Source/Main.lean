import Mathlib.Combinatorics.Matroid.Minor.Delete
import Mathlib.Tactic.TautoSet
import Mathlib.Combinatorics.Matroid.Minor.Contract

open Set

variable {α : Type*}

/--
Source proof (docs/source.tex, lines 23-28): choose a basis `I` of `C`, replace
`cl_M(C)` by `cl_M(I)`, express contraction by this closure as contraction by `I`
followed by deleting `cl_M(I) \ I`, and rearrange contraction/deletion operations.
Prover notes: after statement review, this should be a direct wrapper around
`Matroid.contract_closure_eq_contract_delete`; the explicit `hC` records the
source side condition even though Mathlib proves a stronger version.
-/
theorem contract_closure_eq_contract_delete (M : Matroid α) (C : Set α) (hC : C ⊆ M.E) :
    Matroid.contract M (M.closure C) =
      Matroid.delete (Matroid.contract M C) (M.closure C \ C) := by
  sorry

/--
Source proof (docs/source.tex, lines 36-41): use the loop description
`loops(M/C) = cl_M(C) \ C` and characterize closure after contraction by the
corresponding loop condition; the two inclusions identify exactly the elements
of `cl_M(X ∪ C)` not lying in `C`.
Prover notes: after statement review, use `Matroid.contract_closure_eq M C X`
or recreate the source loop argument via `Matroid.contract_loops_eq`.
-/
theorem contract_closure_eq (M : Matroid α) (C X : Set α) :
    (Matroid.contract M C).closure X = M.closure (X ∪ C) \ C := by
  sorry

/--
Source proof (docs/source.tex, lines 51-56): rewrite spanning as closure equal
to the ground set, apply the contraction closure formula and
`(M/C).E = M.E \ C`, then simplify equality of set differences to spanning of
`X ∪ C` in `M` together with `Disjoint X C`.
Prover notes: after statement review, try
`Matroid.contract_spanning_iff (M := M) (C := C) (X := X) hC`; a from-source
proof should use `contract_closure_eq`, `Matroid.contract_ground`, and
`Matroid.spanning_iff_closure_eq`.
-/
theorem contract_spanning_iff (M : Matroid α) (C : Set α) (hC : C ⊆ M.E) (X : Set α) :
    (Matroid.contract M C).Spanning X ↔ M.Spanning (X ∪ C) ∧ Disjoint X C := by
  sorry
