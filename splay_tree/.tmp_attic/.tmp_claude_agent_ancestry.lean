import Challenges.ZBK

namespace Splay
namespace Splay
namespace Splay
namespace Splay
namespace Splay
namespace Splay

set_option linter.dupNamespace false

/-! # Touched-prefix closure

Along the splay process, on ANY search path, the touched nodes form a prefix:
every ancestor (`u ∈ searchPath w t`) of a touched node `w` is itself touched.
-/

/-- PATHS ARE CHAINS: if `w` lies on `x`'s search path and `u` lies on `w`'s
search path, then `u` lies on `x`'s search path. -/
theorem searchPath_chain {x w u : ℕ} {t : BinaryTree} (hbst : IsBST t)
    (hw : w ∈ searchPath x t) (hu : u ∈ searchPath w t) :
    u ∈ searchPath x t := by
  obtain ⟨sh, heq, hsub⟩ := searchPath_eq_shared_append_suffix x w t
  rw [divergeSuffix_eq_nil_of_mem x w t hbst hw, List.append_nil] at heq
  exact hsub u (heq ▸ hu)

/-- KEY SUBLEMMA (ancestors in the splayed tree): any node on a search path of
the splayed tree was either on the OLD access path of the splayed key, or was
already an ancestor in the old tree. -/
theorem mem_searchPath_splay_cases {x w u : ℕ} {t : BinaryTree} (hbst : IsBST t)
    (hu : u ∈ searchPath w (splay t x)) :
    u ∈ searchPath x t ∨ u ∈ searchPath w t := by
  obtain ⟨p', heq, hsub⟩ := searchPath_splay_decomp x w t hbst
  rw [heq, List.mem_append] at hu
  rcases hu with h | h
  · exact Or.inl (hsub u h)
  · refine Or.inr ?_
    obtain ⟨sh, heq2, _⟩ := searchPath_eq_shared_append_suffix x w t
    rw [heq2]
    exact List.mem_append.mpr (Or.inr h)

/-- Touched-prefix closure, strong form: every ancestor-or-self `u` of a
touched node `w` (in the current process tree) is itself touched. -/
theorem touched_prefix_closed_strong {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (hbst : IsBST init) :
    ∀ (i : ℕ) (u w : ℕ), u ∈ searchPath w (processTree init X i) →
      w ∈ touchedList init X i → u ∈ touchedList init X i := by
  intro i
  induction i with
  | zero =>
      intro u w _ hwt
      rw [touchedList_zero] at hwt
      simp at hwt
  | succ i ih =>
      intro u w hu hwt
      rw [touchedList_succ, List.mem_append] at hwt ⊢
      by_cases h : i < n
      · -- in-range step: processTree (i+1) = splay (processTree i) (accessN X i)
        rw [processTree_succ_nat init X h] at hu
        have hbsti : IsBST (processTree init X i) := processTree_isBST init X hbst i
        rcases mem_searchPath_splay_cases hbsti hu with hx | hold
        · -- u was on the i-th access path
          refine Or.inr ?_
          rw [pathN_lt init X h]
          exact hx
        · -- u was already an ancestor of w in the old tree
          rcases hwt with hwt | hwp
          · exact Or.inl (ih u w hold hwt)
          · -- w itself was on the i-th access path: paths are chains
            refine Or.inr ?_
            rw [pathN_lt init X h] at hwp ⊢
            exact searchPath_chain hbsti hwp hold
      · -- out-of-range step: nothing changes
        have hP : processTree init X (i + 1) = processTree init X i := by
          rw [processTree_succ_dite, dif_neg h]
        have hpath : pathN init X i = [] := by
          unfold pathN
          rw [dif_neg h]
        rw [hP] at hu
        rcases hwt with hwt | hwp
        · exact Or.inl (ih u w hu hwt)
        · rw [hpath] at hwp
          simp at hwp

/-- Touched-prefix closure (requested form): `u` an ancestor-or-self of `w` on
any search path of the process tree, `w` touched ⟹ `u` touched or `u = w`.
(The hypotheses `q`, `hw` of the original statement are not needed; the left
disjunct always holds.) -/
theorem touched_prefix_closed {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (hbst : IsBST init) (i : ℕ) (q : ℕ) (u w : ℕ)
    (hu : u ∈ searchPath w (processTree init X i))
    (_hw : w ∈ searchPath q (processTree init X i))
    (hwt : w ∈ touchedList init X i) :
    u ∈ touchedList init X i ∨ u = w :=
  Or.inl (touched_prefix_closed_strong init X hbst i u w hu hwt)

#print axioms touched_prefix_closed_strong
#print axioms touched_prefix_closed
#print axioms searchPath_chain
#print axioms mem_searchPath_splay_cases

end Splay
end Splay
end Splay
end Splay
end Splay
end Splay
