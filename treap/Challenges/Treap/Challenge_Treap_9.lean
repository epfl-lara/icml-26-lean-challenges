/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Collodel, Sorrachai Yingchareonthawornchai
-/

import Challenges.Treap.Def_TreapComposite

namespace Cslib.Algorithms.Lean.TimeM
namespace TreapLogic
open Tree

variable {Key : Type} [LinearOrder Key]
variable {Prio : Type} [LinearOrder Prio]

/-
  Find correctness

  Find k returns a key-priority pair with key k iff k is present in the treap

-/
theorem find_finds_element (t : Treap Key Prio) (k : Key) :
    get_key (Treap.find t k) = some k ↔ k ∈ t.root.all_keys := by
  have all_keys_union_split :
      ∀ (tn : TreapNode Key Prio) (k : Key),
        (TreapNode.split tn k).1.all_keys ∪ (TreapNode.split tn k).2.all_keys =
          tn.all_keys := by
    intro tn k
    fun_induction TreapNode.split tn k
    · simp [TreapNode.all_keys]
    case case2 kp l r h split_l new_r hsplit new_l ih1 =>
      subst new_l
      simp only [hsplit, TreapNode.all_keys, Set.union_singleton] at ih1 ⊢
      rw [← ih1]
      ext x
      simp [or_assoc]
    case case3 kp l r h split_l split_r hsplit new_r ih1 =>
      subst new_r
      simp only [hsplit, TreapNode.all_keys, Set.union_singleton] at ih1 ⊢
      rw [← ih1]
      ext x
      simp [or_assoc, or_left_comm]
  have leftmost_key_mem :
      ∀ (tn : TreapNode Key Prio) (kp : KeyPrioPair Key Prio),
        TreapNode.leftmost tn = some kp → kp.key ∈ tn.all_keys := by
    intro tn kp h
    induction tn with
    | nil =>
        simp [TreapNode.leftmost] at h
    | node root l r ih_l ih_r =>
        cases l with
        | nil =>
            simp [TreapNode.leftmost] at h
            simpa [TreapNode.all_keys] using
              (Or.inl (congrArg KeyPrioPair.key h.symm) :
                kp.key = root.key ∨ kp.key ∈ TreapNode.all_keys r)
        | node lroot ll lr =>
            have hl : kp.key ∈ TreapNode.all_keys (Tree.node lroot ll lr : TreapNode Key Prio) := by
              exact ih_l (by simpa [TreapNode.leftmost] using h)
            have hl' : (kp.key = lroot.key ∨ kp.key ∈ TreapNode.all_keys ll) ∨
                kp.key ∈ TreapNode.all_keys lr := by
              simpa [TreapNode.all_keys] using hl
            simpa [TreapNode.all_keys] using
              (Or.inl (Or.inr hl') :
                (kp.key = root.key ∨
                    ((kp.key = lroot.key ∨ kp.key ∈ TreapNode.all_keys ll) ∨
                      kp.key ∈ TreapNode.all_keys lr)) ∨
                  kp.key ∈ TreapNode.all_keys r)
  have leftmost_eq_of_mem_min :
      ∀ (tn : TreapNode Key Prio),
        IsBST tn →
        (∀ x, x ∈ tn.all_keys → k ≤ x) →
        k ∈ tn.all_keys →
        get_key (TreapNode.leftmost tn) = some k := by
    intro tn hbst
    induction hbst with
    | nil =>
        intro hmin hmem
        simp [TreapNode.all_keys] at hmem
    | node kp l r hlt hge bst_l bst_r ih_l ih_r =>
        intro hmin hmem
        cases l with
        | nil =>
            have hk_le_root : k ≤ kp.key := by
              exact hmin kp.key (by simp [TreapNode.all_keys])
            have hroot_le_k : kp.key ≤ k := by
              have hmem' : k = kp.key ∨ k ∈ r.all_keys := by
                simpa [TreapNode.all_keys] using hmem
              rcases hmem' with hkroot | hkr
              · exact le_of_eq hkroot.symm
              · exact hge k hkr
            have hkp : kp.key = k := le_antisymm hroot_le_k hk_le_root
            simp [TreapNode.leftmost, get_key, hkp]
        | node lkp ll lr =>
            let lnode : TreapNode Key Prio := Tree.node lkp ll lr
            have hleft_key_mem : lkp.key ∈ lnode.all_keys := by
              simp [lnode, TreapNode.all_keys]
            have hleft_key_mem_whole :
                lkp.key ∈
                  TreapNode.all_keys
                    (Tree.node kp (Tree.node lkp ll lr) r : TreapNode Key Prio) := by
              simp [TreapNode.all_keys]
            have h_lkp_lt_root : lkp.key < kp.key := by
              exact hlt lkp.key hleft_key_mem
            have hk_l : k ∈ lnode.all_keys := by
              have hk_cases : (k = kp.key ∨ k ∈ lnode.all_keys) ∨ k ∈ r.all_keys := by
                simpa [lnode, TreapNode.all_keys] using hmem
              rcases hk_cases with (hkroot | hkl) | hkr
              · have hk_le_lkp : k ≤ lkp.key := hmin lkp.key hleft_key_mem_whole
                have hroot_le_lkp : kp.key ≤ lkp.key := by
                  rwa [hkroot] at hk_le_lkp
                exact False.elim ((not_lt_of_ge hroot_le_lkp) h_lkp_lt_root)
              · exact hkl
              · have hroot_le_k : kp.key ≤ k := hge k hkr
                have hk_le_lkp : k ≤ lkp.key := hmin lkp.key hleft_key_mem_whole
                have hroot_le_lkp : kp.key ≤ lkp.key := le_trans hroot_le_k hk_le_lkp
                exact False.elim ((not_lt_of_ge hroot_le_lkp) h_lkp_lt_root)
            have hmin_l : ∀ x, x ∈ lnode.all_keys → k ≤ x := by
              intro x hx
              have hxwhole :
                  x ∈
                    TreapNode.all_keys
                      (Tree.node kp (Tree.node lkp ll lr) r : TreapNode Key Prio) := by
                have hx_leftnode :
                    x ∈ TreapNode.all_keys (Tree.node lkp ll lr : TreapNode Key Prio) := by
                  simpa [lnode] using hx
                exact Or.inl (Or.inl hx_leftnode)
              exact hmin x hxwhole
            have hres : get_key (TreapNode.leftmost lnode) = some k := ih_l hmin_l hk_l
            simpa [lnode, TreapNode.leftmost] using hres
  constructor
  · intro hfind
    cases hleft : TreapNode.leftmost (TreapNode.split t.root k).2 with
    | none =>
        simp [Treap.find, Treap.split, hleft, get_key] at hfind
    | some kp =>
        by_cases hkp : kp.key = k
        · have hk_right : k ∈ (TreapNode.split t.root k).2.all_keys := by
            have hmem := leftmost_key_mem (TreapNode.split t.root k).2 kp hleft
            simpa [hkp] using hmem
          have hxU : k ∈ (TreapNode.split t.root k).1.all_keys ∪
              (TreapNode.split t.root k).2.all_keys := Or.inr hk_right
          simpa [all_keys_union_split t.root k] using hxU
        · simp [Treap.find, Treap.split, hleft, hkp, get_key] at hfind
  · intro hk_all
    have hxU : k ∈ (TreapNode.split t.root k).1.all_keys ∪
        (TreapNode.split t.root k).2.all_keys := by
      simpa [all_keys_union_split t.root k] using hk_all
    have hk_right : k ∈ (TreapNode.split t.root k).2.all_keys := by
      rcases hxU with hkL | hkR
      · have hlt := split_left_lt_k t.root t.is_treap.2 k k hkL
        exact False.elim ((lt_irrefl k) hlt)
      · exact hkR
    have hbst_right : IsBST (TreapNode.split t.root k).2 :=
      split_IsBST_right t.root t.is_treap.2 k
    have hmin_right : ∀ x, x ∈ (TreapNode.split t.root k).2.all_keys → k ≤ x :=
      split_right_ge_k t.root t.is_treap.2 k
    have hleft_key : get_key (TreapNode.leftmost (TreapNode.split t.root k).2) = some k :=
      leftmost_eq_of_mem_min (TreapNode.split t.root k).2 hbst_right hmin_right hk_right
    cases hleft : TreapNode.leftmost (TreapNode.split t.root k).2 with
    | none =>
        simp [hleft, get_key] at hleft_key
    | some kp =>
        have hkp : kp.key = k := by
          simpa [hleft, get_key] using hleft_key
        simp [Treap.find, Treap.split, hleft, hkp, get_key]

end TreapLogic
end Cslib.Algorithms.Lean.TimeM
