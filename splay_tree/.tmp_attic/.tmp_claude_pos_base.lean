import Challenges.Splay_Tree.Def_Containment
import Challenges.Splay_Tree.Def_Ackermann
import Challenges.Splay_Tree.Def_Splay

/-!
# PHASE A — the HALVING-WITH-POSITION lemma (6th shape induction).

Interior new-path P-keys are repaid survivors: for the splay of `x` in a BST `t`
with old path `P = searchPath x t`, every key `w ∈ P` that is a STRICT new-path
ancestor of another `P`-key `w'` (`w ∈ searchPath w' (splay t x)`, `w ≠ w'`)
satisfies the survivor inequality  `2 * keyDepth w (splay t x) ≤ P.idxOf w + 5`.
The divergence node (last `P`-member of a new path) satisfies the `+6`/`+7` bound
unconditionally.  Base blocks copied verbatim from the compiled dev arsenal
(.tmp_claude_hstep_v3.lean).
-/

set_option maxHeartbeats 4000000

namespace Splay

private theorem forallTree_iff_forall_mem {p : Nat → Prop}
    {t : BinaryTree} :
    ForallTree p t ↔ ∀ k : Nat, k ∈ t.toKeyList → p k := by
  constructor
  · intro ht
    induction ht with
    | left =>
        simp [BinaryTree.toKeyList]
    | node left key right hleft hkey hright ihl ihr =>
        intro k hk
        simp [BinaryTree.toKeyList] at hk
        rcases hk with hk | hk | hk
        · exact ihl k hk
        · simpa [hk] using hkey
        · exact ihr k hk
  · intro hmem
    induction t with
    | empty =>
        exact ForallTree.left
    | node l key r ihl ihr =>
        refine ForallTree.node l key r ?_ ?_ ?_
        · exact ihl (by
            intro k hk
            exact hmem k (by simp [BinaryTree.toKeyList, hk]))
        · exact hmem key (by simp [BinaryTree.toKeyList])
        · exact ihr (by
            intro k hk
            exact hmem k (by simp [BinaryTree.toKeyList, hk]))

private theorem forallTree_imp {p q : Nat → Prop}
    (hpq : ∀ k : Nat, p k → q k) {t : BinaryTree} :
    ForallTree p t → ForallTree q t := by
  intro ht
  induction ht with
  | left =>
      exact ForallTree.left
  | node left key right hleft hkey hright ihl ihr =>
      exact ForallTree.node left key right ihl (hpq key hkey) ihr

private theorem rotateRight_isBST {t : BinaryTree} (hbst : IsBST t) :
    IsBST (rotateRight t) := by
  cases hbst with
  | left =>
      exact IsBST.left
  | node key left right hleft hright hbst_left hbst_right =>
      cases left with
      | empty =>
          simpa [rotateRight] using
            IsBST.node key .empty right hleft hright hbst_left hbst_right
      | node a x b =>
          have hleft_mem : ∀ z : Nat,
              z ∈ (BinaryTree.node a x b).toKeyList → z < key :=
            forallTree_iff_forall_mem.mp hleft
          have hx_lt_key : x < key := by
            exact hleft_mem x (by simp [BinaryTree.toKeyList])
          have hb_lt_key : ForallTree (fun z => z < key) b :=
            forallTree_iff_forall_mem.mpr (by
              intro z hz
              exact hleft_mem z (by simp [BinaryTree.toKeyList, hz]))
          cases hbst_left with
          | node _ _ _ ha_lt_x hx_lt_b hbst_a hbst_b =>
              have hright_gt_x :
                  ForallTree (fun z => x < z) (.node b key right) :=
                ForallTree.node b key right hx_lt_b hx_lt_key
                  (forallTree_imp (fun z hz => lt_trans hx_lt_key hz) hright)
              have hbst_new_right : IsBST (.node b key right) :=
                IsBST.node key b right hb_lt_key hright hbst_b hbst_right
              simpa [rotateRight] using
                IsBST.node x a (.node b key right)
                  ha_lt_x hright_gt_x hbst_a hbst_new_right

private theorem rotateLeft_isBST {t : BinaryTree} (hbst : IsBST t) :
    IsBST (rotateLeft t) := by
  cases hbst with
  | left =>
      exact IsBST.left
  | node key left right hleft hright hbst_left hbst_right =>
      cases right with
      | empty =>
          simpa [rotateLeft] using
            IsBST.node key left .empty hleft hright hbst_left hbst_right
      | node b y c =>
          have hright_mem : ∀ z : Nat,
              z ∈ (BinaryTree.node b y c).toKeyList → key < z :=
            forallTree_iff_forall_mem.mp hright
          have hkey_lt_y : key < y := by
            exact hright_mem y (by simp [BinaryTree.toKeyList])
          have hb_gt_key : ForallTree (fun z => key < z) b :=
            forallTree_iff_forall_mem.mpr (by
              intro z hz
              exact hright_mem z (by simp [BinaryTree.toKeyList, hz]))
          cases hbst_right with
          | node _ _ _ hb_lt_y hy_lt_c hbst_b hbst_c =>
              have hleft_lt_y :
                  ForallTree (fun z => z < y) (.node left key b) :=
                ForallTree.node left key b
                  (forallTree_imp (fun z hz => lt_trans hz hkey_lt_y) hleft)
                  hkey_lt_y hb_lt_y
              have hbst_new_left : IsBST (.node left key b) :=
                IsBST.node key left b hleft hb_gt_key hbst_left hbst_b
              simpa [rotateLeft] using
                IsBST.node y (.node left key b) c
                  hleft_lt_y hy_lt_c hbst_new_left hbst_c

private theorem rotateRight_toKeyList (t : BinaryTree) :
    (rotateRight t).toKeyList = t.toKeyList := by
  cases t with
  | empty => simp [rotateRight, BinaryTree.toKeyList]
  | node l k r =>
      cases l with
      | empty => simp [rotateRight, BinaryTree.toKeyList]
      | node a x b =>
          simp [rotateRight, BinaryTree.toKeyList, List.append_assoc]

private theorem rotateLeft_toKeyList (t : BinaryTree) :
    (rotateLeft t).toKeyList = t.toKeyList := by
  cases t with
  | empty => simp [rotateLeft, BinaryTree.toKeyList]
  | node l k r =>
      cases r with
      | empty => simp [rotateLeft, BinaryTree.toKeyList]
      | node a x b =>
          simp [rotateLeft, BinaryTree.toKeyList, List.append_assoc]

private theorem rotate_toKeyList (t : BinaryTree) (rt : Rot) :
    (rotate t rt).toKeyList = t.toKeyList := by
  cases rt <;> simp [rotate, rotateRight_toKeyList, rotateLeft_toKeyList]
  · cases t with
    | empty => simp
    | node l k r =>
        rw [rotateRight_toKeyList]
        simp [BinaryTree.toKeyList, rotateLeft_toKeyList]
  · cases t with
    | empty => simp
    | node l k r =>
        rw [rotateLeft_toKeyList]
        simp [BinaryTree.toKeyList, rotateRight_toKeyList]

private theorem rotate_forallTree {p : Nat → Prop}
    (t : BinaryTree) (rt : Rot) :
    ForallTree p (rotate t rt) ↔ ForallTree p t := by
  rw [forallTree_iff_forall_mem, forallTree_iff_forall_mem,
    rotate_toKeyList]

private theorem rotate_isBST {t : BinaryTree} (rt : Rot)
    (hbst : IsBST t) :
    IsBST (rotate t rt) := by
  cases rt
  · exact rotateRight_isBST (rotateRight_isBST hbst)
  · cases hbst with
    | left =>
        exact IsBST.left
    | node key left right hleft hright hbst_left hbst_right =>
        have hleft_rot : ForallTree (fun z => z < key) (rotateLeft left) :=
          (rotate_forallTree left .zag).mpr hleft
        have hbst_left_rot : IsBST (rotateLeft left) :=
          rotateLeft_isBST hbst_left
        exact rotateRight_isBST
          (IsBST.node key (rotateLeft left) right
            hleft_rot hright hbst_left_rot hbst_right)
  · exact rotateLeft_isBST (rotateLeft_isBST hbst)
  · cases hbst with
    | left =>
        exact IsBST.left
    | node key left right hleft hright hbst_left hbst_right =>
        have hright_rot : ForallTree (fun z => key < z) (rotateRight right) :=
          (rotate_forallTree right .zig).mpr hright
        have hbst_right_rot : IsBST (rotateRight right) :=
          rotateRight_isBST hbst_right
        exact rotateLeft_isBST
          (IsBST.node key left (rotateRight right)
            hleft hright_rot hbst_left hbst_right_rot)
  · exact rotateRight_isBST hbst
  · exact rotateLeft_isBST hbst

theorem splay_toKeyList : ∀ (t : BinaryTree) (q : Nat),
    (splay t q).toKeyList = t.toKeyList
| .empty, q => by
    simp [splay.eq_def, BinaryTree.toKeyList]
| .node l k r, q => by
    rw [splay.eq_def]
    by_cases hqk : q = k
    · simp [hqk, BinaryTree.toKeyList]
    · by_cases hq_lt_k : q < k
      · cases l with
        | empty =>
            simp [hqk, hq_lt_k, BinaryTree.toKeyList]
        | node ll lk lr =>
            by_cases hq_lt_lk : q < lk
            · cases ll with
              | empty =>
                  simp [hqk, hq_lt_k, hq_lt_lk, BinaryTree.toKeyList,
                    rotate_toKeyList]
              | node a x b =>
                  have hll := splay_toKeyList (BinaryTree.node a x b) q
                  simp [hqk, hq_lt_k, hq_lt_lk, BinaryTree.toKeyList, hll,
                    rotate_toKeyList, List.append_assoc]
            · by_cases hlk_lt_q : lk < q
              · cases lr with
                | empty =>
                    simp [hqk, hq_lt_k, hq_lt_lk, hlk_lt_q,
                      BinaryTree.toKeyList, rotate_toKeyList]
                | node a x b =>
                    have hlr := splay_toKeyList (BinaryTree.node a x b) q
                    simp [hqk, hq_lt_k, hq_lt_lk, hlk_lt_q,
                      BinaryTree.toKeyList, hlr, rotate_toKeyList,
                      List.append_assoc]
              · simp [hqk, hq_lt_k, hq_lt_lk, hlk_lt_q,
                  BinaryTree.toKeyList, rotate_toKeyList]
      · cases r with
        | empty =>
            simp [hqk, hq_lt_k, BinaryTree.toKeyList]
        | node rl rk rr =>
            by_cases hq_lt_rk : q < rk
            · cases rl with
              | empty =>
                  simp [hqk, hq_lt_k, hq_lt_rk, BinaryTree.toKeyList,
                    rotate_toKeyList]
              | node a x b =>
                  have hrl := splay_toKeyList (BinaryTree.node a x b) q
                  simp [hqk, hq_lt_k, hq_lt_rk, BinaryTree.toKeyList, hrl,
                    rotate_toKeyList, List.append_assoc]
            · by_cases hrk_lt_q : rk < q
              · cases rr with
                | empty =>
                    simp [hqk, hq_lt_k, hq_lt_rk, hrk_lt_q,
                      BinaryTree.toKeyList, rotate_toKeyList]
                | node a x b =>
                    have hrr := splay_toKeyList (BinaryTree.node a x b) q
                    simp [hqk, hq_lt_k, hq_lt_rk, hrk_lt_q,
                      BinaryTree.toKeyList, hrr, rotate_toKeyList,
                      List.append_assoc]
              · simp [hqk, hq_lt_k, hq_lt_rk, hrk_lt_q,
                  BinaryTree.toKeyList, rotate_toKeyList]

private theorem splay_forallTree {p : Nat → Prop}
    (t : BinaryTree) (q : Nat) :
    ForallTree p (splay t q) ↔ ForallTree p t := by
  rw [forallTree_iff_forall_mem, forallTree_iff_forall_mem,
    splay_toKeyList]

theorem splay_isBST : ∀ (t : BinaryTree) (q : Nat),
    IsBST t → IsBST (splay t q)
| .empty, q, _hbst => by
    simp [splay.eq_def]
    exact IsBST.left
| .node l k r, q, hbst => by
    rw [splay.eq_def]
    cases hbst with
    | node _ _ _ hleft hright hbst_left hbst_right =>
        by_cases hqk : q = k
        · simpa [hqk] using
            IsBST.node k l r hleft hright hbst_left hbst_right
        · by_cases hq_lt_k : q < k
          · cases l with
            | empty =>
                simpa [hqk, hq_lt_k] using
                  IsBST.node k .empty r hleft hright hbst_left hbst_right
            | node ll lk lr =>
                cases hleft with
                | node _ _ _ hll_lt_k hlk_lt_k hlr_lt_k =>
                    cases hbst_left with
                    | node _ _ _ hll_lt_lk hlk_lt_lr hbst_ll hbst_lr =>
                        by_cases hq_lt_lk : q < lk
                        · cases ll with
                          | empty =>
                              simpa [hqk, hq_lt_k, hq_lt_lk] using
                                rotate_isBST .zig
                                  (IsBST.node k (.node .empty lk lr) r
                                    (ForallTree.node .empty lk lr
                                      hll_lt_k hlk_lt_k hlr_lt_k)
                                    hright
                                    (IsBST.node lk .empty lr
                                      hll_lt_lk hlk_lt_lr hbst_ll hbst_lr)
                                    hbst_right)
                          | node a x b =>
                              have hbst_sll :
                                  IsBST (splay (.node a x b) q) :=
                                splay_isBST (.node a x b) q hbst_ll
                              have hsll_lt_lk :
                                  ForallTree (fun z => z < lk)
                                    (splay (.node a x b) q) :=
                                (splay_forallTree (.node a x b) q).mpr
                                  hll_lt_lk
                              have hsll_lt_k :
                                  ForallTree (fun z => z < k)
                                    (splay (.node a x b) q) :=
                                (splay_forallTree (.node a x b) q).mpr
                                  hll_lt_k
                              have hbst_t' : IsBST
                                  (.node (splay (.node a x b) q) lk lr) :=
                                IsBST.node lk (splay (.node a x b) q) lr
                                  hsll_lt_lk hlk_lt_lr hbst_sll hbst_lr
                              have hleft_t' :
                                  ForallTree (fun z => z < k)
                                    (.node (splay (.node a x b) q) lk lr) :=
                                ForallTree.node (splay (.node a x b) q)
                                  lk lr hsll_lt_k hlk_lt_k hlr_lt_k
                              simpa [hqk, hq_lt_k, hq_lt_lk] using
                                rotate_isBST .zigZig
                                  (IsBST.node k
                                    (.node (splay (.node a x b) q) lk lr)
                                    r hleft_t' hright hbst_t' hbst_right)
                        · by_cases hlk_lt_q : lk < q
                          · cases lr with
                            | empty =>
                                simpa [hqk, hq_lt_k, hq_lt_lk, hlk_lt_q]
                                  using
                                    rotate_isBST .zig
                                      (IsBST.node k (.node ll lk .empty) r
                                        (ForallTree.node ll lk .empty
                                          hll_lt_k hlk_lt_k hlr_lt_k)
                                        hright
                                        (IsBST.node lk ll .empty
                                          hll_lt_lk hlk_lt_lr hbst_ll hbst_lr)
                                        hbst_right)
                            | node a x b =>
                                have hbst_slr :
                                    IsBST (splay (.node a x b) q) :=
                                  splay_isBST (.node a x b) q hbst_lr
                                have hslr_gt_lk :
                                    ForallTree (fun z => lk < z)
                                      (splay (.node a x b) q) :=
                                  (splay_forallTree (.node a x b) q).mpr
                                    hlk_lt_lr
                                have hslr_lt_k :
                                    ForallTree (fun z => z < k)
                                      (splay (.node a x b) q) :=
                                  (splay_forallTree (.node a x b) q).mpr
                                    hlr_lt_k
                                have hbst_t' : IsBST
                                    (.node ll lk (splay (.node a x b) q)) :=
                                  IsBST.node lk ll (splay (.node a x b) q)
                                    hll_lt_lk hslr_gt_lk hbst_ll hbst_slr
                                have hleft_t' :
                                    ForallTree (fun z => z < k)
                                      (.node ll lk
                                        (splay (.node a x b) q)) :=
                                  ForallTree.node ll lk
                                    (splay (.node a x b) q)
                                    hll_lt_k hlk_lt_k hslr_lt_k
                                simpa [hqk, hq_lt_k, hq_lt_lk, hlk_lt_q]
                                  using
                                    rotate_isBST .zigZag
                                      (IsBST.node k
                                        (.node ll lk
                                          (splay (.node a x b) q))
                                        r hleft_t' hright hbst_t' hbst_right)
                          · simpa [hqk, hq_lt_k, hq_lt_lk, hlk_lt_q] using
                              rotate_isBST .zig
                                (IsBST.node k (.node ll lk lr) r
                                  (ForallTree.node ll lk lr
                                    hll_lt_k hlk_lt_k hlr_lt_k)
                                  hright
                                  (IsBST.node lk ll lr
                                    hll_lt_lk hlk_lt_lr hbst_ll hbst_lr)
                                  hbst_right)
          · cases r with
            | empty =>
                simpa [hqk, hq_lt_k] using
                  IsBST.node k l .empty hleft hright hbst_left hbst_right
            | node rl rk rr =>
                cases hright with
                | node _ _ _ hrl_gt_k hk_lt_rk hrr_gt_k =>
                    cases hbst_right with
                    | node _ _ _ hrl_lt_rk hrk_lt_rr hbst_rl hbst_rr =>
                        by_cases hq_lt_rk : q < rk
                        · cases rl with
                          | empty =>
                              simpa [hqk, hq_lt_k, hq_lt_rk] using
                                rotate_isBST .zag
                                  (IsBST.node k l (.node .empty rk rr)
                                    hleft
                                    (ForallTree.node .empty rk rr
                                      hrl_gt_k hk_lt_rk hrr_gt_k)
                                    hbst_left
                                    (IsBST.node rk .empty rr
                                      hrl_lt_rk hrk_lt_rr hbst_rl hbst_rr))
                          | node a x b =>
                              have hbst_srl :
                                  IsBST (splay (.node a x b) q) :=
                                splay_isBST (.node a x b) q hbst_rl
                              have hsrl_lt_rk :
                                  ForallTree (fun z => z < rk)
                                    (splay (.node a x b) q) :=
                                (splay_forallTree (.node a x b) q).mpr
                                  hrl_lt_rk
                              have hsrl_gt_k :
                                  ForallTree (fun z => k < z)
                                    (splay (.node a x b) q) :=
                                (splay_forallTree (.node a x b) q).mpr
                                  hrl_gt_k
                              have hbst_t' : IsBST
                                  (.node (splay (.node a x b) q) rk rr) :=
                                IsBST.node rk (splay (.node a x b) q) rr
                                  hsrl_lt_rk hrk_lt_rr hbst_srl hbst_rr
                              have hright_t' :
                                  ForallTree (fun z => k < z)
                                    (.node (splay (.node a x b) q) rk rr) :=
                                ForallTree.node (splay (.node a x b) q)
                                  rk rr hsrl_gt_k hk_lt_rk hrr_gt_k
                              simpa [hqk, hq_lt_k, hq_lt_rk] using
                                rotate_isBST .zagZig
                                  (IsBST.node k l
                                    (.node (splay (.node a x b) q) rk rr)
                                    hleft hright_t' hbst_left hbst_t')
                        · by_cases hrk_lt_q : rk < q
                          · cases rr with
                            | empty =>
                                simpa [hqk, hq_lt_k, hq_lt_rk, hrk_lt_q]
                                  using
                                    rotate_isBST .zag
                                      (IsBST.node k l (.node rl rk .empty)
                                        hleft
                                        (ForallTree.node rl rk .empty
                                          hrl_gt_k hk_lt_rk hrr_gt_k)
                                        hbst_left
                                        (IsBST.node rk rl .empty
                                          hrl_lt_rk hrk_lt_rr hbst_rl hbst_rr))
                            | node a x b =>
                                have hbst_srr :
                                    IsBST (splay (.node a x b) q) :=
                                  splay_isBST (.node a x b) q hbst_rr
                                have hsrr_gt_rk :
                                    ForallTree (fun z => rk < z)
                                      (splay (.node a x b) q) :=
                                  (splay_forallTree (.node a x b) q).mpr
                                    hrk_lt_rr
                                have hsrr_gt_k :
                                    ForallTree (fun z => k < z)
                                      (splay (.node a x b) q) :=
                                  (splay_forallTree (.node a x b) q).mpr
                                    hrr_gt_k
                                have hbst_t' : IsBST
                                    (.node rl rk (splay (.node a x b) q)) :=
                                  IsBST.node rk rl (splay (.node a x b) q)
                                    hrl_lt_rk hsrr_gt_rk hbst_rl hbst_srr
                                have hright_t' :
                                    ForallTree (fun z => k < z)
                                      (.node rl rk
                                        (splay (.node a x b) q)) :=
                                  ForallTree.node rl rk
                                    (splay (.node a x b) q)
                                    hrl_gt_k hk_lt_rk hsrr_gt_k
                                simpa [hqk, hq_lt_k, hq_lt_rk, hrk_lt_q]
                                  using
                                    rotate_isBST .zagZag
                                      (IsBST.node k l
                                        (.node rl rk
                                          (splay (.node a x b) q))
                                        hleft hright_t' hbst_left hbst_t')
                          · simpa [hqk, hq_lt_k, hq_lt_rk, hrk_lt_q] using
                              rotate_isBST .zag
                                (IsBST.node k l (.node rl rk rr)
                                  hleft
                                  (ForallTree.node rl rk rr
                                    hrl_gt_k hk_lt_rk hrr_gt_k)
                                  hbst_left
                                  (IsBST.node rk rl rr
                                    hrl_lt_rk hrk_lt_rr hbst_rl hbst_rr))


def searchPath (q : Nat) : BinaryTree → List Nat
  | .empty => []
  | .node l k r =>
      if q = k then [k]
      else if q < k then k :: searchPath q l
      else k :: searchPath q r

theorem searchPath_subset_toKeyList (q : Nat) (t : BinaryTree) :
    ∀ y ∈ searchPath q t, y ∈ t.toKeyList := by
  induction t with
  | empty =>
    intro y hy
    simp [searchPath] at hy
  | node l k r ihl ihr =>
    intro y hy
    simp only [searchPath] at hy
    simp only [BinaryTree.toKeyList, List.append_assoc, List.mem_append,
      List.mem_singleton]
    split_ifs at hy with h1 h2
    · simp only [List.mem_singleton] at hy
      exact Or.inr (Or.inl hy)
    · rcases List.mem_cons.mp hy with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl (ihl y h)
    · rcases List.mem_cons.mp hy with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (ihr y h))

def keyDepth (y : Nat) (t : BinaryTree) : Nat := (searchPath y t).length

@[simp] theorem keyDepth_empty (y : Nat) : keyDepth y .empty = 0 := rfl

theorem keyDepth_node (y k : Nat) (l r : BinaryTree) :
    keyDepth y (.node l k r)
      = if y = k then 1 else if y < k then keyDepth y l + 1 else keyDepth y r + 1 := by
  simp only [keyDepth, searchPath]
  by_cases h1 : y = k
  · simp [h1]
  · by_cases h2 : y < k <;> simp [h1, h2]

theorem forallTree_node_iff {p : Nat → Prop} {l r : BinaryTree} {k : Nat} :
    ForallTree p (.node l k r) ↔ ForallTree p l ∧ p k ∧ ForallTree p r := by
  constructor
  · intro h
    cases h
    exact ⟨by assumption, by assumption, by assumption⟩
  · rintro ⟨hl, hk, hr⟩
    exact ForallTree.node l k r hl hk hr

theorem isBST_node_iff {l r : BinaryTree} {k : Nat} :
    IsBST (.node l k r) ↔
      ForallTree (fun x => x < k) l ∧ ForallTree (fun x => k < x) r ∧ IsBST l ∧ IsBST r := by
  constructor
  · intro h
    cases h
    exact ⟨by assumption, by assumption, by assumption, by assumption⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact IsBST.node k l r h1 h2 h3 h4

/-- Fuel-indexed: `splay` preserves any `ForallTree` predicate (it only rearranges keys). -/

-- ===== L2 halving (depth lemmas) =====
theorem searchPath_node_self {q k : Nat} (h : q = k) (l r : BinaryTree) :
    searchPath q (.node l k r) = [k] := by
  simp only [searchPath, if_pos h]

theorem searchPath_node_lt {q k : Nat} (h : q < k) (l r : BinaryTree) :
    searchPath q (.node l k r) = k :: searchPath q l := by
  simp only [searchPath, if_neg (Nat.ne_of_lt h), if_pos h]

theorem searchPath_node_gt {q k : Nat} (h : k < q) (l r : BinaryTree) :
    searchPath q (.node l k r) = k :: searchPath q r := by
  have h1 : q ≠ k := by omega
  have h2 : ¬ q < k := by omega
  simp only [searchPath, if_neg h1, if_neg h2]

theorem keyDepth_node_self {y k : Nat} (h : y = k) (l r : BinaryTree) :
    keyDepth y (.node l k r) = 1 := by
  simp [keyDepth, searchPath_node_self h]

theorem keyDepth_node_lt {y k : Nat} (h : y < k) (l r : BinaryTree) :
    keyDepth y (.node l k r) = keyDepth y l + 1 := by
  simp [keyDepth, searchPath_node_lt h]

theorem keyDepth_node_gt {y k : Nat} (h : k < y) (l r : BinaryTree) :
    keyDepth y (.node l k r) = keyDepth y r + 1 := by
  simp [keyDepth, searchPath_node_gt h]

theorem mem_searchPath_forall {p : Nat → Prop} {q y : Nat} :
    ∀ {t : BinaryTree}, ForallTree p t → y ∈ searchPath q t → p y := by
  intro t
  induction t with
  | empty => intro _ hy; simp [searchPath] at hy
  | node l k r ihl ihr =>
    intro h hy
    rcases forallTree_node_iff.mp h with ⟨hl, hk, hr⟩
    by_cases hqk : q = k
    · rw [searchPath_node_self hqk] at hy
      simp only [List.mem_singleton] at hy
      exact hy ▸ hk
    · by_cases hqlt : q < k
      · rw [searchPath_node_lt hqlt] at hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hk
        · exact ihl hl hy
      · have hklt : k < q := by omega
        rw [searchPath_node_gt hklt] at hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hk
        · exact ihr hr hy

/-- Splaying a nonempty tree gives a nonempty tree. -/

theorem splay_ne_empty (l r : BinaryTree) (k q : Nat) :
    splay (.node l k r) q ≠ .empty := by
  rw [splay.eq_def]
  by_cases hqk : q = k
  · simp only [if_pos hqk]
    exact fun h => nomatch h
  · simp only [if_neg hqk]
    by_cases hqlt : q < k
    · simp only [if_pos hqlt]
      cases l with
      | empty => exact fun h => nomatch h
      | node ll lk lr =>
        by_cases hqlk : q < lk
        · simp only [if_pos hqlk]
          cases ll with
          | empty => exact fun h => nomatch h
          | node a x b =>
            cases hs : splay (.node a x b) q with
            | empty => exact fun h => nomatch h
            | node A s B => exact fun h => nomatch h
        · simp only [if_neg hqlk]
          by_cases hlkq : lk < q
          · simp only [if_pos hlkq]
            cases lr with
            | empty => exact fun h => nomatch h
            | node a x b =>
              cases hs : splay (.node a x b) q with
              | empty => exact fun h => nomatch h
              | node A s B => exact fun h => nomatch h
          · simp only [if_neg hlkq]
            exact fun h => nomatch h
    · simp only [if_neg hqlt]
      cases r with
      | empty => exact fun h => nomatch h
      | node rl rk rr =>
        by_cases hqrk : q < rk
        · simp only [if_pos hqrk]
          cases rl with
          | empty => exact fun h => nomatch h
          | node a x b =>
            cases hs : splay (.node a x b) q with
            | empty => exact fun h => nomatch h
            | node A s B => exact fun h => nomatch h
        · simp only [if_neg hqrk]
          by_cases hrkq : rk < q
          · simp only [if_pos hrkq]
            cases rr with
            | empty => exact fun h => nomatch h
            | node a x b =>
              cases hs : splay (.node a x b) q with
              | empty => exact fun h => nomatch h
              | node A s B => exact fun h => nomatch h
          · simp only [if_neg hrkq]
            exact fun h => nomatch h

/-! ## Shape lemmas (deque-file versions, generalized to an arbitrary result root `s`) -/

theorem splay_zigzig_shape (ll lr r A B : BinaryTree) (lk k q s : Nat)
    (hnk : q ≠ k) (hqlt : q < k) (hqllt : q < lk)
    (hll : ll ≠ .empty)
    (hS : splay ll q = .node A s B) :
    splay (.node (.node ll lk lr) k r) q
      = .node A s (.node B lk (.node lr k r)) := by
  cases ll with
  | empty => exact absurd rfl hll
  | node a b c =>
    rw [splay.eq_def]
    simp only [if_neg hnk, if_pos hqlt, if_pos hqllt]
    rw [hS]
    simp [rotate, rotateRight]

theorem splay_zigzag_shape (ll lr r A B : BinaryTree) (lk k q s : Nat)
    (hnk : q ≠ k) (hqlt : q < k) (hlkq : lk < q)
    (hlr : lr ≠ .empty)
    (hS : splay lr q = .node A s B) :
    splay (.node (.node ll lk lr) k r) q
      = .node (.node ll lk A) s (.node B k r) := by
  have hnot : ¬ q < lk := by omega
  cases lr with
  | empty => exact absurd rfl hlr
  | node a b c =>
    rw [splay.eq_def]
    simp only [if_neg hnk, if_pos hqlt, if_neg hnot, if_pos hlkq]
    rw [hS]
    simp [rotate, rotateRight, rotateLeft]

theorem splay_zagzag_shape (l rl rr A B : BinaryTree) (rk k q s : Nat)
    (hnk : q ≠ k) (hklt : k < q) (hrkq : rk < q)
    (hrr : rr ≠ .empty)
    (hS : splay rr q = .node A s B) :
    splay (.node l k (.node rl rk rr)) q
      = .node (.node (.node l k rl) rk A) s B := by
  have hnlt : ¬ q < k := by omega
  have hnqrk : ¬ q < rk := by omega
  cases rr with
  | empty => exact absurd rfl hrr
  | node a b c =>
    rw [splay.eq_def]
    simp only [if_neg hnk, if_neg hnlt, if_neg hnqrk, if_pos hrkq]
    rw [hS]
    simp [rotate, rotateLeft]

theorem splay_zagzig_shape (l rl rr A B : BinaryTree) (rk k q s : Nat)
    (hnk : q ≠ k) (hklt : k < q) (hqrk : q < rk)
    (hrl : rl ≠ .empty)
    (hS : splay rl q = .node A s B) :
    splay (.node l k (.node rl rk rr)) q
      = .node (.node l k A) s (.node B rk rr) := by
  have hnlt : ¬ q < k := by omega
  cases rl with
  | empty => exact absurd rfl hrl
  | node a b c =>
    rw [splay.eq_def]
    simp only [if_neg hnk, if_neg hnlt, if_pos hqrk]
    rw [hS]
    simp [rotate, rotateLeft, rotateRight]

/-- Splay only rearranges the tree, so it preserves any `ForallTree` predicate.
(Fuel-indexed, strong induction on `num_nodes`.) -/

theorem splay_forall_aux (p : Nat → Prop) :
    ∀ (n : Nat) (t : BinaryTree), t.num_nodes ≤ n → ∀ (q : Nat),
      ForallTree p t → ForallTree p (splay t q) := by
  intro n
  induction n with
  | zero =>
    intro t ht q hp
    cases t with
    | empty => exact hp
    | node l k r =>
      exfalso
      have hnn : (BinaryTree.node l k r).num_nodes = 1 + l.num_nodes + r.num_nodes := rfl
      omega
  | succ n ih =>
    intro t ht q hp
    cases t with
    | empty => exact hp
    | node l k r =>
      rcases forallTree_node_iff.mp hp with ⟨hpl, hpk, hpr⟩
      by_cases hqk : q = k
      · rw [splay.eq_def]
        simp only [if_pos hqk]
        exact hp
      · by_cases hqlt : q < k
        · cases l with
          | empty =>
            rw [splay.eq_def]
            simp only [if_neg hqk, if_pos hqlt]
            exact hp
          | node ll lk lr =>
            rcases forallTree_node_iff.mp hpl with ⟨hpll, hplk, hplr⟩
            by_cases hqlk : q < lk
            · cases ll with
              | empty =>
                rw [splay.eq_def]
                simp only [if_neg hqk, if_pos hqlt, if_pos hqlk]
                show ForallTree p (.node .empty lk (.node lr k r))
                exact .node _ _ _ .left hplk (.node _ _ _ hplr hpk hpr)
              | node a x b =>
                have hsz : (BinaryTree.node a x b).num_nodes ≤ n := by
                  have hnn : (BinaryTree.node (BinaryTree.node (BinaryTree.node a x b) lk lr)
                      k r).num_nodes
                      = 1 + (1 + (BinaryTree.node a x b).num_nodes + lr.num_nodes)
                        + r.num_nodes := rfl
                  omega
                have hrec := ih _ hsz q hpll
                cases hs : splay (BinaryTree.node a x b) q with
                | empty => exact absurd hs (splay_ne_empty _ _ _ _)
                | node A s B =>
                  rw [splay_zigzig_shape (BinaryTree.node a x b) lr r A B lk k q s hqk hqlt
                    hqlk (fun h => nomatch h) hs]
                  rw [hs] at hrec
                  rcases forallTree_node_iff.mp hrec with ⟨hA, hsP, hB⟩
                  exact .node _ _ _ hA hsP
                    (.node _ _ _ hB hplk (.node _ _ _ hplr hpk hpr))
            · by_cases hlkq : lk < q
              · cases lr with
                | empty =>
                  rw [splay.eq_def]
                  simp only [if_neg hqk, if_pos hqlt, if_neg hqlk, if_pos hlkq]
                  show ForallTree p (.node ll lk (.node .empty k r))
                  exact .node _ _ _ hpll hplk (.node _ _ _ .left hpk hpr)
                | node a x b =>
                  have hsz : (BinaryTree.node a x b).num_nodes ≤ n := by
                    have hnn : (BinaryTree.node (BinaryTree.node ll lk (BinaryTree.node a x b))
                        k r).num_nodes
                        = 1 + (1 + ll.num_nodes + (BinaryTree.node a x b).num_nodes)
                          + r.num_nodes := rfl
                    omega
                  have hrec := ih _ hsz q hplr
                  cases hs : splay (BinaryTree.node a x b) q with
                  | empty => exact absurd hs (splay_ne_empty _ _ _ _)
                  | node A s B =>
                    rw [splay_zigzag_shape ll (BinaryTree.node a x b) r A B lk k q s hqk hqlt
                      hlkq (fun h => nomatch h) hs]
                    rw [hs] at hrec
                    rcases forallTree_node_iff.mp hrec with ⟨hA, hsP, hB⟩
                    exact .node _ _ _ (.node _ _ _ hpll hplk hA) hsP
                      (.node _ _ _ hB hpk hpr)
              · rw [splay.eq_def]
                simp only [if_neg hqk, if_pos hqlt, if_neg hqlk, if_neg hlkq]
                show ForallTree p (.node ll lk (.node lr k r))
                exact .node _ _ _ hpll hplk (.node _ _ _ hplr hpk hpr)
        · have hklt : k < q := by omega
          cases r with
          | empty =>
            rw [splay.eq_def]
            simp only [if_neg hqk, if_neg hqlt]
            exact hp
          | node rl rk rr =>
            rcases forallTree_node_iff.mp hpr with ⟨hprl, hprk, hprr⟩
            by_cases hqrk : q < rk
            · cases rl with
              | empty =>
                rw [splay.eq_def]
                simp only [if_neg hqk, if_neg hqlt, if_pos hqrk]
                show ForallTree p (.node (.node l k .empty) rk rr)
                exact .node _ _ _ (.node _ _ _ hpl hpk .left) hprk hprr
              | node a x b =>
                have hsz : (BinaryTree.node a x b).num_nodes ≤ n := by
                  have hnn : (BinaryTree.node l k
                      (BinaryTree.node (BinaryTree.node a x b) rk rr)).num_nodes
                      = 1 + l.num_nodes
                        + (1 + (BinaryTree.node a x b).num_nodes + rr.num_nodes) := rfl
                  omega
                have hrec := ih _ hsz q hprl
                cases hs : splay (BinaryTree.node a x b) q with
                | empty => exact absurd hs (splay_ne_empty _ _ _ _)
                | node A s B =>
                  rw [splay_zagzig_shape l (BinaryTree.node a x b) rr A B rk k q s hqk hklt
                    hqrk (fun h => nomatch h) hs]
                  rw [hs] at hrec
                  rcases forallTree_node_iff.mp hrec with ⟨hA, hsP, hB⟩
                  exact .node _ _ _ (.node _ _ _ hpl hpk hA) hsP
                    (.node _ _ _ hB hprk hprr)
            · by_cases hrkq : rk < q
              · cases rr with
                | empty =>
                  rw [splay.eq_def]
                  simp only [if_neg hqk, if_neg hqlt, if_neg hqrk, if_pos hrkq]
                  show ForallTree p (.node (.node l k rl) rk .empty)
                  exact .node _ _ _ (.node _ _ _ hpl hpk hprl) hprk .left
                | node a x b =>
                  have hsz : (BinaryTree.node a x b).num_nodes ≤ n := by
                    have hnn : (BinaryTree.node l k
                        (BinaryTree.node rl rk (BinaryTree.node a x b))).num_nodes
                        = 1 + l.num_nodes
                          + (1 + rl.num_nodes + (BinaryTree.node a x b).num_nodes) := rfl
                    omega
                  have hrec := ih _ hsz q hprr
                  cases hs : splay (BinaryTree.node a x b) q with
                  | empty => exact absurd hs (splay_ne_empty _ _ _ _)
                  | node A s B =>
                    rw [splay_zagzag_shape l rl (BinaryTree.node a x b) A B rk k q s hqk hklt
                      hrkq (fun h => nomatch h) hs]
                    rw [hs] at hrec
                    rcases forallTree_node_iff.mp hrec with ⟨hA, hsP, hB⟩
                    exact .node _ _ _
                      (.node _ _ _ (.node _ _ _ hpl hpk hprl) hprk hA) hsP hB
              · rw [splay.eq_def]
                simp only [if_neg hqk, if_neg hqlt, if_neg hqrk, if_neg hrkq]
                show ForallTree p (.node (.node l k rl) rk rr)
                exact .node _ _ _ (.node _ _ _ hpl hpk hprl) hprk hprr

theorem splay_forall (p : Nat → Prop) (t : BinaryTree) (q : Nat)
    (h : ForallTree p t) : ForallTree p (splay t q) :=
  splay_forall_aux p t.num_nodes t (Nat.le_refl _) q h

/-! ## The path-halving lemma -/

/-- Fuel-indexed version of `keyDepth_splay_halving`, strong induction on `num_nodes`. -/

theorem keyDepth_splay_halving_aux :
    ∀ (n : Nat) (t : BinaryTree), t.num_nodes ≤ n → ∀ (q y : Nat),
      IsBST t → y ∈ searchPath q t →
      2 * keyDepth y (splay t q) ≤ keyDepth y t + 5 := by
  intro n
  induction n with
  | zero =>
    intro t ht q y _ hy
    cases t with
    | empty => simp [searchPath] at hy
    | node l k r =>
      exfalso
      have hnn : (BinaryTree.node l k r).num_nodes = 1 + l.num_nodes + r.num_nodes := rfl
      omega
  | succ n ih =>
    intro t ht q y hbst hy
    cases t with
    | empty => simp [searchPath] at hy
    | node l k r =>
      rcases isBST_node_iff.mp hbst with ⟨hfl, hfr, hbl, hbr⟩
      by_cases hqk : q = k
      · -- q found at the root: splay returns t, and y = k has depth 1
        rw [searchPath_node_self hqk] at hy
        simp only [List.mem_singleton] at hy
        rw [splay.eq_def]
        simp only [if_pos hqk]
        have h1 : keyDepth y (BinaryTree.node l k r) = 1 := keyDepth_node_self hy _ _
        omega
      · by_cases hqlt : q < k
        · rw [searchPath_node_lt hqlt] at hy
          cases l with
          | empty =>
            -- q not found, root unchanged; path = [k]
            simp only [searchPath, List.mem_cons, List.not_mem_nil, or_false] at hy
            rw [splay.eq_def]
            simp only [if_neg hqk, if_pos hqlt]
            have h1 : keyDepth y (BinaryTree.node .empty k r) = 1 := keyDepth_node_self hy _ _
            omega
          | node ll lk lr =>
            rcases forallTree_node_iff.mp hfl with ⟨hfll, hlkk, hflr⟩
            rcases isBST_node_iff.mp hbl with ⟨hll_lt, hlr_gt, hbll, hblr⟩
            by_cases hqlk : q < lk
            · rw [searchPath_node_lt hqlk] at hy
              cases ll with
              | empty =>
                -- zig with empty grandchild: result = node empty lk (node lr k r)
                simp only [searchPath, List.mem_cons, List.not_mem_nil, or_false] at hy
                rw [splay.eq_def]
                simp only [if_neg hqk, if_pos hqlt, if_pos hqlk]
                show 2 * keyDepth y (BinaryTree.node .empty lk (BinaryTree.node lr k r))
                    ≤ keyDepth y (BinaryTree.node (BinaryTree.node .empty lk lr) k r) + 5
                rcases hy with hy | hy
                · -- y = k : depth 1 → 2
                  have h1 : keyDepth y (BinaryTree.node .empty lk (BinaryTree.node lr k r))
                      = keyDepth y (BinaryTree.node lr k r) + 1 :=
                    keyDepth_node_gt (by omega) _ _
                  have h2 : keyDepth y (BinaryTree.node lr k r) = 1 := keyDepth_node_self hy _ _
                  have h3 : keyDepth y (BinaryTree.node (BinaryTree.node .empty lk lr) k r) = 1 :=
                    keyDepth_node_self hy _ _
                  omega
                · -- y = lk : depth 2 → 1
                  have h1 : keyDepth y (BinaryTree.node .empty lk (BinaryTree.node lr k r)) = 1 :=
                    keyDepth_node_self hy _ _
                  have h2 : keyDepth y (BinaryTree.node (BinaryTree.node .empty lk lr) k r)
                      = keyDepth y (BinaryTree.node .empty lk lr) + 1 :=
                    keyDepth_node_lt (by omega) _ _
                  omega
              | node a x b =>
                -- ZIG-ZIG
                have hsz : (BinaryTree.node a x b).num_nodes ≤ n := by
                  have hnn : (BinaryTree.node
                      (BinaryTree.node (BinaryTree.node a x b) lk lr) k r).num_nodes
                      = 1 + (1 + (BinaryTree.node a x b).num_nodes + lr.num_nodes)
                        + r.num_nodes := rfl
                  omega
                cases hs : splay (BinaryTree.node a x b) q with
                | empty => exact absurd hs (splay_ne_empty _ _ _ _)
                | node A s B =>
                  have hsA : ForallTree (fun z => z < lk) (splay (BinaryTree.node a x b) q) :=
                    splay_forall _ _ _ hll_lt
                  rw [hs] at hsA
                  rcases forallTree_node_iff.mp hsA with ⟨hAlt, hslk, hBlt⟩
                  rw [splay_zigzig_shape (BinaryTree.node a x b) lr r A B lk k q s hqk hqlt
                    hqlk (fun h => nomatch h) hs]
                  simp only [List.mem_cons] at hy
                  rcases hy with hy | hy | hy'
                  · -- y = k : depth 1 → 3 (the tight case, 2*3 = 1+5)
                    have h1 : keyDepth y
                        (BinaryTree.node A s (BinaryTree.node B lk (BinaryTree.node lr k r)))
                        = keyDepth y (BinaryTree.node B lk (BinaryTree.node lr k r)) + 1 :=
                      keyDepth_node_gt (by omega) _ _
                    have h2 : keyDepth y (BinaryTree.node B lk (BinaryTree.node lr k r))
                        = keyDepth y (BinaryTree.node lr k r) + 1 :=
                      keyDepth_node_gt (by omega) _ _
                    have h3 : keyDepth y (BinaryTree.node lr k r) = 1 := keyDepth_node_self hy _ _
                    have h4 : keyDepth y (BinaryTree.node
                        (BinaryTree.node (BinaryTree.node a x b) lk lr) k r) = 1 :=
                      keyDepth_node_self hy _ _
                    omega
                  · -- y = lk : depth 2 → 2
                    have h1 : keyDepth y
                        (BinaryTree.node A s (BinaryTree.node B lk (BinaryTree.node lr k r)))
                        = keyDepth y (BinaryTree.node B lk (BinaryTree.node lr k r)) + 1 :=
                      keyDepth_node_gt (by omega) _ _
                    have h2 : keyDepth y (BinaryTree.node B lk (BinaryTree.node lr k r)) = 1 :=
                      keyDepth_node_self hy _ _
                    have h3 : keyDepth y (BinaryTree.node
                        (BinaryTree.node (BinaryTree.node a x b) lk lr) k r)
                        = keyDepth y (BinaryTree.node (BinaryTree.node a x b) lk lr) + 1 :=
                      keyDepth_node_lt (by omega) _ _
                    have h4 : keyDepth y (BinaryTree.node (BinaryTree.node a x b) lk lr) = 1 :=
                      keyDepth_node_self hy _ _
                    omega
                  · -- y on the path inside the grandchild: use the IH, embedding offset ≤ 1
                    have hIH := ih _ hsz q y hbll hy'
                    rw [hs] at hIH
                    have hylk : y < lk :=
                      mem_searchPath_forall (p := fun z => z < lk) hll_lt hy'
                    have h3 : keyDepth y (BinaryTree.node
                        (BinaryTree.node (BinaryTree.node a x b) lk lr) k r)
                        = keyDepth y (BinaryTree.node (BinaryTree.node a x b) lk lr) + 1 :=
                      keyDepth_node_lt (by omega) _ _
                    have h4 : keyDepth y (BinaryTree.node (BinaryTree.node a x b) lk lr)
                        = keyDepth y (BinaryTree.node a x b) + 1 :=
                      keyDepth_node_lt (by omega) _ _
                    rcases Nat.lt_trichotomy y s with hys | hys | hys
                    · have h1 : keyDepth y
                          (BinaryTree.node A s (BinaryTree.node B lk (BinaryTree.node lr k r)))
                          = keyDepth y A + 1 := keyDepth_node_lt hys _ _
                      have h2 : keyDepth y (BinaryTree.node A s B) = keyDepth y A + 1 :=
                        keyDepth_node_lt hys _ _
                      omega
                    · have h1 : keyDepth y
                          (BinaryTree.node A s (BinaryTree.node B lk (BinaryTree.node lr k r)))
                          = 1 := keyDepth_node_self hys _ _
                      omega
                    · have h1 : keyDepth y
                          (BinaryTree.node A s (BinaryTree.node B lk (BinaryTree.node lr k r)))
                          = keyDepth y (BinaryTree.node B lk (BinaryTree.node lr k r)) + 1 :=
                        keyDepth_node_gt hys _ _
                      have h2 : keyDepth y (BinaryTree.node B lk (BinaryTree.node lr k r))
                          = keyDepth y B + 1 := keyDepth_node_lt (by omega) _ _
                      have h5 : keyDepth y (BinaryTree.node A s B) = keyDepth y B + 1 :=
                        keyDepth_node_gt hys _ _
                      omega
            · by_cases hlkq : lk < q
              · rw [searchPath_node_gt hlkq] at hy
                cases lr with
                | empty =>
                  -- zig with empty grandchild
                  simp only [searchPath, List.mem_cons, List.not_mem_nil, or_false] at hy
                  rw [splay.eq_def]
                  simp only [if_neg hqk, if_pos hqlt, if_neg hqlk, if_pos hlkq]
                  show 2 * keyDepth y (BinaryTree.node ll lk (BinaryTree.node .empty k r))
                      ≤ keyDepth y (BinaryTree.node (BinaryTree.node ll lk .empty) k r) + 5
                  rcases hy with hy | hy
                  · have h1 : keyDepth y (BinaryTree.node ll lk (BinaryTree.node .empty k r))
                        = keyDepth y (BinaryTree.node .empty k r) + 1 :=
                      keyDepth_node_gt (by omega) _ _
                    have h2 : keyDepth y (BinaryTree.node .empty k r) = 1 :=
                      keyDepth_node_self hy _ _
                    have h3 : keyDepth y (BinaryTree.node (BinaryTree.node ll lk .empty) k r)
                        = 1 := keyDepth_node_self hy _ _
                    omega
                  · have h1 : keyDepth y (BinaryTree.node ll lk (BinaryTree.node .empty k r))
                        = 1 := keyDepth_node_self hy _ _
                    have h2 : keyDepth y (BinaryTree.node (BinaryTree.node ll lk .empty) k r)
                        = keyDepth y (BinaryTree.node ll lk .empty) + 1 :=
                      keyDepth_node_lt (by omega) _ _
                    omega
                | node a x b =>
                  -- ZIG-ZAG
                  have hsz : (BinaryTree.node a x b).num_nodes ≤ n := by
                    have hnn : (BinaryTree.node
                        (BinaryTree.node ll lk (BinaryTree.node a x b)) k r).num_nodes
                        = 1 + (1 + ll.num_nodes + (BinaryTree.node a x b).num_nodes)
                          + r.num_nodes := rfl
                    omega
                  cases hs : splay (BinaryTree.node a x b) q with
                  | empty => exact absurd hs (splay_ne_empty _ _ _ _)
                  | node A s B =>
                    have hsA : ForallTree (fun z => lk < z) (splay (BinaryTree.node a x b) q) :=
                      splay_forall _ _ _ hlr_gt
                    rw [hs] at hsA
                    rcases forallTree_node_iff.mp hsA with ⟨hAgt, hlks, hBgt⟩
                    have hsK : ForallTree (fun z => z < k) (splay (BinaryTree.node a x b) q) :=
                      splay_forall _ _ _ hflr
                    rw [hs] at hsK
                    rcases forallTree_node_iff.mp hsK with ⟨hAk, hsk, hBk⟩
                    rw [splay_zigzag_shape ll (BinaryTree.node a x b) r A B lk k q s hqk hqlt
                      hlkq (fun h => nomatch h) hs]
                    simp only [List.mem_cons] at hy
                    rcases hy with hy | hy | hy'
                    · -- y = k : depth 1 → 2
                      have h1 : keyDepth y
                          (BinaryTree.node (BinaryTree.node ll lk A) s (BinaryTree.node B k r))
                          = keyDepth y (BinaryTree.node B k r) + 1 :=
                        keyDepth_node_gt (by omega) _ _
                      have h2 : keyDepth y (BinaryTree.node B k r) = 1 :=
                        keyDepth_node_self hy _ _
                      have h3 : keyDepth y (BinaryTree.node
                          (BinaryTree.node ll lk (BinaryTree.node a x b)) k r) = 1 :=
                        keyDepth_node_self hy _ _
                      omega
                    · -- y = lk : depth 2 → 2
                      have h1 : keyDepth y
                          (BinaryTree.node (BinaryTree.node ll lk A) s (BinaryTree.node B k r))
                          = keyDepth y (BinaryTree.node ll lk A) + 1 :=
                        keyDepth_node_lt (by omega) _ _
                      have h2 : keyDepth y (BinaryTree.node ll lk A) = 1 :=
                        keyDepth_node_self hy _ _
                      have h3 : keyDepth y (BinaryTree.node
                          (BinaryTree.node ll lk (BinaryTree.node a x b)) k r)
                          = keyDepth y (BinaryTree.node ll lk (BinaryTree.node a x b)) + 1 :=
                        keyDepth_node_lt (by omega) _ _
                      have h4 : keyDepth y (BinaryTree.node ll lk (BinaryTree.node a x b)) = 1 :=
                        keyDepth_node_self hy _ _
                      omega
                    · -- y on the path inside the grandchild
                      have hIH := ih _ hsz q y hblr hy'
                      rw [hs] at hIH
                      have hlky : lk < y := mem_searchPath_forall hlr_gt hy'
                      have hyk : y < k :=
                        mem_searchPath_forall (p := fun z => z < k) hflr hy'
                      have h3 : keyDepth y (BinaryTree.node
                          (BinaryTree.node ll lk (BinaryTree.node a x b)) k r)
                          = keyDepth y (BinaryTree.node ll lk (BinaryTree.node a x b)) + 1 :=
                        keyDepth_node_lt hyk _ _
                      have h4 : keyDepth y (BinaryTree.node ll lk (BinaryTree.node a x b))
                          = keyDepth y (BinaryTree.node a x b) + 1 :=
                        keyDepth_node_gt hlky _ _
                      rcases Nat.lt_trichotomy y s with hys | hys | hys
                      · have h1 : keyDepth y
                            (BinaryTree.node (BinaryTree.node ll lk A) s (BinaryTree.node B k r))
                            = keyDepth y (BinaryTree.node ll lk A) + 1 :=
                          keyDepth_node_lt hys _ _
                        have h2 : keyDepth y (BinaryTree.node ll lk A)
                            = keyDepth y A + 1 := keyDepth_node_gt hlky _ _
                        have h5 : keyDepth y (BinaryTree.node A s B) = keyDepth y A + 1 :=
                          keyDepth_node_lt hys _ _
                        omega
                      · have h1 : keyDepth y
                            (BinaryTree.node (BinaryTree.node ll lk A) s (BinaryTree.node B k r))
                            = 1 := keyDepth_node_self hys _ _
                        omega
                      · have h1 : keyDepth y
                            (BinaryTree.node (BinaryTree.node ll lk A) s (BinaryTree.node B k r))
                            = keyDepth y (BinaryTree.node B k r) + 1 :=
                          keyDepth_node_gt hys _ _
                        have h2 : keyDepth y (BinaryTree.node B k r)
                            = keyDepth y B + 1 := keyDepth_node_lt hyk _ _
                        have h5 : keyDepth y (BinaryTree.node A s B) = keyDepth y B + 1 :=
                          keyDepth_node_gt hys _ _
                        omega
              · -- q found at the left child (q = lk): single zig
                have hqlk_eq : q = lk := by omega
                rw [searchPath_node_self hqlk_eq] at hy
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
                rw [splay.eq_def]
                simp only [if_neg hqk, if_pos hqlt, if_neg hqlk, if_neg hlkq]
                show 2 * keyDepth y (BinaryTree.node ll lk (BinaryTree.node lr k r))
                    ≤ keyDepth y (BinaryTree.node (BinaryTree.node ll lk lr) k r) + 5
                rcases hy with hy | hy
                · have h1 : keyDepth y (BinaryTree.node ll lk (BinaryTree.node lr k r))
                      = keyDepth y (BinaryTree.node lr k r) + 1 := keyDepth_node_gt (by omega) _ _
                  have h2 : keyDepth y (BinaryTree.node lr k r) = 1 := keyDepth_node_self hy _ _
                  have h3 : keyDepth y (BinaryTree.node (BinaryTree.node ll lk lr) k r) = 1 :=
                    keyDepth_node_self hy _ _
                  omega
                · have h1 : keyDepth y (BinaryTree.node ll lk (BinaryTree.node lr k r)) = 1 :=
                    keyDepth_node_self hy _ _
                  have h2 : keyDepth y (BinaryTree.node (BinaryTree.node ll lk lr) k r)
                      = keyDepth y (BinaryTree.node ll lk lr) + 1 := keyDepth_node_lt (by omega) _ _
                  omega
        · -- k < q : symmetric (zag) side
          have hklt : k < q := by omega
          rw [searchPath_node_gt hklt] at hy
          cases r with
          | empty =>
            simp only [searchPath, List.mem_cons, List.not_mem_nil, or_false] at hy
            rw [splay.eq_def]
            simp only [if_neg hqk, if_neg hqlt]
            have h1 : keyDepth y (BinaryTree.node l k .empty) = 1 := keyDepth_node_self hy _ _
            omega
          | node rl rk rr =>
            rcases forallTree_node_iff.mp hfr with ⟨hfrl, hkrk, hfrr⟩
            rcases isBST_node_iff.mp hbr with ⟨hrl_lt, hrr_gt, hbrl, hbrr⟩
            by_cases hqrk : q < rk
            · rw [searchPath_node_lt hqrk] at hy
              cases rl with
              | empty =>
                -- zag with empty grandchild: result = node (node l k empty) rk rr
                simp only [searchPath, List.mem_cons, List.not_mem_nil, or_false] at hy
                rw [splay.eq_def]
                simp only [if_neg hqk, if_neg hqlt, if_pos hqrk]
                show 2 * keyDepth y (BinaryTree.node (BinaryTree.node l k .empty) rk rr)
                    ≤ keyDepth y (BinaryTree.node l k (BinaryTree.node .empty rk rr)) + 5
                rcases hy with hy | hy
                · have h1 : keyDepth y (BinaryTree.node (BinaryTree.node l k .empty) rk rr)
                      = keyDepth y (BinaryTree.node l k .empty) + 1 :=
                    keyDepth_node_lt (by omega) _ _
                  have h2 : keyDepth y (BinaryTree.node l k .empty) = 1 :=
                    keyDepth_node_self hy _ _
                  have h3 : keyDepth y (BinaryTree.node l k (BinaryTree.node .empty rk rr)) = 1 :=
                    keyDepth_node_self hy _ _
                  omega
                · have h1 : keyDepth y (BinaryTree.node (BinaryTree.node l k .empty) rk rr) = 1 :=
                    keyDepth_node_self hy _ _
                  have h2 : keyDepth y (BinaryTree.node l k (BinaryTree.node .empty rk rr))
                      = keyDepth y (BinaryTree.node .empty rk rr) + 1 :=
                    keyDepth_node_gt (by omega) _ _
                  omega
              | node a x b =>
                -- ZAG-ZIG
                have hsz : (BinaryTree.node a x b).num_nodes ≤ n := by
                  have hnn : (BinaryTree.node l k
                      (BinaryTree.node (BinaryTree.node a x b) rk rr)).num_nodes
                      = 1 + l.num_nodes
                        + (1 + (BinaryTree.node a x b).num_nodes + rr.num_nodes) := rfl
                  omega
                cases hs : splay (BinaryTree.node a x b) q with
                | empty => exact absurd hs (splay_ne_empty _ _ _ _)
                | node A s B =>
                  have hsA : ForallTree (fun z => k < z) (splay (BinaryTree.node a x b) q) :=
                    splay_forall _ _ _ hfrl
                  rw [hs] at hsA
                  rcases forallTree_node_iff.mp hsA with ⟨hAgt, hks, hBgt⟩
                  have hsK : ForallTree (fun z => z < rk) (splay (BinaryTree.node a x b) q) :=
                    splay_forall _ _ _ hrl_lt
                  rw [hs] at hsK
                  rcases forallTree_node_iff.mp hsK with ⟨hArk, hsrk, hBrk⟩
                  rw [splay_zagzig_shape l (BinaryTree.node a x b) rr A B rk k q s hqk hklt
                    hqrk (fun h => nomatch h) hs]
                  simp only [List.mem_cons] at hy
                  rcases hy with hy | hy | hy'
                  · -- y = k : depth 1 → 2
                    have h1 : keyDepth y
                        (BinaryTree.node (BinaryTree.node l k A) s (BinaryTree.node B rk rr))
                        = keyDepth y (BinaryTree.node l k A) + 1 :=
                      keyDepth_node_lt (by omega) _ _
                    have h2 : keyDepth y (BinaryTree.node l k A) = 1 := keyDepth_node_self hy _ _
                    have h3 : keyDepth y (BinaryTree.node l k
                        (BinaryTree.node (BinaryTree.node a x b) rk rr)) = 1 :=
                      keyDepth_node_self hy _ _
                    omega
                  · -- y = rk : depth 2 → 2
                    have h1 : keyDepth y
                        (BinaryTree.node (BinaryTree.node l k A) s (BinaryTree.node B rk rr))
                        = keyDepth y (BinaryTree.node B rk rr) + 1 :=
                      keyDepth_node_gt (by omega) _ _
                    have h2 : keyDepth y (BinaryTree.node B rk rr) = 1 :=
                      keyDepth_node_self hy _ _
                    have h3 : keyDepth y (BinaryTree.node l k
                        (BinaryTree.node (BinaryTree.node a x b) rk rr))
                        = keyDepth y (BinaryTree.node (BinaryTree.node a x b) rk rr) + 1 :=
                      keyDepth_node_gt (by omega) _ _
                    have h4 : keyDepth y (BinaryTree.node (BinaryTree.node a x b) rk rr) = 1 :=
                      keyDepth_node_self hy _ _
                    omega
                  · -- y on the path inside the grandchild
                    have hIH := ih _ hsz q y hbrl hy'
                    rw [hs] at hIH
                    have hky : k < y := mem_searchPath_forall hfrl hy'
                    have hyrk : y < rk :=
                      mem_searchPath_forall (p := fun z => z < rk) hrl_lt hy'
                    have h3 : keyDepth y (BinaryTree.node l k
                        (BinaryTree.node (BinaryTree.node a x b) rk rr))
                        = keyDepth y (BinaryTree.node (BinaryTree.node a x b) rk rr) + 1 :=
                      keyDepth_node_gt hky _ _
                    have h4 : keyDepth y (BinaryTree.node (BinaryTree.node a x b) rk rr)
                        = keyDepth y (BinaryTree.node a x b) + 1 := keyDepth_node_lt hyrk _ _
                    rcases Nat.lt_trichotomy y s with hys | hys | hys
                    · have h1 : keyDepth y
                          (BinaryTree.node (BinaryTree.node l k A) s (BinaryTree.node B rk rr))
                          = keyDepth y (BinaryTree.node l k A) + 1 := keyDepth_node_lt hys _ _
                      have h2 : keyDepth y (BinaryTree.node l k A) = keyDepth y A + 1 :=
                        keyDepth_node_gt hky _ _
                      have h5 : keyDepth y (BinaryTree.node A s B) = keyDepth y A + 1 :=
                        keyDepth_node_lt hys _ _
                      omega
                    · have h1 : keyDepth y
                          (BinaryTree.node (BinaryTree.node l k A) s (BinaryTree.node B rk rr))
                          = 1 := keyDepth_node_self hys _ _
                      omega
                    · have h1 : keyDepth y
                          (BinaryTree.node (BinaryTree.node l k A) s (BinaryTree.node B rk rr))
                          = keyDepth y (BinaryTree.node B rk rr) + 1 := keyDepth_node_gt hys _ _
                      have h2 : keyDepth y (BinaryTree.node B rk rr) = keyDepth y B + 1 :=
                        keyDepth_node_lt hyrk _ _
                      have h5 : keyDepth y (BinaryTree.node A s B) = keyDepth y B + 1 :=
                        keyDepth_node_gt hys _ _
                      omega
            · by_cases hrkq : rk < q
              · rw [searchPath_node_gt hrkq] at hy
                cases rr with
                | empty =>
                  -- zag with empty grandchild
                  simp only [searchPath, List.mem_cons, List.not_mem_nil, or_false] at hy
                  rw [splay.eq_def]
                  simp only [if_neg hqk, if_neg hqlt, if_neg hqrk, if_pos hrkq]
                  show 2 * keyDepth y (BinaryTree.node (BinaryTree.node l k rl) rk .empty)
                      ≤ keyDepth y (BinaryTree.node l k (BinaryTree.node rl rk .empty)) + 5
                  rcases hy with hy | hy
                  · have h1 : keyDepth y (BinaryTree.node (BinaryTree.node l k rl) rk .empty)
                        = keyDepth y (BinaryTree.node l k rl) + 1 := keyDepth_node_lt (by omega) _ _
                    have h2 : keyDepth y (BinaryTree.node l k rl) = 1 := keyDepth_node_self hy _ _
                    have h3 : keyDepth y (BinaryTree.node l k (BinaryTree.node rl rk .empty)) = 1 :=
                      keyDepth_node_self hy _ _
                    omega
                  · have h1 : keyDepth y (BinaryTree.node (BinaryTree.node l k rl) rk .empty) = 1 :=
                      keyDepth_node_self hy _ _
                    have h2 : keyDepth y (BinaryTree.node l k (BinaryTree.node rl rk .empty))
                        = keyDepth y (BinaryTree.node rl rk .empty) + 1 :=
                      keyDepth_node_gt (by omega) _ _
                    omega
                | node a x b =>
                  -- ZAG-ZAG
                  have hsz : (BinaryTree.node a x b).num_nodes ≤ n := by
                    have hnn : (BinaryTree.node l k
                        (BinaryTree.node rl rk (BinaryTree.node a x b))).num_nodes
                        = 1 + l.num_nodes
                          + (1 + rl.num_nodes + (BinaryTree.node a x b).num_nodes) := rfl
                    omega
                  cases hs : splay (BinaryTree.node a x b) q with
                  | empty => exact absurd hs (splay_ne_empty _ _ _ _)
                  | node A s B =>
                    have hsA : ForallTree (fun z => rk < z) (splay (BinaryTree.node a x b) q) :=
                      splay_forall _ _ _ hrr_gt
                    rw [hs] at hsA
                    rcases forallTree_node_iff.mp hsA with ⟨hAgt, hrks, hBgt⟩
                    rw [splay_zagzag_shape l rl (BinaryTree.node a x b) A B rk k q s hqk hklt
                      hrkq (fun h => nomatch h) hs]
                    simp only [List.mem_cons] at hy
                    rcases hy with hy | hy | hy'
                    · -- y = k : depth 1 → 3 (the tight case)
                      have h1 : keyDepth y (BinaryTree.node
                          (BinaryTree.node (BinaryTree.node l k rl) rk A) s B)
                          = keyDepth y (BinaryTree.node (BinaryTree.node l k rl) rk A) + 1 :=
                        keyDepth_node_lt (by omega) _ _
                      have h2 : keyDepth y (BinaryTree.node (BinaryTree.node l k rl) rk A)
                          = keyDepth y (BinaryTree.node l k rl) + 1 :=
                        keyDepth_node_lt (by omega) _ _
                      have h3 : keyDepth y (BinaryTree.node l k rl) = 1 :=
                        keyDepth_node_self hy _ _
                      have h4 : keyDepth y (BinaryTree.node l k
                          (BinaryTree.node rl rk (BinaryTree.node a x b))) = 1 :=
                        keyDepth_node_self hy _ _
                      omega
                    · -- y = rk : depth 2 → 2
                      have h1 : keyDepth y (BinaryTree.node
                          (BinaryTree.node (BinaryTree.node l k rl) rk A) s B)
                          = keyDepth y (BinaryTree.node (BinaryTree.node l k rl) rk A) + 1 :=
                        keyDepth_node_lt (by omega) _ _
                      have h2 : keyDepth y (BinaryTree.node (BinaryTree.node l k rl) rk A) = 1 :=
                        keyDepth_node_self hy _ _
                      have h3 : keyDepth y (BinaryTree.node l k
                          (BinaryTree.node rl rk (BinaryTree.node a x b)))
                          = keyDepth y (BinaryTree.node rl rk (BinaryTree.node a x b)) + 1 :=
                        keyDepth_node_gt (by omega) _ _
                      have h4 : keyDepth y (BinaryTree.node rl rk (BinaryTree.node a x b)) = 1 :=
                        keyDepth_node_self hy _ _
                      omega
                    · -- y on the path inside the grandchild
                      have hIH := ih _ hsz q y hbrr hy'
                      rw [hs] at hIH
                      have hrky : rk < y := mem_searchPath_forall hrr_gt hy'
                      have h3 : keyDepth y (BinaryTree.node l k
                          (BinaryTree.node rl rk (BinaryTree.node a x b)))
                          = keyDepth y (BinaryTree.node rl rk (BinaryTree.node a x b)) + 1 :=
                        keyDepth_node_gt (by omega) _ _
                      have h4 : keyDepth y (BinaryTree.node rl rk (BinaryTree.node a x b))
                          = keyDepth y (BinaryTree.node a x b) + 1 :=
                        keyDepth_node_gt hrky _ _
                      rcases Nat.lt_trichotomy y s with hys | hys | hys
                      · have h1 : keyDepth y (BinaryTree.node
                            (BinaryTree.node (BinaryTree.node l k rl) rk A) s B)
                            = keyDepth y (BinaryTree.node (BinaryTree.node l k rl) rk A) + 1 :=
                          keyDepth_node_lt hys _ _
                        have h2 : keyDepth y (BinaryTree.node (BinaryTree.node l k rl) rk A)
                            = keyDepth y A + 1 := keyDepth_node_gt hrky _ _
                        have h5 : keyDepth y (BinaryTree.node A s B) = keyDepth y A + 1 :=
                          keyDepth_node_lt hys _ _
                        omega
                      · have h1 : keyDepth y (BinaryTree.node
                            (BinaryTree.node (BinaryTree.node l k rl) rk A) s B)
                            = 1 := keyDepth_node_self hys _ _
                        omega
                      · have h1 : keyDepth y (BinaryTree.node
                            (BinaryTree.node (BinaryTree.node l k rl) rk A) s B)
                            = keyDepth y B + 1 := keyDepth_node_gt hys _ _
                        have h5 : keyDepth y (BinaryTree.node A s B) = keyDepth y B + 1 :=
                          keyDepth_node_gt hys _ _
                        omega
              · -- q found at the right child (q = rk): single zag
                have hqrk_eq : q = rk := by omega
                rw [searchPath_node_self hqrk_eq] at hy
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
                rw [splay.eq_def]
                simp only [if_neg hqk, if_neg hqlt, if_neg hqrk, if_neg hrkq]
                show 2 * keyDepth y (BinaryTree.node (BinaryTree.node l k rl) rk rr)
                    ≤ keyDepth y (BinaryTree.node l k (BinaryTree.node rl rk rr)) + 5
                rcases hy with hy | hy
                · have h1 : keyDepth y (BinaryTree.node (BinaryTree.node l k rl) rk rr)
                      = keyDepth y (BinaryTree.node l k rl) + 1 := keyDepth_node_lt (by omega) _ _
                  have h2 : keyDepth y (BinaryTree.node l k rl) = 1 := keyDepth_node_self hy _ _
                  have h3 : keyDepth y (BinaryTree.node l k (BinaryTree.node rl rk rr)) = 1 :=
                    keyDepth_node_self hy _ _
                  omega
                · have h1 : keyDepth y (BinaryTree.node (BinaryTree.node l k rl) rk rr) = 1 :=
                    keyDepth_node_self hy _ _
                  have h2 : keyDepth y (BinaryTree.node l k (BinaryTree.node rl rk rr))
                      = keyDepth y (BinaryTree.node rl rk rr) + 1 := keyDepth_node_gt (by omega) _ _
                  omega

/-- **Path-halving for top-down splay.** After splaying `q` in a BST, every key `y`
that lay on the search path of `q` has its depth (comparison count) at least halved,
up to the additive constant 5: `2 * keyDepth y (splay t q) ≤ keyDepth y t + 5`.
The constant 5 is tight (e.g. the left spine on keys `{1,2,3}` with `q = 1`, `y = 3`). -/

theorem keyDepth_splay_halving (q y : Nat) (t : BinaryTree)
    (hbst : IsBST t) (hy : y ∈ searchPath q t) :
    2 * keyDepth y (splay t q) ≤ keyDepth y t + 5 :=
  keyDepth_splay_halving_aux t.num_nodes t (Nat.le_refl _) q y hbst hy

/-- The originally targeted constant 6 follows a fortiori. -/

theorem keyDepth_splay_halving_six (q y : Nat) (t : BinaryTree)
    (hbst : IsBST t) (hy : y ∈ searchPath q t) :
    2 * keyDepth y (splay t q) ≤ keyDepth y t + 6 := by
  have := keyDepth_splay_halving q y t hbst hy
  omega


/-! ### BST search paths are duplicate-free -/

/-- Every key on a search path is a key of the tree (on the visited side). -/

theorem searchPath_nodup (q : ℕ) (t : BinaryTree) (hbst : IsBST t) :
    (searchPath q t).Nodup := by
  induction hbst with
  | left => simp [searchPath]
  | node key l r hfl hfr hbl hbr ihl ihr =>
    simp only [searchPath]
    by_cases h1 : q = key
    · simp [h1]
    · by_cases h2 : q < key
      · rw [if_neg h1, if_pos h2, List.nodup_cons]
        refine ⟨fun hmem => ?_, ihl⟩
        have hin : key ∈ l.toKeyList := searchPath_subset_toKeyList q l key hmem
        exact lt_irrefl key ((forallTree_iff_forall_mem.mp hfl) key hin)
      · rw [if_neg h1, if_neg h2, List.nodup_cons]
        refine ⟨fun hmem => ?_, ihr⟩
        have hin : key ∈ r.toKeyList := searchPath_subset_toKeyList q r key hmem
        exact lt_irrefl key ((forallTree_iff_forall_mem.mp hfr) key hin)



-- ===== suffix-preservation (R1 backbone) =====
@[simp] theorem searchPath_empty (q : Nat) : searchPath q .empty = [] := rfl

theorem root_mem_searchPath (y s : Nat) (A B : BinaryTree) :
    s ∈ searchPath y (.node A s B) := by
  by_cases h1 : y = s
  · rw [searchPath_node_self h1]; simp
  · by_cases h2 : y < s
    · rw [searchPath_node_lt h2]; simp
    · rw [searchPath_node_gt (by omega)]; simp

/-! ## The divergence suffix

`divergeSuffix y q t` is the part of `y`'s search path strictly below the point where it
separates from `q`'s search path: we descend simultaneously; if `y` is found at the current
node the suffix is empty; if `q` is found at the current node (but `y` is not) the suffix is
the remainder of `y`'s path below it; if both keys route to the same child we recurse; if
they route to different children the suffix is the remainder of `y`'s path below the
divergence node (the divergence node itself belongs to the shared prefix). -/

def divergeSuffix (y q : Nat) : BinaryTree → List Nat
  | .empty => []
  | .node l k r =>
      if y = k then []
      else if q = k then (if y < k then searchPath y l else searchPath y r)
      else if y < k ∧ q < k then divergeSuffix y q l
      else if k < y ∧ k < q then divergeSuffix y q r
      else (if y < k then searchPath y l else searchPath y r)

@[simp] theorem divergeSuffix_empty (y q : Nat) : divergeSuffix y q .empty = [] := rfl

theorem ds_self {y q k : Nat} (h : y = k) {l r : BinaryTree} :
    divergeSuffix y q (.node l k r) = [] := by
  simp only [divergeSuffix, if_pos h]

theorem ds_qroot_lt {y q k : Nat} (hq : q = k) (hy : y < k) {l r : BinaryTree} :
    divergeSuffix y q (.node l k r) = searchPath y l := by
  have h1 : y ≠ k := by omega
  simp only [divergeSuffix, if_neg h1, if_pos hq, if_pos hy]

theorem ds_qroot_gt {y q k : Nat} (hq : q = k) (hy : k < y) {l r : BinaryTree} :
    divergeSuffix y q (.node l k r) = searchPath y r := by
  have h1 : y ≠ k := by omega
  have h2 : ¬ y < k := by omega
  simp only [divergeSuffix, if_neg h1, if_pos hq, if_neg h2]

theorem ds_both_lt {y q k : Nat} (hy : y < k) (hq : q < k) {l r : BinaryTree} :
    divergeSuffix y q (.node l k r) = divergeSuffix y q l := by
  have h1 : y ≠ k := by omega
  have h2 : q ≠ k := by omega
  simp only [divergeSuffix, if_neg h1, if_neg h2, if_pos (And.intro hy hq)]

theorem ds_both_gt {y q k : Nat} (hy : k < y) (hq : k < q) {l r : BinaryTree} :
    divergeSuffix y q (.node l k r) = divergeSuffix y q r := by
  have h1 : y ≠ k := by omega
  have h2 : q ≠ k := by omega
  have h3 : ¬ (y < k ∧ q < k) := by omega
  simp only [divergeSuffix, if_neg h1, if_neg h2, if_neg h3, if_pos (And.intro hy hq)]

theorem ds_div_lt {y q k : Nat} (hy : y < k) (hq : k < q) {l r : BinaryTree} :
    divergeSuffix y q (.node l k r) = searchPath y l := by
  have h1 : y ≠ k := by omega
  have h2 : q ≠ k := by omega
  have h3 : ¬ (y < k ∧ q < k) := by omega
  have h4 : ¬ (k < y ∧ k < q) := by omega
  simp only [divergeSuffix, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos hy]

theorem ds_div_gt {y q k : Nat} (hy : k < y) (hq : q < k) {l r : BinaryTree} :
    divergeSuffix y q (.node l k r) = searchPath y r := by
  have h1 : y ≠ k := by omega
  have h2 : q ≠ k := by omega
  have h3 : ¬ (y < k ∧ q < k) := by omega
  have h4 : ¬ (k < y ∧ k < q) := by omega
  have h5 : ¬ y < k := by omega
  simp only [divergeSuffix, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]

/-- Splaying key `q` never leaves a divergence suffix for `y = q` itself. -/

theorem divergeSuffix_self_q (q : Nat) : ∀ t : BinaryTree, divergeSuffix q q t = [] := by
  intro t
  induction t with
  | empty => rfl
  | node l k r ihl ihr =>
    by_cases h : q = k
    · exact ds_self h
    · by_cases h2 : q < k
      · rw [ds_both_lt h2 h2]; exact ihl
      · have h3 : k < q := by omega
        rw [ds_both_gt h3 h3]; exact ihr

/-! ## ForallTree / IsBST toolkit (ported from the development file) -/

theorem mem_divergeSuffix_forall {p : Nat → Prop} {q y : Nat} :
    ∀ (t : BinaryTree), ForallTree p t → ∀ z ∈ divergeSuffix y q t, p z := by
  intro t
  induction t with
  | empty => intro _ z hz; simp at hz
  | node l k r ihl ihr =>
    intro h z hz
    rcases forallTree_node_iff.mp h with ⟨hl, hk, hr⟩
    by_cases h1 : y = k
    · rw [ds_self h1] at hz; simp at hz
    · by_cases h2 : q = k
      · by_cases h3 : y < k
        · rw [ds_qroot_lt h2 h3] at hz
          exact mem_searchPath_forall hl hz
        · rw [ds_qroot_gt h2 (by omega)] at hz
          exact mem_searchPath_forall hr hz
      · by_cases h3 : y < k
        · by_cases h4 : q < k
          · rw [ds_both_lt h3 h4] at hz
            exact ihl hl z hz
          · rw [ds_div_lt h3 (by omega)] at hz
            exact mem_searchPath_forall hl hz
        · have h3' : k < y := by omega
          by_cases h4 : k < q
          · rw [ds_both_gt h3' h4] at hz
            exact ihr hr z hz
          · rw [ds_div_gt h3' (by omega)] at hz
            exact mem_searchPath_forall hr hz

/-- In a BST the divergence suffix is disjoint from `q`'s search path. -/

theorem divergeSuffix_disjoint {q y : Nat} :
    ∀ (t : BinaryTree), IsBST t → ∀ z ∈ divergeSuffix y q t, z ∉ searchPath q t := by
  intro t
  induction t with
  | empty => intro _ z hz; simp at hz
  | node l k r ihl ihr =>
    intro hbst z hz
    rcases isBST_node_iff.mp hbst with ⟨hfl, hfr, hbl, hbr⟩
    by_cases h1 : y = k
    · rw [ds_self h1] at hz; simp at hz
    · by_cases h2 : q = k
      · rw [searchPath_node_self h2]
        by_cases h3 : y < k
        · rw [ds_qroot_lt h2 h3] at hz
          have hzk : z < k := mem_searchPath_forall (p := fun w => w < k) hfl hz
          simp only [List.mem_singleton]
          omega
        · rw [ds_qroot_gt h2 (by omega)] at hz
          have hzk : k < z := mem_searchPath_forall hfr hz
          simp only [List.mem_singleton]
          omega
      · by_cases h3 : y < k
        · by_cases h4 : q < k
          · rw [ds_both_lt h3 h4] at hz
            rw [searchPath_node_lt h4]
            have hzk : z < k := mem_divergeSuffix_forall l hfl z hz
            intro hmem
            rcases List.mem_cons.mp hmem with heq | hmem'
            · omega
            · exact ihl hbl z hz hmem'
          · have h4' : k < q := by omega
            rw [ds_div_lt h3 h4'] at hz
            rw [searchPath_node_gt h4']
            have hzk : z < k := mem_searchPath_forall (p := fun w => w < k) hfl hz
            intro hmem
            rcases List.mem_cons.mp hmem with heq | hmem'
            · omega
            · have : k < z := mem_searchPath_forall hfr hmem'
              omega
        · have h3' : k < y := by omega
          by_cases h4 : k < q
          · rw [ds_both_gt h3' h4] at hz
            rw [searchPath_node_gt h4]
            have hzk : k < z := mem_divergeSuffix_forall r hfr z hz
            intro hmem
            rcases List.mem_cons.mp hmem with heq | hmem'
            · omega
            · exact ihr hbr z hz hmem'
          · have h4' : q < k := by omega
            rw [ds_div_gt h3' h4'] at hz
            rw [searchPath_node_lt h4']
            have hzk : k < z := mem_searchPath_forall hfr hz
            intro hmem
            rcases List.mem_cons.mp hmem with heq | hmem'
            · omega
            · have : z < k := mem_searchPath_forall (p := fun w => w < k) hfl hmem'
              omega

/-! ## Companion decomposition of the ORIGINAL path -/

/-- `y`'s original search path is a shared prefix (drawn from `q`'s search path) followed by
the divergence suffix.  Pure structural induction; no BST hypothesis needed. -/

theorem searchPath_eq_shared_append_suffix (q y : Nat) (t : BinaryTree) :
    ∃ sh, searchPath y t = sh ++ divergeSuffix y q t ∧ ∀ z ∈ sh, z ∈ searchPath q t := by
  induction t with
  | empty => exact ⟨[], rfl, by simp⟩
  | node l k r ihl ihr =>
    have hk : k ∈ searchPath q (BinaryTree.node l k r) := root_mem_searchPath q k l r
    by_cases hyk : y = k
    · refine ⟨[k], ?_, ?_⟩
      · simp only [searchPath_node_self hyk, ds_self hyk, List.append_nil]
      · intro z hz
        simp only [List.mem_singleton] at hz
        subst hz; exact hk
    · by_cases hqk : q = k
      · by_cases hylt : y < k
        · refine ⟨[k], ?_, ?_⟩
          · simp only [searchPath_node_lt hylt, ds_qroot_lt hqk hylt,
              List.cons_append, List.nil_append]
          · intro z hz
            simp only [List.mem_singleton] at hz
            subst hz; exact hk
        · have hkly : k < y := by omega
          refine ⟨[k], ?_, ?_⟩
          · simp only [searchPath_node_gt hkly, ds_qroot_gt hqk hkly,
              List.cons_append, List.nil_append]
          · intro z hz
            simp only [List.mem_singleton] at hz
            subst hz; exact hk
      · by_cases hylt : y < k
        · by_cases hqlt : q < k
          · obtain ⟨sh, hsh, hm⟩ := ihl
            refine ⟨k :: sh, ?_, ?_⟩
            · simp only [searchPath_node_lt hylt, ds_both_lt hylt hqlt, hsh,
                List.cons_append]
            · intro z hz
              rcases List.mem_cons.mp hz with rfl | hz
              · exact hk
              · rw [searchPath_node_lt hqlt]
                exact List.mem_cons_of_mem _ (hm z hz)
          · have hklq : k < q := by omega
            refine ⟨[k], ?_, ?_⟩
            · simp only [searchPath_node_lt hylt, ds_div_lt hylt hklq,
                List.cons_append, List.nil_append]
            · intro z hz
              simp only [List.mem_singleton] at hz
              subst hz; exact hk
        · have hkly : k < y := by omega
          by_cases hklq : k < q
          · obtain ⟨sh, hsh, hm⟩ := ihr
            refine ⟨k :: sh, ?_, ?_⟩
            · simp only [searchPath_node_gt hkly, ds_both_gt hkly hklq, hsh,
                List.cons_append]
            · intro z hz
              rcases List.mem_cons.mp hz with rfl | hz
              · exact hk
              · rw [searchPath_node_gt hklq]
                exact List.mem_cons_of_mem _ (hm z hz)
          · have hqlt : q < k := by omega
            refine ⟨[k], ?_, ?_⟩
            · simp only [searchPath_node_gt hkly, ds_div_gt hkly hqlt,
                List.cons_append, List.nil_append]
            · intro z hz
              simp only [List.mem_singleton] at hz
              subst hz; exact hk

/-! ## Splay toolkit (ported from the development file) -/

theorem searchPath_splay_decomp_aux :
    ∀ (n : Nat) (t : BinaryTree), t.num_nodes ≤ n → ∀ (q y : Nat),
      IsBST t →
      ∃ p', searchPath y (splay t q) = p' ++ divergeSuffix y q t
        ∧ ∀ z ∈ p', z ∈ searchPath q t := by
  intro n
  induction n with
  | zero =>
    intro t ht q y _
    cases t with
    | empty => exact ⟨[], rfl, by simp⟩
    | node l k r =>
      exfalso
      have hnn : (BinaryTree.node l k r).num_nodes = 1 + l.num_nodes + r.num_nodes := rfl
      omega
  | succ n ih =>
    intro t ht q y hbst
    cases t with
    | empty => exact ⟨[], rfl, by simp⟩
    | node l k r =>
      rcases isBST_node_iff.mp hbst with ⟨hbL, hbR, hbstl, hbstr⟩
      by_cases hqk : q = k
      · -- (1) FOUND AT ROOT: splay is the identity
        rw [splay.eq_def]
        simp only [if_pos hqk]
        have hqpath : searchPath q (BinaryTree.node l k r) = [k] :=
          searchPath_node_self hqk l r
        by_cases hyk : y = k
        · refine ⟨[k], ?_, ?_⟩
          · simp only [searchPath_node_self hyk, ds_self hyk, List.append_nil]
          · intro z hz
            simp only [List.mem_singleton] at hz
            subst hz; rw [hqpath]; simp
        · by_cases hylt : y < k
          · refine ⟨[k], ?_, ?_⟩
            · simp only [searchPath_node_lt hylt, ds_qroot_lt hqk hylt,
                List.cons_append, List.nil_append]
            · intro z hz
              simp only [List.mem_singleton] at hz
              subst hz; rw [hqpath]; simp
          · have hkly : k < y := by omega
            refine ⟨[k], ?_, ?_⟩
            · simp only [searchPath_node_gt hkly, ds_qroot_gt hqk hkly,
                List.cons_append, List.nil_append]
            · intro z hz
              simp only [List.mem_singleton] at hz
              subst hz; rw [hqpath]; simp
      · by_cases hqlt : q < k
        · cases l with
          | empty =>
            -- (2) q routes left, left child empty: splay is the identity
            rw [splay.eq_def]
            simp only [if_neg hqk, if_pos hqlt]
            show ∃ p', searchPath y (BinaryTree.node .empty k r)
                = p' ++ divergeSuffix y q (BinaryTree.node .empty k r)
              ∧ ∀ z ∈ p', z ∈ searchPath q (BinaryTree.node .empty k r)
            have hqpath : searchPath q (BinaryTree.node .empty k r) = [k] := by
              rw [searchPath_node_lt hqlt, searchPath_empty]
            by_cases hyk : y = k
            · refine ⟨[k], ?_, ?_⟩
              · simp only [searchPath_node_self hyk, ds_self hyk, List.append_nil]
              · intro z hz
                simp only [List.mem_singleton] at hz
                subst hz; rw [hqpath]; simp
            · by_cases hylt : y < k
              · refine ⟨[k], ?_, ?_⟩
                · simp only [searchPath_node_lt hylt, searchPath_empty,
                    ds_both_lt hylt hqlt, divergeSuffix_empty,
                    List.cons_append, List.nil_append, List.append_nil]
                · intro z hz
                  simp only [List.mem_singleton] at hz
                  subst hz; rw [hqpath]; simp
              · have hkly : k < y := by omega
                refine ⟨[k], ?_, ?_⟩
                · simp only [searchPath_node_gt hkly, ds_div_gt hkly hqlt,
                    List.cons_append, List.nil_append]
                · intro z hz
                  simp only [List.mem_singleton] at hz
                  subst hz; rw [hqpath]; simp
          | node ll lk lr =>
            rcases forallTree_node_iff.mp hbL with ⟨hbL_ll, hlk_k, hbL_lr⟩
            rcases isBST_node_iff.mp hbstl with ⟨hbLL, hbLR, hbstll, hbstlr⟩
            by_cases hqlk : q < lk
            · cases ll with
              | empty =>
                -- (3) ZIG with empty grandchild
                rw [splay.eq_def]
                simp only [if_neg hqk, if_pos hqlt, if_pos hqlk]
                show ∃ p', searchPath y (BinaryTree.node .empty lk (BinaryTree.node lr k r))
                    = p' ++ divergeSuffix y q
                        (BinaryTree.node (BinaryTree.node .empty lk lr) k r)
                  ∧ ∀ z ∈ p',
                      z ∈ searchPath q (BinaryTree.node (BinaryTree.node .empty lk lr) k r)
                have hqpath : searchPath q
                    (BinaryTree.node (BinaryTree.node .empty lk lr) k r) = [k, lk] := by
                  rw [searchPath_node_lt hqlt, searchPath_node_lt hqlk, searchPath_empty]
                by_cases hyk : y = k
                · have hlky : lk < y := by omega
                  refine ⟨[lk, k], ?_, ?_⟩
                  · simp only [searchPath_node_gt hlky, searchPath_node_self hyk,
                      ds_self hyk, List.cons_append, List.nil_append, List.append_nil]
                  · intro z hz; rw [hqpath]
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                    tauto
                · by_cases hylt : y < k
                  · by_cases hylk : y = lk
                    · refine ⟨[lk], ?_, ?_⟩
                      · simp only [searchPath_node_self hylk, ds_both_lt hylt hqlt,
                          ds_self hylk, List.cons_append, List.nil_append, List.append_nil]
                      · intro z hz; rw [hqpath]
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                        tauto
                    · by_cases hyllk : y < lk
                      · refine ⟨[lk], ?_, ?_⟩
                        · simp only [searchPath_node_lt hyllk, searchPath_empty,
                            ds_both_lt hylt hqlt, ds_both_lt hyllk hqlk, divergeSuffix_empty,
                            List.cons_append, List.nil_append, List.append_nil]
                        · intro z hz; rw [hqpath]
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                          tauto
                      · have hlky : lk < y := by omega
                        refine ⟨[lk, k], ?_, ?_⟩
                        · simp only [searchPath_node_gt hlky, searchPath_node_lt hylt,
                            ds_both_lt hylt hqlt, ds_div_gt hlky hqlk,
                            List.cons_append, List.nil_append]
                        · intro z hz; rw [hqpath]
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                          tauto
                  · have hkly : k < y := by omega
                    have hlky : lk < y := by omega
                    refine ⟨[lk, k], ?_, ?_⟩
                    · simp only [searchPath_node_gt hlky, searchPath_node_gt hkly,
                        ds_div_gt hkly hqlt, List.cons_append, List.nil_append]
                    · intro z hz; rw [hqpath]
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                      tauto
              | node a x b =>
                -- (4) ZIG-ZIG
                have hsz : (BinaryTree.node a x b).num_nodes ≤ n := by
                  have hnn : (BinaryTree.node (BinaryTree.node (BinaryTree.node a x b) lk lr)
                      k r).num_nodes
                      = 1 + (1 + (BinaryTree.node a x b).num_nodes + lr.num_nodes)
                        + r.num_nodes := rfl
                  omega
                cases hs : splay (BinaryTree.node a x b) q with
                | empty => exact absurd hs (splay_ne_empty _ _ _ _)
                | node A s B =>
                  rw [splay_zigzig_shape (BinaryTree.node a x b) lr r A B lk k q s hqk hqlt
                    hqlk (fun h => nomatch h) hs]
                  have hsA := splay_forall _ (BinaryTree.node a x b) q hbLL
                  rw [hs] at hsA
                  have hslk : s < lk := (forallTree_node_iff.mp hsA).2.1
                  obtain ⟨pq, hpq, hmq⟩ := ih (BinaryTree.node a x b) hsz q q hbstll
                  rw [hs, divergeSuffix_self_q, List.append_nil] at hpq
                  have hsq : s ∈ searchPath q (BinaryTree.node a x b) := by
                    apply hmq
                    rw [← hpq]
                    exact root_mem_searchPath q s A B
                  have hqpath : searchPath q (BinaryTree.node
                      (BinaryTree.node (BinaryTree.node a x b) lk lr) k r)
                      = k :: lk :: searchPath q (BinaryTree.node a x b) := by
                    rw [searchPath_node_lt hqlt, searchPath_node_lt hqlk]
                  by_cases hyk : y = k
                  · have hsy : s < y := by omega
                    have hlky : lk < y := by omega
                    refine ⟨[s, lk, k], ?_, ?_⟩
                    · simp only [searchPath_node_gt hsy, searchPath_node_gt hlky,
                        searchPath_node_self hyk, ds_self hyk,
                        List.cons_append, List.nil_append, List.append_nil]
                    · intro z hz
                      rw [hqpath]
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
                      rcases hz with rfl | rfl | rfl
                      · simp [hsq]
                      · simp
                      · simp
                  · by_cases hylt : y < k
                    · by_cases hylk : y = lk
                      · have hsy : s < y := by omega
                        refine ⟨[s, lk], ?_, ?_⟩
                        · simp only [searchPath_node_gt hsy, searchPath_node_self hylk,
                            ds_both_lt hylt hqlt, ds_self hylk,
                            List.cons_append, List.nil_append, List.append_nil]
                        · intro z hz
                          rw [hqpath]
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
                          rcases hz with rfl | rfl
                          · simp [hsq]
                          · simp
                      · by_cases hyllk : y < lk
                        · -- y in the recursive zone
                          obtain ⟨p'', hp'', hm''⟩ := ih (BinaryTree.node a x b) hsz q y hbstll
                          rw [hs] at hp''
                          have hds : divergeSuffix y q (BinaryTree.node
                              (BinaryTree.node (BinaryTree.node a x b) lk lr) k r)
                              = divergeSuffix y q (BinaryTree.node a x b) := by
                            rw [ds_both_lt hylt hqlt, ds_both_lt hyllk hqlk]
                          rw [hds]
                          rcases Nat.lt_trichotomy y s with hys | hys | hys
                          · rw [searchPath_node_lt hys] at hp''
                            refine ⟨p'', ?_, ?_⟩
                            · rw [searchPath_node_lt hys]
                              exact hp''
                            · intro z hz
                              rw [hqpath]
                              have hzin := hm'' z hz
                              simp [hzin]
                          · rw [searchPath_node_self hys] at hp''
                            refine ⟨p'', ?_, ?_⟩
                            · rw [searchPath_node_self hys]
                              exact hp''
                            · intro z hz
                              rw [hqpath]
                              have hzin := hm'' z hz
                              simp [hzin]
                          · rw [searchPath_node_gt hys] at hp''
                            cases p'' with
                            | nil =>
                              exfalso
                              rw [List.nil_append] at hp''
                              have hsmem : s ∈ divergeSuffix y q (BinaryTree.node a x b) := by
                                rw [← hp'']
                                simp
                              exact divergeSuffix_disjoint (BinaryTree.node a x b)
                                hbstll s hsmem hsq
                            | cons c p''' =>
                              rw [List.cons_append] at hp''
                              injection hp'' with hc htail
                              subst hc
                              refine ⟨s :: lk :: p''', ?_, ?_⟩
                              · simp only [searchPath_node_gt hys, searchPath_node_lt hyllk,
                                  htail, List.cons_append]
                              · intro z hz
                                rw [hqpath]
                                simp only [List.mem_cons] at hz
                                rcases hz with rfl | rfl | hz
                                · simp [hsq]
                                · simp
                                · have hzin := hm'' z (by simp [hz])
                                  simp [hzin]
                        · -- lk < y < k: y lands in the cargo subtree lr
                          have hlky : lk < y := by omega
                          have hsy : s < y := by omega
                          refine ⟨[s, lk, k], ?_, ?_⟩
                          · simp only [searchPath_node_gt hsy, searchPath_node_gt hlky,
                              searchPath_node_lt hylt, ds_both_lt hylt hqlt,
                              ds_div_gt hlky hqlk,
                              List.cons_append, List.nil_append]
                          · intro z hz
                            rw [hqpath]
                            simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
                            rcases hz with rfl | rfl | rfl
                            · simp [hsq]
                            · simp
                            · simp
                    · -- k < y: y lands in the cargo subtree r
                      have hkly : k < y := by omega
                      have hsy : s < y := by omega
                      have hlky : lk < y := by omega
                      refine ⟨[s, lk, k], ?_, ?_⟩
                      · simp only [searchPath_node_gt hsy, searchPath_node_gt hlky,
                          searchPath_node_gt hkly, ds_div_gt hkly hqlt,
                          List.cons_append, List.nil_append]
                      · intro z hz
                        rw [hqpath]
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
                        rcases hz with rfl | rfl | rfl
                        · simp [hsq]
                        · simp
                        · simp
            · by_cases hlkq : lk < q
              · cases lr with
                | empty =>
                  -- (5) ZIG with empty grandchild (q between lk and k)
                  rw [splay.eq_def]
                  simp only [if_neg hqk, if_pos hqlt, if_neg hqlk, if_pos hlkq]
                  show ∃ p', searchPath y (BinaryTree.node ll lk (BinaryTree.node .empty k r))
                      = p' ++ divergeSuffix y q
                          (BinaryTree.node (BinaryTree.node ll lk .empty) k r)
                    ∧ ∀ z ∈ p',
                        z ∈ searchPath q (BinaryTree.node (BinaryTree.node ll lk .empty) k r)
                  have hqpath : searchPath q
                      (BinaryTree.node (BinaryTree.node ll lk .empty) k r) = [k, lk] := by
                    rw [searchPath_node_lt hqlt, searchPath_node_gt hlkq, searchPath_empty]
                  by_cases hyk : y = k
                  · have hlky : lk < y := by omega
                    refine ⟨[lk, k], ?_, ?_⟩
                    · simp only [searchPath_node_gt hlky, searchPath_node_self hyk,
                        ds_self hyk, List.cons_append, List.nil_append, List.append_nil]
                    · intro z hz; rw [hqpath]
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                      tauto
                  · by_cases hylt : y < k
                    · by_cases hylk : y = lk
                      · refine ⟨[lk], ?_, ?_⟩
                        · simp only [searchPath_node_self hylk, ds_both_lt hylt hqlt,
                            ds_self hylk, List.cons_append, List.nil_append, List.append_nil]
                        · intro z hz; rw [hqpath]
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                          tauto
                      · by_cases hyllk : y < lk
                        · refine ⟨[lk], ?_, ?_⟩
                          · simp only [searchPath_node_lt hyllk, ds_both_lt hylt hqlt,
                              ds_div_lt hyllk hlkq,
                              List.cons_append, List.nil_append]
                          · intro z hz; rw [hqpath]
                            simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                            tauto
                        · have hlky : lk < y := by omega
                          refine ⟨[lk, k], ?_, ?_⟩
                          · simp only [searchPath_node_gt hlky, searchPath_node_lt hylt,
                              searchPath_empty, ds_both_lt hylt hqlt,
                              ds_both_gt hlky hlkq, divergeSuffix_empty,
                              List.cons_append, List.nil_append, List.append_nil]
                          · intro z hz; rw [hqpath]
                            simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                            tauto
                    · have hkly : k < y := by omega
                      have hlky : lk < y := by omega
                      refine ⟨[lk, k], ?_, ?_⟩
                      · simp only [searchPath_node_gt hlky, searchPath_node_gt hkly,
                          ds_div_gt hkly hqlt, List.cons_append, List.nil_append]
                      · intro z hz; rw [hqpath]
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                        tauto
                | node a x b =>
                  -- (6) ZIG-ZAG
                  have hsz : (BinaryTree.node a x b).num_nodes ≤ n := by
                    have hnn : (BinaryTree.node (BinaryTree.node ll lk
                        (BinaryTree.node a x b)) k r).num_nodes
                        = 1 + (1 + ll.num_nodes + (BinaryTree.node a x b).num_nodes)
                          + r.num_nodes := rfl
                    omega
                  cases hs : splay (BinaryTree.node a x b) q with
                  | empty => exact absurd hs (splay_ne_empty _ _ _ _)
                  | node A s B =>
                    rw [splay_zigzag_shape ll (BinaryTree.node a x b) r A B lk k q s hqk hqlt
                      hlkq (fun h => nomatch h) hs]
                    have hsF1 := splay_forall _ (BinaryTree.node a x b) q hbLR
                    have hsF2 := splay_forall _ (BinaryTree.node a x b) q hbL_lr
                    rw [hs] at hsF1 hsF2
                    have hlks : lk < s := (forallTree_node_iff.mp hsF1).2.1
                    have hsk : s < k := (forallTree_node_iff.mp hsF2).2.1
                    obtain ⟨pq, hpq, hmq⟩ := ih (BinaryTree.node a x b) hsz q q hbstlr
                    rw [hs, divergeSuffix_self_q, List.append_nil] at hpq
                    have hsq : s ∈ searchPath q (BinaryTree.node a x b) := by
                      apply hmq
                      rw [← hpq]
                      exact root_mem_searchPath q s A B
                    have hqpath : searchPath q (BinaryTree.node
                        (BinaryTree.node ll lk (BinaryTree.node a x b)) k r)
                        = k :: lk :: searchPath q (BinaryTree.node a x b) := by
                      rw [searchPath_node_lt hqlt, searchPath_node_gt hlkq]
                    by_cases hyk : y = k
                    · have hsy : s < y := by omega
                      refine ⟨[s, k], ?_, ?_⟩
                      · simp only [searchPath_node_gt hsy, searchPath_node_self hyk,
                          ds_self hyk, List.cons_append, List.nil_append, List.append_nil]
                      · intro z hz
                        rw [hqpath]
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
                        rcases hz with rfl | rfl
                        · simp [hsq]
                        · simp
                    · by_cases hylt : y < k
                      · by_cases hylk : y = lk
                        · have hys : y < s := by omega
                          refine ⟨[s, lk], ?_, ?_⟩
                          · simp only [searchPath_node_lt hys, searchPath_node_self hylk,
                              ds_both_lt hylt hqlt, ds_self hylk,
                              List.cons_append, List.nil_append, List.append_nil]
                          · intro z hz
                            rw [hqpath]
                            simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
                            rcases hz with rfl | rfl
                            · simp [hsq]
                            · simp
                        · by_cases hyllk : y < lk
                          · -- y < lk: y lands in the cargo subtree ll
                            have hys : y < s := by omega
                            refine ⟨[s, lk], ?_, ?_⟩
                            · simp only [searchPath_node_lt hys, searchPath_node_lt hyllk,
                                ds_both_lt hylt hqlt, ds_div_lt hyllk hlkq,
                                List.cons_append, List.nil_append]
                            · intro z hz
                              rw [hqpath]
                              simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
                              rcases hz with rfl | rfl
                              · simp [hsq]
                              · simp
                          · -- lk < y < k: y in the recursive zone
                            have hlky : lk < y := by omega
                            obtain ⟨p'', hp'', hm''⟩ :=
                              ih (BinaryTree.node a x b) hsz q y hbstlr
                            rw [hs] at hp''
                            have hds : divergeSuffix y q (BinaryTree.node
                                (BinaryTree.node ll lk (BinaryTree.node a x b)) k r)
                                = divergeSuffix y q (BinaryTree.node a x b) := by
                              rw [ds_both_lt hylt hqlt, ds_both_gt hlky hlkq]
                            rw [hds]
                            rcases Nat.lt_trichotomy y s with hys | hys | hys
                            · rw [searchPath_node_lt hys] at hp''
                              cases p'' with
                              | nil =>
                                exfalso
                                rw [List.nil_append] at hp''
                                have hsmem : s ∈ divergeSuffix y q (BinaryTree.node a x b) := by
                                  rw [← hp'']
                                  simp
                                exact divergeSuffix_disjoint (BinaryTree.node a x b)
                                  hbstlr s hsmem hsq
                              | cons c p''' =>
                                rw [List.cons_append] at hp''
                                injection hp'' with hc htail
                                subst hc
                                refine ⟨s :: lk :: p''', ?_, ?_⟩
                                · simp only [searchPath_node_lt hys, searchPath_node_gt hlky,
                                    htail, List.cons_append]
                                · intro z hz
                                  rw [hqpath]
                                  simp only [List.mem_cons] at hz
                                  rcases hz with rfl | rfl | hz
                                  · simp [hsq]
                                  · simp
                                  · have hzin := hm'' z (by simp [hz])
                                    simp [hzin]
                            · rw [searchPath_node_self hys] at hp''
                              refine ⟨p'', ?_, ?_⟩
                              · rw [searchPath_node_self hys]
                                exact hp''
                              · intro z hz
                                rw [hqpath]
                                have hzin := hm'' z hz
                                simp [hzin]
                            · rw [searchPath_node_gt hys] at hp''
                              cases p'' with
                              | nil =>
                                exfalso
                                rw [List.nil_append] at hp''
                                have hsmem : s ∈ divergeSuffix y q (BinaryTree.node a x b) := by
                                  rw [← hp'']
                                  simp
                                exact divergeSuffix_disjoint (BinaryTree.node a x b)
                                  hbstlr s hsmem hsq
                              | cons c p''' =>
                                rw [List.cons_append] at hp''
                                injection hp'' with hc htail
                                subst hc
                                refine ⟨s :: k :: p''', ?_, ?_⟩
                                · simp only [searchPath_node_gt hys, searchPath_node_lt hylt,
                                    htail, List.cons_append]
                                · intro z hz
                                  rw [hqpath]
                                  simp only [List.mem_cons] at hz
                                  rcases hz with rfl | rfl | hz
                                  · simp [hsq]
                                  · simp
                                  · have hzin := hm'' z (by simp [hz])
                                    simp [hzin]
                      · -- k < y: y lands in the cargo subtree r
                        have hkly : k < y := by omega
                        have hsy : s < y := by omega
                        refine ⟨[s, k], ?_, ?_⟩
                        · simp only [searchPath_node_gt hsy, searchPath_node_gt hkly,
                            ds_div_gt hkly hqlt, List.cons_append, List.nil_append]
                        · intro z hz
                          rw [hqpath]
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
                          rcases hz with rfl | rfl
                          · simp [hsq]
                          · simp
              · -- (7) found at the left child: q = lk, single ZIG
                have hqeq : q = lk := by omega
                rw [splay.eq_def]
                simp only [if_neg hqk, if_pos hqlt, if_neg hqlk, if_neg hlkq]
                show ∃ p', searchPath y (BinaryTree.node ll lk (BinaryTree.node lr k r))
                    = p' ++ divergeSuffix y q
                        (BinaryTree.node (BinaryTree.node ll lk lr) k r)
                  ∧ ∀ z ∈ p',
                      z ∈ searchPath q (BinaryTree.node (BinaryTree.node ll lk lr) k r)
                have hqpath : searchPath q
                    (BinaryTree.node (BinaryTree.node ll lk lr) k r) = [k, lk] := by
                  rw [searchPath_node_lt hqlt, searchPath_node_self hqeq]
                by_cases hyk : y = k
                · have hlky : lk < y := by omega
                  refine ⟨[lk, k], ?_, ?_⟩
                  · simp only [searchPath_node_gt hlky, searchPath_node_self hyk,
                      ds_self hyk, List.cons_append, List.nil_append, List.append_nil]
                  · intro z hz; rw [hqpath]
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                    tauto
                · by_cases hylt : y < k
                  · by_cases hylk : y = lk
                    · refine ⟨[lk], ?_, ?_⟩
                      · simp only [searchPath_node_self hylk, ds_both_lt hylt hqlt,
                          ds_self hylk, List.cons_append, List.nil_append, List.append_nil]
                      · intro z hz; rw [hqpath]
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                        tauto
                    · by_cases hyllk : y < lk
                      · refine ⟨[lk], ?_, ?_⟩
                        · simp only [searchPath_node_lt hyllk, ds_both_lt hylt hqlt,
                            ds_qroot_lt hqeq hyllk,
                            List.cons_append, List.nil_append]
                        · intro z hz; rw [hqpath]
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                          tauto
                      · have hlky : lk < y := by omega
                        refine ⟨[lk, k], ?_, ?_⟩
                        · simp only [searchPath_node_gt hlky, searchPath_node_lt hylt,
                            ds_both_lt hylt hqlt, ds_qroot_gt hqeq hlky,
                            List.cons_append, List.nil_append]
                        · intro z hz; rw [hqpath]
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                          tauto
                  · have hkly : k < y := by omega
                    have hlky : lk < y := by omega
                    refine ⟨[lk, k], ?_, ?_⟩
                    · simp only [searchPath_node_gt hlky, searchPath_node_gt hkly,
                        ds_div_gt hkly hqlt, List.cons_append, List.nil_append]
                    · intro z hz; rw [hqpath]
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                      tauto
        · -- k < q
          have hklt : k < q := by omega
          cases r with
          | empty =>
            -- (8) q routes right, right child empty: splay is the identity
            rw [splay.eq_def]
            simp only [if_neg hqk, if_neg hqlt]
            show ∃ p', searchPath y (BinaryTree.node l k .empty)
                = p' ++ divergeSuffix y q (BinaryTree.node l k .empty)
              ∧ ∀ z ∈ p', z ∈ searchPath q (BinaryTree.node l k .empty)
            have hqpath : searchPath q (BinaryTree.node l k .empty) = [k] := by
              rw [searchPath_node_gt hklt, searchPath_empty]
            by_cases hyk : y = k
            · refine ⟨[k], ?_, ?_⟩
              · simp only [searchPath_node_self hyk, ds_self hyk, List.append_nil]
              · intro z hz
                simp only [List.mem_singleton] at hz
                subst hz; rw [hqpath]; simp
            · by_cases hylt : y < k
              · refine ⟨[k], ?_, ?_⟩
                · simp only [searchPath_node_lt hylt, ds_div_lt hylt hklt,
                    List.cons_append, List.nil_append]
                · intro z hz
                  simp only [List.mem_singleton] at hz
                  subst hz; rw [hqpath]; simp
              · have hkly : k < y := by omega
                refine ⟨[k], ?_, ?_⟩
                · simp only [searchPath_node_gt hkly, searchPath_empty,
                    ds_both_gt hkly hklt, divergeSuffix_empty,
                    List.cons_append, List.nil_append, List.append_nil]
                · intro z hz
                  simp only [List.mem_singleton] at hz
                  subst hz; rw [hqpath]; simp
          | node rl rk rr =>
            rcases forallTree_node_iff.mp hbR with ⟨hbR_rl, hk_rk, hbR_rr⟩
            rcases isBST_node_iff.mp hbstr with ⟨hbRL, hbRR, hbstrl, hbstrr⟩
            by_cases hqrk : q < rk
            · cases rl with
              | empty =>
                -- (9) ZAG with empty grandchild (q between k and rk)
                rw [splay.eq_def]
                simp only [if_neg hqk, if_neg hqlt, if_pos hqrk]
                show ∃ p', searchPath y (BinaryTree.node (BinaryTree.node l k .empty) rk rr)
                    = p' ++ divergeSuffix y q
                        (BinaryTree.node l k (BinaryTree.node .empty rk rr))
                  ∧ ∀ z ∈ p',
                      z ∈ searchPath q (BinaryTree.node l k (BinaryTree.node .empty rk rr))
                have hqpath : searchPath q
                    (BinaryTree.node l k (BinaryTree.node .empty rk rr)) = [k, rk] := by
                  rw [searchPath_node_gt hklt, searchPath_node_lt hqrk, searchPath_empty]
                by_cases hyk : y = k
                · have hyrk : y < rk := by omega
                  refine ⟨[rk, k], ?_, ?_⟩
                  · simp only [searchPath_node_lt hyrk, searchPath_node_self hyk,
                      ds_self hyk, List.cons_append, List.nil_append, List.append_nil]
                  · intro z hz; rw [hqpath]
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                    tauto
                · by_cases hylt : y < k
                  · have hyrk : y < rk := by omega
                    refine ⟨[rk, k], ?_, ?_⟩
                    · simp only [searchPath_node_lt hyrk, searchPath_node_lt hylt,
                        ds_div_lt hylt hklt, List.cons_append, List.nil_append]
                    · intro z hz; rw [hqpath]
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                      tauto
                  · have hkly : k < y := by omega
                    by_cases hyrk : y = rk
                    · refine ⟨[rk], ?_, ?_⟩
                      · simp only [searchPath_node_self hyrk, ds_both_gt hkly hklt,
                          ds_self hyrk, List.cons_append, List.nil_append, List.append_nil]
                      · intro z hz; rw [hqpath]
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                        tauto
                    · by_cases hyrklt : y < rk
                      · refine ⟨[rk, k], ?_, ?_⟩
                        · simp only [searchPath_node_lt hyrklt, searchPath_node_gt hkly,
                            searchPath_empty, ds_both_gt hkly hklt,
                            ds_both_lt hyrklt hqrk, divergeSuffix_empty,
                            List.cons_append, List.nil_append, List.append_nil]
                        · intro z hz; rw [hqpath]
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                          tauto
                      · have hrky : rk < y := by omega
                        refine ⟨[rk], ?_, ?_⟩
                        · simp only [searchPath_node_gt hrky, ds_both_gt hkly hklt,
                            ds_div_gt hrky hqrk, List.cons_append, List.nil_append]
                        · intro z hz; rw [hqpath]
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                          tauto
              | node a x b =>
                -- (10) ZAG-ZIG
                have hsz : (BinaryTree.node a x b).num_nodes ≤ n := by
                  have hnn : (BinaryTree.node l k (BinaryTree.node (BinaryTree.node a x b)
                      rk rr)).num_nodes
                      = 1 + l.num_nodes
                        + (1 + (BinaryTree.node a x b).num_nodes + rr.num_nodes) := rfl
                  omega
                cases hs : splay (BinaryTree.node a x b) q with
                | empty => exact absurd hs (splay_ne_empty _ _ _ _)
                | node A s B =>
                  rw [splay_zagzig_shape l (BinaryTree.node a x b) rr A B rk k q s hqk hklt
                    hqrk (fun h => nomatch h) hs]
                  have hsF1 := splay_forall _ (BinaryTree.node a x b) q hbRL
                  have hsF2 := splay_forall _ (BinaryTree.node a x b) q hbR_rl
                  rw [hs] at hsF1 hsF2
                  have hsrk : s < rk := (forallTree_node_iff.mp hsF1).2.1
                  have hks : k < s := (forallTree_node_iff.mp hsF2).2.1
                  obtain ⟨pq, hpq, hmq⟩ := ih (BinaryTree.node a x b) hsz q q hbstrl
                  rw [hs, divergeSuffix_self_q, List.append_nil] at hpq
                  have hsq : s ∈ searchPath q (BinaryTree.node a x b) := by
                    apply hmq
                    rw [← hpq]
                    exact root_mem_searchPath q s A B
                  have hqpath : searchPath q (BinaryTree.node l k
                      (BinaryTree.node (BinaryTree.node a x b) rk rr))
                      = k :: rk :: searchPath q (BinaryTree.node a x b) := by
                    rw [searchPath_node_gt hklt, searchPath_node_lt hqrk]
                  by_cases hyk : y = k
                  · have hys : y < s := by omega
                    refine ⟨[s, k], ?_, ?_⟩
                    · simp only [searchPath_node_lt hys, searchPath_node_self hyk,
                        ds_self hyk, List.cons_append, List.nil_append, List.append_nil]
                    · intro z hz
                      rw [hqpath]
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
                      rcases hz with rfl | rfl
                      · simp [hsq]
                      · simp
                  · by_cases hylt : y < k
                    · -- y < k: y lands in the cargo subtree l
                      have hys : y < s := by omega
                      refine ⟨[s, k], ?_, ?_⟩
                      · simp only [searchPath_node_lt hys, searchPath_node_lt hylt,
                          ds_div_lt hylt hklt, List.cons_append, List.nil_append]
                      · intro z hz
                        rw [hqpath]
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
                        rcases hz with rfl | rfl
                        · simp [hsq]
                        · simp
                    · have hkly : k < y := by omega
                      by_cases hyrk : y = rk
                      · have hsy : s < y := by omega
                        refine ⟨[s, rk], ?_, ?_⟩
                        · simp only [searchPath_node_gt hsy, searchPath_node_self hyrk,
                            ds_both_gt hkly hklt, ds_self hyrk,
                            List.cons_append, List.nil_append, List.append_nil]
                        · intro z hz
                          rw [hqpath]
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
                          rcases hz with rfl | rfl
                          · simp [hsq]
                          · simp
                      · by_cases hyrklt : y < rk
                        · -- k < y < rk: y in the recursive zone
                          obtain ⟨p'', hp'', hm''⟩ :=
                            ih (BinaryTree.node a x b) hsz q y hbstrl
                          rw [hs] at hp''
                          have hds : divergeSuffix y q (BinaryTree.node l k
                              (BinaryTree.node (BinaryTree.node a x b) rk rr))
                              = divergeSuffix y q (BinaryTree.node a x b) := by
                            rw [ds_both_gt hkly hklt, ds_both_lt hyrklt hqrk]
                          rw [hds]
                          rcases Nat.lt_trichotomy y s with hys | hys | hys
                          · rw [searchPath_node_lt hys] at hp''
                            cases p'' with
                            | nil =>
                              exfalso
                              rw [List.nil_append] at hp''
                              have hsmem : s ∈ divergeSuffix y q (BinaryTree.node a x b) := by
                                rw [← hp'']
                                simp
                              exact divergeSuffix_disjoint (BinaryTree.node a x b)
                                hbstrl s hsmem hsq
                            | cons c p''' =>
                              rw [List.cons_append] at hp''
                              injection hp'' with hc htail
                              subst hc
                              refine ⟨s :: k :: p''', ?_, ?_⟩
                              · simp only [searchPath_node_lt hys, searchPath_node_gt hkly,
                                  htail, List.cons_append]
                              · intro z hz
                                rw [hqpath]
                                simp only [List.mem_cons] at hz
                                rcases hz with rfl | rfl | hz
                                · simp [hsq]
                                · simp
                                · have hzin := hm'' z (by simp [hz])
                                  simp [hzin]
                          · rw [searchPath_node_self hys] at hp''
                            refine ⟨p'', ?_, ?_⟩
                            · rw [searchPath_node_self hys]
                              exact hp''
                            · intro z hz
                              rw [hqpath]
                              have hzin := hm'' z hz
                              simp [hzin]
                          · rw [searchPath_node_gt hys] at hp''
                            cases p'' with
                            | nil =>
                              exfalso
                              rw [List.nil_append] at hp''
                              have hsmem : s ∈ divergeSuffix y q (BinaryTree.node a x b) := by
                                rw [← hp'']
                                simp
                              exact divergeSuffix_disjoint (BinaryTree.node a x b)
                                hbstrl s hsmem hsq
                            | cons c p''' =>
                              rw [List.cons_append] at hp''
                              injection hp'' with hc htail
                              subst hc
                              refine ⟨s :: rk :: p''', ?_, ?_⟩
                              · simp only [searchPath_node_gt hys, searchPath_node_lt hyrklt,
                                  htail, List.cons_append]
                              · intro z hz
                                rw [hqpath]
                                simp only [List.mem_cons] at hz
                                rcases hz with rfl | rfl | hz
                                · simp [hsq]
                                · simp
                                · have hzin := hm'' z (by simp [hz])
                                  simp [hzin]
                        · -- rk < y: y lands in the cargo subtree rr
                          have hrky : rk < y := by omega
                          have hsy : s < y := by omega
                          refine ⟨[s, rk], ?_, ?_⟩
                          · simp only [searchPath_node_gt hsy, searchPath_node_gt hrky,
                              ds_both_gt hkly hklt, ds_div_gt hrky hqrk,
                              List.cons_append, List.nil_append]
                          · intro z hz
                            rw [hqpath]
                            simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
                            rcases hz with rfl | rfl
                            · simp [hsq]
                            · simp
            · by_cases hrkq : rk < q
              · cases rr with
                | empty =>
                  -- (11) ZAG with empty grandchild (q above rk)
                  rw [splay.eq_def]
                  simp only [if_neg hqk, if_neg hqlt, if_neg hqrk, if_pos hrkq]
                  show ∃ p', searchPath y (BinaryTree.node (BinaryTree.node l k rl) rk .empty)
                      = p' ++ divergeSuffix y q
                          (BinaryTree.node l k (BinaryTree.node rl rk .empty))
                    ∧ ∀ z ∈ p',
                        z ∈ searchPath q (BinaryTree.node l k (BinaryTree.node rl rk .empty))
                  have hqpath : searchPath q
                      (BinaryTree.node l k (BinaryTree.node rl rk .empty)) = [k, rk] := by
                    rw [searchPath_node_gt hklt, searchPath_node_gt hrkq, searchPath_empty]
                  by_cases hyk : y = k
                  · have hyrk : y < rk := by omega
                    refine ⟨[rk, k], ?_, ?_⟩
                    · simp only [searchPath_node_lt hyrk, searchPath_node_self hyk,
                        ds_self hyk, List.cons_append, List.nil_append, List.append_nil]
                    · intro z hz; rw [hqpath]
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                      tauto
                  · by_cases hylt : y < k
                    · have hyrk : y < rk := by omega
                      refine ⟨[rk, k], ?_, ?_⟩
                      · simp only [searchPath_node_lt hyrk, searchPath_node_lt hylt,
                          ds_div_lt hylt hklt, List.cons_append, List.nil_append]
                      · intro z hz; rw [hqpath]
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                        tauto
                    · have hkly : k < y := by omega
                      by_cases hyrk : y = rk
                      · refine ⟨[rk], ?_, ?_⟩
                        · simp only [searchPath_node_self hyrk, ds_both_gt hkly hklt,
                            ds_self hyrk, List.cons_append, List.nil_append, List.append_nil]
                        · intro z hz; rw [hqpath]
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                          tauto
                      · by_cases hyrklt : y < rk
                        · refine ⟨[rk, k], ?_, ?_⟩
                          · simp only [searchPath_node_lt hyrklt, searchPath_node_gt hkly,
                              ds_both_gt hkly hklt, ds_div_lt hyrklt hrkq,
                              List.cons_append, List.nil_append]
                          · intro z hz; rw [hqpath]
                            simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                            tauto
                        · have hrky : rk < y := by omega
                          refine ⟨[rk], ?_, ?_⟩
                          · simp only [searchPath_node_gt hrky, searchPath_empty,
                              ds_both_gt hkly hklt, ds_both_gt hrky hrkq, divergeSuffix_empty,
                              List.cons_append, List.nil_append, List.append_nil]
                          · intro z hz; rw [hqpath]
                            simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                            tauto
                | node a x b =>
                  -- (12) ZAG-ZAG
                  have hsz : (BinaryTree.node a x b).num_nodes ≤ n := by
                    have hnn : (BinaryTree.node l k (BinaryTree.node rl rk
                        (BinaryTree.node a x b))).num_nodes
                        = 1 + l.num_nodes
                          + (1 + rl.num_nodes + (BinaryTree.node a x b).num_nodes) := rfl
                    omega
                  cases hs : splay (BinaryTree.node a x b) q with
                  | empty => exact absurd hs (splay_ne_empty _ _ _ _)
                  | node A s B =>
                    rw [splay_zagzag_shape l rl (BinaryTree.node a x b) A B rk k q s hqk hklt
                      hrkq (fun h => nomatch h) hs]
                    have hsF1 := splay_forall _ (BinaryTree.node a x b) q hbRR
                    rw [hs] at hsF1
                    have hrks : rk < s := (forallTree_node_iff.mp hsF1).2.1
                    obtain ⟨pq, hpq, hmq⟩ := ih (BinaryTree.node a x b) hsz q q hbstrr
                    rw [hs, divergeSuffix_self_q, List.append_nil] at hpq
                    have hsq : s ∈ searchPath q (BinaryTree.node a x b) := by
                      apply hmq
                      rw [← hpq]
                      exact root_mem_searchPath q s A B
                    have hqpath : searchPath q (BinaryTree.node l k
                        (BinaryTree.node rl rk (BinaryTree.node a x b)))
                        = k :: rk :: searchPath q (BinaryTree.node a x b) := by
                      rw [searchPath_node_gt hklt, searchPath_node_gt hrkq]
                    by_cases hyk : y = k
                    · have hys : y < s := by omega
                      have hyrk : y < rk := by omega
                      refine ⟨[s, rk, k], ?_, ?_⟩
                      · simp only [searchPath_node_lt hys, searchPath_node_lt hyrk,
                          searchPath_node_self hyk, ds_self hyk,
                          List.cons_append, List.nil_append, List.append_nil]
                      · intro z hz
                        rw [hqpath]
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
                        rcases hz with rfl | rfl | rfl
                        · simp [hsq]
                        · simp
                        · simp
                    · by_cases hylt : y < k
                      · -- y < k: y lands in the cargo subtree l
                        have hys : y < s := by omega
                        have hyrk : y < rk := by omega
                        refine ⟨[s, rk, k], ?_, ?_⟩
                        · simp only [searchPath_node_lt hys, searchPath_node_lt hyrk,
                            searchPath_node_lt hylt, ds_div_lt hylt hklt,
                            List.cons_append, List.nil_append]
                        · intro z hz
                          rw [hqpath]
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
                          rcases hz with rfl | rfl | rfl
                          · simp [hsq]
                          · simp
                          · simp
                      · have hkly : k < y := by omega
                        by_cases hyrk : y = rk
                        · have hys : y < s := by omega
                          refine ⟨[s, rk], ?_, ?_⟩
                          · simp only [searchPath_node_lt hys, searchPath_node_self hyrk,
                              ds_both_gt hkly hklt, ds_self hyrk,
                              List.cons_append, List.nil_append, List.append_nil]
                          · intro z hz
                            rw [hqpath]
                            simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
                            rcases hz with rfl | rfl
                            · simp [hsq]
                            · simp
                        · by_cases hyrklt : y < rk
                          · -- k < y < rk: y lands in the cargo subtree rl
                            have hys : y < s := by omega
                            refine ⟨[s, rk, k], ?_, ?_⟩
                            · simp only [searchPath_node_lt hys, searchPath_node_lt hyrklt,
                                searchPath_node_gt hkly, ds_both_gt hkly hklt,
                                ds_div_lt hyrklt hrkq,
                                List.cons_append, List.nil_append]
                            · intro z hz
                              rw [hqpath]
                              simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
                              rcases hz with rfl | rfl | rfl
                              · simp [hsq]
                              · simp
                              · simp
                          · -- rk < y: y in the recursive zone
                            have hrky : rk < y := by omega
                            obtain ⟨p'', hp'', hm''⟩ :=
                              ih (BinaryTree.node a x b) hsz q y hbstrr
                            rw [hs] at hp''
                            have hds : divergeSuffix y q (BinaryTree.node l k
                                (BinaryTree.node rl rk (BinaryTree.node a x b)))
                                = divergeSuffix y q (BinaryTree.node a x b) := by
                              rw [ds_both_gt hkly hklt, ds_both_gt hrky hrkq]
                            rw [hds]
                            rcases Nat.lt_trichotomy y s with hys | hys | hys
                            · rw [searchPath_node_lt hys] at hp''
                              cases p'' with
                              | nil =>
                                exfalso
                                rw [List.nil_append] at hp''
                                have hsmem : s ∈ divergeSuffix y q (BinaryTree.node a x b) := by
                                  rw [← hp'']
                                  simp
                                exact divergeSuffix_disjoint (BinaryTree.node a x b)
                                  hbstrr s hsmem hsq
                              | cons c p''' =>
                                rw [List.cons_append] at hp''
                                injection hp'' with hc htail
                                subst hc
                                refine ⟨s :: rk :: p''', ?_, ?_⟩
                                · simp only [searchPath_node_lt hys, searchPath_node_gt hrky,
                                    htail, List.cons_append]
                                · intro z hz
                                  rw [hqpath]
                                  simp only [List.mem_cons] at hz
                                  rcases hz with rfl | rfl | hz
                                  · simp [hsq]
                                  · simp
                                  · have hzin := hm'' z (by simp [hz])
                                    simp [hzin]
                            · rw [searchPath_node_self hys] at hp''
                              refine ⟨p'', ?_, ?_⟩
                              · rw [searchPath_node_self hys]
                                exact hp''
                              · intro z hz
                                rw [hqpath]
                                have hzin := hm'' z hz
                                simp [hzin]
                            · rw [searchPath_node_gt hys] at hp''
                              refine ⟨p'', ?_, ?_⟩
                              · rw [searchPath_node_gt hys]
                                exact hp''
                              · intro z hz
                                rw [hqpath]
                                have hzin := hm'' z hz
                                simp [hzin]
              · -- (13) found at the right child: q = rk, single ZAG
                have hqeq : q = rk := by omega
                rw [splay.eq_def]
                simp only [if_neg hqk, if_neg hqlt, if_neg hqrk, if_neg hrkq]
                show ∃ p', searchPath y (BinaryTree.node (BinaryTree.node l k rl) rk rr)
                    = p' ++ divergeSuffix y q
                        (BinaryTree.node l k (BinaryTree.node rl rk rr))
                  ∧ ∀ z ∈ p',
                      z ∈ searchPath q (BinaryTree.node l k (BinaryTree.node rl rk rr))
                have hqpath : searchPath q
                    (BinaryTree.node l k (BinaryTree.node rl rk rr)) = [k, rk] := by
                  rw [searchPath_node_gt hklt, searchPath_node_self hqeq]
                by_cases hyk : y = k
                · have hyrk : y < rk := by omega
                  refine ⟨[rk, k], ?_, ?_⟩
                  · simp only [searchPath_node_lt hyrk, searchPath_node_self hyk,
                      ds_self hyk, List.cons_append, List.nil_append, List.append_nil]
                  · intro z hz; rw [hqpath]
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                    tauto
                · by_cases hylt : y < k
                  · have hyrk : y < rk := by omega
                    refine ⟨[rk, k], ?_, ?_⟩
                    · simp only [searchPath_node_lt hyrk, searchPath_node_lt hylt,
                        ds_div_lt hylt hklt, List.cons_append, List.nil_append]
                    · intro z hz; rw [hqpath]
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                      tauto
                  · have hkly : k < y := by omega
                    by_cases hyrk : y = rk
                    · refine ⟨[rk], ?_, ?_⟩
                      · simp only [searchPath_node_self hyrk, ds_both_gt hkly hklt,
                          ds_self hyrk, List.cons_append, List.nil_append, List.append_nil]
                      · intro z hz; rw [hqpath]
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                        tauto
                    · by_cases hyrklt : y < rk
                      · refine ⟨[rk, k], ?_, ?_⟩
                        · simp only [searchPath_node_lt hyrklt, searchPath_node_gt hkly,
                            ds_both_gt hkly hklt, ds_qroot_lt hqeq hyrklt,
                            List.cons_append, List.nil_append]
                        · intro z hz; rw [hqpath]
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                          tauto
                      · have hrky : rk < y := by omega
                        refine ⟨[rk], ?_, ?_⟩
                        · simp only [searchPath_node_gt hrky, ds_both_gt hkly hklt,
                            ds_qroot_gt hqeq hrky, List.cons_append, List.nil_append]
                        · intro z hz; rw [hqpath]
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                          tauto

/-- MAIN THEOREM (suffix preservation): splaying `q` rewrites the search path of any key `y`
as a new prefix drawn from `q`'s OLD search path, followed by the (untouched) divergence
suffix of `y`'s old path. -/

theorem searchPath_splay_decomp (q y : Nat) (t : BinaryTree) (hbst : IsBST t) :
    ∃ p', searchPath y (splay t q) = p' ++ divergeSuffix y q t
      ∧ ∀ z ∈ p', z ∈ searchPath q t :=
  searchPath_splay_decomp_aux t.num_nodes t (Nat.le_refl _) q y hbst



theorem sp_len (y : Nat) (t : BinaryTree) : (searchPath y t).length = keyDepth y t := rfl


theorem splay_eq_of_eq {q k : Nat} (h : q = k) (l r : BinaryTree) :
    splay (.node l k r) q = .node l k r := by
  rw [splay.eq_def]
  simp only [if_pos h]

theorem splay_left_empty {q k : Nat} (h : q < k) (r : BinaryTree) :
    splay (.node .empty k r) q = .node .empty k r := by
  rw [splay.eq_def]
  simp only [if_neg (Nat.ne_of_lt h), if_pos h]

theorem splay_right_empty {q k : Nat} (h : k < q) (l : BinaryTree) :
    splay (.node l k .empty) q = .node l k .empty := by
  have h1 : q ≠ k := by omega
  have h2 : ¬ q < k := by omega
  rw [splay.eq_def]
  simp only [if_neg h1, if_neg h2]

theorem splay_zig_ll_empty {q k lk : Nat} (hqk : q < k) (hqlk : q < lk)
    (lr r : BinaryTree) :
    splay (.node (.node .empty lk lr) k r) q = .node .empty lk (.node lr k r) := by
  rw [splay.eq_def]
  simp only [if_neg (Nat.ne_of_lt hqk), if_pos hqk, if_pos hqlk]
  rfl

theorem splay_zig_found {q k lk : Nat} (hqk : q < k) (h1 : ¬ q < lk) (h2 : ¬ lk < q)
    (ll lr r : BinaryTree) :
    splay (.node (.node ll lk lr) k r) q = .node ll lk (.node lr k r) := by
  rw [splay.eq_def]
  simp only [if_neg (Nat.ne_of_lt hqk), if_pos hqk, if_neg h1, if_neg h2]
  rfl

theorem splay_zig_lr_empty {q k lk : Nat} (hqk : q < k) (hlkq : lk < q)
    (ll r : BinaryTree) :
    splay (.node (.node ll lk .empty) k r) q = .node ll lk (.node .empty k r) := by
  have h1 : ¬ q < lk := by omega
  rw [splay.eq_def]
  simp only [if_neg (Nat.ne_of_lt hqk), if_pos hqk, if_neg h1, if_pos hlkq]
  rfl

theorem splay_zag_rl_empty {q k rk : Nat} (hkq : k < q) (hqrk : q < rk)
    (l rr : BinaryTree) :
    splay (.node l k (.node .empty rk rr)) q = .node (.node l k .empty) rk rr := by
  have h1 : q ≠ k := by omega
  have h2 : ¬ q < k := by omega
  rw [splay.eq_def]
  simp only [if_neg h1, if_neg h2, if_pos hqrk]
  rfl

theorem splay_zag_found {q k rk : Nat} (hkq : k < q) (h1 : ¬ q < rk) (h2 : ¬ rk < q)
    (l rl rr : BinaryTree) :
    splay (.node l k (.node rl rk rr)) q = .node (.node l k rl) rk rr := by
  have h3 : q ≠ k := by omega
  have h4 : ¬ q < k := by omega
  rw [splay.eq_def]
  simp only [if_neg h3, if_neg h4, if_neg h1, if_neg h2]
  rfl

theorem splay_zag_rr_empty {q k rk : Nat} (hkq : k < q) (hrkq : rk < q)
    (l rl : BinaryTree) :
    splay (.node l k (.node rl rk .empty)) q = .node (.node l k rl) rk .empty := by
  have h1 : q ≠ k := by omega
  have h2 : ¬ q < k := by omega
  have h3 : ¬ q < rk := by omega
  rw [splay.eq_def]
  simp only [if_neg h1, if_neg h2, if_neg h3, if_pos hrkq]
  rfl



/-- Positive key depth at a node. -/
theorem keyDepth_node_pos (y k : ℕ) (l r : BinaryTree) :
    1 ≤ keyDepth y (.node l k r) := by
  by_cases h1 : y = k
  · rw [keyDepth_node_self h1]
  · by_cases h2 : y < k
    · rw [keyDepth_node_lt h2]
      omega
    · rw [keyDepth_node_gt (by omega)]
      omega

/-- A present key has positive depth. -/
theorem keyDepth_pos_of_mem {q : ℕ} {t : BinaryTree} (h : q ∈ t.toKeyList) :
    1 ≤ keyDepth q t := by
  cases t with
  | empty => simp [BinaryTree.toKeyList] at h
  | node l k r => exact keyDepth_node_pos q k l r


end Splay
