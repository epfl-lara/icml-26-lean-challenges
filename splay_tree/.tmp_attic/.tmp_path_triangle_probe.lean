import Challenges.Splay_Tree.Def_Containment
import Challenges.Splay_Tree.Def_Ackermann
import Challenges.Splay_Tree.Def_Splay

namespace Splay

private theorem toKeyList_length (t : BinaryTree) :
    t.toKeyList.length = t.num_nodes := by
  induction t with
  | empty =>
      simp [BinaryTree.toKeyList, BinaryTree.num_nodes]
  | node l k r ihl ihr =>
      simp [BinaryTree.toKeyList, BinaryTree.num_nodes, ihl, ihr]
      omega

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

private theorem isBST_toKeyList_nodup {t : BinaryTree} (hbst : IsBST t) :
    t.toKeyList.Nodup := by
  induction hbst with
  | left =>
      simp [BinaryTree.toKeyList]
  | node key left right hleft hright _hlbst _hrbst ihl ihr =>
      have hleft_mem : ∀ x : Nat, x ∈ left.toKeyList → x < key :=
        forallTree_iff_forall_mem.mp hleft
      have hright_mem : ∀ x : Nat, x ∈ right.toKeyList → key < x :=
        forallTree_iff_forall_mem.mp hright
      simp only [BinaryTree.toKeyList]
      rw [List.append_assoc]
      simp only [List.singleton_append]
      refine List.Nodup.append ihl ?_ ?_
      · simp [ihr]
        intro hkey_right
        have hkr := hright_mem key hkey_right
        omega
      · intro x hxleft hxrest
        simp at hxrest
        rcases hxrest with hxkey | hxright
        · subst x
          have hkl := hleft_mem key hxleft
          omega
        · have hxl := hleft_mem x hxleft
          have hxr := hright_mem x hxright
          omega

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

private theorem rotateRight_num_nodes (t : BinaryTree) :
    (rotateRight t).num_nodes = t.num_nodes := by
  cases t with
  | empty => simp [rotateRight, BinaryTree.num_nodes]
  | node l k r =>
      cases l with
      | empty => simp [rotateRight, BinaryTree.num_nodes]
      | node a x b =>
          simp [rotateRight, BinaryTree.num_nodes]
          omega

private theorem rotateLeft_num_nodes (t : BinaryTree) :
    (rotateLeft t).num_nodes = t.num_nodes := by
  cases t with
  | empty => simp [rotateLeft, BinaryTree.num_nodes]
  | node l k r =>
      cases r with
      | empty => simp [rotateLeft, BinaryTree.num_nodes]
      | node a x b =>
          simp [rotateLeft, BinaryTree.num_nodes]
          omega

private theorem rotate_num_nodes (t : BinaryTree) (rt : Rot) :
    (rotate t rt).num_nodes = t.num_nodes := by
  cases rt <;> simp [rotate, rotateRight_num_nodes, rotateLeft_num_nodes]
  · cases t with
    | empty => simp
    | node l k r =>
        rw [rotateRight_num_nodes]
        simp [BinaryTree.num_nodes, rotateLeft_num_nodes]
  · cases t with
    | empty => simp
    | node l k r =>
        rw [rotateLeft_num_nodes]
        simp [BinaryTree.num_nodes, rotateRight_num_nodes]

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

private theorem splay_num_nodes : ∀ (t : BinaryTree) (q : Nat),
    (splay t q).num_nodes = t.num_nodes
| .empty, q => by
    simp [splay.eq_def, BinaryTree.num_nodes]
| .node l k r, q => by
    rw [splay.eq_def]
    by_cases hqk : q = k
    · simp [hqk, BinaryTree.num_nodes]
    · by_cases hq_lt_k : q < k
      · cases l with
        | empty =>
            simp [hqk, hq_lt_k, BinaryTree.num_nodes]
        | node ll lk lr =>
            by_cases hq_lt_lk : q < lk
            · cases ll with
              | empty =>
                  simp [hqk, hq_lt_k, hq_lt_lk, BinaryTree.num_nodes,
                    rotate_num_nodes]
              | node a x b =>
                  have hll := splay_num_nodes (BinaryTree.node a x b) q
                  simp [hqk, hq_lt_k, hq_lt_lk, BinaryTree.num_nodes, hll,
                    rotate_num_nodes]
            · by_cases hlk_lt_q : lk < q
              · cases lr with
                | empty =>
                    simp [hqk, hq_lt_k, hq_lt_lk, hlk_lt_q,
                      BinaryTree.num_nodes, rotate_num_nodes]
                | node a x b =>
                    have hlr := splay_num_nodes (BinaryTree.node a x b) q
                    simp [hqk, hq_lt_k, hq_lt_lk, hlk_lt_q,
                      BinaryTree.num_nodes, hlr, rotate_num_nodes]
              · simp [hqk, hq_lt_k, hq_lt_lk, hlk_lt_q,
                  BinaryTree.num_nodes, rotate_num_nodes]
      · cases r with
        | empty =>
            simp [hqk, hq_lt_k, BinaryTree.num_nodes]
        | node rl rk rr =>
            by_cases hq_lt_rk : q < rk
            · cases rl with
              | empty =>
                  simp [hqk, hq_lt_k, hq_lt_rk, BinaryTree.num_nodes,
                    rotate_num_nodes]
              | node a x b =>
                  have hrl := splay_num_nodes (BinaryTree.node a x b) q
                  simp [hqk, hq_lt_k, hq_lt_rk, BinaryTree.num_nodes, hrl,
                    rotate_num_nodes]
            · by_cases hrk_lt_q : rk < q
              · cases rr with
                | empty =>
                    simp [hqk, hq_lt_k, hq_lt_rk, hrk_lt_q,
                      BinaryTree.num_nodes, rotate_num_nodes]
                | node a x b =>
                    have hrr := splay_num_nodes (BinaryTree.node a x b) q
                    simp [hqk, hq_lt_k, hq_lt_rk, hrk_lt_q,
                      BinaryTree.num_nodes, hrr, rotate_num_nodes]
              · simp [hqk, hq_lt_k, hq_lt_rk, hrk_lt_q,
                  BinaryTree.num_nodes, rotate_num_nodes]

private theorem splay_toKeyList : ∀ (t : BinaryTree) (q : Nat),
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

private theorem splay_isBST : ∀ (t : BinaryTree) (q : Nat),
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

private def rootKey : BinaryTree → Option Nat
| .empty => none
| .node _ k _ => some k

private theorem splay_rootKey_eq_some_of_mem_isBST :
    ∀ (t : BinaryTree) (q : Nat), IsBST t → q ∈ t.toKeyList →
      rootKey (splay t q) = some q
| .empty, q, _hbst, hmem => by
    simp [BinaryTree.toKeyList] at hmem
| .node l k r, q, hbst, hmem => by
    rw [splay.eq_def]
    cases hbst with
    | node _ _ _ hleft hright hbst_left hbst_right =>
        by_cases hqk : q = k
        · subst q
          simp [rootKey]
        · by_cases hq_lt_k : q < k
          · have hlmem : q ∈ l.toKeyList := by
              simp [BinaryTree.toKeyList] at hmem
              rcases hmem with hlmem | hqeq | hrmem
              · exact hlmem
              · omega
              · have hkq := (forallTree_iff_forall_mem.mp hright) q hrmem
                omega
            cases l with
            | empty =>
                simp [BinaryTree.toKeyList] at hlmem
            | node ll lk lr =>
                cases hbst_left with
                | node _ _ _ hll_lt_lk hlk_lt_lr hbst_ll hbst_lr =>
                    by_cases hq_lt_lk : q < lk
                    · have hllmem : q ∈ ll.toKeyList := by
                        simp [BinaryTree.toKeyList] at hlmem
                        rcases hlmem with hllmem | hqlk | hlrmem
                        · exact hllmem
                        · omega
                        · have hlkq :=
                            (forallTree_iff_forall_mem.mp hlk_lt_lr) q hlrmem
                          omega
                      cases ll with
                      | empty =>
                          simp [BinaryTree.toKeyList] at hllmem
                      | node a x b =>
                          have ih :=
                            splay_rootKey_eq_some_of_mem_isBST
                              (.node a x b) q hbst_ll hllmem
                          cases hs : splay (.node a x b) q with
                          | empty =>
                              simp [rootKey, hs] at ih
                          | node sl sk sr =>
                              simp [rootKey, hs] at ih
                              subst sk
                              simp [hqk, hq_lt_k, hq_lt_lk, hs, rootKey,
                                rotate, rotateRight]
                    · by_cases hlk_lt_q : lk < q
                      · have hlrmem : q ∈ lr.toKeyList := by
                          simp [BinaryTree.toKeyList] at hlmem
                          rcases hlmem with hllmem | hqlk | hlrmem
                          · have hq_lk :=
                              (forallTree_iff_forall_mem.mp hll_lt_lk) q hllmem
                            omega
                          · omega
                          · exact hlrmem
                        cases lr with
                        | empty =>
                            simp [BinaryTree.toKeyList] at hlrmem
                        | node a x b =>
                            have ih :=
                              splay_rootKey_eq_some_of_mem_isBST
                                (.node a x b) q hbst_lr hlrmem
                            cases hs : splay (.node a x b) q with
                            | empty =>
                                simp [rootKey, hs] at ih
                            | node sl sk sr =>
                                simp [rootKey, hs] at ih
                                subst sk
                                simp [hqk, hq_lt_k, hq_lt_lk, hlk_lt_q, hs,
                                  rootKey, rotate, rotateLeft, rotateRight]
                      · have : q = lk := by omega
                        subst q
                        simp [hqk, hq_lt_k, rootKey, rotate, rotateRight]
          · have hk_lt_q : k < q := by
              exact lt_of_le_of_ne (Nat.le_of_not_lt hq_lt_k)
                (by intro h; exact hqk h.symm)
            have hrmem : q ∈ r.toKeyList := by
              simp [BinaryTree.toKeyList] at hmem
              rcases hmem with hlmem | hqeq | hrmem
              · have hqk' := (forallTree_iff_forall_mem.mp hleft) q hlmem
                omega
              · omega
              · exact hrmem
            cases r with
            | empty =>
                simp [BinaryTree.toKeyList] at hrmem
            | node rl rk rr =>
                cases hbst_right with
                | node _ _ _ hrl_lt_rk hrk_lt_rr hbst_rl hbst_rr =>
                    by_cases hq_lt_rk : q < rk
                    · have hrlmem : q ∈ rl.toKeyList := by
                        simp [BinaryTree.toKeyList] at hrmem
                        rcases hrmem with hrlmem | hqrk | hrrmem
                        · exact hrlmem
                        · omega
                        · have hrkq :=
                            (forallTree_iff_forall_mem.mp hrk_lt_rr) q hrrmem
                          omega
                      cases rl with
                      | empty =>
                          simp [BinaryTree.toKeyList] at hrlmem
                      | node a x b =>
                          have ih :=
                            splay_rootKey_eq_some_of_mem_isBST
                              (.node a x b) q hbst_rl hrlmem
                          cases hs : splay (.node a x b) q with
                          | empty =>
                              simp [rootKey, hs] at ih
                          | node sl sk sr =>
                              simp [rootKey, hs] at ih
                              subst sk
                              simp [hqk, hq_lt_k, hq_lt_rk, hs, rootKey,
                                rotate, rotateLeft, rotateRight]
                    · by_cases hrk_lt_q : rk < q
                      · have hrrmem : q ∈ rr.toKeyList := by
                          simp [BinaryTree.toKeyList] at hrmem
                          rcases hrmem with hrlmem | hqrk | hrrmem
                          · have hqrk' :=
                              (forallTree_iff_forall_mem.mp hrl_lt_rk) q hrlmem
                            omega
                          · omega
                          · exact hrrmem
                        cases rr with
                        | empty =>
                            simp [BinaryTree.toKeyList] at hrrmem
                        | node a x b =>
                            have ih :=
                              splay_rootKey_eq_some_of_mem_isBST
                                (.node a x b) q hbst_rr hrrmem
                            cases hs : splay (.node a x b) q with
                            | empty =>
                                simp [rootKey, hs] at ih
                            | node sl sk sr =>
                                simp [rootKey, hs] at ih
                                subst sk
                                simp [hqk, hq_lt_k, hq_lt_rk, hrk_lt_q, hs,
                                  rootKey, rotate, rotateLeft]
                      · have : q = rk := by omega
                        subst q
                        simp [hqk, hq_lt_k, rootKey, rotate, rotateLeft]

private theorem splay_self_cost_eq_zero_of_mem_isBST
    (t : BinaryTree) (q : Nat) (hbst : IsBST t)
    (hmem : q ∈ t.toKeyList) :
    splay.cost (splay t q) q = 0 := by
  have hroot := splay_rootKey_eq_some_of_mem_isBST t q hbst hmem
  cases hs : splay t q with
  | empty =>
      simp [rootKey, hs] at hroot
  | node l k r =>
      simp [rootKey, hs] at hroot
      subst k
      simp [splay.cost.eq_def]

private def leftEdges : BinaryTree → Nat
| .empty => 0
| .node .empty _ r => leftEdges r
| .node (.node ll lk lr) _ r =>
    1 + leftEdges (.node ll lk lr) + leftEdges r

private def rightEdges : BinaryTree → Nat
| .empty => 0
| .node l _ .empty => rightEdges l
| .node l _ (.node rl rk rr) =>
    1 + rightEdges l + rightEdges (.node rl rk rr)

private theorem leftEdges_le_num_nodes :
    ∀ (t : BinaryTree), leftEdges t ≤ t.num_nodes
| .empty => by
    simp [leftEdges, BinaryTree.num_nodes]
| .node l k r => by
    cases l with
    | empty =>
        have hr := leftEdges_le_num_nodes r
        simp [leftEdges, BinaryTree.num_nodes]
        omega
    | node ll lk lr =>
        have hl := leftEdges_le_num_nodes (.node ll lk lr)
        have hr := leftEdges_le_num_nodes r
        simp [BinaryTree.num_nodes] at hl
        simp [leftEdges, BinaryTree.num_nodes]
        nlinarith

private theorem rightEdges_le_num_nodes :
    ∀ (t : BinaryTree), rightEdges t ≤ t.num_nodes
| .empty => by
    simp [rightEdges, BinaryTree.num_nodes]
| .node l k r => by
    cases r with
    | empty =>
        have hl := rightEdges_le_num_nodes l
        simp [rightEdges, BinaryTree.num_nodes]
        omega
    | node rl rk rr =>
        have hl := rightEdges_le_num_nodes l
        have hr := rightEdges_le_num_nodes (.node rl rk rr)
        simp [BinaryTree.num_nodes] at hr
        simp [rightEdges, BinaryTree.num_nodes]
        nlinarith

private noncomputable def sequentialPotential (t : BinaryTree) : ℝ :=
  2 * leftEdges t + rightEdges t

private def twoChildNodes : BinaryTree → Nat
| .empty => 0
| .node .empty _ .empty => 0
| .node .empty _ (.node rl rk rr) => twoChildNodes (.node rl rk rr)
| .node (.node ll lk lr) _ .empty => twoChildNodes (.node ll lk lr)
| .node (.node ll lk lr) _ (.node rl rk rr) =>
    1 + twoChildNodes (.node ll lk lr) +
      twoChildNodes (.node rl rk rr)

private noncomputable def strongSequentialPotential (t : BinaryTree) : ℝ :=
  10 * leftEdges t + 5 * rightEdges t

private theorem strongSequentialPotential_nonneg (t : BinaryTree) :
    0 ≤ strongSequentialPotential t := by
  unfold strongSequentialPotential
  positivity

private theorem strongSequentialPotential_le_fifteen_num_nodes
    (t : BinaryTree) :
    strongSequentialPotential t ≤ 15 * (t.num_nodes : ℝ) := by
  have hl := leftEdges_le_num_nodes t
  have hr := rightEdges_le_num_nodes t
  have hlR : (leftEdges t : ℝ) ≤ t.num_nodes := by exact_mod_cast hl
  have hrR : (rightEdges t : ℝ) ≤ t.num_nodes := by exact_mod_cast hr
  unfold strongSequentialPotential
  nlinarith [show 0 ≤ (t.num_nodes : ℝ) by positivity]

private abbrev LeftContextFrame := Nat × BinaryTree

private def attachLeftFrames :
    BinaryTree → List LeftContextFrame → BinaryTree
| t, [] => t
| t, (k, r) :: fs => attachLeftFrames (.node t k r) fs

private def rightChainFrames :
    BinaryTree → List LeftContextFrame → BinaryTree
| t, [] => t
| t, (k, r) :: fs => .node t k (rightChainFrames r fs)

private def framePayloadNodes : List LeftContextFrame → Nat
| [] => 0
| (_k, r) :: fs => 1 + r.num_nodes + framePayloadNodes fs

private def leftMinDepth : BinaryTree → Nat
| .empty => 0
| .node .empty _ _ => 0
| .node (.node ll lk lr) _ _ =>
    1 + leftMinDepth (.node ll lk lr)

private theorem leftMinDepth_le_num_nodes :
    ∀ (t : BinaryTree), leftMinDepth t ≤ t.num_nodes
| .empty => by
    simp [leftMinDepth, BinaryTree.num_nodes]
| .node .empty k r => by
    simp [leftMinDepth, BinaryTree.num_nodes]
| .node (.node ll lk lr) k r => by
    have h := leftMinDepth_le_num_nodes (.node ll lk lr)
    simp [leftMinDepth, BinaryTree.num_nodes] at h ⊢
    omega

private def deleteMinContextResult :
    BinaryTree → List LeftContextFrame → BinaryTree
| .empty, fs => rightChainFrames .empty fs
| .node .empty _ r, fs => rightChainFrames r fs
| .node (.node .empty _ lr) k r, fs =>
    rightChainFrames lr ((k, r) :: fs)
| .node (.node (.node a x b) lk lr) k r, fs =>
    deleteMinContextResult (.node a x b) ((lk, lr) :: (k, r) :: fs)

private def splayMinFramesRev :
    BinaryTree → List LeftContextFrame → BinaryTree
| t, [] => t
| t, [(k, r)] => .node t k r
| t, (b, br) :: (a, ar) :: fs =>
    .node (splayMinFramesRev t fs) a (.node ar b br)

private def splayMinContextResult
    (t : BinaryTree) (fs : List LeftContextFrame) : BinaryTree :=
  splayMinFramesRev t fs.reverse

private def splayMinUnwindResult :
    BinaryTree → List LeftContextFrame → BinaryTree
| .empty, fs => splayMinContextResult .empty fs
| .node .empty _ r, fs => splayMinContextResult r fs
| .node (.node .empty _ lr) k r, fs =>
    splayMinContextResult lr ((k, r) :: fs)
| .node (.node (.node a x b) lk lr) k r, fs =>
    splayMinUnwindResult (.node a x b) ((lk, lr) :: (k, r) :: fs)

private noncomputable def twoFrameCredit
    (fs : List LeftContextFrame) : ℝ :=
  if 2 ≤ fs.length then 2 else 0

private theorem framePayloadNodes_append
    (fs gs : List LeftContextFrame) :
    framePayloadNodes (fs ++ gs) =
      framePayloadNodes fs + framePayloadNodes gs := by
  induction fs with
  | nil =>
      simp [framePayloadNodes]
  | cons fr fs ih =>
      rcases fr with ⟨k, r⟩
      simp [framePayloadNodes, ih]
      omega

private theorem framePayloadNodes_reverse
    (fs : List LeftContextFrame) :
    framePayloadNodes fs.reverse = framePayloadNodes fs := by
  induction fs with
  | nil =>
      simp [framePayloadNodes]
  | cons fr fs ih =>
      rcases fr with ⟨k, r⟩
      rw [List.reverse_cons, framePayloadNodes_append]
      simp [framePayloadNodes, ih]
      omega

private theorem attachLeftFrames_append
    (t : BinaryTree) (fs gs : List LeftContextFrame) :
    attachLeftFrames t (fs ++ gs) =
      attachLeftFrames (attachLeftFrames t fs) gs := by
  induction fs generalizing t with
  | nil =>
      simp [attachLeftFrames]
  | cons fr fs ih =>
      rcases fr with ⟨k, r⟩
      simp [attachLeftFrames, ih]

private theorem attachLeftFrames_num_nodes
    (t : BinaryTree) (fs : List LeftContextFrame) :
    (attachLeftFrames t fs).num_nodes =
      t.num_nodes + framePayloadNodes fs := by
  induction fs generalizing t with
  | nil =>
      simp [attachLeftFrames, framePayloadNodes]
  | cons fr fs ih =>
      rcases fr with ⟨k, r⟩
      simp [attachLeftFrames, framePayloadNodes, ih, BinaryTree.num_nodes]
      omega

private theorem rightChainFrames_num_nodes
    (t : BinaryTree) (fs : List LeftContextFrame) :
    (rightChainFrames t fs).num_nodes =
      t.num_nodes + framePayloadNodes fs := by
  induction fs generalizing t with
  | nil =>
      simp [rightChainFrames, framePayloadNodes]
  | cons fr fs ih =>
      rcases fr with ⟨k, r⟩
      simp [rightChainFrames, framePayloadNodes, ih, BinaryTree.num_nodes]
      omega

private theorem splayMinFramesRev_num_nodes_pair
    (fs : List LeftContextFrame) :
    (∀ t : BinaryTree,
      (splayMinFramesRev t fs).num_nodes =
        t.num_nodes + framePayloadNodes fs) ∧
    (∀ (t : BinaryTree) (fr : LeftContextFrame),
      (splayMinFramesRev t (fr :: fs)).num_nodes =
        t.num_nodes + framePayloadNodes (fr :: fs)) := by
  induction fs with
  | nil =>
      constructor
      · intro t
        simp [splayMinFramesRev, framePayloadNodes]
      · intro t fr
        rcases fr with ⟨k, r⟩
        simp [splayMinFramesRev, framePayloadNodes, BinaryTree.num_nodes]
        omega
  | cons fr fs ih =>
      rcases fr with ⟨a, ar⟩
      rcases ih with ⟨ih0, ih1⟩
      constructor
      · intro t
        exact ih1 t (a, ar)
      · intro t fr0
        rcases fr0 with ⟨b, br⟩
        have hih := ih0 t
        simp [splayMinFramesRev, framePayloadNodes, BinaryTree.num_nodes]
        rw [hih]
        omega

private theorem splayMinFramesRev_num_nodes
    (t : BinaryTree) (fs : List LeftContextFrame) :
    (splayMinFramesRev t fs).num_nodes =
      t.num_nodes + framePayloadNodes fs :=
  (splayMinFramesRev_num_nodes_pair fs).1 t

private theorem splayMinContextResult_num_nodes
    (t : BinaryTree) (fs : List LeftContextFrame) :
    (splayMinContextResult t fs).num_nodes =
      t.num_nodes + framePayloadNodes fs := by
  unfold splayMinContextResult
  rw [splayMinFramesRev_num_nodes, framePayloadNodes_reverse]

private theorem twoFrameCredit_nil :
    twoFrameCredit [] = 0 := by
  simp [twoFrameCredit]

private theorem twoFrameCredit_single
    (fr : LeftContextFrame) :
    twoFrameCredit [fr] = 0 := by
  simp [twoFrameCredit]

private theorem twoFrameCredit_cons_cons
    (fr₁ fr₂ : LeftContextFrame) (fs : List LeftContextFrame) :
    twoFrameCredit (fr₁ :: fr₂ :: fs) = 2 := by
  simp [twoFrameCredit]

private theorem twoFrameCredit_nonneg
    (fs : List LeftContextFrame) :
    0 ≤ twoFrameCredit fs := by
  unfold twoFrameCredit
  split <;> norm_num

private theorem twoFrameCredit_le_two
    (fs : List LeftContextFrame) :
    twoFrameCredit fs ≤ 2 := by
  unfold twoFrameCredit
  split <;> norm_num

private theorem twoFrameCredit_reverse
    (fs : List LeftContextFrame) :
    twoFrameCredit fs.reverse = twoFrameCredit fs := by
  unfold twoFrameCredit
  rw [List.length_reverse]

private theorem twoFrameCredit_cons_le
    (fr : LeftContextFrame) (fs : List LeftContextFrame) :
    twoFrameCredit fs ≤ twoFrameCredit (fr :: fs) := by
  cases fs with
  | nil =>
      simp [twoFrameCredit]
  | cons fr₂ fs =>
      cases fs with
      | nil =>
          simp [twoFrameCredit]
      | cons fr₃ fs =>
          simp [twoFrameCredit]

private theorem splayMinUnwindResult_num_nodes_add_one :
    ∀ (t : BinaryTree) (fs : List LeftContextFrame),
      0 < t.num_nodes →
      (splayMinUnwindResult t fs).num_nodes + 1 =
        (attachLeftFrames t fs).num_nodes
| .empty, fs, hpos => by
    simp [BinaryTree.num_nodes] at hpos
| .node .empty k r, fs, _hpos => by
    simp [splayMinUnwindResult]
    rw [splayMinContextResult_num_nodes, attachLeftFrames_num_nodes]
    simp [BinaryTree.num_nodes]
    omega
| .node (.node .empty lk lr) k r, fs, _hpos => by
    simp [splayMinUnwindResult]
    rw [splayMinContextResult_num_nodes, attachLeftFrames_num_nodes]
    simp [framePayloadNodes, BinaryTree.num_nodes]
    omega
| .node (.node (.node a x b) lk lr) k r, fs, _hpos => by
    have ih := splayMinUnwindResult_num_nodes_add_one
      (.node a x b) ((lk, lr) :: (k, r) :: fs)
      (by simp [BinaryTree.num_nodes])
    simpa [splayMinUnwindResult, attachLeftFrames, framePayloadNodes,
      BinaryTree.num_nodes] using ih

private theorem deleteMinContextResult_num_nodes_add_one :
    ∀ (t : BinaryTree) (fs : List LeftContextFrame),
      0 < t.num_nodes →
      (deleteMinContextResult t fs).num_nodes + 1 =
        (attachLeftFrames t fs).num_nodes
| .empty, fs, hpos => by
    simp [BinaryTree.num_nodes] at hpos
| .node .empty k r, fs, _hpos => by
    simp [deleteMinContextResult]
    rw [rightChainFrames_num_nodes, attachLeftFrames_num_nodes]
    simp [BinaryTree.num_nodes]
    omega
| .node (.node .empty lk lr) k r, fs, _hpos => by
    simp [deleteMinContextResult]
    rw [rightChainFrames_num_nodes, attachLeftFrames_num_nodes]
    simp [framePayloadNodes, BinaryTree.num_nodes]
    omega
| .node (.node (.node a x b) lk lr) k r, fs, _hpos => by
    have ih := deleteMinContextResult_num_nodes_add_one
      (.node a x b) ((lk, lr) :: (k, r) :: fs)
      (by simp [BinaryTree.num_nodes])
    simpa [deleteMinContextResult, attachLeftFrames, framePayloadNodes,
      BinaryTree.num_nodes] using ih

private theorem strongSequentialPotential_attachLeftFrames_le
    (t : BinaryTree) (fs : List LeftContextFrame) :
    strongSequentialPotential (attachLeftFrames t fs) ≤
      15 * ((t.num_nodes + framePayloadNodes fs : Nat) : ℝ) := by
  have h := strongSequentialPotential_le_fifteen_num_nodes
    (attachLeftFrames t fs)
  rw [attachLeftFrames_num_nodes] at h
  exact h

private theorem strongSequentialPotential_rightChainFrames_le
    (t : BinaryTree) (fs : List LeftContextFrame) :
    strongSequentialPotential (rightChainFrames t fs) ≤
      15 * ((t.num_nodes + framePayloadNodes fs : Nat) : ℝ) := by
  have h := strongSequentialPotential_le_fifteen_num_nodes
    (rightChainFrames t fs)
  rw [rightChainFrames_num_nodes] at h
  exact h

private theorem strongSequentialPotential_splayMinContextResult_le
    (t : BinaryTree) (fs : List LeftContextFrame) :
    strongSequentialPotential (splayMinContextResult t fs) ≤
      15 * ((t.num_nodes + framePayloadNodes fs : Nat) : ℝ) := by
  have h := strongSequentialPotential_le_fifteen_num_nodes
    (splayMinContextResult t fs)
  rw [splayMinContextResult_num_nodes] at h
  exact h

private def nonemptyIndicator : BinaryTree → Nat
| .empty => 0
| .node _ _ _ => 1

private theorem strongSequentialPotential_node_eq
    (l r : BinaryTree) (k : Nat) :
    strongSequentialPotential (.node l k r) =
      strongSequentialPotential l + strongSequentialPotential r +
        10 * (nonemptyIndicator l : ℝ) +
        5 * (nonemptyIndicator r : ℝ) := by
  cases l <;> cases r <;>
    simp [strongSequentialPotential, leftEdges, rightEdges,
      nonemptyIndicator] <;>
    ring

private theorem nonemptyIndicator_attachLeftFrames_node
    (l r : BinaryTree) (k : Nat) (fs : List LeftContextFrame) :
    nonemptyIndicator (attachLeftFrames (.node l k r) fs) = 1 := by
  induction fs generalizing l k r with
  | nil =>
      simp [attachLeftFrames, nonemptyIndicator]
  | cons fr fs ih =>
      rcases fr with ⟨fk, frt⟩
      simpa [attachLeftFrames] using ih (.node l k r) frt fk

private def frameKeysAbove (q : Nat) : List LeftContextFrame → Prop
| [] => True
| (k, _r) :: fs => q < k ∧ frameKeysAbove q fs

private theorem frameKeysAbove_append
    (q : Nat) (fs gs : List LeftContextFrame) :
    frameKeysAbove q (fs ++ gs) ↔
      frameKeysAbove q fs ∧ frameKeysAbove q gs := by
  induction fs with
  | nil =>
      simp [frameKeysAbove]
  | cons fr fs ih =>
      rcases fr with ⟨k, r⟩
      simp [frameKeysAbove, ih]
      tauto

private theorem isBST_of_isBST_attachLeftFrames :
    ∀ (t : BinaryTree) (fs : List LeftContextFrame),
      IsBST (attachLeftFrames t fs) → IsBST t
| t, [], hbst => by
    simpa [attachLeftFrames] using hbst
| t, (k, r) :: fs, hbst => by
    have hnode :
        IsBST (.node t k r) :=
      isBST_of_isBST_attachLeftFrames (.node t k r) fs
        (by simpa [attachLeftFrames] using hbst)
    cases hnode with
    | node _ _ _ _hleft _hright hbst_left _hbst_right =>
        exact hbst_left

private theorem mem_toKeyList_attachLeftFrames_of_mem
    (t : BinaryTree) (fs : List LeftContextFrame) {q : Nat}
    (hmem : q ∈ t.toKeyList) :
    q ∈ (attachLeftFrames t fs).toKeyList := by
  induction fs generalizing t with
  | nil =>
      simpa [attachLeftFrames] using hmem
  | cons fr fs ih =>
      rcases fr with ⟨k, r⟩
      exact ih (.node t k r) (by
        simp [BinaryTree.toKeyList, hmem])

private theorem frameKeysAbove_of_isBST_attachLeftFrames_mem :
    ∀ (t : BinaryTree) (fs : List LeftContextFrame) (q : Nat),
      IsBST (attachLeftFrames t fs) →
      q ∈ t.toKeyList →
      frameKeysAbove q fs
| t, [], q, _hbst, _hmem => by
    simp [frameKeysAbove]
| t, (k, r) :: fs, q, hbst, hmem => by
    have hbst_node :
        IsBST (.node t k r) :=
      isBST_of_isBST_attachLeftFrames (.node t k r) fs
        (by simpa [attachLeftFrames] using hbst)
    have hqk : q < k := by
      cases hbst_node with
      | node _ _ _ hleft _hright _hbst_left _hbst_right =>
          exact (forallTree_iff_forall_mem.mp hleft) q hmem
    have htail :
        frameKeysAbove q fs :=
      frameKeysAbove_of_isBST_attachLeftFrames_mem (.node t k r) fs q
        (by simpa [attachLeftFrames] using hbst)
        (by simp [BinaryTree.toKeyList, hmem])
    exact ⟨hqk, htail⟩

private theorem search_path_len_attachLeftFrames_of_frameKeysAbove
    (t : BinaryTree) (q : Nat) :
    ∀ (fs : List LeftContextFrame),
      frameKeysAbove q fs →
      (attachLeftFrames t fs).search_path_len q =
        fs.length + t.search_path_len q
| [], _hframes => by
    simp [attachLeftFrames]
| (k, r) :: fs, hframes => by
    have hqk : q < k := hframes.1
    have htail : frameKeysAbove q fs := hframes.2
    have ih :=
      search_path_len_attachLeftFrames_of_frameKeysAbove
        (.node t k r) q fs htail
    simp [attachLeftFrames]
    rw [ih]
    simp [BinaryTree.search_path_len, hqk]
    omega

private theorem splay_attachLeftFrames_left_empty_eq_rev
    (r : BinaryTree) (k : Nat) :
    ∀ (rs : List LeftContextFrame),
      frameKeysAbove k rs.reverse →
      splay (attachLeftFrames (.node .empty k r) rs.reverse) k =
        .node .empty k (splayMinFramesRev r rs)
| [], _hframes => by
    simp [attachLeftFrames, splay.eq_def, splayMinFramesRev]
| [(pk, ctx)], hframes => by
    have hk_pk : k < pk := by
      simpa [frameKeysAbove] using hframes
    have hneq : k ≠ pk := by omega
    simp [attachLeftFrames, splay.eq_def, splayMinFramesRev,
      hneq, hk_pk, rotate, rotateRight]
| (bk, br) :: (ak, ar) :: rs, hframes => by
    have hsplit :
        frameKeysAbove k (rs.reverse ++ [(ak, ar), (bk, br)]) := by
      simpa [List.reverse_cons] using hframes
    have hframes_rs : frameKeysAbove k rs.reverse :=
      (frameKeysAbove_append k rs.reverse [(ak, ar), (bk, br)]).mp
        hsplit |>.1
    have hk_ak : k < ak := by
      have htail :=
        (frameKeysAbove_append k rs.reverse [(ak, ar), (bk, br)]).mp
          hsplit |>.2
      simpa [frameKeysAbove] using htail.1
    have hk_bk : k < bk := by
      have htail :=
        (frameKeysAbove_append k rs.reverse [(ak, ar), (bk, br)]).mp
          hsplit |>.2
      simpa [frameKeysAbove] using htail.2.1
    have hne_b : k ≠ bk := by omega
    have hne_a : k ≠ ak := by omega
    have ih :=
      splay_attachLeftFrames_left_empty_eq_rev r k rs hframes_rs
    rw [List.reverse_cons, List.reverse_cons]
    simp only [List.singleton_append, List.append_assoc]
    repeat rw [attachLeftFrames_append]
    simp [attachLeftFrames]
    cases hT : attachLeftFrames (.node .empty k r) rs.reverse with
    | empty =>
        simp [hT, splay.eq_def] at ih
    | node tl tk tr =>
        have ihT :
            splay (.node tl tk tr) k =
              .node .empty k (splayMinFramesRev r rs) := by
          simpa [hT] using ih
        rw [splay.eq_def]
        simp only [hne_b, hk_bk, hk_ak, ihT, if_false, if_true]
        simp [rotate, rotateRight, splayMinFramesRev]

private theorem splay_attachLeftFrames_left_empty_eq
    (r : BinaryTree) (k : Nat) (fs : List LeftContextFrame)
    (hframes : frameKeysAbove k fs) :
    splay (attachLeftFrames (.node .empty k r) fs) k =
      .node .empty k (splayMinContextResult r fs) := by
  have h :=
    splay_attachLeftFrames_left_empty_eq_rev r k fs.reverse
      (by simpa using hframes)
  simpa [splayMinContextResult] using h

private theorem attachLeftFrames_zigzig_context
    (a b lr r : BinaryTree) (x lk k : Nat)
    (fs : List LeftContextFrame) :
    attachLeftFrames (.node a x b) ((lk, lr) :: (k, r) :: fs) =
      attachLeftFrames (.node (.node (.node a x b) lk lr) k r) fs := by
  simp [attachLeftFrames]

private theorem frameKeysAbove_zigzig_context_of_isBST
    {a b lr r : BinaryTree} {x lk k q : Nat}
    {fs : List LeftContextFrame}
    (hbst :
      IsBST (attachLeftFrames
        (.node (.node (.node a x b) lk lr) k r) fs))
    (hmem : q ∈ (BinaryTree.node a x b).toKeyList) :
    frameKeysAbove q ((lk, lr) :: (k, r) :: fs) := by
  have hbst_inner_context :
      IsBST (attachLeftFrames (.node a x b)
        ((lk, lr) :: (k, r) :: fs)) := by
    simpa [attachLeftFrames] using hbst
  exact frameKeysAbove_of_isBST_attachLeftFrames_mem
    (.node a x b) ((lk, lr) :: (k, r) :: fs) q
    hbst_inner_context hmem

private theorem splayMinFramesRev_left_empty_potential_le_pair
    (r : BinaryTree) (k : Nat) :
    ∀ rs : List LeftContextFrame,
      (strongSequentialPotential (splayMinFramesRev r rs) +
          twoFrameCredit rs ≤
        strongSequentialPotential
          (attachLeftFrames (.node .empty k r) rs.reverse)) ∧
      (∀ fr : LeftContextFrame,
        strongSequentialPotential (splayMinFramesRev r (fr :: rs)) +
            twoFrameCredit (fr :: rs) ≤
          strongSequentialPotential
            (attachLeftFrames (.node .empty k r) (fr :: rs).reverse))
| [] => by
    constructor
    · cases r <;>
        simp [splayMinFramesRev, twoFrameCredit, attachLeftFrames,
          strongSequentialPotential, leftEdges, rightEdges]
    · intro fr
      rcases fr with ⟨a, ar⟩
      cases r <;> cases ar <;>
        simp [splayMinFramesRev, twoFrameCredit, attachLeftFrames,
          strongSequentialPotential, leftEdges, rightEdges]
| fr :: rs => by
    rcases fr with ⟨a, ar⟩
    rcases splayMinFramesRev_left_empty_potential_le_pair r k rs with
      ⟨ih0, ih1⟩
    constructor
    · exact ih1 (a, ar)
    · intro fr0
      rcases fr0 with ⟨b, br⟩
      cases rs with
      | nil =>
          cases r <;> cases ar <;> cases br <;>
            simp [splayMinFramesRev, twoFrameCredit, attachLeftFrames,
              strongSequentialPotential, leftEdges, rightEdges] <;>
            ring_nf <;>
            nlinarith
      | cons fr1 rs =>
          cases rs with
          | nil =>
              rcases fr1 with ⟨c, cr⟩
              cases r <;> cases ar <;> cases br <;> cases cr <;>
                simp [splayMinFramesRev, twoFrameCredit, attachLeftFrames,
                  strongSequentialPotential, leftEdges, rightEdges] <;>
                ring_nf <;>
                nlinarith
          | cons fr2 rs =>
              have hcredit_inner :
                  twoFrameCredit (fr1 :: fr2 :: rs) = 2 := by
                simp [twoFrameCredit]
              rw [hcredit_inner] at ih0
              simp [List.reverse_cons] at ih0
              have hcredit :
                  twoFrameCredit ((a, ar) :: fr1 :: fr2 :: rs) = 2 := by
                simp [twoFrameCredit]
              have hcredit_outer :
                  twoFrameCredit ((b, br) :: (a, ar) :: fr1 :: fr2 :: rs) =
                    2 := by
                simp [twoFrameCredit]
              have hprev_nonneg :=
                strongSequentialPotential_nonneg
                  (splayMinFramesRev r (fr1 :: fr2 :: rs))
              have hattach_nonempty :
                  nonemptyIndicator
                    (attachLeftFrames (.node .empty k r)
                      (fr1 :: fr2 :: rs).reverse) = 1 := by
                exact nonemptyIndicator_attachLeftFrames_node .empty r k
                  (fr1 :: fr2 :: rs).reverse
              have hattach_inner_nonempty :
                  nonemptyIndicator
                    (attachLeftFrames (.node .empty k r)
                      ((fr2 :: rs).reverse ++ [fr1])) = 1 := by
                simpa [List.reverse_cons] using hattach_nonempty
              simp [List.reverse_cons, List.append_assoc] at hattach_inner_nonempty
              simp [splayMinFramesRev, strongSequentialPotential_node_eq] at ih0
              have hprev_ind :
                  (nonemptyIndicator
                    (splayMinFramesRev r (fr1 :: fr2 :: rs)) : ℝ) ≤ 1 := by
                cases (splayMinFramesRev r (fr1 :: fr2 :: rs)) <;>
                  simp [nonemptyIndicator]
              have har_ind :
                  (nonemptyIndicator ar : ℝ) ≤ 1 := by
                cases ar <;> simp [nonemptyIndicator]
              have hattach_node_ind :
                  (nonemptyIndicator
                    (.node
                      (attachLeftFrames (.node .empty k r)
                        (rs.reverse ++ [fr2, fr1])) a ar) : ℝ) = 1 := by
                simp [nonemptyIndicator]
              have hprev_node_ind :
                  (nonemptyIndicator
                    (.node (splayMinFramesRev r rs) fr2.1
                      (.node fr2.2 fr1.1 fr1.2)) : ℝ) = 1 := by
                simp [nonemptyIndicator]
              have hfr_node_ind :
                  (nonemptyIndicator (.node fr2.2 fr1.1 fr1.2) : ℝ) = 1 := by
                simp [nonemptyIndicator]
              have harbr_node_ind :
                  (nonemptyIndicator (.node ar b br) : ℝ) = 1 := by
                simp [nonemptyIndicator]
              rw [List.reverse_cons, List.reverse_cons]
              simp only [List.singleton_append, List.append_assoc]
              repeat rw [attachLeftFrames_append]
              simp [splayMinFramesRev, attachLeftFrames,
                strongSequentialPotential_node_eq, hattach_inner_nonempty,
                hcredit_outer]
              rw [hattach_node_ind, hprev_node_ind, hfr_node_ind,
                harbr_node_ind]
              rw [hfr_node_ind] at ih0
              ring_nf
              ring_nf at ih0
              nlinarith [ih0, har_ind]

private theorem splayMinFramesRev_left_empty_potential_le
    (r : BinaryTree) (k : Nat) (rs : List LeftContextFrame) :
    strongSequentialPotential (splayMinFramesRev r rs) +
        twoFrameCredit rs ≤
      strongSequentialPotential
        (attachLeftFrames (.node .empty k r) rs.reverse) :=
  (splayMinFramesRev_left_empty_potential_le_pair r k rs).1

private theorem splayMinContextResult_left_empty_potential_le
    (r : BinaryTree) (k : Nat) (fs : List LeftContextFrame) :
    strongSequentialPotential (splayMinContextResult r fs) +
        twoFrameCredit fs ≤
      strongSequentialPotential
        (attachLeftFrames (.node .empty k r) fs) := by
  unfold splayMinContextResult
  have h := splayMinFramesRev_left_empty_potential_le r k fs.reverse
  rw [List.reverse_reverse] at h
  rwa [twoFrameCredit_reverse] at h

private noncomputable def sequentialDeletePotential (t : BinaryTree) : ℝ :=
  sequentialPotential t + 2 * nonemptyIndicator t

private theorem sequentialPotential_nonneg (t : BinaryTree) :
    0 ≤ sequentialPotential t := by
  unfold sequentialPotential
  positivity

private theorem nonemptyIndicator_le_num_nodes :
    ∀ (t : BinaryTree), nonemptyIndicator t ≤ t.num_nodes
| .empty => by
    simp [nonemptyIndicator, BinaryTree.num_nodes]
| .node l k r => by
    simp [nonemptyIndicator, BinaryTree.num_nodes]
    omega

private theorem sequentialDeletePotential_nonneg (t : BinaryTree) :
    0 ≤ sequentialDeletePotential t := by
  have hseq := sequentialPotential_nonneg t
  unfold sequentialDeletePotential
  nlinarith [show 0 ≤ (nonemptyIndicator t : ℝ) by positivity]

private theorem sequentialPotential_le_three_num_nodes (t : BinaryTree) :
    sequentialPotential t ≤ 3 * (t.num_nodes : ℝ) := by
  have hl := leftEdges_le_num_nodes t
  have hr := rightEdges_le_num_nodes t
  unfold sequentialPotential
  have hlR : (leftEdges t : ℝ) ≤ t.num_nodes := by exact_mod_cast hl
  have hrR : (rightEdges t : ℝ) ≤ t.num_nodes := by exact_mod_cast hr
  nlinarith [show 0 ≤ (t.num_nodes : ℝ) by positivity]

private theorem sequentialDeletePotential_le_five_num_nodes
    (t : BinaryTree) :
    sequentialDeletePotential t ≤ 5 * (t.num_nodes : ℝ) := by
  have hseq := sequentialPotential_le_three_num_nodes t
  have hne := nonemptyIndicator_le_num_nodes t
  have hneR : (nonemptyIndicator t : ℝ) ≤ t.num_nodes := by
    exact_mod_cast hne
  unfold sequentialDeletePotential
  nlinarith [show 0 ≤ (t.num_nodes : ℝ) by positivity]

private theorem sequentialDeletePotential_empty :
    sequentialDeletePotential .empty = 0 := by
  simp [sequentialDeletePotential, sequentialPotential, leftEdges,
    rightEdges, nonemptyIndicator]

private theorem sequentialDeletePotential_node
    (l r : BinaryTree) (k : Nat) :
    sequentialDeletePotential (.node l k r) =
      sequentialPotential (.node l k r) + 2 := by
  simp [sequentialDeletePotential, nonemptyIndicator]

private theorem search_path_len_eq_one_of_rootKey_eq_some
    {t : BinaryTree} {q : Nat} (hroot : rootKey t = some q) :
    t.search_path_len q = 1 := by
  cases t with
  | empty =>
      simp [rootKey] at hroot
  | node l k r =>
      simp [rootKey] at hroot
      subst k
      simp [BinaryTree.search_path_len]

private theorem splay_eq_self_of_rootKey_eq_some
    {t : BinaryTree} {q : Nat} (hroot : rootKey t = some q) :
    splay t q = t := by
  cases t with
  | empty =>
      simp [rootKey] at hroot
  | node l k r =>
      simp [rootKey] at hroot
      subst k
      simp [splay.eq_def]

private theorem rootKey_mem_toKeyList
    {t : BinaryTree} {q : Nat} (hroot : rootKey t = some q) :
    q ∈ t.toKeyList := by
  cases t with
  | empty =>
      simp [rootKey] at hroot
  | node l k r =>
      simp [rootKey] at hroot
      subst k
      simp [BinaryTree.toKeyList]

private theorem eq_empty_of_toKeyList_no_mem {t : BinaryTree}
    (hmem : ∀ k : Nat, k ∈ t.toKeyList → False) :
    t = .empty := by
  cases t with
  | empty => rfl
  | node l k r =>
      exfalso
      exact hmem k (by simp [BinaryTree.toKeyList])

private def leftSubtree : BinaryTree → BinaryTree
| .empty => .empty
| .node l _ _ => l

private def rightSubtree : BinaryTree → BinaryTree
| .empty => .empty
| .node _ _ r => r

private theorem leftSubtree_num_nodes_le (t : BinaryTree) :
    (leftSubtree t).num_nodes ≤ t.num_nodes := by
  cases t with
  | empty =>
      simp [leftSubtree, BinaryTree.num_nodes]
  | node l k r =>
      simp [leftSubtree, BinaryTree.num_nodes]
      omega

private theorem rightSubtree_num_nodes_le (t : BinaryTree) :
    (rightSubtree t).num_nodes ≤ t.num_nodes := by
  cases t with
  | empty =>
      simp [rightSubtree, BinaryTree.num_nodes]
  | node l k r =>
      simp [rightSubtree, BinaryTree.num_nodes]

private theorem attachLeftFrames_left_right_of_rootKey
    {t : BinaryTree} {q : Nat}
    (hroot : rootKey t = some q) :
    attachLeftFrames (leftSubtree t) [(q, rightSubtree t)] = t := by
  cases t with
  | empty =>
      simp [rootKey] at hroot
  | node l k r =>
      simp [rootKey] at hroot
      subst k
      simp [attachLeftFrames, leftSubtree, rightSubtree]

private theorem mem_leftSubtree_of_root_lt_isBST
    {t : BinaryTree} {q x : Nat}
    (hbst : IsBST t) (hroot : rootKey t = some q)
    (hxmem : x ∈ t.toKeyList) (hlt : x < q) :
    x ∈ (leftSubtree t).toKeyList := by
  cases t with
  | empty =>
      simp [rootKey] at hroot
  | node l k r =>
      simp [rootKey] at hroot
      subst k
      cases hbst with
      | node _ _ _ _hleft hright _hlbst _hrbst =>
          simp [leftSubtree, BinaryTree.toKeyList] at hxmem ⊢
          rcases hxmem with hxl | hxq | hxr
          · exact hxl
          · omega
          · have hq_lt_x : q < x :=
              (forallTree_iff_forall_mem.mp hright) x hxr
            omega

private theorem frameKeysAbove_singleton_of_mem_leftSubtree_root
    {t : BinaryTree} {q x : Nat}
    (hbst : IsBST t) (hroot : rootKey t = some q)
    (hx : x ∈ (leftSubtree t).toKeyList) :
    frameKeysAbove x [(q, rightSubtree t)] := by
  cases t with
  | empty =>
      simp [rootKey] at hroot
  | node l k r =>
      simp [rootKey] at hroot
      subst k
      cases hbst with
          | node _ _ _ hleft _hright _hlbst _hrbst =>
          simp [leftSubtree] at hx
          simp [frameKeysAbove]
          exact (forallTree_iff_forall_mem.mp hleft) x hx

private theorem mem_rightSubtree_of_root_gt_isBST
    {t : BinaryTree} {q x : Nat}
    (hbst : IsBST t) (hroot : rootKey t = some q)
    (hxmem : x ∈ t.toKeyList) (hgt : q < x) :
    x ∈ (rightSubtree t).toKeyList := by
  cases t with
  | empty =>
      simp [rootKey] at hroot
  | node l k r =>
      simp [rootKey] at hroot
      subst k
      cases hbst with
      | node _ _ _ hleft _hright _hlbst _hrbst =>
          simp [rightSubtree, BinaryTree.toKeyList] at hxmem ⊢
          rcases hxmem with hxl | hxq | hxr
          · have hx_lt_q :=
              (forallTree_iff_forall_mem.mp hleft) x hxl
            omega
          · omega
          · exact hxr

private theorem rightSubtree_splay_attachLeftFrames_left_empty_eq
    (r : BinaryTree) (k : Nat) (fs : List LeftContextFrame)
    (hframes : frameKeysAbove k fs) :
    rightSubtree (splay (attachLeftFrames (.node .empty k r) fs) k) =
      splayMinContextResult r fs := by
  rw [splay_attachLeftFrames_left_empty_eq r k fs hframes]
  simp [rightSubtree]

private theorem leftSubtree_empty_of_root_min_isBST
    {t : BinaryTree} {q : Nat}
    (hbst : IsBST t) (hroot : rootKey t = some q)
    (hmin : ∀ k : Nat, k ∈ t.toKeyList → q ≤ k) :
    leftSubtree t = .empty := by
  cases t with
  | empty =>
      simp [rootKey] at hroot
  | node l k r =>
      simp [rootKey] at hroot
      subst k
      cases hbst with
      | node _ _ _ hleft _hright _hlbst _hrbst =>
          simp [leftSubtree]
          apply eq_empty_of_toKeyList_no_mem
          intro x hx
          have hx_lt : x < q :=
            (forallTree_iff_forall_mem.mp hleft) x hx
          have hq_le_x : q ≤ x :=
            hmin x (by simp [BinaryTree.toKeyList, hx])
          omega

private theorem splay_leftSubtree_empty_of_min_isBST
    (t : BinaryTree) (q : Nat) (hbst : IsBST t)
    (hmem : q ∈ t.toKeyList)
    (hmin : ∀ k : Nat, k ∈ t.toKeyList → q ≤ k) :
    leftSubtree (splay t q) = .empty := by
  have hroot := splay_rootKey_eq_some_of_mem_isBST t q hbst hmem
  have hbst_s := splay_isBST t q hbst
  have hmin_s : ∀ k : Nat, k ∈ (splay t q).toKeyList → q ≤ k := by
    intro k hk
    rw [splay_toKeyList] at hk
    exact hmin k hk
  exact leftSubtree_empty_of_root_min_isBST hbst_s hroot hmin_s

private theorem rightSubtree_num_nodes_add_one_of_root_left_empty
    {t : BinaryTree} {q : Nat}
    (hroot : rootKey t = some q) (hleft : leftSubtree t = .empty) :
    (rightSubtree t).num_nodes + 1 = t.num_nodes := by
  cases t with
  | empty =>
      simp [rootKey] at hroot
  | node l k r =>
      simp [rootKey] at hroot
      subst k
      cases l with
      | empty =>
          simp [rightSubtree, BinaryTree.num_nodes]
          omega
      | node ll lk lr =>
          simp [leftSubtree] at hleft

private theorem splay_min_rightSubtree_num_nodes_add_one
    (t : BinaryTree) (q : Nat) (hbst : IsBST t)
    (hmem : q ∈ t.toKeyList)
    (hmin : ∀ k : Nat, k ∈ t.toKeyList → q ≤ k) :
    (rightSubtree (splay t q)).num_nodes + 1 = t.num_nodes := by
  have hroot := splay_rootKey_eq_some_of_mem_isBST t q hbst hmem
  have hleft := splay_leftSubtree_empty_of_min_isBST t q hbst hmem hmin
  have hnum :=
    rightSubtree_num_nodes_add_one_of_root_left_empty hroot hleft
  rw [splay_num_nodes t q] at hnum
  exact hnum

private theorem mem_rightSubtree_of_root_left_empty_gt
    {t : BinaryTree} {q x : Nat}
    (hroot : rootKey t = some q) (hleft : leftSubtree t = .empty)
    (hxmem : x ∈ t.toKeyList) (hgt : q < x) :
    x ∈ (rightSubtree t).toKeyList := by
  cases t with
  | empty =>
      simp [BinaryTree.toKeyList] at hxmem
  | node l k r =>
      simp [rootKey] at hroot
      subst k
      cases l with
      | empty =>
          simp [rightSubtree, BinaryTree.toKeyList] at hxmem ⊢
          rcases hxmem with hxq | hxr
          · omega
          · exact hxr
      | node ll lk lr =>
          simp [leftSubtree] at hleft

private theorem mem_rightSubtree_splay_min_of_gt
    (t : BinaryTree) (q x : Nat) (hbst : IsBST t)
    (hmem : q ∈ t.toKeyList)
    (hmin : ∀ k : Nat, k ∈ t.toKeyList → q ≤ k)
    (hxmem : x ∈ t.toKeyList) (hgt : q < x) :
    x ∈ (rightSubtree (splay t q)).toKeyList := by
  have hroot := splay_rootKey_eq_some_of_mem_isBST t q hbst hmem
  have hleft := splay_leftSubtree_empty_of_min_isBST t q hbst hmem hmin
  apply mem_rightSubtree_of_root_left_empty_gt hroot hleft
  · rw [splay_toKeyList]
    exact hxmem
  · exact hgt

private theorem mem_rightSubtree_splay_min_iff_gt
    (t : BinaryTree) (q x : Nat) (hbst : IsBST t)
    (hmem : q ∈ t.toKeyList)
    (hmin : ∀ k : Nat, k ∈ t.toKeyList → q ≤ k) :
    x ∈ (rightSubtree (splay t q)).toKeyList ↔
      x ∈ t.toKeyList ∧ q < x := by
  constructor
  · intro hx
    have hroot := splay_rootKey_eq_some_of_mem_isBST t q hbst hmem
    have hbst_s := splay_isBST t q hbst
    cases hs : splay t q with
    | empty =>
        rw [hs] at hx
        simp [rightSubtree, BinaryTree.toKeyList] at hx
    | node l k r =>
        rw [hs] at hx
        simp [rootKey, hs] at hroot
        subst k
        simp [rightSubtree] at hx
        have hx_mem_s : x ∈ (splay t q).toKeyList := by
          rw [hs]
          simp [BinaryTree.toKeyList, hx]
        have hx_mem_t : x ∈ t.toKeyList := by
          rw [splay_toKeyList] at hx_mem_s
          exact hx_mem_s
        have hq_lt_x : q < x := by
          rw [hs] at hbst_s
          cases hbst_s with
          | node _ _ _ _hleft hright _hlbst _hrbst =>
              exact (forallTree_iff_forall_mem.mp hright) x hx
        exact ⟨hx_mem_t, hq_lt_x⟩
  · intro hx
    exact mem_rightSubtree_splay_min_of_gt t q x hbst hmem hmin
      hx.1 hx.2

private theorem rightSubtree_empty_of_root_max_isBST
    {t : BinaryTree} {q : Nat}
    (hbst : IsBST t) (hroot : rootKey t = some q)
    (hmax : ∀ k : Nat, k ∈ t.toKeyList → k ≤ q) :
    rightSubtree t = .empty := by
  cases t with
  | empty =>
      simp [rootKey] at hroot
  | node l k r =>
      simp [rootKey] at hroot
      subst k
      cases hbst with
      | node _ _ _ _hleft hright _hlbst _hrbst =>
          simp [rightSubtree]
          apply eq_empty_of_toKeyList_no_mem
          intro x hx
          have hq_lt_x : q < x :=
            (forallTree_iff_forall_mem.mp hright) x hx
          have hx_le_q : x ≤ q :=
            hmax x (by simp [BinaryTree.toKeyList, hx])
          omega

private theorem splay_rightSubtree_empty_of_max_isBST
    (t : BinaryTree) (q : Nat) (hbst : IsBST t)
    (hmem : q ∈ t.toKeyList)
    (hmax : ∀ k : Nat, k ∈ t.toKeyList → k ≤ q) :
    rightSubtree (splay t q) = .empty := by
  have hroot := splay_rootKey_eq_some_of_mem_isBST t q hbst hmem
  have hbst_s := splay_isBST t q hbst
  have hmax_s : ∀ k : Nat, k ∈ (splay t q).toKeyList → k ≤ q := by
    intro k hk
    rw [splay_toKeyList] at hk
    exact hmax k hk
  exact rightSubtree_empty_of_root_max_isBST hbst_s hroot hmax_s

private theorem leftSubtree_num_nodes_add_one_of_root_right_empty
    {t : BinaryTree} {q : Nat}
    (hroot : rootKey t = some q) (hright : rightSubtree t = .empty) :
    (leftSubtree t).num_nodes + 1 = t.num_nodes := by
  cases t with
  | empty =>
      simp [rootKey] at hroot
  | node l k r =>
      simp [rootKey] at hroot
      subst k
      cases r with
      | empty =>
          simp [leftSubtree, BinaryTree.num_nodes]
          omega
      | node rl rk rr =>
          simp [rightSubtree] at hright

private theorem splay_max_leftSubtree_num_nodes_add_one
    (t : BinaryTree) (q : Nat) (hbst : IsBST t)
    (hmem : q ∈ t.toKeyList)
    (hmax : ∀ k : Nat, k ∈ t.toKeyList → k ≤ q) :
    (leftSubtree (splay t q)).num_nodes + 1 = t.num_nodes := by
  have hroot := splay_rootKey_eq_some_of_mem_isBST t q hbst hmem
  have hright := splay_rightSubtree_empty_of_max_isBST
    t q hbst hmem hmax
  have hnum :=
    leftSubtree_num_nodes_add_one_of_root_right_empty hroot hright
  rw [splay_num_nodes t q] at hnum
  exact hnum

private theorem mem_leftSubtree_of_root_right_empty_lt
    {t : BinaryTree} {q x : Nat}
    (hroot : rootKey t = some q) (hright : rightSubtree t = .empty)
    (hxmem : x ∈ t.toKeyList) (hlt : x < q) :
    x ∈ (leftSubtree t).toKeyList := by
  cases t with
  | empty =>
      simp [BinaryTree.toKeyList] at hxmem
  | node l k r =>
      simp [rootKey] at hroot
      subst k
      cases r with
      | empty =>
          simp [leftSubtree, BinaryTree.toKeyList] at hxmem ⊢
          rcases hxmem with hxl | hxq
          · exact hxl
          · omega
      | node rl rk rr =>
          simp [rightSubtree] at hright

private theorem mem_leftSubtree_splay_max_of_lt
    (t : BinaryTree) (q x : Nat) (hbst : IsBST t)
    (hmem : q ∈ t.toKeyList)
    (hmax : ∀ k : Nat, k ∈ t.toKeyList → k ≤ q)
    (hxmem : x ∈ t.toKeyList) (hlt : x < q) :
    x ∈ (leftSubtree (splay t q)).toKeyList := by
  have hroot := splay_rootKey_eq_some_of_mem_isBST t q hbst hmem
  have hright := splay_rightSubtree_empty_of_max_isBST
    t q hbst hmem hmax
  apply mem_leftSubtree_of_root_right_empty_lt hroot hright
  · rw [splay_toKeyList]
    exact hxmem
  · exact hlt

private theorem mem_leftSubtree_splay_max_iff_lt
    (t : BinaryTree) (q x : Nat) (hbst : IsBST t)
    (hmem : q ∈ t.toKeyList)
    (hmax : ∀ k : Nat, k ∈ t.toKeyList → k ≤ q) :
    x ∈ (leftSubtree (splay t q)).toKeyList ↔
      x ∈ t.toKeyList ∧ x < q := by
  constructor
  · intro hx
    have hroot := splay_rootKey_eq_some_of_mem_isBST t q hbst hmem
    have hbst_s := splay_isBST t q hbst
    cases hs : splay t q with
    | empty =>
        rw [hs] at hx
        simp [leftSubtree, BinaryTree.toKeyList] at hx
    | node l k r =>
        rw [hs] at hx
        simp [rootKey, hs] at hroot
        subst k
        simp [leftSubtree] at hx
        have hx_mem_s : x ∈ (splay t q).toKeyList := by
          rw [hs]
          simp [BinaryTree.toKeyList, hx]
        have hx_mem_t : x ∈ t.toKeyList := by
          rw [splay_toKeyList] at hx_mem_s
          exact hx_mem_s
        have hx_lt_q : x < q := by
          rw [hs] at hbst_s
          cases hbst_s with
          | node _ _ _ hleft _hright _hlbst _hrbst =>
              exact (forallTree_iff_forall_mem.mp hleft) x hx
        exact ⟨hx_mem_t, hx_lt_q⟩
  · intro hx
    exact mem_leftSubtree_splay_max_of_lt t q x hbst hmem hmax
      hx.1 hx.2

private theorem rightSubtree_isBST_of_isBST :
    ∀ {t : BinaryTree}, IsBST t → IsBST (rightSubtree t)
| .empty, _hbst => by
    simp [rightSubtree]
    exact IsBST.left
| .node l k r, hbst => by
    cases hbst with
    | node _ _ _ _hleft _hright _hlbst hrbst =>
        simpa [rightSubtree] using hrbst

private theorem leftSubtree_isBST_of_isBST :
    ∀ {t : BinaryTree}, IsBST t → IsBST (leftSubtree t)
| .empty, _hbst => by
    simp [leftSubtree]
    exact IsBST.left
| .node l k r, hbst => by
    cases hbst with
    | node _ _ _ _hleft _hright hlbst _hrbst =>
        simpa [leftSubtree] using hlbst

private theorem rightSubtree_splay_min_isBST
    (t : BinaryTree) (q : Nat) (hbst : IsBST t) :
    IsBST (rightSubtree (splay t q)) := by
  exact rightSubtree_isBST_of_isBST (splay_isBST t q hbst)

private theorem leftSubtree_splay_max_isBST
    (t : BinaryTree) (q : Nat) (hbst : IsBST t) :
    IsBST (leftSubtree (splay t q)) := by
  exact leftSubtree_isBST_of_isBST (splay_isBST t q hbst)

private theorem future_mem_rightSubtree_splay_min_of_gt {n : Nat}
    (Y : Fin n → Nat) (t : BinaryTree) (q : Nat)
    (hbst : IsBST t) (hmemq : q ∈ t.toKeyList)
    (hmin : ∀ k : Nat, k ∈ t.toKeyList → q ≤ k)
    (hYmem : ∀ i : Fin n, Y i ∈ t.toKeyList)
    (hgt : ∀ i : Fin n, q < Y i) :
    ∀ i : Fin n, Y i ∈ (rightSubtree (splay t q)).toKeyList := by
  intro i
  exact mem_rightSubtree_splay_min_of_gt t q (Y i) hbst hmemq hmin
    (hYmem i) (hgt i)

private theorem future_mem_leftSubtree_splay_max_of_lt {n : Nat}
    (Y : Fin n → Nat) (t : BinaryTree) (q : Nat)
    (hbst : IsBST t) (hmemq : q ∈ t.toKeyList)
    (hmax : ∀ k : Nat, k ∈ t.toKeyList → k ≤ q)
    (hYmem : ∀ i : Fin n, Y i ∈ t.toKeyList)
    (hlt : ∀ i : Fin n, Y i < q) :
    ∀ i : Fin n, Y i ∈ (leftSubtree (splay t q)).toKeyList := by
  intro i
  exact mem_leftSubtree_splay_max_of_lt t q (Y i) hbst hmemq hmax
    (hYmem i) (hlt i)

private theorem splay_min_delete_state {n : Nat}
    (Y : Fin n → Nat) (t : BinaryTree) (q : Nat)
    (hbst : IsBST t) (hmemq : q ∈ t.toKeyList)
    (hmin : ∀ k : Nat, k ∈ t.toKeyList → q ≤ k)
    (hYmem : ∀ i : Fin n, Y i ∈ t.toKeyList)
    (hgt : ∀ i : Fin n, q < Y i) :
    ((rightSubtree (splay t q)).num_nodes + 1 = t.num_nodes) ∧
      IsBST (rightSubtree (splay t q)) ∧
      (∀ i : Fin n, Y i ∈ (rightSubtree (splay t q)).toKeyList) := by
  exact ⟨splay_min_rightSubtree_num_nodes_add_one t q hbst hmemq hmin,
    rightSubtree_splay_min_isBST t q hbst,
    future_mem_rightSubtree_splay_min_of_gt Y t q hbst hmemq hmin hYmem hgt⟩

private theorem splay_max_delete_state {n : Nat}
    (Y : Fin n → Nat) (t : BinaryTree) (q : Nat)
    (hbst : IsBST t) (hmemq : q ∈ t.toKeyList)
    (hmax : ∀ k : Nat, k ∈ t.toKeyList → k ≤ q)
    (hYmem : ∀ i : Fin n, Y i ∈ t.toKeyList)
    (hlt : ∀ i : Fin n, Y i < q) :
    ((leftSubtree (splay t q)).num_nodes + 1 = t.num_nodes) ∧
      IsBST (leftSubtree (splay t q)) ∧
      (∀ i : Fin n, Y i ∈ (leftSubtree (splay t q)).toKeyList) := by
  exact ⟨splay_max_leftSubtree_num_nodes_add_one t q hbst hmemq hmax,
    leftSubtree_splay_max_isBST t q hbst,
    future_mem_leftSubtree_splay_max_of_lt Y t q hbst hmemq hmax
      hYmem hlt⟩

private theorem min_eq_root_of_left_empty
    {r : BinaryTree} {k q : Nat}
    (hbst : IsBST (.node .empty k r))
    (hmem : q ∈ (BinaryTree.node .empty k r).toKeyList)
    (hmin : ∀ x : Nat, x ∈ (BinaryTree.node .empty k r).toKeyList → q ≤ x) :
    q = k := by
  cases hbst with
  | node _ _ _ _hleft hright _hlbst _hrbst =>
      simp [BinaryTree.toKeyList] at hmem
      rcases hmem with hqk | hqr
      · exact hqk
      · have hk_le_q : k ≤ q := by
          exact Nat.le_of_lt ((forallTree_iff_forall_mem.mp hright) q hqr)
        have hq_le_k : q ≤ k := hmin k (by simp [BinaryTree.toKeyList])
        omega

private theorem min_mem_left_of_left_nonempty
    {ll lr r : BinaryTree} {lk k q : Nat}
    (hbst : IsBST (.node (.node ll lk lr) k r))
    (hmem : q ∈ (BinaryTree.node (.node ll lk lr) k r).toKeyList)
    (hmin : ∀ x : Nat,
      x ∈ (BinaryTree.node (.node ll lk lr) k r).toKeyList → q ≤ x) :
    q ∈ (BinaryTree.node ll lk lr).toKeyList := by
  cases hbst with
  | node _ _ _ hleft hright _hlbst _hrbst =>
      change q ∈ (BinaryTree.node ll lk lr).toKeyList ++ [k] ++ r.toKeyList at hmem
      simp at hmem
      rcases hmem with hqleft | hqk | hqr
      · exact hqleft
      · subst q
        have hlk_lt_k : lk < k :=
          (forallTree_iff_forall_mem.mp hleft) lk
            (by simp [BinaryTree.toKeyList])
        have hk_le_lk : k ≤ lk :=
          hmin lk (by
            change lk ∈ (BinaryTree.node ll lk lr).toKeyList ++ [k] ++
              r.toKeyList
            simp [BinaryTree.toKeyList])
        omega
      · have hk_lt_q : k < q :=
          (forallTree_iff_forall_mem.mp hright) q hqr
        have hlk_lt_k : lk < k :=
          (forallTree_iff_forall_mem.mp hleft) lk
            (by simp [BinaryTree.toKeyList])
        have hq_le_lk : q ≤ lk :=
          hmin lk (by
            change lk ∈ (BinaryTree.node ll lk lr).toKeyList ++ [k] ++
              r.toKeyList
            simp [BinaryTree.toKeyList])
        omega

private theorem min_restrict_left_of_left_nonempty
    {ll lr r : BinaryTree} {lk k q : Nat}
    (hmin : ∀ x : Nat,
      x ∈ (BinaryTree.node (.node ll lk lr) k r).toKeyList → q ≤ x) :
    ∀ x : Nat, x ∈ (BinaryTree.node ll lk lr).toKeyList → q ≤ x := by
  intro x hx
  exact hmin x (by
    change x ∈ (BinaryTree.node ll lk lr).toKeyList ++ [k] ++ r.toKeyList
    simp [hx])

private theorem min_eq_left_root_of_left_left_empty
    {lr r : BinaryTree} {lk k q : Nat}
    (hbst : IsBST (.node (.node .empty lk lr) k r))
    (hmem : q ∈ (BinaryTree.node (.node .empty lk lr) k r).toKeyList)
    (hmin : ∀ x : Nat,
      x ∈ (BinaryTree.node (.node .empty lk lr) k r).toKeyList → q ≤ x) :
    q = lk := by
  have hqleft :=
    min_mem_left_of_left_nonempty hbst hmem hmin
  cases hbst with
  | node _ _ _ _hleft _hright hbst_left _hrbst =>
      exact min_eq_root_of_left_empty hbst_left hqleft
        (min_restrict_left_of_left_nonempty hmin)

private theorem min_mem_left_left_of_left_left_nonempty
    {a b lr r : BinaryTree} {x lk k q : Nat}
    (hbst : IsBST (.node (.node (.node a x b) lk lr) k r))
    (hmem : q ∈
      (BinaryTree.node (.node (.node a x b) lk lr) k r).toKeyList)
    (hmin : ∀ y : Nat,
      y ∈ (BinaryTree.node (.node (.node a x b) lk lr) k r).toKeyList →
        q ≤ y) :
    q ∈ (BinaryTree.node a x b).toKeyList := by
  have hqleft :=
    min_mem_left_of_left_nonempty hbst hmem hmin
  cases hbst with
  | node _ _ _ _hleft _hright hbst_left _hrbst =>
      exact min_mem_left_of_left_nonempty hbst_left hqleft
        (min_restrict_left_of_left_nonempty hmin)

private theorem min_restrict_left_left_of_left_left_nonempty
    {a b lr r : BinaryTree} {x lk k q : Nat}
    (hmin : ∀ y : Nat,
      y ∈ (BinaryTree.node (.node (.node a x b) lk lr) k r).toKeyList →
        q ≤ y) :
    ∀ y : Nat, y ∈ (BinaryTree.node a x b).toKeyList → q ≤ y := by
  intro y hy
  have hy_left :
      y ∈ (BinaryTree.node (.node a x b) lk lr).toKeyList := by
    change y ∈ (BinaryTree.node a x b).toKeyList ++ [lk] ++ lr.toKeyList
    simp [hy]
  exact hmin y (by
    change y ∈ (BinaryTree.node (.node a x b) lk lr).toKeyList ++ [k] ++
      r.toKeyList
    simp [hy_left])

private theorem isBST_left_left_of_left_left_nonempty
    {a b lr r : BinaryTree} {x lk k : Nat}
    (hbst : IsBST (.node (.node (.node a x b) lk lr) k r)) :
    IsBST (.node a x b) := by
  cases hbst with
  | node _ _ _ _hleft _hright hbst_left _hrbst =>
      cases hbst_left with
      | node _ _ _ _hll _hlr hbst_ll _hbst_lr =>
          exact hbst_ll

private theorem min_lt_left_root_of_left_left_nonempty
    {a b lr r : BinaryTree} {x lk k q : Nat}
    (hbst : IsBST (.node (.node (.node a x b) lk lr) k r))
    (hmem : q ∈
      (BinaryTree.node (.node (.node a x b) lk lr) k r).toKeyList)
    (hmin : ∀ y : Nat,
      y ∈ (BinaryTree.node (.node (.node a x b) lk lr) k r).toKeyList →
        q ≤ y) :
    q < lk := by
  have hqinner :
      q ∈ (BinaryTree.node a x b).toKeyList :=
    min_mem_left_left_of_left_left_nonempty hbst hmem hmin
  cases hbst with
  | node _ _ _ _hleft _hright hbst_left _hrbst =>
      cases hbst_left with
      | node _ _ _ hleft_left _hright_left _hbst_ll _hbst_lr =>
          exact (forallTree_iff_forall_mem.mp hleft_left) q hqinner

private theorem min_left_left_state_of_left_left_nonempty
    {a b lr r : BinaryTree} {x lk k q : Nat}
    (hbst : IsBST (.node (.node (.node a x b) lk lr) k r))
    (hmem : q ∈
      (BinaryTree.node (.node (.node a x b) lk lr) k r).toKeyList)
    (hmin : ∀ y : Nat,
      y ∈ (BinaryTree.node (.node (.node a x b) lk lr) k r).toKeyList →
        q ≤ y) :
    IsBST (.node a x b) ∧
      q ∈ (BinaryTree.node a x b).toKeyList ∧
      (∀ y : Nat, y ∈ (BinaryTree.node a x b).toKeyList → q ≤ y) ∧
      q < lk := by
  exact ⟨isBST_left_left_of_left_left_nonempty hbst,
    min_mem_left_left_of_left_left_nonempty hbst hmem hmin,
    min_restrict_left_left_of_left_left_nonempty hmin,
    min_lt_left_root_of_left_left_nonempty hbst hmem hmin⟩

private theorem splay_min_delete_step_left_empty
    {r : BinaryTree} {k q : Nat}
    (hbst : IsBST (.node .empty k r))
    (hmem : q ∈ (BinaryTree.node .empty k r).toKeyList)
    (hmin : ∀ x : Nat, x ∈ (BinaryTree.node .empty k r).toKeyList → q ≤ x) :
    splay.cost (.node .empty k r) q +
        sequentialDeletePotential (rightSubtree (splay (.node .empty k r) q)) ≤
      sequentialPotential (.node .empty k r) + 2 := by
  have hq : q = k := min_eq_root_of_left_empty hbst hmem hmin
  subst q
  cases r with
  | empty =>
      simp [splay.cost.eq_def, splay.eq_def, rightSubtree,
        sequentialDeletePotential, sequentialPotential, leftEdges, rightEdges,
        nonemptyIndicator]
  | node rl rk rr =>
      simp [splay.cost.eq_def, splay.eq_def, rightSubtree,
        sequentialDeletePotential, sequentialPotential, leftEdges, rightEdges,
        nonemptyIndicator]

private theorem splay_min_delete_step_left_left_empty
    {lr r : BinaryTree} {lk k q : Nat}
    (hbst : IsBST (.node (.node .empty lk lr) k r))
    (hmem : q ∈ (BinaryTree.node (.node .empty lk lr) k r).toKeyList)
    (hmin : ∀ x : Nat,
      x ∈ (BinaryTree.node (.node .empty lk lr) k r).toKeyList → q ≤ x) :
    splay.cost (.node (.node .empty lk lr) k r) q +
        sequentialDeletePotential
          (rightSubtree (splay (.node (.node .empty lk lr) k r) q)) ≤
      sequentialPotential (.node (.node .empty lk lr) k r) + 2 := by
  have hq : q = lk := min_eq_left_root_of_left_left_empty hbst hmem hmin
  subst q
  have hlk_lt_k : lk < k := by
    cases hbst with
    | node _ _ _ hleft _hright _hlbst _hrbst =>
        exact (forallTree_iff_forall_mem.mp hleft) lk
          (by simp [BinaryTree.toKeyList])
  have hneq : lk ≠ k := by omega
  cases lr with
  | empty =>
      cases r with
      | empty =>
          simp [splay.cost.eq_def, splay.eq_def, hneq, hlk_lt_k, rotate, rotateRight,
            rightSubtree, sequentialDeletePotential, sequentialPotential,
            leftEdges, rightEdges, nonemptyIndicator]
      | node rl rk rr =>
          simp [splay.cost.eq_def, splay.eq_def, hneq, hlk_lt_k, rotate, rotateRight,
            rightSubtree, sequentialDeletePotential, sequentialPotential,
            leftEdges, rightEdges, nonemptyIndicator]
          nlinarith [show 0 ≤ (leftEdges (BinaryTree.node rl rk rr) : ℝ) by positivity,
            show 0 ≤ (rightEdges (BinaryTree.node rl rk rr) : ℝ) by positivity]
  | node lrl lrk lrr =>
      cases r with
      | empty =>
          simp [splay.cost.eq_def, splay.eq_def, hneq, hlk_lt_k, rotate, rotateRight,
            rightSubtree, sequentialDeletePotential, sequentialPotential,
            leftEdges, rightEdges, nonemptyIndicator]
          nlinarith [show 0 ≤ (leftEdges (BinaryTree.node lrl lrk lrr) : ℝ) by positivity,
            show 0 ≤ (rightEdges (BinaryTree.node lrl lrk lrr) : ℝ) by positivity]
      | node rl rk rr =>
          simp [splay.cost.eq_def, splay.eq_def, hneq, hlk_lt_k, rotate, rotateRight,
            rightSubtree, sequentialDeletePotential, sequentialPotential,
            leftEdges, rightEdges, nonemptyIndicator]
          nlinarith [show 0 ≤ (leftEdges (BinaryTree.node lrl lrk lrr) : ℝ) by positivity,
            show 0 ≤ (rightEdges (BinaryTree.node lrl lrk lrr) : ℝ) by positivity,
            show 0 ≤ (leftEdges (BinaryTree.node rl rk rr) : ℝ) by positivity,
            show 0 ≤ (rightEdges (BinaryTree.node rl rk rr) : ℝ) by positivity]

private theorem splay_min_delete_step_left_empty_strong
    {r : BinaryTree} {k q : Nat}
    (hbst : IsBST (.node .empty k r))
    (hmem : q ∈ (BinaryTree.node .empty k r).toKeyList)
    (hmin : ∀ x : Nat, x ∈ (BinaryTree.node .empty k r).toKeyList → q ≤ x) :
    splay.cost (.node .empty k r) q +
        strongSequentialPotential (rightSubtree (splay (.node .empty k r) q)) ≤
      strongSequentialPotential (.node .empty k r) := by
  have hq : q = k := min_eq_root_of_left_empty hbst hmem hmin
  subst q
  cases r with
  | empty =>
      simp [splay.cost.eq_def, splay.eq_def, rightSubtree,
        strongSequentialPotential, leftEdges, rightEdges]
  | node rl rk rr =>
      simp [splay.cost.eq_def, splay.eq_def, rightSubtree,
        strongSequentialPotential, leftEdges, rightEdges]

private theorem splay_min_delete_step_left_left_empty_strong
    {lr r : BinaryTree} {lk k q : Nat}
    (hbst : IsBST (.node (.node .empty lk lr) k r))
    (hmem : q ∈ (BinaryTree.node (.node .empty lk lr) k r).toKeyList)
    (hmin : ∀ x : Nat,
      x ∈ (BinaryTree.node (.node .empty lk lr) k r).toKeyList → q ≤ x) :
    splay.cost (.node (.node .empty lk lr) k r) q +
        strongSequentialPotential
          (rightSubtree (splay (.node (.node .empty lk lr) k r) q)) ≤
      strongSequentialPotential (.node (.node .empty lk lr) k r) := by
  have hq : q = lk := min_eq_left_root_of_left_left_empty hbst hmem hmin
  subst q
  have hlk_lt_k : lk < k := by
    cases hbst with
    | node _ _ _ hleft _hright _hlbst _hrbst =>
        exact (forallTree_iff_forall_mem.mp hleft) lk
          (by simp [BinaryTree.toKeyList])
  have hneq : lk ≠ k := by omega
  cases lr with
  | empty =>
      cases r with
      | empty =>
          simp [splay.cost.eq_def, splay.eq_def, hneq, hlk_lt_k, rotate,
            rotateRight, rightSubtree, strongSequentialPotential, leftEdges,
            rightEdges]
      | node rl rk rr =>
          simp [splay.cost.eq_def, splay.eq_def, hneq, hlk_lt_k, rotate,
            rotateRight, rightSubtree, strongSequentialPotential, leftEdges,
            rightEdges]
          ring_nf
          nlinarith [show 0 ≤ (leftEdges (BinaryTree.node rl rk rr) : ℝ) by positivity,
            show 0 ≤ (rightEdges (BinaryTree.node rl rk rr) : ℝ) by positivity]
  | node lrl lrk lrr =>
      cases r with
      | empty =>
          simp [splay.cost.eq_def, splay.eq_def, hneq, hlk_lt_k, rotate,
            rotateRight, rightSubtree, strongSequentialPotential, leftEdges,
            rightEdges]
          ring_nf
          nlinarith [show 0 ≤ (leftEdges (BinaryTree.node lrl lrk lrr) : ℝ) by positivity,
            show 0 ≤ (rightEdges (BinaryTree.node lrl lrk lrr) : ℝ) by positivity]
      | node rl rk rr =>
          simp [splay.cost.eq_def, splay.eq_def, hneq, hlk_lt_k, rotate,
            rotateRight, rightSubtree, strongSequentialPotential, leftEdges,
            rightEdges]
          ring_nf
          nlinarith [show 0 ≤ (leftEdges (BinaryTree.node lrl lrk lrr) : ℝ) by positivity,
            show 0 ≤ (rightEdges (BinaryTree.node lrl lrk lrr) : ℝ) by positivity,
            show 0 ≤ (leftEdges (BinaryTree.node rl rk rr) : ℝ) by positivity,
            show 0 ≤ (rightEdges (BinaryTree.node rl rk rr) : ℝ) by positivity]

private theorem splay_min_delete_step_zigzig_strong
    {a b lr r : BinaryTree} {x lk k q : Nat}
    (hbst : IsBST (.node (.node (.node a x b) lk lr) k r))
    (hmem : q ∈
      (BinaryTree.node (.node (.node a x b) lk lr) k r).toKeyList)
    (hmin : ∀ y : Nat,
      y ∈ (BinaryTree.node (.node (.node a x b) lk lr) k r).toKeyList →
        q ≤ y)
    (hinner :
      splay.cost (.node a x b) q +
          strongSequentialPotential
            (rightSubtree (splay (.node a x b) q)) ≤
        strongSequentialPotential (.node a x b)) :
    splay.cost (.node (.node (.node a x b) lk lr) k r) q +
        strongSequentialPotential
          (rightSubtree
            (splay (.node (.node (.node a x b) lk lr) k r) q)) ≤
      strongSequentialPotential
        (.node (.node (.node a x b) lk lr) k r) + 2 := by
  rcases min_left_left_state_of_left_left_nonempty hbst hmem hmin with
    ⟨hbst_inner, hmem_inner, hmin_inner, hq_lt_lk⟩
  have hlk_lt_k : lk < k := by
    cases hbst with
    | node _ _ _ hleft _hright _hlbst _hrbst =>
        exact (forallTree_iff_forall_mem.mp hleft) lk
          (by simp [BinaryTree.toKeyList])
  have hq_lt_k : q < k := by omega
  have hq_ne_k : q ≠ k := by omega
  have hroot :=
    splay_rootKey_eq_some_of_mem_isBST (.node a x b) q hbst_inner hmem_inner
  have hleft :=
    splay_leftSubtree_empty_of_min_isBST (.node a x b) q hbst_inner
      hmem_inner hmin_inner
  cases hs : splay (.node a x b) q with
  | empty =>
      simp [rootKey, hs] at hroot
  | node sl sk sr =>
      simp [rootKey, hs] at hroot
      subst sk
      cases sl with
      | empty =>
          rw [hs] at hinner
          have hcost_outer :
              splay.cost (.node (.node (.node a x b) lk lr) k r) q =
                splay.cost (.node a x b) q + 2 := by
            rw [splay.cost.eq_def]
            simp only [hq_ne_k, hq_lt_k, hq_lt_lk, if_false, if_true]
          have hsplay_outer :
              splay (.node (.node (.node a x b) lk lr) k r) q =
                .node .empty q (.node sr lk (.node lr k r)) := by
            rw [splay.eq_def]
            simp only [hq_ne_k, hq_lt_k, hq_lt_lk, if_false, if_true, hs]
            simp [rotate, rotateRight]
          rw [hcost_outer, hsplay_outer]
          cases sr with
          | empty =>
              cases lr with
              | empty =>
                  cases r with
                  | empty =>
                      simp [rightSubtree, strongSequentialPotential, leftEdges,
                        rightEdges] at hinner ⊢
                      ring_nf at hinner ⊢
                      nlinarith
                  | node rl rk rr =>
                      simp [rightSubtree, strongSequentialPotential, leftEdges,
                        rightEdges] at hinner ⊢
                      ring_nf at hinner ⊢
                      nlinarith
              | node lrl lrk lrr =>
                  cases r with
                  | empty =>
                      simp [rightSubtree, strongSequentialPotential, leftEdges,
                        rightEdges] at hinner ⊢
                      ring_nf at hinner ⊢
                      nlinarith
                  | node rl rk rr =>
                      simp [rightSubtree, strongSequentialPotential, leftEdges,
                        rightEdges] at hinner ⊢
                      ring_nf at hinner ⊢
                      nlinarith
          | node srl srk srr =>
              cases lr with
              | empty =>
                  cases r with
                  | empty =>
                      simp [rightSubtree, strongSequentialPotential, leftEdges,
                        rightEdges] at hinner ⊢
                      ring_nf at hinner ⊢
                      nlinarith
                  | node rl rk rr =>
                      simp [rightSubtree, strongSequentialPotential, leftEdges,
                        rightEdges] at hinner ⊢
                      ring_nf at hinner ⊢
                      nlinarith
              | node lrl lrk lrr =>
                  cases r with
                  | empty =>
                      simp [rightSubtree, strongSequentialPotential, leftEdges,
                        rightEdges] at hinner ⊢
                      ring_nf at hinner ⊢
                      nlinarith
                  | node rl rk rr =>
                      simp [rightSubtree, strongSequentialPotential, leftEdges,
                        rightEdges] at hinner ⊢
                      ring_nf at hinner ⊢
                      nlinarith
      | node sll slk slr =>
          simp [leftSubtree, hs] at hleft

private theorem stack_left_empty_nil_strong
    {r : BinaryTree} {k q : Nat}
    (hq : q = k) :
    splay.cost (attachLeftFrames (.node .empty k r) []) q +
        strongSequentialPotential (rightChainFrames r []) ≤
      strongSequentialPotential (attachLeftFrames (.node .empty k r) []) := by
  subst q
  cases r <;>
    simp [attachLeftFrames, rightChainFrames, splay.cost.eq_def,
      strongSequentialPotential, leftEdges, rightEdges]

private theorem stack_left_empty_one_frame_strong
    {r ctx : BinaryTree} {k pk q : Nat}
    (hq : q = k) (hk_pk : k < pk) :
    splay.cost (attachLeftFrames (.node .empty k r) [(pk, ctx)]) q +
        strongSequentialPotential (rightChainFrames r [(pk, ctx)]) ≤
      strongSequentialPotential
        (attachLeftFrames (.node .empty k r) [(pk, ctx)]) := by
  subst q
  have hk_ne_pk : k ≠ pk := by omega
  cases r <;> cases ctx <;>
    simp [attachLeftFrames, rightChainFrames, splay.cost.eq_def,
      hk_ne_pk, hk_pk, strongSequentialPotential, leftEdges, rightEdges] <;>
    ring_nf <;>
    nlinarith

private theorem stack_left_empty_two_frames_strong
    {r lr ctx : BinaryTree} {k lk pk q : Nat}
    (hq : q = k) (hk_lk : k < lk) (hlk_pk : lk < pk) :
    splay.cost
          (attachLeftFrames (.node .empty k r) [(lk, lr), (pk, ctx)]) q +
        strongSequentialPotential
          (rightChainFrames r [(lk, lr), (pk, ctx)]) ≤
      strongSequentialPotential
        (attachLeftFrames (.node .empty k r) [(lk, lr), (pk, ctx)]) := by
  subst q
  have hk_ne_lk : k ≠ lk := by omega
  have hk_lt_pk : k < pk := by omega
  have hk_ne_pk : k ≠ pk := by omega
  cases r <;> cases lr <;> cases ctx <;>
    simp [attachLeftFrames, rightChainFrames, splay.cost.eq_def,
      hk_ne_pk, hk_lt_pk, hk_lk, strongSequentialPotential,
      leftEdges, rightEdges] <;>
    ring_nf <;>
    nlinarith

private theorem forced_min_step_left_empty_strong
    {r ctx : BinaryTree} {k pk q : Nat}
    (hbst : IsBST (.node .empty k r))
    (hmem : q ∈ (BinaryTree.node .empty k r).toKeyList)
    (hmin : ∀ x : Nat, x ∈ (BinaryTree.node .empty k r).toKeyList → q ≤ x) :
    splay.cost (.node .empty k r) q + 2 +
        strongSequentialPotential
          (.node (rightSubtree (splay (.node .empty k r) q)) pk ctx) ≤
      strongSequentialPotential (.node (.node .empty k r) pk ctx) := by
  have hq : q = k := min_eq_root_of_left_empty hbst hmem hmin
  subst q
  cases r with
  | empty =>
      cases ctx with
      | empty =>
          simp [splay.cost.eq_def, splay.eq_def, rightSubtree,
            strongSequentialPotential, leftEdges, rightEdges]
          norm_num
      | node cl ck cr =>
          simp [splay.cost.eq_def, splay.eq_def, rightSubtree,
            strongSequentialPotential, leftEdges, rightEdges]
          ring_nf
          nlinarith [show 0 ≤ (leftEdges (BinaryTree.node cl ck cr) : ℝ) by positivity,
            show 0 ≤ (rightEdges (BinaryTree.node cl ck cr) : ℝ) by positivity]
  | node rl rk rr =>
      cases ctx with
      | empty =>
          simp [splay.cost.eq_def, splay.eq_def, rightSubtree,
            strongSequentialPotential, leftEdges, rightEdges]
          ring_nf
          nlinarith [show 0 ≤ (leftEdges (BinaryTree.node rl rk rr) : ℝ) by positivity,
            show 0 ≤ (rightEdges (BinaryTree.node rl rk rr) : ℝ) by positivity]
      | node cl ck cr =>
          simp [splay.cost.eq_def, splay.eq_def, rightSubtree,
            strongSequentialPotential, leftEdges, rightEdges]
          ring_nf
          nlinarith [show 0 ≤ (leftEdges (BinaryTree.node rl rk rr) : ℝ) by positivity,
            show 0 ≤ (rightEdges (BinaryTree.node rl rk rr) : ℝ) by positivity,
            show 0 ≤ (leftEdges (BinaryTree.node cl ck cr) : ℝ) by positivity,
            show 0 ≤ (rightEdges (BinaryTree.node cl ck cr) : ℝ) by positivity]

private theorem forced_min_step_left_left_empty_strong
    {lr r ctx : BinaryTree} {lk k pk q : Nat}
    (hbst : IsBST (.node (.node .empty lk lr) k r))
    (hmem : q ∈ (BinaryTree.node (.node .empty lk lr) k r).toKeyList)
    (hmin : ∀ x : Nat,
      x ∈ (BinaryTree.node (.node .empty lk lr) k r).toKeyList → q ≤ x) :
    splay.cost (.node (.node .empty lk lr) k r) q + 2 +
        strongSequentialPotential
          (.node
            (rightSubtree (splay (.node (.node .empty lk lr) k r) q))
            pk ctx) ≤
      strongSequentialPotential (.node (.node (.node .empty lk lr) k r) pk ctx) := by
  have hq : q = lk := min_eq_left_root_of_left_left_empty hbst hmem hmin
  subst q
  have hlk_lt_k : lk < k := by
    cases hbst with
    | node _ _ _ hleft _hright _hlbst _hrbst =>
        exact (forallTree_iff_forall_mem.mp hleft) lk
          (by simp [BinaryTree.toKeyList])
  have hneq : lk ≠ k := by omega
  cases lr with
  | empty =>
      cases r with
      | empty =>
          cases ctx with
          | empty =>
              simp [splay.cost.eq_def, splay.eq_def, hneq, hlk_lt_k, rotate,
                rotateRight, rightSubtree, strongSequentialPotential,
                leftEdges, rightEdges]
              norm_num
          | node cl ck cr =>
              simp [splay.cost.eq_def, splay.eq_def, hneq, hlk_lt_k, rotate,
                rotateRight, rightSubtree, strongSequentialPotential,
                leftEdges, rightEdges]
              ring_nf
              nlinarith [show 0 ≤ (leftEdges (BinaryTree.node cl ck cr) : ℝ) by positivity,
                show 0 ≤ (rightEdges (BinaryTree.node cl ck cr) : ℝ) by positivity]
      | node rl rk rr =>
          cases ctx with
          | empty =>
              simp [splay.cost.eq_def, splay.eq_def, hneq, hlk_lt_k, rotate,
                rotateRight, rightSubtree, strongSequentialPotential,
                leftEdges, rightEdges]
              ring_nf
              nlinarith [show 0 ≤ (leftEdges (BinaryTree.node rl rk rr) : ℝ) by positivity,
                show 0 ≤ (rightEdges (BinaryTree.node rl rk rr) : ℝ) by positivity]
          | node cl ck cr =>
              simp [splay.cost.eq_def, splay.eq_def, hneq, hlk_lt_k, rotate,
                rotateRight, rightSubtree, strongSequentialPotential,
                leftEdges, rightEdges]
              ring_nf
              nlinarith [show 0 ≤ (leftEdges (BinaryTree.node rl rk rr) : ℝ) by positivity,
                show 0 ≤ (rightEdges (BinaryTree.node rl rk rr) : ℝ) by positivity,
                show 0 ≤ (leftEdges (BinaryTree.node cl ck cr) : ℝ) by positivity,
                show 0 ≤ (rightEdges (BinaryTree.node cl ck cr) : ℝ) by positivity]
  | node lrl lrk lrr =>
      cases r with
      | empty =>
          cases ctx with
          | empty =>
              simp [splay.cost.eq_def, splay.eq_def, hneq, hlk_lt_k, rotate,
                rotateRight, rightSubtree, strongSequentialPotential,
                leftEdges, rightEdges]
              ring_nf
              nlinarith [show 0 ≤ (leftEdges (BinaryTree.node lrl lrk lrr) : ℝ) by positivity,
                show 0 ≤ (rightEdges (BinaryTree.node lrl lrk lrr) : ℝ) by positivity]
          | node cl ck cr =>
              simp [splay.cost.eq_def, splay.eq_def, hneq, hlk_lt_k, rotate,
                rotateRight, rightSubtree, strongSequentialPotential,
                leftEdges, rightEdges]
              ring_nf
              nlinarith [show 0 ≤ (leftEdges (BinaryTree.node lrl lrk lrr) : ℝ) by positivity,
                show 0 ≤ (rightEdges (BinaryTree.node lrl lrk lrr) : ℝ) by positivity,
                show 0 ≤ (leftEdges (BinaryTree.node cl ck cr) : ℝ) by positivity,
                show 0 ≤ (rightEdges (BinaryTree.node cl ck cr) : ℝ) by positivity]
      | node rl rk rr =>
          cases ctx with
          | empty =>
              simp [splay.cost.eq_def, splay.eq_def, hneq, hlk_lt_k, rotate,
                rotateRight, rightSubtree, strongSequentialPotential,
                leftEdges, rightEdges]
              ring_nf
              nlinarith [show 0 ≤ (leftEdges (BinaryTree.node lrl lrk lrr) : ℝ) by positivity,
                show 0 ≤ (rightEdges (BinaryTree.node lrl lrk lrr) : ℝ) by positivity,
                show 0 ≤ (leftEdges (BinaryTree.node rl rk rr) : ℝ) by positivity,
                show 0 ≤ (rightEdges (BinaryTree.node rl rk rr) : ℝ) by positivity]
          | node cl ck cr =>
              simp [splay.cost.eq_def, splay.eq_def, hneq, hlk_lt_k, rotate,
                rotateRight, rightSubtree, strongSequentialPotential,
                leftEdges, rightEdges]
              ring_nf
              nlinarith [show 0 ≤ (leftEdges (BinaryTree.node lrl lrk lrr) : ℝ) by positivity,
                show 0 ≤ (rightEdges (BinaryTree.node lrl lrk lrr) : ℝ) by positivity,
                show 0 ≤ (leftEdges (BinaryTree.node rl rk rr) : ℝ) by positivity,
                show 0 ≤ (rightEdges (BinaryTree.node rl rk rr) : ℝ) by positivity,
                show 0 ≤ (leftEdges (BinaryTree.node cl ck cr) : ℝ) by positivity,
                show 0 ≤ (rightEdges (BinaryTree.node cl ck cr) : ℝ) by positivity]

private theorem sequentialDeletePotential_rightSubtree_le_five_num_nodes
    (t : BinaryTree) :
    sequentialDeletePotential (rightSubtree t) ≤
      5 * ((rightSubtree t).num_nodes : ℝ) := by
  exact sequentialDeletePotential_le_five_num_nodes (rightSubtree t)

private theorem sequentialDeletePotential_rightSubtree_splay_min_le
    (t : BinaryTree) (q : Nat) (hbst : IsBST t)
    (hmem : q ∈ t.toKeyList)
    (hmin : ∀ k : Nat, k ∈ t.toKeyList → q ≤ k) :
    sequentialDeletePotential (rightSubtree (splay t q)) ≤
      5 * ((t.num_nodes - 1 : Nat) : ℝ) := by
  have hnum :=
    splay_min_rightSubtree_num_nodes_add_one t q hbst hmem hmin
  have hpot :=
    sequentialDeletePotential_le_five_num_nodes
      (rightSubtree (splay t q))
  have hnum' : (rightSubtree (splay t q)).num_nodes = t.num_nodes - 1 := by
    omega
  rw [hnum'] at hpot
  exact hpot

private theorem splay_cost_nonneg : ∀ (t : BinaryTree) (q : Nat),
    0 ≤ splay.cost t q
| .empty, q => by
    simp [splay.cost.eq_def]
| .node l k r, q => by
    rw [splay.cost.eq_def]
    by_cases hqk : q = k
    · simp [hqk]
    · by_cases hq_lt_k : q < k
      · cases l with
        | empty =>
            simp [hqk, hq_lt_k]
        | node ll lk lr =>
            by_cases hq_lt_lk : q < lk
            · cases ll with
              | empty =>
                  simp [hqk, hq_lt_k, hq_lt_lk]
              | node a x b =>
                  have hll := splay_cost_nonneg (BinaryTree.node a x b) q
                  simp [hqk, hq_lt_k, hq_lt_lk]
                  linarith
            · by_cases hlk_lt_q : lk < q
              · cases lr with
                | empty =>
                    simp [hqk, hq_lt_k, hq_lt_lk, hlk_lt_q]
                | node a x b =>
                    have hlr := splay_cost_nonneg (BinaryTree.node a x b) q
                    simp [hqk, hq_lt_k, hq_lt_lk, hlk_lt_q]
                    linarith
              · simp [hqk, hq_lt_k, hq_lt_lk, hlk_lt_q]
      · cases r with
        | empty =>
            simp [hqk, hq_lt_k]
        | node rl rk rr =>
            by_cases hq_lt_rk : q < rk
            · cases rl with
              | empty =>
                  simp [hqk, hq_lt_k, hq_lt_rk]
              | node a x b =>
                  have hrl := splay_cost_nonneg (BinaryTree.node a x b) q
                  simp [hqk, hq_lt_k, hq_lt_rk]
                  linarith
            · by_cases hrk_lt_q : rk < q
              · cases rr with
                | empty =>
                    simp [hqk, hq_lt_k, hq_lt_rk, hrk_lt_q]
                | node a x b =>
                    have hrr := splay_cost_nonneg (BinaryTree.node a x b) q
                    simp [hqk, hq_lt_k, hq_lt_rk, hrk_lt_q]
                    linarith
              · simp [hqk, hq_lt_k, hq_lt_rk, hrk_lt_q]

private theorem cast_pred_add_two_of_pos (m : Nat) (hm : 0 < m) :
    (((m - 1 : Nat) : ℝ) + 2) = 1 + (m : ℝ) := by
  have hnat : (m - 1) + 2 = 1 + m := by omega
  exact_mod_cast hnat

private theorem node_search_path_len_pos (l : BinaryTree) (k : Nat)
    (r : BinaryTree) (q : Nat) :
    0 < (BinaryTree.node l k r).search_path_len q := by
  simp only [BinaryTree.search_path_len]
  by_cases hqk : q < k
  · simp [hqk]
  · by_cases hkq : k < q
    · simp [hqk, hkq]
    · simp [hqk, hkq]

private theorem splay_cost_eq_search_path_len_sub_one :
    ∀ (t : BinaryTree) (q : Nat),
      splay.cost t q = ((t.search_path_len q - 1 : Nat) : ℝ)
| .empty, q => by
    simp [splay.cost.eq_def, BinaryTree.search_path_len]
| .node l k r, q => by
    rw [splay.cost.eq_def]
    simp only [BinaryTree.search_path_len]
    by_cases hqk : q = k
    · simp [hqk]
    · by_cases hq_lt_k : q < k
      · cases l with
        | empty =>
            simp [hqk, hq_lt_k]
        | node ll lk lr =>
            by_cases hq_lt_lk : q < lk
            · cases ll with
              | empty =>
                  simp [hqk, hq_lt_k, hq_lt_lk,
                    BinaryTree.search_path_len]
              | node a x b =>
                  have hll := splay_cost_eq_search_path_len_sub_one
                    (BinaryTree.node a x b) q
                  simp [hqk, hq_lt_k, hq_lt_lk,
                    BinaryTree.search_path_len, hll]
                  simpa [BinaryTree.search_path_len] using
                    cast_pred_add_two_of_pos
                      ((BinaryTree.node a x b).search_path_len q)
                      (node_search_path_len_pos a x b q)
            · by_cases hlk_lt_q : lk < q
              · cases lr with
                | empty =>
                    simp [hqk, hq_lt_k, hq_lt_lk, hlk_lt_q,
                      BinaryTree.search_path_len]
                | node a x b =>
                    have hlr := splay_cost_eq_search_path_len_sub_one
                      (BinaryTree.node a x b) q
                    simp [hqk, hq_lt_k, hq_lt_lk, hlk_lt_q,
                      BinaryTree.search_path_len, hlr]
                    simpa [BinaryTree.search_path_len] using
                      cast_pred_add_two_of_pos
                        ((BinaryTree.node a x b).search_path_len q)
                        (node_search_path_len_pos a x b q)
              · simp [hqk, hq_lt_k, hq_lt_lk, hlk_lt_q,
                  BinaryTree.search_path_len]
      · cases r with
        | empty =>
            have hk_lt_q : k < q := by
              exact lt_of_le_of_ne (Nat.le_of_not_lt hq_lt_k)
                (by intro h; exact hqk h.symm)
            simp [hqk, hq_lt_k, hk_lt_q]
        | node rl rk rr =>
            have hk_lt_q : k < q := by
              exact lt_of_le_of_ne (Nat.le_of_not_lt hq_lt_k)
                (by intro h; exact hqk h.symm)
            by_cases hq_lt_rk : q < rk
            · cases rl with
              | empty =>
                  simp [hqk, hq_lt_k, hk_lt_q, hq_lt_rk,
                    BinaryTree.search_path_len]
              | node a x b =>
                  have hrl := splay_cost_eq_search_path_len_sub_one
                    (BinaryTree.node a x b) q
                  simp [hqk, hq_lt_k, hk_lt_q, hq_lt_rk,
                    BinaryTree.search_path_len, hrl]
                  simpa [BinaryTree.search_path_len] using
                    cast_pred_add_two_of_pos
                      ((BinaryTree.node a x b).search_path_len q)
                      (node_search_path_len_pos a x b q)
            · by_cases hrk_lt_q : rk < q
              · cases rr with
                | empty =>
                    simp [hqk, hq_lt_k, hk_lt_q, hq_lt_rk, hrk_lt_q,
                      BinaryTree.search_path_len]
                | node a x b =>
                    have hrr := splay_cost_eq_search_path_len_sub_one
                      (BinaryTree.node a x b) q
                    simp [hqk, hq_lt_k, hk_lt_q, hq_lt_rk, hrk_lt_q,
                      BinaryTree.search_path_len, hrr]
                    simpa [BinaryTree.search_path_len] using
                      cast_pred_add_two_of_pos
                        ((BinaryTree.node a x b).search_path_len q)
                        (node_search_path_len_pos a x b q)
              · simp [hqk, hq_lt_k, hk_lt_q, hq_lt_rk, hrk_lt_q,
                  BinaryTree.search_path_len]

private theorem splay_cost_le_search_path_len (t : BinaryTree) (q : Nat) :
    splay.cost t q ≤ t.search_path_len q := by
  rw [splay_cost_eq_search_path_len_sub_one]
  exact_mod_cast Nat.sub_le (t.search_path_len q) 1

private theorem splay_cost_attachLeftFrames_left_empty_eq_length
    (r : BinaryTree) (k : Nat) (fs : List LeftContextFrame)
    (hframes : frameKeysAbove k fs) :
    splay.cost (attachLeftFrames (.node .empty k r) fs) k =
      (fs.length : ℝ) := by
  rw [splay_cost_eq_search_path_len_sub_one]
  have hpath :=
    search_path_len_attachLeftFrames_of_frameKeysAbove
      (.node .empty k r) k fs hframes
  rw [hpath]
  simp [BinaryTree.search_path_len]

private theorem splayMinContext_left_empty_amortized
    (r : BinaryTree) (k : Nat) (fs : List LeftContextFrame)
    (hframes : frameKeysAbove k fs) :
    splay.cost (attachLeftFrames (.node .empty k r) fs) k +
        strongSequentialPotential (splayMinContextResult r fs) ≤
      strongSequentialPotential (attachLeftFrames (.node .empty k r) fs) +
        (fs.length : ℝ) := by
  have hcost :=
    splay_cost_attachLeftFrames_left_empty_eq_length r k fs hframes
  have hpot :=
    splayMinContextResult_left_empty_potential_le r k fs
  have hcredit_nonneg := twoFrameCredit_nonneg fs
  nlinarith

private theorem splayMinContext_left_empty_amortized_with_credit
    (r : BinaryTree) (k : Nat) (fs : List LeftContextFrame)
    (hframes : frameKeysAbove k fs) :
    splay.cost (attachLeftFrames (.node .empty k r) fs) k +
        strongSequentialPotential (splayMinContextResult r fs) +
        twoFrameCredit fs ≤
      strongSequentialPotential (attachLeftFrames (.node .empty k r) fs) +
        (fs.length : ℝ) := by
  have hcost :=
    splay_cost_attachLeftFrames_left_empty_eq_length r k fs hframes
  have hpot :=
    splayMinContextResult_left_empty_potential_le r k fs
  nlinarith

private theorem splayMinContext_left_left_empty_amortized
    (lr r : BinaryTree) (lk k : Nat) (fs : List LeftContextFrame)
    (hlk : lk < k) (hframes : frameKeysAbove lk fs) :
    splay.cost (attachLeftFrames (.node (.node .empty lk lr) k r) fs) lk +
        strongSequentialPotential
          (splayMinContextResult lr ((k, r) :: fs)) ≤
      strongSequentialPotential
        (attachLeftFrames (.node (.node .empty lk lr) k r) fs) +
        (fs.length : ℝ) := by
  cases fs with
  | nil =>
      have hneq : lk ≠ k := by omega
      cases lr <;> cases r <;>
        simp [attachLeftFrames, splay.cost.eq_def, hneq, hlk,
          splayMinContextResult, splayMinFramesRev,
          strongSequentialPotential, leftEdges, rightEdges] <;>
        ring_nf <;>
        nlinarith
  | cons fr fs =>
      have hframes_cons :
          frameKeysAbove lk ((k, r) :: fr :: fs) := by
        exact ⟨hlk, hframes⟩
      have hcost0 :=
        splay_cost_attachLeftFrames_left_empty_eq_length
          lr lk ((k, r) :: fr :: fs) hframes_cons
      have hcost :
          splay.cost
              (attachLeftFrames (.node (.node .empty lk lr) k r)
                (fr :: fs)) lk =
            (((k, r) :: fr :: fs).length : ℝ) := by
        simpa [attachLeftFrames] using hcost0
      have hpot :=
        splayMinContextResult_left_empty_potential_le
          lr lk ((k, r) :: fr :: fs)
      have hcredit :
          twoFrameCredit ((k, r) :: fr :: fs) = 2 := by
        simp [twoFrameCredit]
      rw [hcredit] at hpot
      simp [attachLeftFrames] at hpot
      rw [hcost]
      simp [attachLeftFrames]
      nlinarith

private theorem splayMinContext_left_empty_amortized_of_min
    {r : BinaryTree} {k q : Nat} {fs : List LeftContextFrame}
    (hbst : IsBST (attachLeftFrames (.node .empty k r) fs))
    (hmem : q ∈ (BinaryTree.node .empty k r).toKeyList)
    (hmin : ∀ x : Nat,
      x ∈ (attachLeftFrames (.node .empty k r) fs).toKeyList → q ≤ x) :
    splay.cost (attachLeftFrames (.node .empty k r) fs) q +
        strongSequentialPotential (splayMinContextResult r fs) ≤
      strongSequentialPotential (attachLeftFrames (.node .empty k r) fs) +
        (fs.length : ℝ) := by
  have hbst_base :
      IsBST (.node .empty k r) :=
    isBST_of_isBST_attachLeftFrames (.node .empty k r) fs hbst
  have hmin_base :
      ∀ x : Nat, x ∈ (BinaryTree.node .empty k r).toKeyList → q ≤ x := by
    intro x hx
    exact hmin x (mem_toKeyList_attachLeftFrames_of_mem
      (.node .empty k r) fs hx)
  have hq : q = k :=
    min_eq_root_of_left_empty hbst_base hmem hmin_base
  subst q
  have hframes :
      frameKeysAbove k fs :=
    frameKeysAbove_of_isBST_attachLeftFrames_mem
      (.node .empty k r) fs k hbst
      (by simp [BinaryTree.toKeyList])
  exact splayMinContext_left_empty_amortized r k fs hframes

private theorem splayMinContext_left_empty_amortized_with_credit_of_min
    {r : BinaryTree} {k q : Nat} {fs : List LeftContextFrame}
    (hbst : IsBST (attachLeftFrames (.node .empty k r) fs))
    (hmem : q ∈ (BinaryTree.node .empty k r).toKeyList)
    (hmin : ∀ x : Nat,
      x ∈ (attachLeftFrames (.node .empty k r) fs).toKeyList → q ≤ x) :
    splay.cost (attachLeftFrames (.node .empty k r) fs) q +
        strongSequentialPotential (splayMinContextResult r fs) +
        twoFrameCredit fs ≤
      strongSequentialPotential (attachLeftFrames (.node .empty k r) fs) +
        (fs.length : ℝ) := by
  have hbst_base :
      IsBST (.node .empty k r) :=
    isBST_of_isBST_attachLeftFrames (.node .empty k r) fs hbst
  have hmin_base :
      ∀ x : Nat, x ∈ (BinaryTree.node .empty k r).toKeyList → q ≤ x := by
    intro x hx
    exact hmin x (mem_toKeyList_attachLeftFrames_of_mem
      (.node .empty k r) fs hx)
  have hq : q = k :=
    min_eq_root_of_left_empty hbst_base hmem hmin_base
  subst q
  have hframes :
      frameKeysAbove k fs :=
    frameKeysAbove_of_isBST_attachLeftFrames_mem
      (.node .empty k r) fs k hbst
      (by simp [BinaryTree.toKeyList])
  exact splayMinContext_left_empty_amortized_with_credit r k fs hframes

private theorem splayMinContext_left_left_empty_amortized_of_min
    {lr r : BinaryTree} {lk k q : Nat} {fs : List LeftContextFrame}
    (hbst : IsBST (attachLeftFrames (.node (.node .empty lk lr) k r) fs))
    (hmem : q ∈
      (BinaryTree.node (.node .empty lk lr) k r).toKeyList)
    (hmin : ∀ x : Nat,
      x ∈ (attachLeftFrames (.node (.node .empty lk lr) k r) fs).toKeyList →
        q ≤ x) :
    splay.cost (attachLeftFrames (.node (.node .empty lk lr) k r) fs) q +
        strongSequentialPotential
          (splayMinContextResult lr ((k, r) :: fs)) ≤
      strongSequentialPotential
        (attachLeftFrames (.node (.node .empty lk lr) k r) fs) +
        (fs.length : ℝ) := by
  have hbst_base :
      IsBST (.node (.node .empty lk lr) k r) :=
    isBST_of_isBST_attachLeftFrames
      (.node (.node .empty lk lr) k r) fs hbst
  have hmin_base :
      ∀ x : Nat,
        x ∈ (BinaryTree.node (.node .empty lk lr) k r).toKeyList →
          q ≤ x := by
    intro x hx
    exact hmin x (mem_toKeyList_attachLeftFrames_of_mem
      (.node (.node .empty lk lr) k r) fs hx)
  have hq : q = lk :=
    min_eq_left_root_of_left_left_empty hbst_base hmem hmin_base
  subst q
  have hlk : lk < k := by
    cases hbst_base with
    | node _ _ _ hleft _hright _hlbst _hrbst =>
        exact (forallTree_iff_forall_mem.mp hleft) lk
          (by simp [BinaryTree.toKeyList])
  have hframes :
      frameKeysAbove lk fs :=
    frameKeysAbove_of_isBST_attachLeftFrames_mem
      (.node (.node .empty lk lr) k r) fs lk hbst
      (by simp [BinaryTree.toKeyList])
  exact splayMinContext_left_left_empty_amortized lr r lk k fs hlk hframes

private theorem search_path_len_le_num_nodes :
    ∀ (t : BinaryTree) (q : Nat), t.search_path_len q ≤ t.num_nodes
| .empty, q => by
    simp [BinaryTree.search_path_len, BinaryTree.num_nodes]
| .node l k r, q => by
    simp only [BinaryTree.search_path_len, BinaryTree.num_nodes]
    by_cases hqk : q < k
    · have hl := search_path_len_le_num_nodes l q
      simp [hqk]
      omega
    · by_cases hkq : k < q
      · have hr := search_path_len_le_num_nodes r q
        simp [hqk, hkq]
        omega
      · simp [hqk, hkq]
        omega

private theorem search_path_len_le_reset_path_add_after_splay_add_num_nodes
    (t : BinaryTree) (q y : Nat) :
    t.search_path_len y ≤
      t.search_path_len q + (splay t q).search_path_len y + t.num_nodes := by
  have h := search_path_len_le_num_nodes t y
  omega

private theorem isBST_left_mem_lt_root {l r : BinaryTree} {k q : Nat}
    (hbst : IsBST (BinaryTree.node l k r))
    (hmem : q ∈ l.toKeyList) :
    q < k := by
  cases hbst with
  | node _ _ _ hleft _hright _hlbst _hrbst =>
      exact (forallTree_iff_forall_mem.mp hleft) q hmem

private theorem isBST_right_mem_gt_root {l r : BinaryTree} {k q : Nat}
    (hbst : IsBST (BinaryTree.node l k r))
    (hmem : q ∈ r.toKeyList) :
    k < q := by
  cases hbst with
  | node _ _ _ _hleft hright _hlbst _hrbst =>
      exact (forallTree_iff_forall_mem.mp hright) q hmem

private theorem mem_toKeyList_of_mem_leftSubtree
    {t : BinaryTree} {q : Nat}
    (hmem : q ∈ (leftSubtree t).toKeyList) :
    q ∈ t.toKeyList := by
  cases t with
  | empty =>
      simp [leftSubtree, BinaryTree.toKeyList] at hmem
  | node l k r =>
      simp [leftSubtree] at hmem
      simp [BinaryTree.toKeyList, hmem]

private theorem mem_toKeyList_of_mem_rightSubtree
    {t : BinaryTree} {q : Nat}
    (hmem : q ∈ (rightSubtree t).toKeyList) :
    q ∈ t.toKeyList := by
  cases t with
  | empty =>
      simp [rightSubtree, BinaryTree.toKeyList] at hmem
  | node l k r =>
      simp [rightSubtree] at hmem
      simp [BinaryTree.toKeyList, hmem]

private theorem rooted_leftSubtree_mem_lt
    {t : BinaryTree} {q x : Nat}
    (hbst : IsBST t) (hroot : rootKey t = some q)
    (hmem_left : x ∈ (leftSubtree t).toKeyList) :
    x < q := by
  cases ht : t with
  | empty =>
      simp [rootKey, ht] at hroot
  | node l k r =>
      simp [rootKey, ht] at hroot
      subst k
      have hbst_node : IsBST (BinaryTree.node l q r) := by
        simpa [ht] using hbst
      have hmem_l : x ∈ l.toKeyList := by
        simpa [ht, leftSubtree] using hmem_left
      exact isBST_left_mem_lt_root hbst_node hmem_l

private theorem rooted_rightSubtree_mem_gt
    {t : BinaryTree} {q x : Nat}
    (hbst : IsBST t) (hroot : rootKey t = some q)
    (hmem_right : x ∈ (rightSubtree t).toKeyList) :
    q < x := by
  cases ht : t with
  | empty =>
      simp [rootKey, ht] at hroot
  | node l k r =>
      simp [rootKey, ht] at hroot
      subst k
      have hbst_node : IsBST (BinaryTree.node l q r) := by
        simpa [ht] using hbst
      have hmem_r : x ∈ r.toKeyList := by
        simpa [ht, rightSubtree] using hmem_right
      exact isBST_right_mem_gt_root hbst_node hmem_r

private theorem search_path_len_node_left_of_isBST_mem
    {l r : BinaryTree} {k q : Nat}
    (hbst : IsBST (BinaryTree.node l k r))
    (hmem : q ∈ l.toKeyList) :
    (BinaryTree.node l k r).search_path_len q =
      1 + l.search_path_len q := by
  have hqk : q < k := isBST_left_mem_lt_root hbst hmem
  simp [BinaryTree.search_path_len, hqk]

private theorem search_path_len_node_right_of_isBST_mem
    {l r : BinaryTree} {k q : Nat}
    (hbst : IsBST (BinaryTree.node l k r))
    (hmem : q ∈ r.toKeyList) :
    (BinaryTree.node l k r).search_path_len q =
      1 + r.search_path_len q := by
  have hkq : k < q := isBST_right_mem_gt_root hbst hmem
  have hnot : ¬ q < k := by omega
  simp [BinaryTree.search_path_len, hnot, hkq]

private theorem search_path_len_node_of_lt {l r : BinaryTree}
    {k q : Nat} (hqk : q < k) :
    (BinaryTree.node l k r).search_path_len q =
      1 + l.search_path_len q := by
  simp [BinaryTree.search_path_len, hqk]

private theorem search_path_len_node_of_gt {l r : BinaryTree}
    {k q : Nat} (hkq : k < q) :
    (BinaryTree.node l k r).search_path_len q =
      1 + r.search_path_len q := by
  have hnot : ¬ q < k := by omega
  simp [BinaryTree.search_path_len, hnot, hkq]

private theorem search_path_len_node_of_eq {l r : BinaryTree}
    {k q : Nat} (hqk : q = k) :
    (BinaryTree.node l k r).search_path_len q = 1 := by
  subst q
  simp [BinaryTree.search_path_len]

private theorem search_path_len_le_root_path_add_after_splay
    {t : BinaryTree} {q y : Nat}
    (hroot : rootKey t = some q) :
    t.search_path_len y ≤
      t.search_path_len q + (splay t q).search_path_len y := by
  cases ht : t with
  | empty =>
      simp [rootKey, ht] at hroot
  | node l k r =>
      simp [rootKey, ht] at hroot
      subst k
      have hpath : (BinaryTree.node l q r).search_path_len q = 1 := by
        simp [BinaryTree.search_path_len]
      have hsplay : splay (BinaryTree.node l q r) q = BinaryTree.node l q r := by
        rw [splay.eq_def]
        simp
      rw [hpath, hsplay]
      omega

private theorem root_search_path_len_le_path_add_after_splay
    {t : BinaryTree} {root q : Nat}
    (hroot : rootKey t = some root)
    (hq_mem : q ∈ t.toKeyList) :
    t.search_path_len root ≤
      t.search_path_len q + (splay t q).search_path_len root := by
  have hroot_path : t.search_path_len root = 1 :=
    search_path_len_eq_one_of_rootKey_eq_some hroot
  have hq_pos : 0 < t.search_path_len q := by
    cases ht : t with
    | empty =>
        simp [rootKey, ht] at hroot
    | node l k r =>
        simpa [ht] using node_search_path_len_pos l k r q
  rw [hroot_path]
  omega

private theorem search_path_len_node_left_le_num_nodes {l r : BinaryTree}
    {k q : Nat} (hqk : q < k) :
    (BinaryTree.node l k r).search_path_len q ≤ 1 + l.num_nodes := by
  rw [search_path_len_node_of_lt hqk]
  exact Nat.add_le_add_left (search_path_len_le_num_nodes l q) 1

private theorem search_path_len_node_right_le_num_nodes {l r : BinaryTree}
    {k q : Nat} (hkq : k < q) :
    (BinaryTree.node l k r).search_path_len q ≤ 1 + r.num_nodes := by
  rw [search_path_len_node_of_gt hkq]
  exact Nat.add_le_add_left (search_path_len_le_num_nodes r q) 1

private theorem search_path_len_pos_of_mem :
    ∀ (t : BinaryTree) (q : Nat), q ∈ t.toKeyList →
      0 < t.search_path_len q
| .empty, q, hmem => by
    simp [BinaryTree.toKeyList] at hmem
| .node l k r, q, hmem => by
    simp [BinaryTree.toKeyList] at hmem
    simp only [BinaryTree.search_path_len]
    rcases hmem with hmem | hqk | hmem
    · have hlpos := search_path_len_pos_of_mem l q hmem
      by_cases hq_lt_k : q < k
      · simp [hq_lt_k]
      · by_cases hk_lt_q : k < q
        · simp [hq_lt_k, hk_lt_q]
        · simp [hq_lt_k, hk_lt_q]
    · subst q
      simp
    · have hrpos := search_path_len_pos_of_mem r q hmem
      by_cases hq_lt_k : q < k
      · simp [hq_lt_k]
      · by_cases hk_lt_q : k < q
        · simp [hq_lt_k, hk_lt_q]
        · simp [hq_lt_k, hk_lt_q]

private theorem search_path_len_pivot_after_splay_left_le
    {l r : BinaryTree} {q x : Nat}
    (hbst : IsBST (.node l q r))
    (hmem : x ∈ l.toKeyList) :
    (splay (.node l q r) x).search_path_len q ≤
      (BinaryTree.node l q r).search_path_len x := by
  have hx_lt_q : x < q := isBST_left_mem_lt_root hbst hmem
  cases l with
  | empty =>
      simp [BinaryTree.toKeyList] at hmem
  | node ll lk lr =>
      cases hbst with
      | node _ _ _ hleft _hright hbst_left _hrbst =>
          cases hbst_left with
          | node _ _ _ hll_left hlr_right hbst_ll hbst_lr =>
              have hlk_lt_q : lk < q :=
                (forallTree_iff_forall_mem.mp hleft) lk
                  (by simp [BinaryTree.toKeyList])
              simp [BinaryTree.toKeyList] at hmem
              rw [splay.eq_def]
              rcases hmem with hmem_ll | hx_eq_lk | hmem_lr
              · have hx_lt_lk : x < lk :=
                  (forallTree_iff_forall_mem.mp hll_left) x hmem_ll
                have hpos : 0 < (BinaryTree.node ll lk lr).search_path_len x :=
                  search_path_len_pos_of_mem (.node ll lk lr) x
                    (by simp [BinaryTree.toKeyList, hmem_ll])
                cases ll with
                | empty =>
                    simp [BinaryTree.toKeyList] at hmem_ll
                | node a y b =>
                    have hroot_inner :=
                      splay_rootKey_eq_some_of_mem_isBST
                        (.node a y b) x hbst_ll hmem_ll
                    have hinner_pos :
                        0 < (BinaryTree.node a y b).search_path_len x :=
                      search_path_len_pos_of_mem (.node a y b) x hmem_ll
                    have hpath_eq :
                        (BinaryTree.node (.node a y b) lk lr).search_path_len x =
                          1 + (BinaryTree.node a y b).search_path_len x := by
                      simp [BinaryTree.search_path_len, hx_lt_lk]
                    cases hs : splay (.node a y b) x with
                    | empty =>
                        simp [rootKey, hs] at hroot_inner
                    | node sl sk sr =>
                        simp [rootKey, hs] at hroot_inner
                        subst sk
                        have hx_ne_q : x ≠ q := by omega
                        have hq_not_lt_x : ¬ q < x := by omega
                        have hq_not_lt_lk : ¬ q < lk := by omega
                        have houter_path_eq :
                            (BinaryTree.node (BinaryTree.node (.node a y b) lk lr) q r).search_path_len x =
                              1 + (BinaryTree.node (.node a y b) lk lr).search_path_len x := by
                          simp [BinaryTree.search_path_len, hx_lt_q]
                        have hinner_ge_one :
                            1 ≤ (BinaryTree.node a y b).search_path_len x :=
                          Nat.succ_le_iff.mpr hinner_pos
                        simp [BinaryTree.search_path_len] at hinner_ge_one
                        rw [houter_path_eq, hpath_eq]
                        simp [hx_lt_q, hx_lt_lk, hs, rotate, rotateRight,
                          BinaryTree.search_path_len, hx_ne_q, hq_not_lt_x,
                          hlk_lt_q, hq_not_lt_lk]
                        omega
              · subst x
                have hlk_ne_q : lk ≠ q := by omega
                have hq_not_lt_lk : ¬ q < lk := by omega
                simp [hx_lt_q, rotate, rotateRight, hlk_ne_q,
                  hq_not_lt_lk, BinaryTree.search_path_len]
              · have hlk_lt_x : lk < x :=
                  (forallTree_iff_forall_mem.mp hlr_right) x hmem_lr
                have hnot : ¬ x < lk := by omega
                have hpos : 0 < (BinaryTree.node ll lk lr).search_path_len x :=
                  search_path_len_pos_of_mem (.node ll lk lr) x
                    (by simp [BinaryTree.toKeyList, hmem_lr])
                cases lr with
                | empty =>
                    simp [BinaryTree.toKeyList] at hmem_lr
                | node a y b =>
                    have hroot_inner :=
                      splay_rootKey_eq_some_of_mem_isBST
                        (.node a y b) x hbst_lr hmem_lr
                    have hinner_pos :
                        0 < (BinaryTree.node a y b).search_path_len x :=
                      search_path_len_pos_of_mem (.node a y b) x hmem_lr
                    have hpath_eq :
                        (BinaryTree.node ll lk (.node a y b)).search_path_len x =
                          1 + (BinaryTree.node a y b).search_path_len x := by
                      simp [BinaryTree.search_path_len, hnot, hlk_lt_x]
                    cases hs : splay (.node a y b) x with
                    | empty =>
                        simp [rootKey, hs] at hroot_inner
                    | node sl sk sr =>
                        simp [rootKey, hs] at hroot_inner
                        subst sk
                        have hx_ne_q : x ≠ q := by omega
                        have hq_not_lt_x : ¬ q < x := by omega
                        have hq_not_lt_lk : ¬ q < lk := by omega
                        have houter_path_eq :
                            (BinaryTree.node (BinaryTree.node ll lk (.node a y b)) q r).search_path_len x =
                              1 + (BinaryTree.node ll lk (.node a y b)).search_path_len x := by
                          simp [BinaryTree.search_path_len, hx_lt_q]
                        have hinner_ge_one :
                            1 ≤ (BinaryTree.node a y b).search_path_len x :=
                          Nat.succ_le_iff.mpr hinner_pos
                        simp [BinaryTree.search_path_len] at hinner_ge_one
                        rw [houter_path_eq, hpath_eq]
                        simp [hx_lt_q, hnot, hlk_lt_x, hs, rotate,
                          rotateLeft, rotateRight, BinaryTree.search_path_len,
                          hx_ne_q, hq_not_lt_x]
                        omega

private theorem search_path_len_pivot_after_splay_right_le
    {l r : BinaryTree} {q x : Nat}
    (hbst : IsBST (.node l q r))
    (hmem : x ∈ r.toKeyList) :
    (splay (.node l q r) x).search_path_len q ≤
      (BinaryTree.node l q r).search_path_len x := by
  have hq_lt_x : q < x := isBST_right_mem_gt_root hbst hmem
  cases r with
  | empty =>
      simp [BinaryTree.toKeyList] at hmem
  | node rl rk rr =>
      cases hbst with
      | node _ _ _ _hleft hright _hlbst hbst_right =>
          cases hbst_right with
          | node _ _ _ hrl_left hrr_right hbst_rl hbst_rr =>
              have hq_lt_rk : q < rk :=
                (forallTree_iff_forall_mem.mp hright) rk
                  (by simp [BinaryTree.toKeyList])
              simp [BinaryTree.toKeyList] at hmem
              rw [splay.eq_def]
              rcases hmem with hmem_rl | hx_eq_rk | hmem_rr
              · have hx_lt_rk : x < rk :=
                  (forallTree_iff_forall_mem.mp hrl_left) x hmem_rl
                have hnot : ¬ rk < x := by omega
                have hpos : 0 < (BinaryTree.node rl rk rr).search_path_len x :=
                  search_path_len_pos_of_mem (.node rl rk rr) x
                    (by simp [BinaryTree.toKeyList, hmem_rl])
                cases rl with
                | empty =>
                    simp [BinaryTree.toKeyList] at hmem_rl
                | node a y b =>
                    have hroot_inner :=
                      splay_rootKey_eq_some_of_mem_isBST
                        (.node a y b) x hbst_rl hmem_rl
                    have hinner_pos :
                        0 < (BinaryTree.node a y b).search_path_len x :=
                      search_path_len_pos_of_mem (.node a y b) x hmem_rl
                    have hpath_eq :
                        (BinaryTree.node (.node a y b) rk rr).search_path_len x =
                          1 + (BinaryTree.node a y b).search_path_len x := by
                      simp [BinaryTree.search_path_len, hx_lt_rk]
                    cases hs : splay (.node a y b) x with
                    | empty =>
                        simp [rootKey, hs] at hroot_inner
                    | node sl sk sr =>
                        simp [rootKey, hs] at hroot_inner
                        subst sk
                        have hx_ne_q : x ≠ q := by omega
                        have hnot_x_lt_q : ¬ x < q := by omega
                        have houter_path_eq :
                            (BinaryTree.node l q (BinaryTree.node (.node a y b) rk rr)).search_path_len x =
                              1 + (BinaryTree.node (.node a y b) rk rr).search_path_len x := by
                          simp [BinaryTree.search_path_len, hnot_x_lt_q, hq_lt_x]
                        have hinner_ge_one :
                            1 ≤ (BinaryTree.node a y b).search_path_len x :=
                          Nat.succ_le_iff.mpr hinner_pos
                        simp [BinaryTree.search_path_len] at hinner_ge_one
                        rw [houter_path_eq, hpath_eq]
                        simp [hq_lt_x, hx_lt_rk, hs, rotate,
                          rotateLeft, rotateRight, BinaryTree.search_path_len,
                          hx_ne_q, hnot_x_lt_q]
                        omega
              · subst x
                have hrk_ne_q : rk ≠ q := by omega
                have hnot_rk_lt_q : ¬ rk < q := by omega
                simp [hq_lt_x, rotate, rotateLeft, hrk_ne_q,
                  hnot_rk_lt_q, BinaryTree.search_path_len]
              · have hrk_lt_x : rk < x :=
                  (forallTree_iff_forall_mem.mp hrr_right) x hmem_rr
                have hnot : ¬ x < rk := by omega
                have hpos : 0 < (BinaryTree.node rl rk rr).search_path_len x :=
                  search_path_len_pos_of_mem (.node rl rk rr) x
                    (by simp [BinaryTree.toKeyList, hmem_rr])
                cases rr with
                | empty =>
                    simp [BinaryTree.toKeyList] at hmem_rr
                | node a y b =>
                    have hroot_inner :=
                      splay_rootKey_eq_some_of_mem_isBST
                        (.node a y b) x hbst_rr hmem_rr
                    have hinner_pos :
                        0 < (BinaryTree.node a y b).search_path_len x :=
                      search_path_len_pos_of_mem (.node a y b) x hmem_rr
                    have hpath_eq :
                        (BinaryTree.node rl rk (.node a y b)).search_path_len x =
                          1 + (BinaryTree.node a y b).search_path_len x := by
                      simp [BinaryTree.search_path_len, hnot, hrk_lt_x]
                    cases hs : splay (.node a y b) x with
                    | empty =>
                        simp [rootKey, hs] at hroot_inner
                    | node sl sk sr =>
                        simp [rootKey, hs] at hroot_inner
                        subst sk
                        have hx_ne_q : x ≠ q := by omega
                        have hnot_x_lt_q : ¬ x < q := by omega
                        have houter_path_eq :
                            (BinaryTree.node l q (BinaryTree.node rl rk (.node a y b))).search_path_len x =
                              1 + (BinaryTree.node rl rk (.node a y b)).search_path_len x := by
                          simp [BinaryTree.search_path_len, hnot_x_lt_q, hq_lt_x]
                        have hinner_ge_one :
                            1 ≤ (BinaryTree.node a y b).search_path_len x :=
                          Nat.succ_le_iff.mpr hinner_pos
                        simp [BinaryTree.search_path_len] at hinner_ge_one
                        rw [houter_path_eq, hpath_eq]
                        simp [hq_lt_x, hnot, hrk_lt_x, hs, rotate,
                          rotateLeft, BinaryTree.search_path_len,
                          hx_ne_q, hnot_x_lt_q, hq_lt_rk]
                        omega

private theorem rooted_pivot_reset_search_path_le
    {t : BinaryTree} {q x : Nat}
    (hbst : IsBST t) (hroot : rootKey t = some q)
    (hmem_left : x ∈ (leftSubtree t).toKeyList) :
    (splay t x).search_path_len q ≤ t.search_path_len x := by
  cases ht : t with
  | empty =>
      simp [rootKey, ht] at hroot
  | node l k r =>
      simp [rootKey, ht] at hroot
      subst k
      have hbst_node : IsBST (BinaryTree.node l q r) := by
        simpa [ht] using hbst
      have hmem_l : x ∈ l.toKeyList := by
        simpa [ht, leftSubtree] using hmem_left
      simpa [ht] using
        search_path_len_pivot_after_splay_left_le
          (l := l) (r := r) (q := q) (x := x)
          hbst_node hmem_l

private theorem rooted_pivot_reset_search_path_right_le
    {t : BinaryTree} {q x : Nat}
    (hbst : IsBST t) (hroot : rootKey t = some q)
    (hmem_right : x ∈ (rightSubtree t).toKeyList) :
    (splay t x).search_path_len q ≤ t.search_path_len x := by
  cases ht : t with
  | empty =>
      simp [rootKey, ht] at hroot
  | node l k r =>
      simp [rootKey, ht] at hroot
      subst k
      have hbst_node : IsBST (BinaryTree.node l q r) := by
        simpa [ht] using hbst
      have hmem_r : x ∈ r.toKeyList := by
        simpa [ht, rightSubtree] using hmem_right
      simpa [ht] using
        search_path_len_pivot_after_splay_right_le
          (l := l) (r := r) (q := q) (x := x)
          hbst_node hmem_r

private theorem rooted_pivot_access_reset_pair_path_le
    {t : BinaryTree} {q x : Nat}
    (hbst : IsBST t) (hroot : rootKey t = some q)
    (hmem_left : x ∈ (leftSubtree t).toKeyList) :
    t.search_path_len x + (splay t x).search_path_len q ≤
      2 * t.search_path_len x := by
  have hreset :=
    rooted_pivot_reset_search_path_le hbst hroot hmem_left
  omega

private theorem rooted_pivot_access_reset_pair_path_le_three_leftSubtree
    {t : BinaryTree} {q x : Nat}
    (hbst : IsBST t) (hroot : rootKey t = some q)
    (hmem_left : x ∈ (leftSubtree t).toKeyList) :
    t.search_path_len x + (splay t x).search_path_len q ≤
      3 * (1 + (leftSubtree t).search_path_len x) := by
  have hpair :=
    rooted_pivot_access_reset_pair_path_le hbst hroot hmem_left
  have hpath :
      t.search_path_len x = 1 + (leftSubtree t).search_path_len x := by
    cases ht : t with
    | empty =>
        simp [rootKey, ht] at hroot
    | node l k r =>
        simp [rootKey, ht] at hroot
        subst k
        have hbst_node : IsBST (BinaryTree.node l q r) := by
          simpa [ht] using hbst
        have hmem_l : x ∈ l.toKeyList := by
          simpa [ht, leftSubtree] using hmem_left
        have hx_lt_q := isBST_left_mem_lt_root hbst_node hmem_l
        simp [leftSubtree, BinaryTree.search_path_len, hx_lt_q]
  rw [hpath] at hpair
  omega

private theorem rooted_pivot_access_reset_pair_path_right_le
    {t : BinaryTree} {q x : Nat}
    (hbst : IsBST t) (hroot : rootKey t = some q)
    (hmem_right : x ∈ (rightSubtree t).toKeyList) :
    t.search_path_len x + (splay t x).search_path_len q ≤
      2 * t.search_path_len x := by
  have hreset :=
    rooted_pivot_reset_search_path_right_le hbst hroot hmem_right
  omega

private theorem rooted_pivot_access_reset_pair_path_right_le_three_rightSubtree
    {t : BinaryTree} {q x : Nat}
    (hbst : IsBST t) (hroot : rootKey t = some q)
    (hmem_right : x ∈ (rightSubtree t).toKeyList) :
    t.search_path_len x + (splay t x).search_path_len q ≤
      3 * (1 + (rightSubtree t).search_path_len x) := by
  have hpair :=
    rooted_pivot_access_reset_pair_path_right_le hbst hroot hmem_right
  have hpath :
      t.search_path_len x = 1 + (rightSubtree t).search_path_len x := by
    cases ht : t with
    | empty =>
        simp [rootKey, ht] at hroot
    | node l k r =>
        simp [rootKey, ht] at hroot
        subst k
        have hbst_node : IsBST (BinaryTree.node l q r) := by
          simpa [ht] using hbst
        have hmem_r : x ∈ r.toKeyList := by
          simpa [ht, rightSubtree] using hmem_right
        have hq_lt_x := isBST_right_mem_gt_root hbst_node hmem_r
        have hnot : ¬ x < q := by omega
        simp [rightSubtree, BinaryTree.search_path_len, hnot, hq_lt_x]
  rw [hpath] at hpair
  omega

private theorem search_path_len_left_le_after_splay_right
    {l r : BinaryTree} {k q y : Nat}
    (hbst : IsBST (BinaryTree.node l k r))
    (hqmem : q ∈ r.toKeyList)
    (hymem : y ∈ l.toKeyList) :
    (BinaryTree.node l k r).search_path_len y ≤
      (splay (BinaryTree.node l k r) q).search_path_len y := by
  have hy_lt_k : y < k := isBST_left_mem_lt_root hbst hymem
  have hk_lt_q : k < q := isBST_right_mem_gt_root hbst hqmem
  cases r with
  | empty =>
      simp [BinaryTree.toKeyList] at hqmem
  | node rl rk rr =>
      cases hbst with
      | node _ _ _ hleft hright hbst_left hbst_right =>
          cases hbst_right with
          | node _ _ _ hrl_left hrr_right hbst_rl hbst_rr =>
              have hk_lt_rk : k < rk :=
                (forallTree_iff_forall_mem.mp hright) rk
                  (by simp [BinaryTree.toKeyList])
              have hy_lt_rk : y < rk := by omega
              simp [BinaryTree.toKeyList] at hqmem
              rw [splay.eq_def]
              rcases hqmem with hqmem_rl | hq_eq_rk | hqmem_rr
              · have hq_lt_rk : q < rk :=
                  (forallTree_iff_forall_mem.mp hrl_left) q hqmem_rl
                have hnot_q_lt_k : ¬ q < k := by omega
                have hq_ne_k : q ≠ k := by omega
                have hq_ne_rk : q ≠ rk := by omega
                cases rl with
                | empty =>
                    simp [BinaryTree.toKeyList] at hqmem_rl
                | node a x b =>
                    have hroot_inner :=
                      splay_rootKey_eq_some_of_mem_isBST
                        (.node a x b) q hbst_rl hqmem_rl
                    cases hs : splay (.node a x b) q with
                    | empty =>
                        simp [rootKey, hs] at hroot_inner
                    | node sl sk sr =>
                        simp [rootKey, hs] at hroot_inner
                        subst sk
                        have hy_lt_q : y < q := by omega
                        simp [hnot_q_lt_k, hq_ne_k, hq_lt_rk,
                          hs, rotate, rotateLeft, rotateRight,
                          BinaryTree.search_path_len, hy_lt_k, hy_lt_q]
              · subst q
                have hnot_rk_lt_k : ¬ rk < k := by omega
                have hrk_ne_k : rk ≠ k := by omega
                simp [hnot_rk_lt_k, hrk_ne_k, rotate, rotateLeft,
                  BinaryTree.search_path_len, hy_lt_k, hy_lt_rk]
              · have hrk_lt_q : rk < q :=
                  (forallTree_iff_forall_mem.mp hrr_right) q hqmem_rr
                have hnot_q_lt_k : ¬ q < k := by omega
                have hnot_q_lt_rk : ¬ q < rk := by omega
                have hq_ne_k : q ≠ k := by omega
                have hq_ne_rk : q ≠ rk := by omega
                cases rr with
                | empty =>
                    simp [BinaryTree.toKeyList] at hqmem_rr
                | node a x b =>
                    have hroot_inner :=
                      splay_rootKey_eq_some_of_mem_isBST
                        (.node a x b) q hbst_rr hqmem_rr
                    cases hs : splay (.node a x b) q with
                    | empty =>
                        simp [rootKey, hs] at hroot_inner
                    | node sl sk sr =>
                        simp [rootKey, hs] at hroot_inner
                        subst sk
                        have hy_lt_q : y < q := by omega
                        simp [hnot_q_lt_k, hq_ne_k, hnot_q_lt_rk,
                          hrk_lt_q, hs, rotate, rotateLeft,
                          BinaryTree.search_path_len, hy_lt_k, hy_lt_rk,
                          hy_lt_q]
                        omega

private theorem search_path_len_right_le_after_splay_left
    {l r : BinaryTree} {k q y : Nat}
    (hbst : IsBST (BinaryTree.node l k r))
    (hqmem : q ∈ l.toKeyList)
    (hymem : y ∈ r.toKeyList) :
    (BinaryTree.node l k r).search_path_len y ≤
      (splay (BinaryTree.node l k r) q).search_path_len y := by
  have hq_lt_k : q < k := isBST_left_mem_lt_root hbst hqmem
  have hk_lt_y : k < y := isBST_right_mem_gt_root hbst hymem
  cases l with
  | empty =>
      simp [BinaryTree.toKeyList] at hqmem
  | node ll lk lr =>
      cases hbst with
      | node _ _ _ hleft hright hbst_left hbst_right =>
          cases hbst_left with
          | node _ _ _ hll_left hlr_right hbst_ll hbst_lr =>
              have hlk_lt_k : lk < k :=
                (forallTree_iff_forall_mem.mp hleft) lk
                  (by simp [BinaryTree.toKeyList])
              have hlk_lt_y : lk < y := by omega
              simp [BinaryTree.toKeyList] at hqmem
              rw [splay.eq_def]
              rcases hqmem with hqmem_ll | hq_eq_lk | hqmem_lr
              · have hq_lt_lk : q < lk :=
                  (forallTree_iff_forall_mem.mp hll_left) q hqmem_ll
                have hq_ne_k : q ≠ k := by omega
                have hq_ne_lk : q ≠ lk := by omega
                cases ll with
                | empty =>
                    simp [BinaryTree.toKeyList] at hqmem_ll
                | node a x b =>
                    have hroot_inner :=
                      splay_rootKey_eq_some_of_mem_isBST
                        (.node a x b) q hbst_ll hqmem_ll
                    cases hs : splay (.node a x b) q with
                    | empty =>
                        simp [rootKey, hs] at hroot_inner
                    | node sl sk sr =>
                        simp [rootKey, hs] at hroot_inner
                        subst sk
                        have hq_lt_y : q < y := by omega
                        have hnot_y_lt_q : ¬ y < q := by omega
                        have hnot_y_lt_lk : ¬ y < lk := by omega
                        have hnot_y_lt_k : ¬ y < k := by omega
                        simp [hq_ne_k, hq_lt_k, hq_lt_lk,
                          hs, rotate, rotateRight,
                          BinaryTree.search_path_len, hnot_y_lt_q,
                          hnot_y_lt_lk, hnot_y_lt_k, hlk_lt_y, hk_lt_y,
                          hq_lt_y]
                        omega
              · subst q
                have hlk_ne_k : lk ≠ k := by omega
                have hnot_y_lt_lk : ¬ y < lk := by omega
                have hnot_y_lt_k : ¬ y < k := by omega
                simp [hlk_lt_k, hlk_ne_k, rotate, rotateRight,
                  BinaryTree.search_path_len, hnot_y_lt_lk, hnot_y_lt_k,
                  hk_lt_y, hlk_lt_y]
              · have hlk_lt_q : lk < q :=
                  (forallTree_iff_forall_mem.mp hlr_right) q hqmem_lr
                have hnot_q_lt_lk : ¬ q < lk := by omega
                have hq_ne_k : q ≠ k := by omega
                have hq_ne_lk : q ≠ lk := by omega
                cases lr with
                | empty =>
                    simp [BinaryTree.toKeyList] at hqmem_lr
                | node a x b =>
                    have hroot_inner :=
                      splay_rootKey_eq_some_of_mem_isBST
                        (.node a x b) q hbst_lr hqmem_lr
                    cases hs : splay (.node a x b) q with
                    | empty =>
                        simp [rootKey, hs] at hroot_inner
                    | node sl sk sr =>
                        simp [rootKey, hs] at hroot_inner
                        subst sk
                        have hq_lt_y : q < y := by omega
                        have hnot_y_lt_q : ¬ y < q := by omega
                        have hnot_y_lt_lk : ¬ y < lk := by omega
                        have hnot_y_lt_k : ¬ y < k := by omega
                        simp [hq_ne_k, hq_lt_k, hnot_q_lt_lk,
                          hlk_lt_q, hs, rotate, rotateLeft,
                          rotateRight, BinaryTree.search_path_len,
                          hnot_y_lt_q, hnot_y_lt_k, hk_lt_y, hq_lt_y]

private theorem rooted_left_path_le_after_splay_right
    {t : BinaryTree} {root q y : Nat}
    (hbst : IsBST t) (hroot : rootKey t = some root)
    (hqmem : q ∈ (rightSubtree t).toKeyList)
    (hymem : y ∈ (leftSubtree t).toKeyList) :
    t.search_path_len y ≤ (splay t q).search_path_len y := by
  cases ht : t with
  | empty =>
      simp [rootKey, ht] at hroot
  | node l k r =>
      simp [rootKey, ht] at hroot
      subst k
      have hbst_node : IsBST (BinaryTree.node l root r) := by
        simpa [ht] using hbst
      have hqmem_r : q ∈ r.toKeyList := by
        simpa [ht, rightSubtree] using hqmem
      have hymem_l : y ∈ l.toKeyList := by
        simpa [ht, leftSubtree] using hymem
      simpa [ht] using
        search_path_len_left_le_after_splay_right
          (l := l) (r := r) (k := root) (q := q) (y := y)
          hbst_node hqmem_r hymem_l

private theorem rooted_right_path_le_after_splay_left
    {t : BinaryTree} {root q y : Nat}
    (hbst : IsBST t) (hroot : rootKey t = some root)
    (hqmem : q ∈ (leftSubtree t).toKeyList)
    (hymem : y ∈ (rightSubtree t).toKeyList) :
    t.search_path_len y ≤ (splay t q).search_path_len y := by
  cases ht : t with
  | empty =>
      simp [rootKey, ht] at hroot
  | node l k r =>
      simp [rootKey, ht] at hroot
      subst k
      have hbst_node : IsBST (BinaryTree.node l root r) := by
        simpa [ht] using hbst
      have hqmem_l : q ∈ l.toKeyList := by
        simpa [ht, leftSubtree] using hqmem
      have hymem_r : y ∈ r.toKeyList := by
        simpa [ht, rightSubtree] using hymem
      simpa [ht] using
        search_path_len_right_le_after_splay_left
          (l := l) (r := r) (k := root) (q := q) (y := y)
          hbst_node hqmem_l hymem_r

private theorem rooted_cross_path_len_le_path_add_after_splay
    {t : BinaryTree} {root q y : Nat}
    (hbst : IsBST t) (hroot : rootKey t = some root)
    (hq_right : q ∈ (rightSubtree t).toKeyList)
    (hy_left : y ∈ (leftSubtree t).toKeyList) :
    t.search_path_len y ≤
      t.search_path_len q + (splay t q).search_path_len y := by
  have hle :=
    rooted_left_path_le_after_splay_right
      hbst hroot hq_right hy_left
  omega

private theorem rooted_cross_path_len_le_path_add_after_splay_symm
    {t : BinaryTree} {root q y : Nat}
    (hbst : IsBST t) (hroot : rootKey t = some root)
    (hq_left : q ∈ (leftSubtree t).toKeyList)
    (hy_right : y ∈ (rightSubtree t).toKeyList) :
    t.search_path_len y ≤
      t.search_path_len q + (splay t q).search_path_len y := by
  have hle :=
    rooted_right_path_le_after_splay_left
      hbst hroot hq_left hy_right
  omega

private theorem rootKey_after_pivot_reset_of_root
    {t : BinaryTree} {q x : Nat}
    (hbst : IsBST t) (hroot : rootKey t = some q) :
    rootKey (splay (splay t x) q) = some q := by
  have hmem : q ∈ (splay t x).toKeyList := by
    rw [splay_toKeyList]
    exact rootKey_mem_toKeyList hroot
  exact splay_rootKey_eq_some_of_mem_isBST (splay t x) q
    (splay_isBST t x hbst) hmem

private theorem mem_leftSubtree_after_pivot_reset_of_lt
    {t : BinaryTree} {q x y : Nat}
    (hbst : IsBST t) (hroot : rootKey t = some q)
    (hymem : y ∈ t.toKeyList) (hylt : y < q) :
    y ∈ (leftSubtree (splay (splay t x) q)).toKeyList := by
  let tr := splay (splay t x) q
  have hroot_tr : rootKey tr = some q := by
    unfold tr
    exact rootKey_after_pivot_reset_of_root hbst hroot
  have hbst_tr : IsBST tr := by
    unfold tr
    exact splay_isBST (splay t x) q (splay_isBST t x hbst)
  have hymem_tr : y ∈ tr.toKeyList := by
    unfold tr
    rw [splay_toKeyList, splay_toKeyList]
    exact hymem
  exact mem_leftSubtree_of_root_lt_isBST hbst_tr hroot_tr hymem_tr hylt

private theorem mem_rightSubtree_after_pivot_reset_of_gt
    {t : BinaryTree} {q x y : Nat}
    (hbst : IsBST t) (hroot : rootKey t = some q)
    (hymem : y ∈ t.toKeyList) (hygt : q < y) :
    y ∈ (rightSubtree (splay (splay t x) q)).toKeyList := by
  let tr := splay (splay t x) q
  have hroot_tr : rootKey tr = some q := by
    unfold tr
    exact rootKey_after_pivot_reset_of_root hbst hroot
  have hbst_tr : IsBST tr := by
    unfold tr
    exact splay_isBST (splay t x) q (splay_isBST t x hbst)
  have hymem_tr : y ∈ tr.toKeyList := by
    unfold tr
    rw [splay_toKeyList, splay_toKeyList]
    exact hymem
  exact mem_rightSubtree_of_root_gt_isBST hbst_tr hroot_tr hymem_tr hygt

private theorem splay_cost_add_one_eq_search_path_len_of_mem
    (t : BinaryTree) (q : Nat) (hmem : q ∈ t.toKeyList) :
    splay.cost t q + 1 = t.search_path_len q := by
  rw [splay_cost_eq_search_path_len_sub_one]
  have hpos := search_path_len_pos_of_mem t q hmem
  have hnat : (t.search_path_len q - 1) + 1 = t.search_path_len q := by
    omega
  exact_mod_cast hnat

private theorem splay_cost_attachLeftFrames_eq_add_length
    (t : BinaryTree) (q : Nat) (fs : List LeftContextFrame)
    (hframes : frameKeysAbove q fs) (hmem : q ∈ t.toKeyList) :
    splay.cost (attachLeftFrames t fs) q =
      splay.cost t q + (fs.length : ℝ) := by
  have hmem_attach :
      q ∈ (attachLeftFrames t fs).toKeyList :=
    mem_toKeyList_attachLeftFrames_of_mem t fs hmem
  have hcost_attach :=
    splay_cost_add_one_eq_search_path_len_of_mem
      (attachLeftFrames t fs) q hmem_attach
  have hcost_base :=
    splay_cost_add_one_eq_search_path_len_of_mem t q hmem
  have hpath :=
    search_path_len_attachLeftFrames_of_frameKeysAbove t q fs hframes
  rw [hpath] at hcost_attach
  norm_num at hcost_attach
  nlinarith

private theorem splay_cost_attachLeftFrames_zigzig_eq
    {a b lr r : BinaryTree} {x lk k q : Nat}
    {fs : List LeftContextFrame}
    (hbst :
      IsBST (attachLeftFrames
        (.node (.node (.node a x b) lk lr) k r) fs))
    (hmem : q ∈ (BinaryTree.node a x b).toKeyList) :
    splay.cost
        (attachLeftFrames (.node (.node (.node a x b) lk lr) k r) fs) q =
      splay.cost (.node a x b) q + ((fs.length + 2 : Nat) : ℝ) := by
  have hframes :=
    frameKeysAbove_zigzig_context_of_isBST hbst hmem
  have hcost :=
    splay_cost_attachLeftFrames_eq_add_length
      (.node a x b) q ((lk, lr) :: (k, r) :: fs) hframes hmem
  rw [attachLeftFrames_zigzig_context] at hcost
  simpa [Nat.cast_add, Nat.cast_ofNat, add_assoc, add_comm, add_left_comm]
    using hcost

private theorem splayMinUnwindResult_zigzig_context
    (a b lr r : BinaryTree) (x lk k : Nat)
    (fs : List LeftContextFrame) :
    splayMinUnwindResult
        (.node (.node (.node a x b) lk lr) k r) fs =
      splayMinUnwindResult (.node a x b)
        ((lk, lr) :: (k, r) :: fs) := by
  simp [splayMinUnwindResult]

private theorem zigzig_context_min_state
    {a b lr r : BinaryTree} {x lk k q : Nat}
    {fs : List LeftContextFrame}
    (hbst :
      IsBST (attachLeftFrames
        (.node (.node (.node a x b) lk lr) k r) fs))
    (hmem : q ∈
      (BinaryTree.node (.node (.node a x b) lk lr) k r).toKeyList)
    (hmin : ∀ y : Nat,
      y ∈ (attachLeftFrames
        (.node (.node (.node a x b) lk lr) k r) fs).toKeyList →
        q ≤ y) :
    IsBST (attachLeftFrames (.node a x b)
        ((lk, lr) :: (k, r) :: fs)) ∧
      q ∈ (BinaryTree.node a x b).toKeyList ∧
      (∀ y : Nat,
        y ∈ (attachLeftFrames (.node a x b)
          ((lk, lr) :: (k, r) :: fs)).toKeyList →
          q ≤ y) := by
  have hbst_base :
      IsBST (.node (.node (.node a x b) lk lr) k r) :=
    isBST_of_isBST_attachLeftFrames
      (.node (.node (.node a x b) lk lr) k r) fs hbst
  have hmin_base :
      ∀ y : Nat,
        y ∈
          (BinaryTree.node (.node (.node a x b) lk lr) k r).toKeyList →
          q ≤ y := by
    intro y hy
    exact hmin y (mem_toKeyList_attachLeftFrames_of_mem
      (.node (.node (.node a x b) lk lr) k r) fs hy)
  rcases min_left_left_state_of_left_left_nonempty hbst_base hmem
      hmin_base with
    ⟨_hbst_inner, hmem_inner, _hmin_inner, _hq_lt_lk⟩
  have hbst_inner_context :
      IsBST (attachLeftFrames (.node a x b)
        ((lk, lr) :: (k, r) :: fs)) := by
    simpa [attachLeftFrames] using hbst
  refine ⟨hbst_inner_context, hmem_inner, ?_⟩
  intro y hy
  exact hmin y (by
    simpa [attachLeftFrames] using hy)

private theorem splayMinUnwind_zigzig_bound_of_inner
    {a b lr r : BinaryTree} {x lk k q : Nat}
    {fs : List LeftContextFrame} {C : ℝ}
    (hinner :
      splay.cost
          (attachLeftFrames (.node a x b)
            ((lk, lr) :: (k, r) :: fs)) q +
          strongSequentialPotential
            (splayMinUnwindResult (.node a x b)
              ((lk, lr) :: (k, r) :: fs)) ≤
        strongSequentialPotential
          (attachLeftFrames (.node a x b)
            ((lk, lr) :: (k, r) :: fs)) + C) :
    splay.cost
        (attachLeftFrames
          (.node (.node (.node a x b) lk lr) k r) fs) q +
        strongSequentialPotential
          (splayMinUnwindResult
            (.node (.node (.node a x b) lk lr) k r) fs) ≤
      strongSequentialPotential
        (attachLeftFrames
          (.node (.node (.node a x b) lk lr) k r) fs) + C := by
  simpa [attachLeftFrames, splayMinUnwindResult] using hinner

private theorem splayMinUnwind_amortized_with_leftMinDepth :
    ∀ (t : BinaryTree) (fs : List LeftContextFrame) (q : Nat),
      IsBST (attachLeftFrames t fs) →
      q ∈ t.toKeyList →
      (∀ y : Nat, y ∈ (attachLeftFrames t fs).toKeyList → q ≤ y) →
      splay.cost (attachLeftFrames t fs) q +
          strongSequentialPotential (splayMinUnwindResult t fs) ≤
        strongSequentialPotential (attachLeftFrames t fs) +
          (fs.length : ℝ) + (leftMinDepth t : ℝ)
| .empty, fs, q, _hbst, hmem, _hmin => by
    simp [BinaryTree.toKeyList] at hmem
| .node .empty k r, fs, q, hbst, hmem, hmin => by
    have h :=
      splayMinContext_left_empty_amortized_of_min
        (r := r) (k := k) (q := q) (fs := fs) hbst hmem hmin
    simpa [splayMinUnwindResult, leftMinDepth, add_assoc] using h
| .node (.node .empty lk lr) k r, fs, q, hbst, hmem, hmin => by
    have h :=
      splayMinContext_left_left_empty_amortized_of_min
        (lr := lr) (r := r) (lk := lk) (k := k) (q := q)
        (fs := fs) hbst hmem hmin
    simp [splayMinUnwindResult, leftMinDepth]
    nlinarith [h]
| .node (.node (.node a x b) lk lr) k r, fs, q, hbst, hmem, hmin => by
    rcases zigzig_context_min_state hbst hmem hmin with
      ⟨hbst_inner, hmem_inner, hmin_inner⟩
    have ih :=
      splayMinUnwind_amortized_with_leftMinDepth
        (.node a x b) ((lk, lr) :: (k, r) :: fs) q
        hbst_inner hmem_inner hmin_inner
    simp [attachLeftFrames, splayMinUnwindResult, leftMinDepth,
      Nat.cast_add, Nat.cast_ofNat, add_assoc, add_comm, add_left_comm] at ih ⊢
    nlinarith [ih]

private theorem rightSubtree_splay_attachLeftFrames_min_eq_unwind :
    ∀ (t : BinaryTree) (fs : List LeftContextFrame) (q : Nat),
      IsBST (attachLeftFrames t fs) →
      q ∈ t.toKeyList →
      (∀ y : Nat, y ∈ (attachLeftFrames t fs).toKeyList → q ≤ y) →
      rightSubtree (splay (attachLeftFrames t fs) q) =
        splayMinUnwindResult t fs
| .empty, fs, q, _hbst, hmem, _hmin => by
    simp [BinaryTree.toKeyList] at hmem
| .node .empty k r, fs, q, hbst, hmem, hmin => by
    have hbst_base :
        IsBST (.node .empty k r) :=
      isBST_of_isBST_attachLeftFrames (.node .empty k r) fs hbst
    have hmin_base :
        ∀ y : Nat, y ∈ (BinaryTree.node .empty k r).toKeyList → q ≤ y := by
      intro y hy
      exact hmin y (mem_toKeyList_attachLeftFrames_of_mem
        (.node .empty k r) fs hy)
    have hq : q = k :=
      min_eq_root_of_left_empty hbst_base hmem hmin_base
    subst q
    have hframes :
        frameKeysAbove k fs :=
      frameKeysAbove_of_isBST_attachLeftFrames_mem
        (.node .empty k r) fs k hbst
        (by simp [BinaryTree.toKeyList])
    simpa [splayMinUnwindResult] using
      rightSubtree_splay_attachLeftFrames_left_empty_eq r k fs hframes
| .node (.node .empty lk lr) k r, fs, q, hbst, hmem, hmin => by
    have hbst_base :
        IsBST (.node (.node .empty lk lr) k r) :=
      isBST_of_isBST_attachLeftFrames
        (.node (.node .empty lk lr) k r) fs hbst
    have hmin_base :
        ∀ y : Nat,
          y ∈ (BinaryTree.node (.node .empty lk lr) k r).toKeyList →
            q ≤ y := by
      intro y hy
      exact hmin y (mem_toKeyList_attachLeftFrames_of_mem
        (.node (.node .empty lk lr) k r) fs hy)
    have hq : q = lk :=
      min_eq_left_root_of_left_left_empty hbst_base hmem hmin_base
    subst q
    have hbst_context :
        IsBST (attachLeftFrames (.node .empty lk lr) ((k, r) :: fs)) := by
      simpa [attachLeftFrames] using hbst
    have hframes :
        frameKeysAbove lk ((k, r) :: fs) :=
      frameKeysAbove_of_isBST_attachLeftFrames_mem
        (.node .empty lk lr) ((k, r) :: fs) lk hbst_context
        (by simp [BinaryTree.toKeyList])
    have hroot :=
      rightSubtree_splay_attachLeftFrames_left_empty_eq
        lr lk ((k, r) :: fs) hframes
    simpa [attachLeftFrames, splayMinUnwindResult] using hroot
| .node (.node (.node a x b) lk lr) k r, fs, q, hbst, hmem, hmin => by
    rcases zigzig_context_min_state hbst hmem hmin with
      ⟨hbst_inner, hmem_inner, hmin_inner⟩
    have ih :=
      rightSubtree_splay_attachLeftFrames_min_eq_unwind
        (.node a x b) ((lk, lr) :: (k, r) :: fs) q
        hbst_inner hmem_inner hmin_inner
    simpa [attachLeftFrames, splayMinUnwindResult] using ih

private theorem rightSubtree_splay_min_eq_unwind
    (t : BinaryTree) (q : Nat)
    (hbst : IsBST t) (hmem : q ∈ t.toKeyList)
    (hmin : ∀ y : Nat, y ∈ t.toKeyList → q ≤ y) :
    rightSubtree (splay t q) = splayMinUnwindResult t [] := by
  simpa [attachLeftFrames] using
    rightSubtree_splay_attachLeftFrames_min_eq_unwind
      t [] q (by simpa [attachLeftFrames] using hbst) hmem
      (by simpa [attachLeftFrames] using hmin)

private theorem splay_min_delete_step_strong_of_unwind_bound
    (t : BinaryTree) (q : Nat)
    (hbst : IsBST t) (hmem : q ∈ t.toKeyList)
    (hmin : ∀ y : Nat, y ∈ t.toKeyList → q ≤ y)
    (hbound :
      splay.cost t q + strongSequentialPotential (splayMinUnwindResult t []) ≤
        strongSequentialPotential t) :
    splay.cost t q +
        strongSequentialPotential (rightSubtree (splay t q)) ≤
      strongSequentialPotential t := by
  rw [rightSubtree_splay_min_eq_unwind t q hbst hmem hmin]
  exact hbound

private theorem splay_min_delete_step_strong_with_leftMinDepth
    (t : BinaryTree) (q : Nat)
    (hbst : IsBST t) (hmem : q ∈ t.toKeyList)
    (hmin : ∀ y : Nat, y ∈ t.toKeyList → q ≤ y) :
    splay.cost t q +
        strongSequentialPotential (rightSubtree (splay t q)) ≤
      strongSequentialPotential t + (leftMinDepth t : ℝ) := by
  have h :=
    splayMinUnwind_amortized_with_leftMinDepth
      t [] q (by simpa [attachLeftFrames] using hbst) hmem
      (by simpa [attachLeftFrames] using hmin)
  rw [rightSubtree_splay_min_eq_unwind t q hbst hmem hmin]
  simpa [attachLeftFrames, add_assoc] using h

private theorem splay_min_delete_step_strong_with_num_nodes
    (t : BinaryTree) (q : Nat)
    (hbst : IsBST t) (hmem : q ∈ t.toKeyList)
    (hmin : ∀ y : Nat, y ∈ t.toKeyList → q ≤ y) :
    splay.cost t q +
        strongSequentialPotential (rightSubtree (splay t q)) ≤
      strongSequentialPotential t + (t.num_nodes : ℝ) := by
  have h :=
    splay_min_delete_step_strong_with_leftMinDepth
      t q hbst hmem hmin
  have hdepth_nat := leftMinDepth_le_num_nodes t
  have hdepth : (leftMinDepth t : ℝ) ≤ t.num_nodes := by
    exact_mod_cast hdepth_nat
  nlinarith

private theorem splayMinUnwindResult_isBST
    (t : BinaryTree) (fs : List LeftContextFrame) (q : Nat)
    (hbst : IsBST (attachLeftFrames t fs))
    (hmem : q ∈ t.toKeyList)
    (hmin : ∀ y : Nat, y ∈ (attachLeftFrames t fs).toKeyList → q ≤ y) :
    IsBST (splayMinUnwindResult t fs) := by
  have heq :=
    rightSubtree_splay_attachLeftFrames_min_eq_unwind
      t fs q hbst hmem hmin
  rw [← heq]
  exact rightSubtree_isBST_of_isBST
    (splay_isBST (attachLeftFrames t fs) q hbst)

private theorem mem_splayMinUnwindResult_of_gt
    (t : BinaryTree) (fs : List LeftContextFrame) (q x : Nat)
    (hbst : IsBST (attachLeftFrames t fs))
    (hmemq : q ∈ t.toKeyList)
    (hmin : ∀ y : Nat, y ∈ (attachLeftFrames t fs).toKeyList → q ≤ y)
    (hxmem : x ∈ (attachLeftFrames t fs).toKeyList) (hgt : q < x) :
    x ∈ (splayMinUnwindResult t fs).toKeyList := by
  have heq :=
    rightSubtree_splay_attachLeftFrames_min_eq_unwind
      t fs q hbst hmemq hmin
  rw [← heq]
  exact mem_rightSubtree_splay_min_of_gt
    (attachLeftFrames t fs) q x hbst
    (mem_toKeyList_attachLeftFrames_of_mem t fs hmemq)
    hmin hxmem hgt

private theorem mem_splayMinUnwindResult_iff_gt
    (t : BinaryTree) (fs : List LeftContextFrame) (q x : Nat)
    (hbst : IsBST (attachLeftFrames t fs))
    (hmemq : q ∈ t.toKeyList)
    (hmin : ∀ y : Nat, y ∈ (attachLeftFrames t fs).toKeyList → q ≤ y) :
    x ∈ (splayMinUnwindResult t fs).toKeyList ↔
      x ∈ (attachLeftFrames t fs).toKeyList ∧ q < x := by
  rw [← rightSubtree_splay_attachLeftFrames_min_eq_unwind
    t fs q hbst hmemq hmin]
  exact mem_rightSubtree_splay_min_iff_gt
    (attachLeftFrames t fs) q x hbst
    (mem_toKeyList_attachLeftFrames_of_mem t fs hmemq) hmin

private theorem future_mem_splayMinUnwindResult_of_gt {n : Nat}
    (Y : Fin n → Nat) (t : BinaryTree) (fs : List LeftContextFrame)
    (q : Nat)
    (hbst : IsBST (attachLeftFrames t fs))
    (hmemq : q ∈ t.toKeyList)
    (hmin : ∀ y : Nat, y ∈ (attachLeftFrames t fs).toKeyList → q ≤ y)
    (hYmem : ∀ i : Fin n, Y i ∈ (attachLeftFrames t fs).toKeyList)
    (hgt : ∀ i : Fin n, q < Y i) :
    ∀ i : Fin n, Y i ∈ (splayMinUnwindResult t fs).toKeyList := by
  intro i
  exact mem_splayMinUnwindResult_of_gt t fs q (Y i)
    hbst hmemq hmin (hYmem i) (hgt i)

private theorem splayMinUnwind_delete_state {n : Nat}
    (Y : Fin n → Nat) (t : BinaryTree) (fs : List LeftContextFrame)
    (q : Nat)
    (hbst : IsBST (attachLeftFrames t fs))
    (hmemq : q ∈ t.toKeyList)
    (hpos : 0 < t.num_nodes)
    (hmin : ∀ y : Nat, y ∈ (attachLeftFrames t fs).toKeyList → q ≤ y)
    (hYmem : ∀ i : Fin n, Y i ∈ (attachLeftFrames t fs).toKeyList)
    (hgt : ∀ i : Fin n, q < Y i) :
    ((splayMinUnwindResult t fs).num_nodes + 1 =
        (attachLeftFrames t fs).num_nodes) ∧
      IsBST (splayMinUnwindResult t fs) ∧
      (∀ i : Fin n, Y i ∈ (splayMinUnwindResult t fs).toKeyList) := by
  exact ⟨splayMinUnwindResult_num_nodes_add_one t fs hpos,
    splayMinUnwindResult_isBST t fs q hbst hmemq hmin,
    future_mem_splayMinUnwindResult_of_gt Y t fs q hbst hmemq hmin
      hYmem hgt⟩

private theorem splay_cost_le_num_nodes : ∀ (t : BinaryTree) (q : Nat),
    splay.cost t q ≤ t.num_nodes
| .empty, q => by
    simp [splay.cost.eq_def, BinaryTree.num_nodes]
| .node l k r, q => by
    rw [splay.cost.eq_def]
    by_cases hqk : q = k
    · simp [hqk, BinaryTree.num_nodes]
      positivity
    · by_cases hq_lt_k : q < k
      · cases l with
        | empty =>
            simp [hqk, hq_lt_k, BinaryTree.num_nodes]
            positivity
        | node ll lk lr =>
            by_cases hq_lt_lk : q < lk
            · cases ll with
              | empty =>
                  simp [hqk, hq_lt_k, hq_lt_lk, BinaryTree.num_nodes]
                  nlinarith [show 0 ≤ (lr.num_nodes : ℝ) by positivity,
                    show 0 ≤ (r.num_nodes : ℝ) by positivity]
              | node a x b =>
                  have hll := splay_cost_le_num_nodes
                    (BinaryTree.node a x b) q
                  simp [BinaryTree.num_nodes] at hll
                  simp [hqk, hq_lt_k, hq_lt_lk, BinaryTree.num_nodes]
                  nlinarith [hll, show 0 ≤ (lr.num_nodes : ℝ) by positivity,
                    show 0 ≤ (r.num_nodes : ℝ) by positivity]
            · by_cases hlk_lt_q : lk < q
              · cases lr with
                | empty =>
                    simp [hqk, hq_lt_k, hq_lt_lk, hlk_lt_q,
                      BinaryTree.num_nodes]
                    nlinarith [show 0 ≤ (ll.num_nodes : ℝ) by positivity,
                      show 0 ≤ (r.num_nodes : ℝ) by positivity]
                | node a x b =>
                    have hlr := splay_cost_le_num_nodes
                      (BinaryTree.node a x b) q
                    simp [BinaryTree.num_nodes] at hlr
                    simp [hqk, hq_lt_k, hq_lt_lk, hlk_lt_q,
                      BinaryTree.num_nodes]
                    nlinarith [hlr, show 0 ≤ (ll.num_nodes : ℝ) by positivity,
                      show 0 ≤ (r.num_nodes : ℝ) by positivity]
              · simp [hqk, hq_lt_k, hq_lt_lk, hlk_lt_q,
                  BinaryTree.num_nodes]
                nlinarith [show 0 ≤ (ll.num_nodes : ℝ) by positivity,
                  show 0 ≤ (lr.num_nodes : ℝ) by positivity,
                  show 0 ≤ (r.num_nodes : ℝ) by positivity]
      · cases r with
        | empty =>
            simp [hqk, hq_lt_k, BinaryTree.num_nodes]
            positivity
        | node rl rk rr =>
            by_cases hq_lt_rk : q < rk
            · cases rl with
              | empty =>
                  simp [hqk, hq_lt_k, hq_lt_rk, BinaryTree.num_nodes]
                  nlinarith [show 0 ≤ (l.num_nodes : ℝ) by positivity,
                    show 0 ≤ (rr.num_nodes : ℝ) by positivity]
              | node a x b =>
                  have hrl := splay_cost_le_num_nodes
                    (BinaryTree.node a x b) q
                  simp [BinaryTree.num_nodes] at hrl
                  simp [hqk, hq_lt_k, hq_lt_rk, BinaryTree.num_nodes]
                  nlinarith [hrl, show 0 ≤ (l.num_nodes : ℝ) by positivity,
                    show 0 ≤ (rr.num_nodes : ℝ) by positivity]
            · by_cases hrk_lt_q : rk < q
              · cases rr with
                | empty =>
                    simp [hqk, hq_lt_k, hq_lt_rk, hrk_lt_q,
                      BinaryTree.num_nodes]
                    nlinarith [show 0 ≤ (l.num_nodes : ℝ) by positivity,
                      show 0 ≤ (rl.num_nodes : ℝ) by positivity]
                | node a x b =>
                    have hrr := splay_cost_le_num_nodes
                      (BinaryTree.node a x b) q
                    simp [BinaryTree.num_nodes] at hrr
                    simp [hqk, hq_lt_k, hq_lt_rk, hrk_lt_q,
                      BinaryTree.num_nodes]
                    nlinarith [hrr, show 0 ≤ (l.num_nodes : ℝ) by positivity,
                      show 0 ≤ (rl.num_nodes : ℝ) by positivity]
              · simp [hqk, hq_lt_k, hq_lt_rk, hrk_lt_q,
                  BinaryTree.num_nodes]
                nlinarith [show 0 ≤ (l.num_nodes : ℝ) by positivity,
                  show 0 ≤ (rl.num_nodes : ℝ) by positivity,
                  show 0 ≤ (rr.num_nodes : ℝ) by positivity]

private def splayStep {n : Nat} (X : Fin n → Nat)
    (acc : BinaryTree × ℝ) (i : Fin n) : BinaryTree × ℝ :=
  let (t, c) := acc
  (splay t (X i), c + splay.cost t (X i))

private def splayPathSum {n : Nat} (X : Fin n → Nat) :
    BinaryTree → List (Fin n) → ℝ
| _t, [] => 0
| t, i :: xs =>
    t.search_path_len (X i) + splayPathSum X (splay t (X i)) xs

private theorem splayPathSum_nonneg {n : Nat} (X : Fin n → Nat) :
    ∀ (xs : List (Fin n)) (t : BinaryTree),
      0 ≤ splayPathSum X t xs
| [], t => by
    simp [splayPathSum]
| i :: xs, t => by
    have ih := splayPathSum_nonneg X xs (splay t (X i))
    simp [splayPathSum]
    positivity

private theorem splayPathSum_le_length_mul_num_nodes {n : Nat}
    (X : Fin n → Nat) :
    ∀ (xs : List (Fin n)) (t : BinaryTree),
      splayPathSum X t xs ≤ (xs.length : ℝ) * t.num_nodes
| [], t => by
    simp [splayPathSum]
| i :: xs, t => by
    have hhead_nat := search_path_len_le_num_nodes t (X i)
    have hhead : (t.search_path_len (X i) : ℝ) ≤ t.num_nodes := by
      exact_mod_cast hhead_nat
    have htail := splayPathSum_le_length_mul_num_nodes X xs (splay t (X i))
    rw [splay_num_nodes] at htail
    simp [splayPathSum]
    nlinarith [show 0 ≤ (xs.length : ℝ) by positivity,
      show 0 ≤ (t.num_nodes : ℝ) by positivity]

private def pivotResetLowerPathSum {n : Nat} (Y : Fin n → Nat) (q : Nat) :
    BinaryTree → List (Fin n) → ℝ
| _t, [] => 0
| t, i :: xs =>
    t.search_path_len (Y i) +
      pivotResetLowerPathSum Y q (splay (splay t (Y i)) q) xs

private def pivotResetTreeAfter {n : Nat} (Y : Fin n → Nat) (q : Nat) :
    BinaryTree → List (Fin n) → BinaryTree
| t, [] => t
| t, i :: xs =>
    pivotResetTreeAfter Y q (splay (splay t (Y i)) q) xs

private def pivotResetPairPathSum {n : Nat} (Y : Fin n → Nat) (q : Nat) :
    BinaryTree → List (Fin n) → ℝ
| _t, [] => 0
| t, i :: xs =>
    t.search_path_len (Y i) +
      (splay t (Y i)).search_path_len q +
      pivotResetPairPathSum Y q (splay (splay t (Y i)) q) xs

private def splayPathSumWithFinal {n : Nat} (Y : Fin n → Nat) (q : Nat) :
    BinaryTree → List (Fin n) → ℝ
| t, [] => t.search_path_len q
| t, i :: xs =>
    t.search_path_len (Y i) +
      splayPathSumWithFinal Y q (splay t (Y i)) xs

private theorem splayPathSumWithFinal_nil {n : Nat}
    (Y : Fin n → Nat) (q : Nat) (t : BinaryTree) :
    splayPathSumWithFinal Y q t [] = t.search_path_len q := by
  simp [splayPathSumWithFinal]

private theorem splayPathSumWithFinal_cons {n : Nat}
    (Y : Fin n → Nat) (q : Nat) (t : BinaryTree)
    (i : Fin n) (xs : List (Fin n)) :
    splayPathSumWithFinal Y q t (i :: xs) =
      t.search_path_len (Y i) +
        splayPathSumWithFinal Y q (splay t (Y i)) xs := by
  simp [splayPathSumWithFinal]

private theorem splayPathSumWithFinal_singleton_eq_pairHead {n : Nat}
    (Y : Fin n → Nat) (q : Nat) (t : BinaryTree) (i : Fin n) :
    splayPathSumWithFinal Y q t [i] =
      t.search_path_len (Y i) + (splay t (Y i)).search_path_len q := by
  simp [splayPathSumWithFinal]

private theorem splayPathSumWithFinal_singleton_eq_pivotResetPairPathSum
    {n : Nat} (Y : Fin n → Nat) (q : Nat) (t : BinaryTree)
    (i : Fin n) :
    splayPathSumWithFinal Y q t [i] =
      pivotResetPairPathSum Y q t [i] := by
  simp [splayPathSumWithFinal_singleton_eq_pairHead,
    pivotResetPairPathSum]

private def suffixResetUpperPathSum {n : Nat} (Y : Fin n → Nat) (q : Nat) :
    BinaryTree → List (Fin n) → ℝ
| _t, [] => 0
| t, i :: xs =>
    if Y i < q then
      t.search_path_len (Y i) +
        (splay t (Y i)).search_path_len q +
        suffixResetUpperPathSum Y q (splay (splay t (Y i)) q) xs
    else
      1 + suffixResetUpperPathSum Y q t xs

private theorem suffixResetUpperPathSum_filter_split {n : Nat}
    (Y : Fin n → Nat) (q : Nat) :
    ∀ (xs : List (Fin n)) (t : BinaryTree),
      suffixResetUpperPathSum Y q t xs =
        pivotResetPairPathSum Y q t
          (xs.filter (fun i => decide (Y i < q))) +
          ((xs.filter (fun i => ! decide (Y i < q))).length : ℝ)
| [], t => by
    simp [suffixResetUpperPathSum, pivotResetPairPathSum]
| i :: xs, t => by
    by_cases hlt : Y i < q
    · have ih :=
        suffixResetUpperPathSum_filter_split Y q xs
          (splay (splay t (Y i)) q)
      simp [suffixResetUpperPathSum, pivotResetPairPathSum, hlt, ih]
      ring
    · have ih := suffixResetUpperPathSum_filter_split Y q xs t
      simp [suffixResetUpperPathSum, hlt, ih]
      ring

private theorem pivotResetLowerPathSum_map_comp {n m : Nat}
    (Y : Fin n → Nat) (g : Fin m → Fin n) (q : Nat) :
    ∀ (xs : List (Fin m)) (t : BinaryTree),
      pivotResetLowerPathSum Y q t (xs.map g) =
        pivotResetLowerPathSum (fun i : Fin m => Y (g i)) q t xs
| [], t => by
    simp [pivotResetLowerPathSum]
| i :: xs, t => by
    simp [pivotResetLowerPathSum,
      pivotResetLowerPathSum_map_comp Y g q xs
        (splay (splay t (Y (g i))) q)]

private theorem pivotResetTreeAfter_map_comp {n m : Nat}
    (Y : Fin n → Nat) (g : Fin m → Fin n) (q : Nat) :
    ∀ (xs : List (Fin m)) (t : BinaryTree),
      pivotResetTreeAfter Y q t (xs.map g) =
        pivotResetTreeAfter (fun i : Fin m => Y (g i)) q t xs
| [], t => by
    simp [pivotResetTreeAfter]
| i :: xs, t => by
    simp [pivotResetTreeAfter,
      pivotResetTreeAfter_map_comp Y g q xs
        (splay (splay t (Y (g i))) q)]

private theorem pivotResetPairPathSum_map_comp {n m : Nat}
    (Y : Fin n → Nat) (g : Fin m → Fin n) (q : Nat) :
    ∀ (xs : List (Fin m)) (t : BinaryTree),
      pivotResetPairPathSum Y q t (xs.map g) =
        pivotResetPairPathSum (fun i : Fin m => Y (g i)) q t xs
| [], t => by
    simp [pivotResetPairPathSum]
| i :: xs, t => by
    simp [pivotResetPairPathSum,
      pivotResetPairPathSum_map_comp Y g q xs
        (splay (splay t (Y (g i))) q)]

private theorem pivotResetPairPathSum_le_two_lowerPathSum {n : Nat}
    (Y : Fin n → Nat) (q : Nat) :
    ∀ (xs : List (Fin n)) (t : BinaryTree),
      IsBST t →
      rootKey t = some q →
      (∀ i : Fin n, i ∈ xs → Y i ∈ (leftSubtree t).toKeyList) →
      pivotResetPairPathSum Y q t xs ≤
        2 * pivotResetLowerPathSum Y q t xs
| [], t, _hbst, _hroot, _hmem_left => by
    simp [pivotResetPairPathSum, pivotResetLowerPathSum]
| i :: xs, t, hbst, hroot, hmem_left => by
    let tr := splay (splay t (Y i)) q
    have hi_left : Y i ∈ (leftSubtree t).toKeyList :=
      hmem_left i (by simp)
    have hpair :
        (t.search_path_len (Y i) : ℝ) +
            ((splay t (Y i)).search_path_len q : ℝ) ≤
          2 * (t.search_path_len (Y i) : ℝ) := by
      exact_mod_cast
        rooted_pivot_access_reset_pair_path_le hbst hroot hi_left
    have hbst_tr : IsBST tr := by
      unfold tr
      exact splay_isBST (splay t (Y i)) q (splay_isBST t (Y i) hbst)
    have hroot_tr : rootKey tr = some q := by
      unfold tr
      exact rootKey_after_pivot_reset_of_root hbst hroot
    have hmem_tail :
        ∀ j : Fin n, j ∈ xs → Y j ∈ (leftSubtree tr).toKeyList := by
      intro j hj
      have hj_left : Y j ∈ (leftSubtree t).toKeyList :=
        hmem_left j (by simp [hj])
      have hj_mem_t : Y j ∈ t.toKeyList :=
        mem_toKeyList_of_mem_leftSubtree hj_left
      have hj_lt : Y j < q :=
        rooted_leftSubtree_mem_lt hbst hroot hj_left
      unfold tr
      exact mem_leftSubtree_after_pivot_reset_of_lt
        hbst hroot hj_mem_t hj_lt
    have ih :=
      pivotResetPairPathSum_le_two_lowerPathSum Y q xs tr
        hbst_tr hroot_tr hmem_tail
    simp [pivotResetPairPathSum, pivotResetLowerPathSum]
    nlinarith

private theorem pivotResetPairPathSum_right_le_two_lowerPathSum {n : Nat}
    (Y : Fin n → Nat) (q : Nat) :
    ∀ (xs : List (Fin n)) (t : BinaryTree),
      IsBST t →
      rootKey t = some q →
      (∀ i : Fin n, i ∈ xs → Y i ∈ (rightSubtree t).toKeyList) →
      pivotResetPairPathSum Y q t xs ≤
        2 * pivotResetLowerPathSum Y q t xs
| [], t, _hbst, _hroot, _hmem_right => by
    simp [pivotResetPairPathSum, pivotResetLowerPathSum]
| i :: xs, t, hbst, hroot, hmem_right => by
    let tr := splay (splay t (Y i)) q
    have hi_right : Y i ∈ (rightSubtree t).toKeyList :=
      hmem_right i (by simp)
    have hpair :
        (t.search_path_len (Y i) : ℝ) +
            ((splay t (Y i)).search_path_len q : ℝ) ≤
          2 * (t.search_path_len (Y i) : ℝ) := by
      exact_mod_cast
        rooted_pivot_access_reset_pair_path_right_le hbst hroot hi_right
    have hbst_tr : IsBST tr := by
      unfold tr
      exact splay_isBST (splay t (Y i)) q (splay_isBST t (Y i) hbst)
    have hroot_tr : rootKey tr = some q := by
      unfold tr
      exact rootKey_after_pivot_reset_of_root hbst hroot
    have hmem_tail :
        ∀ j : Fin n, j ∈ xs → Y j ∈ (rightSubtree tr).toKeyList := by
      intro j hj
      have hj_right : Y j ∈ (rightSubtree t).toKeyList :=
        hmem_right j (by simp [hj])
      have hj_mem_t : Y j ∈ t.toKeyList :=
        mem_toKeyList_of_mem_rightSubtree hj_right
      have hj_gt : q < Y j :=
        rooted_rightSubtree_mem_gt hbst hroot hj_right
      unfold tr
      exact mem_rightSubtree_after_pivot_reset_of_gt
        hbst hroot hj_mem_t hj_gt
    have ih :=
      pivotResetPairPathSum_right_le_two_lowerPathSum Y q xs tr
        hbst_tr hroot_tr hmem_tail
    simp [pivotResetPairPathSum, pivotResetLowerPathSum]
    nlinarith

private theorem pivotResetLowerPathSum_le_num_nodes_mul_length {n : Nat}
    (Y : Fin n → Nat) (q : Nat) :
    ∀ (xs : List (Fin n)) (t : BinaryTree),
      pivotResetLowerPathSum Y q t xs ≤ (t.num_nodes : ℝ) * xs.length
| [], t => by
    simp [pivotResetLowerPathSum]
| i :: xs, t => by
    let tr := splay (splay t (Y i)) q
    have hstep_nat := search_path_len_le_num_nodes t (Y i)
    have hstep : (t.search_path_len (Y i) : ℝ) ≤ t.num_nodes := by
      exact_mod_cast hstep_nat
    have ih := pivotResetLowerPathSum_le_num_nodes_mul_length Y q xs tr
    have hnodes : tr.num_nodes = t.num_nodes := by
      unfold tr
      rw [splay_num_nodes, splay_num_nodes]
    rw [hnodes] at ih
    simp [pivotResetLowerPathSum]
    nlinarith

private theorem pivotResetPairPathSum_le_two_num_nodes_mul_length {n : Nat}
    (Y : Fin n → Nat) (q : Nat) (xs : List (Fin n)) (t : BinaryTree)
    (hbst : IsBST t)
    (hroot : rootKey t = some q)
    (hmem_left : ∀ i : Fin n, i ∈ xs → Y i ∈ (leftSubtree t).toKeyList) :
    pivotResetPairPathSum Y q t xs ≤
      2 * ((t.num_nodes : ℝ) * xs.length) := by
  have hpair :=
    pivotResetPairPathSum_le_two_lowerPathSum Y q xs t
      hbst hroot hmem_left
  have hlower := pivotResetLowerPathSum_le_num_nodes_mul_length Y q xs t
  nlinarith

private theorem pivotResetPairPathSum_right_le_two_num_nodes_mul_length
    {n : Nat}
    (Y : Fin n → Nat) (q : Nat) (xs : List (Fin n)) (t : BinaryTree)
    (hbst : IsBST t)
    (hroot : rootKey t = some q)
    (hmem_right :
      ∀ i : Fin n, i ∈ xs → Y i ∈ (rightSubtree t).toKeyList) :
    pivotResetPairPathSum Y q t xs ≤
      2 * ((t.num_nodes : ℝ) * xs.length) := by
  have hpair :=
    pivotResetPairPathSum_right_le_two_lowerPathSum Y q xs t
      hbst hroot hmem_right
  have hlower := pivotResetLowerPathSum_le_num_nodes_mul_length Y q xs t
  nlinarith

private theorem pivotResetTreeAfter_isBST {n : Nat}
    (Y : Fin n → Nat) (q : Nat) :
    ∀ (xs : List (Fin n)) (t : BinaryTree),
      IsBST t → IsBST (pivotResetTreeAfter Y q t xs)
| [], t, hbst => by
    simpa [pivotResetTreeAfter] using hbst
| i :: xs, t, hbst => by
    simp [pivotResetTreeAfter]
    exact pivotResetTreeAfter_isBST Y q xs
      (splay (splay t (Y i)) q)
      (splay_isBST (splay t (Y i)) q (splay_isBST t (Y i) hbst))

private theorem pivotResetTreeAfter_rootKey {n : Nat}
    (Y : Fin n → Nat) (q : Nat) :
    ∀ (xs : List (Fin n)) (t : BinaryTree),
      IsBST t →
      rootKey t = some q →
      rootKey (pivotResetTreeAfter Y q t xs) = some q
| [], t, _hbst, hroot => by
    simpa [pivotResetTreeAfter] using hroot
| i :: xs, t, hbst, hroot => by
    let tr := splay (splay t (Y i)) q
    have hbst_tr : IsBST tr := by
      unfold tr
      exact splay_isBST (splay t (Y i)) q (splay_isBST t (Y i) hbst)
    have hroot_tr : rootKey tr = some q := by
      unfold tr
      exact rootKey_after_pivot_reset_of_root hbst hroot
    simpa [pivotResetTreeAfter, tr] using
      pivotResetTreeAfter_rootKey Y q xs tr hbst_tr hroot_tr

private theorem pivotResetTreeAfter_toKeyList {n : Nat}
    (Y : Fin n → Nat) (q : Nat) :
    ∀ (xs : List (Fin n)) (t : BinaryTree),
      (pivotResetTreeAfter Y q t xs).toKeyList = t.toKeyList
| [], t => by
    simp [pivotResetTreeAfter]
| i :: xs, t => by
    simp [pivotResetTreeAfter,
      pivotResetTreeAfter_toKeyList Y q xs (splay (splay t (Y i)) q),
      splay_toKeyList]

private theorem pivotResetTreeAfter_mem_leftSubtree_of_lt {n : Nat}
    (Y : Fin n → Nat) (q : Nat) :
    ∀ (xs : List (Fin n)) (t : BinaryTree) (y : Nat),
      IsBST t →
      rootKey t = some q →
      y ∈ t.toKeyList →
      y < q →
      y ∈ (leftSubtree (pivotResetTreeAfter Y q t xs)).toKeyList
| [], t, y, hbst, hroot, hymem, hylt => by
    simpa [pivotResetTreeAfter] using
      mem_leftSubtree_of_root_lt_isBST hbst hroot hymem hylt
| i :: xs, t, y, hbst, hroot, hymem, hylt => by
    let tr := splay (splay t (Y i)) q
    have hbst_tr : IsBST tr := by
      unfold tr
      exact splay_isBST (splay t (Y i)) q (splay_isBST t (Y i) hbst)
    have hroot_tr : rootKey tr = some q := by
      unfold tr
      exact rootKey_after_pivot_reset_of_root hbst hroot
    have hymem_tr : y ∈ tr.toKeyList := by
      unfold tr
      rw [splay_toKeyList, splay_toKeyList]
      exact hymem
    simpa [pivotResetTreeAfter, tr] using
      pivotResetTreeAfter_mem_leftSubtree_of_lt
        Y q xs tr y hbst_tr hroot_tr hymem_tr hylt

private theorem pivotResetTreeAfter_mem_rightSubtree_of_gt {n : Nat}
    (Y : Fin n → Nat) (q : Nat) :
    ∀ (xs : List (Fin n)) (t : BinaryTree) (y : Nat),
      IsBST t →
      rootKey t = some q →
      y ∈ t.toKeyList →
      q < y →
      y ∈ (rightSubtree (pivotResetTreeAfter Y q t xs)).toKeyList
| [], t, y, hbst, hroot, hymem, hygt => by
    simpa [pivotResetTreeAfter] using
      mem_rightSubtree_of_root_gt_isBST hbst hroot hymem hygt
| i :: xs, t, y, hbst, hroot, hymem, hygt => by
    let tr := splay (splay t (Y i)) q
    have hbst_tr : IsBST tr := by
      unfold tr
      exact splay_isBST (splay t (Y i)) q (splay_isBST t (Y i) hbst)
    have hroot_tr : rootKey tr = some q := by
      unfold tr
      exact rootKey_after_pivot_reset_of_root hbst hroot
    have hymem_tr : y ∈ tr.toKeyList := by
      unfold tr
      rw [splay_toKeyList, splay_toKeyList]
      exact hymem
    simpa [pivotResetTreeAfter, tr] using
      pivotResetTreeAfter_mem_rightSubtree_of_gt
        Y q xs tr y hbst_tr hroot_tr hymem_tr hygt

private theorem splayPathSum_const_of_root {n : Nat}
    (X : Fin n → Nat) :
    ∀ (xs : List (Fin n)) (t : BinaryTree) (q : Nat),
      rootKey t = some q →
      (∀ i : Fin n, i ∈ xs → X i = q) →
      splayPathSum X t xs = xs.length
| [], t, q, _hroot, _hconst => by
    simp [splayPathSum]
| i :: xs, t, q, hroot, hconst => by
    have hxi : X i = q := hconst i (by simp)
    have htail : ∀ j : Fin n, j ∈ xs → X j = q := by
      intro j hj
      exact hconst j (by simp [hj])
    have hpath := search_path_len_eq_one_of_rootKey_eq_some hroot
    have hsplay := splay_eq_self_of_rootKey_eq_some hroot
    simp [splayPathSum, hxi, hpath, hsplay,
      splayPathSum_const_of_root X xs t q hroot htail]
    ring

private theorem splayPathSum_const_le_num_nodes_add_length {n : Nat}
    (X : Fin n → Nat) :
    ∀ (xs : List (Fin n)) (t : BinaryTree) (q : Nat),
      IsBST t → q ∈ t.toKeyList →
      (∀ i : Fin n, i ∈ xs → X i = q) →
      splayPathSum X t xs ≤ (t.num_nodes : ℝ) + xs.length
| [], t, q, _hbst, _hmem, _hconst => by
    simp [splayPathSum]
| i :: xs, t, q, hbst, hmem, hconst => by
    have hxi : X i = q := hconst i (by simp)
    have htail : ∀ j : Fin n, j ∈ xs → X j = q := by
      intro j hj
      exact hconst j (by simp [hj])
    have hroot := splay_rootKey_eq_some_of_mem_isBST t q hbst hmem
    have htail_sum :
        splayPathSum X (splay t q) xs = xs.length :=
      splayPathSum_const_of_root X xs (splay t q) q hroot htail
    have hstep_nat := search_path_len_le_num_nodes t q
    have hstep : (t.search_path_len q : ℝ) ≤ t.num_nodes := by
      exact_mod_cast hstep_nat
    simp [splayPathSum, hxi, htail_sum]
    nlinarith [show 0 ≤ (xs.length : ℝ) by positivity]

private def searchPathKeys : BinaryTree → Nat → List Nat
| .empty, _q => []
| .node l k r, q =>
    k :: if q < k then searchPathKeys l q
      else if k < q then searchPathKeys r q
      else []

private theorem searchPathKeys_length_eq_search_path_len :
    ∀ (t : BinaryTree) (q : Nat),
      (searchPathKeys t q).length = t.search_path_len q
| .empty, q => by
    simp [searchPathKeys, BinaryTree.search_path_len]
| .node l k r, q => by
    simp only [searchPathKeys, BinaryTree.search_path_len]
    by_cases hqk : q < k
    · simp [hqk, searchPathKeys_length_eq_search_path_len l q]
      omega
    · by_cases hkq : k < q
      · simp [hqk, hkq, searchPathKeys_length_eq_search_path_len r q]
        omega
      · simp [hqk, hkq]

private theorem searchPathKeys_subset_toKeyList :
    ∀ (t : BinaryTree) (q key : Nat),
      key ∈ searchPathKeys t q → key ∈ t.toKeyList
| .empty, q, key, hmem => by
    simp [searchPathKeys] at hmem
| .node l k r, q, key, hmem => by
    simp only [searchPathKeys] at hmem
    by_cases hqk : q < k
    · simp [hqk] at hmem
      rcases hmem with hkey | hmem
      · subst key
        simp [BinaryTree.toKeyList]
      · have hsub := searchPathKeys_subset_toKeyList l q key hmem
        simp [BinaryTree.toKeyList, hsub]
    · by_cases hkq : k < q
      · simp [hqk, hkq] at hmem
        rcases hmem with hkey | hmem
        · subst key
          simp [BinaryTree.toKeyList]
        · have hsub := searchPathKeys_subset_toKeyList r q key hmem
          simp [BinaryTree.toKeyList, hsub]
      · simp [hqk, hkq] at hmem
        subst key
        simp [BinaryTree.toKeyList]

private theorem searchPathKeys_rotateRight_subset_of_mem_left
    {l r : BinaryTree} {k x y key : Nat}
    (hbst : IsBST (BinaryTree.node l k r))
    (hxmem : x ∈ l.toKeyList)
    (hkey : key ∈ searchPathKeys (rotateRight (BinaryTree.node l k r)) y) :
    key ∈ searchPathKeys (BinaryTree.node l k r) x ∨
      key ∈ searchPathKeys (BinaryTree.node l k r) y := by
  cases l with
  | empty =>
      simp [BinaryTree.toKeyList] at hxmem
  | node ll lk lr =>
      cases hbst with
      | node _ _ _ hleft _hright hbst_left _hbst_right =>
          cases hbst_left with
          | node _ _ _ hll_left hlr_right _hbst_ll _hbst_lr =>
              have hx_lt_k : x < k :=
                (forallTree_iff_forall_mem.mp hleft) x
                  (by simpa [BinaryTree.toKeyList] using hxmem)
              have hlk_lt_k : lk < k :=
                (forallTree_iff_forall_mem.mp hleft) lk
                  (by simp [BinaryTree.toKeyList])
              simp only [BinaryTree.toKeyList, List.mem_append,
                List.mem_singleton] at hxmem
              rcases hxmem with (hx_ll | hx_lk) | hx_lr
              · have hx_lt_lk :=
                  (forallTree_iff_forall_mem.mp hll_left) x hx_ll
                by_cases hy_lt_lk : y < lk
                · have hy_lt_k : y < k := by omega
                  simp [rotateRight, searchPathKeys, hx_lt_k, hx_lt_lk,
                    hy_lt_lk, hy_lt_k] at hkey ⊢
                  tauto
                · by_cases hlk_lt_y : lk < y
                  · by_cases hy_lt_k : y < k
                    · simp [rotateRight, searchPathKeys, hx_lt_k, hx_lt_lk,
                        hy_lt_lk, hlk_lt_y, hy_lt_k] at hkey ⊢
                      tauto
                    · by_cases hk_lt_y : k < y
                      · simp [rotateRight, searchPathKeys, hx_lt_k, hx_lt_lk,
                          hy_lt_lk, hlk_lt_y, hy_lt_k, hk_lt_y] at hkey ⊢
                        tauto
                      · simp [rotateRight, searchPathKeys, hx_lt_k, hx_lt_lk,
                          hy_lt_lk, hlk_lt_y, hy_lt_k, hk_lt_y] at hkey ⊢
                        tauto
                  · simp [rotateRight, searchPathKeys, hx_lt_k, hx_lt_lk,
                      hy_lt_lk, hlk_lt_y] at hkey ⊢
                    tauto
              · subst x
                by_cases hy_lt_lk : y < lk
                · have hy_lt_k : y < k := by omega
                  simp [rotateRight, searchPathKeys, hlk_lt_k,
                    hy_lt_lk, hy_lt_k] at hkey ⊢
                  tauto
                · by_cases hlk_lt_y : lk < y
                  · by_cases hy_lt_k : y < k
                    · simp [rotateRight, searchPathKeys, hlk_lt_k,
                        hy_lt_lk, hlk_lt_y, hy_lt_k] at hkey ⊢
                      tauto
                    · by_cases hk_lt_y : k < y
                      · simp [rotateRight, searchPathKeys, hlk_lt_k,
                          hy_lt_lk, hlk_lt_y, hy_lt_k, hk_lt_y] at hkey ⊢
                        tauto
                      · simp [rotateRight, searchPathKeys, hlk_lt_k,
                          hy_lt_lk, hlk_lt_y, hy_lt_k, hk_lt_y] at hkey ⊢
                        tauto
                  · simp [rotateRight, searchPathKeys, hlk_lt_k,
                      hy_lt_lk, hlk_lt_y] at hkey ⊢
                    tauto
              · have hlk_lt_x :=
                  (forallTree_iff_forall_mem.mp hlr_right) x hx_lr
                have hnot_x_lt_lk : ¬ x < lk := by omega
                by_cases hy_lt_lk : y < lk
                · have hy_lt_k : y < k := by omega
                  simp [rotateRight, searchPathKeys, hx_lt_k, hnot_x_lt_lk,
                    hlk_lt_x, hy_lt_lk, hy_lt_k] at hkey ⊢
                  tauto
                · by_cases hlk_lt_y : lk < y
                  · by_cases hy_lt_k : y < k
                    · simp [rotateRight, searchPathKeys, hx_lt_k,
                        hnot_x_lt_lk, hlk_lt_x, hy_lt_lk, hlk_lt_y,
                        hy_lt_k] at hkey ⊢
                      tauto
                    · by_cases hk_lt_y : k < y
                      · simp [rotateRight, searchPathKeys, hx_lt_k,
                          hnot_x_lt_lk, hlk_lt_x, hy_lt_lk, hlk_lt_y,
                          hy_lt_k, hk_lt_y] at hkey ⊢
                        tauto
                      · simp [rotateRight, searchPathKeys, hx_lt_k,
                          hnot_x_lt_lk, hlk_lt_x, hy_lt_lk, hlk_lt_y,
                          hy_lt_k, hk_lt_y] at hkey ⊢
                        tauto
                  · simp [rotateRight, searchPathKeys, hx_lt_k,
                      hnot_x_lt_lk, hlk_lt_x, hy_lt_lk, hlk_lt_y] at hkey ⊢
                    tauto

private theorem searchPathKeys_rotateLeft_subset_of_mem_right
    {l r : BinaryTree} {k x y key : Nat}
    (hbst : IsBST (BinaryTree.node l k r))
    (hxmem : x ∈ r.toKeyList)
    (hkey : key ∈ searchPathKeys (rotateLeft (BinaryTree.node l k r)) y) :
    key ∈ searchPathKeys (BinaryTree.node l k r) x ∨
      key ∈ searchPathKeys (BinaryTree.node l k r) y := by
  cases r with
  | empty =>
      simp [BinaryTree.toKeyList] at hxmem
  | node rl rk rr =>
      cases hbst with
      | node _ _ _ _hleft hright _hbst_left hbst_right =>
          cases hbst_right with
          | node _ _ _ hrl_left hrr_right _hbst_rl _hbst_rr =>
              have hk_lt_x : k < x :=
                (forallTree_iff_forall_mem.mp hright) x
                  (by simpa [BinaryTree.toKeyList] using hxmem)
              have hk_lt_rk : k < rk :=
                (forallTree_iff_forall_mem.mp hright) rk
                  (by simp [BinaryTree.toKeyList])
              simp only [BinaryTree.toKeyList, List.mem_append,
                List.mem_singleton] at hxmem
              rcases hxmem with (hx_rl | hx_rk) | hx_rr
              · have hx_lt_rk :=
                  (forallTree_iff_forall_mem.mp hrl_left) x hx_rl
                have hnot_x_lt_k : ¬ x < k := by omega
                by_cases hy_lt_rk : y < rk
                · by_cases hy_lt_k : y < k
                  · simp [rotateLeft, searchPathKeys, hnot_x_lt_k, hk_lt_x,
                      hx_lt_rk, hy_lt_rk, hy_lt_k] at hkey ⊢
                    tauto
                  · by_cases hk_lt_y : k < y
                    · simp [rotateLeft, searchPathKeys, hnot_x_lt_k, hk_lt_x,
                        hx_lt_rk, hy_lt_rk, hy_lt_k, hk_lt_y] at hkey ⊢
                      tauto
                    · simp [rotateLeft, searchPathKeys, hnot_x_lt_k, hk_lt_x,
                        hx_lt_rk, hy_lt_rk, hy_lt_k, hk_lt_y] at hkey ⊢
                      tauto
                · by_cases hrk_lt_y : rk < y
                  · have hk_lt_y : k < y := by omega
                    have hnot_y_lt_k : ¬ y < k := by omega
                    simp [rotateLeft, searchPathKeys, hnot_x_lt_k, hk_lt_x,
                      hx_lt_rk, hy_lt_rk, hrk_lt_y, hk_lt_y,
                      hnot_y_lt_k] at hkey ⊢
                    tauto
                  · simp [rotateLeft, searchPathKeys, hnot_x_lt_k, hk_lt_x,
                      hx_lt_rk, hy_lt_rk, hrk_lt_y] at hkey ⊢
                    tauto
              · subst x
                have hnot_rk_lt_k : ¬ rk < k := by omega
                by_cases hy_lt_rk : y < rk
                · by_cases hy_lt_k : y < k
                  · simp [rotateLeft, searchPathKeys, hnot_rk_lt_k,
                      hk_lt_rk, hy_lt_rk, hy_lt_k] at hkey ⊢
                    tauto
                  · by_cases hk_lt_y : k < y
                    · simp [rotateLeft, searchPathKeys, hnot_rk_lt_k,
                        hk_lt_rk, hy_lt_rk, hy_lt_k, hk_lt_y] at hkey ⊢
                      tauto
                    · simp [rotateLeft, searchPathKeys, hnot_rk_lt_k,
                        hk_lt_rk, hy_lt_rk, hy_lt_k, hk_lt_y] at hkey ⊢
                      tauto
                · by_cases hrk_lt_y : rk < y
                  · have hk_lt_y : k < y := by omega
                    have hnot_y_lt_k : ¬ y < k := by omega
                    simp [rotateLeft, searchPathKeys, hnot_rk_lt_k,
                      hk_lt_rk, hy_lt_rk, hrk_lt_y, hk_lt_y,
                      hnot_y_lt_k] at hkey ⊢
                    tauto
                  · simp [rotateLeft, searchPathKeys, hnot_rk_lt_k,
                      hk_lt_rk, hy_lt_rk, hrk_lt_y] at hkey ⊢
                    tauto
              · have hrk_lt_x :=
                  (forallTree_iff_forall_mem.mp hrr_right) x hx_rr
                have hnot_x_lt_k : ¬ x < k := by omega
                have hnot_x_lt_rk : ¬ x < rk := by omega
                by_cases hy_lt_rk : y < rk
                · by_cases hy_lt_k : y < k
                  · simp [rotateLeft, searchPathKeys, hnot_x_lt_k,
                      hnot_x_lt_rk, hrk_lt_x, hy_lt_rk, hy_lt_k] at hkey ⊢
                    tauto
                  · by_cases hk_lt_y : k < y
                    · simp [rotateLeft, searchPathKeys, hnot_x_lt_k,
                        hnot_x_lt_rk, hrk_lt_x, hy_lt_rk, hy_lt_k,
                        hk_lt_y] at hkey ⊢
                      tauto
                    · simp [rotateLeft, searchPathKeys, hnot_x_lt_k,
                        hnot_x_lt_rk, hrk_lt_x, hy_lt_rk, hy_lt_k,
                        hk_lt_y] at hkey ⊢
                      tauto
                · by_cases hrk_lt_y : rk < y
                  · have hk_lt_y : k < y := by omega
                    have hnot_y_lt_k : ¬ y < k := by omega
                    simp [rotateLeft, searchPathKeys, hnot_x_lt_k,
                      hnot_x_lt_rk, hrk_lt_x, hy_lt_rk, hrk_lt_y,
                      hk_lt_y, hnot_y_lt_k] at hkey ⊢
                    tauto
                  · simp [rotateLeft, searchPathKeys, hnot_x_lt_k,
                      hnot_x_lt_rk, hrk_lt_x, hy_lt_rk, hrk_lt_y] at hkey ⊢
                    tauto

private theorem searchPathKeys_rotate_zig_subset_of_mem_left
    {l r : BinaryTree} {k x y key : Nat}
    (hbst : IsBST (BinaryTree.node l k r))
    (hxmem : x ∈ l.toKeyList)
    (hkey : key ∈ searchPathKeys (rotate (BinaryTree.node l k r) .zig) y) :
    key ∈ searchPathKeys (BinaryTree.node l k r) x ∨
      key ∈ searchPathKeys (BinaryTree.node l k r) y := by
  simpa [rotate] using
    (searchPathKeys_rotateRight_subset_of_mem_left
      (l := l) (r := r) (k := k) (x := x) (y := y) (key := key)
      hbst hxmem hkey)

private theorem searchPathKeys_rotate_zag_subset_of_mem_right
    {l r : BinaryTree} {k x y key : Nat}
    (hbst : IsBST (BinaryTree.node l k r))
    (hxmem : x ∈ r.toKeyList)
    (hkey : key ∈ searchPathKeys (rotate (BinaryTree.node l k r) .zag) y) :
    key ∈ searchPathKeys (BinaryTree.node l k r) x ∨
      key ∈ searchPathKeys (BinaryTree.node l k r) y := by
  simpa [rotate] using
    (searchPathKeys_rotateLeft_subset_of_mem_right
      (l := l) (r := r) (k := k) (x := x) (y := y) (key := key)
      hbst hxmem hkey)

private theorem searchPathKeys_eq_singleton_of_rootKey_eq_some
    {t : BinaryTree} {q : Nat} (hroot : rootKey t = some q) :
    searchPathKeys t q = [q] := by
  cases t with
  | empty =>
      simp [rootKey] at hroot
  | node l k r =>
      simp [rootKey] at hroot
      subst k
      simp [searchPathKeys]

private theorem mem_searchPathKeys_self_of_mem_isBST :
    ∀ (t : BinaryTree) (q : Nat), IsBST t → q ∈ t.toKeyList →
      q ∈ searchPathKeys t q
| .empty, q, _hbst, hmem => by
    simp [BinaryTree.toKeyList] at hmem
| .node l k r, q, hbst, hmem => by
    cases hbst with
    | node _ _ _ hleft hright hbst_left hbst_right =>
        simp only [BinaryTree.toKeyList, List.mem_append,
          List.mem_singleton] at hmem
        rcases hmem with (hql | hqk) | hqr
        · have hq_lt_k :=
            (forallTree_iff_forall_mem.mp hleft) q hql
          simp [searchPathKeys, hq_lt_k,
            mem_searchPathKeys_self_of_mem_isBST l q hbst_left hql]
        · subst q
          simp [searchPathKeys]
        · have hk_lt_q :=
            (forallTree_iff_forall_mem.mp hright) q hqr
          have hnot_q_lt_k : ¬ q < k := by omega
          simp [searchPathKeys, hnot_q_lt_k, hk_lt_q,
            mem_searchPathKeys_self_of_mem_isBST r q hbst_right hqr]

private theorem searchPathKeys_node_left_splay_subset_of_inner
    {ll lr r : BinaryTree} {lk k x y key : Nat}
    (hbst : IsBST (BinaryTree.node (BinaryTree.node ll lk lr) k r))
    (hxmem : x ∈ ll.toKeyList)
    (hymem : y ∈ (BinaryTree.node (BinaryTree.node ll lk lr) k r).toKeyList)
    (hinner : ∀ key, y ∈ ll.toKeyList →
      key ∈ searchPathKeys (splay ll x) y →
        key ∈ searchPathKeys ll x ∨ key ∈ searchPathKeys ll y)
    (hkey :
      key ∈ searchPathKeys
        (BinaryTree.node (BinaryTree.node (splay ll x) lk lr) k r) y) :
    key ∈ searchPathKeys (BinaryTree.node (BinaryTree.node ll lk lr) k r) x ∨
      key ∈ searchPathKeys (BinaryTree.node (BinaryTree.node ll lk lr) k r) y := by
  cases hbst with
  | node _ _ _ hleft hright hbst_left _hbst_right =>
      cases hbst_left with
      | node _ _ _ hll_left hlr_right hbst_ll _hbst_lr =>
          have hx_lt_lk :=
            (forallTree_iff_forall_mem.mp hll_left) x hxmem
          have hx_left_mem :
              x ∈ (BinaryTree.node ll lk lr).toKeyList := by
            simp [BinaryTree.toKeyList, hxmem]
          have hx_lt_k :=
            (forallTree_iff_forall_mem.mp hleft) x hx_left_mem
          by_cases hy_lt_k : y < k
          · by_cases hy_lt_lk : y < lk
            · have hyll : y ∈ ll.toKeyList := by
                simp only [BinaryTree.toKeyList, List.mem_append,
                  List.mem_singleton] at hymem ⊢
                rcases hymem with (((hyll | hylk) | hylr) | hyk) | hyr
                · exact hyll
                · omega
                · have hlk_lt_y :=
                    (forallTree_iff_forall_mem.mp hlr_right) y hylr
                  omega
                · omega
                · have hk_lt_y :=
                    (forallTree_iff_forall_mem.mp hright) y hyr
                  omega
              simp [searchPathKeys, hx_lt_k, hx_lt_lk, hy_lt_k, hy_lt_lk] at hkey ⊢
              rcases hkey with hkey | hkey | hkey
              · tauto
              · tauto
              · have hor := hinner key hyll hkey
                tauto
            · by_cases hlk_lt_y : lk < y
              · simp [searchPathKeys, hx_lt_k, hx_lt_lk, hy_lt_k, hy_lt_lk,
                  hlk_lt_y] at hkey ⊢
                tauto
              · simp [searchPathKeys, hx_lt_k, hx_lt_lk, hy_lt_k, hy_lt_lk,
                  hlk_lt_y] at hkey ⊢
                tauto
          · by_cases hk_lt_y : k < y
            · simp [searchPathKeys, hx_lt_k, hx_lt_lk, hy_lt_k, hk_lt_y] at hkey ⊢
              tauto
            · simp [searchPathKeys, hx_lt_k, hx_lt_lk, hy_lt_k, hk_lt_y] at hkey ⊢
              tauto

private theorem searchPathKeys_node_left_right_splay_subset_of_inner
    {ll lr r : BinaryTree} {lk k x y key : Nat}
    (hbst : IsBST (BinaryTree.node (BinaryTree.node ll lk lr) k r))
    (hxmem : x ∈ lr.toKeyList)
    (hymem : y ∈ (BinaryTree.node (BinaryTree.node ll lk lr) k r).toKeyList)
    (hinner : ∀ key, y ∈ lr.toKeyList →
      key ∈ searchPathKeys (splay lr x) y →
        key ∈ searchPathKeys lr x ∨ key ∈ searchPathKeys lr y)
    (hkey :
      key ∈ searchPathKeys
        (BinaryTree.node (BinaryTree.node ll lk (splay lr x)) k r) y) :
    key ∈ searchPathKeys (BinaryTree.node (BinaryTree.node ll lk lr) k r) x ∨
      key ∈ searchPathKeys (BinaryTree.node (BinaryTree.node ll lk lr) k r) y := by
  cases hbst with
  | node _ _ _ hleft hright hbst_left _hbst_right =>
      cases hbst_left with
      | node _ _ _ hll_left hlr_right _hbst_ll hbst_lr =>
          have hlk_lt_x :=
            (forallTree_iff_forall_mem.mp hlr_right) x hxmem
          have hx_left_mem :
              x ∈ (BinaryTree.node ll lk lr).toKeyList := by
            simp [BinaryTree.toKeyList, hxmem]
          have hx_lt_k :=
            (forallTree_iff_forall_mem.mp hleft) x hx_left_mem
          have hnot_x_lt_lk : ¬ x < lk := by omega
          by_cases hy_lt_k : y < k
          · by_cases hy_lt_lk : y < lk
            · simp [searchPathKeys, hx_lt_k, hnot_x_lt_lk, hlk_lt_x,
                hy_lt_k, hy_lt_lk] at hkey ⊢
              tauto
            · by_cases hlk_lt_y : lk < y
              · have hylr : y ∈ lr.toKeyList := by
                  simp only [BinaryTree.toKeyList, List.mem_append,
                    List.mem_singleton] at hymem ⊢
                  rcases hymem with (((hyll | hylk) | hylr) | hyk) | hyr
                  · have hy_lt_lk' :=
                      (forallTree_iff_forall_mem.mp hll_left) y hyll
                    omega
                  · omega
                  · exact hylr
                  · omega
                  · have hk_lt_y :=
                      (forallTree_iff_forall_mem.mp hright) y hyr
                    omega
                simp [searchPathKeys, hx_lt_k, hnot_x_lt_lk, hlk_lt_x,
                  hy_lt_k, hy_lt_lk, hlk_lt_y] at hkey ⊢
                rcases hkey with hkey | hkey | hkey
                · tauto
                · tauto
                · have hor := hinner key hylr hkey
                  tauto
              · simp [searchPathKeys, hx_lt_k, hnot_x_lt_lk, hlk_lt_x,
                  hy_lt_k, hy_lt_lk, hlk_lt_y] at hkey ⊢
                tauto
          · by_cases hk_lt_y : k < y
            · simp [searchPathKeys, hx_lt_k, hnot_x_lt_lk, hlk_lt_x,
                hy_lt_k, hk_lt_y] at hkey ⊢
              tauto
            · simp [searchPathKeys, hx_lt_k, hnot_x_lt_lk, hlk_lt_x,
                hy_lt_k, hk_lt_y] at hkey ⊢
              tauto

private theorem searchPathKeys_node_left_rotateLeft_subset_of_mem_right
    {ll lr r : BinaryTree} {lk k x y key : Nat}
    (hbst : IsBST (BinaryTree.node (BinaryTree.node ll lk lr) k r))
    (hxmem : x ∈ lr.toKeyList)
    (hkey :
      key ∈ searchPathKeys
        (BinaryTree.node (rotateLeft (BinaryTree.node ll lk lr)) k r) y) :
    key ∈ searchPathKeys (BinaryTree.node (BinaryTree.node ll lk lr) k r) x ∨
      key ∈ searchPathKeys (BinaryTree.node (BinaryTree.node ll lk lr) k r) y := by
  cases hbst with
  | node _ _ _ hleft hright hbst_left _hbst_right =>
      cases hbst_left with
      | node _ _ _ hll_left hlr_right _hbst_ll _hbst_lr =>
          have hbst_left_old : IsBST (BinaryTree.node ll lk lr) :=
            IsBST.node lk ll lr hll_left hlr_right _hbst_ll _hbst_lr
          have hlk_lt_x :=
            (forallTree_iff_forall_mem.mp hlr_right) x hxmem
          have hx_left_mem :
              x ∈ (BinaryTree.node ll lk lr).toKeyList := by
            simp [BinaryTree.toKeyList, hxmem]
          have hx_lt_k :=
            (forallTree_iff_forall_mem.mp hleft) x hx_left_mem
          have hnot_x_lt_lk : ¬ x < lk := by omega
          by_cases hy_lt_k : y < k
          · simp [searchPathKeys, hx_lt_k, hnot_x_lt_lk, hlk_lt_x,
              hy_lt_k] at hkey ⊢
            rcases hkey with hkey | hkey
            · tauto
            · have hrot :=
                searchPathKeys_rotateLeft_subset_of_mem_right
                  (l := ll) (r := lr) (k := lk)
                  (x := x) (y := y) (key := key)
                  hbst_left_old hxmem hkey
              rcases hrot with hx_path | hy_path
              · simp [searchPathKeys, hnot_x_lt_lk, hlk_lt_x] at hx_path ⊢
                tauto
              · by_cases hy_lt_lk : y < lk
                · simp [searchPathKeys, hy_lt_lk] at hy_path ⊢
                  tauto
                · by_cases hlk_lt_y : lk < y
                  · simp [searchPathKeys, hy_lt_lk, hlk_lt_y] at hy_path ⊢
                    tauto
                  · simp [searchPathKeys, hy_lt_lk, hlk_lt_y] at hy_path ⊢
                    tauto
          · by_cases hk_lt_y : k < y
            · simp [searchPathKeys, hx_lt_k, hnot_x_lt_lk, hlk_lt_x,
                hy_lt_k, hk_lt_y] at hkey ⊢
              tauto
            · simp [searchPathKeys, hx_lt_k, hnot_x_lt_lk, hlk_lt_x,
                hy_lt_k, hk_lt_y] at hkey ⊢
              tauto

private theorem searchPathKeys_node_right_right_splay_subset_of_inner
    {l rl rr : BinaryTree} {k rk x y key : Nat}
    (hbst : IsBST (BinaryTree.node l k (BinaryTree.node rl rk rr)))
    (hxmem : x ∈ rr.toKeyList)
    (hymem : y ∈ (BinaryTree.node l k (BinaryTree.node rl rk rr)).toKeyList)
    (hinner : ∀ key, y ∈ rr.toKeyList →
      key ∈ searchPathKeys (splay rr x) y →
        key ∈ searchPathKeys rr x ∨ key ∈ searchPathKeys rr y)
    (hkey :
      key ∈ searchPathKeys
        (BinaryTree.node l k (BinaryTree.node rl rk (splay rr x))) y) :
    key ∈ searchPathKeys (BinaryTree.node l k (BinaryTree.node rl rk rr)) x ∨
      key ∈ searchPathKeys (BinaryTree.node l k (BinaryTree.node rl rk rr)) y := by
  cases hbst with
  | node _ _ _ hleft hright _hbst_left hbst_right =>
      cases hbst_right with
      | node _ _ _ hrl_left hrr_right _hbst_rl hbst_rr =>
          have hrk_lt_x :=
            (forallTree_iff_forall_mem.mp hrr_right) x hxmem
          have hx_right_mem :
              x ∈ (BinaryTree.node rl rk rr).toKeyList := by
            simp [BinaryTree.toKeyList, hxmem]
          have hk_lt_x :=
            (forallTree_iff_forall_mem.mp hright) x hx_right_mem
          have hnot_x_lt_k : ¬ x < k := by omega
          have hnot_x_lt_rk : ¬ x < rk := by omega
          by_cases hy_lt_k : y < k
          · simp [searchPathKeys, hnot_x_lt_k, hk_lt_x, hnot_x_lt_rk,
              hrk_lt_x, hy_lt_k] at hkey ⊢
            tauto
          · by_cases hk_lt_y : k < y
            · by_cases hy_lt_rk : y < rk
              · simp [searchPathKeys, hnot_x_lt_k, hk_lt_x, hnot_x_lt_rk,
                  hrk_lt_x, hy_lt_k, hk_lt_y, hy_lt_rk] at hkey ⊢
                tauto
              · by_cases hrk_lt_y : rk < y
                · have hyrr : y ∈ rr.toKeyList := by
                    simp only [BinaryTree.toKeyList, List.mem_append,
                      List.mem_singleton] at hymem ⊢
                    rcases hymem with (hyl | hyk) | ((hyrl | hyrk) | hyrr)
                    · have hy_lt_k' :=
                        (forallTree_iff_forall_mem.mp hleft) y hyl
                      omega
                    · omega
                    · have hy_lt_rk' :=
                        (forallTree_iff_forall_mem.mp hrl_left) y hyrl
                      omega
                    · omega
                    · exact hyrr
                  simp [searchPathKeys, hnot_x_lt_k, hk_lt_x, hnot_x_lt_rk,
                    hrk_lt_x, hy_lt_k, hk_lt_y, hy_lt_rk, hrk_lt_y] at hkey ⊢
                  rcases hkey with hkey | hkey | hkey
                  · tauto
                  · tauto
                  · have hor := hinner key hyrr hkey
                    tauto
                · simp [searchPathKeys, hnot_x_lt_k, hk_lt_x, hnot_x_lt_rk,
                    hrk_lt_x, hy_lt_k, hk_lt_y, hy_lt_rk, hrk_lt_y] at hkey ⊢
                  tauto
            · simp [searchPathKeys, hnot_x_lt_k, hk_lt_x, hnot_x_lt_rk,
                hrk_lt_x, hy_lt_k, hk_lt_y] at hkey ⊢
              tauto

private theorem searchPathKeys_node_right_left_splay_subset_of_inner
    {l rl rr : BinaryTree} {k rk x y key : Nat}
    (hbst : IsBST (BinaryTree.node l k (BinaryTree.node rl rk rr)))
    (hxmem : x ∈ rl.toKeyList)
    (hymem : y ∈ (BinaryTree.node l k (BinaryTree.node rl rk rr)).toKeyList)
    (hinner : ∀ key, y ∈ rl.toKeyList →
      key ∈ searchPathKeys (splay rl x) y →
        key ∈ searchPathKeys rl x ∨ key ∈ searchPathKeys rl y)
    (hkey :
      key ∈ searchPathKeys
        (BinaryTree.node l k (BinaryTree.node (splay rl x) rk rr)) y) :
    key ∈ searchPathKeys (BinaryTree.node l k (BinaryTree.node rl rk rr)) x ∨
      key ∈ searchPathKeys (BinaryTree.node l k (BinaryTree.node rl rk rr)) y := by
  cases hbst with
  | node _ _ _ hleft hright _hbst_left hbst_right =>
      cases hbst_right with
      | node _ _ _ hrl_left hrr_right hbst_rl _hbst_rr =>
          have hx_lt_rk :=
            (forallTree_iff_forall_mem.mp hrl_left) x hxmem
          have hx_right_mem :
              x ∈ (BinaryTree.node rl rk rr).toKeyList := by
            simp [BinaryTree.toKeyList, hxmem]
          have hk_lt_x :=
            (forallTree_iff_forall_mem.mp hright) x hx_right_mem
          have hnot_x_lt_k : ¬ x < k := by omega
          by_cases hy_lt_k : y < k
          · simp [searchPathKeys, hnot_x_lt_k, hk_lt_x, hx_lt_rk,
              hy_lt_k] at hkey ⊢
            tauto
          · by_cases hk_lt_y : k < y
            · by_cases hy_lt_rk : y < rk
              · have hyrl : y ∈ rl.toKeyList := by
                  simp only [BinaryTree.toKeyList, List.mem_append,
                    List.mem_singleton] at hymem ⊢
                  rcases hymem with (hyl | hyk) | ((hyrl | hyrk) | hyrr)
                  · have hy_lt_k' :=
                      (forallTree_iff_forall_mem.mp hleft) y hyl
                    omega
                  · omega
                  · exact hyrl
                  · omega
                  · have hrk_lt_y :=
                      (forallTree_iff_forall_mem.mp hrr_right) y hyrr
                    omega
                simp [searchPathKeys, hnot_x_lt_k, hk_lt_x, hx_lt_rk,
                  hy_lt_k, hk_lt_y, hy_lt_rk] at hkey ⊢
                rcases hkey with hkey | hkey | hkey
                · tauto
                · tauto
                · have hor := hinner key hyrl hkey
                  tauto
              · by_cases hrk_lt_y : rk < y
                · simp [searchPathKeys, hnot_x_lt_k, hk_lt_x, hx_lt_rk,
                    hy_lt_k, hk_lt_y, hy_lt_rk, hrk_lt_y] at hkey ⊢
                  tauto
                · simp [searchPathKeys, hnot_x_lt_k, hk_lt_x, hx_lt_rk,
                    hy_lt_k, hk_lt_y, hy_lt_rk, hrk_lt_y] at hkey ⊢
                  tauto
            · simp [searchPathKeys, hnot_x_lt_k, hk_lt_x, hx_lt_rk,
                hy_lt_k, hk_lt_y] at hkey ⊢
              tauto

private theorem searchPathKeys_node_right_rotateRight_subset_of_mem_left
    {l rl rr : BinaryTree} {k rk x y key : Nat}
    (hbst : IsBST (BinaryTree.node l k (BinaryTree.node rl rk rr)))
    (hxmem : x ∈ rl.toKeyList)
    (hkey :
      key ∈ searchPathKeys
        (BinaryTree.node l k (rotateRight (BinaryTree.node rl rk rr))) y) :
    key ∈ searchPathKeys (BinaryTree.node l k (BinaryTree.node rl rk rr)) x ∨
      key ∈ searchPathKeys (BinaryTree.node l k (BinaryTree.node rl rk rr)) y := by
  cases hbst with
  | node _ _ _ hleft hright _hbst_left hbst_right =>
      cases hbst_right with
      | node _ _ _ hrl_left hrr_right hbst_rl _hbst_rr =>
          have hbst_right_old : IsBST (BinaryTree.node rl rk rr) :=
            IsBST.node rk rl rr hrl_left hrr_right hbst_rl _hbst_rr
          have hx_lt_rk :=
            (forallTree_iff_forall_mem.mp hrl_left) x hxmem
          have hx_right_mem :
              x ∈ (BinaryTree.node rl rk rr).toKeyList := by
            simp [BinaryTree.toKeyList, hxmem]
          have hk_lt_x :=
            (forallTree_iff_forall_mem.mp hright) x hx_right_mem
          have hnot_x_lt_k : ¬ x < k := by omega
          by_cases hy_lt_k : y < k
          · simp [searchPathKeys, hnot_x_lt_k, hk_lt_x, hx_lt_rk,
              hy_lt_k] at hkey ⊢
            tauto
          · by_cases hk_lt_y : k < y
            · simp [searchPathKeys, hnot_x_lt_k, hk_lt_x, hx_lt_rk,
                hy_lt_k, hk_lt_y] at hkey ⊢
              rcases hkey with hkey | hkey
              · tauto
              · have hrot :=
                  searchPathKeys_rotateRight_subset_of_mem_left
                    (l := rl) (r := rr) (k := rk)
                    (x := x) (y := y) (key := key)
                    hbst_right_old hxmem hkey
                rcases hrot with hx_path | hy_path
                · simp [searchPathKeys, hx_lt_rk] at hx_path ⊢
                  tauto
                · by_cases hy_lt_rk : y < rk
                  · simp [searchPathKeys, hy_lt_rk] at hy_path ⊢
                    tauto
                  · by_cases hrk_lt_y : rk < y
                    · simp [searchPathKeys, hy_lt_rk, hrk_lt_y] at hy_path ⊢
                      tauto
                    · simp [searchPathKeys, hy_lt_rk, hrk_lt_y] at hy_path ⊢
                      tauto
            · simp [searchPathKeys, hnot_x_lt_k, hk_lt_x, hx_lt_rk,
                hy_lt_k, hk_lt_y] at hkey ⊢
              tauto

private theorem searchPathKeys_zigZig_subset_of_inner
    {ll lr r : BinaryTree} {lk k x y key : Nat}
    (hbst : IsBST (BinaryTree.node (BinaryTree.node ll lk lr) k r))
    (hxmem : x ∈ ll.toKeyList)
    (hymem : y ∈ (BinaryTree.node (BinaryTree.node ll lk lr) k r).toKeyList)
    (hinner : ∀ z key, z ∈ ll.toKeyList →
      key ∈ searchPathKeys (splay ll x) z →
        key ∈ searchPathKeys ll x ∨ key ∈ searchPathKeys ll z)
    (hkey :
      key ∈ searchPathKeys
        (rotate
          (BinaryTree.node (BinaryTree.node (splay ll x) lk lr) k r)
          .zigZig) y) :
    key ∈ searchPathKeys (BinaryTree.node (BinaryTree.node ll lk lr) k r) x ∨
      key ∈ searchPathKeys (BinaryTree.node (BinaryTree.node ll lk lr) k r) y := by
  cases hbst with
  | node _ _ _ hleft hright hbst_left hbst_right =>
      cases hbst_left with
      | node _ _ _ hll_left hlr_right hbst_ll hbst_lr =>
          have hbst_s_ll : IsBST (splay ll x) :=
            splay_isBST ll x hbst_ll
          have hll_left_s :
              ForallTree (fun a => a < lk) (splay ll x) := by
            rw [forallTree_iff_forall_mem]
            intro a ha
            have ha_old : a ∈ ll.toKeyList := by
              simpa [splay_toKeyList] using ha
            exact (forallTree_iff_forall_mem.mp hll_left) a ha_old
          have hleft_new :
              ForallTree (fun a => a < k)
                (BinaryTree.node (splay ll x) lk lr) := by
            rw [forallTree_iff_forall_mem]
            intro a ha
            have ha_old :
                a ∈ (BinaryTree.node ll lk lr).toKeyList := by
              simpa [BinaryTree.toKeyList, splay_toKeyList] using ha
            exact (forallTree_iff_forall_mem.mp hleft) a ha_old
          have hbst_left_new :
              IsBST (BinaryTree.node (splay ll x) lk lr) :=
            IsBST.node lk (splay ll x) lr
              hll_left_s hlr_right hbst_s_ll hbst_lr
          have hbst_new :
              IsBST
                (BinaryTree.node
                  (BinaryTree.node (splay ll x) lk lr) k r) :=
            IsBST.node k (BinaryTree.node (splay ll x) lk lr) r
              hleft_new hright hbst_left_new hbst_right
          have hbst_after_first :
              IsBST
                (BinaryTree.node (splay ll x) lk
                  (BinaryTree.node lr k r)) := by
            simpa [rotateRight] using rotateRight_isBST hbst_new
          have hxmem_s : x ∈ (splay ll x).toKeyList := by
            simpa [splay_toKeyList] using hxmem
          have hxmem_new_left :
              x ∈ (BinaryTree.node (splay ll x) lk lr).toKeyList := by
            simp [BinaryTree.toKeyList, hxmem_s]
          have hkey_after_second :
              key ∈ searchPathKeys
                (rotateRight
                  (BinaryTree.node (splay ll x) lk
                    (BinaryTree.node lr k r))) y := by
            simpa [rotate, rotateRight] using hkey
          have hsecond :=
            searchPathKeys_rotateRight_subset_of_mem_left
              (l := splay ll x) (r := BinaryTree.node lr k r)
              (k := lk) (x := x) (y := y) (key := key)
              hbst_after_first hxmem_s hkey_after_second
          have hxmem_old :
              x ∈ (BinaryTree.node (BinaryTree.node ll lk lr) k r).toKeyList := by
            simp [BinaryTree.toKeyList, hxmem]
          have hbst_left_old : IsBST (BinaryTree.node ll lk lr) :=
            IsBST.node lk ll lr hll_left hlr_right hbst_ll hbst_lr
          have hbst_old :
              IsBST (BinaryTree.node (BinaryTree.node ll lk lr) k r) :=
            IsBST.node k (BinaryTree.node ll lk lr) r
              hleft hright hbst_left_old hbst_right
          let Tnew :=
            BinaryTree.node (BinaryTree.node (splay ll x) lk lr) k r
          have replace_x :
              ∀ key,
                key ∈ searchPathKeys Tnew x →
                  key ∈ searchPathKeys
                    (BinaryTree.node (BinaryTree.node ll lk lr) k r) x ∨
                    key ∈ searchPathKeys
                      (BinaryTree.node (BinaryTree.node ll lk lr) k r) x := by
            intro key hkey_x
            exact searchPathKeys_node_left_splay_subset_of_inner
              (ll := ll) (lr := lr) (r := r) (lk := lk) (k := k)
              (x := x) (y := x) (key := key)
              hbst_old hxmem
              hxmem_old (fun key hx_in_ll hkey_inner =>
                hinner x key hx_in_ll hkey_inner) hkey_x
          have replace_y :
              ∀ key,
                key ∈ searchPathKeys Tnew y →
                  key ∈ searchPathKeys
                    (BinaryTree.node (BinaryTree.node ll lk lr) k r) x ∨
                    key ∈ searchPathKeys
                      (BinaryTree.node (BinaryTree.node ll lk lr) k r) y := by
            intro key hkey_y
            exact searchPathKeys_node_left_splay_subset_of_inner
              (ll := ll) (lr := lr) (r := r) (lk := lk) (k := k)
              (x := x) (y := y) (key := key)
              hbst_old hxmem
              hymem (fun key hy_in_ll hkey_inner =>
                hinner y key hy_in_ll hkey_inner) hkey_y
          rcases hsecond with hmid_x | hmid_y
          · have hmid_x_first :
                key ∈ searchPathKeys
                  (rotateRight
                    (BinaryTree.node
                      (BinaryTree.node (splay ll x) lk lr) k r)) x := by
              simpa [Tnew, rotateRight] using hmid_x
            have hfirst :=
              searchPathKeys_rotateRight_subset_of_mem_left
                (l := BinaryTree.node (splay ll x) lk lr) (r := r)
                (k := k) (x := x) (y := x) (key := key)
                hbst_new hxmem_new_left hmid_x_first
            rcases hfirst with htnew_x | htnew_x
            · rcases replace_x key htnew_x with h_old_x | h_old_x
              · exact Or.inl h_old_x
              · exact Or.inl h_old_x
            · rcases replace_x key htnew_x with h_old_x | h_old_x
              · exact Or.inl h_old_x
              · exact Or.inl h_old_x
          · have hmid_y_first :
                key ∈ searchPathKeys
                  (rotateRight
                    (BinaryTree.node
                      (BinaryTree.node (splay ll x) lk lr) k r)) y := by
              simpa [Tnew, rotateRight] using hmid_y
            have hfirst :=
              searchPathKeys_rotateRight_subset_of_mem_left
                (l := BinaryTree.node (splay ll x) lk lr) (r := r)
                (k := k) (x := x) (y := y) (key := key)
                hbst_new hxmem_new_left hmid_y_first
            rcases hfirst with htnew_x | htnew_y
            · rcases replace_x key htnew_x with h_old_x | h_old_x
              · exact Or.inl h_old_x
              · exact Or.inl h_old_x
            · exact replace_y key htnew_y

private theorem searchPathKeys_zigZag_subset_of_inner
    {ll lr r : BinaryTree} {lk k x y key : Nat}
    (hbst : IsBST (BinaryTree.node (BinaryTree.node ll lk lr) k r))
    (hxmem : x ∈ lr.toKeyList)
    (hymem : y ∈ (BinaryTree.node (BinaryTree.node ll lk lr) k r).toKeyList)
    (hinner : ∀ z key, z ∈ lr.toKeyList →
      key ∈ searchPathKeys (splay lr x) z →
        key ∈ searchPathKeys lr x ∨ key ∈ searchPathKeys lr z)
    (hkey :
      key ∈ searchPathKeys
        (rotate
          (BinaryTree.node (BinaryTree.node ll lk (splay lr x)) k r)
          .zigZag) y) :
    key ∈ searchPathKeys (BinaryTree.node (BinaryTree.node ll lk lr) k r) x ∨
      key ∈ searchPathKeys (BinaryTree.node (BinaryTree.node ll lk lr) k r) y := by
  cases hbst with
  | node _ _ _ hleft hright hbst_left hbst_right =>
      cases hbst_left with
      | node _ _ _ hll_left hlr_right hbst_ll hbst_lr =>
          have hbst_s_lr : IsBST (splay lr x) :=
            splay_isBST lr x hbst_lr
          have hlr_right_s :
              ForallTree (fun a => lk < a) (splay lr x) := by
            rw [forallTree_iff_forall_mem]
            intro a ha
            have ha_old : a ∈ lr.toKeyList := by
              simpa [splay_toKeyList] using ha
            exact (forallTree_iff_forall_mem.mp hlr_right) a ha_old
          have hleft_new :
              ForallTree (fun a => a < k)
                (BinaryTree.node ll lk (splay lr x)) := by
            rw [forallTree_iff_forall_mem]
            intro a ha
            have ha_old :
                a ∈ (BinaryTree.node ll lk lr).toKeyList := by
              simpa [BinaryTree.toKeyList, splay_toKeyList] using ha
            exact (forallTree_iff_forall_mem.mp hleft) a ha_old
          have hbst_left_new :
              IsBST (BinaryTree.node ll lk (splay lr x)) :=
            IsBST.node lk ll (splay lr x)
              hll_left hlr_right_s hbst_ll hbst_s_lr
          have hbst_new :
              IsBST
                (BinaryTree.node
                  (BinaryTree.node ll lk (splay lr x)) k r) :=
            IsBST.node k (BinaryTree.node ll lk (splay lr x)) r
              hleft_new hright hbst_left_new hbst_right
          let Lnew := BinaryTree.node ll lk (splay lr x)
          have hleft_rot :
              ForallTree (fun a => a < k) (rotateLeft Lnew) := by
            rw [forallTree_iff_forall_mem]
            intro a ha
            have ha_new : a ∈ Lnew.toKeyList := by
              simpa [Lnew, rotateLeft_toKeyList] using ha
            exact (forallTree_iff_forall_mem.mp hleft_new) a ha_new
          have hbst_left_rot : IsBST (rotateLeft Lnew) := by
            exact rotateLeft_isBST hbst_left_new
          have hbst_after_inner :
              IsBST (BinaryTree.node (rotateLeft Lnew) k r) :=
            IsBST.node k (rotateLeft Lnew) r
              hleft_rot hright hbst_left_rot hbst_right
          have hxmem_s : x ∈ (splay lr x).toKeyList := by
            simpa [splay_toKeyList] using hxmem
          have hxmem_lnew_right :
              x ∈ (splay lr x).toKeyList := hxmem_s
          have hxmem_lnew :
              x ∈ Lnew.toKeyList := by
            simp [Lnew, BinaryTree.toKeyList, hxmem_s]
          have hxmem_leftrot : x ∈ (rotateLeft Lnew).toKeyList := by
            simpa [Lnew, rotateLeft_toKeyList] using hxmem_lnew
          have hkey_outer :
              key ∈ searchPathKeys
                (rotateRight (BinaryTree.node (rotateLeft Lnew) k r)) y := by
            simpa [rotate, Lnew] using hkey
          have houter :=
            searchPathKeys_rotateRight_subset_of_mem_left
              (l := rotateLeft Lnew) (r := r) (k := k)
              (x := x) (y := y) (key := key)
              hbst_after_inner hxmem_leftrot hkey_outer
          have hxmem_old :
              x ∈ (BinaryTree.node (BinaryTree.node ll lk lr) k r).toKeyList := by
            simp [BinaryTree.toKeyList, hxmem]
          have hbst_left_old : IsBST (BinaryTree.node ll lk lr) :=
            IsBST.node lk ll lr hll_left hlr_right hbst_ll hbst_lr
          have hbst_old :
              IsBST (BinaryTree.node (BinaryTree.node ll lk lr) k r) :=
            IsBST.node k (BinaryTree.node ll lk lr) r
              hleft hright hbst_left_old hbst_right
          let Tnew := BinaryTree.node Lnew k r
          have replace_x :
              ∀ key,
                key ∈ searchPathKeys Tnew x →
                  key ∈ searchPathKeys
                    (BinaryTree.node (BinaryTree.node ll lk lr) k r) x ∨
                    key ∈ searchPathKeys
                      (BinaryTree.node (BinaryTree.node ll lk lr) k r) x := by
            intro key hkey_x
            exact searchPathKeys_node_left_right_splay_subset_of_inner
              (ll := ll) (lr := lr) (r := r) (lk := lk) (k := k)
              (x := x) (y := x) (key := key)
              hbst_old hxmem hxmem_old
              (fun key hx_in_lr hkey_inner =>
                hinner x key hx_in_lr hkey_inner)
              (by simpa [Tnew, Lnew] using hkey_x)
          have replace_y :
              ∀ key,
                key ∈ searchPathKeys Tnew y →
                  key ∈ searchPathKeys
                    (BinaryTree.node (BinaryTree.node ll lk lr) k r) x ∨
                    key ∈ searchPathKeys
                      (BinaryTree.node (BinaryTree.node ll lk lr) k r) y := by
            intro key hkey_y
            exact searchPathKeys_node_left_right_splay_subset_of_inner
              (ll := ll) (lr := lr) (r := r) (lk := lk) (k := k)
              (x := x) (y := y) (key := key)
              hbst_old hxmem hymem
              (fun key hy_in_lr hkey_inner =>
                hinner y key hy_in_lr hkey_inner)
              (by simpa [Tnew, Lnew] using hkey_y)
          have inner_lift :
              ∀ z key,
                key ∈ searchPathKeys (BinaryTree.node (rotateLeft Lnew) k r) z →
                  key ∈ searchPathKeys Tnew x ∨
                    key ∈ searchPathKeys Tnew z := by
            intro z key hpath
            have hrot :=
              searchPathKeys_node_left_rotateLeft_subset_of_mem_right
                (ll := ll) (lr := splay lr x) (r := r)
                (lk := lk) (k := k) (x := x) (y := z) (key := key)
                (by simpa [Tnew, Lnew] using hbst_new)
                hxmem_lnew_right
                (by simpa [Tnew, Lnew] using hpath)
            simpa [Tnew, Lnew] using hrot
          rcases houter with hmid_x | hmid_y
          · rcases inner_lift x key hmid_x with htnew_x | htnew_x
            · rcases replace_x key htnew_x with h_old_x | h_old_x
              · exact Or.inl h_old_x
              · exact Or.inl h_old_x
            · rcases replace_x key htnew_x with h_old_x | h_old_x
              · exact Or.inl h_old_x
              · exact Or.inl h_old_x
          · rcases inner_lift y key hmid_y with htnew_x | htnew_y
            · rcases replace_x key htnew_x with h_old_x | h_old_x
              · exact Or.inl h_old_x
              · exact Or.inl h_old_x
            · exact replace_y key htnew_y

private theorem searchPathKeys_zagZag_subset_of_inner
    {l rl rr : BinaryTree} {k rk x y key : Nat}
    (hbst : IsBST (BinaryTree.node l k (BinaryTree.node rl rk rr)))
    (hxmem : x ∈ rr.toKeyList)
    (hymem : y ∈ (BinaryTree.node l k (BinaryTree.node rl rk rr)).toKeyList)
    (hinner : ∀ z key, z ∈ rr.toKeyList →
      key ∈ searchPathKeys (splay rr x) z →
        key ∈ searchPathKeys rr x ∨ key ∈ searchPathKeys rr z)
    (hkey :
      key ∈ searchPathKeys
        (rotate
          (BinaryTree.node l k (BinaryTree.node rl rk (splay rr x)))
          .zagZag) y) :
    key ∈ searchPathKeys (BinaryTree.node l k (BinaryTree.node rl rk rr)) x ∨
      key ∈ searchPathKeys (BinaryTree.node l k (BinaryTree.node rl rk rr)) y := by
  cases hbst with
  | node _ _ _ hleft hright hbst_left hbst_right =>
      cases hbst_right with
      | node _ _ _ hrl_left hrr_right hbst_rl hbst_rr =>
          have hbst_s_rr : IsBST (splay rr x) :=
            splay_isBST rr x hbst_rr
          have hrr_right_s :
              ForallTree (fun a => rk < a) (splay rr x) := by
            rw [forallTree_iff_forall_mem]
            intro a ha
            have ha_old : a ∈ rr.toKeyList := by
              simpa [splay_toKeyList] using ha
            exact (forallTree_iff_forall_mem.mp hrr_right) a ha_old
          have hright_new :
              ForallTree (fun a => k < a)
                (BinaryTree.node rl rk (splay rr x)) := by
            rw [forallTree_iff_forall_mem]
            intro a ha
            have ha_old :
                a ∈ (BinaryTree.node rl rk rr).toKeyList := by
              simpa [BinaryTree.toKeyList, splay_toKeyList] using ha
            exact (forallTree_iff_forall_mem.mp hright) a ha_old
          have hbst_right_new :
              IsBST (BinaryTree.node rl rk (splay rr x)) :=
            IsBST.node rk rl (splay rr x)
              hrl_left hrr_right_s hbst_rl hbst_s_rr
          have hbst_new :
              IsBST
                (BinaryTree.node l k
                  (BinaryTree.node rl rk (splay rr x))) :=
            IsBST.node k l (BinaryTree.node rl rk (splay rr x))
              hleft hright_new hbst_left hbst_right_new
          have hbst_after_first :
              IsBST
                (BinaryTree.node
                  (BinaryTree.node l k rl) rk (splay rr x)) := by
            simpa [rotateLeft] using rotateLeft_isBST hbst_new
          have hxmem_s : x ∈ (splay rr x).toKeyList := by
            simpa [splay_toKeyList] using hxmem
          have hxmem_new_right :
              x ∈ (BinaryTree.node rl rk (splay rr x)).toKeyList := by
            simp [BinaryTree.toKeyList, hxmem_s]
          have hkey_after_second :
              key ∈ searchPathKeys
                (rotateLeft
                  (BinaryTree.node
                    (BinaryTree.node l k rl) rk (splay rr x))) y := by
            simpa [rotate, rotateLeft] using hkey
          have hsecond :=
            searchPathKeys_rotateLeft_subset_of_mem_right
              (l := BinaryTree.node l k rl) (r := splay rr x)
              (k := rk) (x := x) (y := y) (key := key)
              hbst_after_first hxmem_s hkey_after_second
          have hxmem_old :
              x ∈ (BinaryTree.node l k (BinaryTree.node rl rk rr)).toKeyList := by
            simp [BinaryTree.toKeyList, hxmem]
          have hbst_right_old : IsBST (BinaryTree.node rl rk rr) :=
            IsBST.node rk rl rr hrl_left hrr_right hbst_rl hbst_rr
          have hbst_old :
              IsBST (BinaryTree.node l k (BinaryTree.node rl rk rr)) :=
            IsBST.node k l (BinaryTree.node rl rk rr)
              hleft hright hbst_left hbst_right_old
          let Tnew := BinaryTree.node l k (BinaryTree.node rl rk (splay rr x))
          have replace_x :
              ∀ key,
                key ∈ searchPathKeys Tnew x →
                  key ∈ searchPathKeys
                    (BinaryTree.node l k (BinaryTree.node rl rk rr)) x ∨
                    key ∈ searchPathKeys
                      (BinaryTree.node l k (BinaryTree.node rl rk rr)) x := by
            intro key hkey_x
            exact searchPathKeys_node_right_right_splay_subset_of_inner
              (l := l) (rl := rl) (rr := rr) (k := k) (rk := rk)
              (x := x) (y := x) (key := key)
              hbst_old hxmem hxmem_old
              (fun key hx_in_rr hkey_inner =>
                hinner x key hx_in_rr hkey_inner)
              (by simpa [Tnew] using hkey_x)
          have replace_y :
              ∀ key,
                key ∈ searchPathKeys Tnew y →
                  key ∈ searchPathKeys
                    (BinaryTree.node l k (BinaryTree.node rl rk rr)) x ∨
                    key ∈ searchPathKeys
                      (BinaryTree.node l k (BinaryTree.node rl rk rr)) y := by
            intro key hkey_y
            exact searchPathKeys_node_right_right_splay_subset_of_inner
              (l := l) (rl := rl) (rr := rr) (k := k) (rk := rk)
              (x := x) (y := y) (key := key)
              hbst_old hxmem hymem
              (fun key hy_in_rr hkey_inner =>
                hinner y key hy_in_rr hkey_inner)
              (by simpa [Tnew] using hkey_y)
          rcases hsecond with hmid_x | hmid_y
          · have hmid_x_first :
                key ∈ searchPathKeys
                  (rotateLeft
                    (BinaryTree.node l k
                      (BinaryTree.node rl rk (splay rr x)))) x := by
              simpa [Tnew, rotateLeft] using hmid_x
            have hfirst :=
              searchPathKeys_rotateLeft_subset_of_mem_right
                (l := l) (r := BinaryTree.node rl rk (splay rr x))
                (k := k) (x := x) (y := x) (key := key)
                hbst_new hxmem_new_right hmid_x_first
            rcases hfirst with htnew_x | htnew_x
            · rcases replace_x key htnew_x with h_old_x | h_old_x
              · exact Or.inl h_old_x
              · exact Or.inl h_old_x
            · rcases replace_x key htnew_x with h_old_x | h_old_x
              · exact Or.inl h_old_x
              · exact Or.inl h_old_x
          · have hmid_y_first :
                key ∈ searchPathKeys
                  (rotateLeft
                    (BinaryTree.node l k
                      (BinaryTree.node rl rk (splay rr x)))) y := by
              simpa [Tnew, rotateLeft] using hmid_y
            have hfirst :=
              searchPathKeys_rotateLeft_subset_of_mem_right
                (l := l) (r := BinaryTree.node rl rk (splay rr x))
                (k := k) (x := x) (y := y) (key := key)
                hbst_new hxmem_new_right hmid_y_first
            rcases hfirst with htnew_x | htnew_y
            · rcases replace_x key htnew_x with h_old_x | h_old_x
              · exact Or.inl h_old_x
              · exact Or.inl h_old_x
            · exact replace_y key htnew_y

private theorem searchPathKeys_zagZig_subset_of_inner
    {l rl rr : BinaryTree} {k rk x y key : Nat}
    (hbst : IsBST (BinaryTree.node l k (BinaryTree.node rl rk rr)))
    (hxmem : x ∈ rl.toKeyList)
    (hymem : y ∈ (BinaryTree.node l k (BinaryTree.node rl rk rr)).toKeyList)
    (hinner : ∀ z key, z ∈ rl.toKeyList →
      key ∈ searchPathKeys (splay rl x) z →
        key ∈ searchPathKeys rl x ∨ key ∈ searchPathKeys rl z)
    (hkey :
      key ∈ searchPathKeys
        (rotate
          (BinaryTree.node l k (BinaryTree.node (splay rl x) rk rr))
          .zagZig) y) :
    key ∈ searchPathKeys (BinaryTree.node l k (BinaryTree.node rl rk rr)) x ∨
      key ∈ searchPathKeys (BinaryTree.node l k (BinaryTree.node rl rk rr)) y := by
  cases hbst with
  | node _ _ _ hleft hright hbst_left hbst_right =>
      cases hbst_right with
      | node _ _ _ hrl_left hrr_right hbst_rl hbst_rr =>
          have hbst_s_rl : IsBST (splay rl x) :=
            splay_isBST rl x hbst_rl
          have hrl_left_s :
              ForallTree (fun a => a < rk) (splay rl x) := by
            rw [forallTree_iff_forall_mem]
            intro a ha
            have ha_old : a ∈ rl.toKeyList := by
              simpa [splay_toKeyList] using ha
            exact (forallTree_iff_forall_mem.mp hrl_left) a ha_old
          have hright_new :
              ForallTree (fun a => k < a)
                (BinaryTree.node (splay rl x) rk rr) := by
            rw [forallTree_iff_forall_mem]
            intro a ha
            have ha_old :
                a ∈ (BinaryTree.node rl rk rr).toKeyList := by
              simpa [BinaryTree.toKeyList, splay_toKeyList] using ha
            exact (forallTree_iff_forall_mem.mp hright) a ha_old
          have hbst_right_new :
              IsBST (BinaryTree.node (splay rl x) rk rr) :=
            IsBST.node rk (splay rl x) rr
              hrl_left_s hrr_right hbst_s_rl hbst_rr
          have hbst_new :
              IsBST
                (BinaryTree.node l k
                  (BinaryTree.node (splay rl x) rk rr)) :=
            IsBST.node k l (BinaryTree.node (splay rl x) rk rr)
              hleft hright_new hbst_left hbst_right_new
          let Rnew := BinaryTree.node (splay rl x) rk rr
          have hright_rot :
              ForallTree (fun a => k < a) (rotateRight Rnew) := by
            rw [forallTree_iff_forall_mem]
            intro a ha
            have ha_new : a ∈ Rnew.toKeyList := by
              simpa [Rnew, rotateRight_toKeyList] using ha
            exact (forallTree_iff_forall_mem.mp hright_new) a ha_new
          have hbst_right_rot : IsBST (rotateRight Rnew) := by
            exact rotateRight_isBST hbst_right_new
          have hbst_after_inner :
              IsBST (BinaryTree.node l k (rotateRight Rnew)) :=
            IsBST.node k l (rotateRight Rnew)
              hleft hright_rot hbst_left hbst_right_rot
          have hxmem_s : x ∈ (splay rl x).toKeyList := by
            simpa [splay_toKeyList] using hxmem
          have hxmem_rnew_left :
              x ∈ (splay rl x).toKeyList := hxmem_s
          have hxmem_rnew :
              x ∈ Rnew.toKeyList := by
            simp [Rnew, BinaryTree.toKeyList, hxmem_s]
          have hxmem_rightrot : x ∈ (rotateRight Rnew).toKeyList := by
            simpa [Rnew, rotateRight_toKeyList] using hxmem_rnew
          have hkey_outer :
              key ∈ searchPathKeys
                (rotateLeft (BinaryTree.node l k (rotateRight Rnew))) y := by
            simpa [rotate, Rnew] using hkey
          have houter :=
            searchPathKeys_rotateLeft_subset_of_mem_right
              (l := l) (r := rotateRight Rnew) (k := k)
              (x := x) (y := y) (key := key)
              hbst_after_inner hxmem_rightrot hkey_outer
          have hxmem_old :
              x ∈ (BinaryTree.node l k (BinaryTree.node rl rk rr)).toKeyList := by
            simp [BinaryTree.toKeyList, hxmem]
          have hbst_right_old : IsBST (BinaryTree.node rl rk rr) :=
            IsBST.node rk rl rr hrl_left hrr_right hbst_rl hbst_rr
          have hbst_old :
              IsBST (BinaryTree.node l k (BinaryTree.node rl rk rr)) :=
            IsBST.node k l (BinaryTree.node rl rk rr)
              hleft hright hbst_left hbst_right_old
          let Tnew := BinaryTree.node l k Rnew
          have replace_x :
              ∀ key,
                key ∈ searchPathKeys Tnew x →
                  key ∈ searchPathKeys
                    (BinaryTree.node l k (BinaryTree.node rl rk rr)) x ∨
                    key ∈ searchPathKeys
                      (BinaryTree.node l k (BinaryTree.node rl rk rr)) x := by
            intro key hkey_x
            exact searchPathKeys_node_right_left_splay_subset_of_inner
              (l := l) (rl := rl) (rr := rr) (k := k) (rk := rk)
              (x := x) (y := x) (key := key)
              hbst_old hxmem hxmem_old
              (fun key hx_in_rl hkey_inner =>
                hinner x key hx_in_rl hkey_inner)
              (by simpa [Tnew, Rnew] using hkey_x)
          have replace_y :
              ∀ key,
                key ∈ searchPathKeys Tnew y →
                  key ∈ searchPathKeys
                    (BinaryTree.node l k (BinaryTree.node rl rk rr)) x ∨
                    key ∈ searchPathKeys
                      (BinaryTree.node l k (BinaryTree.node rl rk rr)) y := by
            intro key hkey_y
            exact searchPathKeys_node_right_left_splay_subset_of_inner
              (l := l) (rl := rl) (rr := rr) (k := k) (rk := rk)
              (x := x) (y := y) (key := key)
              hbst_old hxmem hymem
              (fun key hy_in_rl hkey_inner =>
                hinner y key hy_in_rl hkey_inner)
              (by simpa [Tnew, Rnew] using hkey_y)
          have inner_lift :
              ∀ z key,
                key ∈ searchPathKeys (BinaryTree.node l k (rotateRight Rnew)) z →
                  key ∈ searchPathKeys Tnew x ∨
                    key ∈ searchPathKeys Tnew z := by
            intro z key hpath
            have hrot :=
              searchPathKeys_node_right_rotateRight_subset_of_mem_left
                (l := l) (rl := splay rl x) (rr := rr)
                (k := k) (rk := rk) (x := x) (y := z) (key := key)
                (by simpa [Tnew, Rnew] using hbst_new)
                hxmem_rnew_left
                (by simpa [Tnew, Rnew] using hpath)
            simpa [Tnew, Rnew] using hrot
          rcases houter with hmid_x | hmid_y
          · rcases inner_lift x key hmid_x with htnew_x | htnew_x
            · rcases replace_x key htnew_x with h_old_x | h_old_x
              · exact Or.inl h_old_x
              · exact Or.inl h_old_x
            · rcases replace_x key htnew_x with h_old_x | h_old_x
              · exact Or.inl h_old_x
              · exact Or.inl h_old_x
          · rcases inner_lift y key hmid_y with htnew_x | htnew_y
            · rcases replace_x key htnew_x with h_old_x | h_old_x
              · exact Or.inl h_old_x
              · exact Or.inl h_old_x
            · exact replace_y key htnew_y

private theorem searchPathKeys_splay_zigZig_branch_subset_of_inner
    {ll lr r : BinaryTree} {lk k x y key : Nat}
    (hbst : IsBST (BinaryTree.node (BinaryTree.node ll lk lr) k r))
    (hxmem : x ∈ ll.toKeyList)
    (hymem : y ∈ (BinaryTree.node (BinaryTree.node ll lk lr) k r).toKeyList)
    (hinner : ∀ z key, z ∈ ll.toKeyList →
      key ∈ searchPathKeys (splay ll x) z →
        key ∈ searchPathKeys ll x ∨ key ∈ searchPathKeys ll z)
    (hkey :
      key ∈ searchPathKeys
        (splay (BinaryTree.node (BinaryTree.node ll lk lr) k r) x) y) :
    key ∈ searchPathKeys (BinaryTree.node (BinaryTree.node ll lk lr) k r) x ∨
      key ∈ searchPathKeys (BinaryTree.node (BinaryTree.node ll lk lr) k r) y := by
  cases hbst with
  | node _ _ _ hleft _hright hbst_left _hbst_right =>
      cases hbst_left with
      | node _ _ _ hll_left _hlr_right _hbst_ll _hbst_lr =>
          have hx_left_mem :
              x ∈ (BinaryTree.node ll lk lr).toKeyList := by
            simp [BinaryTree.toKeyList, hxmem]
          have hx_lt_k :=
            (forallTree_iff_forall_mem.mp hleft) x hx_left_mem
          have hx_lt_lk :=
            (forallTree_iff_forall_mem.mp hll_left) x hxmem
          have hx_ne_k : x ≠ k := by omega
          have hsplay :
              splay (BinaryTree.node (BinaryTree.node ll lk lr) k r) x =
                rotate
                  (BinaryTree.node
                    (BinaryTree.node (splay ll x) lk lr) k r)
                  .zigZig := by
            cases ll with
            | empty =>
                simp [BinaryTree.toKeyList] at hxmem
            | node a q b =>
                conv_lhs => unfold splay
                simp [hx_ne_k, hx_lt_k, hx_lt_lk]
          rw [hsplay] at hkey
          have hbst_left_old : IsBST (BinaryTree.node ll lk lr) :=
            IsBST.node lk ll lr hll_left _hlr_right _hbst_ll _hbst_lr
          have hbst_old :
              IsBST (BinaryTree.node (BinaryTree.node ll lk lr) k r) :=
            IsBST.node k (BinaryTree.node ll lk lr) r
              hleft _hright hbst_left_old _hbst_right
          exact searchPathKeys_zigZig_subset_of_inner
            (ll := ll) (lr := lr) (r := r) (lk := lk) (k := k)
            (x := x) (y := y) (key := key)
            hbst_old
            hxmem hymem hinner hkey

private theorem searchPathKeys_splay_zigZag_branch_subset_of_inner
    {ll lr r : BinaryTree} {lk k x y key : Nat}
    (hbst : IsBST (BinaryTree.node (BinaryTree.node ll lk lr) k r))
    (hxmem : x ∈ lr.toKeyList)
    (hymem : y ∈ (BinaryTree.node (BinaryTree.node ll lk lr) k r).toKeyList)
    (hinner : ∀ z key, z ∈ lr.toKeyList →
      key ∈ searchPathKeys (splay lr x) z →
        key ∈ searchPathKeys lr x ∨ key ∈ searchPathKeys lr z)
    (hkey :
      key ∈ searchPathKeys
        (splay (BinaryTree.node (BinaryTree.node ll lk lr) k r) x) y) :
    key ∈ searchPathKeys (BinaryTree.node (BinaryTree.node ll lk lr) k r) x ∨
      key ∈ searchPathKeys (BinaryTree.node (BinaryTree.node ll lk lr) k r) y := by
  cases hbst with
  | node _ _ _ hleft _hright hbst_left _hbst_right =>
      cases hbst_left with
      | node _ _ _ _hll_left hlr_right _hbst_ll _hbst_lr =>
          have hx_left_mem :
              x ∈ (BinaryTree.node ll lk lr).toKeyList := by
            simp [BinaryTree.toKeyList, hxmem]
          have hx_lt_k :=
            (forallTree_iff_forall_mem.mp hleft) x hx_left_mem
          have hlk_lt_x :=
            (forallTree_iff_forall_mem.mp hlr_right) x hxmem
          have hx_ne_k : x ≠ k := by omega
          have hnot_x_lt_lk : ¬ x < lk := by omega
          have hsplay :
              splay (BinaryTree.node (BinaryTree.node ll lk lr) k r) x =
                rotate
                  (BinaryTree.node
                    (BinaryTree.node ll lk (splay lr x)) k r)
                  .zigZag := by
            cases lr with
            | empty =>
                simp [BinaryTree.toKeyList] at hxmem
            | node a q b =>
                conv_lhs => unfold splay
                simp [hx_ne_k, hx_lt_k, hnot_x_lt_lk, hlk_lt_x]
          rw [hsplay] at hkey
          have hbst_left_old : IsBST (BinaryTree.node ll lk lr) :=
            IsBST.node lk ll lr _hll_left hlr_right _hbst_ll _hbst_lr
          have hbst_old :
              IsBST (BinaryTree.node (BinaryTree.node ll lk lr) k r) :=
            IsBST.node k (BinaryTree.node ll lk lr) r
              hleft _hright hbst_left_old _hbst_right
          exact searchPathKeys_zigZag_subset_of_inner
            (ll := ll) (lr := lr) (r := r) (lk := lk) (k := k)
            (x := x) (y := y) (key := key)
            hbst_old
            hxmem hymem hinner hkey

private theorem searchPathKeys_splay_zagZag_branch_subset_of_inner
    {l rl rr : BinaryTree} {k rk x y key : Nat}
    (hbst : IsBST (BinaryTree.node l k (BinaryTree.node rl rk rr)))
    (hxmem : x ∈ rr.toKeyList)
    (hymem : y ∈ (BinaryTree.node l k (BinaryTree.node rl rk rr)).toKeyList)
    (hinner : ∀ z key, z ∈ rr.toKeyList →
      key ∈ searchPathKeys (splay rr x) z →
        key ∈ searchPathKeys rr x ∨ key ∈ searchPathKeys rr z)
    (hkey :
      key ∈ searchPathKeys
        (splay (BinaryTree.node l k (BinaryTree.node rl rk rr)) x) y) :
    key ∈ searchPathKeys (BinaryTree.node l k (BinaryTree.node rl rk rr)) x ∨
      key ∈ searchPathKeys (BinaryTree.node l k (BinaryTree.node rl rk rr)) y := by
  cases hbst with
  | node _ _ _ _hleft hright _hbst_left hbst_right =>
      cases hbst_right with
      | node _ _ _ _hrl_left hrr_right _hbst_rl _hbst_rr =>
          have hx_right_mem :
              x ∈ (BinaryTree.node rl rk rr).toKeyList := by
            simp [BinaryTree.toKeyList, hxmem]
          have hk_lt_x :=
            (forallTree_iff_forall_mem.mp hright) x hx_right_mem
          have hrk_lt_x :=
            (forallTree_iff_forall_mem.mp hrr_right) x hxmem
          have hx_ne_k : x ≠ k := by omega
          have hnot_x_lt_k : ¬ x < k := by omega
          have hnot_x_lt_rk : ¬ x < rk := by omega
          have hsplay :
              splay (BinaryTree.node l k (BinaryTree.node rl rk rr)) x =
                rotate
                  (BinaryTree.node l k
                    (BinaryTree.node rl rk (splay rr x)))
                  .zagZag := by
            cases rr with
            | empty =>
                simp [BinaryTree.toKeyList] at hxmem
            | node a q b =>
                conv_lhs => unfold splay
                simp [hx_ne_k, hnot_x_lt_k, hnot_x_lt_rk, hrk_lt_x]
          rw [hsplay] at hkey
          have hbst_right_old : IsBST (BinaryTree.node rl rk rr) :=
            IsBST.node rk rl rr _hrl_left hrr_right _hbst_rl _hbst_rr
          have hbst_old :
              IsBST (BinaryTree.node l k (BinaryTree.node rl rk rr)) :=
            IsBST.node k l (BinaryTree.node rl rk rr)
              _hleft hright _hbst_left hbst_right_old
          exact searchPathKeys_zagZag_subset_of_inner
            (l := l) (rl := rl) (rr := rr) (k := k) (rk := rk)
            (x := x) (y := y) (key := key)
            hbst_old
            hxmem hymem hinner hkey

private theorem searchPathKeys_splay_zagZig_branch_subset_of_inner
    {l rl rr : BinaryTree} {k rk x y key : Nat}
    (hbst : IsBST (BinaryTree.node l k (BinaryTree.node rl rk rr)))
    (hxmem : x ∈ rl.toKeyList)
    (hymem : y ∈ (BinaryTree.node l k (BinaryTree.node rl rk rr)).toKeyList)
    (hinner : ∀ z key, z ∈ rl.toKeyList →
      key ∈ searchPathKeys (splay rl x) z →
        key ∈ searchPathKeys rl x ∨ key ∈ searchPathKeys rl z)
    (hkey :
      key ∈ searchPathKeys
        (splay (BinaryTree.node l k (BinaryTree.node rl rk rr)) x) y) :
    key ∈ searchPathKeys (BinaryTree.node l k (BinaryTree.node rl rk rr)) x ∨
      key ∈ searchPathKeys (BinaryTree.node l k (BinaryTree.node rl rk rr)) y := by
  cases hbst with
  | node _ _ _ _hleft hright _hbst_left hbst_right =>
      cases hbst_right with
      | node _ _ _ hrl_left _hrr_right _hbst_rl _hbst_rr =>
          have hx_right_mem :
              x ∈ (BinaryTree.node rl rk rr).toKeyList := by
            simp [BinaryTree.toKeyList, hxmem]
          have hk_lt_x :=
            (forallTree_iff_forall_mem.mp hright) x hx_right_mem
          have hx_lt_rk :=
            (forallTree_iff_forall_mem.mp hrl_left) x hxmem
          have hx_ne_k : x ≠ k := by omega
          have hnot_x_lt_k : ¬ x < k := by omega
          have hsplay :
              splay (BinaryTree.node l k (BinaryTree.node rl rk rr)) x =
                rotate
                  (BinaryTree.node l k
                    (BinaryTree.node (splay rl x) rk rr))
                  .zagZig := by
            cases rl with
            | empty =>
                simp [BinaryTree.toKeyList] at hxmem
            | node a q b =>
                conv_lhs => unfold splay
                simp [hx_ne_k, hnot_x_lt_k, hx_lt_rk]
          rw [hsplay] at hkey
          have hbst_right_old : IsBST (BinaryTree.node rl rk rr) :=
            IsBST.node rk rl rr hrl_left _hrr_right _hbst_rl _hbst_rr
          have hbst_old :
              IsBST (BinaryTree.node l k (BinaryTree.node rl rk rr)) :=
            IsBST.node k l (BinaryTree.node rl rk rr)
              _hleft hright _hbst_left hbst_right_old
          exact searchPathKeys_zagZig_subset_of_inner
            (l := l) (rl := rl) (rr := rr) (k := k) (rk := rk)
            (x := x) (y := y) (key := key)
            hbst_old
            hxmem hymem hinner hkey

private theorem searchPathKeys_splay_zig_child_branch_subset
    {ll lr r : BinaryTree} {lk k x y key : Nat}
    (hbst : IsBST (BinaryTree.node (BinaryTree.node ll lk lr) k r))
    (hx : x = lk)
    (hkey :
      key ∈ searchPathKeys
        (splay (BinaryTree.node (BinaryTree.node ll lk lr) k r) x) y) :
    key ∈ searchPathKeys (BinaryTree.node (BinaryTree.node ll lk lr) k r) x ∨
      key ∈ searchPathKeys (BinaryTree.node (BinaryTree.node ll lk lr) k r) y := by
  subst x
  cases hbst with
  | node _ _ _ hleft hright hbst_left hbst_right =>
      cases hbst_left with
      | node _ _ _ hll_left hlr_right hbst_ll hbst_lr =>
          have hlk_mem_left :
              lk ∈ (BinaryTree.node ll lk lr).toKeyList := by
            simp [BinaryTree.toKeyList]
          have hlk_lt_k :=
            (forallTree_iff_forall_mem.mp hleft) lk hlk_mem_left
          have hlk_ne_k : lk ≠ k := by omega
          have hsplay :
              splay (BinaryTree.node (BinaryTree.node ll lk lr) k r) lk =
                rotate (BinaryTree.node (BinaryTree.node ll lk lr) k r) .zig := by
            conv_lhs => unfold splay
            simp [hlk_ne_k, hlk_lt_k]
          rw [hsplay] at hkey
          have hleft_mem :
              lk ∈ (BinaryTree.node ll lk lr).toKeyList := by
            simp [BinaryTree.toKeyList]
          have hbst_old :
              IsBST (BinaryTree.node (BinaryTree.node ll lk lr) k r) :=
            IsBST.node k (BinaryTree.node ll lk lr) r
              hleft hright
              (IsBST.node lk ll lr hll_left hlr_right hbst_ll hbst_lr)
              hbst_right
          exact searchPathKeys_rotate_zig_subset_of_mem_left
            (l := BinaryTree.node ll lk lr) (r := r)
            (k := k) (x := lk) (y := y) (key := key)
            hbst_old hleft_mem hkey

private theorem searchPathKeys_splay_zag_child_branch_subset
    {l rl rr : BinaryTree} {k rk x y key : Nat}
    (hbst : IsBST (BinaryTree.node l k (BinaryTree.node rl rk rr)))
    (hx : x = rk)
    (hkey :
      key ∈ searchPathKeys
        (splay (BinaryTree.node l k (BinaryTree.node rl rk rr)) x) y) :
    key ∈ searchPathKeys (BinaryTree.node l k (BinaryTree.node rl rk rr)) x ∨
      key ∈ searchPathKeys (BinaryTree.node l k (BinaryTree.node rl rk rr)) y := by
  subst x
  cases hbst with
  | node _ _ _ hleft hright hbst_left hbst_right =>
      cases hbst_right with
      | node _ _ _ hrl_left hrr_right hbst_rl hbst_rr =>
          have hrk_mem_right :
              rk ∈ (BinaryTree.node rl rk rr).toKeyList := by
            simp [BinaryTree.toKeyList]
          have hk_lt_rk :=
            (forallTree_iff_forall_mem.mp hright) rk hrk_mem_right
          have hrk_ne_k : rk ≠ k := by omega
          have hnot_rk_lt_k : ¬ rk < k := by omega
          have hsplay :
              splay (BinaryTree.node l k (BinaryTree.node rl rk rr)) rk =
                rotate (BinaryTree.node l k (BinaryTree.node rl rk rr)) .zag := by
            conv_lhs => unfold splay
            simp [hrk_ne_k, hnot_rk_lt_k]
          rw [hsplay] at hkey
          have hright_mem :
              rk ∈ (BinaryTree.node rl rk rr).toKeyList := by
            simp [BinaryTree.toKeyList]
          have hbst_old :
              IsBST (BinaryTree.node l k (BinaryTree.node rl rk rr)) :=
            IsBST.node k l (BinaryTree.node rl rk rr)
              hleft hright hbst_left
              (IsBST.node rk rl rr hrl_left hrr_right hbst_rl hbst_rr)
          exact searchPathKeys_rotate_zag_subset_of_mem_right
            (l := l) (r := BinaryTree.node rl rk rr)
            (k := k) (x := rk) (y := y) (key := key)
            hbst_old hright_mem hkey

private theorem searchPathKeys_splay_subset_union :
    ∀ (t : BinaryTree) (x y key : Nat), IsBST t →
      x ∈ t.toKeyList → y ∈ t.toKeyList →
      key ∈ searchPathKeys (splay t x) y →
        key ∈ searchPathKeys t x ∨ key ∈ searchPathKeys t y
| .empty, x, y, key, _hbst, hxmem, _hymem, _hkey => by
    simp [BinaryTree.toKeyList] at hxmem
| .node l k r, x, y, key, hbst, hxmem, hymem, hkey => by
    cases hbst with
    | node _ _ _ hleft hright hbst_left hbst_right =>
        simp only [BinaryTree.toKeyList, List.mem_append,
          List.mem_singleton] at hxmem
        rcases hxmem with (hx_left | hx_root) | hx_right
        · have hx_lt_k :=
            (forallTree_iff_forall_mem.mp hleft) x hx_left
          have hx_ne_k : x ≠ k := by omega
          cases l with
          | empty =>
              simp [BinaryTree.toKeyList] at hx_left
          | node ll lk lr =>
              cases hbst_left with
              | node _ _ _ hll_left hlr_right hbst_ll hbst_lr =>
                  simp only [BinaryTree.toKeyList, List.mem_append,
                    List.mem_singleton] at hx_left
                  rcases hx_left with (hx_ll | hx_lk) | hx_lr
                  · have hbst_old :
                        IsBST (BinaryTree.node (BinaryTree.node ll lk lr) k r) :=
                      IsBST.node k (BinaryTree.node ll lk lr) r
                        hleft hright
                        (IsBST.node lk ll lr hll_left hlr_right hbst_ll hbst_lr)
                        hbst_right
                    exact searchPathKeys_splay_zigZig_branch_subset_of_inner
                      (ll := ll) (lr := lr) (r := r) (lk := lk) (k := k)
                      (x := x) (y := y) (key := key)
                      hbst_old hx_ll hymem
                      (fun z key hz hpath =>
                        searchPathKeys_splay_subset_union
                          ll x z key hbst_ll hx_ll hz hpath)
                      hkey
                  · subst x
                    have hbst_old :
                        IsBST (BinaryTree.node (BinaryTree.node ll lk lr) k r) :=
                      IsBST.node k (BinaryTree.node ll lk lr) r
                        hleft hright
                        (IsBST.node lk ll lr hll_left hlr_right hbst_ll hbst_lr)
                        hbst_right
                    exact searchPathKeys_splay_zig_child_branch_subset
                      (ll := ll) (lr := lr) (r := r) (lk := lk) (k := k)
                      (x := lk) (y := y) (key := key)
                      hbst_old rfl hkey
                  · have hbst_old :
                        IsBST (BinaryTree.node (BinaryTree.node ll lk lr) k r) :=
                      IsBST.node k (BinaryTree.node ll lk lr) r
                        hleft hright
                        (IsBST.node lk ll lr hll_left hlr_right hbst_ll hbst_lr)
                        hbst_right
                    exact searchPathKeys_splay_zigZag_branch_subset_of_inner
                      (ll := ll) (lr := lr) (r := r) (lk := lk) (k := k)
                      (x := x) (y := y) (key := key)
                      hbst_old hx_lr hymem
                      (fun z key hz hpath =>
                        searchPathKeys_splay_subset_union
                          lr x z key hbst_lr hx_lr hz hpath)
                      hkey
        · subst x
          have hsplay : splay (BinaryTree.node l k r) k = BinaryTree.node l k r := by
            conv_lhs => unfold splay
            simp
          rw [hsplay] at hkey
          exact Or.inr hkey
        · have hk_lt_x :=
            (forallTree_iff_forall_mem.mp hright) x hx_right
          have hx_ne_k : x ≠ k := by omega
          have hnot_x_lt_k : ¬ x < k := by omega
          cases r with
          | empty =>
              simp [BinaryTree.toKeyList] at hx_right
          | node rl rk rr =>
              cases hbst_right with
              | node _ _ _ hrl_left hrr_right hbst_rl hbst_rr =>
                  simp only [BinaryTree.toKeyList, List.mem_append,
                    List.mem_singleton] at hx_right
                  rcases hx_right with (hx_rl | hx_rk) | hx_rr
                  · have hbst_old :
                        IsBST (BinaryTree.node l k (BinaryTree.node rl rk rr)) :=
                      IsBST.node k l (BinaryTree.node rl rk rr)
                        hleft hright hbst_left
                        (IsBST.node rk rl rr hrl_left hrr_right hbst_rl hbst_rr)
                    exact searchPathKeys_splay_zagZig_branch_subset_of_inner
                      (l := l) (rl := rl) (rr := rr) (k := k) (rk := rk)
                      (x := x) (y := y) (key := key)
                      hbst_old hx_rl hymem
                      (fun z key hz hpath =>
                        searchPathKeys_splay_subset_union
                          rl x z key hbst_rl hx_rl hz hpath)
                      hkey
                  · subst x
                    have hbst_old :
                        IsBST (BinaryTree.node l k (BinaryTree.node rl rk rr)) :=
                      IsBST.node k l (BinaryTree.node rl rk rr)
                        hleft hright hbst_left
                        (IsBST.node rk rl rr hrl_left hrr_right hbst_rl hbst_rr)
                    exact searchPathKeys_splay_zag_child_branch_subset
                      (l := l) (rl := rl) (rr := rr) (k := k) (rk := rk)
                      (x := rk) (y := y) (key := key)
                      hbst_old rfl hkey
                  · have hbst_old :
                        IsBST (BinaryTree.node l k (BinaryTree.node rl rk rr)) :=
                      IsBST.node k l (BinaryTree.node rl rk rr)
                        hleft hright hbst_left
                        (IsBST.node rk rl rr hrl_left hrr_right hbst_rl hbst_rr)
                    exact searchPathKeys_splay_zagZag_branch_subset_of_inner
                      (l := l) (rl := rl) (rr := rr) (k := k) (rk := rk)
                      (x := x) (y := y) (key := key)
                      hbst_old hx_rr hymem
                      (fun z key hz hpath =>
                        searchPathKeys_splay_subset_union
                          rr x z key hbst_rr hx_rr hz hpath)
                      hkey

private theorem searchPathKeys_nodup_of_isBST :
    ∀ (t : BinaryTree) (q : Nat), IsBST t → (searchPathKeys t q).Nodup
| .empty, q, _hbst => by
    simp [searchPathKeys]
| .node l k r, q, hbst => by
    cases hbst with
    | node _ _ _ hleft hright hbst_left hbst_right =>
        simp only [searchPathKeys]
        by_cases hqk : q < k
        · simp [hqk]
          constructor
          · intro hkpath
            have hleft_mem : k ∈ l.toKeyList :=
              searchPathKeys_subset_toKeyList l q k hkpath
            have hk_lt : k < k :=
              (forallTree_iff_forall_mem.mp hleft) k hleft_mem
            omega
          · exact searchPathKeys_nodup_of_isBST l q hbst_left
        · by_cases hkq : k < q
          · simp [hqk, hkq]
            constructor
            · intro hkpath
              have hright_mem : k ∈ r.toKeyList :=
                searchPathKeys_subset_toKeyList r q k hkpath
              have hk_gt : k < k :=
                (forallTree_iff_forall_mem.mp hright) k hright_mem
              omega
            · exact searchPathKeys_nodup_of_isBST r q hbst_right
          · simp [hqk, hkq]

private noncomputable def activeHullKeys {n : Nat} (X : Fin n → Nat)
    (t : BinaryTree) (xs : List (Fin n)) : List Nat :=
  t.toKeyList.filter (fun key =>
    decide (∃ i : Fin n, i ∈ xs ∧ key ∈ searchPathKeys t (X i)))

private noncomputable def activeHullSize {n : Nat} (X : Fin n → Nat)
    (t : BinaryTree) (xs : List (Fin n)) : Nat :=
  (activeHullKeys X t xs).length

private theorem activeHullKeys_subset_toKeyList {n : Nat}
    (X : Fin n → Nat) (t : BinaryTree) (xs : List (Fin n))
    {key : Nat} :
    key ∈ activeHullKeys X t xs → key ∈ t.toKeyList := by
  intro hkey
  unfold activeHullKeys at hkey
  exact List.mem_of_mem_filter hkey

private theorem mem_activeHullKeys_iff {n : Nat}
    (X : Fin n → Nat) (t : BinaryTree) (xs : List (Fin n))
    {key : Nat} :
    key ∈ activeHullKeys X t xs ↔
      key ∈ t.toKeyList ∧
        ∃ i : Fin n, i ∈ xs ∧ key ∈ searchPathKeys t (X i) := by
  unfold activeHullKeys
  rw [List.mem_filter]
  simp

private theorem activeHullKeys_nodup_of_isBST {n : Nat}
    (X : Fin n → Nat) {t : BinaryTree} (xs : List (Fin n))
    (hbst : IsBST t) :
    (activeHullKeys X t xs).Nodup := by
  unfold activeHullKeys
  exact List.Nodup.filter _
    (isBST_toKeyList_nodup hbst)

private theorem mem_activeHullKeys_of_mem_searchPath {n : Nat}
    (X : Fin n → Nat) (t : BinaryTree) (xs : List (Fin n))
    {i : Fin n} {key : Nat}
    (hi : i ∈ xs) (hpath : key ∈ searchPathKeys t (X i)) :
    key ∈ activeHullKeys X t xs := by
  unfold activeHullKeys
  refine List.mem_filter_of_mem ?_ ?_
  · exact searchPathKeys_subset_toKeyList t (X i) key hpath
  · exact decide_eq_true
      (show ∃ j : Fin n, j ∈ xs ∧ key ∈ searchPathKeys t (X j) from
        ⟨i, hi, hpath⟩)

private theorem filter_sublist_filter_of_imp {α : Type}
    (p q : α → Bool)
    (himp : ∀ x, p x = true → q x = true) :
    ∀ xs : List α, (xs.filter p).Sublist (xs.filter q)
| [] => by
    simp
| x :: xs => by
    have ih := filter_sublist_filter_of_imp p q himp xs
    by_cases hp : p x = true
    · have hq : q x = true := himp x hp
      simp [List.filter, hp, hq, ih]
    · by_cases hq : q x = true
      · simp [List.filter, hp, hq]
        exact List.Sublist.cons x ih
      · simp [List.filter, hp, hq, ih]

private theorem activeHullKeys_sublist_of_sublist {n : Nat}
    (X : Fin n → Nat) (t : BinaryTree) {xs ys : List (Fin n)}
    (hsub : xs.Sublist ys) :
    (activeHullKeys X t xs).Sublist (activeHullKeys X t ys) := by
  unfold activeHullKeys
  apply filter_sublist_filter_of_imp
  intro key hkey
  simp at hkey ⊢
  rcases hkey with ⟨i, hi, hpath⟩
  exact ⟨i, hsub.subset hi, hpath⟩

private theorem activeHullSize_sublist_le {n : Nat}
    (X : Fin n → Nat) (t : BinaryTree) {xs ys : List (Fin n)}
    (hsub : xs.Sublist ys) :
    activeHullSize X t xs ≤ activeHullSize X t ys := by
  unfold activeHullSize
  exact List.Sublist.length_le
    (activeHullKeys_sublist_of_sublist X t hsub)

private theorem activeHullSize_le_num_nodes {n : Nat}
    (X : Fin n → Nat) (t : BinaryTree) (xs : List (Fin n)) :
    activeHullSize X t xs ≤ t.num_nodes := by
  unfold activeHullSize activeHullKeys
  have hlen := List.length_eq_length_filter_add
    (l := t.toKeyList)
    (f := fun key =>
      decide (∃ i : Fin n, i ∈ xs ∧ key ∈ searchPathKeys t (X i)))
  rw [toKeyList_length] at hlen
  omega

private theorem activeHullSize_append_le {n : Nat}
    (X : Fin n → Nat) {t : BinaryTree} (xs ys : List (Fin n))
    (hbst : IsBST t) :
    activeHullSize X t (xs ++ ys) ≤
      activeHullSize X t xs + activeHullSize X t ys := by
  have happ_nodup :
      (activeHullKeys X t (xs ++ ys)).Nodup :=
    activeHullKeys_nodup_of_isBST X (xs ++ ys) hbst
  have hxs_nodup :
      (activeHullKeys X t xs).Nodup :=
    activeHullKeys_nodup_of_isBST X xs hbst
  have hys_nodup :
      (activeHullKeys X t ys).Nodup :=
    activeHullKeys_nodup_of_isBST X ys hbst
  have happ_card :
      (activeHullKeys X t (xs ++ ys)).toFinset.card =
        activeHullSize X t (xs ++ ys) := by
    unfold activeHullSize
    exact List.toFinset_card_of_nodup happ_nodup
  have hxs_card :
      (activeHullKeys X t xs).toFinset.card =
        activeHullSize X t xs := by
    unfold activeHullSize
    exact List.toFinset_card_of_nodup hxs_nodup
  have hys_card :
      (activeHullKeys X t ys).toFinset.card =
        activeHullSize X t ys := by
    unfold activeHullSize
    exact List.toFinset_card_of_nodup hys_nodup
  rw [← happ_card, ← hxs_card, ← hys_card]
  calc
    (activeHullKeys X t (xs ++ ys)).toFinset.card
        ≤ ((activeHullKeys X t xs).toFinset ∪
            (activeHullKeys X t ys).toFinset).card := by
          apply Finset.card_le_card
          intro key hkey
          have hmem : key ∈ activeHullKeys X t (xs ++ ys) := by
            simpa using hkey
          rw [Finset.mem_union]
          rcases (mem_activeHullKeys_iff X t (xs ++ ys)).mp hmem with
            ⟨hkey_tree, i, hi, hpath⟩
          simp at hi
          rcases hi with hix | hiy
          · left
            simpa using
              (mem_activeHullKeys_iff X t xs).mpr
                ⟨hkey_tree, i, hix, hpath⟩
          · right
            simpa using
              (mem_activeHullKeys_iff X t ys).mpr
                ⟨hkey_tree, i, hiy, hpath⟩
    _ ≤ (activeHullKeys X t xs).toFinset.card +
          (activeHullKeys X t ys).toFinset.card :=
        Finset.card_union_le _ _

private theorem search_path_len_le_activeHullSize_of_mem {n : Nat}
    (X : Fin n → Nat) {t : BinaryTree} (xs : List (Fin n))
    (hbst : IsBST t) {i : Fin n} (hi : i ∈ xs) :
    t.search_path_len (X i) ≤ activeHullSize X t xs := by
  rw [← searchPathKeys_length_eq_search_path_len]
  have hpath_nodup : (searchPathKeys t (X i)).Nodup :=
    searchPathKeys_nodup_of_isBST t (X i) hbst
  have hhull_nodup : (activeHullKeys X t xs).Nodup :=
    activeHullKeys_nodup_of_isBST X xs hbst
  have hpath_card :
      (searchPathKeys t (X i)).toFinset.card =
        (searchPathKeys t (X i)).length :=
    List.toFinset_card_of_nodup hpath_nodup
  have hhull_card :
      (activeHullKeys X t xs).toFinset.card =
        activeHullSize X t xs := by
    unfold activeHullSize
    exact List.toFinset_card_of_nodup hhull_nodup
  rw [← hpath_card, ← hhull_card]
  apply Finset.card_le_card
  intro key hkey
  simp at hkey ⊢
  exact mem_activeHullKeys_of_mem_searchPath X t xs hi hkey

private theorem activeHullKeys_nil {n : Nat}
    (X : Fin n → Nat) (t : BinaryTree) :
    activeHullKeys X t [] = [] := by
  unfold activeHullKeys
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro key hkey
  have hactive := (List.mem_filter.mp hkey).2
  simp at hactive

private theorem activeHullSize_nil {n : Nat}
    (X : Fin n → Nat) (t : BinaryTree) :
    activeHullSize X t [] = 0 := by
  unfold activeHullSize
  rw [activeHullKeys_nil]
  simp

private theorem search_path_len_real_le_activeHullSize_of_mem {n : Nat}
    (X : Fin n → Nat) {t : BinaryTree} (xs : List (Fin n))
    (hbst : IsBST t) {i : Fin n} (hi : i ∈ xs) :
    (t.search_path_len (X i) : ℝ) ≤ activeHullSize X t xs := by
  exact_mod_cast search_path_len_le_activeHullSize_of_mem X xs hbst hi

private noncomputable def activeBudget {n : Nat} (X : Fin n → Nat)
    (t : BinaryTree) (xs : List (Fin n)) : ℝ :=
  (xs.length : ℝ) + activeHullSize X t xs

private theorem activeBudget_nonneg {n : Nat}
    (X : Fin n → Nat) (t : BinaryTree) (xs : List (Fin n)) :
    0 ≤ activeBudget X t xs := by
  unfold activeBudget
  positivity

private theorem activeBudget_sublist_le {n : Nat}
    (X : Fin n → Nat) (t : BinaryTree) {xs ys : List (Fin n)}
    (hsub : xs.Sublist ys) :
    activeBudget X t xs ≤ activeBudget X t ys := by
  have hlen := List.Sublist.length_le hsub
  have hhull := activeHullSize_sublist_le X t hsub
  unfold activeBudget
  exact_mod_cast Nat.add_le_add hlen hhull

private theorem activeHullKeys_after_splay_sublist_cons {n : Nat}
    (X : Fin n → Nat) {t : BinaryTree} (i : Fin n)
    (xs : List (Fin n))
    (hbst : IsBST t)
    (hi_mem : X i ∈ t.toKeyList)
    (hmem_tail : ∀ j : Fin n, j ∈ xs → X j ∈ t.toKeyList) :
    (activeHullKeys X (splay t (X i)) xs).Sublist
      (activeHullKeys X t (i :: xs)) := by
  unfold activeHullKeys
  rw [splay_toKeyList]
  apply filter_sublist_filter_of_imp
  intro key hkey
  simp at hkey ⊢
  rcases hkey with ⟨j, hj, hpath⟩
  have hor :=
    searchPathKeys_splay_subset_union t (X i) (X j) key
      hbst hi_mem (hmem_tail j hj) hpath
  rcases hor with hxi | hxj
  · exact Or.inl hxi
  · exact Or.inr ⟨j, hj, hxj⟩

private theorem activeHullSize_after_splay_le_cons {n : Nat}
    (X : Fin n → Nat) {t : BinaryTree} (i : Fin n)
    (xs : List (Fin n))
    (hbst : IsBST t)
    (hi_mem : X i ∈ t.toKeyList)
    (hmem_tail : ∀ j : Fin n, j ∈ xs → X j ∈ t.toKeyList) :
    activeHullSize X (splay t (X i)) xs ≤
      activeHullSize X t (i :: xs) := by
  unfold activeHullSize
  exact List.Sublist.length_le
    (activeHullKeys_after_splay_sublist_cons
      X i xs hbst hi_mem hmem_tail)

private theorem activeBudget_after_splay_le_cons {n : Nat}
    (X : Fin n → Nat) {t : BinaryTree} (i : Fin n)
    (xs : List (Fin n))
    (hbst : IsBST t)
    (hi_mem : X i ∈ t.toKeyList)
    (hmem_tail : ∀ j : Fin n, j ∈ xs → X j ∈ t.toKeyList) :
    activeBudget X (splay t (X i)) xs ≤
      activeBudget X t (i :: xs) := by
  have hlen : xs.length ≤ (i :: xs).length := by simp
  have hhull :=
    activeHullSize_after_splay_le_cons X i xs hbst hi_mem hmem_tail
  unfold activeBudget
  exact_mod_cast Nat.add_le_add hlen hhull

private theorem activeHullSize_after_splay_le_path_add {n : Nat}
    (X : Fin n → Nat) {t : BinaryTree} (q : Nat)
    (xs : List (Fin n))
    (hbst : IsBST t)
    (hq_mem : q ∈ t.toKeyList)
    (hmem_tail : ∀ j : Fin n, j ∈ xs → X j ∈ t.toKeyList) :
    activeHullSize X (splay t q) xs ≤
      activeHullSize X t xs + t.search_path_len q := by
  let newKeys := activeHullKeys X (splay t q) xs
  let oldKeys := activeHullKeys X t xs
  let qKeys := searchPathKeys t q
  have hbst_s : IsBST (splay t q) := splay_isBST t q hbst
  have hnew_nodup : newKeys.Nodup := by
    unfold newKeys
    exact activeHullKeys_nodup_of_isBST X xs hbst_s
  have hold_nodup : oldKeys.Nodup := by
    unfold oldKeys
    exact activeHullKeys_nodup_of_isBST X xs hbst
  have hq_nodup : qKeys.Nodup := by
    unfold qKeys
    exact searchPathKeys_nodup_of_isBST t q hbst
  have hnew_card : newKeys.toFinset.card = activeHullSize X (splay t q) xs := by
    unfold newKeys activeHullSize
    exact List.toFinset_card_of_nodup hnew_nodup
  have hold_card : oldKeys.toFinset.card = activeHullSize X t xs := by
    unfold oldKeys activeHullSize
    exact List.toFinset_card_of_nodup hold_nodup
  have hq_card : qKeys.toFinset.card = t.search_path_len q := by
    unfold qKeys
    rw [List.toFinset_card_of_nodup hq_nodup]
    exact searchPathKeys_length_eq_search_path_len t q
  have hsubset_card :
      newKeys.toFinset.card ≤
        (oldKeys.toFinset ∪ qKeys.toFinset).card := by
    apply Finset.card_le_card
    intro key hkey
    have hkey_new : key ∈ newKeys := by
      simpa [newKeys] using hkey
    rw [Finset.mem_union]
    rcases (mem_activeHullKeys_iff X (splay t q) xs).mp
        (by simpa [newKeys] using hkey_new) with
      ⟨_hkey_tree, j, hj, hpath⟩
    have hor :=
      searchPathKeys_splay_subset_union t q (X j) key
        hbst hq_mem (hmem_tail j hj) hpath
    rcases hor with hq_path | hj_path
    · right
      simpa [qKeys] using hq_path
    · left
      have hkey_old :
          key ∈ oldKeys := by
        unfold oldKeys
        exact mem_activeHullKeys_of_mem_searchPath X t xs hj hj_path
      simpa [oldKeys] using hkey_old
  have hunion_card :
      (oldKeys.toFinset ∪ qKeys.toFinset).card ≤
        oldKeys.toFinset.card + qKeys.toFinset.card :=
    Finset.card_union_le _ _
  omega

private theorem activeBudget_after_splay_le_path_add {n : Nat}
    (X : Fin n → Nat) {t : BinaryTree} (q : Nat)
    (xs : List (Fin n))
    (hbst : IsBST t)
    (hq_mem : q ∈ t.toKeyList)
    (hmem_tail : ∀ j : Fin n, j ∈ xs → X j ∈ t.toKeyList) :
    activeBudget X (splay t q) xs ≤
      activeBudget X t xs + (t.search_path_len q : ℝ) := by
  have hhull :=
    activeHullSize_after_splay_le_path_add X q xs hbst hq_mem hmem_tail
  have hnat :
      xs.length + activeHullSize X (splay t q) xs ≤
        xs.length + activeHullSize X t xs + t.search_path_len q := by
    omega
  unfold activeBudget
  exact_mod_cast hnat

private theorem root_mem_searchPathKeys_of_rootKey
    {t : BinaryTree} {q y : Nat} (hroot : rootKey t = some q) :
    q ∈ searchPathKeys t y := by
  cases t with
  | empty =>
      simp [rootKey] at hroot
  | node l k r =>
      simp [rootKey] at hroot
      subst k
      simp [searchPathKeys]

private theorem activeHullKeys_after_access_reset_sublist_cons {n : Nat}
    (X : Fin n → Nat) {t : BinaryTree} (q : Nat) (i : Fin n)
    (xs : List (Fin n))
    (hbst : IsBST t)
    (hroot : rootKey t = some q)
    (hi_mem : X i ∈ t.toKeyList)
    (hmem_tail : ∀ j : Fin n, j ∈ xs → X j ∈ t.toKeyList) :
    (activeHullKeys X (splay (splay t (X i)) q) xs).Sublist
      (activeHullKeys X t (i :: xs)) := by
  unfold activeHullKeys
  rw [splay_toKeyList, splay_toKeyList]
  apply filter_sublist_filter_of_imp
  intro key hkey
  simp at hkey ⊢
  rcases hkey with ⟨j, hj, hpath⟩
  have hq_mem_t : q ∈ t.toKeyList := rootKey_mem_toKeyList hroot
  have hq_mem_s : q ∈ (splay t (X i)).toKeyList := by
    rw [splay_toKeyList]
    exact hq_mem_t
  have hj_mem_s : X j ∈ (splay t (X i)).toKeyList := by
    rw [splay_toKeyList]
    exact hmem_tail j hj
  have hbst_s : IsBST (splay t (X i)) :=
    splay_isBST t (X i) hbst
  have hor_reset :=
    searchPathKeys_splay_subset_union (splay t (X i)) q (X j) key
      hbst_s hq_mem_s hj_mem_s hpath
  rcases hor_reset with hq_path | hj_path
  · have hor_q :=
      searchPathKeys_splay_subset_union t (X i) q key
        hbst hi_mem hq_mem_t hq_path
    rcases hor_q with hi_path | hroot_path
    · exact Or.inl hi_path
    · have hroot_key : key = q := by
        rw [searchPathKeys_eq_singleton_of_rootKey_eq_some hroot] at hroot_path
        simpa using hroot_path
      subst key
      exact Or.inl (root_mem_searchPathKeys_of_rootKey hroot)
  · have hor_j :=
      searchPathKeys_splay_subset_union t (X i) (X j) key
        hbst hi_mem (hmem_tail j hj) hj_path
    rcases hor_j with hi_path | hj_path_old
    · exact Or.inl hi_path
    · exact Or.inr ⟨j, hj, hj_path_old⟩

private theorem activeHullSize_after_access_reset_le_cons {n : Nat}
    (X : Fin n → Nat) {t : BinaryTree} (q : Nat) (i : Fin n)
    (xs : List (Fin n))
    (hbst : IsBST t)
    (hroot : rootKey t = some q)
    (hi_mem : X i ∈ t.toKeyList)
    (hmem_tail : ∀ j : Fin n, j ∈ xs → X j ∈ t.toKeyList) :
    activeHullSize X (splay (splay t (X i)) q) xs ≤
      activeHullSize X t (i :: xs) := by
  unfold activeHullSize
  exact List.Sublist.length_le
    (activeHullKeys_after_access_reset_sublist_cons
      X q i xs hbst hroot hi_mem hmem_tail)

private theorem activeBudget_after_access_reset_le_cons {n : Nat}
    (X : Fin n → Nat) {t : BinaryTree} (q : Nat) (i : Fin n)
    (xs : List (Fin n))
    (hbst : IsBST t)
    (hroot : rootKey t = some q)
    (hi_mem : X i ∈ t.toKeyList)
    (hmem_tail : ∀ j : Fin n, j ∈ xs → X j ∈ t.toKeyList) :
    activeBudget X (splay (splay t (X i)) q) xs ≤
      activeBudget X t (i :: xs) := by
  have hlen : xs.length ≤ (i :: xs).length := by simp
  have hhull :=
    activeHullSize_after_access_reset_le_cons
      X q i xs hbst hroot hi_mem hmem_tail
  unfold activeBudget
  exact_mod_cast Nat.add_le_add hlen hhull

private theorem length_le_activeBudget {n : Nat}
    (X : Fin n → Nat) (t : BinaryTree) (xs : List (Fin n)) :
    (xs.length : ℝ) ≤ activeBudget X t xs := by
  have hhull_nonneg : 0 ≤ (activeHullSize X t xs : ℝ) := by
    positivity
  unfold activeBudget
  nlinarith

private theorem finRange_length_le_activeBudget {n : Nat}
    (X : Fin n → Nat) (t : BinaryTree) :
    (n : ℝ) ≤ activeBudget X t (List.finRange n) := by
  simpa [List.length_finRange] using
    length_le_activeBudget X t (List.finRange n)

private theorem one_add_num_nodes_le_two_activeBudget_finRange {n : Nat}
    (X : Fin n → Nat) (init : BinaryTree)
    (hn : 0 < n) (h_size : init.num_nodes = n) :
    (1 + init.num_nodes : ℝ) ≤
      2 * activeBudget X init (List.finRange n) := by
  have hbudget := finRange_length_le_activeBudget X init
  have hnR : (1 : ℝ) ≤ n := by
    exact_mod_cast hn
  rw [h_size]
  nlinarith

private theorem search_path_len_real_le_activeBudget_of_mem {n : Nat}
    (X : Fin n → Nat) {t : BinaryTree} (xs : List (Fin n))
    (hbst : IsBST t) {i : Fin n} (hi : i ∈ xs) :
    (t.search_path_len (X i) : ℝ) ≤ activeBudget X t xs := by
  have hpath := search_path_len_real_le_activeHullSize_of_mem X xs hbst hi
  unfold activeBudget
  nlinarith [show 0 ≤ (xs.length : ℝ) by positivity]

private theorem activeBudget_le_length_add_num_nodes {n : Nat}
    (X : Fin n → Nat) (t : BinaryTree) (xs : List (Fin n)) :
    activeBudget X t xs ≤ (xs.length : ℝ) + t.num_nodes := by
  have hhull := activeHullSize_le_num_nodes X t xs
  unfold activeBudget
  exact_mod_cast Nat.add_le_add_left hhull xs.length

private theorem activeBudget_append_le {n : Nat}
    (X : Fin n → Nat) {t : BinaryTree} (xs ys : List (Fin n))
    (hbst : IsBST t) :
    activeBudget X t (xs ++ ys) ≤
      activeBudget X t xs + activeBudget X t ys := by
  have hhull := activeHullSize_append_le X xs ys hbst
  have hhullR :
      (activeHullSize X t (xs ++ ys) : ℝ) ≤
        activeHullSize X t xs + activeHullSize X t ys := by
    exact_mod_cast hhull
  unfold activeBudget
  simp [List.length_append]
  nlinarith

private theorem activeBudget_split_singleton_le {n : Nat}
    (X : Fin n → Nat) {t : BinaryTree}
    (xs ys : List (Fin n)) (i : Fin n)
    (hbst : IsBST t) :
    activeBudget X t (xs ++ [i] ++ ys) ≤
      activeBudget X t xs + activeBudget X t ys +
        (1 + t.num_nodes : ℝ) := by
  have hmain :
      activeBudget X t (xs ++ ([i] ++ ys)) ≤
        activeBudget X t xs + activeBudget X t ([i] ++ ys) :=
    activeBudget_append_le X xs ([i] ++ ys) hbst
  have htail :
      activeBudget X t ([i] ++ ys) ≤
        activeBudget X t [i] + activeBudget X t ys :=
    activeBudget_append_le X [i] ys hbst
  have hsingle :
      activeBudget X t [i] ≤ (1 : ℝ) + t.num_nodes := by
    simpa using activeBudget_le_length_add_num_nodes X t [i]
  rw [List.append_assoc]
  nlinarith

private theorem activeHullKeys_map_comp {n m : Nat}
    (X : Fin n → Nat) (g : Fin m → Fin n)
    (t : BinaryTree) (xs : List (Fin m)) :
    activeHullKeys X t (xs.map g) =
      activeHullKeys (fun i : Fin m => X (g i)) t xs := by
  unfold activeHullKeys
  apply List.filter_congr
  intro key _hkey
  have hiff :
      (∃ j : Fin n, j ∈ xs.map g ∧ key ∈ searchPathKeys t (X j)) ↔
        ∃ i : Fin m, i ∈ xs ∧
          key ∈ searchPathKeys t ((fun i : Fin m => X (g i)) i) := by
    constructor
    · rintro ⟨j, hj, hpath⟩
      rcases List.mem_map.mp hj with ⟨i, hi, hgi⟩
      subst j
      exact ⟨i, hi, hpath⟩
    · rintro ⟨i, hi, hpath⟩
      exact ⟨g i, List.mem_map.mpr ⟨i, hi, rfl⟩, hpath⟩
  by_cases hp :
      ∃ j : Fin n, j ∈ xs.map g ∧ key ∈ searchPathKeys t (X j)
  · have hq :
        ∃ i : Fin m, i ∈ xs ∧
          key ∈ searchPathKeys t ((fun i : Fin m => X (g i)) i) :=
      hiff.mp hp
    simp [hq]
  · have hq :
        ¬ (∃ i : Fin m, i ∈ xs ∧
          key ∈ searchPathKeys t ((fun i : Fin m => X (g i)) i)) := by
      intro hq
      exact hp (hiff.mpr hq)
    simp [hq]

private theorem activeHullSize_map_comp {n m : Nat}
    (X : Fin n → Nat) (g : Fin m → Fin n)
    (t : BinaryTree) (xs : List (Fin m)) :
    activeHullSize X t (xs.map g) =
      activeHullSize (fun i : Fin m => X (g i)) t xs := by
  unfold activeHullSize
  rw [activeHullKeys_map_comp X g t xs]

private theorem activeBudget_map_comp {n m : Nat}
    (X : Fin n → Nat) (g : Fin m → Fin n)
    (t : BinaryTree) (xs : List (Fin m)) :
    activeBudget X t (xs.map g) =
      activeBudget (fun i : Fin m => X (g i)) t xs := by
  unfold activeBudget
  rw [List.length_map, activeHullSize_map_comp X g t xs]

private def splayTreeAfter {n : Nat} (X : Fin n → Nat) :
    BinaryTree → List (Fin n) → BinaryTree
| t, [] => t
| t, i :: xs => splayTreeAfter X (splay t (X i)) xs

private theorem splayTreeAfter_append {n : Nat} (X : Fin n → Nat) :
    ∀ (xs ys : List (Fin n)) (t : BinaryTree),
      splayTreeAfter X t (xs ++ ys) =
        splayTreeAfter X (splayTreeAfter X t xs) ys
| [], ys, t => by
    simp [splayTreeAfter]
| i :: xs, ys, t => by
    simp [splayTreeAfter, splayTreeAfter_append X xs ys (splay t (X i))]

private theorem splayTreeAfter_map_comp {n m : Nat}
    (X : Fin n → Nat) (g : Fin m → Fin n) :
    ∀ (xs : List (Fin m)) (t : BinaryTree),
      splayTreeAfter X t (xs.map g) =
        splayTreeAfter (fun i : Fin m => X (g i)) t xs
| [], t => by
    simp [splayTreeAfter]
| i :: xs, t => by
    simp [splayTreeAfter,
      splayTreeAfter_map_comp X g xs (splay t (X (g i)))]

private theorem splayPathSum_append {n : Nat} (X : Fin n → Nat) :
    ∀ (xs ys : List (Fin n)) (t : BinaryTree),
      splayPathSum X t (xs ++ ys) =
        splayPathSum X t xs +
          splayPathSum X (splayTreeAfter X t xs) ys
| [], ys, t => by
    simp [splayPathSum, splayTreeAfter]
| i :: xs, ys, t => by
    simp [splayPathSum, splayTreeAfter,
      splayPathSum_append X xs ys (splay t (X i))]
    ring

private theorem splayPathSumWithFinal_eq_pathSum_add_final {n : Nat}
    (X : Fin n → Nat) (q : Nat) :
    ∀ (xs : List (Fin n)) (t : BinaryTree),
      splayPathSumWithFinal X q t xs =
        splayPathSum X t xs +
          (splayTreeAfter X t xs).search_path_len q
| [], t => by
    simp [splayPathSumWithFinal, splayPathSum, splayTreeAfter]
| i :: xs, t => by
    simp [splayPathSumWithFinal, splayPathSum, splayTreeAfter,
      splayPathSumWithFinal_eq_pathSum_add_final X q xs
        (splay t (X i))]
    ring

private theorem splayPathSumWithFinal_append {n : Nat}
    (X : Fin n → Nat) (q : Nat) :
    ∀ (xs ys : List (Fin n)) (t : BinaryTree),
      splayPathSumWithFinal X q t (xs ++ ys) =
        splayPathSum X t xs +
          splayPathSumWithFinal X q
            (splayTreeAfter X t xs) ys
| [], ys, t => by
    simp [splayPathSum, splayTreeAfter]
| i :: xs, ys, t => by
    simp [splayPathSumWithFinal, splayPathSum, splayTreeAfter,
      splayPathSumWithFinal_append X q xs ys (splay t (X i))]
    ring

private theorem splayPathSumWithFinal_map_comp {n m : Nat}
    (X : Fin n → Nat) (g : Fin m → Fin n) (q : Nat) :
    ∀ (xs : List (Fin m)) (t : BinaryTree),
      splayPathSumWithFinal X q t (xs.map g) =
        splayPathSumWithFinal (fun i : Fin m => X (g i)) q t xs
| [], t => by
    simp [splayPathSumWithFinal]
| i :: xs, t => by
    simp [splayPathSumWithFinal,
      splayPathSumWithFinal_map_comp X g q xs
        (splay t (X (g i)))]

private theorem splayTreeAfter_singleton {n : Nat}
    (X : Fin n → Nat) (t : BinaryTree) (i : Fin n) :
    splayTreeAfter X t [i] = splay t (X i) := by
  simp [splayTreeAfter]

private theorem splayPathSum_split_singleton {n : Nat}
    (X : Fin n → Nat) :
    ∀ (xs ys : List (Fin n)) (t : BinaryTree) (i : Fin n),
      splayPathSum X t (xs ++ [i] ++ ys) =
        splayPathSum X t xs +
          ((splayTreeAfter X t xs).search_path_len (X i) +
            splayPathSum X
              (splay (splayTreeAfter X t xs) (X i)) ys)
| xs, ys, t, i => by
    rw [List.append_assoc]
    rw [splayPathSum_append X xs ([i] ++ ys) t]
    simp [splayPathSum]

private theorem splayTreeAfter_split_singleton {n : Nat}
    (X : Fin n → Nat) :
    ∀ (xs ys : List (Fin n)) (t : BinaryTree) (i : Fin n),
      splayTreeAfter X t (xs ++ [i] ++ ys) =
        splayTreeAfter X
          (splay (splayTreeAfter X t xs) (X i)) ys
| xs, ys, t, i => by
    rw [List.append_assoc]
    rw [splayTreeAfter_append X xs ([i] ++ ys) t]
    simp [splayTreeAfter]

private def tailSeq {n : Nat} (X : Fin (n + 1) → Nat) : Fin n → Nat :=
  fun i => X (Fin.succ i)

private theorem fold_splayStep_map_succ_tailSeq {n : Nat}
    (X : Fin (n + 1) → Nat) :
    ∀ (xs : List (Fin n)) (acc : BinaryTree × ℝ),
      (xs.map Fin.succ).foldl (splayStep X) acc =
        xs.foldl (splayStep (tailSeq X)) acc
| [], acc => by
    simp
| i :: xs, acc => by
    cases acc with
    | mk t c =>
        simp [splayStep, tailSeq,
          fold_splayStep_map_succ_tailSeq X xs
            (splay t (X (Fin.succ i)), c + splay.cost t (X (Fin.succ i)))]

private theorem fold_splayStep_cost_offset {n : Nat}
    (X : Fin n → Nat) :
    ∀ (xs : List (Fin n)) (t : BinaryTree) (c0 d : ℝ),
      (xs.foldl (splayStep X) (t, c0 + d)).2 =
        d + (xs.foldl (splayStep X) (t, c0)).2
| [], t, c0, d => by
    simp
    ring
| i :: xs, t, c0, d => by
    dsimp [List.foldl, splayStep]
    have ih := fold_splayStep_cost_offset X xs
      (splay t (X i)) (c0 + splay.cost t (X i)) d
    simpa [add_assoc, add_comm, add_left_comm] using ih

private theorem sequence_cost_finRange_succ {n : Nat}
    (X : Fin (n + 1) → Nat) (init : BinaryTree) :
    splay.sequence_cost init X =
      splay.cost init (X 0) +
        splay.sequence_cost (splay init (X 0)) (tailSeq X) := by
  unfold splay.sequence_cost
  rw [List.finRange_succ]
  simp only [List.foldl]
  have hmap :=
    congrArg Prod.snd
      (fold_splayStep_map_succ_tailSeq X (List.finRange n)
        (splay init (X 0), 0 + splay.cost init (X 0)))
  have hoff :=
    fold_splayStep_cost_offset (tailSeq X) (List.finRange n)
      (splay init (X 0)) 0 (splay.cost init (X 0))
  exact (by
    simpa [splayStep, tailSeq, zero_add] using hmap.trans hoff)

private theorem splayPathSum_map_succ_tailSeq {n : Nat}
    (X : Fin (n + 1) → Nat) :
    ∀ (xs : List (Fin n)) (t : BinaryTree),
      splayPathSum X t (xs.map Fin.succ) =
        splayPathSum (tailSeq X) t xs
| [], t => by
    simp [splayPathSum]
| i :: xs, t => by
    simp [splayPathSum, tailSeq,
      splayPathSum_map_succ_tailSeq X xs (splay t (X (Fin.succ i)))]

private theorem splayPathSum_map_comp {n m : Nat}
    (X : Fin n → Nat) (g : Fin m → Fin n) :
    ∀ (xs : List (Fin m)) (t : BinaryTree),
      splayPathSum X t (xs.map g) =
        splayPathSum (fun i : Fin m => X (g i)) t xs
| [], t => by
    simp [splayPathSum]
| i :: xs, t => by
    simp [splayPathSum,
      splayPathSum_map_comp X g xs (splay t (X (g i)))]

private theorem splayPathSum_finRange_succ {n : Nat}
    (X : Fin (n + 1) → Nat) (init : BinaryTree) :
    splayPathSum X init (List.finRange (n + 1)) =
      init.search_path_len (X 0) +
        splayPathSum (tailSeq X) (splay init (X 0)) (List.finRange n) := by
  rw [List.finRange_succ]
  simp [splayPathSum, splayPathSum_map_succ_tailSeq X]

private theorem splayTreeAfter_num_nodes {n : Nat} (X : Fin n → Nat) :
    ∀ (xs : List (Fin n)) (t : BinaryTree),
      (splayTreeAfter X t xs).num_nodes = t.num_nodes
| [], t => by
    simp [splayTreeAfter]
| i :: xs, t => by
    simp [splayTreeAfter, splayTreeAfter_num_nodes X xs (splay t (X i)),
      splay_num_nodes]

private theorem splayPathSumWithFinal_le_pathSum_add_num_nodes {n : Nat}
    (X : Fin n → Nat) (q : Nat)
    (xs : List (Fin n)) (t : BinaryTree) :
    splayPathSumWithFinal X q t xs ≤
      splayPathSum X t xs + t.num_nodes := by
  rw [splayPathSumWithFinal_eq_pathSum_add_final X q xs t]
  have hpath :=
    search_path_len_le_num_nodes (splayTreeAfter X t xs) q
  have hnodes :=
    splayTreeAfter_num_nodes X xs t
  have hpathR :
      ((splayTreeAfter X t xs).search_path_len q : ℝ) ≤
        t.num_nodes := by
    rw [hnodes] at hpath
    exact_mod_cast hpath
  nlinarith

private theorem splayTreeAfter_toKeyList {n : Nat} (X : Fin n → Nat) :
    ∀ (xs : List (Fin n)) (t : BinaryTree),
      (splayTreeAfter X t xs).toKeyList = t.toKeyList
| [], t => by
    simp [splayTreeAfter]
| i :: xs, t => by
    simp [splayTreeAfter, splayTreeAfter_toKeyList X xs (splay t (X i)),
      splay_toKeyList]

private theorem splayTreeAfter_isBST {n : Nat} (X : Fin n → Nat) :
    ∀ (xs : List (Fin n)) (t : BinaryTree),
      IsBST t → IsBST (splayTreeAfter X t xs)
| [], t, hbst => by
    simpa [splayTreeAfter] using hbst
| i :: xs, t, hbst => by
    simp [splayTreeAfter]
    exact splayTreeAfter_isBST X xs (splay t (X i))
      (splay_isBST t (X i) hbst)

private noncomputable def splayActiveBudgetSum {n : Nat}
    (X : Fin n → Nat) : BinaryTree → List (Fin n) → ℝ
| _t, [] => 0
| t, i :: xs =>
    activeBudget X t (i :: xs) +
      splayActiveBudgetSum X (splay t (X i)) xs

private theorem splayPathSum_le_activeBudgetSum {n : Nat}
    (X : Fin n → Nat) :
    ∀ (xs : List (Fin n)) (t : BinaryTree),
      IsBST t →
      splayPathSum X t xs ≤ splayActiveBudgetSum X t xs
| [], t, _hbst => by
    simp [splayPathSum, splayActiveBudgetSum]
| i :: xs, t, hbst => by
    have hstep :=
      search_path_len_real_le_activeBudget_of_mem X (i :: xs) hbst
        (i := i) (by simp)
    have ih :=
      splayPathSum_le_activeBudgetSum X xs (splay t (X i))
        (splay_isBST t (X i) hbst)
    simp [splayPathSum, splayActiveBudgetSum]
    nlinarith

private theorem splayPathSum_le_num_nodes_mul_length {n : Nat}
    (X : Fin n → Nat) :
    ∀ (xs : List (Fin n)) (t : BinaryTree),
      splayPathSum X t xs ≤ (t.num_nodes : ℝ) * xs.length
| [], t => by
    simp [splayPathSum]
| i :: xs, t => by
    have ih := splayPathSum_le_num_nodes_mul_length X xs (splay t (X i))
    have hstep := search_path_len_le_num_nodes t (X i)
    have hstepR : (t.search_path_len (X i) : ℝ) ≤ t.num_nodes := by
      exact_mod_cast hstep
    change
      ↑(t.search_path_len (X i)) + splayPathSum X (splay t (X i)) xs ≤
        (t.num_nodes : ℝ) * ((i :: xs).length)
    rw [splay_num_nodes] at ih
    calc
      ↑(t.search_path_len (X i)) + splayPathSum X (splay t (X i)) xs
          ≤ (t.num_nodes : ℝ) + (t.num_nodes : ℝ) * xs.length := by
            nlinarith [hstepR, ih]
      _ = (t.num_nodes : ℝ) * ((i :: xs).length) := by
            simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
            ring

private theorem fold_splayStep_bound {n : Nat} (X : Fin n → Nat) :
    ∀ (xs : List (Fin n)) (t : BinaryTree) (c0 : ℝ),
      ((xs.foldl (splayStep X) (t, c0)).2 ≤
          c0 + (t.num_nodes : ℝ) * xs.length) ∧
        ((xs.foldl (splayStep X) (t, c0)).1.num_nodes = t.num_nodes)
| [], t, c0 => by
    simp
| i :: xs, t, c0 => by
    dsimp [List.foldl, splayStep]
    have ih := fold_splayStep_bound X xs (splay t (X i))
      (c0 + splay.cost t (X i))
    rcases ih with ⟨hcosts, hnodes⟩
    constructor
    · calc
        (xs.foldl (splayStep X)
            (splay t (X i), c0 + splay.cost t (X i))).2
            ≤ c0 + splay.cost t (X i) +
                ((splay t (X i)).num_nodes : ℝ) * xs.length := hcosts
        _ ≤ c0 + (t.num_nodes : ℝ) +
              (t.num_nodes : ℝ) * xs.length := by
            rw [splay_num_nodes]
            nlinarith [splay_cost_le_num_nodes t (X i)]
        _ = c0 + (t.num_nodes : ℝ) * (i :: xs).length := by
            simp
            ring
    · rw [hnodes, splay_num_nodes]

private theorem fold_splayStep_toKeyList {n : Nat} (X : Fin n → Nat) :
    ∀ (xs : List (Fin n)) (t : BinaryTree) (c0 : ℝ),
      ((xs.foldl (splayStep X) (t, c0)).1.toKeyList = t.toKeyList)
| [], t, c0 => by
    simp
| i :: xs, t, c0 => by
    dsimp [List.foldl, splayStep]
    rw [fold_splayStep_toKeyList X xs (splay t (X i))
      (c0 + splay.cost t (X i)), splay_toKeyList]

private theorem fold_splayStep_isBST {n : Nat} (X : Fin n → Nat) :
    ∀ (xs : List (Fin n)) (t : BinaryTree) (c0 : ℝ),
      IsBST t → IsBST ((xs.foldl (splayStep X) (t, c0)).1)
| [], t, c0, hbst => by
    simpa using hbst
| i :: xs, t, c0, hbst => by
    dsimp [List.foldl, splayStep]
    exact fold_splayStep_isBST X xs (splay t (X i))
      (c0 + splay.cost t (X i)) (splay_isBST t (X i) hbst)

private theorem fold_splayStep_cost_add_length_eq_pathSum {n : Nat}
    (X : Fin n → Nat) :
    ∀ (xs : List (Fin n)) (t : BinaryTree) (c0 : ℝ),
      (∀ i : Fin n, i ∈ xs → X i ∈ t.toKeyList) →
      ((xs.foldl (splayStep X) (t, c0)).2 + (xs.length : ℝ) =
        c0 + splayPathSum X t xs)
| [], t, c0, _hmem => by
    simp [splayPathSum]
| i :: xs, t, c0, hmem => by
    dsimp [List.foldl, splayStep, splayPathSum]
    have hi_mem : X i ∈ t.toKeyList := hmem i (by simp)
    have hcost_path :=
      splay_cost_add_one_eq_search_path_len_of_mem t (X i) hi_mem
    have hmem_tail : ∀ j : Fin n, j ∈ xs →
        X j ∈ (splay t (X i)).toKeyList := by
      intro j hj
      rw [splay_toKeyList]
      exact hmem j (by simp [hj])
    have ih := fold_splayStep_cost_add_length_eq_pathSum X xs
      (splay t (X i)) (c0 + splay.cost t (X i)) hmem_tail
    calc
      (xs.foldl (splayStep X)
          (splay t (X i), c0 + splay.cost t (X i))).2 +
          ((i :: xs).length : ℝ)
          = ((xs.foldl (splayStep X)
              (splay t (X i), c0 + splay.cost t (X i))).2 +
              (xs.length : ℝ)) + 1 := by
              simp
              ring
      _ = (c0 + splay.cost t (X i) +
            splayPathSum X (splay t (X i)) xs) + 1 := by
              rw [ih]
      _ = c0 + ↑(t.search_path_len (X i)) +
            splayPathSum X (splay t (X i)) xs := by
              linarith
      _ = c0 + (↑(t.search_path_len (X i)) +
            splayPathSum X (splay t (X i)) xs) := by
              ring

private theorem sequence_cost_le_num_nodes_mul_length {n : Nat}
    (X : Fin n → Nat) (init : BinaryTree) :
    splay.sequence_cost init X ≤ (init.num_nodes : ℝ) * n := by
  have h := (fold_splayStep_bound X (List.finRange n) init 0).1
  simpa [splay.sequence_cost] using h

private theorem sequence_cost_add_length_eq_pathSum {n : Nat}
    (X : Fin n → Nat) (init : BinaryTree)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList) :
    splay.sequence_cost init X + (n : ℝ) =
      splayPathSum X init (List.finRange n) := by
  have h := fold_splayStep_cost_add_length_eq_pathSum X
    (List.finRange n) init 0 (by
      intro i _hi
      exact hmem i)
  simpa [splay.sequence_cost] using h

private theorem sequence_cost_const_le_num_nodes {n : Nat}
    (X : Fin n → Nat) (init : BinaryTree) (q : Nat)
    (hbst : IsBST init) (hmemq : q ∈ init.toKeyList)
    (hconst : ∀ i : Fin n, X i = q) :
    splay.sequence_cost init X ≤ init.num_nodes := by
  have hmem : ∀ i : Fin n, X i ∈ init.toKeyList := by
    intro i
    rw [hconst i]
    exact hmemq
  have hcost_path := sequence_cost_add_length_eq_pathSum X init hmem
  have hpath :=
    splayPathSum_const_le_num_nodes_add_length X (List.finRange n)
      init q hbst hmemq (by
        intro i _hi
        exact hconst i)
  rw [List.length_finRange] at hpath
  nlinarith [hcost_path]

private theorem activeBudget_finRange_le_two_mul_size {n : Nat}
    (X : Fin n → Nat) (init : BinaryTree)
    (h_size : init.num_nodes = n) :
    activeBudget X init (List.finRange n) ≤ 2 * (n : ℝ) := by
  have hbudget :=
    activeBudget_le_length_add_num_nodes X init (List.finRange n)
  rw [List.length_finRange, h_size] at hbudget
  calc
    activeBudget X init (List.finRange n) ≤ (n : ℝ) + n := hbudget
    _ = 2 * (n : ℝ) := by ring

private theorem traversal_conjecture_of_activeBudget_path_bound
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ n, ∀ X : Fin n → Nat,
      (X avoids ![2, 3, 1]) →
      ∀ (init : BinaryTree), init.num_nodes = n → IsBST init →
      (∀ i : Fin n, (X i) ∈ init.toKeyList) →
      splayPathSum X init (List.finRange n) ≤
        K * activeBudget X init (List.finRange n)) :
    ∃ c, ∀ n, ∀ X : Fin n → Nat,
      (X avoids ![2, 3, 1]) →
      ∀ (init : BinaryTree), init.num_nodes = n → IsBST init →
      (∀ i : Fin n, (X i) ∈ init.toKeyList) →
      splay.sequence_cost init X ≤ c * n := by
  refine ⟨2 * K, ?_⟩
  intro n X havoid init h_size hbst hmem
  have hcost_path := sequence_cost_add_length_eq_pathSum X init hmem
  have hpath := hbound n X havoid init h_size hbst hmem
  have hbudget := activeBudget_finRange_le_two_mul_size X init h_size
  have hpath_linear :
      splayPathSum X init (List.finRange n) ≤ K * (2 * (n : ℝ)) := by
    exact le_trans hpath (mul_le_mul_of_nonneg_left hbudget hK)
  nlinarith [show 0 ≤ (n : ℝ) by positivity, hcost_path, hpath_linear]

private theorem traversal_conjecture_of_general_activeBudget_path_bound
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ n, ∀ X : Fin n → Nat,
      (X avoids ![2, 3, 1]) →
      ∀ (init : BinaryTree), IsBST init →
      (∀ i : Fin n, (X i) ∈ init.toKeyList) →
      splayPathSum X init (List.finRange n) ≤
        K * activeBudget X init (List.finRange n)) :
    ∃ c, ∀ n, ∀ X : Fin n → Nat,
      (X avoids ![2, 3, 1]) →
      ∀ (init : BinaryTree), init.num_nodes = n → IsBST init →
      (∀ i : Fin n, (X i) ∈ init.toKeyList) →
      splay.sequence_cost init X ≤ c * n := by
  exact traversal_conjecture_of_activeBudget_path_bound K hK
    (by
      intro n X havoid init _h_size hbst hmem
      exact hbound n X havoid init hbst hmem)

private theorem sequence_cost_le_sq_of_size {n : Nat}
    (X : Fin n → Nat) (init : BinaryTree)
    (h_size : init.num_nodes = n) :
    splay.sequence_cost init X ≤ (n : ℝ) * n := by
  have h := sequence_cost_le_num_nodes_mul_length X init
  rw [h_size] at h
  exact h

private theorem traversal_small_n_le_eight :
    ∀ n, n ≤ 8 → ∀ X : Fin n → Nat,
      ∀ (init : BinaryTree), init.num_nodes = n → IsBST init →
      (∀ i : Fin n, X i ∈ init.toKeyList) →
      splay.sequence_cost init X ≤ 8 * (n : ℝ) := by
  intro n hn X init h_size _hbst _hmem
  have hsq := sequence_cost_le_sq_of_size X init h_size
  have hnR : (n : ℝ) ≤ 8 := by
    exact_mod_cast hn
  nlinarith [show 0 ≤ (n : ℝ) by positivity]

private theorem splayPathSum_small_n_le_activeBudget
    (K : ℝ) (hK : 8 ≤ K) :
    ∀ n, n ≤ 8 → ∀ X : Fin n → Nat,
      ∀ (init : BinaryTree), init.num_nodes = n → IsBST init →
      (∀ i : Fin n, X i ∈ init.toKeyList) →
      splayPathSum X init (List.finRange n) ≤
        K * activeBudget X init (List.finRange n) := by
  intro n hn X init h_size _hbst _hmem
  have hpath :=
    splayPathSum_le_length_mul_num_nodes X (List.finRange n) init
  rw [List.length_finRange, h_size] at hpath
  have hnR : (n : ℝ) ≤ 8 := by
    exact_mod_cast hn
  have hbudget := finRange_length_le_activeBudget X init
  have hK_nonneg : 0 ≤ K := by nlinarith
  have hpath_active :
      splayPathSum X init (List.finRange n) ≤
        8 * activeBudget X init (List.finRange n) := by
    nlinarith [show 0 ≤ (n : ℝ) by positivity]
  have hbudget_nonneg :=
    activeBudget_nonneg X init (List.finRange n)
  exact le_trans hpath_active
    (mul_le_mul_of_nonneg_right hK hbudget_nonneg)

private theorem general_activeBudget_path_bound_of_induction
    (K : ℝ)
    (hsmall :
      ∀ n, n ≤ 8 → ∀ X : Fin n → Nat,
        (X avoids ![2, 3, 1]) →
        ∀ (init : BinaryTree), IsBST init →
        (∀ i : Fin n, X i ∈ init.toKeyList) →
        splayPathSum X init (List.finRange n) ≤
          K * activeBudget X init (List.finRange n))
    (hstep :
      ∀ n, 8 < n →
        (∀ k, k < n → ∀ X : Fin k → Nat,
          (X avoids ![2, 3, 1]) →
          ∀ (init : BinaryTree), IsBST init →
          (∀ i : Fin k, X i ∈ init.toKeyList) →
          splayPathSum X init (List.finRange k) ≤
            K * activeBudget X init (List.finRange k)) →
        ∀ X : Fin n → Nat,
          (X avoids ![2, 3, 1]) →
          ∀ (init : BinaryTree), IsBST init →
          (∀ i : Fin n, X i ∈ init.toKeyList) →
          splayPathSum X init (List.finRange n) ≤
            K * activeBudget X init (List.finRange n)) :
    ∀ n, ∀ X : Fin n → Nat,
      (X avoids ![2, 3, 1]) →
      ∀ (init : BinaryTree), IsBST init →
      (∀ i : Fin n, X i ∈ init.toKeyList) →
      splayPathSum X init (List.finRange n) ≤
        K * activeBudget X init (List.finRange n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro X havoid init hbst hmem
      by_cases hn : n ≤ 8
      · exact hsmall n hn X havoid init hbst hmem
      · have hn8 : 8 < n := Nat.lt_of_not_ge hn
        exact hstep n hn8 ih X havoid init hbst hmem

private theorem traversal_conjecture_of_activeBudget_induction
    (K : ℝ) (hK_nonneg : 0 ≤ K)
    (hsmall :
      ∀ n, n ≤ 8 → ∀ X : Fin n → Nat,
        (X avoids ![2, 3, 1]) →
        ∀ (init : BinaryTree), IsBST init →
        (∀ i : Fin n, X i ∈ init.toKeyList) →
        splayPathSum X init (List.finRange n) ≤
          K * activeBudget X init (List.finRange n))
    (hstep :
      ∀ n, 8 < n →
        (∀ k, k < n → ∀ X : Fin k → Nat,
          (X avoids ![2, 3, 1]) →
          ∀ (init : BinaryTree), IsBST init →
          (∀ i : Fin k, X i ∈ init.toKeyList) →
          splayPathSum X init (List.finRange k) ≤
            K * activeBudget X init (List.finRange k)) →
        ∀ X : Fin n → Nat,
          (X avoids ![2, 3, 1]) →
          ∀ (init : BinaryTree), IsBST init →
          (∀ i : Fin n, X i ∈ init.toKeyList) →
          splayPathSum X init (List.finRange n) ≤
            K * activeBudget X init (List.finRange n)) :
    ∃ c, ∀ n, ∀ X : Fin n → Nat,
      (X avoids ![2, 3, 1]) →
      ∀ (init : BinaryTree), init.num_nodes = n → IsBST init →
      (∀ i : Fin n, (X i) ∈ init.toKeyList) →
      splay.sequence_cost init X ≤ c * n := by
  exact traversal_conjecture_of_general_activeBudget_path_bound K hK_nonneg
    (general_activeBudget_path_bound_of_induction K hsmall hstep)

private theorem general_activeBudget_path_bound_le_one
    (K : ℝ) (hK : 1 ≤ K) :
    ∀ n, n ≤ 1 → ∀ X : Fin n → Nat,
      (X avoids ![2, 3, 1]) →
      ∀ (init : BinaryTree), IsBST init →
      (∀ i : Fin n, X i ∈ init.toKeyList) →
      splayPathSum X init (List.finRange n) ≤
        K * activeBudget X init (List.finRange n) := by
  intro n hn X _havoid init hbst _hmem
  cases n with
  | zero =>
      simp [splayPathSum, activeBudget, activeHullSize_nil]
  | succ n =>
      cases n with
      | zero =>
          have hpath :=
            search_path_len_real_le_activeBudget_of_mem X (List.finRange 1) hbst
              (i := (0 : Fin 1)) (by simp)
          have hbudget_nonneg :=
            activeBudget_nonneg X init (List.finRange 1)
          have hscale :
              activeBudget X init (List.finRange 1) ≤
                K * activeBudget X init (List.finRange 1) := by
            nlinarith
          simpa [splayPathSum, List.finRange_succ] using le_trans hpath hscale
      | succ n =>
          omega

private theorem second_access_bound_of_searchPathKeys_after_splay_subset
    (hsubset :
      ∀ (t : BinaryTree) (x y key : Nat),
        IsBST t → x ∈ t.toKeyList → y ∈ t.toKeyList →
        key ∈ searchPathKeys (splay t x) y →
          key ∈ searchPathKeys t x ∨ key ∈ searchPathKeys t y) :
      ∀ {n : Nat} (X : Fin n → Nat) (init : BinaryTree)
        (i j : Fin n), IsBST init →
        X i ∈ init.toKeyList → X j ∈ init.toKeyList →
        ((splay init (X i)).search_path_len (X j) : ℝ) ≤
          activeBudget X init [i, j] := by
  intro n X init i j hbst hi_mem hj_mem
  have hpath_nodup :
      (searchPathKeys (splay init (X i)) (X j)).Nodup :=
    searchPathKeys_nodup_of_isBST (splay init (X i)) (X j)
      (splay_isBST init (X i) hbst)
  have hhull_nodup :
      (activeHullKeys X init [i, j]).Nodup :=
    activeHullKeys_nodup_of_isBST X [i, j] hbst
  have hpath_card :
      (searchPathKeys (splay init (X i)) (X j)).toFinset.card =
        (searchPathKeys (splay init (X i)) (X j)).length :=
    List.toFinset_card_of_nodup hpath_nodup
  have hhull_card :
      (activeHullKeys X init [i, j]).toFinset.card =
        activeHullSize X init [i, j] := by
    unfold activeHullSize
    exact List.toFinset_card_of_nodup hhull_nodup
  have hcard :
      (searchPathKeys (splay init (X i)) (X j)).length ≤
        activeHullSize X init [i, j] := by
    rw [← hpath_card, ← hhull_card]
    apply Finset.card_le_card
    intro key hkey
    simp at hkey ⊢
    have hor :=
      hsubset init (X i) (X j) key hbst hi_mem hj_mem hkey
    rcases hor with hxi | hxj
    · exact mem_activeHullKeys_of_mem_searchPath X init [i, j]
        (i := i) (by simp) hxi
    · exact mem_activeHullKeys_of_mem_searchPath X init [i, j]
        (i := j) (by simp) hxj
  have hlen :
      (splay init (X i)).search_path_len (X j) ≤
        activeHullSize X init [i, j] := by
    rw [← searchPathKeys_length_eq_search_path_len]
    exact hcard
  have hlenR :
      (((splay init (X i)).search_path_len (X j) : Nat) : ℝ) ≤
        activeHullSize X init [i, j] := by
    exact_mod_cast hlen
  unfold activeBudget
  nlinarith [show 0 ≤ (([i, j] : List (Fin n)).length : ℝ) by positivity]

private theorem general_activeBudget_path_bound_le_two_of_second_access_bound
    (K : ℝ) (hK : 2 ≤ K)
    (hsecond :
      ∀ {n : Nat} (X : Fin n → Nat) (init : BinaryTree)
        (i j : Fin n), IsBST init →
        X i ∈ init.toKeyList → X j ∈ init.toKeyList →
        ((splay init (X i)).search_path_len (X j) : ℝ) ≤
          activeBudget X init [i, j]) :
    ∀ n, n ≤ 2 → ∀ X : Fin n → Nat,
      (X avoids ![2, 3, 1]) →
      ∀ (init : BinaryTree), IsBST init →
      (∀ i : Fin n, X i ∈ init.toKeyList) →
      splayPathSum X init (List.finRange n) ≤
        K * activeBudget X init (List.finRange n) := by
  intro n hn X havoid init hbst hmem
  by_cases hn1 : n ≤ 1
  · have hK1 : 1 ≤ K := by nlinarith
    exact general_activeBudget_path_bound_le_one K hK1
      n hn1 X havoid init hbst hmem
  · have hn2 : n = 2 := by omega
    subst n
    let i0 : Fin 2 := 0
    let i1 : Fin 2 := 1
    have hfirst :
        (init.search_path_len (X i0) : ℝ) ≤
          activeBudget X init (List.finRange 2) := by
      exact search_path_len_real_le_activeBudget_of_mem X
        (List.finRange 2) hbst (i := i0) (by simp [i0])
    have hsecond' :
        ((splay init (X i0)).search_path_len (X i1) : ℝ) ≤
          activeBudget X init (List.finRange 2) := by
      have h :=
        hsecond X init i0 i1 hbst (hmem i0) (hmem i1)
      simpa [List.finRange_succ, i0, i1] using h
    have hbudget_nonneg :=
      activeBudget_nonneg X init (List.finRange 2)
    have hpath :
        splayPathSum X init (List.finRange 2) =
          (init.search_path_len (X i0) : ℝ) +
            ((splay init (X i0)).search_path_len (X i1) : ℝ) := by
      simp [splayPathSum, List.finRange_succ, i0, i1]
    rw [hpath]
    nlinarith

private theorem general_activeBudget_path_bound_le_two_of_searchPathKeys_after_splay_subset
    (K : ℝ) (hK : 2 ≤ K)
    (hsubset :
      ∀ (t : BinaryTree) (x y key : Nat),
        IsBST t → x ∈ t.toKeyList → y ∈ t.toKeyList →
        key ∈ searchPathKeys (splay t x) y →
          key ∈ searchPathKeys t x ∨ key ∈ searchPathKeys t y) :
    ∀ n, n ≤ 2 → ∀ X : Fin n → Nat,
      (X avoids ![2, 3, 1]) →
      ∀ (init : BinaryTree), IsBST init →
      (∀ i : Fin n, X i ∈ init.toKeyList) →
      splayPathSum X init (List.finRange n) ≤
        K * activeBudget X init (List.finRange n) := by
  exact general_activeBudget_path_bound_le_two_of_second_access_bound
    K hK (second_access_bound_of_searchPathKeys_after_splay_subset hsubset)

private theorem general_activeBudget_path_bound_le_two
    (K : ℝ) (hK : 2 ≤ K) :
    ∀ n, n ≤ 2 → ∀ X : Fin n → Nat,
      (X avoids ![2, 3, 1]) →
      ∀ (init : BinaryTree), IsBST init →
      (∀ i : Fin n, X i ∈ init.toKeyList) →
      splayPathSum X init (List.finRange n) ≤
        K * activeBudget X init (List.finRange n) := by
  exact general_activeBudget_path_bound_le_two_of_searchPathKeys_after_splay_subset
    K hK searchPathKeys_splay_subset_union

private theorem general_activeBudget_path_bound_of_induction_le_two
    (K : ℝ)
    (hsmall :
      ∀ n, n ≤ 2 → ∀ X : Fin n → Nat,
        (X avoids ![2, 3, 1]) →
        ∀ (init : BinaryTree), IsBST init →
        (∀ i : Fin n, X i ∈ init.toKeyList) →
        splayPathSum X init (List.finRange n) ≤
          K * activeBudget X init (List.finRange n))
    (hstep :
      ∀ n, 2 < n →
        (∀ k, k < n → ∀ X : Fin k → Nat,
          (X avoids ![2, 3, 1]) →
          ∀ (init : BinaryTree), IsBST init →
          (∀ i : Fin k, X i ∈ init.toKeyList) →
          splayPathSum X init (List.finRange k) ≤
            K * activeBudget X init (List.finRange k)) →
        ∀ X : Fin n → Nat,
          (X avoids ![2, 3, 1]) →
          ∀ (init : BinaryTree), IsBST init →
          (∀ i : Fin n, X i ∈ init.toKeyList) →
          splayPathSum X init (List.finRange n) ≤
            K * activeBudget X init (List.finRange n)) :
    ∀ n, ∀ X : Fin n → Nat,
      (X avoids ![2, 3, 1]) →
      ∀ (init : BinaryTree), IsBST init →
      (∀ i : Fin n, X i ∈ init.toKeyList) →
      splayPathSum X init (List.finRange n) ≤
        K * activeBudget X init (List.finRange n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro X havoid init hbst hmem
      by_cases hn : n ≤ 2
      · exact hsmall n hn X havoid init hbst hmem
      · have hn2 : 2 < n := Nat.lt_of_not_ge hn
        exact hstep n hn2 ih X havoid init hbst hmem

private theorem traversal_conjecture_of_activeBudget_induction_le_two
    (K : ℝ) (hK_nonneg : 0 ≤ K)
    (hsmall :
      ∀ n, n ≤ 2 → ∀ X : Fin n → Nat,
        (X avoids ![2, 3, 1]) →
        ∀ (init : BinaryTree), IsBST init →
        (∀ i : Fin n, X i ∈ init.toKeyList) →
        splayPathSum X init (List.finRange n) ≤
          K * activeBudget X init (List.finRange n))
    (hstep :
      ∀ n, 2 < n →
        (∀ k, k < n → ∀ X : Fin k → Nat,
          (X avoids ![2, 3, 1]) →
          ∀ (init : BinaryTree), IsBST init →
          (∀ i : Fin k, X i ∈ init.toKeyList) →
          splayPathSum X init (List.finRange k) ≤
            K * activeBudget X init (List.finRange k)) →
        ∀ X : Fin n → Nat,
          (X avoids ![2, 3, 1]) →
          ∀ (init : BinaryTree), IsBST init →
          (∀ i : Fin n, X i ∈ init.toKeyList) →
          splayPathSum X init (List.finRange n) ≤
            K * activeBudget X init (List.finRange n)) :
    ∃ c, ∀ n, ∀ X : Fin n → Nat,
      (X avoids ![2, 3, 1]) →
      ∀ (init : BinaryTree), init.num_nodes = n → IsBST init →
      (∀ i : Fin n, (X i) ∈ init.toKeyList) →
      splay.sequence_cost init X ≤ c * n := by
  exact traversal_conjecture_of_general_activeBudget_path_bound K hK_nonneg
    (general_activeBudget_path_bound_of_induction_le_two K hsmall hstep)

private theorem finRange_split_at {n : Nat} (m : Fin n) :
    List.finRange n =
      (List.finRange n).take m.val ++ [m] ++
        (List.finRange n).drop (m.val + 1) := by
  have hlen : m.val < (List.finRange n).length := by
    simp [List.length_finRange, m.isLt]
  have hdrop := List.drop_eq_getElem_cons (l := List.finRange n) hlen
  have hget : (List.finRange n)[m.val] = m := by
    rw [List.getElem_finRange]
    exact Fin.ext (by simp)
  rw [hget] at hdrop
  calc
    List.finRange n =
        (List.finRange n).take m.val ++
          (List.finRange n).drop m.val := by
            rw [List.take_append_drop]
    _ = (List.finRange n).take m.val ++
          (m :: (List.finRange n).drop (m.val + 1)) := by
            rw [hdrop]
    _ = (List.finRange n).take m.val ++ [m] ++
          (List.finRange n).drop (m.val + 1) := by
            simp [List.append_assoc]

private theorem splayPathSum_finRange_split_at {n : Nat}
    (X : Fin n → Nat) (init : BinaryTree) (m : Fin n) :
    splayPathSum X init (List.finRange n) =
      splayPathSum X init ((List.finRange n).take m.val) +
        ((splayTreeAfter X init ((List.finRange n).take m.val)).search_path_len
            (X m) +
          splayPathSum X
            (splay
              (splayTreeAfter X init ((List.finRange n).take m.val))
              (X m))
            ((List.finRange n).drop (m.val + 1))) := by
  let pre := (List.finRange n).take m.val
  let suf := (List.finRange n).drop (m.val + 1)
  have hsplit : List.finRange n = pre ++ [m] ++ suf := by
    unfold pre suf
    exact finRange_split_at m
  change splayPathSum X init (List.finRange n) =
      splayPathSum X init pre +
        (↑((splayTreeAfter X init pre).search_path_len (X m)) +
          splayPathSum X (splay (splayTreeAfter X init pre) (X m)) suf)
  rw [hsplit]
  rw [List.append_assoc]
  rw [splayPathSum_append X pre ([m] ++ suf) init]
  simp [splayPathSum]

private theorem mem_take_finRange_lt {n : Nat} {m i : Fin n}
    (hmem : i ∈ (List.finRange n).take m.val) :
    i < m := by
  have hidx := (List.mem_take_iff_idxOf_lt
    (a := i) (n := m.val) (l := List.finRange n)
    (List.mem_finRange i)).mp hmem
  simpa [List.idxOf_finRange] using hidx

private theorem mem_drop_finRange_gt {n : Nat} {m i : Fin n}
    (hmem : i ∈ (List.finRange n).drop (m.val + 1)) :
    m < i := by
  rcases (List.mem_iff_getElem.mp hmem) with ⟨j, hj, hget⟩
  have hlen : m.val + 1 + j < (List.finRange n).length := by
    have hj' : j < n - (m.val + 1) := by
      simpa [List.length_drop, List.length_finRange] using hj
    have hm : m.val + 1 ≤ n := by omega
    have hnat : m.val + 1 + j < n := by omega
    simpa [List.length_finRange] using hnat
  have hfull :
      (List.finRange n)[m.val + 1 + j] = i := by
    rw [← hget]
    simp [List.getElem_drop]
  rw [List.getElem_finRange] at hfull
  have hval : m.val + 1 + j = i.val := by
    exact Fin.ext_iff.mp hfull
  change m.val < i.val
  omega

private theorem avoids_comp_strictMono
    {α β γ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ]
    {X : α → Nat} {P : γ → Nat} {g : β → α}
    (havoid : X avoids P) (hg : StrictMono g) :
    (fun b => X (g b)) avoids P := by
  intro hcontains
  rcases hcontains with ⟨f, hf, hcmp⟩
  exact havoid ⟨fun c => g (f c), hg.comp hf, hcmp⟩

private theorem tailSeq_avoids231 {n : Nat}
    {X : Fin (n + 1) → Nat} (havoid : X avoids ![2, 3, 1]) :
    tailSeq X avoids ![2, 3, 1] := by
  unfold tailSeq
  refine avoids_comp_strictMono havoid ?_
  intro i j hij
  change i.val + 1 < j.val + 1
  omega

private theorem tailSeq_mem {n : Nat}
    {X : Fin (n + 1) → Nat} {init : BinaryTree}
    (hmem : ∀ i : Fin (n + 1), X i ∈ init.toKeyList) :
    ∀ i : Fin n, tailSeq X i ∈ init.toKeyList := by
  intro i
  exact hmem (Fin.succ i)

private theorem tailSeq_mem_after_splay {n : Nat}
    {X : Fin (n + 1) → Nat} {init : BinaryTree}
    (hmem : ∀ i : Fin (n + 1), X i ∈ init.toKeyList) :
    ∀ i : Fin n, tailSeq X i ∈ (splay init (X 0)).toKeyList := by
  intro i
  rw [splay_toKeyList]
  exact tailSeq_mem hmem i

private theorem tailSeq_after_splay_hyps {n : Nat}
    {X : Fin (n + 1) → Nat} {init : BinaryTree}
    (havoid : X avoids ![2, 3, 1])
    (hbst : IsBST init)
    (hmem : ∀ i : Fin (n + 1), X i ∈ init.toKeyList) :
    (tailSeq X avoids ![2, 3, 1]) ∧
      (splay init (X 0)).num_nodes = init.num_nodes ∧
      IsBST (splay init (X 0)) ∧
      (∀ i : Fin n, tailSeq X i ∈ (splay init (X 0)).toKeyList) := by
  exact ⟨tailSeq_avoids231 havoid, splay_num_nodes init (X 0),
    splay_isBST init (X 0) hbst, tailSeq_mem_after_splay hmem⟩

private def prefixSeq {n : Nat} (X : Fin n → Nat) (m : Fin n) :
    Fin m.val → Nat :=
  fun i => X ⟨i.val, lt_trans i.isLt m.isLt⟩

private def prefixIndex {n : Nat} (m : Fin n) (i : Fin m.val) : Fin n :=
  ⟨i.val, lt_trans i.isLt m.isLt⟩

private theorem prefixSeq_apply {n : Nat} (X : Fin n → Nat)
    (m : Fin n) (i : Fin m.val) :
    prefixSeq X m i = X (prefixIndex m i) := rfl

private theorem prefixSeq_avoids231 {n : Nat} {X : Fin n → Nat}
    (havoid : X avoids ![2, 3, 1]) (m : Fin n) :
    prefixSeq X m avoids ![2, 3, 1] := by
  unfold prefixSeq
  refine avoids_comp_strictMono havoid ?_
  intro a b hab
  exact hab

private theorem prefixSeq_mem {n : Nat} {X : Fin n → Nat}
    {init : BinaryTree}
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList) (m : Fin n) :
    ∀ i : Fin m.val, prefixSeq X m i ∈ init.toKeyList := by
  intro i
  exact hmem ⟨i.val, lt_trans i.isLt m.isLt⟩

private def suffixSeq {n : Nat} (X : Fin n → Nat) (m : Fin n) :
    Fin (n - (m.val + 1)) → Nat :=
  fun i => X ⟨m.val + 1 + i.val, by
    have hm := m.isLt
    have hi := i.isLt
    omega⟩

private def suffixIndex {n : Nat} (m : Fin n)
    (i : Fin (n - (m.val + 1))) : Fin n :=
  ⟨m.val + 1 + i.val, by
    have hm := m.isLt
    have hi := i.isLt
    omega⟩

private theorem suffixSeq_apply {n : Nat} (X : Fin n → Nat)
    (m : Fin n) (i : Fin (n - (m.val + 1))) :
    suffixSeq X m i = X (suffixIndex m i) := rfl

private theorem suffixSeq_avoids231 {n : Nat} {X : Fin n → Nat}
    (havoid : X avoids ![2, 3, 1]) (m : Fin n) :
    suffixSeq X m avoids ![2, 3, 1] := by
  unfold suffixSeq
  refine avoids_comp_strictMono havoid ?_
  intro a b hab
  change m.val + 1 + a.val < m.val + 1 + b.val
  omega

private theorem suffixSeq_mem {n : Nat} {X : Fin n → Nat}
    {init : BinaryTree}
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList) (m : Fin n) :
    ∀ i : Fin (n - (m.val + 1)), suffixSeq X m i ∈ init.toKeyList := by
  intro i
  unfold suffixSeq
  exact hmem ⟨m.val + 1 + i.val, by
    have hm := m.isLt
    have hi := i.isLt
    omega⟩

private theorem suffixSeq_mem_after_prefix_pivot {n : Nat}
    {X : Fin n → Nat} {init : BinaryTree}
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList) (m : Fin n) :
    ∀ i : Fin (n - (m.val + 1)),
      suffixSeq X m i ∈
        (splay
          (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
          (X m)).toKeyList := by
  intro i
  rw [splay_toKeyList,
    splayTreeAfter_toKeyList (prefixSeq X m) (List.finRange m.val) init]
  exact suffixSeq_mem hmem m i

private theorem suffix_state_after_prefix_pivot_isBST {n : Nat}
    (X : Fin n → Nat) (init : BinaryTree) (m : Fin n)
    (hbst : IsBST init) :
    IsBST
      (splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m)) := by
  exact splay_isBST
    (splayTreeAfter (prefixSeq X m) init (List.finRange m.val)) (X m)
    (splayTreeAfter_isBST (prefixSeq X m) (List.finRange m.val) init hbst)

private theorem suffix_state_after_prefix_pivot_num_nodes {n : Nat}
    (X : Fin n → Nat) (init : BinaryTree) (m : Fin n) :
    (splay
      (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
      (X m)).num_nodes = init.num_nodes := by
  rw [splay_num_nodes,
    splayTreeAfter_num_nodes (prefixSeq X m) (List.finRange m.val) init]

private theorem suffixSeq_eq_pivot_or_mem_leftSubtree_after_prefix_pivot
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (hsuf_le :
      ∀ j : Fin (n - (m.val + 1)), suffixSeq X m j ≤ X m) :
    ∀ j : Fin (n - (m.val + 1)),
      suffixSeq X m j = X m ∨
        suffixSeq X m j ∈
          (leftSubtree
            (splay
              (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
              (X m))).toKeyList := by
  intro j
  let tp :=
    splayTreeAfter (prefixSeq X m) init (List.finRange m.val)
  let ts := splay tp (X m)
  have htp_bst : IsBST tp := by
    unfold tp
    exact splayTreeAfter_isBST (prefixSeq X m)
      (List.finRange m.val) init hbst
  have hpivot_mem_tp : X m ∈ tp.toKeyList := by
    unfold tp
    rw [splayTreeAfter_toKeyList (prefixSeq X m)
      (List.finRange m.val) init]
    exact hmem m
  have hroot : rootKey ts = some (X m) := by
    unfold ts
    exact splay_rootKey_eq_some_of_mem_isBST tp (X m)
      htp_bst hpivot_mem_tp
  have hts_bst : IsBST ts := by
    unfold ts
    exact splay_isBST tp (X m) htp_bst
  have hmem_ts : suffixSeq X m j ∈ ts.toKeyList := by
    unfold ts tp
    exact suffixSeq_mem_after_prefix_pivot hmem m j
  by_cases heq : suffixSeq X m j = X m
  · exact Or.inl heq
  · right
    have hlt : suffixSeq X m j < X m :=
      lt_of_le_of_ne (hsuf_le j) heq
    exact mem_leftSubtree_of_root_lt_isBST hts_bst hroot hmem_ts hlt

private theorem suffixSeq_mem_leftSubtree_after_prefix_pivot_of_strict
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (hsuf_lt :
      ∀ j : Fin (n - (m.val + 1)), suffixSeq X m j < X m) :
    ∀ j : Fin (n - (m.val + 1)),
      suffixSeq X m j ∈
        (leftSubtree
          (splay
            (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
            (X m))).toKeyList := by
  intro j
  rcases suffixSeq_eq_pivot_or_mem_leftSubtree_after_prefix_pivot
      hbst hmem (fun j => Nat.le_of_lt (hsuf_lt j)) j with heq | hmem_left
  · have hlt := hsuf_lt j
    omega
  · exact hmem_left

private def strictLowerSuffixIndices {n : Nat}
    (X : Fin n → Nat) (m : Fin n) :
    List (Fin (n - (m.val + 1))) :=
  (List.finRange (n - (m.val + 1))).filter
    (fun i => decide (suffixSeq X m i < X m))

private def strictLowerSuffixSeq {n : Nat}
    (X : Fin n → Nat) (m : Fin n) :
    Fin (strictLowerSuffixIndices X m).length → Nat :=
  fun i => suffixSeq X m ((strictLowerSuffixIndices X m)[i.val])

private def pivotSuffixIndices {n : Nat}
    (X : Fin n → Nat) (m : Fin n) :
    List (Fin (n - (m.val + 1))) :=
  (List.finRange (n - (m.val + 1))).filter
    (fun i => ! decide (suffixSeq X m i < X m))

private theorem mem_strictLowerSuffixIndices_iff {n : Nat}
    (X : Fin n → Nat) (m : Fin n)
    {i : Fin (n - (m.val + 1))} :
    i ∈ strictLowerSuffixIndices X m ↔ suffixSeq X m i < X m := by
  unfold strictLowerSuffixIndices
  simp

private theorem mem_pivotSuffixIndices_iff_not_lt {n : Nat}
    (X : Fin n → Nat) (m : Fin n)
    {i : Fin (n - (m.val + 1))} :
    i ∈ pivotSuffixIndices X m ↔ ¬ suffixSeq X m i < X m := by
  unfold pivotSuffixIndices
  simp

private theorem mem_pivotSuffixIndices_iff_eq {n : Nat}
    (X : Fin n → Nat) (m : Fin n)
    (hsuf_le :
      ∀ j : Fin (n - (m.val + 1)), suffixSeq X m j ≤ X m)
    {i : Fin (n - (m.val + 1))} :
    i ∈ pivotSuffixIndices X m ↔ suffixSeq X m i = X m := by
  rw [mem_pivotSuffixIndices_iff_not_lt]
  constructor
  · intro hnot
    have hle := hsuf_le i
    omega
  · intro heq
    rw [heq]
    omega

private theorem strictLowerSuffixSeq_lt_first_max {n : Nat}
    (X : Fin n → Nat) (m : Fin n)
    (i : Fin (strictLowerSuffixIndices X m).length) :
    strictLowerSuffixSeq X m i < X m := by
  unfold strictLowerSuffixSeq
  exact (mem_strictLowerSuffixIndices_iff X m).mp
    (List.getElem_mem i.isLt)

private theorem strictLowerSuffixIndices_length_le {n : Nat}
    (X : Fin n → Nat) (m : Fin n) :
    (strictLowerSuffixIndices X m).length ≤ n - (m.val + 1) := by
  unfold strictLowerSuffixIndices
  simpa [List.length_finRange] using
    List.length_filter_le
      (fun i : Fin (n - (m.val + 1)) =>
        decide (suffixSeq X m i < X m))
      (List.finRange (n - (m.val + 1)))

private theorem prefix_length_lt_of_fin {n : Nat} (m : Fin n) :
    m.val < n := m.isLt

private theorem suffix_length_lt_of_fin {n : Nat} (m : Fin n) :
    n - (m.val + 1) < n := by
  have hm : m.val < n := m.isLt
  omega

private theorem strictLowerSuffixIndices_length_lt {n : Nat}
    (X : Fin n → Nat) (m : Fin n) :
    (strictLowerSuffixIndices X m).length < n := by
  have hle := strictLowerSuffixIndices_length_le X m
  have hlt := suffix_length_lt_of_fin m
  omega

private theorem strictLowerSuffixIndices_get_lt_of_lt {n : Nat}
    (X : Fin n → Nat) (m : Fin n)
    {a b : Fin (strictLowerSuffixIndices X m).length} (hab : a < b) :
    (strictLowerSuffixIndices X m).get a <
      (strictLowerSuffixIndices X m).get b := by
  let inds := strictLowerSuffixIndices X m
  let N := n - (m.val + 1)
  have hsub : inds.Sublist (List.finRange N) := by
    unfold inds strictLowerSuffixIndices N
    exact List.filter_sublist
  rcases (List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub) with
    ⟨e, he⟩
  have hea := he a
  have heb := he b
  have he_lt : e a < e b := e.strictMono hab
  rw [hea, heb]
  exact (List.sortedLT_finRange N).getElem_lt_getElem_of_lt he_lt

private theorem strictLowerSuffixIndices_length_add_pivotSuffixIndices_length
    {n : Nat} (X : Fin n → Nat) (m : Fin n) :
    (strictLowerSuffixIndices X m).length +
        (pivotSuffixIndices X m).length =
      n - (m.val + 1) := by
  have h :=
    List.length_eq_length_filter_add
      (l := List.finRange (n - (m.val + 1)))
      (f := fun i : Fin (n - (m.val + 1)) =>
        decide (suffixSeq X m i < X m))
  unfold strictLowerSuffixIndices pivotSuffixIndices
  simpa [List.length_finRange, Bool.not_eq_true] using h.symm

private theorem pivotSuffixIndices_length_le {n : Nat}
    (X : Fin n → Nat) (m : Fin n) :
    (pivotSuffixIndices X m).length ≤ n - (m.val + 1) := by
  unfold pivotSuffixIndices
  simpa [List.length_finRange] using
    List.length_filter_le
      (fun i : Fin (n - (m.val + 1)) =>
        ! decide (suffixSeq X m i < X m))
      (List.finRange (n - (m.val + 1)))

private theorem leftSubtree_after_prefix_pivot_num_nodes_le {n : Nat}
    (X : Fin n → Nat) (init : BinaryTree) (m : Fin n) :
    (leftSubtree
      (splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m))).num_nodes ≤ init.num_nodes := by
  have hleft :=
    leftSubtree_num_nodes_le
      (splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m))
  rw [splay_num_nodes,
    splayTreeAfter_num_nodes (prefixSeq X m) (List.finRange m.val) init] at hleft
  exact hleft

private theorem strictLowerSuffixSeq_mem_init {n : Nat}
    {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList) :
    ∀ i : Fin (strictLowerSuffixIndices X m).length,
      strictLowerSuffixSeq X m i ∈ init.toKeyList := by
  intro i
  unfold strictLowerSuffixSeq
  exact suffixSeq_mem hmem m
    ((strictLowerSuffixIndices X m)[i.val])

private theorem strictLowerSuffixSeq_mem_after_prefix_pivot {n : Nat}
    {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList) :
    ∀ i : Fin (strictLowerSuffixIndices X m).length,
      strictLowerSuffixSeq X m i ∈
        (splay
          (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
          (X m)).toKeyList := by
  intro i
  unfold strictLowerSuffixSeq
  exact suffixSeq_mem_after_prefix_pivot hmem m
    ((strictLowerSuffixIndices X m)[i.val])

private theorem strictLowerSuffixSeq_mem_leftSubtree_after_prefix_pivot
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList) :
    ∀ i : Fin (strictLowerSuffixIndices X m).length,
      strictLowerSuffixSeq X m i ∈
        (leftSubtree
          (splay
            (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
            (X m))).toKeyList := by
  intro i
  let j : Fin (n - (m.val + 1)) :=
    (strictLowerSuffixIndices X m)[i.val]
  let tp :=
    splayTreeAfter (prefixSeq X m) init (List.finRange m.val)
  let ts := splay tp (X m)
  have hj_lt : suffixSeq X m j < X m := by
    exact (mem_strictLowerSuffixIndices_iff X m).mp
      (by
        unfold j
        exact List.getElem_mem i.isLt)
  have htp_bst : IsBST tp := by
    unfold tp
    exact splayTreeAfter_isBST (prefixSeq X m)
      (List.finRange m.val) init hbst
  have hpivot_mem_tp : X m ∈ tp.toKeyList := by
    unfold tp
    rw [splayTreeAfter_toKeyList (prefixSeq X m)
      (List.finRange m.val) init]
    exact hmem m
  have hroot : rootKey ts = some (X m) := by
    unfold ts
    exact splay_rootKey_eq_some_of_mem_isBST tp (X m)
      htp_bst hpivot_mem_tp
  have hts_bst : IsBST ts := by
    unfold ts
    exact splay_isBST tp (X m) htp_bst
  have hmem_ts : suffixSeq X m j ∈ ts.toKeyList := by
    unfold ts tp
    exact suffixSeq_mem_after_prefix_pivot hmem m j
  have hleft :=
    mem_leftSubtree_of_root_lt_isBST hts_bst hroot hmem_ts hj_lt
  simpa [strictLowerSuffixSeq, j, tp, ts] using hleft

private theorem strictLowerSuffixSeq_frameKeysAbove_pivot_after_prefix_pivot
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList) :
    ∀ i : Fin (strictLowerSuffixIndices X m).length,
      frameKeysAbove (strictLowerSuffixSeq X m i)
        [(X m,
          rightSubtree
            (splay
              (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
              (X m)))] := by
  intro i
  let tp :=
    splayTreeAfter (prefixSeq X m) init (List.finRange m.val)
  let ts := splay tp (X m)
  have htp_bst : IsBST tp := by
    unfold tp
    exact splayTreeAfter_isBST (prefixSeq X m)
      (List.finRange m.val) init hbst
  have hpivot_mem_tp : X m ∈ tp.toKeyList := by
    unfold tp
    rw [splayTreeAfter_toKeyList (prefixSeq X m)
      (List.finRange m.val) init]
    exact hmem m
  have hroot : rootKey ts = some (X m) := by
    unfold ts
    exact splay_rootKey_eq_some_of_mem_isBST tp (X m)
      htp_bst hpivot_mem_tp
  have hts_bst : IsBST ts := by
    unfold ts
    exact splay_isBST tp (X m) htp_bst
  have hleft :
      strictLowerSuffixSeq X m i ∈ (leftSubtree ts).toKeyList := by
    unfold ts tp
    exact strictLowerSuffixSeq_mem_leftSubtree_after_prefix_pivot
      hbst hmem i
  simpa [ts] using
    frameKeysAbove_singleton_of_mem_leftSubtree_root
      hts_bst hroot hleft

private theorem suffix_state_after_prefix_pivot_attachLeftFrames
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList) :
    attachLeftFrames
        (leftSubtree
          (splay
            (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
            (X m)))
        [(X m,
          rightSubtree
            (splay
              (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
              (X m)))] =
      splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m) := by
  let tp :=
    splayTreeAfter (prefixSeq X m) init (List.finRange m.val)
  let ts := splay tp (X m)
  have htp_bst : IsBST tp := by
    unfold tp
    exact splayTreeAfter_isBST (prefixSeq X m)
      (List.finRange m.val) init hbst
  have hpivot_mem_tp : X m ∈ tp.toKeyList := by
    unfold tp
    rw [splayTreeAfter_toKeyList (prefixSeq X m)
      (List.finRange m.val) init]
    exact hmem m
  have hroot : rootKey ts = some (X m) := by
    unfold ts
    exact splay_rootKey_eq_some_of_mem_isBST tp (X m)
      htp_bst hpivot_mem_tp
  simpa [tp, ts] using
    attachLeftFrames_left_right_of_rootKey hroot

private theorem strictLowerSuffixSeq_search_path_len_after_prefix_pivot_eq
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (i : Fin (strictLowerSuffixIndices X m).length) :
    (splay
      (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
      (X m)).search_path_len (strictLowerSuffixSeq X m i) =
      1 +
        (leftSubtree
          (splay
            (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
            (X m))).search_path_len (strictLowerSuffixSeq X m i) := by
  let ts :=
    splay
      (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
      (X m)
  have hframes :
      frameKeysAbove (strictLowerSuffixSeq X m i)
        [(X m, rightSubtree ts)] := by
    unfold ts
    exact strictLowerSuffixSeq_frameKeysAbove_pivot_after_prefix_pivot
      hbst hmem i
  have hpath :=
    search_path_len_attachLeftFrames_of_frameKeysAbove
      (leftSubtree ts) (strictLowerSuffixSeq X m i)
      [(X m, rightSubtree ts)] hframes
  have heq :
      attachLeftFrames (leftSubtree ts) [(X m, rightSubtree ts)] = ts := by
    unfold ts
    exact suffix_state_after_prefix_pivot_attachLeftFrames hbst hmem
  rw [heq] at hpath
  simpa [ts] using hpath

private theorem strictLowerSuffixSeq_pivot_reset_search_path_le
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (i : Fin (strictLowerSuffixIndices X m).length) :
    (splay
        (splay
          (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
          (X m))
        (strictLowerSuffixSeq X m i)).search_path_len (X m) ≤
      (splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m)).search_path_len (strictLowerSuffixSeq X m i) := by
  let tp :=
    splayTreeAfter (prefixSeq X m) init (List.finRange m.val)
  let ts := splay tp (X m)
  have htp_bst : IsBST tp := by
    unfold tp
    exact splayTreeAfter_isBST (prefixSeq X m)
      (List.finRange m.val) init hbst
  have hpivot_mem_tp : X m ∈ tp.toKeyList := by
    unfold tp
    rw [splayTreeAfter_toKeyList (prefixSeq X m)
      (List.finRange m.val) init]
    exact hmem m
  have hroot : rootKey ts = some (X m) := by
    unfold ts
    exact splay_rootKey_eq_some_of_mem_isBST tp (X m)
      htp_bst hpivot_mem_tp
  have hts_bst : IsBST ts := by
    unfold ts
    exact splay_isBST tp (X m) htp_bst
  have hleft_mem :
      strictLowerSuffixSeq X m i ∈ (leftSubtree ts).toKeyList := by
    unfold ts tp
    exact strictLowerSuffixSeq_mem_leftSubtree_after_prefix_pivot
      hbst hmem i
  change
    (splay ts (strictLowerSuffixSeq X m i)).search_path_len (X m) ≤
      ts.search_path_len (strictLowerSuffixSeq X m i)
  cases hts : ts with
  | empty =>
      simp [rootKey, hts] at hroot
  | node l k r =>
      simp [rootKey, hts] at hroot
      subst k
      have hbst_node : IsBST (BinaryTree.node l (X m) r) := by
        simpa [ts, hts] using hts_bst
      have hmem_l :
          strictLowerSuffixSeq X m i ∈ l.toKeyList := by
        simpa [ts, hts, leftSubtree] using hleft_mem
      simpa [hts] using
        search_path_len_pivot_after_splay_left_le
          (l := l) (r := r) (q := X m)
          (x := strictLowerSuffixSeq X m i)
          hbst_node hmem_l

private theorem strictLowerSuffixSeq_access_pivot_pair_path_le
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (i : Fin (strictLowerSuffixIndices X m).length) :
    let ts :=
      splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m)
    ts.search_path_len (strictLowerSuffixSeq X m i) +
        (splay ts (strictLowerSuffixSeq X m i)).search_path_len (X m) ≤
      2 * ts.search_path_len (strictLowerSuffixSeq X m i) := by
  let ts :=
    splay
      (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
      (X m)
  have hreset :=
    strictLowerSuffixSeq_pivot_reset_search_path_le
      hbst hmem i
  change
    (splay ts (strictLowerSuffixSeq X m i)).search_path_len (X m) ≤
      ts.search_path_len (strictLowerSuffixSeq X m i) at hreset
  change
    ts.search_path_len (strictLowerSuffixSeq X m i) +
        (splay ts (strictLowerSuffixSeq X m i)).search_path_len (X m) ≤
      2 * ts.search_path_len (strictLowerSuffixSeq X m i)
  omega

private theorem strictLowerSuffixSeq_rootKey_after_access_pivot_reset
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (i : Fin (strictLowerSuffixIndices X m).length) :
    let ts :=
      splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m)
    rootKey (splay (splay ts (strictLowerSuffixSeq X m i)) (X m)) =
      some (X m) := by
  let tp :=
    splayTreeAfter (prefixSeq X m) init (List.finRange m.val)
  let ts := splay tp (X m)
  have htp_bst : IsBST tp := by
    unfold tp
    exact splayTreeAfter_isBST (prefixSeq X m)
      (List.finRange m.val) init hbst
  have hpivot_mem_tp : X m ∈ tp.toKeyList := by
    unfold tp
    rw [splayTreeAfter_toKeyList (prefixSeq X m)
      (List.finRange m.val) init]
    exact hmem m
  have hroot_ts : rootKey ts = some (X m) := by
    unfold ts
    exact splay_rootKey_eq_some_of_mem_isBST tp (X m)
      htp_bst hpivot_mem_tp
  have hbst_ts : IsBST ts := by
    unfold ts
    exact splay_isBST tp (X m) htp_bst
  change
    rootKey (splay (splay ts (strictLowerSuffixSeq X m i)) (X m)) =
      some (X m)
  exact rootKey_after_pivot_reset_of_root hbst_ts hroot_ts

private theorem strictLowerSuffixSeq_mem_leftSubtree_after_access_pivot_reset
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (i j : Fin (strictLowerSuffixIndices X m).length) :
    let ts :=
      splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m)
    strictLowerSuffixSeq X m j ∈
      (leftSubtree
        (splay (splay ts (strictLowerSuffixSeq X m i)) (X m))).toKeyList := by
  let tp :=
    splayTreeAfter (prefixSeq X m) init (List.finRange m.val)
  let ts := splay tp (X m)
  have htp_bst : IsBST tp := by
    unfold tp
    exact splayTreeAfter_isBST (prefixSeq X m)
      (List.finRange m.val) init hbst
  have hpivot_mem_tp : X m ∈ tp.toKeyList := by
    unfold tp
    rw [splayTreeAfter_toKeyList (prefixSeq X m)
      (List.finRange m.val) init]
    exact hmem m
  have hroot_ts : rootKey ts = some (X m) := by
    unfold ts
    exact splay_rootKey_eq_some_of_mem_isBST tp (X m)
      htp_bst hpivot_mem_tp
  have hbst_ts : IsBST ts := by
    unfold ts
    exact splay_isBST tp (X m) htp_bst
  have hj_mem_ts : strictLowerSuffixSeq X m j ∈ ts.toKeyList := by
    unfold ts tp
    exact strictLowerSuffixSeq_mem_after_prefix_pivot hmem j
  have hj_lt : strictLowerSuffixSeq X m j < X m :=
    strictLowerSuffixSeq_lt_first_max X m j
  change
    strictLowerSuffixSeq X m j ∈
      (leftSubtree
        (splay (splay ts (strictLowerSuffixSeq X m i)) (X m))).toKeyList
  exact mem_leftSubtree_after_pivot_reset_of_lt
    hbst_ts hroot_ts hj_mem_ts hj_lt

private theorem strictLowerSuffixSeq_pivotResetPairPathSum_le_two_lowerPathSum
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList) :
    let ts :=
      splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m)
    pivotResetPairPathSum (strictLowerSuffixSeq X m) (X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) ≤
      2 *
        pivotResetLowerPathSum (strictLowerSuffixSeq X m) (X m) ts
          (List.finRange (strictLowerSuffixIndices X m).length) := by
  let tp :=
    splayTreeAfter (prefixSeq X m) init (List.finRange m.val)
  let ts := splay tp (X m)
  have htp_bst : IsBST tp := by
    unfold tp
    exact splayTreeAfter_isBST (prefixSeq X m)
      (List.finRange m.val) init hbst
  have hpivot_mem_tp : X m ∈ tp.toKeyList := by
    unfold tp
    rw [splayTreeAfter_toKeyList (prefixSeq X m)
      (List.finRange m.val) init]
    exact hmem m
  have hroot_ts : rootKey ts = some (X m) := by
    unfold ts
    exact splay_rootKey_eq_some_of_mem_isBST tp (X m)
      htp_bst hpivot_mem_tp
  have hbst_ts : IsBST ts := by
    unfold ts
    exact splay_isBST tp (X m) htp_bst
  have hmem_left :
      ∀ i : Fin (strictLowerSuffixIndices X m).length,
        i ∈ List.finRange (strictLowerSuffixIndices X m).length →
        strictLowerSuffixSeq X m i ∈ (leftSubtree ts).toKeyList := by
    intro i _hi
    unfold ts tp
    exact strictLowerSuffixSeq_mem_leftSubtree_after_prefix_pivot
      hbst hmem i
  change
    pivotResetPairPathSum (strictLowerSuffixSeq X m) (X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) ≤
      2 *
        pivotResetLowerPathSum (strictLowerSuffixSeq X m) (X m) ts
          (List.finRange (strictLowerSuffixIndices X m).length)
  exact pivotResetPairPathSum_le_two_lowerPathSum
    (strictLowerSuffixSeq X m) (X m)
    (List.finRange (strictLowerSuffixIndices X m).length)
    ts hbst_ts hroot_ts hmem_left

private theorem strictLowerSuffixSeq_mem_leftSubtree_after_pivotResetTreeAfter
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (xs : List (Fin (strictLowerSuffixIndices X m).length))
    (j : Fin (strictLowerSuffixIndices X m).length) :
    let ts :=
      splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m)
    strictLowerSuffixSeq X m j ∈
      (leftSubtree
        (pivotResetTreeAfter (strictLowerSuffixSeq X m) (X m) ts xs)).toKeyList := by
  let tp :=
    splayTreeAfter (prefixSeq X m) init (List.finRange m.val)
  let ts := splay tp (X m)
  have htp_bst : IsBST tp := by
    unfold tp
    exact splayTreeAfter_isBST (prefixSeq X m)
      (List.finRange m.val) init hbst
  have hpivot_mem_tp : X m ∈ tp.toKeyList := by
    unfold tp
    rw [splayTreeAfter_toKeyList (prefixSeq X m)
      (List.finRange m.val) init]
    exact hmem m
  have hroot_ts : rootKey ts = some (X m) := by
    unfold ts
    exact splay_rootKey_eq_some_of_mem_isBST tp (X m)
      htp_bst hpivot_mem_tp
  have hbst_ts : IsBST ts := by
    unfold ts
    exact splay_isBST tp (X m) htp_bst
  have hj_mem_ts : strictLowerSuffixSeq X m j ∈ ts.toKeyList := by
    unfold ts tp
    exact strictLowerSuffixSeq_mem_after_prefix_pivot hmem j
  have hj_lt : strictLowerSuffixSeq X m j < X m :=
    strictLowerSuffixSeq_lt_first_max X m j
  change
    strictLowerSuffixSeq X m j ∈
      (leftSubtree
        (pivotResetTreeAfter (strictLowerSuffixSeq X m) (X m) ts xs)).toKeyList
  exact pivotResetTreeAfter_mem_leftSubtree_of_lt
    (strictLowerSuffixSeq X m) (X m) xs ts
    (strictLowerSuffixSeq X m j) hbst_ts hroot_ts hj_mem_ts hj_lt

private theorem strictLowerSuffixSeq_avoids231 {n : Nat}
    {X : Fin n → Nat} (havoid : X avoids ![2, 3, 1])
    (m : Fin n) :
    strictLowerSuffixSeq X m avoids ![2, 3, 1] := by
  intro hcontains
  rcases hcontains with ⟨f, hf, hcmp⟩
  let inds := strictLowerSuffixIndices X m
  let N := n - (m.val + 1)
  have hsub : inds.Sublist (List.finRange N) := by
    unfold inds strictLowerSuffixIndices N
    exact List.filter_sublist
  rcases (List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub) with
    ⟨e, he⟩
  let g : Fin 3 → Fin N :=
    fun c => (List.finRange N).get (e (f c))
  have hg : StrictMono g := by
    intro a b hab
    have hef : e (f a) < e (f b) := by
      exact e.strictMono (hf hab)
    unfold g
    simpa [List.getElem_finRange] using hef
  have hval : ∀ c : Fin 3,
      strictLowerSuffixSeq X m (f c) = suffixSeq X m (g c) := by
    intro c
    unfold strictLowerSuffixSeq g inds
    exact congrArg (suffixSeq X m) (he (f c))
  have hcontains_suffix :
      contains_pattern (suffixSeq X m) (![2, 3, 1] : Fin 3 → Nat) := by
    refine ⟨g, hg, ?_⟩
    intro a b
    rw [← hval a, ← hval b]
    exact hcmp a b
  exact suffixSeq_avoids231 havoid m hcontains_suffix

private theorem splayPathSum_strictLowerSuffixIndices_eq {n : Nat}
    (X : Fin n → Nat) (m : Fin n) (init : BinaryTree) :
    splayPathSum (suffixSeq X m) init (strictLowerSuffixIndices X m) =
      splayPathSum (strictLowerSuffixSeq X m) init
        (List.finRange (strictLowerSuffixIndices X m).length) := by
  have hmap :=
    splayPathSum_map_comp (suffixSeq X m)
      (fun i : Fin (strictLowerSuffixIndices X m).length =>
        (strictLowerSuffixIndices X m).get i)
      (List.finRange (strictLowerSuffixIndices X m).length) init
  rw [List.map_get_finRange] at hmap
  simpa [strictLowerSuffixSeq] using hmap

private theorem splayPathSumWithFinal_strictLowerSuffixIndices_eq {n : Nat}
    (X : Fin n → Nat) (m : Fin n) (init : BinaryTree) :
    splayPathSumWithFinal (suffixSeq X m) (X m) init
        (strictLowerSuffixIndices X m) =
      splayPathSumWithFinal (strictLowerSuffixSeq X m) (X m) init
        (List.finRange (strictLowerSuffixIndices X m).length) := by
  have hmap :=
    splayPathSumWithFinal_map_comp (suffixSeq X m)
      (fun i : Fin (strictLowerSuffixIndices X m).length =>
        (strictLowerSuffixIndices X m).get i)
      (X m) (List.finRange (strictLowerSuffixIndices X m).length) init
  rw [List.map_get_finRange] at hmap
  simpa [strictLowerSuffixSeq] using hmap

private theorem splayTreeAfter_strictLowerSuffixIndices_eq {n : Nat}
    (X : Fin n → Nat) (m : Fin n) (init : BinaryTree) :
    splayTreeAfter (suffixSeq X m) init (strictLowerSuffixIndices X m) =
      splayTreeAfter (strictLowerSuffixSeq X m) init
        (List.finRange (strictLowerSuffixIndices X m).length) := by
  have hmap :=
    splayTreeAfter_map_comp (suffixSeq X m)
      (fun i : Fin (strictLowerSuffixIndices X m).length =>
        (strictLowerSuffixIndices X m).get i)
      (List.finRange (strictLowerSuffixIndices X m).length) init
  rw [List.map_get_finRange] at hmap
  simpa [strictLowerSuffixSeq] using hmap

private theorem activeBudget_strictLowerSuffixIndices_eq {n : Nat}
    (X : Fin n → Nat) (m : Fin n) (init : BinaryTree) :
    activeBudget (suffixSeq X m) init (strictLowerSuffixIndices X m) =
      activeBudget (strictLowerSuffixSeq X m) init
        (List.finRange (strictLowerSuffixIndices X m).length) := by
  have hmap :=
    activeBudget_map_comp (suffixSeq X m)
      (fun i : Fin (strictLowerSuffixIndices X m).length =>
        (strictLowerSuffixIndices X m).get i)
      init (List.finRange (strictLowerSuffixIndices X m).length)
  rw [List.map_get_finRange] at hmap
  simpa [strictLowerSuffixSeq] using hmap

private theorem pivotResetPairPathSum_strictLowerSuffixIndices_eq {n : Nat}
    (X : Fin n → Nat) (m : Fin n) (init : BinaryTree) :
    pivotResetPairPathSum (suffixSeq X m) (X m) init
        (strictLowerSuffixIndices X m) =
      pivotResetPairPathSum (strictLowerSuffixSeq X m) (X m) init
        (List.finRange (strictLowerSuffixIndices X m).length) := by
  have hmap :=
    pivotResetPairPathSum_map_comp (suffixSeq X m)
      (fun i : Fin (strictLowerSuffixIndices X m).length =>
        (strictLowerSuffixIndices X m).get i)
      (X m) (List.finRange (strictLowerSuffixIndices X m).length) init
  rw [List.map_get_finRange] at hmap
  simpa [strictLowerSuffixSeq] using hmap

private theorem pivotResetLowerPathSum_strictLowerSuffixIndices_eq {n : Nat}
    (X : Fin n → Nat) (m : Fin n) (init : BinaryTree) :
    pivotResetLowerPathSum (suffixSeq X m) (X m) init
        (strictLowerSuffixIndices X m) =
      pivotResetLowerPathSum (strictLowerSuffixSeq X m) (X m) init
        (List.finRange (strictLowerSuffixIndices X m).length) := by
  have hmap :=
    pivotResetLowerPathSum_map_comp (suffixSeq X m)
      (fun i : Fin (strictLowerSuffixIndices X m).length =>
        (strictLowerSuffixIndices X m).get i)
      (X m) (List.finRange (strictLowerSuffixIndices X m).length) init
  rw [List.map_get_finRange] at hmap
  simpa [strictLowerSuffixSeq] using hmap

private theorem suffixResetUpperPathSum_suffix_finRange_split {n : Nat}
    (X : Fin n → Nat) (m : Fin n) (init : BinaryTree) :
    suffixResetUpperPathSum (suffixSeq X m) (X m) init
        (List.finRange (n - (m.val + 1))) =
      pivotResetPairPathSum (strictLowerSuffixSeq X m) (X m) init
        (List.finRange (strictLowerSuffixIndices X m).length) +
      ((pivotSuffixIndices X m).length : ℝ) := by
  have hsplit :=
    suffixResetUpperPathSum_filter_split (suffixSeq X m) (X m)
      (List.finRange (n - (m.val + 1))) init
  rw [hsplit]
  change
    pivotResetPairPathSum (suffixSeq X m) (X m) init
        (strictLowerSuffixIndices X m) +
      ((pivotSuffixIndices X m).length : ℝ) =
    pivotResetPairPathSum (strictLowerSuffixSeq X m) (X m) init
        (List.finRange (strictLowerSuffixIndices X m).length) +
      ((pivotSuffixIndices X m).length : ℝ)
  rw [pivotResetPairPathSum_strictLowerSuffixIndices_eq X m init]

private theorem activeBudget_strictLowerSuffixIndices_le_finRange {n : Nat}
    (X : Fin n → Nat) (m : Fin n) (init : BinaryTree) :
    activeBudget (suffixSeq X m) init (strictLowerSuffixIndices X m) ≤
      activeBudget (suffixSeq X m) init
        (List.finRange (n - (m.val + 1))) := by
  apply activeBudget_sublist_le
  unfold strictLowerSuffixIndices
  exact List.filter_sublist

private theorem activeBudget_pivotSuffixIndices_le_finRange {n : Nat}
    (X : Fin n → Nat) (m : Fin n) (init : BinaryTree) :
    activeBudget (suffixSeq X m) init (pivotSuffixIndices X m) ≤
      activeBudget (suffixSeq X m) init
        (List.finRange (n - (m.val + 1))) := by
  apply activeBudget_sublist_le
  unfold pivotSuffixIndices
  exact List.filter_sublist

private theorem activeBudget_strictLowerSuffixSeq_le_suffixSeq {n : Nat}
    (X : Fin n → Nat) (m : Fin n) (init : BinaryTree) :
    activeBudget (strictLowerSuffixSeq X m) init
        (List.finRange (strictLowerSuffixIndices X m).length) ≤
      activeBudget (suffixSeq X m) init
        (List.finRange (n - (m.val + 1))) := by
  rw [← activeBudget_strictLowerSuffixIndices_eq X m init]
  exact activeBudget_strictLowerSuffixIndices_le_finRange X m init

private theorem pivotSuffixIndices_length_le_activeBudget_suffix {n : Nat}
    (X : Fin n → Nat) (m : Fin n) (init : BinaryTree) :
    ((pivotSuffixIndices X m).length : ℝ) ≤
      activeBudget (suffixSeq X m) init
        (List.finRange (n - (m.val + 1))) := by
  have hlen :
      ((pivotSuffixIndices X m).length : ℝ) ≤
        (List.finRange (n - (m.val + 1))).length := by
    exact_mod_cast List.Sublist.length_le (by
      unfold pivotSuffixIndices
      exact List.filter_sublist)
  have hbudget :=
    length_le_activeBudget (suffixSeq X m) init
      (List.finRange (n - (m.val + 1)))
  nlinarith

private theorem suffixResetUpperPathSum_after_prefix_pivot_le_lowerPath_budget
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList) :
    let ts :=
      splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m)
    suffixResetUpperPathSum (suffixSeq X m) (X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      2 *
        pivotResetLowerPathSum (strictLowerSuffixSeq X m) (X m) ts
          (List.finRange (strictLowerSuffixIndices X m).length) +
      activeBudget (suffixSeq X m) init
        (List.finRange (n - (m.val + 1))) := by
  let ts :=
    splay
      (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
      (X m)
  have hsplit :=
    suffixResetUpperPathSum_suffix_finRange_split X m ts
  have hpair :=
    strictLowerSuffixSeq_pivotResetPairPathSum_le_two_lowerPathSum
      (m := m) hbst hmem
  change
    suffixResetUpperPathSum (suffixSeq X m) (X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      2 *
        pivotResetLowerPathSum (strictLowerSuffixSeq X m) (X m) ts
          (List.finRange (strictLowerSuffixIndices X m).length) +
      activeBudget (suffixSeq X m) init
        (List.finRange (n - (m.val + 1)))
  change
    pivotResetPairPathSum (strictLowerSuffixSeq X m) (X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) ≤
      2 *
        pivotResetLowerPathSum (strictLowerSuffixSeq X m) (X m) ts
          (List.finRange (strictLowerSuffixIndices X m).length) at hpair
  have hpivot :=
    pivotSuffixIndices_length_le_activeBudget_suffix X m init
  rw [hsplit]
  nlinarith

private theorem suffixResetUpperPathSum_after_prefix_pivot_le_size_lower_budget
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList) :
    let ts :=
      splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m)
    suffixResetUpperPathSum (suffixSeq X m) (X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      2 * ((init.num_nodes : ℝ) *
        (strictLowerSuffixIndices X m).length) +
      activeBudget (suffixSeq X m) init
        (List.finRange (n - (m.val + 1))) := by
  let ts :=
    splay
      (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
      (X m)
  have hupper :=
    suffixResetUpperPathSum_after_prefix_pivot_le_lowerPath_budget
      (m := m) hbst hmem
  change
    suffixResetUpperPathSum (suffixSeq X m) (X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      2 *
        pivotResetLowerPathSum (strictLowerSuffixSeq X m) (X m) ts
          (List.finRange (strictLowerSuffixIndices X m).length) +
      activeBudget (suffixSeq X m) init
        (List.finRange (n - (m.val + 1))) at hupper
  have hlower :=
    pivotResetLowerPathSum_le_num_nodes_mul_length
      (strictLowerSuffixSeq X m) (X m)
      (List.finRange (strictLowerSuffixIndices X m).length) ts
  have hnodes : ts.num_nodes = init.num_nodes := by
    unfold ts
    rw [splay_num_nodes,
      splayTreeAfter_num_nodes (prefixSeq X m) (List.finRange m.val) init]
  rw [List.length_finRange, hnodes] at hlower
  change
    suffixResetUpperPathSum (suffixSeq X m) (X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      2 * ((init.num_nodes : ℝ) *
        (strictLowerSuffixIndices X m).length) +
      activeBudget (suffixSeq X m) init
        (List.finRange (n - (m.val + 1)))
  nlinarith

private theorem suffixResetUpperPathSum_after_prefix_pivot_le_three_actualLower_budget
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    (hpairdom :
      ∀ (t : BinaryTree),
        let xs := List.finRange (strictLowerSuffixIndices X m).length
        pivotResetPairPathSum (strictLowerSuffixSeq X m) (X m) t xs ≤
          3 *
            (splayPathSumWithFinal (strictLowerSuffixSeq X m) (X m) t xs +
              xs.length))
    :
    let ts :=
      splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m)
    suffixResetUpperPathSum (suffixSeq X m) (X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      3 *
        (splayPathSumWithFinal (strictLowerSuffixSeq X m) (X m) ts
          (List.finRange (strictLowerSuffixIndices X m).length) +
          (strictLowerSuffixIndices X m).length) +
      activeBudget (suffixSeq X m) init
        (List.finRange (n - (m.val + 1))) := by
  let ts :=
    splay
      (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
      (X m)
  have hsplit :=
    suffixResetUpperPathSum_suffix_finRange_split X m ts
  have hpair := hpairdom ts
  change
    pivotResetPairPathSum (strictLowerSuffixSeq X m) (X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) ≤
      3 *
        (splayPathSumWithFinal (strictLowerSuffixSeq X m) (X m) ts
          (List.finRange (strictLowerSuffixIndices X m).length) +
          (List.finRange (strictLowerSuffixIndices X m).length).length) at hpair
  rw [List.length_finRange] at hpair
  have hpivot :=
    pivotSuffixIndices_length_le_activeBudget_suffix X m init
  change
    suffixResetUpperPathSum (suffixSeq X m) (X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      3 *
        (splayPathSumWithFinal (strictLowerSuffixSeq X m) (X m) ts
          (List.finRange (strictLowerSuffixIndices X m).length) +
          (strictLowerSuffixIndices X m).length) +
      activeBudget (suffixSeq X m) init
        (List.finRange (n - (m.val + 1)))
  rw [hsplit]
  nlinarith

private theorem splayPathSum_pivotSuffixIndices_of_root {n : Nat}
    (X : Fin n → Nat) (m : Fin n) (t : BinaryTree)
    (hsuf_le :
      ∀ j : Fin (n - (m.val + 1)), suffixSeq X m j ≤ X m)
    (hroot : rootKey t = some (X m)) :
    splayPathSum (suffixSeq X m) t (pivotSuffixIndices X m) =
      (pivotSuffixIndices X m).length := by
  exact splayPathSum_const_of_root (suffixSeq X m)
    (pivotSuffixIndices X m) t (X m) hroot
    (fun i hi => (mem_pivotSuffixIndices_iff_eq X m hsuf_le).mp hi)

private theorem splayPathSum_pivotSuffixIndices_le_activeBudget_suffix
    {n : Nat}
    (X : Fin n → Nat) (m : Fin n) (t init : BinaryTree)
    (hsuf_le :
      ∀ j : Fin (n - (m.val + 1)), suffixSeq X m j ≤ X m)
    (hroot : rootKey t = some (X m)) :
    splayPathSum (suffixSeq X m) t (pivotSuffixIndices X m) ≤
      activeBudget (suffixSeq X m) init
        (List.finRange (n - (m.val + 1))) := by
  rw [splayPathSum_pivotSuffixIndices_of_root X m t hsuf_le hroot]
  exact pivotSuffixIndices_length_le_activeBudget_suffix X m init

private theorem splayPathSum_le_suffixResetUpperPathSum_of_lower_continuation
    {n : Nat} (Y : Fin n → Nat) (q : Nat)
    (hcont :
      ∀ (t : BinaryTree) (i : Fin n) (xs : List (Fin n)),
        IsBST t → rootKey t = some q →
        Y i ∈ t.toKeyList → Y i < q →
        (∀ j : Fin n, j ∈ xs → Y j ∈ t.toKeyList) →
        (∀ j : Fin n, j ∈ xs → Y j ≤ q) →
        splayPathSum Y (splay t (Y i)) xs ≤
          (splay t (Y i)).search_path_len q +
            suffixResetUpperPathSum Y q
              (splay (splay t (Y i)) q) xs) :
    ∀ (xs : List (Fin n)) (t : BinaryTree),
      IsBST t → rootKey t = some q →
      (∀ i : Fin n, i ∈ xs → Y i ∈ t.toKeyList) →
      (∀ i : Fin n, i ∈ xs → Y i ≤ q) →
      splayPathSum Y t xs ≤ suffixResetUpperPathSum Y q t xs
| [], t, _hbst, _hroot, _hmem, _hle => by
    simp [splayPathSum, suffixResetUpperPathSum]
| i :: xs, t, hbst, hroot, hmem, hle => by
    have hi_mem : Y i ∈ t.toKeyList := hmem i (by simp)
    have hi_le : Y i ≤ q := hle i (by simp)
    have hmem_tail : ∀ j : Fin n, j ∈ xs → Y j ∈ t.toKeyList := by
      intro j hj
      exact hmem j (by simp [hj])
    have hle_tail : ∀ j : Fin n, j ∈ xs → Y j ≤ q := by
      intro j hj
      exact hle j (by simp [hj])
    by_cases hi_lt : Y i < q
    · have htail :=
        hcont t i xs hbst hroot hi_mem hi_lt hmem_tail hle_tail
      simp [splayPathSum, suffixResetUpperPathSum, hi_lt]
      nlinarith
    · have hi_eq : Y i = q := by omega
      have hpath : t.search_path_len (Y i) = 1 := by
        rw [hi_eq]
        exact search_path_len_eq_one_of_rootKey_eq_some hroot
      have hsplay : splay t (Y i) = t := by
        rw [hi_eq]
        exact splay_eq_self_of_rootKey_eq_some hroot
      have ih :=
        splayPathSum_le_suffixResetUpperPathSum_of_lower_continuation
          Y q hcont xs t hbst hroot hmem_tail hle_tail
      simp [splayPathSum, suffixResetUpperPathSum, hi_lt, hpath, hsplay]
      nlinarith

private theorem splayPathSum_le_suffixResetUpperPathSum_add_activeBudget
    {n : Nat} (Y : Fin n → Nat) (q : Nat)
    (hcont :
      ∀ (t : BinaryTree) (i : Fin n) (xs : List (Fin n)),
        IsBST t → rootKey t = some q →
        Y i ∈ t.toKeyList → Y i < q →
        (∀ j : Fin n, j ∈ xs → Y j ∈ t.toKeyList) →
        (∀ j : Fin n, j ∈ xs → Y j ≤ q) →
        splayPathSum Y (splay t (Y i)) xs ≤
          (splay t (Y i)).search_path_len q +
            suffixResetUpperPathSum Y q
              (splay (splay t (Y i)) q) xs +
            activeBudget Y t (i :: xs)) :
    ∀ (xs : List (Fin n)) (t : BinaryTree),
      IsBST t → rootKey t = some q →
      (∀ i : Fin n, i ∈ xs → Y i ∈ t.toKeyList) →
      (∀ i : Fin n, i ∈ xs → Y i ≤ q) →
      splayPathSum Y t xs ≤
        suffixResetUpperPathSum Y q t xs + activeBudget Y t xs
| [], t, _hbst, _hroot, _hmem, _hle => by
    simp [splayPathSum, suffixResetUpperPathSum, activeBudget,
      activeHullSize_nil]
| i :: xs, t, hbst, hroot, hmem, hle => by
    have hi_mem : Y i ∈ t.toKeyList := hmem i (by simp)
    have hi_le : Y i ≤ q := hle i (by simp)
    have hmem_tail : ∀ j : Fin n, j ∈ xs → Y j ∈ t.toKeyList := by
      intro j hj
      exact hmem j (by simp [hj])
    have hle_tail : ∀ j : Fin n, j ∈ xs → Y j ≤ q := by
      intro j hj
      exact hle j (by simp [hj])
    by_cases hi_lt : Y i < q
    · have htail :=
        hcont t i xs hbst hroot hi_mem hi_lt hmem_tail hle_tail
      simp [splayPathSum, suffixResetUpperPathSum, hi_lt]
      nlinarith
    · have hi_eq : Y i = q := by omega
      have hpath : t.search_path_len (Y i) = 1 := by
        rw [hi_eq]
        exact search_path_len_eq_one_of_rootKey_eq_some hroot
      have hsplay : splay t (Y i) = t := by
        rw [hi_eq]
        exact splay_eq_self_of_rootKey_eq_some hroot
      have ih :=
        splayPathSum_le_suffixResetUpperPathSum_add_activeBudget
          Y q hcont xs t hbst hroot hmem_tail hle_tail
      have hbudget_tail :
          activeBudget Y t xs ≤ activeBudget Y t (i :: xs) := by
        exact activeBudget_sublist_le Y t
          (List.Sublist.cons i (List.Sublist.refl xs))
      simp [splayPathSum, suffixResetUpperPathSum, hi_lt, hpath, hsplay]
      nlinarith

private theorem budgeted_lower_continuation_of_reset_compare
    {n : Nat} (Y : Fin n → Nat) (q : Nat)
    (hrootActual :
      ∀ (xs : List (Fin n)) (t : BinaryTree),
        IsBST t → rootKey t = some q →
        (∀ j : Fin n, j ∈ xs → Y j ∈ t.toKeyList) →
        (∀ j : Fin n, j ∈ xs → Y j ≤ q) →
        splayPathSum Y t xs ≤
          suffixResetUpperPathSum Y q t xs + activeBudget Y t xs)
    (hcompare :
      ∀ (t : BinaryTree) (i : Fin n) (xs : List (Fin n)),
        IsBST t → rootKey t = some q →
        Y i ∈ t.toKeyList → Y i < q →
        (∀ j : Fin n, j ∈ xs → Y j ∈ t.toKeyList) →
        (∀ j : Fin n, j ∈ xs → Y j ≤ q) →
        splayPathSum Y (splay t (Y i)) xs ≤
          (splay t (Y i)).search_path_len q +
            splayPathSum Y (splay (splay t (Y i)) q) xs)
    (hbudgetMove :
      ∀ (t : BinaryTree) (i : Fin n) (xs : List (Fin n)),
        IsBST t → rootKey t = some q →
        Y i ∈ t.toKeyList → Y i < q →
        (∀ j : Fin n, j ∈ xs → Y j ∈ t.toKeyList) →
        (∀ j : Fin n, j ∈ xs → Y j ≤ q) →
        activeBudget Y (splay (splay t (Y i)) q) xs ≤
          activeBudget Y t (i :: xs)) :
      ∀ (t : BinaryTree) (i : Fin n) (xs : List (Fin n)),
        IsBST t → rootKey t = some q →
        Y i ∈ t.toKeyList → Y i < q →
        (∀ j : Fin n, j ∈ xs → Y j ∈ t.toKeyList) →
        (∀ j : Fin n, j ∈ xs → Y j ≤ q) →
        splayPathSum Y (splay t (Y i)) xs ≤
          (splay t (Y i)).search_path_len q +
            suffixResetUpperPathSum Y q
              (splay (splay t (Y i)) q) xs +
            activeBudget Y t (i :: xs) := by
  intro t i xs hbst hroot hi_mem hi_lt hmem_tail hle_tail
  let tr := splay (splay t (Y i)) q
  have hbst_tr : IsBST tr := by
    unfold tr
    exact splay_isBST (splay t (Y i)) q
      (splay_isBST t (Y i) hbst)
  have hroot_tr : rootKey tr = some q := by
    unfold tr
    exact rootKey_after_pivot_reset_of_root hbst hroot
  have hmem_tr :
      ∀ j : Fin n, j ∈ xs → Y j ∈ tr.toKeyList := by
    intro j hj
    unfold tr
    rw [splay_toKeyList, splay_toKeyList]
    exact hmem_tail j hj
  have hactual_tr :=
    hrootActual xs tr hbst_tr hroot_tr hmem_tr hle_tail
  have hcmp :=
    hcompare t i xs hbst hroot hi_mem hi_lt hmem_tail hle_tail
  have hbudget :=
    hbudgetMove t i xs hbst hroot hi_mem hi_lt hmem_tail hle_tail
  nlinarith

private theorem budgeted_lower_continuation_of_reset_compare_of_path_compare
    {n : Nat} (Y : Fin n → Nat) (q : Nat)
    (hrootActual :
      ∀ (xs : List (Fin n)) (t : BinaryTree),
        IsBST t → rootKey t = some q →
        (∀ j : Fin n, j ∈ xs → Y j ∈ t.toKeyList) →
        (∀ j : Fin n, j ∈ xs → Y j ≤ q) →
        splayPathSum Y t xs ≤
          suffixResetUpperPathSum Y q t xs + activeBudget Y t xs)
    (hcompare :
      ∀ (t : BinaryTree) (i : Fin n) (xs : List (Fin n)),
        IsBST t → rootKey t = some q →
        Y i ∈ t.toKeyList → Y i < q →
        (∀ j : Fin n, j ∈ xs → Y j ∈ t.toKeyList) →
        (∀ j : Fin n, j ∈ xs → Y j ≤ q) →
        splayPathSum Y (splay t (Y i)) xs ≤
          (splay t (Y i)).search_path_len q +
            splayPathSum Y (splay (splay t (Y i)) q) xs) :
      ∀ (t : BinaryTree) (i : Fin n) (xs : List (Fin n)),
        IsBST t → rootKey t = some q →
        Y i ∈ t.toKeyList → Y i < q →
        (∀ j : Fin n, j ∈ xs → Y j ∈ t.toKeyList) →
        (∀ j : Fin n, j ∈ xs → Y j ≤ q) →
        splayPathSum Y (splay t (Y i)) xs ≤
          (splay t (Y i)).search_path_len q +
            suffixResetUpperPathSum Y q
              (splay (splay t (Y i)) q) xs +
            activeBudget Y t (i :: xs) := by
  apply budgeted_lower_continuation_of_reset_compare Y q hrootActual hcompare
  intro t i xs hbst hroot hi_mem _hi_lt hmem_tail _hle_tail
  exact activeBudget_after_access_reset_le_cons
    Y q i xs hbst hroot hi_mem hmem_tail

private theorem budgeted_lower_continuation_of_amortized_reset_compare
    {n : Nat} (Y : Fin n → Nat) (q : Nat)
    (hrootActual :
      ∀ (xs : List (Fin n)) (t : BinaryTree),
        IsBST t → rootKey t = some q →
        (∀ j : Fin n, j ∈ xs → Y j ∈ t.toKeyList) →
        (∀ j : Fin n, j ∈ xs → Y j ≤ q) →
        splayPathSum Y t xs ≤
          suffixResetUpperPathSum Y q t xs + activeBudget Y t xs)
    (hamortizedCompare :
      ∀ (t : BinaryTree) (i : Fin n) (xs : List (Fin n)),
        IsBST t → rootKey t = some q →
        Y i ∈ t.toKeyList → Y i < q →
        (∀ j : Fin n, j ∈ xs → Y j ∈ t.toKeyList) →
        (∀ j : Fin n, j ∈ xs → Y j ≤ q) →
        splayPathSum Y (splay t (Y i)) xs +
            activeBudget Y (splay (splay t (Y i)) q) xs ≤
          (splay t (Y i)).search_path_len q +
            splayPathSum Y (splay (splay t (Y i)) q) xs +
            activeBudget Y t (i :: xs)) :
      ∀ (t : BinaryTree) (i : Fin n) (xs : List (Fin n)),
        IsBST t → rootKey t = some q →
        Y i ∈ t.toKeyList → Y i < q →
        (∀ j : Fin n, j ∈ xs → Y j ∈ t.toKeyList) →
        (∀ j : Fin n, j ∈ xs → Y j ≤ q) →
        splayPathSum Y (splay t (Y i)) xs ≤
          (splay t (Y i)).search_path_len q +
            suffixResetUpperPathSum Y q
              (splay (splay t (Y i)) q) xs +
            activeBudget Y t (i :: xs) := by
  intro t i xs hbst hroot hi_mem hi_lt hmem_tail hle_tail
  let tr := splay (splay t (Y i)) q
  have hbst_tr : IsBST tr := by
    unfold tr
    exact splay_isBST (splay t (Y i)) q
      (splay_isBST t (Y i) hbst)
  have hroot_tr : rootKey tr = some q := by
    unfold tr
    exact rootKey_after_pivot_reset_of_root hbst hroot
  have hmem_tr :
      ∀ j : Fin n, j ∈ xs → Y j ∈ tr.toKeyList := by
    intro j hj
    unfold tr
    rw [splay_toKeyList, splay_toKeyList]
    exact hmem_tail j hj
  have hactual_tr :=
    hrootActual xs tr hbst_tr hroot_tr hmem_tr hle_tail
  have hcmp :=
    hamortizedCompare t i xs hbst hroot hi_mem hi_lt hmem_tail hle_tail
  nlinarith

private theorem rooted_actualModel_of_amortized_reset_compare
    {n : Nat} (Y : Fin n → Nat) (q : Nat)
    (hamortizedCompare :
      ∀ (t : BinaryTree) (i : Fin n) (xs : List (Fin n)),
        IsBST t → rootKey t = some q →
        Y i ∈ t.toKeyList → Y i < q →
        (∀ j : Fin n, j ∈ xs → Y j ∈ t.toKeyList) →
        (∀ j : Fin n, j ∈ xs → Y j ≤ q) →
        splayPathSum Y (splay t (Y i)) xs +
            activeBudget Y (splay (splay t (Y i)) q) xs ≤
          (splay t (Y i)).search_path_len q +
            splayPathSum Y (splay (splay t (Y i)) q) xs +
            activeBudget Y t (i :: xs)) :
    ∀ (xs : List (Fin n)) (t : BinaryTree),
      IsBST t → rootKey t = some q →
      (∀ i : Fin n, i ∈ xs → Y i ∈ t.toKeyList) →
      (∀ i : Fin n, i ∈ xs → Y i ≤ q) →
      splayPathSum Y t xs ≤
        suffixResetUpperPathSum Y q t xs + activeBudget Y t xs
| [], t, _hbst, _hroot, _hmem, _hle => by
    simp [splayPathSum, suffixResetUpperPathSum, activeBudget,
      activeHullSize_nil]
| i :: xs, t, hbst, hroot, hmem, hle => by
    have hi_mem : Y i ∈ t.toKeyList := hmem i (by simp)
    have hi_le : Y i ≤ q := hle i (by simp)
    have hmem_tail : ∀ j : Fin n, j ∈ xs → Y j ∈ t.toKeyList := by
      intro j hj
      exact hmem j (by simp [hj])
    have hle_tail : ∀ j : Fin n, j ∈ xs → Y j ≤ q := by
      intro j hj
      exact hle j (by simp [hj])
    by_cases hi_lt : Y i < q
    · let tr := splay (splay t (Y i)) q
      have hbst_tr : IsBST tr := by
        unfold tr
        exact splay_isBST (splay t (Y i)) q
          (splay_isBST t (Y i) hbst)
      have hroot_tr : rootKey tr = some q := by
        unfold tr
        exact rootKey_after_pivot_reset_of_root hbst hroot
      have hmem_tr :
          ∀ j : Fin n, j ∈ xs → Y j ∈ tr.toKeyList := by
        intro j hj
        unfold tr
        rw [splay_toKeyList, splay_toKeyList]
        exact hmem_tail j hj
      have ih_tr :=
        rooted_actualModel_of_amortized_reset_compare
          Y q hamortizedCompare xs tr hbst_tr hroot_tr hmem_tr hle_tail
      have hcmp :=
        hamortizedCompare t i xs hbst hroot hi_mem hi_lt hmem_tail hle_tail
      simp [splayPathSum, suffixResetUpperPathSum, hi_lt]
      nlinarith
    · have hi_eq : Y i = q := by omega
      have hpath : t.search_path_len (Y i) = 1 := by
        rw [hi_eq]
        exact search_path_len_eq_one_of_rootKey_eq_some hroot
      have hsplay : splay t (Y i) = t := by
        rw [hi_eq]
        exact splay_eq_self_of_rootKey_eq_some hroot
      have ih :=
        rooted_actualModel_of_amortized_reset_compare
          Y q hamortizedCompare xs t hbst hroot hmem_tail hle_tail
      have hbudget_tail :
          activeBudget Y t xs ≤ activeBudget Y t (i :: xs) := by
        exact activeBudget_sublist_le Y t
          (List.Sublist.cons i (List.Sublist.refl xs))
      simp [splayPathSum, suffixResetUpperPathSum, hi_lt, hpath, hsplay]
      nlinarith

private theorem rooted_actualModel_of_amortized_reset_compare_const
    {n : Nat} (A : ℝ) (hA : 0 ≤ A)
    (Y : Fin n → Nat) (q : Nat)
    (hamortizedCompare :
      ∀ (t : BinaryTree) (i : Fin n) (xs : List (Fin n)),
        IsBST t → rootKey t = some q →
        Y i ∈ t.toKeyList → Y i < q →
        (∀ j : Fin n, j ∈ xs → Y j ∈ t.toKeyList) →
        (∀ j : Fin n, j ∈ xs → Y j ≤ q) →
        splayPathSum Y (splay t (Y i)) xs +
            A * activeBudget Y (splay (splay t (Y i)) q) xs ≤
          (splay t (Y i)).search_path_len q +
            splayPathSum Y (splay (splay t (Y i)) q) xs +
            A * activeBudget Y t (i :: xs)) :
    ∀ (xs : List (Fin n)) (t : BinaryTree),
      IsBST t → rootKey t = some q →
      (∀ i : Fin n, i ∈ xs → Y i ∈ t.toKeyList) →
      (∀ i : Fin n, i ∈ xs → Y i ≤ q) →
      splayPathSum Y t xs ≤
        suffixResetUpperPathSum Y q t xs + A * activeBudget Y t xs
| [], t, _hbst, _hroot, _hmem, _hle => by
    simp [splayPathSum, suffixResetUpperPathSum, activeBudget,
      activeHullSize_nil]
| i :: xs, t, hbst, hroot, hmem, hle => by
    have hi_mem : Y i ∈ t.toKeyList := hmem i (by simp)
    have hi_le : Y i ≤ q := hle i (by simp)
    have hmem_tail : ∀ j : Fin n, j ∈ xs → Y j ∈ t.toKeyList := by
      intro j hj
      exact hmem j (by simp [hj])
    have hle_tail : ∀ j : Fin n, j ∈ xs → Y j ≤ q := by
      intro j hj
      exact hle j (by simp [hj])
    by_cases hi_lt : Y i < q
    · let tr := splay (splay t (Y i)) q
      have hbst_tr : IsBST tr := by
        unfold tr
        exact splay_isBST (splay t (Y i)) q
          (splay_isBST t (Y i) hbst)
      have hroot_tr : rootKey tr = some q := by
        unfold tr
        exact rootKey_after_pivot_reset_of_root hbst hroot
      have hmem_tr :
          ∀ j : Fin n, j ∈ xs → Y j ∈ tr.toKeyList := by
        intro j hj
        unfold tr
        rw [splay_toKeyList, splay_toKeyList]
        exact hmem_tail j hj
      have ih_tr :=
        rooted_actualModel_of_amortized_reset_compare_const
          A hA Y q hamortizedCompare xs tr hbst_tr hroot_tr hmem_tr hle_tail
      have hcmp :=
        hamortizedCompare t i xs hbst hroot hi_mem hi_lt hmem_tail hle_tail
      simp [splayPathSum, suffixResetUpperPathSum, hi_lt]
      nlinarith
    · have hi_eq : Y i = q := by omega
      have hpath : t.search_path_len (Y i) = 1 := by
        rw [hi_eq]
        exact search_path_len_eq_one_of_rootKey_eq_some hroot
      have hsplay : splay t (Y i) = t := by
        rw [hi_eq]
        exact splay_eq_self_of_rootKey_eq_some hroot
      have ih :=
        rooted_actualModel_of_amortized_reset_compare_const
          A hA Y q hamortizedCompare xs t hbst hroot hmem_tail hle_tail
      have hbudget_tail :
          activeBudget Y t xs ≤ activeBudget Y t (i :: xs) := by
        exact activeBudget_sublist_le Y t
          (List.Sublist.cons i (List.Sublist.refl xs))
      have hbudget_tail_scaled :
          A * activeBudget Y t xs ≤ A * activeBudget Y t (i :: xs) :=
        mul_le_mul_of_nonneg_left hbudget_tail hA
      simp [splayPathSum, suffixResetUpperPathSum, hi_lt, hpath, hsplay]
      nlinarith

private theorem rooted_pairModel_of_amortized_reset_compare
    {n : Nat} (Y : Fin n → Nat) (q : Nat)
    (hpairCompare :
      ∀ (t : BinaryTree) (i : Fin n) (xs : List (Fin n)),
        IsBST t → rootKey t = some q →
        Y i ∈ t.toKeyList → Y i < q →
        (∀ j : Fin n, j ∈ xs → Y j ∈ t.toKeyList) →
        (∀ j : Fin n, j ∈ xs → Y j < q) →
        (splay t (Y i)).search_path_len q +
            splayPathSum Y (splay (splay t (Y i)) q) xs +
            5 * activeBudget Y (splay (splay t (Y i)) q) xs ≤
          splayPathSum Y (splay t (Y i)) xs +
            5 * activeBudget Y t (i :: xs)) :
    ∀ (xs : List (Fin n)) (t : BinaryTree),
      IsBST t → rootKey t = some q →
      (∀ i : Fin n, i ∈ xs → Y i ∈ t.toKeyList) →
      (∀ i : Fin n, i ∈ xs → Y i < q) →
      pivotResetPairPathSum Y q t xs ≤
        splayPathSum Y t xs + 5 * activeBudget Y t xs
| [], t, _hbst, _hroot, _hmem, _hlt => by
    simp [pivotResetPairPathSum, splayPathSum, activeBudget,
      activeHullSize_nil]
| i :: xs, t, hbst, hroot, hmem, hlt => by
    have hi_mem : Y i ∈ t.toKeyList := hmem i (by simp)
    have hi_lt : Y i < q := hlt i (by simp)
    have hmem_tail : ∀ j : Fin n, j ∈ xs → Y j ∈ t.toKeyList := by
      intro j hj
      exact hmem j (by simp [hj])
    have hlt_tail : ∀ j : Fin n, j ∈ xs → Y j < q := by
      intro j hj
      exact hlt j (by simp [hj])
    let tr := splay (splay t (Y i)) q
    have hbst_tr : IsBST tr := by
      unfold tr
      exact splay_isBST (splay t (Y i)) q
        (splay_isBST t (Y i) hbst)
    have hroot_tr : rootKey tr = some q := by
      unfold tr
      exact rootKey_after_pivot_reset_of_root hbst hroot
    have hmem_tr :
        ∀ j : Fin n, j ∈ xs → Y j ∈ tr.toKeyList := by
      intro j hj
      unfold tr
      rw [splay_toKeyList, splay_toKeyList]
      exact hmem_tail j hj
    have ih_tr :=
      rooted_pairModel_of_amortized_reset_compare
        Y q hpairCompare xs tr hbst_tr hroot_tr hmem_tr hlt_tail
    have hcmp :=
      hpairCompare t i xs hbst hroot hi_mem hi_lt hmem_tail hlt_tail
    simp [pivotResetPairPathSum, splayPathSum]
    nlinarith

private theorem suffix_after_prefix_pivot_le_reset_of_lower_continuation
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (hsuf_le :
      ∀ j : Fin (n - (m.val + 1)), suffixSeq X m j ≤ X m)
    (hcont :
      ∀ (t : BinaryTree) (i : Fin (n - (m.val + 1)))
        (xs : List (Fin (n - (m.val + 1)))),
        IsBST t → rootKey t = some (X m) →
        suffixSeq X m i ∈ t.toKeyList → suffixSeq X m i < X m →
        (∀ j : Fin (n - (m.val + 1)),
          j ∈ xs → suffixSeq X m j ∈ t.toKeyList) →
        (∀ j : Fin (n - (m.val + 1)),
          j ∈ xs → suffixSeq X m j ≤ X m) →
        splayPathSum (suffixSeq X m)
            (splay t (suffixSeq X m i)) xs ≤
          (splay t (suffixSeq X m i)).search_path_len (X m) +
            suffixResetUpperPathSum (suffixSeq X m) (X m)
              (splay (splay t (suffixSeq X m i)) (X m)) xs) :
    let ts :=
      splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m)
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      suffixResetUpperPathSum (suffixSeq X m) (X m) ts
        (List.finRange (n - (m.val + 1))) := by
  let tp :=
    splayTreeAfter (prefixSeq X m) init (List.finRange m.val)
  let ts := splay tp (X m)
  have htp_bst : IsBST tp := by
    unfold tp
    exact splayTreeAfter_isBST (prefixSeq X m)
      (List.finRange m.val) init hbst
  have hpivot_mem_tp : X m ∈ tp.toKeyList := by
    unfold tp
    rw [splayTreeAfter_toKeyList (prefixSeq X m)
      (List.finRange m.val) init]
    exact hmem m
  have hroot_ts : rootKey ts = some (X m) := by
    unfold ts
    exact splay_rootKey_eq_some_of_mem_isBST tp (X m)
      htp_bst hpivot_mem_tp
  have hbst_ts : IsBST ts := by
    unfold ts
    exact splay_isBST tp (X m) htp_bst
  have hmem_ts :
      ∀ i : Fin (n - (m.val + 1)),
        i ∈ List.finRange (n - (m.val + 1)) →
        suffixSeq X m i ∈ ts.toKeyList := by
    intro i _hi
    unfold ts tp
    exact suffixSeq_mem_after_prefix_pivot hmem m i
  have hle_all :
      ∀ i : Fin (n - (m.val + 1)),
        i ∈ List.finRange (n - (m.val + 1)) →
        suffixSeq X m i ≤ X m := by
    intro i _hi
    exact hsuf_le i
  change
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      suffixResetUpperPathSum (suffixSeq X m) (X m) ts
        (List.finRange (n - (m.val + 1)))
  exact
    splayPathSum_le_suffixResetUpperPathSum_of_lower_continuation
      (suffixSeq X m) (X m) hcont
      (List.finRange (n - (m.val + 1))) ts
      hbst_ts hroot_ts hmem_ts hle_all

private theorem suffix_after_prefix_pivot_le_reset_add_activeBudget
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (hsuf_le :
      ∀ j : Fin (n - (m.val + 1)), suffixSeq X m j ≤ X m)
    (hcont :
      ∀ (t : BinaryTree) (i : Fin (n - (m.val + 1)))
        (xs : List (Fin (n - (m.val + 1)))),
        IsBST t → rootKey t = some (X m) →
        suffixSeq X m i ∈ t.toKeyList → suffixSeq X m i < X m →
        (∀ j : Fin (n - (m.val + 1)),
          j ∈ xs → suffixSeq X m j ∈ t.toKeyList) →
        (∀ j : Fin (n - (m.val + 1)),
          j ∈ xs → suffixSeq X m j ≤ X m) →
        splayPathSum (suffixSeq X m)
            (splay t (suffixSeq X m i)) xs ≤
          (splay t (suffixSeq X m i)).search_path_len (X m) +
            suffixResetUpperPathSum (suffixSeq X m) (X m)
              (splay (splay t (suffixSeq X m i)) (X m)) xs +
            activeBudget (suffixSeq X m) t (i :: xs)) :
    let ts :=
      splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m)
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      suffixResetUpperPathSum (suffixSeq X m) (X m) ts
        (List.finRange (n - (m.val + 1))) +
      activeBudget (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) := by
  let tp :=
    splayTreeAfter (prefixSeq X m) init (List.finRange m.val)
  let ts := splay tp (X m)
  have htp_bst : IsBST tp := by
    unfold tp
    exact splayTreeAfter_isBST (prefixSeq X m)
      (List.finRange m.val) init hbst
  have hpivot_mem_tp : X m ∈ tp.toKeyList := by
    unfold tp
    rw [splayTreeAfter_toKeyList (prefixSeq X m)
      (List.finRange m.val) init]
    exact hmem m
  have hroot_ts : rootKey ts = some (X m) := by
    unfold ts
    exact splay_rootKey_eq_some_of_mem_isBST tp (X m)
      htp_bst hpivot_mem_tp
  have hbst_ts : IsBST ts := by
    unfold ts
    exact splay_isBST tp (X m) htp_bst
  have hmem_ts :
      ∀ i : Fin (n - (m.val + 1)),
        i ∈ List.finRange (n - (m.val + 1)) →
        suffixSeq X m i ∈ ts.toKeyList := by
    intro i _hi
    unfold ts tp
    exact suffixSeq_mem_after_prefix_pivot hmem m i
  have hle_all :
      ∀ i : Fin (n - (m.val + 1)),
        i ∈ List.finRange (n - (m.val + 1)) →
        suffixSeq X m i ≤ X m := by
    intro i _hi
    exact hsuf_le i
  change
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      suffixResetUpperPathSum (suffixSeq X m) (X m) ts
        (List.finRange (n - (m.val + 1))) +
      activeBudget (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1)))
  exact
    splayPathSum_le_suffixResetUpperPathSum_add_activeBudget
      (suffixSeq X m) (X m) hcont
      (List.finRange (n - (m.val + 1))) ts
      hbst_ts hroot_ts hmem_ts hle_all

private theorem splayPathSum_le_suffixResetUpperPathSum_of_lower_reset_step
    {n : Nat} (Y : Fin n → Nat) (q : Nat)
    (hstep :
      ∀ (t : BinaryTree) (i : Fin n) (xs : List (Fin n)),
        IsBST t → q ∈ t.toKeyList →
        Y i ∈ t.toKeyList → Y i < q →
        (∀ j : Fin n, j ∈ xs → Y j ∈ t.toKeyList) →
        (∀ j : Fin n, j ∈ xs → Y j ≤ q) →
        (t.search_path_len (Y i) : ℝ) +
            (splay t (Y i)).search_path_len q +
            suffixResetUpperPathSum Y q
              (splay (splay t (Y i)) q) xs ≤
          t.search_path_len q +
            suffixResetUpperPathSum Y q (splay t q) (i :: xs)) :
    ∀ (xs : List (Fin n)) (t : BinaryTree),
      IsBST t → q ∈ t.toKeyList →
      (∀ i : Fin n, i ∈ xs → Y i ∈ t.toKeyList) →
      (∀ i : Fin n, i ∈ xs → Y i ≤ q) →
      splayPathSum Y t xs ≤
        t.search_path_len q +
          suffixResetUpperPathSum Y q (splay t q) xs
| [], t, _hbst, _hqmem, _hmem, _hle => by
    simp [splayPathSum, suffixResetUpperPathSum]
| i :: xs, t, hbst, hqmem, hmem, hle => by
    have hi_mem : Y i ∈ t.toKeyList := hmem i (by simp)
    have hi_le : Y i ≤ q := hle i (by simp)
    have hmem_tail : ∀ j : Fin n, j ∈ xs → Y j ∈ t.toKeyList := by
      intro j hj
      exact hmem j (by simp [hj])
    have hle_tail : ∀ j : Fin n, j ∈ xs → Y j ≤ q := by
      intro j hj
      exact hle j (by simp [hj])
    by_cases hi_lt : Y i < q
    · have htail :=
        splayPathSum_le_suffixResetUpperPathSum_of_lower_reset_step
          Y q hstep xs (splay t (Y i))
          (splay_isBST t (Y i) hbst)
          (by
            rw [splay_toKeyList]
            exact hqmem)
          (by
            intro j hj
            rw [splay_toKeyList]
            exact hmem_tail j hj)
          hle_tail
      have hstep_i :=
        hstep t i xs hbst hqmem hi_mem hi_lt hmem_tail hle_tail
      simp [splayPathSum]
      nlinarith
    · have hi_eq : Y i = q := by omega
      have htail :=
        splayPathSum_le_suffixResetUpperPathSum_of_lower_reset_step
          Y q hstep xs (splay t q)
          (splay_isBST t q hbst)
          (by
            rw [splay_toKeyList]
            exact hqmem)
          (by
            intro j hj
            rw [splay_toKeyList]
            exact hmem_tail j hj)
          hle_tail
      have hroot_s : rootKey (splay t q) = some q :=
        splay_rootKey_eq_some_of_mem_isBST t q hbst hqmem
      have hpath_s : (splay t q).search_path_len q = 1 :=
        search_path_len_eq_one_of_rootKey_eq_some hroot_s
      have hsplay_s : splay (splay t q) q = splay t q :=
        splay_eq_self_of_rootKey_eq_some hroot_s
      rw [hpath_s, hsplay_s] at htail
      norm_num at htail
      simp [splayPathSum, suffixResetUpperPathSum, hi_eq]
      nlinarith

private theorem lower_continuation_of_lower_reset_step
    {n : Nat} (Y : Fin n → Nat) (q : Nat)
    (hstep :
      ∀ (t : BinaryTree) (i : Fin n) (xs : List (Fin n)),
        IsBST t → q ∈ t.toKeyList →
        Y i ∈ t.toKeyList → Y i < q →
        (∀ j : Fin n, j ∈ xs → Y j ∈ t.toKeyList) →
        (∀ j : Fin n, j ∈ xs → Y j ≤ q) →
        (t.search_path_len (Y i) : ℝ) +
            (splay t (Y i)).search_path_len q +
            suffixResetUpperPathSum Y q
              (splay (splay t (Y i)) q) xs ≤
          t.search_path_len q +
            suffixResetUpperPathSum Y q (splay t q) (i :: xs)) :
      ∀ (t : BinaryTree) (i : Fin n) (xs : List (Fin n)),
        IsBST t → rootKey t = some q →
        Y i ∈ t.toKeyList → Y i < q →
        (∀ j : Fin n, j ∈ xs → Y j ∈ t.toKeyList) →
        (∀ j : Fin n, j ∈ xs → Y j ≤ q) →
        splayPathSum Y (splay t (Y i)) xs ≤
          (splay t (Y i)).search_path_len q +
            suffixResetUpperPathSum Y q
              (splay (splay t (Y i)) q) xs := by
  intro t i xs hbst hroot hi_mem _hi_lt hmem_tail hle_tail
  have hqmem : q ∈ t.toKeyList := rootKey_mem_toKeyList hroot
  exact
    splayPathSum_le_suffixResetUpperPathSum_of_lower_reset_step
      Y q hstep xs (splay t (Y i))
      (splay_isBST t (Y i) hbst)
      (by
        rw [splay_toKeyList]
        exact hqmem)
      (by
        intro j hj
        rw [splay_toKeyList]
        exact hmem_tail j hj)
      hle_tail

private theorem suffix_after_prefix_pivot_le_reset_of_lower_reset_step
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (hsuf_le :
      ∀ j : Fin (n - (m.val + 1)), suffixSeq X m j ≤ X m)
    (hstep :
      ∀ (t : BinaryTree) (i : Fin (n - (m.val + 1)))
        (xs : List (Fin (n - (m.val + 1)))),
        IsBST t → X m ∈ t.toKeyList →
        suffixSeq X m i ∈ t.toKeyList → suffixSeq X m i < X m →
        (∀ j : Fin (n - (m.val + 1)),
          j ∈ xs → suffixSeq X m j ∈ t.toKeyList) →
        (∀ j : Fin (n - (m.val + 1)),
          j ∈ xs → suffixSeq X m j ≤ X m) →
        (t.search_path_len (suffixSeq X m i) : ℝ) +
            (splay t (suffixSeq X m i)).search_path_len (X m) +
            suffixResetUpperPathSum (suffixSeq X m) (X m)
              (splay (splay t (suffixSeq X m i)) (X m)) xs ≤
          t.search_path_len (X m) +
            suffixResetUpperPathSum (suffixSeq X m) (X m)
              (splay t (X m)) (i :: xs)) :
    let ts :=
      splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m)
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      suffixResetUpperPathSum (suffixSeq X m) (X m) ts
        (List.finRange (n - (m.val + 1))) := by
  exact suffix_after_prefix_pivot_le_reset_of_lower_continuation
    (m := m) hbst hmem hsuf_le
    (lower_continuation_of_lower_reset_step
      (suffixSeq X m) (X m) hstep)

private theorem suffix_after_prefix_pivot_le_three_actualLower_budget_of_bridges
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (hsuf_le :
      ∀ j : Fin (n - (m.val + 1)), suffixSeq X m j ≤ X m)
    (hcont :
      ∀ (t : BinaryTree) (i : Fin (n - (m.val + 1)))
        (xs : List (Fin (n - (m.val + 1)))),
        IsBST t → rootKey t = some (X m) →
        suffixSeq X m i ∈ t.toKeyList → suffixSeq X m i < X m →
        (∀ j : Fin (n - (m.val + 1)),
          j ∈ xs → suffixSeq X m j ∈ t.toKeyList) →
        (∀ j : Fin (n - (m.val + 1)),
          j ∈ xs → suffixSeq X m j ≤ X m) →
        splayPathSum (suffixSeq X m)
            (splay t (suffixSeq X m i)) xs ≤
          (splay t (suffixSeq X m i)).search_path_len (X m) +
            suffixResetUpperPathSum (suffixSeq X m) (X m)
              (splay (splay t (suffixSeq X m i)) (X m)) xs)
    (hpairdom :
      ∀ (t : BinaryTree),
        let xs := List.finRange (strictLowerSuffixIndices X m).length
        pivotResetPairPathSum (strictLowerSuffixSeq X m) (X m) t xs ≤
          3 *
            (splayPathSumWithFinal (strictLowerSuffixSeq X m) (X m) t xs +
              xs.length)) :
    let ts :=
      splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m)
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      3 *
        (splayPathSumWithFinal (strictLowerSuffixSeq X m) (X m) ts
          (List.finRange (strictLowerSuffixIndices X m).length) +
          (strictLowerSuffixIndices X m).length) +
      activeBudget (suffixSeq X m) init
        (List.finRange (n - (m.val + 1))) := by
  let ts :=
    splay
      (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
      (X m)
  have hactual :=
    suffix_after_prefix_pivot_le_reset_of_lower_continuation
      (m := m) hbst hmem hsuf_le hcont
  have hreset :=
    suffixResetUpperPathSum_after_prefix_pivot_le_three_actualLower_budget
      (m := m) (init := init) hpairdom
  change
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      3 *
        (splayPathSumWithFinal (strictLowerSuffixSeq X m) (X m) ts
          (List.finRange (strictLowerSuffixIndices X m).length) +
          (strictLowerSuffixIndices X m).length) +
      activeBudget (suffixSeq X m) init
        (List.finRange (n - (m.val + 1)))
  change
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      suffixResetUpperPathSum (suffixSeq X m) (X m) ts
        (List.finRange (n - (m.val + 1))) at hactual
  change
    suffixResetUpperPathSum (suffixSeq X m) (X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      3 *
        (splayPathSumWithFinal (strictLowerSuffixSeq X m) (X m) ts
          (List.finRange (strictLowerSuffixIndices X m).length) +
          (strictLowerSuffixIndices X m).length) +
      activeBudget (suffixSeq X m) init
        (List.finRange (n - (m.val + 1))) at hreset
  exact le_trans hactual hreset

private theorem suffix_after_prefix_pivot_le_three_lowerPath_size_budget_of_bridges
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (hsuf_le :
      ∀ j : Fin (n - (m.val + 1)), suffixSeq X m j ≤ X m)
    (hcont :
      ∀ (t : BinaryTree) (i : Fin (n - (m.val + 1)))
        (xs : List (Fin (n - (m.val + 1)))),
        IsBST t → rootKey t = some (X m) →
        suffixSeq X m i ∈ t.toKeyList → suffixSeq X m i < X m →
        (∀ j : Fin (n - (m.val + 1)),
          j ∈ xs → suffixSeq X m j ∈ t.toKeyList) →
        (∀ j : Fin (n - (m.val + 1)),
          j ∈ xs → suffixSeq X m j ≤ X m) →
        splayPathSum (suffixSeq X m)
            (splay t (suffixSeq X m i)) xs ≤
          (splay t (suffixSeq X m i)).search_path_len (X m) +
            suffixResetUpperPathSum (suffixSeq X m) (X m)
              (splay (splay t (suffixSeq X m i)) (X m)) xs)
    (hpairdom :
      ∀ (t : BinaryTree),
        let xs := List.finRange (strictLowerSuffixIndices X m).length
        pivotResetPairPathSum (strictLowerSuffixSeq X m) (X m) t xs ≤
          3 *
            (splayPathSumWithFinal (strictLowerSuffixSeq X m) (X m) t xs +
              xs.length)) :
    let ts :=
      splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m)
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      3 *
        (splayPathSum (strictLowerSuffixSeq X m) ts
          (List.finRange (strictLowerSuffixIndices X m).length) +
          init.num_nodes +
          (strictLowerSuffixIndices X m).length) +
      activeBudget (suffixSeq X m) init
        (List.finRange (n - (m.val + 1))) := by
  let ts :=
    splay
      (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
      (X m)
  have hstrong :=
    suffix_after_prefix_pivot_le_three_actualLower_budget_of_bridges
      (m := m) hbst hmem hsuf_le hcont hpairdom
  have hfinal :=
    splayPathSumWithFinal_le_pathSum_add_num_nodes
      (strictLowerSuffixSeq X m) (X m)
      (List.finRange (strictLowerSuffixIndices X m).length) ts
  have hnodes : ts.num_nodes = init.num_nodes := by
    unfold ts
    rw [splay_num_nodes,
      splayTreeAfter_num_nodes (prefixSeq X m) (List.finRange m.val) init]
  rw [hnodes] at hfinal
  change
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      3 *
        (splayPathSum (strictLowerSuffixSeq X m) ts
          (List.finRange (strictLowerSuffixIndices X m).length) +
          init.num_nodes +
          (strictLowerSuffixIndices X m).length) +
      activeBudget (suffixSeq X m) init
        (List.finRange (n - (m.val + 1)))
  change
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      3 *
        (splayPathSumWithFinal (strictLowerSuffixSeq X m) (X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
          (strictLowerSuffixIndices X m).length) +
      activeBudget (suffixSeq X m) init
        (List.finRange (n - (m.val + 1))) at hstrong
  nlinarith

private theorem suffix_after_prefix_pivot_le_lowerPath_activeBudgets_of_model_bridges
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    (hactualReset :
      let ts :=
        splay
          (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
          (X m)
      splayPathSum (suffixSeq X m) ts
          (List.finRange (n - (m.val + 1))) ≤
        suffixResetUpperPathSum (suffixSeq X m) (X m) ts
          (List.finRange (n - (m.val + 1))) +
        activeBudget (suffixSeq X m) ts
          (List.finRange (n - (m.val + 1))))
    (hpairActual :
      let ts :=
        splay
          (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
          (X m)
      let xs := List.finRange (strictLowerSuffixIndices X m).length
      pivotResetPairPathSum (strictLowerSuffixSeq X m) (X m) ts xs ≤
        splayPathSum (strictLowerSuffixSeq X m) ts xs +
          5 * activeBudget (strictLowerSuffixSeq X m) ts xs) :
    let ts :=
      splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m)
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      5 * activeBudget (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      2 * activeBudget (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) := by
  let ts :=
    splay
      (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
      (X m)
  have hsplit :=
    suffixResetUpperPathSum_suffix_finRange_split X m ts
  have hpivotLen :
      ((pivotSuffixIndices X m).length : ℝ) ≤
        activeBudget (suffixSeq X m) ts
          (List.finRange (n - (m.val + 1))) := by
    exact pivotSuffixIndices_length_le_activeBudget_suffix X m ts
  change
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      5 * activeBudget (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      2 * activeBudget (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1)))
  change
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      suffixResetUpperPathSum (suffixSeq X m) (X m) ts
        (List.finRange (n - (m.val + 1))) +
      activeBudget (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) at hactualReset
  change
    pivotResetPairPathSum (strictLowerSuffixSeq X m) (X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      5 * activeBudget (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) at hpairActual
  rw [hsplit] at hactualReset
  nlinarith

private theorem suffix_after_prefix_pivot_le_lowerPath_linear_of_model_bridges
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    (hactualReset :
      let ts :=
        splay
          (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
          (X m)
      splayPathSum (suffixSeq X m) ts
          (List.finRange (n - (m.val + 1))) ≤
        suffixResetUpperPathSum (suffixSeq X m) (X m) ts
          (List.finRange (n - (m.val + 1))) +
        activeBudget (suffixSeq X m) ts
          (List.finRange (n - (m.val + 1))))
    (hpairActual :
      let ts :=
        splay
          (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
          (X m)
      let xs := List.finRange (strictLowerSuffixIndices X m).length
      pivotResetPairPathSum (strictLowerSuffixSeq X m) (X m) ts xs ≤
        splayPathSum (strictLowerSuffixSeq X m) ts xs +
          5 * activeBudget (strictLowerSuffixSeq X m) ts xs) :
    let ts :=
      splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m)
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      7 * ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ) := by
  let ts :=
    splay
      (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
      (X m)
  have hmain :=
    suffix_after_prefix_pivot_le_lowerPath_activeBudgets_of_model_bridges
      (m := m) hactualReset hpairActual
  have hlowerBudget :=
    activeBudget_le_length_add_num_nodes (strictLowerSuffixSeq X m) ts
      (List.finRange (strictLowerSuffixIndices X m).length)
  have hsuffixBudget :=
    activeBudget_le_length_add_num_nodes (suffixSeq X m) ts
      (List.finRange (n - (m.val + 1)))
  have hlowerLen :=
    strictLowerSuffixIndices_length_le X m
  have hnodes : ts.num_nodes = init.num_nodes := by
    unfold ts
    rw [splay_num_nodes,
      splayTreeAfter_num_nodes (prefixSeq X m) (List.finRange m.val) init]
  rw [List.length_finRange, hnodes] at hlowerBudget hsuffixBudget
  change
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      7 * ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ)
  change
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      5 * activeBudget (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      2 * activeBudget (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) at hmain
  have hlowerLenR :
      ((strictLowerSuffixIndices X m).length : ℝ) ≤
        (n - (m.val + 1) : Nat) := by
    exact_mod_cast hlowerLen
  nlinarith

private theorem suffix_after_prefix_pivot_le_lowerPath_linear_of_budgeted_continuation
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (hsuf_le :
      ∀ j : Fin (n - (m.val + 1)), suffixSeq X m j ≤ X m)
    (hcont :
      ∀ (t : BinaryTree) (i : Fin (n - (m.val + 1)))
        (xs : List (Fin (n - (m.val + 1)))),
        IsBST t → rootKey t = some (X m) →
        suffixSeq X m i ∈ t.toKeyList → suffixSeq X m i < X m →
        (∀ j : Fin (n - (m.val + 1)),
          j ∈ xs → suffixSeq X m j ∈ t.toKeyList) →
        (∀ j : Fin (n - (m.val + 1)),
          j ∈ xs → suffixSeq X m j ≤ X m) →
        splayPathSum (suffixSeq X m)
            (splay t (suffixSeq X m i)) xs ≤
          (splay t (suffixSeq X m i)).search_path_len (X m) +
            suffixResetUpperPathSum (suffixSeq X m) (X m)
              (splay (splay t (suffixSeq X m i)) (X m)) xs +
            activeBudget (suffixSeq X m) t (i :: xs))
    (hpairActual :
      let ts :=
        splay
          (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
          (X m)
      let xs := List.finRange (strictLowerSuffixIndices X m).length
      pivotResetPairPathSum (strictLowerSuffixSeq X m) (X m) ts xs ≤
        splayPathSum (strictLowerSuffixSeq X m) ts xs +
          5 * activeBudget (strictLowerSuffixSeq X m) ts xs) :
    let ts :=
      splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m)
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      7 * ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ) := by
  have hactualReset :=
    suffix_after_prefix_pivot_le_reset_add_activeBudget
      (m := m) hbst hmem hsuf_le hcont
  exact
    suffix_after_prefix_pivot_le_lowerPath_linear_of_model_bridges
      (m := m) hactualReset hpairActual

private theorem suffix_after_prefix_pivot_le_lowerPath_linear_of_generic_model_bridges
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (hsuf_le :
      ∀ j : Fin (n - (m.val + 1)), suffixSeq X m j ≤ X m)
    (hactualModel :
      ∀ {N : Nat} (Y : Fin N → Nat) (q : Nat)
        (t : BinaryTree) (xs : List (Fin N)),
        IsBST t → rootKey t = some q →
        (∀ i : Fin N, i ∈ xs → Y i ∈ t.toKeyList) →
        (∀ i : Fin N, i ∈ xs → Y i ≤ q) →
        splayPathSum Y t xs ≤
          suffixResetUpperPathSum Y q t xs + activeBudget Y t xs)
    (hpairModel :
      ∀ {N : Nat} (Y : Fin N → Nat) (q : Nat)
        (t : BinaryTree) (xs : List (Fin N)),
        IsBST t → rootKey t = some q →
        (∀ i : Fin N, i ∈ xs → Y i ∈ t.toKeyList) →
        (∀ i : Fin N, i ∈ xs → Y i < q) →
        pivotResetPairPathSum Y q t xs ≤
          splayPathSum Y t xs + 5 * activeBudget Y t xs) :
    let ts :=
      splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m)
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      7 * ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ) := by
  let tp :=
    splayTreeAfter (prefixSeq X m) init (List.finRange m.val)
  let ts := splay tp (X m)
  have htp_bst : IsBST tp := by
    unfold tp
    exact splayTreeAfter_isBST (prefixSeq X m)
      (List.finRange m.val) init hbst
  have hpivot_mem_tp : X m ∈ tp.toKeyList := by
    unfold tp
    rw [splayTreeAfter_toKeyList (prefixSeq X m)
      (List.finRange m.val) init]
    exact hmem m
  have hbst_ts : IsBST ts := by
    unfold ts
    exact splay_isBST tp (X m) htp_bst
  have hroot_ts : rootKey ts = some (X m) := by
    unfold ts
    exact splay_rootKey_eq_some_of_mem_isBST tp (X m)
      htp_bst hpivot_mem_tp
  have hactualReset :
      splayPathSum (suffixSeq X m) ts
          (List.finRange (n - (m.val + 1))) ≤
        suffixResetUpperPathSum (suffixSeq X m) (X m) ts
          (List.finRange (n - (m.val + 1))) +
        activeBudget (suffixSeq X m) ts
          (List.finRange (n - (m.val + 1))) := by
    apply hactualModel
    · exact hbst_ts
    · exact hroot_ts
    · intro i _hi
      unfold ts tp
      exact suffixSeq_mem_after_prefix_pivot hmem m i
    · intro i _hi
      exact hsuf_le i
  have hpairActual :
      let xs := List.finRange (strictLowerSuffixIndices X m).length
      pivotResetPairPathSum (strictLowerSuffixSeq X m) (X m) ts xs ≤
        splayPathSum (strictLowerSuffixSeq X m) ts xs +
          5 * activeBudget (strictLowerSuffixSeq X m) ts xs := by
    dsimp
    apply hpairModel
    · exact hbst_ts
    · exact hroot_ts
    · intro i _hi
      unfold ts tp
      exact strictLowerSuffixSeq_mem_after_prefix_pivot hmem i
    · intro i _hi
      exact strictLowerSuffixSeq_lt_first_max X m i
  change
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      7 * ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ)
  exact
    suffix_after_prefix_pivot_le_lowerPath_linear_of_model_bridges
      (m := m) hactualReset hpairActual

private theorem rooted_pairModel_of_amortized_reset_compare_const
    {n : Nat} (C : ℝ) (Y : Fin n → Nat) (q : Nat)
    (hpairCompare :
      ∀ (t : BinaryTree) (i : Fin n) (xs : List (Fin n)),
        IsBST t → rootKey t = some q →
        Y i ∈ t.toKeyList → Y i < q →
        (∀ j : Fin n, j ∈ xs → Y j ∈ t.toKeyList) →
        (∀ j : Fin n, j ∈ xs → Y j < q) →
        (splay t (Y i)).search_path_len q +
            splayPathSum Y (splay (splay t (Y i)) q) xs +
            C * activeBudget Y (splay (splay t (Y i)) q) xs ≤
          splayPathSum Y (splay t (Y i)) xs +
            C * activeBudget Y t (i :: xs)) :
    ∀ (xs : List (Fin n)) (t : BinaryTree),
      IsBST t → rootKey t = some q →
      (∀ i : Fin n, i ∈ xs → Y i ∈ t.toKeyList) →
      (∀ i : Fin n, i ∈ xs → Y i < q) →
      pivotResetPairPathSum Y q t xs ≤
        splayPathSum Y t xs + C * activeBudget Y t xs
| [], t, _hbst, _hroot, _hmem, _hlt => by
    simp [pivotResetPairPathSum, splayPathSum, activeBudget,
      activeHullSize_nil]
| i :: xs, t, hbst, hroot, hmem, hlt => by
    have hi_mem : Y i ∈ t.toKeyList := hmem i (by simp)
    have hi_lt : Y i < q := hlt i (by simp)
    have hmem_tail : ∀ j : Fin n, j ∈ xs → Y j ∈ t.toKeyList := by
      intro j hj
      exact hmem j (by simp [hj])
    have hlt_tail : ∀ j : Fin n, j ∈ xs → Y j < q := by
      intro j hj
      exact hlt j (by simp [hj])
    let tr := splay (splay t (Y i)) q
    have hbst_tr : IsBST tr := by
      unfold tr
      exact splay_isBST (splay t (Y i)) q
        (splay_isBST t (Y i) hbst)
    have hroot_tr : rootKey tr = some q := by
      unfold tr
      exact rootKey_after_pivot_reset_of_root hbst hroot
    have hmem_tr :
        ∀ j : Fin n, j ∈ xs → Y j ∈ tr.toKeyList := by
      intro j hj
      unfold tr
      rw [splay_toKeyList, splay_toKeyList]
      exact hmem_tail j hj
    have ih_tr :=
      rooted_pairModel_of_amortized_reset_compare_const
        C Y q hpairCompare xs tr hbst_tr hroot_tr hmem_tr hlt_tail
    have hcmp :=
      hpairCompare t i xs hbst hroot hi_mem hi_lt hmem_tail hlt_tail
    simp [pivotResetPairPathSum, splayPathSum]
    nlinarith

private theorem suffix_after_prefix_pivot_le_lowerPath_activeBudgets_of_model_bridges_const
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    {C : ℝ}
    (hactualReset :
      let ts :=
        splay
          (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
          (X m)
      splayPathSum (suffixSeq X m) ts
          (List.finRange (n - (m.val + 1))) ≤
        suffixResetUpperPathSum (suffixSeq X m) (X m) ts
          (List.finRange (n - (m.val + 1))) +
        activeBudget (suffixSeq X m) ts
          (List.finRange (n - (m.val + 1))))
    (hpairActual :
      let ts :=
        splay
          (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
          (X m)
      let xs := List.finRange (strictLowerSuffixIndices X m).length
      pivotResetPairPathSum (strictLowerSuffixSeq X m) (X m) ts xs ≤
        splayPathSum (strictLowerSuffixSeq X m) ts xs +
          C * activeBudget (strictLowerSuffixSeq X m) ts xs) :
    let ts :=
      splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m)
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      C * activeBudget (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      2 * activeBudget (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) := by
  let ts :=
    splay
      (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
      (X m)
  have hsplit :=
    suffixResetUpperPathSum_suffix_finRange_split X m ts
  have hpivotLen :
      ((pivotSuffixIndices X m).length : ℝ) ≤
        activeBudget (suffixSeq X m) ts
          (List.finRange (n - (m.val + 1))) := by
    exact pivotSuffixIndices_length_le_activeBudget_suffix X m ts
  change
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      C * activeBudget (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      2 * activeBudget (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1)))
  change
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      suffixResetUpperPathSum (suffixSeq X m) (X m) ts
        (List.finRange (n - (m.val + 1))) +
      activeBudget (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) at hactualReset
  change
    pivotResetPairPathSum (strictLowerSuffixSeq X m) (X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      C * activeBudget (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) at hpairActual
  rw [hsplit] at hactualReset
  nlinarith

private theorem suffix_after_prefix_pivot_le_lowerPath_linear_of_model_bridges_const
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    {C : ℝ} (hC : 0 ≤ C)
    (hactualReset :
      let ts :=
        splay
          (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
          (X m)
      splayPathSum (suffixSeq X m) ts
          (List.finRange (n - (m.val + 1))) ≤
        suffixResetUpperPathSum (suffixSeq X m) (X m) ts
          (List.finRange (n - (m.val + 1))) +
        activeBudget (suffixSeq X m) ts
          (List.finRange (n - (m.val + 1))))
    (hpairActual :
      let ts :=
        splay
          (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
          (X m)
      let xs := List.finRange (strictLowerSuffixIndices X m).length
      pivotResetPairPathSum (strictLowerSuffixSeq X m) (X m) ts xs ≤
        splayPathSum (strictLowerSuffixSeq X m) ts xs +
          C * activeBudget (strictLowerSuffixSeq X m) ts xs) :
    let ts :=
      splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m)
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      (C + 2) * ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ) := by
  let ts :=
    splay
      (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
      (X m)
  have hmain :=
    suffix_after_prefix_pivot_le_lowerPath_activeBudgets_of_model_bridges_const
      (m := m) (C := C) hactualReset hpairActual
  have hlowerBudget :=
    activeBudget_le_length_add_num_nodes (strictLowerSuffixSeq X m) ts
      (List.finRange (strictLowerSuffixIndices X m).length)
  have hsuffixBudget :=
    activeBudget_le_length_add_num_nodes (suffixSeq X m) ts
      (List.finRange (n - (m.val + 1)))
  have hlowerLen :=
    strictLowerSuffixIndices_length_le X m
  have hnodes : ts.num_nodes = init.num_nodes := by
    unfold ts
    rw [splay_num_nodes,
      splayTreeAfter_num_nodes (prefixSeq X m) (List.finRange m.val) init]
  rw [List.length_finRange, hnodes] at hlowerBudget hsuffixBudget
  let A : ℝ := (n - (m.val + 1) : Nat) + init.num_nodes
  have hlowerLenR :
      ((strictLowerSuffixIndices X m).length : ℝ) ≤
        (n - (m.val + 1) : Nat) := by
    exact_mod_cast hlowerLen
  have hlowerBudgetA :
      activeBudget (strictLowerSuffixSeq X m) ts
          (List.finRange (strictLowerSuffixIndices X m).length) ≤ A := by
    unfold A
    nlinarith
  have hsuffixBudgetA :
      activeBudget (suffixSeq X m) ts
          (List.finRange (n - (m.val + 1))) ≤ A := by
    unfold A
    nlinarith
  have hLowerTerm :
      C * activeBudget (strictLowerSuffixSeq X m) ts
          (List.finRange (strictLowerSuffixIndices X m).length) ≤
        C * A := by
    exact mul_le_mul_of_nonneg_left hlowerBudgetA hC
  have hSuffixTerm :
      2 * activeBudget (suffixSeq X m) ts
          (List.finRange (n - (m.val + 1))) ≤
        2 * A := by
    nlinarith
  change
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      (C + 2) * A
  change
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      C * activeBudget (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      2 * activeBudget (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) at hmain
  nlinarith

private theorem suffix_after_prefix_pivot_le_lowerPath_activeBudgets_of_model_bridges_coeff
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    {A C : ℝ}
    (hactualReset :
      let ts :=
        splay
          (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
          (X m)
      splayPathSum (suffixSeq X m) ts
          (List.finRange (n - (m.val + 1))) ≤
        suffixResetUpperPathSum (suffixSeq X m) (X m) ts
          (List.finRange (n - (m.val + 1))) +
        A * activeBudget (suffixSeq X m) ts
          (List.finRange (n - (m.val + 1))))
    (hpairActual :
      let ts :=
        splay
          (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
          (X m)
      let xs := List.finRange (strictLowerSuffixIndices X m).length
      pivotResetPairPathSum (strictLowerSuffixSeq X m) (X m) ts xs ≤
        splayPathSum (strictLowerSuffixSeq X m) ts xs +
          C * activeBudget (strictLowerSuffixSeq X m) ts xs) :
    let ts :=
      splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m)
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      C * activeBudget (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      (A + 1) * activeBudget (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) := by
  let ts :=
    splay
      (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
      (X m)
  have hsplit :=
    suffixResetUpperPathSum_suffix_finRange_split X m ts
  have hpivotLen :
      ((pivotSuffixIndices X m).length : ℝ) ≤
        activeBudget (suffixSeq X m) ts
          (List.finRange (n - (m.val + 1))) := by
    exact pivotSuffixIndices_length_le_activeBudget_suffix X m ts
  change
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      C * activeBudget (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      (A + 1) * activeBudget (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1)))
  change
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      suffixResetUpperPathSum (suffixSeq X m) (X m) ts
        (List.finRange (n - (m.val + 1))) +
      A * activeBudget (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) at hactualReset
  change
    pivotResetPairPathSum (strictLowerSuffixSeq X m) (X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      C * activeBudget (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) at hpairActual
  rw [hsplit] at hactualReset
  nlinarith

private theorem suffix_after_prefix_pivot_le_lowerPath_linear_of_model_bridges_coeff
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hactualReset :
      let ts :=
        splay
          (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
          (X m)
      splayPathSum (suffixSeq X m) ts
          (List.finRange (n - (m.val + 1))) ≤
        suffixResetUpperPathSum (suffixSeq X m) (X m) ts
          (List.finRange (n - (m.val + 1))) +
        A * activeBudget (suffixSeq X m) ts
          (List.finRange (n - (m.val + 1))))
    (hpairActual :
      let ts :=
        splay
          (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
          (X m)
      let xs := List.finRange (strictLowerSuffixIndices X m).length
      pivotResetPairPathSum (strictLowerSuffixSeq X m) (X m) ts xs ≤
        splayPathSum (strictLowerSuffixSeq X m) ts xs +
          C * activeBudget (strictLowerSuffixSeq X m) ts xs) :
    let ts :=
      splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m)
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      (C + A + 1) * ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ) := by
  let ts :=
    splay
      (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
      (X m)
  have hmain :=
    suffix_after_prefix_pivot_le_lowerPath_activeBudgets_of_model_bridges_coeff
      (m := m) (A := A) (C := C) hactualReset hpairActual
  have hlowerBudget :=
    activeBudget_le_length_add_num_nodes (strictLowerSuffixSeq X m) ts
      (List.finRange (strictLowerSuffixIndices X m).length)
  have hsuffixBudget :=
    activeBudget_le_length_add_num_nodes (suffixSeq X m) ts
      (List.finRange (n - (m.val + 1)))
  have hlowerLen :=
    strictLowerSuffixIndices_length_le X m
  have hnodes : ts.num_nodes = init.num_nodes := by
    unfold ts
    rw [splay_num_nodes,
      splayTreeAfter_num_nodes (prefixSeq X m) (List.finRange m.val) init]
  rw [List.length_finRange, hnodes] at hlowerBudget hsuffixBudget
  let B : ℝ := (n - (m.val + 1) : Nat) + init.num_nodes
  have hlowerLenR :
      ((strictLowerSuffixIndices X m).length : ℝ) ≤
        (n - (m.val + 1) : Nat) := by
    exact_mod_cast hlowerLen
  have hlowerBudgetB :
      activeBudget (strictLowerSuffixSeq X m) ts
          (List.finRange (strictLowerSuffixIndices X m).length) ≤ B := by
    unfold B
    nlinarith
  have hsuffixBudgetB :
      activeBudget (suffixSeq X m) ts
          (List.finRange (n - (m.val + 1))) ≤ B := by
    unfold B
    nlinarith
  have hLowerTerm :
      C * activeBudget (strictLowerSuffixSeq X m) ts
          (List.finRange (strictLowerSuffixIndices X m).length) ≤
        C * B := by
    exact mul_le_mul_of_nonneg_left hlowerBudgetB hC
  have hA1 : 0 ≤ A + 1 := by nlinarith
  have hSuffixTerm :
      (A + 1) * activeBudget (suffixSeq X m) ts
          (List.finRange (n - (m.val + 1))) ≤
        (A + 1) * B := by
    exact mul_le_mul_of_nonneg_left hsuffixBudgetB hA1
  change
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      (C + A + 1) * B
  change
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      C * activeBudget (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      (A + 1) * activeBudget (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) at hmain
  nlinarith

private theorem suffix_after_prefix_pivot_le_lowerPath_linear_of_generic_model_bridges_const
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    {C : ℝ} (hC : 0 ≤ C)
    (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (hsuf_le :
      ∀ j : Fin (n - (m.val + 1)), suffixSeq X m j ≤ X m)
    (hactualModel :
      ∀ {N : Nat} (Y : Fin N → Nat) (q : Nat)
        (t : BinaryTree) (xs : List (Fin N)),
        IsBST t → rootKey t = some q →
        (∀ i : Fin N, i ∈ xs → Y i ∈ t.toKeyList) →
        (∀ i : Fin N, i ∈ xs → Y i ≤ q) →
        splayPathSum Y t xs ≤
          suffixResetUpperPathSum Y q t xs + activeBudget Y t xs)
    (hpairModel :
      ∀ {N : Nat} (Y : Fin N → Nat) (q : Nat)
        (t : BinaryTree) (xs : List (Fin N)),
        IsBST t → rootKey t = some q →
        (∀ i : Fin N, i ∈ xs → Y i ∈ t.toKeyList) →
        (∀ i : Fin N, i ∈ xs → Y i < q) →
        pivotResetPairPathSum Y q t xs ≤
          splayPathSum Y t xs + C * activeBudget Y t xs) :
    let ts :=
      splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m)
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      (C + 2) * ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ) := by
  let tp :=
    splayTreeAfter (prefixSeq X m) init (List.finRange m.val)
  let ts := splay tp (X m)
  have htp_bst : IsBST tp := by
    unfold tp
    exact splayTreeAfter_isBST (prefixSeq X m)
      (List.finRange m.val) init hbst
  have hpivot_mem_tp : X m ∈ tp.toKeyList := by
    unfold tp
    rw [splayTreeAfter_toKeyList (prefixSeq X m)
      (List.finRange m.val) init]
    exact hmem m
  have hbst_ts : IsBST ts := by
    unfold ts
    exact splay_isBST tp (X m) htp_bst
  have hroot_ts : rootKey ts = some (X m) := by
    unfold ts
    exact splay_rootKey_eq_some_of_mem_isBST tp (X m)
      htp_bst hpivot_mem_tp
  have hactualReset :
      splayPathSum (suffixSeq X m) ts
          (List.finRange (n - (m.val + 1))) ≤
        suffixResetUpperPathSum (suffixSeq X m) (X m) ts
          (List.finRange (n - (m.val + 1))) +
        activeBudget (suffixSeq X m) ts
          (List.finRange (n - (m.val + 1))) := by
    apply hactualModel
    · exact hbst_ts
    · exact hroot_ts
    · intro i _hi
      unfold ts tp
      exact suffixSeq_mem_after_prefix_pivot hmem m i
    · intro i _hi
      exact hsuf_le i
  have hpairActual :
      let xs := List.finRange (strictLowerSuffixIndices X m).length
      pivotResetPairPathSum (strictLowerSuffixSeq X m) (X m) ts xs ≤
        splayPathSum (strictLowerSuffixSeq X m) ts xs +
          C * activeBudget (strictLowerSuffixSeq X m) ts xs := by
    dsimp
    apply hpairModel
    · exact hbst_ts
    · exact hroot_ts
    · intro i _hi
      unfold ts tp
      exact strictLowerSuffixSeq_mem_after_prefix_pivot hmem i
    · intro i _hi
      exact strictLowerSuffixSeq_lt_first_max X m i
  change
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      (C + 2) * ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ)
  exact
    suffix_after_prefix_pivot_le_lowerPath_linear_of_model_bridges_const
      (m := m) hC hactualReset hpairActual

private theorem suffix_after_prefix_pivot_le_lowerPath_linear_of_generic_model_bridges_coeff
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (hsuf_le :
      ∀ j : Fin (n - (m.val + 1)), suffixSeq X m j ≤ X m)
    (hactualModel :
      ∀ {N : Nat} (Y : Fin N → Nat) (q : Nat)
        (t : BinaryTree) (xs : List (Fin N)),
        IsBST t → rootKey t = some q →
        (∀ i : Fin N, i ∈ xs → Y i ∈ t.toKeyList) →
        (∀ i : Fin N, i ∈ xs → Y i ≤ q) →
        splayPathSum Y t xs ≤
          suffixResetUpperPathSum Y q t xs + A * activeBudget Y t xs)
    (hpairModel :
      ∀ {N : Nat} (Y : Fin N → Nat) (q : Nat)
        (t : BinaryTree) (xs : List (Fin N)),
        IsBST t → rootKey t = some q →
        (∀ i : Fin N, i ∈ xs → Y i ∈ t.toKeyList) →
        (∀ i : Fin N, i ∈ xs → Y i < q) →
        pivotResetPairPathSum Y q t xs ≤
          splayPathSum Y t xs + C * activeBudget Y t xs) :
    let ts :=
      splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m)
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      (C + A + 1) * ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ) := by
  let tp :=
    splayTreeAfter (prefixSeq X m) init (List.finRange m.val)
  let ts := splay tp (X m)
  have htp_bst : IsBST tp := by
    unfold tp
    exact splayTreeAfter_isBST (prefixSeq X m)
      (List.finRange m.val) init hbst
  have hpivot_mem_tp : X m ∈ tp.toKeyList := by
    unfold tp
    rw [splayTreeAfter_toKeyList (prefixSeq X m)
      (List.finRange m.val) init]
    exact hmem m
  have hbst_ts : IsBST ts := by
    unfold ts
    exact splay_isBST tp (X m) htp_bst
  have hroot_ts : rootKey ts = some (X m) := by
    unfold ts
    exact splay_rootKey_eq_some_of_mem_isBST tp (X m)
      htp_bst hpivot_mem_tp
  have hactualReset :
      splayPathSum (suffixSeq X m) ts
          (List.finRange (n - (m.val + 1))) ≤
        suffixResetUpperPathSum (suffixSeq X m) (X m) ts
          (List.finRange (n - (m.val + 1))) +
        A * activeBudget (suffixSeq X m) ts
          (List.finRange (n - (m.val + 1))) := by
    apply hactualModel
    · exact hbst_ts
    · exact hroot_ts
    · intro i _hi
      unfold ts tp
      exact suffixSeq_mem_after_prefix_pivot hmem m i
    · intro i _hi
      exact hsuf_le i
  have hpairActual :
      let xs := List.finRange (strictLowerSuffixIndices X m).length
      pivotResetPairPathSum (strictLowerSuffixSeq X m) (X m) ts xs ≤
        splayPathSum (strictLowerSuffixSeq X m) ts xs +
          C * activeBudget (strictLowerSuffixSeq X m) ts xs := by
    dsimp
    apply hpairModel
    · exact hbst_ts
    · exact hroot_ts
    · intro i _hi
      unfold ts tp
      exact strictLowerSuffixSeq_mem_after_prefix_pivot hmem i
    · intro i _hi
      exact strictLowerSuffixSeq_lt_first_max X m i
  change
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      (C + A + 1) * ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ)
  exact
    suffix_after_prefix_pivot_le_lowerPath_linear_of_model_bridges_coeff
      (m := m) hA hC hactualReset hpairActual

private theorem suffix_after_prefix_pivot_le_lowerPath_linear_of_amortized_compares_coeff
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (hsuf_le :
      ∀ j : Fin (n - (m.val + 1)), suffixSeq X m j ≤ X m)
    (hactualCompare :
      ∀ {N : Nat} (Y : Fin N → Nat) (q : Nat)
        (t : BinaryTree) (i : Fin N) (xs : List (Fin N)),
        IsBST t → rootKey t = some q →
        Y i ∈ t.toKeyList → Y i < q →
        (∀ j : Fin N, j ∈ xs → Y j ∈ t.toKeyList) →
        (∀ j : Fin N, j ∈ xs → Y j ≤ q) →
        splayPathSum Y (splay t (Y i)) xs +
            A * activeBudget Y (splay (splay t (Y i)) q) xs ≤
          (splay t (Y i)).search_path_len q +
            splayPathSum Y (splay (splay t (Y i)) q) xs +
            A * activeBudget Y t (i :: xs))
    (hpairCompare :
      ∀ {N : Nat} (Y : Fin N → Nat) (q : Nat)
        (t : BinaryTree) (i : Fin N) (xs : List (Fin N)),
        IsBST t → rootKey t = some q →
        Y i ∈ t.toKeyList → Y i < q →
        (∀ j : Fin N, j ∈ xs → Y j ∈ t.toKeyList) →
        (∀ j : Fin N, j ∈ xs → Y j < q) →
        (splay t (Y i)).search_path_len q +
            splayPathSum Y (splay (splay t (Y i)) q) xs +
            C * activeBudget Y (splay (splay t (Y i)) q) xs ≤
          splayPathSum Y (splay t (Y i)) xs +
            C * activeBudget Y t (i :: xs)) :
    let ts :=
      splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m)
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      (C + A + 1) * ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ) := by
  apply suffix_after_prefix_pivot_le_lowerPath_linear_of_generic_model_bridges_coeff
  · exact hA
  · exact hC
  · exact hbst
  · exact hmem
  · exact hsuf_le
  · intro N Y q t xs hbst_t hroot_t hmem_xs hle_xs
    exact rooted_actualModel_of_amortized_reset_compare_const
      A hA Y q (hactualCompare Y q) xs t hbst_t hroot_t hmem_xs hle_xs
  · intro N Y q t xs hbst_t hroot_t hmem_xs hlt_xs
    exact rooted_pairModel_of_amortized_reset_compare_const
      C Y q (hpairCompare Y q) xs t hbst_t hroot_t hmem_xs hlt_xs

private theorem suffix_after_prefix_pivot_le_lowerPath_linear_of_amortized_compares_const
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    {C : ℝ} (hC : 0 ≤ C)
    (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (hsuf_le :
      ∀ j : Fin (n - (m.val + 1)), suffixSeq X m j ≤ X m)
    (hactualCompare :
      ∀ {N : Nat} (Y : Fin N → Nat) (q : Nat)
        (t : BinaryTree) (i : Fin N) (xs : List (Fin N)),
        IsBST t → rootKey t = some q →
        Y i ∈ t.toKeyList → Y i < q →
        (∀ j : Fin N, j ∈ xs → Y j ∈ t.toKeyList) →
        (∀ j : Fin N, j ∈ xs → Y j ≤ q) →
        splayPathSum Y (splay t (Y i)) xs +
            activeBudget Y (splay (splay t (Y i)) q) xs ≤
          (splay t (Y i)).search_path_len q +
            splayPathSum Y (splay (splay t (Y i)) q) xs +
            activeBudget Y t (i :: xs))
    (hpairCompare :
      ∀ {N : Nat} (Y : Fin N → Nat) (q : Nat)
        (t : BinaryTree) (i : Fin N) (xs : List (Fin N)),
        IsBST t → rootKey t = some q →
        Y i ∈ t.toKeyList → Y i < q →
        (∀ j : Fin N, j ∈ xs → Y j ∈ t.toKeyList) →
        (∀ j : Fin N, j ∈ xs → Y j < q) →
        (splay t (Y i)).search_path_len q +
            splayPathSum Y (splay (splay t (Y i)) q) xs +
            C * activeBudget Y (splay (splay t (Y i)) q) xs ≤
          splayPathSum Y (splay t (Y i)) xs +
            C * activeBudget Y t (i :: xs)) :
    let ts :=
      splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m)
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      (C + 2) * ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ) := by
  apply suffix_after_prefix_pivot_le_lowerPath_linear_of_generic_model_bridges_const
  · exact hC
  · exact hbst
  · exact hmem
  · exact hsuf_le
  · intro N Y q t xs hbst_t hroot_t hmem_xs hle_xs
    exact rooted_actualModel_of_amortized_reset_compare
      Y q (hactualCompare Y q) xs t hbst_t hroot_t hmem_xs hle_xs
  · intro N Y q t xs hbst_t hroot_t hmem_xs hlt_xs
    exact rooted_pairModel_of_amortized_reset_compare_const
      C Y q (hpairCompare Y q) xs t hbst_t hroot_t hmem_xs hlt_xs

private theorem rooted_actualModel_nil {n : Nat}
    (Y : Fin n → Nat) (q : Nat) (t : BinaryTree) :
    splayPathSum Y t [] ≤
      suffixResetUpperPathSum Y q t [] + activeBudget Y t [] := by
  simp [splayPathSum, suffixResetUpperPathSum, activeBudget]

private theorem rooted_actualModel_singleton {n : Nat}
    (Y : Fin n → Nat) (q : Nat) (t : BinaryTree) (i : Fin n)
    (hroot : rootKey t = some q)
    (hi_le : Y i ≤ q) :
    splayPathSum Y t [i] ≤
      suffixResetUpperPathSum Y q t [i] + activeBudget Y t [i] := by
  by_cases hlt : Y i < q
  · simp [splayPathSum, suffixResetUpperPathSum, hlt]
    have hbudget_nonneg := activeBudget_nonneg Y t [i]
    nlinarith [show 0 ≤ (((splay t (Y i)).search_path_len q : Nat) : ℝ) by positivity]
  · have heq : Y i = q := by omega
    have hpath : t.search_path_len (Y i) = 1 := by
      rw [heq]
      exact search_path_len_eq_one_of_rootKey_eq_some hroot
    simp [splayPathSum, suffixResetUpperPathSum, hlt, hpath]
    exact activeBudget_nonneg Y t [i]

private theorem rooted_pairModel_nil {n : Nat}
    (Y : Fin n → Nat) (q : Nat) (t : BinaryTree) :
    pivotResetPairPathSum Y q t [] ≤
      splayPathSum Y t [] + 5 * activeBudget Y t [] := by
  simp [pivotResetPairPathSum, splayPathSum, activeBudget]

private theorem rooted_pairModel_singleton {n : Nat}
    (Y : Fin n → Nat) (q : Nat) (t : BinaryTree) (i : Fin n)
    (hbst : IsBST t) (hroot : rootKey t = some q)
    (hi_mem : Y i ∈ t.toKeyList) (hi_lt : Y i < q) :
    pivotResetPairPathSum Y q t [i] ≤
      splayPathSum Y t [i] + 5 * activeBudget Y t [i] := by
  have hleft : Y i ∈ (leftSubtree t).toKeyList :=
    mem_leftSubtree_of_root_lt_isBST hbst hroot hi_mem hi_lt
  have hreset :=
    rooted_pivot_reset_search_path_le hbst hroot hleft
  have hbudget :=
    search_path_len_real_le_activeBudget_of_mem Y [i] hbst
      (i := i) (by simp)
  have hresetR :
      (((splay t (Y i)).search_path_len q : Nat) : ℝ) ≤
        (t.search_path_len (Y i) : ℝ) := by
    exact_mod_cast hreset
  have hbudget_nonneg := activeBudget_nonneg Y t [i]
  simp [pivotResetPairPathSum, splayPathSum]
  nlinarith

private theorem rooted_actualModel_length_le_one {n : Nat}
    (Y : Fin n → Nat) (q : Nat) (t : BinaryTree) (xs : List (Fin n))
    (hroot : rootKey t = some q)
    (hle : ∀ i : Fin n, i ∈ xs → Y i ≤ q)
    (hlen : xs.length ≤ 1) :
    splayPathSum Y t xs ≤
      suffixResetUpperPathSum Y q t xs + activeBudget Y t xs := by
  cases xs with
  | nil =>
      exact rooted_actualModel_nil Y q t
  | cons i xs =>
      cases xs with
      | nil =>
          exact rooted_actualModel_singleton Y q t i hroot
            (hle i (by simp))
      | cons j xs =>
          simp at hlen

private theorem rooted_pairModel_length_le_one {n : Nat}
    (Y : Fin n → Nat) (q : Nat) (t : BinaryTree) (xs : List (Fin n))
    (hbst : IsBST t) (hroot : rootKey t = some q)
    (hmem : ∀ i : Fin n, i ∈ xs → Y i ∈ t.toKeyList)
    (hlt : ∀ i : Fin n, i ∈ xs → Y i < q)
    (hlen : xs.length ≤ 1) :
    pivotResetPairPathSum Y q t xs ≤
      splayPathSum Y t xs + 5 * activeBudget Y t xs := by
  cases xs with
  | nil =>
      exact rooted_pairModel_nil Y q t
  | cons i xs =>
      cases xs with
      | nil =>
          exact rooted_pairModel_singleton Y q t i hbst hroot
            (hmem i (by simp)) (hlt i (by simp))
      | cons j xs =>
          simp at hlen

private theorem suffixResetUpperPathSum_nonneg {n : Nat}
    (Y : Fin n → Nat) (q : Nat) :
    ∀ (xs : List (Fin n)) (t : BinaryTree),
      0 ≤ suffixResetUpperPathSum Y q t xs
| [], t => by
    simp [suffixResetUpperPathSum]
| i :: xs, t => by
    by_cases hlt : Y i < q
    · have ih :=
        suffixResetUpperPathSum_nonneg Y q xs
          (splay (splay t (Y i)) q)
      simp [suffixResetUpperPathSum, hlt]
      positivity
    · have ih := suffixResetUpperPathSum_nonneg Y q xs t
      simp [suffixResetUpperPathSum, hlt]
      positivity

private theorem rooted_actualModel_length_le_two {n : Nat}
    (Y : Fin n → Nat) (q : Nat) (t : BinaryTree) (xs : List (Fin n))
    (hbst : IsBST t) (hroot : rootKey t = some q)
    (hmem : ∀ i : Fin n, i ∈ xs → Y i ∈ t.toKeyList)
    (hle : ∀ i : Fin n, i ∈ xs → Y i ≤ q)
    (hlen : xs.length ≤ 2) :
    splayPathSum Y t xs ≤
      suffixResetUpperPathSum Y q t xs + activeBudget Y t xs := by
  cases xs with
  | nil =>
      exact rooted_actualModel_nil Y q t
  | cons i xs =>
      cases xs with
      | nil =>
          exact rooted_actualModel_singleton Y q t i hroot
            (hle i (by simp))
      | cons j xs =>
          cases xs with
          | nil =>
              have hi_mem : Y i ∈ t.toKeyList := hmem i (by simp)
              have hj_mem : Y j ∈ t.toKeyList := hmem j (by simp)
              have hi_le : Y i ≤ q := hle i (by simp)
              have hj_le : Y j ≤ q := hle j (by simp)
              by_cases hi_lt : Y i < q
              · let t1 := splay t (Y i)
                have hbst_t1 : IsBST t1 := by
                  unfold t1
                  exact splay_isBST t (Y i) hbst
                have hpath_j :
                    (t1.search_path_len (Y j) : ℝ) ≤
                      activeBudget Y t1 [j] := by
                  exact search_path_len_real_le_activeBudget_of_mem
                    Y [j] hbst_t1 (i := j) (by simp)
                have hbudget_drop :
                    activeBudget Y t1 [j] ≤ activeBudget Y t [i, j] := by
                  unfold t1
                  exact activeBudget_after_splay_le_cons
                    Y i [j] hbst hi_mem
                    (by
                      intro a ha
                      simp at ha
                      subst a
                      exact hj_mem)
                have hsuf_nonneg :
                    0 ≤ suffixResetUpperPathSum Y q
                      (splay (splay t (Y i)) q) [j] :=
                  suffixResetUpperPathSum_nonneg Y q [j]
                    (splay (splay t (Y i)) q)
                have hpath_j_old :
                    (((splay t (Y i)).search_path_len (Y j) : Nat) : ℝ) ≤
                      activeBudget Y t [i, j] := by
                  simpa [t1] using le_trans hpath_j hbudget_drop
                simp [suffixResetUpperPathSum] at hsuf_nonneg
                simp [splayPathSum, suffixResetUpperPathSum, hi_lt]
                nlinarith [hpath_j_old, hsuf_nonneg,
                  show 0 ≤ (((splay t (Y i)).search_path_len q : Nat) : ℝ) by positivity]
              · have hi_eq : Y i = q := by omega
                have hpath_i : t.search_path_len (Y i) = 1 := by
                  rw [hi_eq]
                  exact search_path_len_eq_one_of_rootKey_eq_some hroot
                have hsplay_i : splay t (Y i) = t := by
                  rw [hi_eq]
                  exact splay_eq_self_of_rootKey_eq_some hroot
                have hsingle :=
                  rooted_actualModel_singleton Y q t j hroot hj_le
                have hbudget_tail :
                    activeBudget Y t [j] ≤ activeBudget Y t [i, j] := by
                  exact activeBudget_sublist_le Y t
                    (List.Sublist.cons i (List.Sublist.refl [j]))
                have hsingle_old :
                    (t.search_path_len (Y j) : ℝ) ≤
                      suffixResetUpperPathSum Y q t [j] +
                        activeBudget Y t [i, j] := by
                  have hsingle' :
                      (t.search_path_len (Y j) : ℝ) ≤
                        suffixResetUpperPathSum Y q t [j] +
                          activeBudget Y t [j] := by
                    simpa [splayPathSum] using hsingle
                  nlinarith
                simp [suffixResetUpperPathSum] at hsingle_old
                simp [splayPathSum, suffixResetUpperPathSum, hi_lt,
                  hpath_i, hsplay_i]
                nlinarith [hsingle_old]
          | cons k xs =>
              simp at hlen
              omega

private theorem rooted_pairModel_length_le_two {n : Nat}
    (Y : Fin n → Nat) (q : Nat) (t : BinaryTree) (xs : List (Fin n))
    (hbst : IsBST t) (hroot : rootKey t = some q)
    (hmem : ∀ i : Fin n, i ∈ xs → Y i ∈ t.toKeyList)
    (hlt : ∀ i : Fin n, i ∈ xs → Y i < q)
    (hlen : xs.length ≤ 2) :
    pivotResetPairPathSum Y q t xs ≤
      splayPathSum Y t xs + 5 * activeBudget Y t xs := by
  cases xs with
  | nil =>
      exact rooted_pairModel_nil Y q t
  | cons i xs =>
      cases xs with
      | nil =>
          exact rooted_pairModel_singleton Y q t i hbst hroot
            (hmem i (by simp)) (hlt i (by simp))
      | cons j xs =>
          cases xs with
          | nil =>
              have hi_mem : Y i ∈ t.toKeyList := hmem i (by simp)
              have hj_mem : Y j ∈ t.toKeyList := hmem j (by simp)
              have hi_lt : Y i < q := hlt i (by simp)
              have hj_lt : Y j < q := hlt j (by simp)
              let t1 := splay t (Y i)
              let tr := splay t1 q
              have hleft_i : Y i ∈ (leftSubtree t).toKeyList :=
                mem_leftSubtree_of_root_lt_isBST hbst hroot hi_mem hi_lt
              have hreset_i_nat :
                  (splay t (Y i)).search_path_len q ≤
                    t.search_path_len (Y i) :=
                rooted_pivot_reset_search_path_le hbst hroot hleft_i
              have hpath_i_budget :
                  (t.search_path_len (Y i) : ℝ) ≤
                    activeBudget Y t [i, j] :=
                search_path_len_real_le_activeBudget_of_mem
                  Y [i, j] hbst (i := i) (by simp)
              have hreset_i_budget :
                  (((splay t (Y i)).search_path_len q : Nat) : ℝ) ≤
                    activeBudget Y t [i, j] := by
                exact le_trans (by exact_mod_cast hreset_i_nat) hpath_i_budget
              have hbst_tr : IsBST tr := by
                unfold tr t1
                exact splay_isBST (splay t (Y i)) q
                  (splay_isBST t (Y i) hbst)
              have hroot_tr : rootKey tr = some q := by
                unfold tr t1
                exact rootKey_after_pivot_reset_of_root hbst hroot
              have hj_mem_tr : Y j ∈ tr.toKeyList := by
                unfold tr t1
                rw [splay_toKeyList, splay_toKeyList]
                exact hj_mem
              have hleft_j_tr :
                  Y j ∈ (leftSubtree tr).toKeyList :=
                mem_leftSubtree_of_root_lt_isBST
                  hbst_tr hroot_tr hj_mem_tr hj_lt
              have hpair_j_nat :
                  tr.search_path_len (Y j) +
                      (splay tr (Y j)).search_path_len q ≤
                    2 * tr.search_path_len (Y j) :=
                rooted_pivot_access_reset_pair_path_le
                  hbst_tr hroot_tr hleft_j_tr
              have hpath_j_tr_budget :
                  (tr.search_path_len (Y j) : ℝ) ≤
                    activeBudget Y tr [j] := by
                exact search_path_len_real_le_activeBudget_of_mem
                  Y [j] hbst_tr (i := j) (by simp)
              have hbudget_drop :
                  activeBudget Y tr [j] ≤ activeBudget Y t [i, j] := by
                unfold tr t1
                exact activeBudget_after_access_reset_le_cons
                  Y q i [j] hbst hroot hi_mem
                  (by
                    intro a ha
                    simp at ha
                    subst a
                    exact hj_mem)
              have hpair_j_budget :
                  (tr.search_path_len (Y j) : ℝ) +
                      ((splay tr (Y j)).search_path_len q : ℝ) ≤
                    2 * activeBudget Y t [i, j] := by
                have hpair_j_real :
                    (tr.search_path_len (Y j) : ℝ) +
                        ((splay tr (Y j)).search_path_len q : ℝ) ≤
                      2 * (tr.search_path_len (Y j) : ℝ) := by
                  exact_mod_cast hpair_j_nat
                nlinarith [hpair_j_real, hpath_j_tr_budget, hbudget_drop]
              have hpair_j_budget_old :
                  (((splay (splay t (Y i)) q).search_path_len (Y j) : Nat) : ℝ) +
                      (((splay (splay (splay t (Y i)) q) (Y j)).search_path_len q : Nat) : ℝ) ≤
                    2 * activeBudget Y t [i, j] := by
                simpa [tr, t1] using hpair_j_budget
              simp [pivotResetPairPathSum, splayPathSum]
              nlinarith [hreset_i_budget, hpair_j_budget_old,
                show 0 ≤ (((splay t (Y i)).search_path_len (Y j) : Nat) : ℝ) by positivity,
                activeBudget_nonneg Y t [i, j]]
          | cons k xs =>
              simp at hlen
              omega

private theorem resetModel_with_initial_search_length_le_one {n : Nat}
    (Y : Fin n → Nat) (q : Nat) (t : BinaryTree) (xs : List (Fin n))
    (hbst : IsBST t)
    (hmem : ∀ i : Fin n, i ∈ xs → Y i ∈ t.toKeyList)
    (hle : ∀ i : Fin n, i ∈ xs → Y i ≤ q)
    (hlen : xs.length ≤ 1) :
    splayPathSum Y t xs ≤
      (t.search_path_len q : ℝ) +
        suffixResetUpperPathSum Y q (splay t q) xs +
        activeBudget Y t xs := by
  cases xs with
  | nil =>
      simp [splayPathSum, suffixResetUpperPathSum, activeBudget,
        activeHullSize_nil]
  | cons i xs =>
      cases xs with
      | nil =>
          have hi_mem : Y i ∈ t.toKeyList := hmem i (by simp)
          have hi_le : Y i ≤ q := hle i (by simp)
          by_cases hi_lt : Y i < q
          · have hpath_budget :
                (t.search_path_len (Y i) : ℝ) ≤ activeBudget Y t [i] :=
              search_path_len_real_le_activeBudget_of_mem Y [i] hbst
                (i := i) (by simp)
            simp [splayPathSum, suffixResetUpperPathSum, hi_lt]
            nlinarith [
              show 0 ≤ ((t.search_path_len q : Nat) : ℝ) by positivity,
              show 0 ≤ (((splay t q).search_path_len (Y i) : Nat) : ℝ) by positivity,
              show 0 ≤ (((splay (splay t q) (Y i)).search_path_len q : Nat) : ℝ) by positivity]
          · have hi_eq : Y i = q := by omega
            simp [splayPathSum, suffixResetUpperPathSum, hi_eq]
            nlinarith [activeBudget_nonneg Y t [i]]
      | cons j xs =>
          simp at hlen

private theorem lower_continuation_length_le_one {n : Nat}
    (Y : Fin n → Nat) (q : Nat) (t : BinaryTree)
    (i : Fin n) (xs : List (Fin n))
    (hbst : IsBST t)
    (hi_mem : Y i ∈ t.toKeyList) (_hi_lt : Y i < q)
    (hmem_tail : ∀ j : Fin n, j ∈ xs → Y j ∈ t.toKeyList)
    (hle_tail : ∀ j : Fin n, j ∈ xs → Y j ≤ q)
    (hlen : xs.length ≤ 1) :
    splayPathSum Y (splay t (Y i)) xs ≤
      ((splay t (Y i)).search_path_len q : ℝ) +
        suffixResetUpperPathSum Y q
          (splay (splay t (Y i)) q) xs +
        activeBudget Y t (i :: xs) := by
  let t1 := splay t (Y i)
  have hbst_t1 : IsBST t1 := by
    unfold t1
    exact splay_isBST t (Y i) hbst
  have hmem_t1 :
      ∀ j : Fin n, j ∈ xs → Y j ∈ t1.toKeyList := by
    intro j hj
    unfold t1
    rw [splay_toKeyList]
    exact hmem_tail j hj
  have hmodel :=
    resetModel_with_initial_search_length_le_one
      Y q t1 xs hbst_t1 hmem_t1 hle_tail hlen
  have hbudget :
      activeBudget Y t1 xs ≤ activeBudget Y t (i :: xs) := by
    unfold t1
    exact activeBudget_after_splay_le_cons
      Y i xs hbst hi_mem hmem_tail
  simpa [t1] using (by nlinarith [hmodel, hbudget] :
    splayPathSum Y t1 xs ≤
      (t1.search_path_len q : ℝ) +
        suffixResetUpperPathSum Y q (splay t1 q) xs +
        activeBudget Y t (i :: xs))

private theorem suffix_after_prefix_pivot_le_lowerPath_linear_of_short_suffix
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (hsuf_le :
      ∀ j : Fin (n - (m.val + 1)), suffixSeq X m j ≤ X m)
    (hlen : n - (m.val + 1) ≤ 2) :
    let ts :=
      splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m)
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      7 * ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ) := by
  let tp := splayTreeAfter (prefixSeq X m) init (List.finRange m.val)
  let ts := splay tp (X m)
  have htp_bst : IsBST tp := by
    unfold tp
    exact splayTreeAfter_isBST (prefixSeq X m)
      (List.finRange m.val) init hbst
  have hpivot_mem_tp : X m ∈ tp.toKeyList := by
    unfold tp
    rw [splayTreeAfter_toKeyList (prefixSeq X m)
      (List.finRange m.val) init]
    exact hmem m
  have hbst_ts : IsBST ts := by
    unfold ts
    exact splay_isBST tp (X m) htp_bst
  have hroot_ts : rootKey ts = some (X m) := by
    unfold ts
    exact splay_rootKey_eq_some_of_mem_isBST tp (X m)
      htp_bst hpivot_mem_tp
  have hactualReset :
      splayPathSum (suffixSeq X m) ts
          (List.finRange (n - (m.val + 1))) ≤
        suffixResetUpperPathSum (suffixSeq X m) (X m) ts
          (List.finRange (n - (m.val + 1))) +
        activeBudget (suffixSeq X m) ts
          (List.finRange (n - (m.val + 1))) := by
    apply rooted_actualModel_length_le_two
    · exact hbst_ts
    · exact hroot_ts
    · intro i _hi
      exact suffixSeq_mem_after_prefix_pivot hmem m i
    · intro i _hi
      exact hsuf_le i
    · simpa [List.length_finRange] using hlen
  have hlower_len : (strictLowerSuffixIndices X m).length ≤ 2 := by
    exact le_trans (strictLowerSuffixIndices_length_le X m) hlen
  have hpairActual :
      let xs := List.finRange (strictLowerSuffixIndices X m).length
      pivotResetPairPathSum (strictLowerSuffixSeq X m) (X m) ts xs ≤
        splayPathSum (strictLowerSuffixSeq X m) ts xs +
          5 * activeBudget (strictLowerSuffixSeq X m) ts xs := by
    dsimp
    apply rooted_pairModel_length_le_two
    · exact hbst_ts
    · exact hroot_ts
    · intro i _hi
      unfold ts tp
      exact strictLowerSuffixSeq_mem_after_prefix_pivot hmem i
    · intro i _hi
      exact strictLowerSuffixSeq_lt_first_max X m i
    · simpa [List.length_finRange] using hlower_len
  change
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      7 * ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ)
  exact
    suffix_after_prefix_pivot_le_lowerPath_linear_of_model_bridges
      (m := m) hactualReset hpairActual

private theorem suffix_after_prefix_pivot_le_lowerPath_linear_of_suffix_length_le_two
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    (hlen : n - (m.val + 1) ≤ 2) :
    let ts :=
      splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m)
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      7 * ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ) := by
  let tp := splayTreeAfter (prefixSeq X m) init (List.finRange m.val)
  let ts := splay tp (X m)
  have hsufBound :=
    splayPathSum_le_length_mul_num_nodes (suffixSeq X m)
      (List.finRange (n - (m.val + 1))) ts
  have hnodes : ts.num_nodes = init.num_nodes := by
    unfold ts tp
    rw [splay_num_nodes,
      splayTreeAfter_num_nodes (prefixSeq X m) (List.finRange m.val) init]
  rw [List.length_finRange, hnodes] at hsufBound
  have hlowerNonneg :=
    splayPathSum_nonneg (strictLowerSuffixSeq X m)
      (List.finRange (strictLowerSuffixIndices X m).length) ts
  have hlenR : ((n - (m.val + 1) : Nat) : ℝ) ≤ 2 := by
    exact_mod_cast hlen
  change
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      7 * ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ)
  nlinarith [show 0 ≤ ((n - (m.val + 1) : Nat) : ℝ) by positivity,
    show 0 ≤ (init.num_nodes : ℝ) by positivity]

private theorem suffix_after_prefix_pivot_le_lowerPath_linear_of_suffix_length_le_seven
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    (hlen : n - (m.val + 1) ≤ 7) :
    let ts :=
      splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m)
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      7 * ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ) := by
  let tp := splayTreeAfter (prefixSeq X m) init (List.finRange m.val)
  let ts := splay tp (X m)
  have hsufBound :=
    splayPathSum_le_length_mul_num_nodes (suffixSeq X m)
      (List.finRange (n - (m.val + 1))) ts
  have hnodes : ts.num_nodes = init.num_nodes := by
    unfold ts tp
    rw [splay_num_nodes,
      splayTreeAfter_num_nodes (prefixSeq X m) (List.finRange m.val) init]
  rw [List.length_finRange, hnodes] at hsufBound
  have hlowerNonneg :=
    splayPathSum_nonneg (strictLowerSuffixSeq X m)
      (List.finRange (strictLowerSuffixIndices X m).length) ts
  have hlenR : ((n - (m.val + 1) : Nat) : ℝ) ≤ 7 := by
    exact_mod_cast hlen
  change
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      7 * ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ)
  nlinarith [show 0 ≤ ((n - (m.val + 1) : Nat) : ℝ) by positivity,
    show 0 ≤ (init.num_nodes : ℝ) by positivity]

private theorem suffix_after_prefix_pivot_le_lowerPath_linear_of_amortized_compares
    {n : Nat} {X : Fin n → Nat} {init : BinaryTree} {m : Fin n}
    (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (hsuf_le :
      ∀ j : Fin (n - (m.val + 1)), suffixSeq X m j ≤ X m)
    (hactualCompare :
      ∀ {N : Nat} (Y : Fin N → Nat) (q : Nat)
        (t : BinaryTree) (i : Fin N) (xs : List (Fin N)),
        IsBST t → rootKey t = some q →
        Y i ∈ t.toKeyList → Y i < q →
        (∀ j : Fin N, j ∈ xs → Y j ∈ t.toKeyList) →
        (∀ j : Fin N, j ∈ xs → Y j ≤ q) →
        splayPathSum Y (splay t (Y i)) xs +
            activeBudget Y (splay (splay t (Y i)) q) xs ≤
          (splay t (Y i)).search_path_len q +
            splayPathSum Y (splay (splay t (Y i)) q) xs +
            activeBudget Y t (i :: xs))
    (hpairCompare :
      ∀ {N : Nat} (Y : Fin N → Nat) (q : Nat)
        (t : BinaryTree) (i : Fin N) (xs : List (Fin N)),
        IsBST t → rootKey t = some q →
        Y i ∈ t.toKeyList → Y i < q →
        (∀ j : Fin N, j ∈ xs → Y j ∈ t.toKeyList) →
        (∀ j : Fin N, j ∈ xs → Y j < q) →
        (splay t (Y i)).search_path_len q +
            splayPathSum Y (splay (splay t (Y i)) q) xs +
            5 * activeBudget Y (splay (splay t (Y i)) q) xs ≤
          splayPathSum Y (splay t (Y i)) xs +
            5 * activeBudget Y t (i :: xs)) :
    let ts :=
      splay
        (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
        (X m)
    splayPathSum (suffixSeq X m) ts
        (List.finRange (n - (m.val + 1))) ≤
      splayPathSum (strictLowerSuffixSeq X m) ts
        (List.finRange (strictLowerSuffixIndices X m).length) +
      7 * ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ) := by
  apply suffix_after_prefix_pivot_le_lowerPath_linear_of_generic_model_bridges
  · exact hbst
  · exact hmem
  · exact hsuf_le
  · intro N Y q t xs hbst_t hroot_t hmem_xs hle_xs
    exact rooted_actualModel_of_amortized_reset_compare
      Y q (hactualCompare Y q) xs t hbst_t hroot_t hmem_xs hle_xs
  · intro N Y q t xs hbst_t hroot_t hmem_xs hlt_xs
    exact rooted_pairModel_of_amortized_reset_compare
      Y q (hpairCompare Y q) xs t hbst_t hroot_t hmem_xs hlt_xs

private theorem finRange_take_eq_map_prefixIndex {n : Nat} (m : Fin n) :
    (List.finRange n).take m.val =
      (List.finRange m.val).map (prefixIndex m) := by
  apply List.ext_getElem
  · simp [List.length_take, List.length_finRange]
  · intro i hleft hright
    simp [List.getElem_take, List.getElem_finRange, prefixIndex]

private theorem finRange_drop_eq_map_suffixIndex {n : Nat} (m : Fin n) :
    (List.finRange n).drop (m.val + 1) =
      (List.finRange (n - (m.val + 1))).map (suffixIndex m) := by
  apply List.ext_getElem
  · simp [List.length_drop, List.length_finRange]
  · intro i hleft hright
    simp [List.getElem_drop, List.getElem_finRange, suffixIndex]

private theorem splayPathSum_take_eq_prefixSeq {n : Nat}
    (X : Fin n → Nat) (init : BinaryTree) (m : Fin n) :
    splayPathSum X init ((List.finRange n).take m.val) =
      splayPathSum (prefixSeq X m) init (List.finRange m.val) := by
  rw [finRange_take_eq_map_prefixIndex m,
    splayPathSum_map_comp X (prefixIndex m)]
  rfl

private theorem splayPathSum_drop_eq_suffixSeq {n : Nat}
    (X : Fin n → Nat) (init : BinaryTree) (m : Fin n) :
    splayPathSum X init ((List.finRange n).drop (m.val + 1)) =
      splayPathSum (suffixSeq X m) init
        (List.finRange (n - (m.val + 1))) := by
  rw [finRange_drop_eq_map_suffixIndex m,
    splayPathSum_map_comp X (suffixIndex m)]
  rfl

private theorem activeBudget_take_eq_prefixSeq {n : Nat}
    (X : Fin n → Nat) (init : BinaryTree) (m : Fin n) :
    activeBudget X init ((List.finRange n).take m.val) =
      activeBudget (prefixSeq X m) init (List.finRange m.val) := by
  rw [finRange_take_eq_map_prefixIndex m,
    activeBudget_map_comp X (prefixIndex m)]
  rfl

private theorem activeBudget_drop_eq_suffixSeq {n : Nat}
    (X : Fin n → Nat) (init : BinaryTree) (m : Fin n) :
    activeBudget X init ((List.finRange n).drop (m.val + 1)) =
      activeBudget (suffixSeq X m) init
        (List.finRange (n - (m.val + 1))) := by
  rw [finRange_drop_eq_map_suffixIndex m,
    activeBudget_map_comp X (suffixIndex m)]
  rfl

private theorem activeBudget_finRange_split_le {n : Nat}
    (X : Fin n → Nat) (init : BinaryTree) (m : Fin n)
    (hbst : IsBST init) :
    activeBudget X init (List.finRange n) ≤
      activeBudget (prefixSeq X m) init (List.finRange m.val) +
        activeBudget (suffixSeq X m) init
          (List.finRange (n - (m.val + 1))) +
        (1 + init.num_nodes : ℝ) := by
  let pre := (List.finRange n).take m.val
  let suf := (List.finRange n).drop (m.val + 1)
  have hsplit : List.finRange n = pre ++ ([m] ++ suf) := by
    unfold pre suf
    simpa [List.append_assoc] using finRange_split_at m
  have hmain :
      activeBudget X init (pre ++ ([m] ++ suf)) ≤
        activeBudget X init pre + activeBudget X init ([m] ++ suf) :=
    activeBudget_append_le X pre ([m] ++ suf) hbst
  have htail :
      activeBudget X init ([m] ++ suf) ≤
        activeBudget X init [m] + activeBudget X init suf :=
    activeBudget_append_le X [m] suf hbst
  have hsingle :
      activeBudget X init [m] ≤ (1 : ℝ) + init.num_nodes := by
    simpa using activeBudget_le_length_add_num_nodes X init [m]
  have hpre :
      activeBudget X init pre =
        activeBudget (prefixSeq X m) init (List.finRange m.val) := by
    unfold pre
    exact activeBudget_take_eq_prefixSeq X init m
  have hsuf :
      activeBudget X init suf =
        activeBudget (suffixSeq X m) init
          (List.finRange (n - (m.val + 1))) := by
    unfold suf
    exact activeBudget_drop_eq_suffixSeq X init m
  calc
    activeBudget X init (List.finRange n)
        = activeBudget X init (pre ++ ([m] ++ suf)) := by
          rw [hsplit]
    _ ≤ activeBudget X init pre + activeBudget X init ([m] ++ suf) :=
          hmain
    _ ≤ activeBudget X init pre +
          (activeBudget X init [m] + activeBudget X init suf) := by
          nlinarith [htail]
    _ ≤ activeBudget (prefixSeq X m) init (List.finRange m.val) +
          activeBudget (suffixSeq X m) init
            (List.finRange (n - (m.val + 1))) +
          (1 + init.num_nodes : ℝ) := by
          rw [hpre, hsuf]
          nlinarith [hsingle]

private theorem splayTreeAfter_take_eq_prefixSeq {n : Nat}
    (X : Fin n → Nat) (init : BinaryTree) (m : Fin n) :
    splayTreeAfter X init ((List.finRange n).take m.val) =
      splayTreeAfter (prefixSeq X m) init (List.finRange m.val) := by
  rw [finRange_take_eq_map_prefixIndex m,
    splayTreeAfter_map_comp X (prefixIndex m)]
  rfl

private theorem splayTreeAfter_drop_eq_suffixSeq {n : Nat}
    (X : Fin n → Nat) (init : BinaryTree) (m : Fin n) :
    splayTreeAfter X init ((List.finRange n).drop (m.val + 1)) =
      splayTreeAfter (suffixSeq X m) init
        (List.finRange (n - (m.val + 1))) := by
  rw [finRange_drop_eq_map_suffixIndex m,
    splayTreeAfter_map_comp X (suffixIndex m)]
  rfl

private theorem splayPathSum_finRange_prefix_pivot_suffix {n : Nat}
    (X : Fin n → Nat) (init : BinaryTree) (m : Fin n) :
    splayPathSum X init (List.finRange n) =
      splayPathSum (prefixSeq X m) init (List.finRange m.val) +
        ((splayTreeAfter (prefixSeq X m) init
            (List.finRange m.val)).search_path_len (X m) +
          splayPathSum (suffixSeq X m)
            (splay
              (splayTreeAfter (prefixSeq X m) init
                (List.finRange m.val))
              (X m))
            (List.finRange (n - (m.val + 1)))) := by
  have hsplit := splayPathSum_finRange_split_at X init m
  rw [splayPathSum_take_eq_prefixSeq X init m] at hsplit
  rw [splayTreeAfter_take_eq_prefixSeq X init m] at hsplit
  rw [splayPathSum_drop_eq_suffixSeq X
    (splay
      (splayTreeAfter (prefixSeq X m) init (List.finRange m.val))
      (X m)) m] at hsplit
  exact hsplit

private theorem firstMax_pivot_search_len_le_activeBudget {n : Nat}
    (X : Fin n → Nat) (init : BinaryTree) (m : Fin n)
    (h_size : init.num_nodes = n) :
    ((splayTreeAfter (prefixSeq X m) init
        (List.finRange m.val)).search_path_len (X m) : ℝ) ≤
      activeBudget X init (List.finRange n) := by
  have hpath_nat :=
    search_path_len_le_num_nodes
      (splayTreeAfter (prefixSeq X m) init (List.finRange m.val)) (X m)
  have hnodes :=
    splayTreeAfter_num_nodes (prefixSeq X m) (List.finRange m.val) init
  have hpath_n : (splayTreeAfter (prefixSeq X m) init
        (List.finRange m.val)).search_path_len (X m) ≤ n := by
    rw [hnodes, h_size] at hpath_nat
    exact hpath_nat
  have hpathR :
      ((splayTreeAfter (prefixSeq X m) init
        (List.finRange m.val)).search_path_len (X m) : ℝ) ≤ n := by
    exact_mod_cast hpath_n
  have hbudget := finRange_length_le_activeBudget X init
  exact le_trans hpathR hbudget

set_option linter.flexible false in
private theorem contains231_iff_exists_triple {n : Nat} {X : Fin n → Nat} :
    contains_pattern X (![2, 3, 1] : Fin 3 → Nat) ↔
      ∃ i j k : Fin n, i < j ∧ j < k ∧ X k < X i ∧ X i < X j := by
  constructor
  · rintro ⟨f, hf, hcmp⟩
    refine ⟨f (0 : Fin 3), f (1 : Fin 3), f (2 : Fin 3), ?_, ?_, ?_, ?_⟩
    · exact hf (show (0 : Fin 3) < (1 : Fin 3) by decide)
    · exact hf (show (1 : Fin 3) < (2 : Fin 3) by decide)
    · exact (hcmp (2 : Fin 3) (0 : Fin 3)).mp (by decide)
    · exact (hcmp (0 : Fin 3) (1 : Fin 3)).mp (by decide)
  · rintro ⟨i, j, k, hij, hjk, hki, hijv⟩
    refine ⟨(fun p : Fin 3 => ![i, j, k] p), ?_, ?_⟩
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp at hab ⊢
      · exact hij
      · exact lt_trans hij hjk
      · exact hjk
    · intro a b
      fin_cases a <;> fin_cases b <;> simp
      all_goals omega

private theorem avoids231_no_triple {n : Nat} {X : Fin n → Nat}
    (havoid : X avoids ![2, 3, 1]) {i j k : Fin n}
    (hij : i < j) (hjk : j < k) :
    ¬ (X k < X i ∧ X i < X j) := by
  intro hx
  exact havoid (contains231_iff_exists_triple.mpr ⟨i, j, k, hij, hjk, hx.1, hx.2⟩)

private theorem avoids231_left_le_right_of_left_lt_mid {n : Nat}
    {X : Fin n → Nat} (havoid : X avoids ![2, 3, 1])
    {i j k : Fin n} (hij : i < j) (hjk : j < k)
    (hijv : X i < X j) :
    X i ≤ X k := by
  by_contra hnot
  have hki : X k < X i := Nat.lt_of_not_ge hnot
  exact avoids231_no_triple havoid hij hjk ⟨hki, hijv⟩

private theorem avoids231_mid_le_left_of_right_lt_left {n : Nat}
    {X : Fin n → Nat} (havoid : X avoids ![2, 3, 1])
    {i j k : Fin n} (hij : i < j) (hjk : j < k)
    (hki : X k < X i) :
    X j ≤ X i := by
  by_contra hnot
  have hijv : X i < X j := Nat.lt_of_not_ge hnot
  exact avoids231_no_triple havoid hij hjk ⟨hki, hijv⟩

private theorem avoids231_before_first_max_le_after {n : Nat}
    {X : Fin n → Nat} (havoid : X avoids ![2, 3, 1])
    {m i k : Fin n}
    (hmax : ∀ a : Fin n, X a ≤ X m)
    (hfirst : ∀ a : Fin n, a < m → X a ≠ X m)
    (him : i < m) (hmk : m < k) :
    X i ≤ X k := by
  by_contra hnot
  have hki : X k < X i := Nat.lt_of_not_ge hnot
  have himax_le : X i ≤ X m := hmax i
  have himax_ne : X i ≠ X m := hfirst i him
  have himax_lt : X i < X m := lt_of_le_of_ne himax_le himax_ne
  exact avoids231_no_triple havoid him hmk ⟨hki, himax_lt⟩

private theorem before_first_max_lt_first_max {n : Nat}
    {X : Fin n → Nat} {m i : Fin n}
    (hmax : ∀ a : Fin n, X a ≤ X m)
    (hfirst : ∀ a : Fin n, a < m → X a ≠ X m)
    (him : i < m) :
    X i < X m := by
  exact lt_of_le_of_ne (hmax i) (hfirst i him)

private theorem prefixSeq_lt_first_max {n : Nat}
    {X : Fin n → Nat} {m : Fin n}
    (hmax : ∀ a : Fin n, X a ≤ X m)
    (hfirst : ∀ a : Fin n, a < m → X a ≠ X m)
    (i : Fin m.val) :
    prefixSeq X m i < X m := by
  unfold prefixSeq
  exact before_first_max_lt_first_max hmax hfirst i.isLt

private theorem suffixSeq_le_first_max {n : Nat}
    {X : Fin n → Nat} {m : Fin n}
    (hmax : ∀ a : Fin n, X a ≤ X m)
    (j : Fin (n - (m.val + 1))) :
    suffixSeq X m j ≤ X m := by
  unfold suffixSeq
  exact hmax _

private theorem take_value_lt_first_max_of_first_max {n : Nat}
    {X : Fin n → Nat} {m i : Fin n}
    (hmax : ∀ a : Fin n, X a ≤ X m)
    (hfirst : ∀ a : Fin n, a < m → X a ≠ X m)
    (hi : i ∈ (List.finRange n).take m.val) :
    X i < X m := by
  exact before_first_max_lt_first_max hmax hfirst (mem_take_finRange_lt hi)

private theorem drop_value_le_first_max_of_first_max {n : Nat}
    {X : Fin n → Nat} {m j : Fin n}
    (hmax : ∀ a : Fin n, X a ≤ X m)
    (_hj : j ∈ (List.finRange n).drop (m.val + 1)) :
    X j ≤ X m := by
  exact hmax j

private theorem take_value_le_drop_value_of_first_max {n : Nat}
    {X : Fin n → Nat} (havoid : X avoids ![2, 3, 1])
    {m i j : Fin n}
    (hmax : ∀ a : Fin n, X a ≤ X m)
    (hfirst : ∀ a : Fin n, a < m → X a ≠ X m)
    (hi : i ∈ (List.finRange n).take m.val)
    (hj : j ∈ (List.finRange n).drop (m.val + 1)) :
    X i ≤ X j := by
  have him : i < m := mem_take_finRange_lt hi
  have hmj : m < j := mem_drop_finRange_gt hj
  exact avoids231_before_first_max_le_after havoid hmax hfirst him hmj

private theorem prefixSeq_le_suffixSeq_of_first_max {n : Nat}
    {X : Fin n → Nat} (havoid : X avoids ![2, 3, 1])
    {m : Fin n}
    (hmax : ∀ a : Fin n, X a ≤ X m)
    (hfirst : ∀ a : Fin n, a < m → X a ≠ X m)
    (i : Fin m.val) (j : Fin (n - (m.val + 1))) :
    prefixSeq X m i ≤ suffixSeq X m j := by
  unfold prefixSeq suffixSeq
  refine avoids231_before_first_max_le_after havoid hmax hfirst ?_ ?_
  · exact i.isLt
  · change m.val < m.val + 1 + j.val
    omega

private theorem suffixSeq_left_le_right_of_middle_eq_first_max {n : Nat}
    {X : Fin n → Nat} (havoid : X avoids ![2, 3, 1])
    {m : Fin n} {i j k : Fin (n - (m.val + 1))}
    (hij : i < j) (hjk : j < k)
    (hj_eq : suffixSeq X m j = X m)
    (hi_lt : suffixSeq X m i < X m) :
    suffixSeq X m i ≤ suffixSeq X m k := by
  have hijv : suffixSeq X m i < suffixSeq X m j := by
    rw [hj_eq]
    exact hi_lt
  exact avoids231_left_le_right_of_left_lt_mid
    (suffixSeq_avoids231 havoid m) hij hjk hijv

private theorem suffixSeq_no_drop_across_repeated_first_max {n : Nat}
    {X : Fin n → Nat} (havoid : X avoids ![2, 3, 1])
    {m : Fin n} {i j k : Fin (n - (m.val + 1))}
    (hij : i < j) (hjk : j < k)
    (hj_eq : suffixSeq X m j = X m)
    (hi_lt : suffixSeq X m i < X m) :
    ¬ suffixSeq X m k < suffixSeq X m i := by
  intro hk_lt
  have hle :=
    suffixSeq_left_le_right_of_middle_eq_first_max
      havoid hij hjk hj_eq hi_lt
  omega

private theorem strictLowerSuffixSeq_left_le_right_of_pivot_between
    {n : Nat} {X : Fin n → Nat} (havoid : X avoids ![2, 3, 1])
    {m : Fin n}
    {a b : Fin (strictLowerSuffixIndices X m).length}
    {p : Fin (n - (m.val + 1))}
    (ha_p : (strictLowerSuffixIndices X m).get a < p)
    (hp_b : p < (strictLowerSuffixIndices X m).get b)
    (hp_eq : suffixSeq X m p = X m) :
    strictLowerSuffixSeq X m a ≤ strictLowerSuffixSeq X m b := by
  have ha_lt : suffixSeq X m ((strictLowerSuffixIndices X m).get a) < X m := by
    exact (mem_strictLowerSuffixIndices_iff X m).mp
      (List.getElem_mem a.isLt)
  have hno :=
    suffixSeq_no_drop_across_repeated_first_max
      havoid ha_p hp_b hp_eq ha_lt
  by_contra hnot
  have hdrop :
      suffixSeq X m ((strictLowerSuffixIndices X m).get b) <
        suffixSeq X m ((strictLowerSuffixIndices X m).get a) := by
    have hlt : strictLowerSuffixSeq X m b < strictLowerSuffixSeq X m a :=
      Nat.lt_of_not_ge hnot
    simpa [strictLowerSuffixSeq] using hlt
  exact hno hdrop

private theorem strictLowerSuffixSeq_left_le_right_of_pivotSuffix_between
    {n : Nat} {X : Fin n → Nat} (havoid : X avoids ![2, 3, 1])
    {m : Fin n}
    (hsuf_le :
      ∀ j : Fin (n - (m.val + 1)), suffixSeq X m j ≤ X m)
    {a b : Fin (strictLowerSuffixIndices X m).length}
    {p : Fin (pivotSuffixIndices X m).length}
    (ha_p :
      (strictLowerSuffixIndices X m).get a <
        (pivotSuffixIndices X m).get p)
    (hp_b :
      (pivotSuffixIndices X m).get p <
        (strictLowerSuffixIndices X m).get b) :
    strictLowerSuffixSeq X m a ≤ strictLowerSuffixSeq X m b := by
  apply strictLowerSuffixSeq_left_le_right_of_pivot_between havoid ha_p hp_b
  exact (mem_pivotSuffixIndices_iff_eq X m hsuf_le).mp
    (List.getElem_mem p.isLt)

private theorem exists_first_max {n : Nat} (hn : 0 < n)
    (X : Fin n → Nat) :
    ∃ m : Fin n,
      (∀ a : Fin n, X a ≤ X m) ∧
      (∀ a : Fin n, a < m → X a ≠ X m) := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨m₀, hmax₀⟩ := Finite.exists_max X
  let p : Fin n → Prop := fun a => ∀ b : Fin n, X b ≤ X a
  have hp₀ : p m₀ := hmax₀
  obtain ⟨m, _hm_le, hmin⟩ :=
    Finite.exists_le_minimal (p := p) (a := m₀) hp₀
  refine ⟨m, hmin.1, ?_⟩
  intro a ham heq
  have hpa : p a := by
    intro b
    rw [heq]
    exact hmin.1 b
  have hma : m ≤ a := hmin.2 hpa (le_of_lt ham)
  exact (not_lt_of_ge hma) ham

private theorem exists_first_max_split {n : Nat} (hn : 0 < n)
    {X : Fin n → Nat} (havoid : X avoids ![2, 3, 1]) :
    ∃ m : Fin n,
      (∀ a : Fin n, X a ≤ X m) ∧
      (∀ a : Fin n, a < m → X a ≠ X m) ∧
      (∀ i k : Fin n, i < m → m < k → X i ≤ X k) := by
  obtain ⟨m, hmax, hfirst⟩ := exists_first_max hn X
  refine ⟨m, hmax, hfirst, ?_⟩
  intro i k him hmk
  exact avoids231_before_first_max_le_after havoid hmax hfirst him hmk

private theorem exists_first_max_prefix_suffix_split {n : Nat} (hn : 0 < n)
    {X : Fin n → Nat} (havoid : X avoids ![2, 3, 1]) :
    ∃ m : Fin n,
      (∀ a : Fin n, X a ≤ X m) ∧
      (∀ a : Fin n, a < m → X a ≠ X m) ∧
      (prefixSeq X m avoids ![2, 3, 1]) ∧
      (suffixSeq X m avoids ![2, 3, 1]) ∧
      (∀ i : Fin m.val, ∀ j : Fin (n - (m.val + 1)),
        prefixSeq X m i ≤ suffixSeq X m j) := by
  obtain ⟨m, hmax, hfirst⟩ := exists_first_max hn X
  refine ⟨m, hmax, hfirst, prefixSeq_avoids231 havoid m,
    suffixSeq_avoids231 havoid m, ?_⟩
  intro i j
  exact prefixSeq_le_suffixSeq_of_first_max havoid hmax hfirst i j

private theorem exists_first_max_prefix_suffix_strict_split {n : Nat}
    (hn : 0 < n) {X : Fin n → Nat} (havoid : X avoids ![2, 3, 1]) :
    ∃ m : Fin n,
      (∀ a : Fin n, X a ≤ X m) ∧
      (∀ a : Fin n, a < m → X a ≠ X m) ∧
      (prefixSeq X m avoids ![2, 3, 1]) ∧
      (suffixSeq X m avoids ![2, 3, 1]) ∧
      (∀ i : Fin m.val, prefixSeq X m i < X m) ∧
      (∀ j : Fin (n - (m.val + 1)), suffixSeq X m j ≤ X m) ∧
      (∀ i : Fin m.val, ∀ j : Fin (n - (m.val + 1)),
        prefixSeq X m i ≤ suffixSeq X m j) := by
  obtain ⟨m, hmax, hfirst⟩ := exists_first_max hn X
  refine ⟨m, hmax, hfirst, prefixSeq_avoids231 havoid m,
    suffixSeq_avoids231 havoid m, ?_, ?_, ?_⟩
  · intro i
    exact prefixSeq_lt_first_max hmax hfirst i
  · intro j
    exact suffixSeq_le_first_max hmax j
  · intro i j
    exact prefixSeq_le_suffixSeq_of_first_max havoid hmax hfirst i j

private theorem exists_first_max_path_decomp {n : Nat}
    (hn : 0 < n) (X : Fin n → Nat) (havoid : X avoids ![2, 3, 1])
    (init : BinaryTree) :
    ∃ m : Fin n,
      (∀ a : Fin n, X a ≤ X m) ∧
      (∀ a : Fin n, a < m → X a ≠ X m) ∧
      (prefixSeq X m avoids ![2, 3, 1]) ∧
      (suffixSeq X m avoids ![2, 3, 1]) ∧
      (∀ i : Fin m.val, prefixSeq X m i < X m) ∧
      (∀ j : Fin (n - (m.val + 1)), suffixSeq X m j ≤ X m) ∧
      (∀ i : Fin m.val, ∀ j : Fin (n - (m.val + 1)),
        prefixSeq X m i ≤ suffixSeq X m j) ∧
      splayPathSum X init (List.finRange n) =
        splayPathSum (prefixSeq X m) init (List.finRange m.val) +
          ((splayTreeAfter (prefixSeq X m) init
              (List.finRange m.val)).search_path_len (X m) +
            splayPathSum (suffixSeq X m)
              (splay
                (splayTreeAfter (prefixSeq X m) init
                  (List.finRange m.val))
                (X m))
              (List.finRange (n - (m.val + 1)))) := by
  obtain ⟨m, hmax, hfirst, hpre, hsuf, hpre_lt, hsuf_le,
    hpre_suf⟩ :=
    exists_first_max_prefix_suffix_strict_split hn havoid
  refine ⟨m, hmax, hfirst, hpre, hsuf, hpre_lt, hsuf_le, hpre_suf, ?_⟩
  exact splayPathSum_finRange_prefix_pivot_suffix X init m

private theorem exists_first_max_path_budget_decomp {n : Nat}
    (hn : 0 < n) (X : Fin n → Nat) (havoid : X avoids ![2, 3, 1])
    (init : BinaryTree) (hbst : IsBST init) :
    ∃ m : Fin n,
      (∀ a : Fin n, X a ≤ X m) ∧
      (∀ a : Fin n, a < m → X a ≠ X m) ∧
      (prefixSeq X m avoids ![2, 3, 1]) ∧
      (suffixSeq X m avoids ![2, 3, 1]) ∧
      (∀ i : Fin m.val, prefixSeq X m i < X m) ∧
      (∀ j : Fin (n - (m.val + 1)), suffixSeq X m j ≤ X m) ∧
      (∀ i : Fin m.val, ∀ j : Fin (n - (m.val + 1)),
        prefixSeq X m i ≤ suffixSeq X m j) ∧
      splayPathSum X init (List.finRange n) =
        splayPathSum (prefixSeq X m) init (List.finRange m.val) +
          ((splayTreeAfter (prefixSeq X m) init
              (List.finRange m.val)).search_path_len (X m) +
            splayPathSum (suffixSeq X m)
              (splay
                (splayTreeAfter (prefixSeq X m) init
                  (List.finRange m.val))
                (X m))
              (List.finRange (n - (m.val + 1)))) ∧
      activeBudget X init (List.finRange n) ≤
        activeBudget (prefixSeq X m) init (List.finRange m.val) +
          activeBudget (suffixSeq X m) init
            (List.finRange (n - (m.val + 1))) +
          (1 + init.num_nodes : ℝ) := by
  obtain ⟨m, hmax, hfirst, hpre, hsuf, hpre_lt, hsuf_le,
    hpre_suf, hpath⟩ :=
    exists_first_max_path_decomp hn X havoid init
  refine ⟨m, hmax, hfirst, hpre, hsuf, hpre_lt, hsuf_le,
    hpre_suf, hpath, ?_⟩
  exact activeBudget_finRange_split_le X init m hbst

private theorem exists_first_max_take_drop_split {n : Nat} (hn : 0 < n)
    {X : Fin n → Nat} (havoid : X avoids ![2, 3, 1]) :
    ∃ m : Fin n,
      (∀ a : Fin n, X a ≤ X m) ∧
      (∀ a : Fin n, a < m → X a ≠ X m) ∧
      (prefixSeq X m avoids ![2, 3, 1]) ∧
      (suffixSeq X m avoids ![2, 3, 1]) ∧
      (∀ i j : Fin n,
        i ∈ (List.finRange n).take m.val →
        j ∈ (List.finRange n).drop (m.val + 1) →
        X i ≤ X j) := by
  obtain ⟨m, hmax, hfirst⟩ := exists_first_max hn X
  refine ⟨m, hmax, hfirst, prefixSeq_avoids231 havoid m,
    suffixSeq_avoids231 havoid m, ?_⟩
  intro i j hi hj
  exact take_value_le_drop_value_of_first_max havoid hmax hfirst hi hj

private theorem exists_first_max_path_recurrence_of_generic_model_bridges
    {n : Nat} (hn : 0 < n) (X : Fin n → Nat) (init : BinaryTree)
    (havoid : X avoids ![2, 3, 1])
    (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (hactualModel :
      ∀ {N : Nat} (Y : Fin N → Nat) (q : Nat)
        (t : BinaryTree) (xs : List (Fin N)),
        IsBST t → rootKey t = some q →
        (∀ i : Fin N, i ∈ xs → Y i ∈ t.toKeyList) →
        (∀ i : Fin N, i ∈ xs → Y i ≤ q) →
        splayPathSum Y t xs ≤
          suffixResetUpperPathSum Y q t xs + activeBudget Y t xs)
    (hpairModel :
      ∀ {N : Nat} (Y : Fin N → Nat) (q : Nat)
        (t : BinaryTree) (xs : List (Fin N)),
        IsBST t → rootKey t = some q →
        (∀ i : Fin N, i ∈ xs → Y i ∈ t.toKeyList) →
        (∀ i : Fin N, i ∈ xs → Y i < q) →
        pivotResetPairPathSum Y q t xs ≤
          splayPathSum Y t xs + 5 * activeBudget Y t xs) :
    ∃ m : Fin n,
      (∀ a : Fin n, X a ≤ X m) ∧
      (∀ a : Fin n, a < m → X a ≠ X m) ∧
      (prefixSeq X m avoids ![2, 3, 1]) ∧
      (suffixSeq X m avoids ![2, 3, 1]) ∧
      (∀ i : Fin m.val, prefixSeq X m i < X m) ∧
      (∀ j : Fin (n - (m.val + 1)), suffixSeq X m j ≤ X m) ∧
      (∀ i : Fin m.val, ∀ j : Fin (n - (m.val + 1)),
        prefixSeq X m i ≤ suffixSeq X m j) ∧
      splayPathSum X init (List.finRange n) ≤
        splayPathSum (prefixSeq X m) init (List.finRange m.val) +
          ((splayTreeAfter (prefixSeq X m) init
              (List.finRange m.val)).search_path_len (X m) +
            (splayPathSum (strictLowerSuffixSeq X m)
              (splay
                (splayTreeAfter (prefixSeq X m) init
                  (List.finRange m.val))
                (X m))
              (List.finRange (strictLowerSuffixIndices X m).length) +
            7 * ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ))) := by
  obtain ⟨m, hmax, hfirst, hpre, hsuf, hpre_lt, hsuf_le,
      hpre_suf, hpath⟩ :=
    exists_first_max_path_decomp hn X havoid init
  refine ⟨m, hmax, hfirst, hpre, hsuf, hpre_lt, hsuf_le,
    hpre_suf, ?_⟩
  let tp := splayTreeAfter (prefixSeq X m) init (List.finRange m.val)
  let ts := splay tp (X m)
  have hsufBridge :
      splayPathSum (suffixSeq X m) ts
          (List.finRange (n - (m.val + 1))) ≤
        splayPathSum (strictLowerSuffixSeq X m) ts
          (List.finRange (strictLowerSuffixIndices X m).length) +
        7 * ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ) := by
    unfold ts tp
    exact
      suffix_after_prefix_pivot_le_lowerPath_linear_of_generic_model_bridges
        (m := m) hbst hmem hsuf_le hactualModel hpairModel
  rw [hpath]
  change
    splayPathSum (prefixSeq X m) init (List.finRange m.val) +
        (tp.search_path_len (X m) +
          splayPathSum (suffixSeq X m) ts
            (List.finRange (n - (m.val + 1)))) ≤
      splayPathSum (prefixSeq X m) init (List.finRange m.val) +
        (tp.search_path_len (X m) +
          (splayPathSum (strictLowerSuffixSeq X m) ts
            (List.finRange (strictLowerSuffixIndices X m).length) +
          7 * ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ)))
  nlinarith

private theorem exists_first_max_path_recurrence_of_generic_model_bridges_const
    {n : Nat} {C : ℝ} (hC : 0 ≤ C)
    (hn : 0 < n) (X : Fin n → Nat) (init : BinaryTree)
    (havoid : X avoids ![2, 3, 1])
    (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (hactualModel :
      ∀ {N : Nat} (Y : Fin N → Nat) (q : Nat)
        (t : BinaryTree) (xs : List (Fin N)),
        IsBST t → rootKey t = some q →
        (∀ i : Fin N, i ∈ xs → Y i ∈ t.toKeyList) →
        (∀ i : Fin N, i ∈ xs → Y i ≤ q) →
        splayPathSum Y t xs ≤
          suffixResetUpperPathSum Y q t xs + activeBudget Y t xs)
    (hpairModel :
      ∀ {N : Nat} (Y : Fin N → Nat) (q : Nat)
        (t : BinaryTree) (xs : List (Fin N)),
        IsBST t → rootKey t = some q →
        (∀ i : Fin N, i ∈ xs → Y i ∈ t.toKeyList) →
        (∀ i : Fin N, i ∈ xs → Y i < q) →
        pivotResetPairPathSum Y q t xs ≤
          splayPathSum Y t xs + C * activeBudget Y t xs) :
    ∃ m : Fin n,
      (∀ a : Fin n, X a ≤ X m) ∧
      (∀ a : Fin n, a < m → X a ≠ X m) ∧
      (prefixSeq X m avoids ![2, 3, 1]) ∧
      (suffixSeq X m avoids ![2, 3, 1]) ∧
      (∀ i : Fin m.val, prefixSeq X m i < X m) ∧
      (∀ j : Fin (n - (m.val + 1)), suffixSeq X m j ≤ X m) ∧
      (∀ i : Fin m.val, ∀ j : Fin (n - (m.val + 1)),
        prefixSeq X m i ≤ suffixSeq X m j) ∧
      splayPathSum X init (List.finRange n) ≤
        splayPathSum (prefixSeq X m) init (List.finRange m.val) +
          ((splayTreeAfter (prefixSeq X m) init
              (List.finRange m.val)).search_path_len (X m) +
            (splayPathSum (strictLowerSuffixSeq X m)
              (splay
                (splayTreeAfter (prefixSeq X m) init
                  (List.finRange m.val))
                (X m))
              (List.finRange (strictLowerSuffixIndices X m).length) +
            (C + 2) * ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ))) := by
  obtain ⟨m, hmax, hfirst, hpre, hsuf, hpre_lt, hsuf_le,
      hpre_suf, hpath⟩ :=
    exists_first_max_path_decomp hn X havoid init
  refine ⟨m, hmax, hfirst, hpre, hsuf, hpre_lt, hsuf_le,
    hpre_suf, ?_⟩
  let tp := splayTreeAfter (prefixSeq X m) init (List.finRange m.val)
  let ts := splay tp (X m)
  have hsufBridge :
      splayPathSum (suffixSeq X m) ts
          (List.finRange (n - (m.val + 1))) ≤
        splayPathSum (strictLowerSuffixSeq X m) ts
          (List.finRange (strictLowerSuffixIndices X m).length) +
        (C + 2) * ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ) := by
    unfold ts tp
    exact
      suffix_after_prefix_pivot_le_lowerPath_linear_of_generic_model_bridges_const
        (m := m) hC hbst hmem hsuf_le hactualModel hpairModel
  rw [hpath]
  change
    splayPathSum (prefixSeq X m) init (List.finRange m.val) +
        (tp.search_path_len (X m) +
          splayPathSum (suffixSeq X m) ts
            (List.finRange (n - (m.val + 1)))) ≤
      splayPathSum (prefixSeq X m) init (List.finRange m.val) +
        (tp.search_path_len (X m) +
          (splayPathSum (strictLowerSuffixSeq X m) ts
            (List.finRange (strictLowerSuffixIndices X m).length) +
          (C + 2) * ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ)))
  nlinarith

private theorem activeBudget_induction_step_of_firstMax_budget_certificate
    (K : ℝ)
    {n : Nat} (hn : 0 < n) (X : Fin n → Nat) (init : BinaryTree)
    (havoid : X avoids ![2, 3, 1])
    (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (ih :
      ∀ k, k < n → ∀ Y : Fin k → Nat,
        (Y avoids ![2, 3, 1]) →
        ∀ (t : BinaryTree), IsBST t →
        (∀ i : Fin k, Y i ∈ t.toKeyList) →
        splayPathSum Y t (List.finRange k) ≤
          K * activeBudget Y t (List.finRange k))
    (hactualModel :
      ∀ {N : Nat} (Y : Fin N → Nat) (q : Nat)
        (t : BinaryTree) (xs : List (Fin N)),
        IsBST t → rootKey t = some q →
        (∀ i : Fin N, i ∈ xs → Y i ∈ t.toKeyList) →
        (∀ i : Fin N, i ∈ xs → Y i ≤ q) →
        splayPathSum Y t xs ≤
          suffixResetUpperPathSum Y q t xs + activeBudget Y t xs)
    (hpairModel :
      ∀ {N : Nat} (Y : Fin N → Nat) (q : Nat)
        (t : BinaryTree) (xs : List (Fin N)),
        IsBST t → rootKey t = some q →
        (∀ i : Fin N, i ∈ xs → Y i ∈ t.toKeyList) →
        (∀ i : Fin N, i ∈ xs → Y i < q) →
        pivotResetPairPathSum Y q t xs ≤
          splayPathSum Y t xs + 5 * activeBudget Y t xs)
    (hbudgetCert :
      ∀ (m : Fin n),
        (∀ a : Fin n, X a ≤ X m) →
        (∀ a : Fin n, a < m → X a ≠ X m) →
        (prefixSeq X m avoids ![2, 3, 1]) →
        (suffixSeq X m avoids ![2, 3, 1]) →
        (∀ i : Fin m.val, prefixSeq X m i < X m) →
        (∀ j : Fin (n - (m.val + 1)), suffixSeq X m j ≤ X m) →
        (∀ i : Fin m.val, ∀ j : Fin (n - (m.val + 1)),
          prefixSeq X m i ≤ suffixSeq X m j) →
        let tp :=
          splayTreeAfter (prefixSeq X m) init (List.finRange m.val)
        let ts := splay tp (X m)
        K * activeBudget (prefixSeq X m) init (List.finRange m.val) +
            ((tp.search_path_len (X m) : ℝ) +
              (K * activeBudget (strictLowerSuffixSeq X m) ts
                  (List.finRange (strictLowerSuffixIndices X m).length) +
                7 * ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ))) ≤
          K * activeBudget X init (List.finRange n)) :
    splayPathSum X init (List.finRange n) ≤
      K * activeBudget X init (List.finRange n) := by
  obtain ⟨m, hmax, hfirst, hpreAvoid, _hsufAvoid, hpre_lt,
      hsuf_le, hpre_suf, hrec⟩ :=
    exists_first_max_path_recurrence_of_generic_model_bridges
      hn X init havoid hbst hmem hactualModel hpairModel
  let tp := splayTreeAfter (prefixSeq X m) init (List.finRange m.val)
  let ts := splay tp (X m)
  have hpreBound :
      splayPathSum (prefixSeq X m) init (List.finRange m.val) ≤
        K * activeBudget (prefixSeq X m) init (List.finRange m.val) := by
    exact ih m.val (prefix_length_lt_of_fin m)
      (prefixSeq X m) hpreAvoid init hbst (prefixSeq_mem hmem m)
  have hts_bst : IsBST ts := by
    unfold ts tp
    exact suffix_state_after_prefix_pivot_isBST X init m hbst
  have hstrictAvoid :
      strictLowerSuffixSeq X m avoids ![2, 3, 1] :=
    strictLowerSuffixSeq_avoids231 havoid m
  have hstrictMem :
      ∀ i : Fin (strictLowerSuffixIndices X m).length,
        strictLowerSuffixSeq X m i ∈ ts.toKeyList := by
    intro i
    unfold ts tp
    exact strictLowerSuffixSeq_mem_after_prefix_pivot hmem i
  have hlowerBound :
      splayPathSum (strictLowerSuffixSeq X m) ts
          (List.finRange (strictLowerSuffixIndices X m).length) ≤
        K * activeBudget (strictLowerSuffixSeq X m) ts
          (List.finRange (strictLowerSuffixIndices X m).length) := by
    exact ih (strictLowerSuffixIndices X m).length
      (strictLowerSuffixIndices_length_lt X m)
      (strictLowerSuffixSeq X m) hstrictAvoid ts hts_bst hstrictMem
  have hcert :=
    hbudgetCert m hmax hfirst hpreAvoid
      (suffixSeq_avoids231 havoid m) hpre_lt hsuf_le hpre_suf
  change
    splayPathSum X init (List.finRange n) ≤
      K * activeBudget X init (List.finRange n)
  change
    splayPathSum X init (List.finRange n) ≤
      splayPathSum (prefixSeq X m) init (List.finRange m.val) +
        ((tp.search_path_len (X m) : ℝ) +
          (splayPathSum (strictLowerSuffixSeq X m) ts
            (List.finRange (strictLowerSuffixIndices X m).length) +
          7 * ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ))) at hrec
  change
    K * activeBudget (prefixSeq X m) init (List.finRange m.val) +
        ((tp.search_path_len (X m) : ℝ) +
          (K * activeBudget (strictLowerSuffixSeq X m) ts
              (List.finRange (strictLowerSuffixIndices X m).length) +
            7 * ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ))) ≤
      K * activeBudget X init (List.finRange n) at hcert
  nlinarith

private theorem activeBudget_induction_step_of_firstMax_budget_certificate_const
    (K C : ℝ) (hC : 0 ≤ C)
    {n : Nat} (hn : 0 < n) (X : Fin n → Nat) (init : BinaryTree)
    (havoid : X avoids ![2, 3, 1])
    (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (ih :
      ∀ k, k < n → ∀ Y : Fin k → Nat,
        (Y avoids ![2, 3, 1]) →
        ∀ (t : BinaryTree), IsBST t →
        (∀ i : Fin k, Y i ∈ t.toKeyList) →
        splayPathSum Y t (List.finRange k) ≤
          K * activeBudget Y t (List.finRange k))
    (hactualModel :
      ∀ {N : Nat} (Y : Fin N → Nat) (q : Nat)
        (t : BinaryTree) (xs : List (Fin N)),
        IsBST t → rootKey t = some q →
        (∀ i : Fin N, i ∈ xs → Y i ∈ t.toKeyList) →
        (∀ i : Fin N, i ∈ xs → Y i ≤ q) →
        splayPathSum Y t xs ≤
          suffixResetUpperPathSum Y q t xs + activeBudget Y t xs)
    (hpairModel :
      ∀ {N : Nat} (Y : Fin N → Nat) (q : Nat)
        (t : BinaryTree) (xs : List (Fin N)),
        IsBST t → rootKey t = some q →
        (∀ i : Fin N, i ∈ xs → Y i ∈ t.toKeyList) →
        (∀ i : Fin N, i ∈ xs → Y i < q) →
        pivotResetPairPathSum Y q t xs ≤
          splayPathSum Y t xs + C * activeBudget Y t xs)
    (hbudgetCert :
      ∀ (m : Fin n),
        (∀ a : Fin n, X a ≤ X m) →
        (∀ a : Fin n, a < m → X a ≠ X m) →
        (prefixSeq X m avoids ![2, 3, 1]) →
        (suffixSeq X m avoids ![2, 3, 1]) →
        (∀ i : Fin m.val, prefixSeq X m i < X m) →
        (∀ j : Fin (n - (m.val + 1)), suffixSeq X m j ≤ X m) →
        (∀ i : Fin m.val, ∀ j : Fin (n - (m.val + 1)),
          prefixSeq X m i ≤ suffixSeq X m j) →
        let tp :=
          splayTreeAfter (prefixSeq X m) init (List.finRange m.val)
        let ts := splay tp (X m)
        K * activeBudget (prefixSeq X m) init (List.finRange m.val) +
            ((tp.search_path_len (X m) : ℝ) +
              (K * activeBudget (strictLowerSuffixSeq X m) ts
                  (List.finRange (strictLowerSuffixIndices X m).length) +
                (C + 2) *
                  ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ))) ≤
          K * activeBudget X init (List.finRange n)) :
    splayPathSum X init (List.finRange n) ≤
      K * activeBudget X init (List.finRange n) := by
  obtain ⟨m, hmax, hfirst, hpreAvoid, _hsufAvoid, hpre_lt,
      hsuf_le, hpre_suf, hrec⟩ :=
    exists_first_max_path_recurrence_of_generic_model_bridges_const
      (C := C) hC hn X init havoid hbst hmem hactualModel hpairModel
  let tp := splayTreeAfter (prefixSeq X m) init (List.finRange m.val)
  let ts := splay tp (X m)
  have hpreBound :
      splayPathSum (prefixSeq X m) init (List.finRange m.val) ≤
        K * activeBudget (prefixSeq X m) init (List.finRange m.val) := by
    exact ih m.val (prefix_length_lt_of_fin m)
      (prefixSeq X m) hpreAvoid init hbst (prefixSeq_mem hmem m)
  have hts_bst : IsBST ts := by
    unfold ts tp
    exact suffix_state_after_prefix_pivot_isBST X init m hbst
  have hstrictAvoid :
      strictLowerSuffixSeq X m avoids ![2, 3, 1] :=
    strictLowerSuffixSeq_avoids231 havoid m
  have hstrictMem :
      ∀ i : Fin (strictLowerSuffixIndices X m).length,
        strictLowerSuffixSeq X m i ∈ ts.toKeyList := by
    intro i
    unfold ts tp
    exact strictLowerSuffixSeq_mem_after_prefix_pivot hmem i
  have hlowerBound :
      splayPathSum (strictLowerSuffixSeq X m) ts
          (List.finRange (strictLowerSuffixIndices X m).length) ≤
        K * activeBudget (strictLowerSuffixSeq X m) ts
          (List.finRange (strictLowerSuffixIndices X m).length) := by
    exact ih (strictLowerSuffixIndices X m).length
      (strictLowerSuffixIndices_length_lt X m)
      (strictLowerSuffixSeq X m) hstrictAvoid ts hts_bst hstrictMem
  have hcert :=
    hbudgetCert m hmax hfirst hpreAvoid
      (suffixSeq_avoids231 havoid m) hpre_lt hsuf_le hpre_suf
  change
    splayPathSum X init (List.finRange n) ≤
      K * activeBudget X init (List.finRange n)
  change
    splayPathSum X init (List.finRange n) ≤
      splayPathSum (prefixSeq X m) init (List.finRange m.val) +
        ((tp.search_path_len (X m) : ℝ) +
          (splayPathSum (strictLowerSuffixSeq X m) ts
            (List.finRange (strictLowerSuffixIndices X m).length) +
          (C + 2) *
            ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ))) at hrec
  change
    K * activeBudget (prefixSeq X m) init (List.finRange m.val) +
        ((tp.search_path_len (X m) : ℝ) +
          (K * activeBudget (strictLowerSuffixSeq X m) ts
              (List.finRange (strictLowerSuffixIndices X m).length) +
            (C + 2) *
              ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ))) ≤
      K * activeBudget X init (List.finRange n) at hcert
  nlinarith

private theorem traversal_conjecture_of_firstMax_budget_certificates
    (K : ℝ) (hK_nonneg : 0 ≤ K)
    (hsmall :
      ∀ n, n ≤ 8 → ∀ X : Fin n → Nat,
        (X avoids ![2, 3, 1]) →
        ∀ (init : BinaryTree), IsBST init →
        (∀ i : Fin n, X i ∈ init.toKeyList) →
        splayPathSum X init (List.finRange n) ≤
          K * activeBudget X init (List.finRange n))
    (hactualModel :
      ∀ {N : Nat} (Y : Fin N → Nat) (q : Nat)
        (t : BinaryTree) (xs : List (Fin N)),
        IsBST t → rootKey t = some q →
        (∀ i : Fin N, i ∈ xs → Y i ∈ t.toKeyList) →
        (∀ i : Fin N, i ∈ xs → Y i ≤ q) →
        splayPathSum Y t xs ≤
          suffixResetUpperPathSum Y q t xs + activeBudget Y t xs)
    (hpairModel :
      ∀ {N : Nat} (Y : Fin N → Nat) (q : Nat)
        (t : BinaryTree) (xs : List (Fin N)),
        IsBST t → rootKey t = some q →
        (∀ i : Fin N, i ∈ xs → Y i ∈ t.toKeyList) →
        (∀ i : Fin N, i ∈ xs → Y i < q) →
        pivotResetPairPathSum Y q t xs ≤
          splayPathSum Y t xs + 5 * activeBudget Y t xs)
    (hbudgetCert :
      ∀ n, 8 < n → ∀ X : Fin n → Nat,
        (X avoids ![2, 3, 1]) →
        ∀ (init : BinaryTree), IsBST init →
        (∀ i : Fin n, X i ∈ init.toKeyList) →
        ∀ (m : Fin n),
          (∀ a : Fin n, X a ≤ X m) →
          (∀ a : Fin n, a < m → X a ≠ X m) →
          (prefixSeq X m avoids ![2, 3, 1]) →
          (suffixSeq X m avoids ![2, 3, 1]) →
          (∀ i : Fin m.val, prefixSeq X m i < X m) →
          (∀ j : Fin (n - (m.val + 1)), suffixSeq X m j ≤ X m) →
          (∀ i : Fin m.val, ∀ j : Fin (n - (m.val + 1)),
            prefixSeq X m i ≤ suffixSeq X m j) →
          let tp :=
            splayTreeAfter (prefixSeq X m) init (List.finRange m.val)
          let ts := splay tp (X m)
          K * activeBudget (prefixSeq X m) init (List.finRange m.val) +
              ((tp.search_path_len (X m) : ℝ) +
                (K * activeBudget (strictLowerSuffixSeq X m) ts
                    (List.finRange (strictLowerSuffixIndices X m).length) +
                  7 * ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ))) ≤
            K * activeBudget X init (List.finRange n)) :
    ∃ c, ∀ n, ∀ X : Fin n → Nat,
      (X avoids ![2, 3, 1]) →
      ∀ (init : BinaryTree), init.num_nodes = n → IsBST init →
      (∀ i : Fin n, (X i) ∈ init.toKeyList) →
      splay.sequence_cost init X ≤ c * n := by
  apply traversal_conjecture_of_activeBudget_induction K hK_nonneg hsmall
  intro n hn8 ih X havoid init hbst hmem
  have hn_pos : 0 < n := by omega
  exact
    activeBudget_induction_step_of_firstMax_budget_certificate
      K hn_pos X init havoid hbst hmem ih hactualModel hpairModel
      (hbudgetCert n hn8 X havoid init hbst hmem)

private theorem traversal_conjecture_of_firstMax_budget_certificates_const
    (K C : ℝ) (hK_nonneg : 0 ≤ K) (hC : 0 ≤ C)
    (hsmall :
      ∀ n, n ≤ 8 → ∀ X : Fin n → Nat,
        (X avoids ![2, 3, 1]) →
        ∀ (init : BinaryTree), IsBST init →
        (∀ i : Fin n, X i ∈ init.toKeyList) →
        splayPathSum X init (List.finRange n) ≤
          K * activeBudget X init (List.finRange n))
    (hactualModel :
      ∀ {N : Nat} (Y : Fin N → Nat) (q : Nat)
        (t : BinaryTree) (xs : List (Fin N)),
        IsBST t → rootKey t = some q →
        (∀ i : Fin N, i ∈ xs → Y i ∈ t.toKeyList) →
        (∀ i : Fin N, i ∈ xs → Y i ≤ q) →
        splayPathSum Y t xs ≤
          suffixResetUpperPathSum Y q t xs + activeBudget Y t xs)
    (hpairModel :
      ∀ {N : Nat} (Y : Fin N → Nat) (q : Nat)
        (t : BinaryTree) (xs : List (Fin N)),
        IsBST t → rootKey t = some q →
        (∀ i : Fin N, i ∈ xs → Y i ∈ t.toKeyList) →
        (∀ i : Fin N, i ∈ xs → Y i < q) →
        pivotResetPairPathSum Y q t xs ≤
          splayPathSum Y t xs + C * activeBudget Y t xs)
    (hbudgetCert :
      ∀ n, 8 < n → ∀ X : Fin n → Nat,
        (X avoids ![2, 3, 1]) →
        ∀ (init : BinaryTree), IsBST init →
        (∀ i : Fin n, X i ∈ init.toKeyList) →
        ∀ (m : Fin n),
          (∀ a : Fin n, X a ≤ X m) →
          (∀ a : Fin n, a < m → X a ≠ X m) →
          (prefixSeq X m avoids ![2, 3, 1]) →
          (suffixSeq X m avoids ![2, 3, 1]) →
          (∀ i : Fin m.val, prefixSeq X m i < X m) →
          (∀ j : Fin (n - (m.val + 1)), suffixSeq X m j ≤ X m) →
          (∀ i : Fin m.val, ∀ j : Fin (n - (m.val + 1)),
            prefixSeq X m i ≤ suffixSeq X m j) →
          let tp :=
            splayTreeAfter (prefixSeq X m) init (List.finRange m.val)
          let ts := splay tp (X m)
          K * activeBudget (prefixSeq X m) init (List.finRange m.val) +
              ((tp.search_path_len (X m) : ℝ) +
                (K * activeBudget (strictLowerSuffixSeq X m) ts
                    (List.finRange (strictLowerSuffixIndices X m).length) +
                  (C + 2) *
                    ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ))) ≤
            K * activeBudget X init (List.finRange n)) :
    ∃ c, ∀ n, ∀ X : Fin n → Nat,
      (X avoids ![2, 3, 1]) →
      ∀ (init : BinaryTree), init.num_nodes = n → IsBST init →
      (∀ i : Fin n, (X i) ∈ init.toKeyList) →
      splay.sequence_cost init X ≤ c * n := by
  apply traversal_conjecture_of_activeBudget_induction K hK_nonneg hsmall
  intro n hn8 ih X havoid init hbst hmem
  have hn_pos : 0 < n := by omega
  exact
    activeBudget_induction_step_of_firstMax_budget_certificate_const
      K C hC hn_pos X init havoid hbst hmem ih hactualModel hpairModel
      (hbudgetCert n hn8 X havoid init hbst hmem)

private theorem traversal_conjecture_of_firstMax_budget_certificates_const_le_two
    (K C : ℝ) (hK_nonneg : 0 ≤ K) (hK_two : 2 ≤ K) (hC : 0 ≤ C)
    (hactualModel :
      ∀ {N : Nat} (Y : Fin N → Nat) (q : Nat)
        (t : BinaryTree) (xs : List (Fin N)),
        IsBST t → rootKey t = some q →
        (∀ i : Fin N, i ∈ xs → Y i ∈ t.toKeyList) →
        (∀ i : Fin N, i ∈ xs → Y i ≤ q) →
        splayPathSum Y t xs ≤
          suffixResetUpperPathSum Y q t xs + activeBudget Y t xs)
    (hpairModel :
      ∀ {N : Nat} (Y : Fin N → Nat) (q : Nat)
        (t : BinaryTree) (xs : List (Fin N)),
        IsBST t → rootKey t = some q →
        (∀ i : Fin N, i ∈ xs → Y i ∈ t.toKeyList) →
        (∀ i : Fin N, i ∈ xs → Y i < q) →
        pivotResetPairPathSum Y q t xs ≤
          splayPathSum Y t xs + C * activeBudget Y t xs)
    (hbudgetCert :
      ∀ n, 2 < n → ∀ X : Fin n → Nat,
        (X avoids ![2, 3, 1]) →
        ∀ (init : BinaryTree), IsBST init →
        (∀ i : Fin n, X i ∈ init.toKeyList) →
        ∀ (m : Fin n),
          (∀ a : Fin n, X a ≤ X m) →
          (∀ a : Fin n, a < m → X a ≠ X m) →
          (prefixSeq X m avoids ![2, 3, 1]) →
          (suffixSeq X m avoids ![2, 3, 1]) →
          (∀ i : Fin m.val, prefixSeq X m i < X m) →
          (∀ j : Fin (n - (m.val + 1)), suffixSeq X m j ≤ X m) →
          (∀ i : Fin m.val, ∀ j : Fin (n - (m.val + 1)),
            prefixSeq X m i ≤ suffixSeq X m j) →
          let tp :=
            splayTreeAfter (prefixSeq X m) init (List.finRange m.val)
          let ts := splay tp (X m)
          K * activeBudget (prefixSeq X m) init (List.finRange m.val) +
              ((tp.search_path_len (X m) : ℝ) +
                (K * activeBudget (strictLowerSuffixSeq X m) ts
                    (List.finRange (strictLowerSuffixIndices X m).length) +
                  (C + 2) *
                    ((n - (m.val + 1) : Nat) + init.num_nodes : ℝ))) ≤
            K * activeBudget X init (List.finRange n)) :
    ∃ c, ∀ n, ∀ X : Fin n → Nat,
      (X avoids ![2, 3, 1]) →
      ∀ (init : BinaryTree), init.num_nodes = n → IsBST init →
      (∀ i : Fin n, (X i) ∈ init.toKeyList) →
      splay.sequence_cost init X ≤ c * n := by
  apply traversal_conjecture_of_activeBudget_induction_le_two K hK_nonneg
  · exact general_activeBudget_path_bound_le_two K hK_two
  · intro n hn2 ih X havoid init hbst hmem
    have hn_pos : 0 < n := by omega
    exact
      activeBudget_induction_step_of_firstMax_budget_certificate_const
        K C hC hn_pos X init havoid hbst hmem ih hactualModel hpairModel
        (hbudgetCert n hn2 X havoid init hbst hmem)

private def badResetTree : BinaryTree :=
  .node
    (.node
      (.node .empty 0 .empty)
      1
      (.node (.node .empty 2 .empty) 3 .empty))
    4
    .empty

private def badResetY : Fin 5 → Nat := ![0, 2, 4, 0, 2]

private theorem amortized_reset_compare_counterexample :
    ¬
      (splayPathSum badResetY (splay badResetTree (badResetY (0 : Fin 5)))
            [(1 : Fin 5), (2 : Fin 5), (3 : Fin 5), (4 : Fin 5)] +
          activeBudget badResetY
            (splay (splay badResetTree (badResetY (0 : Fin 5))) 4)
            [(1 : Fin 5), (2 : Fin 5), (3 : Fin 5), (4 : Fin 5)] ≤
        ((splay badResetTree (badResetY (0 : Fin 5))).search_path_len 4 : ℝ) +
          splayPathSum badResetY
            (splay (splay badResetTree (badResetY (0 : Fin 5))) 4)
            [(1 : Fin 5), (2 : Fin 5), (3 : Fin 5), (4 : Fin 5)] +
          activeBudget badResetY badResetTree
            [(0 : Fin 5), (1 : Fin 5), (2 : Fin 5), (3 : Fin 5),
              (4 : Fin 5)]) := by
  have hY0 : badResetY (0 : Fin 5) = 0 := by native_decide
  have hY1 : badResetY (1 : Fin 5) = 2 := by native_decide
  have hY2 : badResetY (2 : Fin 5) = 4 := by native_decide
  have hY3 : badResetY (3 : Fin 5) = 0 := by native_decide
  have hY4 : badResetY (4 : Fin 5) = 2 := by native_decide
  norm_num [badResetTree, splayPathSum, activeBudget,
    activeHullSize, activeHullKeys, searchPathKeys, BinaryTree.toKeyList,
    BinaryTree.search_path_len, splay, rotate, rotateRight, rotateLeft,
    hY0, hY1, hY2, hY3, hY4]

private def badAvoidResetTree : BinaryTree :=
  .node
    (.node
      (.node .empty 0
        (.node .empty 1
          (.node .empty 2 .empty)))
      3
      (.node .empty 4 .empty))
    5
    .empty

private def badAvoidResetY : Fin 7 → Nat := ![4, 2, 0, 2, 0, 4, 2]

private theorem badAvoidResetY_avoids231 :
    badAvoidResetY avoids ![2, 3, 1] := by
  intro hcontains
  rcases (contains231_iff_exists_triple.mp hcontains) with
    ⟨i, j, k, hij, hjk, hki, hijv⟩
  have hY0 : badAvoidResetY (0 : Fin 7) = 4 := by native_decide
  have hY1 : badAvoidResetY (1 : Fin 7) = 2 := by native_decide
  have hY2 : badAvoidResetY (2 : Fin 7) = 0 := by native_decide
  have hY3 : badAvoidResetY (3 : Fin 7) = 2 := by native_decide
  have hY4 : badAvoidResetY (4 : Fin 7) = 0 := by native_decide
  have hY5 : badAvoidResetY (5 : Fin 7) = 4 := by native_decide
  have hY6 : badAvoidResetY (6 : Fin 7) = 2 := by native_decide
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [hY0, hY1, hY2, hY3, hY4, hY5, hY6] at *

private theorem amortized_reset_compare_three_avoiding_counterexample :
    ¬
      (splayPathSum badAvoidResetY
            (splay badAvoidResetTree (badAvoidResetY (0 : Fin 7)))
            [(1 : Fin 7), (2 : Fin 7), (3 : Fin 7), (4 : Fin 7),
              (5 : Fin 7), (6 : Fin 7)] +
          3 * activeBudget badAvoidResetY
            (splay (splay badAvoidResetTree (badAvoidResetY (0 : Fin 7))) 5)
            [(1 : Fin 7), (2 : Fin 7), (3 : Fin 7), (4 : Fin 7),
              (5 : Fin 7), (6 : Fin 7)] ≤
        ((splay badAvoidResetTree
            (badAvoidResetY (0 : Fin 7))).search_path_len 5 : ℝ) +
          splayPathSum badAvoidResetY
            (splay (splay badAvoidResetTree (badAvoidResetY (0 : Fin 7))) 5)
            [(1 : Fin 7), (2 : Fin 7), (3 : Fin 7), (4 : Fin 7),
              (5 : Fin 7), (6 : Fin 7)] +
          3 * activeBudget badAvoidResetY badAvoidResetTree
            [(0 : Fin 7), (1 : Fin 7), (2 : Fin 7), (3 : Fin 7),
              (4 : Fin 7), (5 : Fin 7), (6 : Fin 7)]) := by
  have hY0 : badAvoidResetY (0 : Fin 7) = 4 := by native_decide
  have hY1 : badAvoidResetY (1 : Fin 7) = 2 := by native_decide
  have hY2 : badAvoidResetY (2 : Fin 7) = 0 := by native_decide
  have hY3 : badAvoidResetY (3 : Fin 7) = 2 := by native_decide
  have hY4 : badAvoidResetY (4 : Fin 7) = 0 := by native_decide
  have hY5 : badAvoidResetY (5 : Fin 7) = 4 := by native_decide
  have hY6 : badAvoidResetY (6 : Fin 7) = 2 := by native_decide
  norm_num [badAvoidResetTree, splayPathSum, activeBudget,
    activeHullSize, activeHullKeys, searchPathKeys, BinaryTree.toKeyList,
    BinaryTree.search_path_len, splay, rotate, rotateRight, rotateLeft,
    hY0, hY1, hY2, hY3, hY4, hY5, hY6]

private def badActiveCertTree : BinaryTree :=
  .node .empty 0 (.node .empty 1 (.node .empty 2 .empty))

private def badActiveCertSeq : Fin 3 → Nat := ![0, 1, 0]

private theorem activeBudget_firstMax_budget_certificate_counterexample
    (K : ℝ) :
    let m : Fin 3 := 1
    ¬
      (let tp :=
        splayTreeAfter (prefixSeq badActiveCertSeq m)
          badActiveCertTree (List.finRange m.val)
      let ts := splay tp (badActiveCertSeq m)
      K * activeBudget (prefixSeq badActiveCertSeq m)
            badActiveCertTree (List.finRange m.val) +
          ((tp.search_path_len (badActiveCertSeq m) : ℝ) +
            (K * activeBudget (strictLowerSuffixSeq badActiveCertSeq m) ts
                (List.finRange
                  (strictLowerSuffixIndices badActiveCertSeq m).length) +
              7 * ((3 - (m.val + 1) : Nat) +
                badActiveCertTree.num_nodes : ℝ))) ≤
        K * activeBudget badActiveCertSeq badActiveCertTree
          (List.finRange 3)) := by
  dsimp
  intro h
  norm_num [badActiveCertSeq, badActiveCertTree, prefixSeq,
    strictLowerSuffixSeq, strictLowerSuffixIndices, suffixSeq,
    splayTreeAfter, splay, rotate, rotateRight, rotateLeft,
    activeBudget, activeHullSize, activeHullKeys, searchPathKeys,
    BinaryTree.toKeyList, BinaryTree.search_path_len, List.finRange,
    List.filter, BinaryTree.num_nodes] at h
  nlinarith

private def badLeftLiftTree : BinaryTree :=
  .node .empty 0 (.node .empty 1 (.node .empty 2 .empty))

private theorem probe_left_lift_counterexample :
    ¬
      ((splay badLeftLiftTree 2).search_path_len 0 ≤
        (splay (BinaryTree.node badLeftLiftTree 3 .empty) 2).search_path_len
          0) := by
  norm_num [badLeftLiftTree, splay, rotate, rotateRight, rotateLeft,
    BinaryTree.search_path_len]

end Splay
