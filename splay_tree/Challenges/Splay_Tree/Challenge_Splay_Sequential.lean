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

private theorem rightSubtree_num_nodes_le (t : BinaryTree) :
    (rightSubtree t).num_nodes ≤ t.num_nodes := by
  cases t with
  | empty =>
      simp [rightSubtree, BinaryTree.num_nodes]
  | node l k r =>
      simp [rightSubtree, BinaryTree.num_nodes]

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

private theorem rightSubtree_isBST_of_isBST :
    ∀ {t : BinaryTree}, IsBST t → IsBST (rightSubtree t)
| .empty, _hbst => by
    simp [rightSubtree]
    exact IsBST.left
| .node l k r, hbst => by
    cases hbst with
    | node _ _ _ _hleft _hright _hlbst hrbst =>
        simpa [rightSubtree] using hrbst

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
    simp only [splay.cost.eq_def, BinaryTree.search_path_len, zero_tsub, CharP.cast_eq_zero]
| .node l k r, q => by
    rw [splay.cost.eq_def]
    simp only [BinaryTree.search_path_len]
    by_cases hqk : q = k
    · simp only [hqk, ↓reduceIte, lt_self_iff_false, tsub_self, CharP.cast_eq_zero]
    · by_cases hq_lt_k : q < k
      · cases l with
        | empty =>
            simp only [hqk, ↓reduceIte, hq_lt_k, add_tsub_cancel_left, CharP.cast_eq_zero]
        | node ll lk lr =>
            by_cases hq_lt_lk : q < lk
            · cases ll with
              | empty =>
                  simp only [hqk, ↓reduceIte, hq_lt_k, hq_lt_lk, BinaryTree.search_path_len,
                    add_zero, Nat.reduceAdd, Nat.add_one_sub_one, Nat.cast_one]
              | node a x b =>
                  have hll := splay_cost_eq_search_path_len_sub_one
                    (BinaryTree.node a x b) q
                  simp only [hqk, ↓reduceIte, hq_lt_k, hq_lt_lk, hll, BinaryTree.search_path_len,
                    add_tsub_cancel_left, Nat.cast_add, Nat.cast_one, Nat.cast_ite]
                  simpa only [BinaryTree.search_path_len, Nat.cast_ite, Nat.cast_add,
                    Nat.cast_one] using
                    cast_pred_add_two_of_pos
                      ((BinaryTree.node a x b).search_path_len q)
                      (node_search_path_len_pos a x b q)
            · by_cases hlk_lt_q : lk < q
              · cases lr with
                | empty =>
                    simp only [hqk, ↓reduceIte, hq_lt_k, hq_lt_lk, hlk_lt_q,
                      BinaryTree.search_path_len, add_zero, Nat.reduceAdd, Nat.add_one_sub_one,
                      Nat.cast_one]
                | node a x b =>
                    have hlr := splay_cost_eq_search_path_len_sub_one
                      (BinaryTree.node a x b) q
                    simp only [hqk, ↓reduceIte, hq_lt_k, hq_lt_lk, hlk_lt_q, hlr,
                      BinaryTree.search_path_len, add_tsub_cancel_left, Nat.cast_add, Nat.cast_one,
                      Nat.cast_ite]
                    simpa only [BinaryTree.search_path_len, Nat.cast_ite, Nat.cast_add,
                      Nat.cast_one] using
                      cast_pred_add_two_of_pos
                        ((BinaryTree.node a x b).search_path_len q)
                        (node_search_path_len_pos a x b q)
              · simp only [hqk, ↓reduceIte, hq_lt_k, hq_lt_lk, hlk_lt_q,
                  BinaryTree.search_path_len, Nat.reduceAdd, Nat.add_one_sub_one, Nat.cast_one]
      · cases r with
        | empty =>
            have hk_lt_q : k < q := by
              exact lt_of_le_of_ne (Nat.le_of_not_lt hq_lt_k)
                (by intro h; exact hqk h.symm)
            simp only [hqk, ↓reduceIte, hq_lt_k, hk_lt_q, add_tsub_cancel_left, CharP.cast_eq_zero]
        | node rl rk rr =>
            have hk_lt_q : k < q := by
              exact lt_of_le_of_ne (Nat.le_of_not_lt hq_lt_k)
                (by intro h; exact hqk h.symm)
            by_cases hq_lt_rk : q < rk
            · cases rl with
              | empty =>
                  simp only [hqk, ↓reduceIte, hq_lt_k, hq_lt_rk, hk_lt_q,
                    BinaryTree.search_path_len, add_zero, Nat.reduceAdd, Nat.add_one_sub_one,
                    Nat.cast_one]
              | node a x b =>
                  have hrl := splay_cost_eq_search_path_len_sub_one
                    (BinaryTree.node a x b) q
                  simp only [hqk, ↓reduceIte, hq_lt_k, hq_lt_rk, hrl, BinaryTree.search_path_len,
                    hk_lt_q, add_tsub_cancel_left, Nat.cast_add, Nat.cast_one, Nat.cast_ite]
                  simpa only [BinaryTree.search_path_len, Nat.cast_ite, Nat.cast_add,
                    Nat.cast_one] using
                    cast_pred_add_two_of_pos
                      ((BinaryTree.node a x b).search_path_len q)
                      (node_search_path_len_pos a x b q)
            · by_cases hrk_lt_q : rk < q
              · cases rr with
                | empty =>
                    simp only [hqk, ↓reduceIte, hq_lt_k, hq_lt_rk, hrk_lt_q, hk_lt_q,
                      BinaryTree.search_path_len, add_zero, Nat.reduceAdd, Nat.add_one_sub_one,
                      Nat.cast_one]
                | node a x b =>
                    have hrr := splay_cost_eq_search_path_len_sub_one
                      (BinaryTree.node a x b) q
                    simp only [hqk, ↓reduceIte, hq_lt_k, hq_lt_rk, hrk_lt_q, hrr,
                      BinaryTree.search_path_len, hk_lt_q, add_tsub_cancel_left, Nat.cast_add,
                      Nat.cast_one, Nat.cast_ite]
                    simpa only [BinaryTree.search_path_len, Nat.cast_ite, Nat.cast_add,
                      Nat.cast_one] using
                      cast_pred_add_two_of_pos
                        ((BinaryTree.node a x b).search_path_len q)
                        (node_search_path_len_pos a x b q)
              · simp only [hqk, ↓reduceIte, hq_lt_k, hq_lt_rk, hrk_lt_q, hk_lt_q,
                  BinaryTree.search_path_len, Nat.reduceAdd, Nat.add_one_sub_one, Nat.cast_one]

private theorem splay_cost_le_search_path_len (t : BinaryTree) (q : Nat) :
    splay.cost t q ≤ t.search_path_len q := by
  rw [splay_cost_eq_search_path_len_sub_one]
  exact_mod_cast Nat.sub_le (t.search_path_len q) 1

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

private theorem isBST_right_mem_gt_root {l r : BinaryTree} {k q : Nat}
    (hbst : IsBST (BinaryTree.node l k r))
    (hmem : q ∈ r.toKeyList) :
    k < q := by
  cases hbst with
  | node _ _ _ _hleft hright _hlbst _hrbst =>
      exact (forallTree_iff_forall_mem.mp hright) q hmem

private theorem isBST_node_mem_left_of_lt_root
    {l r : BinaryTree} {k q : Nat}
    (hbst : IsBST (BinaryTree.node l k r))
    (hmem : q ∈ (BinaryTree.node l k r).toKeyList)
    (hqk : q < k) :
    q ∈ l.toKeyList := by
  cases hbst with
  | node _ _ _ hleft hright _hlbst _hrbst =>
      simp only [BinaryTree.toKeyList, List.mem_append,
        List.mem_singleton] at hmem
      rcases hmem with ((hmem_l | hqeq) | hmem_r)
      · exact hmem_l
      · subst q
        omega
      · have hkq : k < q :=
          (forallTree_iff_forall_mem.mp hright) q hmem_r
        omega

private theorem isBST_node_mem_right_of_gt_root
    {l r : BinaryTree} {k q : Nat}
    (hbst : IsBST (BinaryTree.node l k r))
    (hmem : q ∈ (BinaryTree.node l k r).toKeyList)
    (hkq : k < q) :
    q ∈ r.toKeyList := by
  cases hbst with
  | node _ _ _ hleft hright _hlbst _hrbst =>
      simp only [BinaryTree.toKeyList, List.mem_append,
        List.mem_singleton] at hmem
      rcases hmem with ((hmem_l | hqeq) | hmem_r)
      · have hqk : q < k :=
          (forallTree_iff_forall_mem.mp hleft) q hmem_l
        omega
      · subst q
        omega
      · exact hmem_r

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

private theorem splay_cost_add_one_eq_search_path_len_of_mem
    (t : BinaryTree) (q : Nat) (hmem : q ∈ t.toKeyList) :
    splay.cost t q + 1 = t.search_path_len q := by
  rw [splay_cost_eq_search_path_len_sub_one]
  have hpos := search_path_len_pos_of_mem t q hmem
  have hnat : (t.search_path_len q - 1) + 1 = t.search_path_len q := by
    omega
  exact_mod_cast hnat

private theorem tree_eq_node_empty_right (t : BinaryTree) (q : Nat)
    (hroot : rootKey t = some q) (hleft : leftSubtree t = .empty) :
    t = .node .empty q (rightSubtree t) := by
  cases t with
  | empty => simp [rootKey] at hroot
  | node l k r =>
      simp [rootKey] at hroot
      simp [leftSubtree] at hleft
      subst hroot; subst hleft
      simp [rightSubtree]

/-- Min-splay normal form: splaying the minimum key of a BST yields `node empty q R`
(the min at the root, no left child). Backbone of Elmasry's "splaying spine" reframing. -/
private theorem splay_min_eq_node_empty (t : BinaryTree) (q : Nat) (hbst : IsBST t)
    (hmem : q ∈ t.toKeyList) (hmin : ∀ k : Nat, k ∈ t.toKeyList → q ≤ k) :
    splay t q = .node .empty q (rightSubtree (splay t q)) :=
  tree_eq_node_empty_right (splay t q) q
    (splay_rootKey_eq_some_of_mem_isBST t q hbst hmem)
    (splay_leftSubtree_empty_of_min_isBST t q hbst hmem hmin)


/-- Shed-left (cost): accessing a key `q` greater than the root costs the same regardless
of the left subtree — `splay.cost`'s right branch never inspects `L`. This justifies
ignoring the accumulating left subtree during sequential access. -/
private theorem splay_cost_node_right_indep_left
    (L R : BinaryTree) (k q : Nat) (h : k < q) :
    splay.cost (.node L k R) q = splay.cost (.node .empty k R) q := by
  have h1 : ¬ q = k := by omega
  have h2 : ¬ q < k := by omega
  cases L with
  | empty => rfl
  | node ll lk lr =>
      cases R with
      | empty => simp [splay.cost, h1, h2]
      | node rl rk rr => simp [splay.cost, h1, h2]


/-- The sequential-access process: `seqTree init k` = tree after accessing `0,1,…,k-1`. -/
private def seqTree (init : BinaryTree) : Nat → BinaryTree
  | 0 => init
  | k + 1 => splay (seqTree init k) k

/-- Keys are preserved through the sequential process. -/
private theorem seqTree_toKeyList (init : BinaryTree) (k : Nat) :
    (seqTree init k).toKeyList = init.toKeyList := by
  induction k with
  | zero => rfl
  | succ k ih => rw [seqTree, splay_toKeyList, ih]

/-- BST is preserved through the sequential process. -/
private theorem seqTree_isBST (init : BinaryTree) (hbst : IsBST init) (k : Nat) :
    IsBST (seqTree init k) := by
  induction k with
  | zero => exact hbst
  | succ k ih => exact splay_isBST (seqTree init k) k ih

/-- After accessing `0,…,k` the last-accessed key `k` is at the root. -/
private theorem seqTree_rootKey (init : BinaryTree) (hbst : IsBST init)
    {n : Nat} (hkeys : ∀ m : Nat, m < n → m ∈ init.toKeyList)
    (k : Nat) (hk : k < n) :
    rootKey (seqTree init (k + 1)) = some k := by
  rw [seqTree]
  have hmem : k ∈ (seqTree init k).toKeyList := by
    rw [seqTree_toKeyList]; exact hkeys k hk
  exact splay_rootKey_eq_some_of_mem_isBST (seqTree init k) k
    (seqTree_isBST init hbst k) hmem


/-- A tree with a root key equals `node (leftSubtree) key (rightSubtree)`. -/
private theorem tree_eq_node_of_rootKey (t : BinaryTree) (m : Nat)
    (h : rootKey t = some m) : t = .node (leftSubtree t) m (rightSubtree t) := by
  cases t with
  | empty => simp [rootKey] at h
  | node l k r => simp only [rootKey, Option.some.injEq] at h; subst h; rfl

/-- Cost isolation: the cost of the `k`-th sequential access depends only on the right
subtree of the current tree (its root is `k-1`, and the access cost ignores the left part).
This is the formal core of Elmasry's "keep track only of the right subtree". -/
private theorem seq_access_cost_eq (init : BinaryTree) (hbst : IsBST init)
    {n : Nat} (hkeys : ∀ m : Nat, m < n → m ∈ init.toKeyList)
    (k : Nat) (hk1 : 1 ≤ k) (hkn : k - 1 < n) :
    splay.cost (seqTree init k) k
      = splay.cost (.node .empty (k - 1) (rightSubtree (seqTree init k))) k := by
  have hroot : rootKey (seqTree init k) = some (k - 1) := by
    have h := seqTree_rootKey init hbst hkeys (k - 1) hkn
    rwa [Nat.sub_add_cancel hk1] at h
  obtain ⟨l, r, heq⟩ : ∃ l r, seqTree init k = .node l (k - 1) r := by
    cases hh : seqTree init k with
    | empty => rw [hh] at hroot; simp [rootKey] at hroot
    | node a b c =>
        rw [hh] at hroot; simp only [rootKey, Option.some.injEq] at hroot
        exact ⟨a, c, by rw [hroot]⟩
  rw [heq, splay_cost_node_right_indep_left l r (k - 1) k (by omega)]
  simp [rightSubtree]


/-- Accumulated rotation cost of the sequential process (mirrors `seqTree`). -/
private def seqCost (init : BinaryTree) : Nat → ℝ
  | 0 => 0
  | k + 1 => seqCost init k + splay.cost (seqTree init k) k

/-- The `(tree, cost)` state after sequentially accessing the keys in `ks`. -/
private def seqAcc (init : BinaryTree) (ks : List Nat) : BinaryTree × ℝ :=
  ks.foldl (fun (acc : BinaryTree × ℝ) (m : Nat) =>
    (splay acc.1 m, acc.2 + splay.cost acc.1 m)) (init, 0)

/-- Folding the cost recursion over `range n` reproduces `(seqTree, seqCost)`. -/
private theorem seqAcc_range_eq (init : BinaryTree) (n : Nat) :
    seqAcc init (List.range n) = (seqTree init n, seqCost init n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      unfold seqAcc at ih ⊢
      rw [List.range_succ, List.foldl_append, ih]
      simp [seqTree, seqCost]

/-- **Bridge** (Component A keystone): the real sequential-access cost
`sequence_cost init (one_to_n n)` equals the recursive process cost `seqCost init n`,
i.e. `Σₖ splay.cost (seqTree init k) k`. This connects the actual challenge goal to the
min-splay reframing. -/
private theorem sequence_cost_eq_seqCost (init : BinaryTree) (n : Nat) :
    splay.sequence_cost init (one_to_n n) = seqCost init n := by
  have hfold : splay.sequence_cost init (one_to_n n) = (seqAcc init (List.range n)).2 := by
    unfold splay.sequence_cost seqAcc
    rw [← List.map_coe_finRange (n := n), List.foldl_map]
    rfl
  rw [hfold, seqAcc_range_eq]


/-- `seqCost` as an explicit finite sum of per-access rotation costs. -/
private theorem seqCost_eq_sum (init : BinaryTree) (n : Nat) :
    seqCost init n = ∑ k ∈ Finset.range n, splay.cost (seqTree init k) k := by
  induction n with
  | zero => simp [seqCost]
  | succ n ih => rw [Finset.sum_range_succ, ← ih]; rfl

/-- **Goal reduction** (Component A complete): the challenge's `sequence_cost` equals the
explicit sum of per-access rotation costs over the sequential process. Bounding this sum by
`c·n` (Elmasry's amortized accounting, components B–E) closes `Splay.sequential`. -/
private theorem sequence_cost_eq_sum (init : BinaryTree) (n : Nat) :
    splay.sequence_cost init (one_to_n n)
      = ∑ k ∈ Finset.range n, splay.cost (seqTree init k) k := by
  rw [sequence_cost_eq_seqCost, seqCost_eq_sum]


/-- The sequential process preserves the node count. -/
private theorem seqTree_num_nodes (init : BinaryTree) (k : Nat) :
    (seqTree init k).num_nodes = init.num_nodes := by
  induction k with
  | zero => rfl
  | succ k ih => rw [seqTree, splay_num_nodes, ih]

/-- **Right-subtree key-set evolution** (the *true* Component-A structural fact, replacing the
naive — and false — `Rₖ₊₁ = rightSubtree(splay Rₖ k)` recursion): after accessing `0…k`, the
remaining right subtree holds exactly the not-yet-reached keys `> k`. This is what Elmasry's
"remaining tree" actually is; the per-step splay *shape* is not a clean recursion (splay pairs
rotations bottom-up, so prepending the root changes the result), but the *key set* is. -/
private theorem rightSubtree_seqTree_succ_mem_iff (init : BinaryTree) (hbst : IsBST init)
    {n : Nat} (hkeys : ∀ m : Nat, m < n → m ∈ init.toKeyList)
    (k : Nat) (hk : k < n) (x : Nat) :
    x ∈ (rightSubtree (seqTree init (k + 1))).toKeyList
      ↔ (k < x ∧ x ∈ init.toKeyList) := by
  have hroot : rootKey (seqTree init (k + 1)) = some k :=
    seqTree_rootKey init hbst hkeys k hk
  have hkeyk : (seqTree init (k + 1)).toKeyList = init.toKeyList :=
    seqTree_toKeyList init (k + 1)
  have hbstk : IsBST (seqTree init (k + 1)) := seqTree_isBST init hbst (k + 1)
  obtain ⟨l, r, heq⟩ : ∃ l r, seqTree init (k + 1) = .node l k r := by
    cases hh : seqTree init (k + 1) with
    | empty => rw [hh] at hroot; simp [rootKey] at hroot
    | node a b c =>
        rw [hh] at hroot; simp only [rootKey, Option.some.injEq] at hroot
        exact ⟨a, c, by rw [hroot]⟩
  rw [heq] at hkeyk hbstk
  rw [heq]; simp only [rightSubtree]
  constructor
  · intro hx
    refine ⟨isBST_right_mem_gt_root hbstk hx, ?_⟩
    have hxn : x ∈ (BinaryTree.node l k r).toKeyList := by
      simp only [BinaryTree.toKeyList, List.mem_append, List.mem_singleton]; tauto
    rw [hkeyk] at hxn; exact hxn
  · rintro ⟨hkx, hxmem⟩
    have hxnode : x ∈ (BinaryTree.node l k r).toKeyList := by rw [hkeyk]; exact hxmem
    exact isBST_node_mem_right_of_gt_root hbstk hxnode hkx


/-! ### Component B (charging argument) — Milestone 1: reduce to the depth-sum

Since `splay.cost = search_path_len - 1` (rotations = depth), the challenge goal reduces to
bounding `∑ₖ search_path_len (seqTree init k) k`. This connects the sequential process to the
file's extensive `search_path_len`/`splayPathSum` machinery. -/

/-- **Milestone 1**: the sequential-access cost equals the depth-sum minus `n`. Hence
`Splay.sequential` (the `≤ c·n` goal) is equivalent to `∑ₖ search_path_len (seqTree init k) k
≤ (c+1)·n`. -/
private theorem sequence_cost_eq_search_path_sum (init : BinaryTree) (hbst : IsBST init)
    {n : Nat} (hkeys : ∀ m : Nat, m < n → m ∈ init.toKeyList) :
    splay.sequence_cost init (one_to_n n)
      = (∑ k ∈ Finset.range n, ((seqTree init k).search_path_len k : ℝ)) - n := by
  rw [sequence_cost_eq_sum]
  have hstep : ∀ k ∈ Finset.range n,
      splay.cost (seqTree init k) k = ((seqTree init k).search_path_len k : ℝ) - 1 := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hmem : k ∈ (seqTree init k).toKeyList := by
      rw [seqTree_toKeyList]; exact hkeys k hk
    have h := splay_cost_add_one_eq_search_path_len_of_mem (seqTree init k) k hmem
    linarith
  rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib]
  simp [Finset.sum_const, Finset.card_range]


/-- **Milestone 2** (per-step spine reduction): for `1 ≤ k` (root is `k-1`), the access depth is
`1 +` the depth of `k` within the right subtree `Rₖ`. Since `k = min Rₖ`, the latter is exactly
`leftSpineLen(Rₖ) + 1`. Hence `∑ₖ search_path_len ≤ O(n) + ∑ₖ search_path_len(Rₖ, k)`, and the
charging target becomes `∑ₖ search_path_len (rightSubtree (seqTree init k)) k ≤ C·n`. -/
private theorem search_path_len_seqTree_eq_succ (init : BinaryTree) (hbst : IsBST init)
    {n : Nat} (hkeys : ∀ m : Nat, m < n → m ∈ init.toKeyList)
    (k : Nat) (hk1 : 1 ≤ k) (hkn : k - 1 < n) :
    (seqTree init k).search_path_len k
      = 1 + (rightSubtree (seqTree init k)).search_path_len k := by
  have hroot : rootKey (seqTree init k) = some (k - 1) := by
    have h := seqTree_rootKey init hbst hkeys (k - 1) hkn
    rwa [Nat.sub_add_cancel hk1] at h
  obtain ⟨l, r, heq⟩ : ∃ l r, seqTree init k = .node l (k - 1) r := by
    cases hh : seqTree init k with
    | empty => rw [hh] at hroot; simp [rootKey] at hroot
    | node a b c =>
        rw [hh] at hroot; simp only [rootKey, Option.some.injEq] at hroot
        exact ⟨a, c, by rw [hroot]⟩
  rw [heq]; simp only [rightSubtree]
  exact search_path_len_node_of_gt (by omega)


/-- The **splaying spine** as an explicit list of keys: the keys from the root down the left
spine (root first, leftmost/min last). This is the central object Elmasry's coloring acts on. -/
private def leftSpine : BinaryTree → List Nat
  | .empty => []
  | .node l k _ => k :: leftSpine l

/-- For the minimum key `q` of a BST `t`, the search path is exactly the left spine, so its
length equals the number of spine nodes. Hence the charging target `∑ₖ search_path_len(Rₖ, k)`
equals `∑ₖ |leftSpine Rₖ|` — the total spine length over the process. -/
private theorem search_path_len_min_eq_leftSpine_length :
    ∀ (t : BinaryTree) (q : Nat), IsBST t → q ∈ t.toKeyList →
      (∀ y ∈ t.toKeyList, q ≤ y) → t.search_path_len q = (leftSpine t).length
  | .empty, q, _, hmem, _ => by simp [BinaryTree.toKeyList] at hmem
  | .node l k r, q, hbst, hmem, hmin => by
      have hqk : q ≤ k := hmin k (by simp [BinaryTree.toKeyList])
      rcases Nat.lt_or_ge q k with hlt | hge
      · rw [search_path_len_node_of_lt hlt]
        have hmeml : q ∈ l.toKeyList := isBST_node_mem_left_of_lt_root hbst hmem hlt
        have hbstl : IsBST l := by cases hbst; assumption
        have hminl : ∀ y ∈ l.toKeyList, q ≤ y :=
          fun y hy => hmin y (by simp only [BinaryTree.toKeyList, List.mem_append]; tauto)
        rw [search_path_len_min_eq_leftSpine_length l q hbstl hmeml hminl]
        simp only [leftSpine, List.length_cons]; omega
      · have hqeq : q = k := by omega
        subst hqeq
        rw [search_path_len_node_of_eq rfl]
        cases l with
        | empty => simp [leftSpine]
        | node ll lk lr =>
            exfalso
            have hlkmem : lk ∈ (BinaryTree.node (BinaryTree.node ll lk lr) q r).toKeyList := by
              simp [BinaryTree.toKeyList]
            have hle : q ≤ lk := hmin lk hlkmem
            have hlt : lk < q := by
              cases hbst with
              | node _ _ _ hleft _ _ _ =>
                  exact (forallTree_iff_forall_mem.mp hleft) lk (by simp [BinaryTree.toKeyList])
            omega


/-- **Capstone of the reduction**: the per-access rotation cost equals the splaying-spine length.
So the total cost `= ∑ₖ |leftSpine (rightSubtree (seqTree init k))|`, and the 50-pt goal is exactly
"the total splaying-spine length is linear". Combines M1/M2/M2.5 with the right-subtree key set
`{k,…,n-1}` (so `k = min Rₖ`). -/
private theorem splay_cost_seqTree_eq_leftSpine_length (init : BinaryTree) (hbst : IsBST init)
    {n : Nat} (hkeys : ∀ m : Nat, m < n → m ∈ init.toKeyList)
    (k : Nat) (hk1 : 1 ≤ k) (hkn : k < n) :
    splay.cost (seqTree init k) k
      = ((leftSpine (rightSubtree (seqTree init k))).length : ℝ) := by
  have hRbst : IsBST (rightSubtree (seqTree init k)) :=
    rightSubtree_isBST_of_isBST (seqTree_isBST init hbst k)
  have hmemiff : ∀ x, x ∈ (rightSubtree (seqTree init k)).toKeyList ↔
      (k - 1 < x ∧ x ∈ init.toKeyList) := by
    intro x
    have h := rightSubtree_seqTree_succ_mem_iff init hbst hkeys (k - 1) (by omega) x
    rwa [Nat.sub_add_cancel hk1] at h
  have hkmemR : k ∈ (rightSubtree (seqTree init k)).toKeyList :=
    (hmemiff k).mpr ⟨by omega, hkeys k hkn⟩
  have hkminR : ∀ y ∈ (rightSubtree (seqTree init k)).toKeyList, k ≤ y :=
    fun y hy => by have := (hmemiff y).mp hy; omega
  have hsplR : (rightSubtree (seqTree init k)).search_path_len k
      = (leftSpine (rightSubtree (seqTree init k))).length :=
    search_path_len_min_eq_leftSpine_length (rightSubtree (seqTree init k)) k hRbst hkmemR hkminR
  have hsucc : (seqTree init k).search_path_len k
      = 1 + (rightSubtree (seqTree init k)).search_path_len k :=
    search_path_len_seqTree_eq_succ init hbst hkeys k hk1 (by omega)
  have hkmem : k ∈ (seqTree init k).toKeyList := by
    rw [seqTree_toKeyList]; exact hkeys k hkn
  have hcost : splay.cost (seqTree init k) k + 1
      = ((seqTree init k).search_path_len k : ℝ) :=
    splay_cost_add_one_eq_search_path_len_of_mem (seqTree init k) k hkmem
  rw [hsucc, hsplR] at hcost
  push_cast at hcost
  linarith


/-! ### Component B (the coloring) — foundations

Elmasry colors each node over time to count rotations (= links). We begin the state model.
The hard dynamics (the linking rules, relations (1)–(5), Lemma 1, the `h²/2` credit accounting)
are built on top of these. -/

/-- Elmasry's node coloring. `uncolored` until a node first joins a splaying spine (→`yellow`),
then `green` once linked; `black` overrides for nodes on the tree's right spine. -/
private inductive SplayColor where
  | uncolored
  | yellow
  | green
  | black
deriving DecidableEq, Repr

/-- The right spine of a tree as a list of keys (root first, rightmost last). Black nodes live
here; `g`/`h` count colored nodes along right spines. -/
private def rightSpine : BinaryTree → List Nat
  | .empty => []
  | .node _ k r => k :: rightSpine r


/-! ### The idealized process (Elmasry's mental model)

Elmasry's restructuring (Fig. 3) is phrased on the process that repeatedly splays the *minimum*
of the remaining tree and keeps only its right subtree. Unlike the real right-subtree sequence
`Rₖ` (whose shape is *not* `rightSubtree (splay Rₖ k)` — the parity mismatch), this idealized
sequence `Iₖ` **does** satisfy the clean recursion, so the coloring/relations transcribe directly.
Empirically `∑ₖ |leftSpine Iₖ| ≥ ∑ₖ |leftSpine Rₖ|` up to an `O(n)` gap, so a bound on the ideal
process plus a process-comparison closes the real one. -/

/-- The idealized process: `Iₖ` = repeatedly splay the minimum and drop it (keep right subtree).
This is the clean-recursion process Elmasry's argument is stated on. -/
private def idealTree (init : BinaryTree) : Nat → BinaryTree
  | 0 => init
  | k + 1 => rightSubtree (splay (idealTree init k) k)

/-- The ideal process preserves BST-ness. -/
private theorem idealTree_isBST (init : BinaryTree) (hbst : IsBST init) (k : Nat) :
    IsBST (idealTree init k) := by
  induction k with
  | zero => exact hbst
  | succ k ih =>
      exact rightSubtree_isBST_of_isBST (splay_isBST (idealTree init k) k ih)

/-- **Key-set invariant of the ideal process**: `Iₖ` holds exactly the keys `≥ k`. (Here the
clean recursion pays off: `mem_rightSubtree_splay_min_iff_gt` applies at every step since `k` is
genuinely the min of `Iₖ`.) -/
private theorem idealTree_mem_iff (init : BinaryTree) (hbst : IsBST init)
    {n : Nat} (hkeys : ∀ m : Nat, m < n → m ∈ init.toKeyList) :
    ∀ (k : Nat), k ≤ n → ∀ x, x ∈ (idealTree init k).toKeyList ↔ (k ≤ x ∧ x ∈ init.toKeyList) := by
  intro k
  induction k with
  | zero =>
      intro _ x
      exact ⟨fun hx => ⟨Nat.zero_le x, hx⟩, fun hx => hx.2⟩
  | succ k ih =>
      intro hk x
      have hkn : k < n := by omega
      have ihk := ih (by omega)
      have hkmem : k ∈ (idealTree init k).toKeyList := (ihk k).mpr ⟨le_refl k, hkeys k hkn⟩
      have hkmin : ∀ y : Nat, y ∈ (idealTree init k).toKeyList → k ≤ y :=
        fun y hy => ((ihk y).mp hy).1
      have hbstk : IsBST (idealTree init k) := idealTree_isBST init hbst k
      rw [show idealTree init (k + 1) = rightSubtree (splay (idealTree init k) k) from rfl,
          mem_rightSubtree_splay_min_iff_gt (idealTree init k) k x hbstk hkmem hkmin, ihk x]
      constructor
      · rintro ⟨⟨_, hxinit⟩, hklt⟩; exact ⟨by omega, hxinit⟩
      · rintro ⟨hk1x, hxinit⟩; exact ⟨⟨by omega, hxinit⟩, by omega⟩


/-- Every left-spine key belongs to the tree. -/
private theorem leftSpine_subset_toKeyList :
    ∀ (t : BinaryTree) (x : Nat), x ∈ leftSpine t → x ∈ t.toKeyList
  | .empty, x, hx => by simp [leftSpine] at hx
  | .node l k r, x, hx => by
      simp only [leftSpine, List.mem_cons] at hx
      rcases hx with rfl | hx
      · simp [BinaryTree.toKeyList]
      · have := leftSpine_subset_toKeyList l x hx
        simp only [BinaryTree.toKeyList, List.mem_append]; tauto

/-- The splaying spine of the ideal process at step `k` (the keys Elmasry colors at that step). -/
private def idealSpine (init : BinaryTree) (k : Nat) : List Nat :=
  leftSpine (idealTree init k)

/-- Every node on the step-`k` splaying spine is a not-yet-reached key (`k ≤ x`). So the spine
lives entirely in `{k,…,n-1}` — colored nodes are exactly the keys not yet splayed past. -/
private theorem idealSpine_mem_ge (init : BinaryTree) (hbst : IsBST init)
    {n : Nat} (hkeys : ∀ m : Nat, m < n → m ∈ init.toKeyList)
    (k : Nat) (hk : k ≤ n) (x : Nat) (hx : x ∈ idealSpine init k) : k ≤ x := by
  have hmem : x ∈ (idealTree init k).toKeyList :=
    leftSpine_subset_toKeyList (idealTree init k) x hx
  exact ((idealTree_mem_iff init hbst hkeys k hk x).mp hmem).1


/-- The right subtree of the minimum node (the min's "cargo"): when the min is splayed away,
exactly the left spine of this subtree enters the new splaying spine. -/
private def minCargo : BinaryTree → BinaryTree
  | .empty => .empty
  | .node .empty _ r => r
  | .node (.node a x b) _ _ => minCargo (.node a x b)

/-- **Entrant-source lemma** (verified empirically with 0 violations, now proven): after
splaying the minimum `q`, every node on the new splaying spine `leftSpine (rightSubtree (splay
t q))` was either already on the old spine `leftSpine t`, or enters from `leftSpine (minCargo
t)` — the left spine of the min's right subtree. This pins down exactly where spine entrants
come from; bounding total entries is then the remaining accounting core. -/
private theorem leftSpine_rightSubtree_splay_min_subset :
    ∀ (t : BinaryTree) (q : Nat), IsBST t → q ∈ t.toKeyList →
      (∀ y ∈ t.toKeyList, q ≤ y) →
      ∀ x, x ∈ leftSpine (rightSubtree (splay t q)) →
        x ∈ leftSpine t ∨ x ∈ leftSpine (minCargo t)
  | .empty, q, _, hmem, _, x, hx => by simp only [BinaryTree.toKeyList, List.not_mem_nil] at hmem
  | .node l k r, q, hbst, hmem, hmin, x, hx => by
      rcases eq_or_ne q k with hqk | hqk
      · -- accessed at root: root is the min ⇒ left subtree is empty; splay is the identity
        subst hqk
        have hleq : l = .empty := by
          cases l with
          | empty => rfl
          | node la lx lb =>
              exfalso
              have hlx_mem : lx ∈ (BinaryTree.node (.node la lx lb) q r).toKeyList := by
                simp only [BinaryTree.toKeyList, List.append_assoc, List.cons_append,
                  List.nil_append, List.mem_append, List.mem_cons, true_or, or_true]
              have hlx_lt : lx < q := by
                cases hbst with
                | node _ _ _ hfl _ _ _ =>
                    exact (forallTree_iff_forall_mem.mp hfl) lx (by simp [BinaryTree.toKeyList])
              have := hmin lx hlx_mem
              omega
        subst hleq
        have hsp : splay (BinaryTree.node .empty q r) q = BinaryTree.node .empty q r := by
          simp only [splay.eq_def, ↓reduceIte]
        rw [hsp] at hx
        simp only [rightSubtree] at hx
        right
        simpa only [minCargo] using hx
      · -- q ≠ k: q < k (q is the min), so the access goes left
        have hkmem : k ∈ (BinaryTree.node l k r).toKeyList := by simp [BinaryTree.toKeyList]
        have hqlt : q < k := lt_of_le_of_ne (hmin k hkmem) hqk
        have hql : q ∈ l.toKeyList := isBST_node_mem_left_of_lt_root hbst hmem hqlt
        have hbl : IsBST l := by cases hbst; assumption
        cases l with
        | empty => simp only [BinaryTree.toKeyList, List.not_mem_nil] at hql
        | node ll lk lr =>
            have hminl : ∀ y ∈ (BinaryTree.node ll lk lr).toKeyList, q ≤ y := by
              intro y hy
              refine hmin y ?_
              rw [BinaryTree.toKeyList]
              exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hy)))
            have hqlk : q ≤ lk := hminl lk (by simp [BinaryTree.toKeyList])
            rcases eq_or_ne q lk with hqeq | hqne
            · -- found at child (zig): the min is the left child; its left subtree is empty
              subst hqeq
              have hlleq : ll = .empty := by
                cases ll with
                | empty => rfl
                | node a b c =>
                    exfalso
                    have hb_lt : b < q := by
                      cases hbl with
                      | node _ _ _ hfl _ _ _ =>
                          exact (forallTree_iff_forall_mem.mp hfl) b
                            (by simp [BinaryTree.toKeyList])
                    have := hminl b (by simp [BinaryTree.toKeyList])
                    omega
              subst hlleq
              have hnk : ¬ q = k := hqk
              have hnq : ¬ q < q := lt_irrefl q
              have hsp : splay (BinaryTree.node (.node .empty q lr) k r) q
                  = BinaryTree.node .empty q (.node lr k r) := by
                rw [splay.eq_def]
                simp only [hnk, ↓reduceIte, hqlt, lt_self_iff_false, rotate, rotateRight]
              rw [hsp] at hx
              simp only [rightSubtree, leftSpine, List.mem_cons] at hx
              rcases hx with rfl | hx
              · left; simp only [leftSpine, List.mem_cons, List.not_mem_nil, or_false, true_or]
              · right; simpa only [minCargo] using hx
            · -- q < lk: zig-zig with recursion into ll
              have hqllt : q < lk := lt_of_le_of_ne hqlk hqne
              have hqll : q ∈ ll.toKeyList :=
                isBST_node_mem_left_of_lt_root hbl hql hqllt
              cases ll with
              | empty => simp only [BinaryTree.toKeyList, List.not_mem_nil] at hqll
              | node a b c =>
                  have hbll : IsBST (BinaryTree.node a b c) := by cases hbl; assumption
                  have hminll : ∀ y ∈ (BinaryTree.node a b c).toKeyList, q ≤ y := by
                    intro y hy
                    refine hminl y ?_
                    rw [BinaryTree.toKeyList]
                    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hy)))
                  have hS := splay_min_eq_node_empty (BinaryTree.node a b c) q hbll hqll hminll
                  have hnk : ¬ q = k := hqk
                  have hsp : splay (BinaryTree.node (.node (.node a b c) lk lr) k r) q
                      = BinaryTree.node .empty q
                          (.node (rightSubtree (splay (BinaryTree.node a b c) q)) lk
                            (.node lr k r)) := by
                    rw [splay.eq_def]
                    simp only [if_neg hnk, if_pos hqlt, if_pos hqllt]
                    rw [hS]
                    simp only [rotate, rotateRight, rightSubtree]
                  rw [hsp] at hx
                  simp only [rightSubtree, leftSpine, List.mem_cons] at hx
                  rcases hx with rfl | hx
                  · left; simp only [leftSpine, List.mem_cons, true_or, or_true]
                  · rcases leftSpine_rightSubtree_splay_min_subset (BinaryTree.node a b c) q
                        hbll hqll hminll x hx with hold | hcargo
                    · left
                      show x ∈ k :: lk :: leftSpine (BinaryTree.node a b c)
                      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hold)
                    · right
                      simpa only [minCargo] using hcargo


/-- **Halving lemma** for min-splay (the geometric-decay engine): the new splaying spine is at
most half the old spine plus the entrants. `2·s' ≤ s + 2·e` where `s' = |leftSpine(rightSubtree
(splay t q))|`, `s = |leftSpine t|`, `e = |leftSpine (minCargo t)|`. With the entrant bound this
yields the linear spine-sum by geometric unrolling. -/
private theorem leftSpine_rightSubtree_splay_min_length :
    ∀ (t : BinaryTree) (q : Nat), IsBST t → q ∈ t.toKeyList →
      (∀ y ∈ t.toKeyList, q ≤ y) →
      2 * (leftSpine (rightSubtree (splay t q))).length
        ≤ (leftSpine t).length + 2 * (leftSpine (minCargo t)).length
  | .empty, q, _, hmem, _ => by simp only [BinaryTree.toKeyList, List.not_mem_nil] at hmem
  | .node l k r, q, hbst, hmem, hmin => by
      rcases eq_or_ne q k with hqk | hqk
      · subst hqk
        have hleq : l = .empty := by
          cases l with
          | empty => rfl
          | node la lx lb =>
              exfalso
              have hlx_lt : lx < q := by
                cases hbst with
                | node _ _ _ hfl _ _ _ =>
                    exact (forallTree_iff_forall_mem.mp hfl) lx (by simp [BinaryTree.toKeyList])
              have := hmin lx (by simp [BinaryTree.toKeyList])
              omega
        subst hleq
        have hsp : splay (BinaryTree.node .empty q r) q = BinaryTree.node .empty q r := by
          simp only [splay.eq_def, ↓reduceIte]
        rw [hsp]
        simp only [rightSubtree, leftSpine, List.length_cons, List.length_nil, zero_add, minCargo,
          le_add_iff_nonneg_left, zero_le]
      · have hkmem : k ∈ (BinaryTree.node l k r).toKeyList := by simp [BinaryTree.toKeyList]
        have hqlt : q < k := lt_of_le_of_ne (hmin k hkmem) hqk
        have hql : q ∈ l.toKeyList := isBST_node_mem_left_of_lt_root hbst hmem hqlt
        have hbl : IsBST l := by cases hbst; assumption
        cases l with
        | empty => simp only [BinaryTree.toKeyList, List.not_mem_nil] at hql
        | node ll lk lr =>
            have hminl : ∀ y ∈ (BinaryTree.node ll lk lr).toKeyList, q ≤ y := by
              intro y hy
              refine hmin y ?_
              rw [BinaryTree.toKeyList]
              exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hy)))
            have hqlk : q ≤ lk := hminl lk (by simp [BinaryTree.toKeyList])
            rcases eq_or_ne q lk with hqeq | hqne
            · subst hqeq
              have hlleq : ll = .empty := by
                cases ll with
                | empty => rfl
                | node a b c =>
                    exfalso
                    have hb_lt : b < q := by
                      cases hbl with
                      | node _ _ _ hfl _ _ _ =>
                          exact (forallTree_iff_forall_mem.mp hfl) b
                            (by simp [BinaryTree.toKeyList])
                    have := hminl b (by simp [BinaryTree.toKeyList])
                    omega
              subst hlleq
              have hnk : ¬ q = k := hqk
              have hnq : ¬ q < q := lt_irrefl q
              have hsp : splay (BinaryTree.node (.node .empty q lr) k r) q
                  = BinaryTree.node .empty q (.node lr k r) := by
                rw [splay.eq_def]
                simp only [hnk, ↓reduceIte, hqlt, lt_self_iff_false, rotate, rotateRight]
              rw [hsp]
              simp only [rightSubtree, minCargo, leftSpine, List.length_cons, List.length_nil]
              omega
            · have hqllt : q < lk := lt_of_le_of_ne hqlk hqne
              have hqll : q ∈ ll.toKeyList :=
                isBST_node_mem_left_of_lt_root hbl hql hqllt
              cases ll with
              | empty => simp only [BinaryTree.toKeyList, List.not_mem_nil] at hqll
              | node a b c =>
                  have hbll : IsBST (BinaryTree.node a b c) := by cases hbl; assumption
                  have hminll : ∀ y ∈ (BinaryTree.node a b c).toKeyList, q ≤ y := by
                    intro y hy
                    refine hminl y ?_
                    rw [BinaryTree.toKeyList]
                    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hy)))
                  have hS := splay_min_eq_node_empty (BinaryTree.node a b c) q hbll hqll hminll
                  have hnk : ¬ q = k := hqk
                  have hsp : splay (BinaryTree.node (.node (.node a b c) lk lr) k r) q
                      = BinaryTree.node .empty q
                          (.node (rightSubtree (splay (BinaryTree.node a b c) q)) lk
                            (.node lr k r)) := by
                    rw [splay.eq_def]
                    simp only [if_neg hnk, if_pos hqlt, if_pos hqllt]
                    rw [hS]
                    simp only [rotate, rotateRight, rightSubtree]
                  have ih := leftSpine_rightSubtree_splay_min_length (BinaryTree.node a b c) q
                    hbll hqll hminll
                  rw [hsp]
                  have hmc : minCargo (BinaryTree.node (.node (.node a b c) lk lr) k r)
                      = minCargo (BinaryTree.node a b c) := by
                    simp only [minCargo]
                  rw [hmc]
                  simp only [rightSubtree, leftSpine, List.length_cons] at ih ⊢
                  omega


/-- **Real-shape halving**: the per-step inequality for the actual sequential process. At step
`k` the tree is `node L m R` (`m = k-1` at the root) and we splay `q = k = min R`, which does one
zag-type step at the root and then a min-splay inside `R`'s left child. The new right subtree's
spine obeys `2·s' ≤ s + 1 + 2·e` with `s = |leftSpine R|`, `e = |leftSpine (minCargo R)|`. -/
private theorem real_halving (L R : BinaryTree) (m q : Nat)
    (hbst : IsBST (BinaryTree.node L m R)) (hmq : m < q)
    (hqR : q ∈ R.toKeyList) (hminR : ∀ y ∈ R.toKeyList, q ≤ y) :
    2 * (leftSpine (rightSubtree (splay (BinaryTree.node L m R) q))).length
      ≤ (leftSpine R).length + 1 + 2 * (leftSpine (minCargo R)).length := by
  have hbR : IsBST R := by cases hbst; assumption
  have hnqm : ¬ q = m := by omega
  have hnqltm : ¬ q < m := by omega
  cases R with
  | empty => simp [BinaryTree.toKeyList] at hqR
  | node rl rk rr =>
      have hqrk : q ≤ rk := hminR rk (by simp [BinaryTree.toKeyList])
      rcases eq_or_ne q rk with hqeq | hqne
      · -- min at R's root: single zag, R' = rr
        subst hqeq
        have hrleq : rl = .empty := by
          cases rl with
          | empty => rfl
          | node a b c =>
              exfalso
              have hb_lt : b < q := by
                cases hbR with
                | node _ _ _ hfl _ _ _ =>
                    exact (forallTree_iff_forall_mem.mp hfl) b (by simp [BinaryTree.toKeyList])
              have := hminR b (by simp [BinaryTree.toKeyList])
              omega
        subst hrleq
        have hnq : ¬ q < q := lt_irrefl q
        have hsp : splay (BinaryTree.node L m (.node .empty q rr)) q
            = BinaryTree.node (.node L m .empty) q rr := by
          rw [splay.eq_def]
          simp [hnqm, hnqltm, hnq, rotate, rotateLeft]
        rw [hsp]
        simp only [rightSubtree, minCargo, leftSpine, List.length_cons, List.length_nil]
        omega
      · -- min strictly inside rl: zagZig wrapper around a min-splay of rl
        have hqltrk : q < rk := lt_of_le_of_ne hqrk hqne
        have hqrl : q ∈ rl.toKeyList := isBST_node_mem_left_of_lt_root hbR hqR hqltrk
        have hbrl : IsBST rl := by cases hbR; assumption
        have hminrl : ∀ y ∈ rl.toKeyList, q ≤ y := by
          intro y hy
          exact hminR y (by
            simp only [BinaryTree.toKeyList, List.mem_append] at hy ⊢; tauto)
        cases rl with
        | empty => simp [BinaryTree.toKeyList] at hqrl
        | node a b c =>
            have hS := splay_min_eq_node_empty (BinaryTree.node a b c) q hbrl hqrl hminrl
            have hsp : splay (BinaryTree.node L m (.node (.node a b c) rk rr)) q
                = BinaryTree.node (.node L m .empty) q
                    (.node (rightSubtree (splay (BinaryTree.node a b c) q)) rk rr) := by
              rw [splay.eq_def]
              simp only [if_neg hnqm, if_neg hnqltm, if_pos hqltrk]
              rw [hS]
              simp [rotate, rotateLeft, rotateRight, rightSubtree]
            have ih := leftSpine_rightSubtree_splay_min_length (BinaryTree.node a b c) q
              hbrl hqrl hminrl
            rw [hsp]
            have hmc : minCargo (BinaryTree.node (.node a b c) rk rr)
                = minCargo (BinaryTree.node a b c) := by
              simp [minCargo]
            rw [hmc]
            simp only [rightSubtree, leftSpine, List.length_cons] at ih ⊢
            omega


/-- A left spine is no longer than the tree. -/
private theorem leftSpine_length_le_num_nodes :
    ∀ (t : BinaryTree), (leftSpine t).length ≤ t.num_nodes
  | .empty => by simp [leftSpine, BinaryTree.num_nodes]
  | .node l k r => by
      have := leftSpine_length_le_num_nodes l
      simp only [leftSpine, List.length_cons, BinaryTree.num_nodes]
      omega

/-- Spine length of the process: `sSeq init k = |leftSpine Rₖ|` (= the `k`-th access cost). -/
private def sSeq (init : BinaryTree) (k : Nat) : Nat :=
  (leftSpine (rightSubtree (seqTree init k))).length

/-- Entrant count of the process: `eSeq init k = |leftSpine (minCargo Rₖ)|`. -/
private def eSeq (init : BinaryTree) (k : Nat) : Nat :=
  (leftSpine (minCargo (rightSubtree (seqTree init k)))).length

/-- **Per-step halving on the actual process**: for `1 ≤ k < n`,
`2·sSeq (k+1) ≤ sSeq k + 1 + 2·eSeq k`. -/
private theorem sSeq_halving (init : BinaryTree) (hbst : IsBST init)
    {n : Nat} (hkeys : ∀ m : Nat, m < n → m ∈ init.toKeyList)
    (k : Nat) (hk1 : 1 ≤ k) (hkn : k < n) :
    2 * sSeq init (k + 1) ≤ sSeq init k + 1 + 2 * eSeq init k := by
  have hroot : rootKey (seqTree init k) = some (k - 1) := by
    have h := seqTree_rootKey init hbst hkeys (k - 1) (by omega)
    rwa [Nat.sub_add_cancel hk1] at h
  obtain ⟨L, R, heq⟩ : ∃ L R, seqTree init k = .node L (k - 1) R := by
    cases hh : seqTree init k with
    | empty => rw [hh] at hroot; simp [rootKey] at hroot
    | node a b c =>
        rw [hh] at hroot; simp only [rootKey, Option.some.injEq] at hroot
        exact ⟨a, c, by rw [hroot]⟩
  have hbstk : IsBST (BinaryTree.node L (k - 1) R) := heq ▸ seqTree_isBST init hbst k
  have hmemiff : ∀ x, x ∈ R.toKeyList ↔ (k - 1 < x ∧ x ∈ init.toKeyList) := by
    intro x
    have h := rightSubtree_seqTree_succ_mem_iff init hbst hkeys (k - 1) (by omega) x
    rw [Nat.sub_add_cancel hk1, heq] at h
    simpa [rightSubtree] using h
  have hkR : k ∈ R.toKeyList := (hmemiff k).mpr ⟨by omega, hkeys k hkn⟩
  have hkminR : ∀ y ∈ R.toKeyList, k ≤ y := fun y hy => by
    have := (hmemiff y).mp hy; omega
  have hhalv := real_halving L R (k - 1) k hbstk (by omega) hkR hkminR
  have hs1 : sSeq init (k + 1)
      = (leftSpine (rightSubtree (splay (BinaryTree.node L (k - 1) R) k))).length := by
    unfold sSeq
    rw [show seqTree init (k + 1) = splay (seqTree init k) k from rfl, heq]
  have hs0 : sSeq init k = (leftSpine R).length := by
    unfold sSeq; rw [heq]; simp [rightSubtree]
  have he0 : eSeq init k = (leftSpine (minCargo R)).length := by
    unfold eSeq; rw [heq]; simp [rightSubtree]
  rw [hs1, hs0, he0]
  exact hhalv


/-- Arithmetic unrolling of the halving recurrence: if `2·u(k+1) ≤ u k + 1 + 2·e k` on
`[1, n)`, then `∑_{k∈[1,n)} u k ≤ 2·u 1 + (n-1) + 2·∑_{k∈[1,n)} e k`. -/
private theorem sum_halving_unroll (u e : Nat → Nat) (n : Nat) (hn : 1 ≤ n)
    (hrec : ∀ k, 1 ≤ k → k < n → 2 * u (k + 1) ≤ u k + 1 + 2 * e k) :
    ∑ k ∈ Finset.Ico 1 n, u k ≤ 2 * u 1 + (n - 1) + 2 * ∑ k ∈ Finset.Ico 1 n, e k := by
  have key : ∀ N, 1 ≤ N → N ≤ n →
      (∑ k ∈ Finset.Ico 1 N, u k) + 2 * u N
        ≤ 2 * u 1 + (∑ k ∈ Finset.Ico 1 N, (1 + 2 * e k)) := by
    intro N
    induction N with
    | zero => omega
    | succ N ih =>
        intro _ hNn
        rcases Nat.eq_or_lt_of_le (show 1 ≤ N + 1 by omega) with h1 | h1
        · -- N + 1 = 1, i.e. N = 0: empty sum
          have hN0 : N = 0 := by omega
          subst hN0
          simp
        · -- N ≥ 1: extend by one step
          have hN1 : 1 ≤ N := by omega
          have hNn' : N ≤ n := by omega
          have hstep := hrec N hN1 (by omega)
          have hIH := ih hN1 hNn'
          rw [Finset.sum_Ico_succ_top hN1, Finset.sum_Ico_succ_top hN1]
          omega
  have h := key n hn le_rfl
  have hsum : ∑ k ∈ Finset.Ico 1 n, (1 + 2 * e k)
      = (n - 1) + 2 * ∑ k ∈ Finset.Ico 1 n, e k := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, Finset.mul_sum]
    simp
  omega


/-- **MASTER REDUCTION**: the full sequential-access cost is linear *plus twice the total
entrant count*. `sequence_cost init (one_to_n n) ≤ 4n + 2E` with
`E = ∑_{k∈[1,n)} |leftSpine (minCargo Rₖ)|`. The 50-pt challenge `Splay.sequential` is hereby
machine-reduced to the single combinatorial bound `E ≤ C·n`. -/
private theorem sequence_cost_le_four_n_add_two_entries (init : BinaryTree)
    (hbst : IsBST init) {n : Nat} (hn : 1 ≤ n) (hnum : init.num_nodes = n)
    (hkeys : ∀ m : Nat, m < n → m ∈ init.toKeyList) :
    splay.sequence_cost init (one_to_n n)
      ≤ 4 * n + 2 * ((∑ k ∈ Finset.Ico 1 n, eSeq init k : ℕ) : ℝ) := by
  rw [sequence_cost_eq_sum]
  have hn0 : 0 < n := hn
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hn0]
  -- head term: the very first access costs at most n
  have hhead : splay.cost (seqTree init 0) 0 ≤ (n : ℝ) := by
    have h1 := splay_cost_le_search_path_len (seqTree init 0) 0
    have h2 := search_path_len_le_num_nodes (seqTree init 0) 0
    have h3 : (seqTree init 0).num_nodes = n := by
      rw [seqTree_num_nodes]; exact hnum
    rw [h3] at h2
    calc splay.cost (seqTree init 0) 0 ≤ ((seqTree init 0).search_path_len 0 : ℝ) := h1
      _ ≤ (n : ℝ) := by exact_mod_cast h2
  -- tail terms: cost equals the spine length, then unroll the halving
  have htail : ∑ k ∈ Finset.Ico 1 n, splay.cost (seqTree init k) k
      = ((∑ k ∈ Finset.Ico 1 n, sSeq init k : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [Finset.mem_Ico] at hk
    exact splay_cost_seqTree_eq_leftSpine_length init hbst hkeys k hk.1 hk.2
  have hunroll : ∑ k ∈ Finset.Ico 1 n, sSeq init k
      ≤ 2 * sSeq init 1 + (n - 1) + 2 * ∑ k ∈ Finset.Ico 1 n, eSeq init k :=
    sum_halving_unroll (sSeq init) (eSeq init) n hn
      (fun k hk1 hkn => sSeq_halving init hbst hkeys k hk1 hkn)
  have hs1 : sSeq init 1 ≤ n := by
    unfold sSeq
    have h1 := leftSpine_length_le_num_nodes (rightSubtree (seqTree init 1))
    have h2 := rightSubtree_num_nodes_le (seqTree init 1)
    have h3 : (seqTree init 1).num_nodes = n := by rw [seqTree_num_nodes]; exact hnum
    omega
  have hsum_le : (∑ k ∈ Finset.Ico 1 n, sSeq init k)
      ≤ 3 * n + 2 * ∑ k ∈ Finset.Ico 1 n, eSeq init k := by omega
  rw [htail]
  have hcast : ((∑ k ∈ Finset.Ico 1 n, sSeq init k : ℕ) : ℝ)
      ≤ ((3 * n + 2 * ∑ k ∈ Finset.Ico 1 n, eSeq init k : ℕ) : ℝ) := by
    exact_mod_cast hsum_le
  push_cast at hcast ⊢
  linarith


/-! ### The credit machine (Elmasry accounting, repo-variant) — foundations

Validated spec (empirical, zero violations): touched = ever-on-spine; black = ever-on-
`rightSpine Rₖ`; `g x` = #touched on `rightSpine` (subtree at `x`); `h x` = #touched on
`rightSpine` (left child of `x`). Lemma 1 (`g − h ≥ 0` for touched non-black), the once-per-node
A-link property, and the strengthened monotonicity `v_z' ≥ v_z + v_w` all hold exactly. Below:
the state defs and the per-level link relations (Elmasry (1)/(3)/(4)) for the proven zig-zig
restructuring `node (node ll lk lr) k r ↦ node M lk (node lr k r)`. -/

/-- Number of touched keys along a chain (the `g`/`h` counting primitive). -/
private def touchedCount (T : List Nat) (c : List Nat) : Nat :=
  (c.filter (· ∈ T)).length

private theorem touchedCount_cons_of_mem (T : List Nat) {x : Nat} (c : List Nat)
    (hx : x ∈ T) : touchedCount T (x :: c) = touchedCount T c + 1 := by
  simp [touchedCount, List.filter_cons, hx]

private theorem touchedCount_cons_of_not_mem (T : List Nat) {x : Nat} (c : List Nat)
    (hx : x ∉ T) : touchedCount T (x :: c) = touchedCount T c := by
  simp [touchedCount, List.filter_cons, hx]

/-- The cumulative touched set: all keys that have appeared on a splaying spine by step `k`.
(Elmasry's yellow∪green∪black, as a process state.) Accumulation starts at step 1: the actual
splaying spine at step `k ≥ 1` is `leftSpine Rₖ` (the access of `k` descends through the root
into `Rₖ`'s left spine); `leftSpine R₀` is *not* an access path (step 0 descends the left side),
and including it breaks `touchedClosed` (verified by counterexample). -/
private def touchedKeys (init : BinaryTree) : Nat → List Nat
  | 0 => []
  | k + 1 => touchedKeys init k ++ leftSpine (rightSubtree (seqTree init (k + 1)))

/-- Spine members are touched (from step 1 on). -/
private theorem spine_subset_touchedKeys (init : BinaryTree) (k : Nat) (hk : 1 ≤ k) :
    ∀ x ∈ leftSpine (rightSubtree (seqTree init k)), x ∈ touchedKeys init k := by
  cases k with
  | zero => omega
  | succ k => intro x hx; unfold touchedKeys; exact List.mem_append_right _ hx

/-- The touched set only grows. -/
private theorem touchedKeys_mono (init : BinaryTree) (k : Nat) :
    ∀ x ∈ touchedKeys init k, x ∈ touchedKeys init (k + 1) := by
  intro x hx
  unfold touchedKeys
  exact List.mem_append_left _ hx

/-- **Relation (1)** (definitional in these coordinates): the dropped parent `k`'s h-chain *is*
the survivor `lk`'s g-chain — `w`'s left child is exactly the subtree rooted at `z`. So
`h_w = g_z` holds by `rfl`; we record the chain shape. -/
private theorem rightSpine_node_eq (ll lr : BinaryTree) (lk : Nat) :
    rightSpine (BinaryTree.node ll lk lr) = lk :: rightSpine lr := rfl

/-- **Relation (3)** at one zig-zig link: the dropped parent's h-count decreases by exactly one
(its left child changes from the survivor's subtree `node ll lk lr` to the survivor's old cargo
`lr`, and the survivor `lk` is touched). -/
private theorem relation3_zigzig (T : List Nat) (ll lr : BinaryTree) (lk : Nat)
    (hlk : lk ∈ T) :
    touchedCount T (rightSpine (BinaryTree.node ll lk lr))
      = touchedCount T (rightSpine lr) + 1 := by
  rw [rightSpine_node_eq]
  exact touchedCount_cons_of_mem T _ hlk

/-- **Relation (4)** at one zig-zig link: the survivor's g-count after the link equals the
dropped parent's g-count before it, plus one (the survivor `lk`, touched, now heads the chain
`lk :: k :: rightSpine r`, while the parent's old chain was `k :: rightSpine r`; the parent's
left subtree is irrelevant to either count). -/
private theorem relation4_zigzig (T : List Nat) (M lr r l : BinaryTree) (lk k : Nat)
    (hlk : lk ∈ T) :
    touchedCount T (rightSpine (BinaryTree.node M lk (BinaryTree.node lr k r)))
      = touchedCount T (rightSpine (BinaryTree.node l k r)) + 1 := by
  rw [rightSpine_node_eq, rightSpine_node_eq, rightSpine_node_eq]
  exact touchedCount_cons_of_mem T _ hlk


/-! ### F6: cost = 2·links + O(1) — the links formulation

Each zig-zig/zig-zag level of a splay is one *link* (Elmasry's credit-counted event) and costs
exactly 2; terminal zigs cost 1 with no link. So per splay `cost ≤ 2·links + 1`, and the whole
challenge reduces to bounding total links. -/

/-- Number of double-rotation links in one splay (mirrors the `splay.cost` recursion). -/
private def splayLinks : BinaryTree → Nat → Nat
  | .empty, _ => 0
  | .node l k r, q =>
    if q = k then 0
    else if q < k then
      match l with
      | .empty => 0
      | .node ll lk lr =>
        if q < lk then
          match ll with
          | .empty => 0
          | _ => splayLinks ll q + 1
        else if lk < q then
          match lr with
          | .empty => 0
          | _ => splayLinks lr q + 1
        else 0
    else
      match r with
      | .empty => 0
      | .node rl rk rr =>
        if q < rk then
          match rl with
          | .empty => 0
          | _ => splayLinks rl q + 1
        else if rk < q then
          match rr with
          | .empty => 0
          | _ => splayLinks rr q + 1
        else 0

/-- Per-splay: the rotation cost is at most twice the link count plus one. -/
private theorem splay_cost_le_two_mul_splayLinks_add_one :
    ∀ (t : BinaryTree) (q : Nat), splay.cost t q ≤ 2 * (splayLinks t q : ℝ) + 1
  | .empty, q => by simp [splay.cost, splayLinks]
  | .node l k r, q => by
      rw [splay.cost.eq_def, splayLinks.eq_def]
      by_cases hqk : q = k
      · simp [hqk]
      · by_cases hlt : q < k
        · cases l with
          | empty => simp [hqk, hlt]
          | node ll lk lr =>
              by_cases hqlk : q < lk
              · cases ll with
                | empty => simp [hqk, hlt, hqlk]
                | node a b c =>
                    have ih := splay_cost_le_two_mul_splayLinks_add_one
                      (BinaryTree.node a b c) q
                    simp only [hqk, hlt, hqlk, if_neg, if_pos, if_true, if_false]
                    push_cast
                    linarith
              · by_cases hlkq : lk < q
                · cases lr with
                  | empty => simp [hqk, hlt, hqlk, hlkq]
                  | node a b c =>
                      have ih := splay_cost_le_two_mul_splayLinks_add_one
                        (BinaryTree.node a b c) q
                      simp only [hqk, hlt, hqlk, hlkq, if_neg, if_pos, if_true, if_false]
                      push_cast
                      linarith
                · simp [hqk, hlt, hqlk, hlkq]
        · cases r with
          | empty => simp [hqk, hlt]
          | node rl rk rr =>
              by_cases hqrk : q < rk
              · cases rl with
                | empty => simp [hqk, hlt, hqrk]
                | node a b c =>
                    have ih := splay_cost_le_two_mul_splayLinks_add_one
                      (BinaryTree.node a b c) q
                    simp only [hqk, hlt, hqrk, if_neg, if_pos, if_true, if_false]
                    push_cast
                    linarith
              · by_cases hrkq : rk < q
                · cases rr with
                  | empty => simp [hqk, hlt, hqrk, hrkq]
                  | node a b c =>
                      have ih := splay_cost_le_two_mul_splayLinks_add_one
                        (BinaryTree.node a b c) q
                      simp only [hqk, hlt, hqrk, hrkq, if_neg, if_pos, if_true, if_false]
                      push_cast
                      linarith
                · simp [hqk, hlt, hqrk, hrkq]

/-- **F6 (sequence level)**: total cost ≤ 2·(total links) + n. Combined with the master
reduction targets, the challenge is now: `totalLinks ≤ C·n`. -/
private theorem sequence_cost_le_two_mul_links_add_n (init : BinaryTree) (n : Nat) :
    splay.sequence_cost init (one_to_n n)
      ≤ 2 * ((∑ k ∈ Finset.range n, splayLinks (seqTree init k) k : ℕ) : ℝ) + n := by
  rw [sequence_cost_eq_sum]
  have hterm : ∀ k ∈ Finset.range n,
      splay.cost (seqTree init k) k ≤ 2 * (splayLinks (seqTree init k) k : ℝ) + 1 :=
    fun k _ => splay_cost_le_two_mul_splayLinks_add_one (seqTree init k) k
  calc ∑ k ∈ Finset.range n, splay.cost (seqTree init k) k
      ≤ ∑ k ∈ Finset.range n, (2 * (splayLinks (seqTree init k) k : ℝ) + 1) :=
        Finset.sum_le_sum hterm
    _ = 2 * ((∑ k ∈ Finset.range n, splayLinks (seqTree init k) k : ℕ) : ℝ) + n := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum]
        push_cast
        ring


/-! ### F1 foundations: the credit potential and relation (5) -/

/-- The credit potential (doubled, so it stays in `ℕ`): `Σ_x h_x²` where `h_x` = touched count
on the right spine of `x`'s left child. Initially zero (nothing touched). -/
private def hSqPotential (T : List Nat) : BinaryTree → Nat
  | .empty => 0
  | .node l _ r =>
      (touchedCount T (rightSpine l)) ^ 2 + hSqPotential T l + hSqPotential T r

/-- Per-link potential arithmetic (the B-link payment): if the survivor's h rises by one and the
dropped parent's h falls by one, the doubled potential changes by exactly `2(h_z − h_w + 1)`. -/
private theorem hsq_pair_change (hz hw : Nat) (hw1 : 1 ≤ hw) :
    (hz + 1) ^ 2 + (hw - 1) ^ 2 + 2 * hw = hz ^ 2 + hw ^ 2 + 2 * hz + 2 := by
  obtain ⟨w, rfl⟩ : ∃ w, hw = w + 1 := ⟨hw - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

/-- **Relation (5)** (the survivor's new h-chain): after a min-splay, the touched count on the
right spine of the result's right subtree grows by at most one. Applied to the subtree `ll`
below a survivor `z`, this is exactly Elmasry's `h_z(t+1) ≤ h_z(t) + 1`: the survivor's new left
child is `rightSubtree (splay ll q)`, its old one was `ll`. Non-recursive: the three min-splay
shapes give `= +1` (zig-zig), `= 0` (zig), `= −1` (root, the x₂-exception). -/
private theorem relation5_touchedCount_rightSpine_splay_min (T : List Nat) :
    ∀ (t : BinaryTree) (q : Nat), IsBST t → q ∈ t.toKeyList →
      (∀ y ∈ t.toKeyList, q ≤ y) →
      (∀ x ∈ leftSpine t, x ∈ T) →
      touchedCount T (rightSpine (rightSubtree (splay t q)))
        ≤ touchedCount T (rightSpine t) + 1
  | .empty, q, _, hmem, _, _ => by simp only [BinaryTree.toKeyList, List.not_mem_nil] at hmem
  | .node l k r, q, hbst, hmem, hmin, hT => by
      rcases eq_or_ne q k with hqk | hqk
      · -- root case: result right subtree is `r`; old chain was `q :: rightSpine r`
        subst hqk
        have hleq : l = .empty := by
          cases l with
          | empty => rfl
          | node la lx lb =>
              exfalso
              have hlx_lt : lx < q := by
                cases hbst with
                | node _ _ _ hfl _ _ _ =>
                    exact (forallTree_iff_forall_mem.mp hfl) lx (by simp [BinaryTree.toKeyList])
              have := hmin lx (by simp [BinaryTree.toKeyList])
              omega
        subst hleq
        have hsp : splay (BinaryTree.node .empty q r) q = BinaryTree.node .empty q r := by
          simp only [splay.eq_def, ↓reduceIte]
        rw [hsp]
        simp only [rightSubtree, rightSpine_node_eq]
        by_cases hq : q ∈ T
        · rw [touchedCount_cons_of_mem T _ hq]; omega
        · rw [touchedCount_cons_of_not_mem T _ hq]; omega
      · have hkmem : k ∈ (BinaryTree.node l k r).toKeyList := by simp [BinaryTree.toKeyList]
        have hqlt : q < k := lt_of_le_of_ne (hmin k hkmem) hqk
        have hql : q ∈ l.toKeyList := isBST_node_mem_left_of_lt_root hbst hmem hqlt
        have hbl : IsBST l := by cases hbst; assumption
        cases l with
        | empty => simp only [BinaryTree.toKeyList, List.not_mem_nil] at hql
        | node ll lk lr =>
            have hminl : ∀ y ∈ (BinaryTree.node ll lk lr).toKeyList, q ≤ y := by
              intro y hy
              refine hmin y ?_
              rw [BinaryTree.toKeyList]
              exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hy)))
            have hqlk : q ≤ lk := hminl lk (by simp [BinaryTree.toKeyList])
            rcases eq_or_ne q lk with hqeq | hqne
            · -- zig: result right subtree `node lr k r`; chain `k :: rightSpine r` unchanged
              subst hqeq
              have hlleq : ll = .empty := by
                cases ll with
                | empty => rfl
                | node a b c =>
                    exfalso
                    have hb_lt : b < q := by
                      cases hbl with
                      | node _ _ _ hfl _ _ _ =>
                          exact (forallTree_iff_forall_mem.mp hfl) b
                            (by simp [BinaryTree.toKeyList])
                    have := hminl b (by simp [BinaryTree.toKeyList])
                    omega
              subst hlleq
              have hnk : ¬ q = k := hqk
              have hnq : ¬ q < q := lt_irrefl q
              have hsp : splay (BinaryTree.node (.node .empty q lr) k r) q
                  = BinaryTree.node .empty q (.node lr k r) := by
                rw [splay.eq_def]
                simp only [hnk, ↓reduceIte, hqlt, lt_self_iff_false, rotate, rotateRight]
              rw [hsp]
              simp only [rightSubtree, rightSpine_node_eq]
              omega
            · -- zig-zig: result right subtree `node M lk (node lr k r)`;
              -- chain `lk :: k :: rightSpine r` vs old `k :: rightSpine r`; `lk` is touched
              have hqllt : q < lk := lt_of_le_of_ne hqlk hqne
              have hqll : q ∈ ll.toKeyList :=
                isBST_node_mem_left_of_lt_root hbl hql hqllt
              cases ll with
              | empty => simp only [BinaryTree.toKeyList, List.not_mem_nil] at hqll
              | node a b c =>
                  have hbll : IsBST (BinaryTree.node a b c) := by cases hbl; assumption
                  have hminll : ∀ y ∈ (BinaryTree.node a b c).toKeyList, q ≤ y := by
                    intro y hy
                    refine hminl y ?_
                    rw [BinaryTree.toKeyList]
                    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hy)))
                  have hS := splay_min_eq_node_empty (BinaryTree.node a b c) q hbll hqll hminll
                  have hnk : ¬ q = k := hqk
                  have hsp : splay (BinaryTree.node (.node (.node a b c) lk lr) k r) q
                      = BinaryTree.node .empty q
                          (.node (rightSubtree (splay (BinaryTree.node a b c) q)) lk
                            (.node lr k r)) := by
                    rw [splay.eq_def]
                    simp only [if_neg hnk, if_pos hqlt, if_pos hqllt]
                    rw [hS]
                    simp only [rotate, rotateRight, rightSubtree]
                  rw [hsp]
                  have hlkT : lk ∈ T := hT lk (by
                    simp only [leftSpine, List.mem_cons, true_or, or_true])
                  simp only [rightSubtree, rightSpine_node_eq]
                  rw [touchedCount_cons_of_mem T _ hlkT]


/-! ### F1 bricks: the per-level Φ-exchange (exact, invariant-free)

At one zig-zig level the potential satisfies an *exact* exchange equation: writing
`M = rightSubtree (splay ll q)`, the only h-terms that change are the dropped parent `k`'s
(`(tc (lk :: rs lr))² → (tc (rs lr))²`, i.e. `h_w → h_w − 1`) and the survivor `lk`'s
(`(tc (rs ll))² → (tc (rs M))²`, i.e. `h_z → h_z'`, with `h_z' ≤ h_z + 1` by relation (5));
everything else moves as frozen blocks. No coloring or invariants enter the equation. -/

/-- The zig-zig shape of a min-splay, extracted standalone: given the branch conditions and the
min-normal-form of the recursive call, the splay result is explicit. -/
private theorem splay_min_zigzig_shape (a c lr r : BinaryTree) (b lk k q : Nat)
    (hnk : ¬ q = k) (hqlt : q < k) (hqllt : q < lk)
    (hS : splay (BinaryTree.node a b c) q
      = BinaryTree.node .empty q (rightSubtree (splay (BinaryTree.node a b c) q))) :
    splay (BinaryTree.node (.node (.node a b c) lk lr) k r) q
      = BinaryTree.node .empty q
          (.node (rightSubtree (splay (BinaryTree.node a b c) q)) lk
            (.node lr k r)) := by
  rw [splay.eq_def]
  simp only [if_neg hnk, if_pos hqlt, if_pos hqllt]
  rw [hS]
  simp [rotate, rotateRight, rightSubtree]

/-- **Φ-exchange at one zig-zig level** (exact ℕ equation, no hypotheses on `T`): the potential
of the new right subtree differs from the old tree's by swapping the dropped parent's h-term
(`tc (lk :: rs lr)` ↦ `tc (rs lr)`) and the survivor's h-term (`tc (rs ll)` ↦ `tc (rs M)`),
where the latter swap is the recursive subproblem's contribution. -/
private theorem hSqPotential_exchange_zigzig (T : List Nat) (a c lr r : BinaryTree)
    (b lk k q : Nat)
    (hnk : ¬ q = k) (hqlt : q < k) (hqllt : q < lk)
    (hS : splay (BinaryTree.node a b c) q
      = BinaryTree.node .empty q (rightSubtree (splay (BinaryTree.node a b c) q))) :
    hSqPotential T (rightSubtree (splay (BinaryTree.node (.node (.node a b c) lk lr) k r) q))
        + (touchedCount T (lk :: rightSpine lr)) ^ 2
        + (touchedCount T (rightSpine (BinaryTree.node a b c))) ^ 2
        + hSqPotential T (BinaryTree.node a b c)
      = hSqPotential T (BinaryTree.node (.node (.node a b c) lk lr) k r)
        + (touchedCount T (rightSpine
            (rightSubtree (splay (BinaryTree.node a b c) q)))) ^ 2
        + hSqPotential T (rightSubtree (splay (BinaryTree.node a b c) q))
        + (touchedCount T (rightSpine lr)) ^ 2 := by
  rw [splay_min_zigzig_shape a c lr r b lk k q hnk hqlt hqllt hS]
  simp only [rightSubtree, hSqPotential, rightSpine_node_eq]
  ring


private theorem touchedCount_nil (T : List Nat) : touchedCount T [] = 0 := rfl

/-- Φ-exchange, root case: accessing the min at the root leaves the potential unchanged. -/
private theorem hSqPotential_exchange_root (T : List Nat) (r : BinaryTree) (q : Nat) :
    hSqPotential T (rightSubtree (splay (BinaryTree.node .empty q r) q))
      = hSqPotential T (BinaryTree.node .empty q r) := by
  have hsp : splay (BinaryTree.node .empty q r) q = BinaryTree.node .empty q r := by
    simp [splay.eq_def]
  rw [hsp]
  simp [rightSubtree, hSqPotential, rightSpine, touchedCount_nil]

/-- Φ-exchange, zig (found-at-child) case — the `x₂`-exception: the bottom survivor `k`'s
h-term swaps `tc (q :: rs lr)` ↦ `tc (rs lr)` (it absorbs the consumed min's cargo); the
min's own h-term was zero. Exact ℕ equation, no hypotheses on `T`. -/
private theorem hSqPotential_exchange_zig (T : List Nat) (lr r : BinaryTree) (k q : Nat)
    (hnk : ¬ q = k) (hqlt : q < k) :
    hSqPotential T (rightSubtree (splay (BinaryTree.node (.node .empty q lr) k r) q))
        + (touchedCount T (q :: rightSpine lr)) ^ 2
      = hSqPotential T (BinaryTree.node (.node .empty q lr) k r)
        + (touchedCount T (rightSpine lr)) ^ 2 := by
  have hnq : ¬ q < q := lt_irrefl q
  have hsp : splay (BinaryTree.node (.node .empty q lr) k r) q
      = BinaryTree.node .empty q (.node lr k r) := by
    rw [splay.eq_def]
    simp [hnk, hqlt, hnq, rotate, rotateRight]
  rw [hsp]
  simp only [rightSubtree, hSqPotential, rightSpine_node_eq]
  show (touchedCount T (rightSpine lr)) ^ 2 + hSqPotential T lr + hSqPotential T r
        + (touchedCount T (q :: rightSpine lr)) ^ 2
      = (touchedCount T (q :: rightSpine lr)) ^ 2
        + ((touchedCount T (rightSpine .empty)) ^ 2
            + hSqPotential T .empty + hSqPotential T lr)
        + hSqPotential T r + (touchedCount T (rightSpine lr)) ^ 2
  simp only [hSqPotential, rightSpine, touchedCount_nil]
  ring


/-! ### F2: Lemma 1 (the `v ≥ 0` invariant) — state and engine

Elmasry's Lemma 1 transfers, but the bare `v ≥ 0` is not inductive through *release* events:
when the consumed min's cargo chain joins the spine, the first untouched chain member gets
touched, bumping the `h` of the (touched) node directly above it — the chain's
touched/untouched boundary. The inductive strengthening: `v_x ≥ 1` whenever the head of `x`'s
h-chain is untouched (*boundary-readiness*). All events re-establish it: fresh yellowing gives
`v = 0` with a touched head (or `v = 1` with no head); a drop gives the dropped parent
`v' = v + 1 ≥ 1` (relation (3)); a survivor gets `v' ≥ v_z + v_w ≥ 0` with a touched head
(the next survivor); the base survivor gets `v' = v + 1 ≥ 1` covering an exposed cargo head;
the release event itself consumes the bit (`v ≥ 1 → v' ≥ 0`, head now touched). -/

/-- The boundary bit: `1` if the chain has an untouched head (a future `h`-bump is pending). -/
private def boundaryBit (T : List Nat) : List Nat → Nat
  | [] => 0
  | y :: _ => if y ∈ T then 0 else 1

/-- Node-level invariant: for a touched node with left subtree `l`, right subtree `r`:
`h + bit ≤ g`, i.e. `tc (rs l) + boundaryBit (rs l) ≤ 1 + tc (rs r)`. -/
private def vAt (T : List Nat) (l : BinaryTree) (k : Nat) (r : BinaryTree) : Prop :=
  k ∈ T → touchedCount T (rightSpine l) + boundaryBit T (rightSpine l)
    ≤ 1 + touchedCount T (rightSpine r)

/-- The invariant at every node of a tree. -/
private def vInvariantFull (T : List Nat) : BinaryTree → Prop
  | .empty => True
  | .node l k r => vAt T l k r ∧ vInvariantFull T l ∧ vInvariantFull T r

/-- The invariant at every *non-black* node: the root and its right chain (the blacks of this
subtree) are exempt; all left subtrees along the right chain are fully checked. -/
private def vInvariantNB (T : List Nat) : BinaryTree → Prop
  | .empty => True
  | .node l _ r => vInvariantFull T l ∧ vInvariantNB T r

/-- Untouched blocks satisfy the full invariant vacuously. -/
private theorem vInvariantFull_of_untouched (T : List Nat) :
    ∀ (t : BinaryTree), (∀ x ∈ t.toKeyList, x ∉ T) → vInvariantFull T t
  | .empty, _ => trivial
  | .node l k r, h => by
      refine ⟨fun hk => absurd hk (h k (by simp [BinaryTree.toKeyList])), ?_, ?_⟩
      · exact vInvariantFull_of_untouched T l (fun x hx =>
          h x (by simp only [BinaryTree.toKeyList, List.mem_append]; tauto))
      · exact vInvariantFull_of_untouched T r (fun x hx =>
          h x (by simp only [BinaryTree.toKeyList, List.mem_append]; tauto))

/-- **The v-jump engine** (Lemma 1(c), strengthened): at a zig-zig link with survivor `lk`
touched and relation (5) for the recursive result `M`, the survivor's new v dominates the sum
of both old v's: `v_z' ≥ v_z + v_w`. In ℕ form (`g' = tc(lk :: k :: rs r)`, `h' = tc(rs M)`,
`g_z = h_w = tc(lk :: rs lr)` by relation (1), `h_z = tc(rs ll)`, `g_w = tc(k :: rs r)`). -/
private theorem vjump_zigzig (T : List Nat) (ll M r : BinaryTree) (lk k : Nat)
    (hlk : lk ∈ T)
    (h5 : touchedCount T (rightSpine M) ≤ touchedCount T (rightSpine ll) + 1) :
    touchedCount T (rightSpine M) + touchedCount T (k :: rightSpine r)
      ≤ touchedCount T (lk :: k :: rightSpine r) + touchedCount T (rightSpine ll) := by
  rw [touchedCount_cons_of_mem T _ hlk]
  omega


/-- The boundary bit is at most one. -/
private theorem boundaryBit_le_one (T : List Nat) (c : List Nat) : boundaryBit T c ≤ 1 := by
  cases c with
  | nil => simp [boundaryBit]
  | cons y c => simp only [boundaryBit]; split <;> omega

/-- Confinement: keys newly touched at step `k+1` lie on the new splaying spine. -/
private theorem touchedKeys_succ_diff (init : BinaryTree) (k : Nat) :
    ∀ x ∈ touchedKeys init (k + 1), x ∉ touchedKeys init k →
      x ∈ leftSpine (rightSubtree (seqTree init (k + 1))) := by
  intro x hx hnx
  unfold touchedKeys at hx
  rcases List.mem_append.mp hx with h | h
  · exact absurd h hnx
  · exact h


/-! ### F2 sub-lemmas: frozen-stability and the release events (integrated from the fan-out) -/

private theorem forallTree_mem {p : Nat → Prop} {t : BinaryTree} (h : ForallTree p t) :
    ∀ x ∈ t.toKeyList, p x := forallTree_iff_forall_mem.mp h

private theorem touchedCount_mono_T (T T' : List Nat) (c : List Nat)
    (h : ∀ x ∈ T, x ∈ T') : touchedCount T c ≤ touchedCount T' c := by
  induction c with
  | nil => simp [touchedCount]
  | cons y c ih =>
    by_cases hy : y ∈ T
    · rw [touchedCount_cons_of_mem T c hy, touchedCount_cons_of_mem T' c (h y hy)]
      omega
    · rw [touchedCount_cons_of_not_mem T c hy]
      by_cases hy' : y ∈ T'
      · rw [touchedCount_cons_of_mem T' c hy']
        omega
      · rw [touchedCount_cons_of_not_mem T' c hy']
        exact ih

private theorem touchedCount_frozen (T T' : List Nat) (c : List Nat)
    (hmono : ∀ x ∈ T, x ∈ T') (hfroz : ∀ y ∈ c, y ∈ T' → y ∈ T) :
    touchedCount T' c = touchedCount T c := by
  induction c with
  | nil => simp [touchedCount]
  | cons y c ih =>
    have ih' : touchedCount T' c = touchedCount T c :=
      ih (fun z hz hz' => hfroz z (List.mem_cons_of_mem y hz) hz')
    by_cases hy : y ∈ T
    · rw [touchedCount_cons_of_mem T c hy, touchedCount_cons_of_mem T' c (hmono y hy), ih']
    · have hy' : y ∉ T' := fun h' => hy (hfroz y (List.mem_cons_self ..) h')
      rw [touchedCount_cons_of_not_mem T c hy, touchedCount_cons_of_not_mem T' c hy', ih']

private theorem boundaryBit_frozen (T T' : List Nat) (c : List Nat)
    (hmono : ∀ x ∈ T, x ∈ T') (hfroz : ∀ y ∈ c, y ∈ T' → y ∈ T) :
    boundaryBit T' c = boundaryBit T c := by
  cases c with
  | nil => rfl
  | cons y c =>
    have hiff : y ∈ T' ↔ y ∈ T :=
      ⟨fun h' => hfroz y (List.mem_cons_self ..) h', fun h => hmono y h⟩
    simp only [boundaryBit, hiff]

private theorem touchedCount_zero (T : List Nat) :
    ∀ (c : List Nat), (∀ y ∈ c, y ∉ T) → touchedCount T c = 0 := by
  intro c
  induction c with
  | nil => intro _; simp [touchedCount]
  | cons y c ih =>
      intro h
      rw [touchedCount_cons_of_not_mem T c (h y (by simp))]
      exact ih (fun z hz => h z (by simp [hz]))

private theorem rightSpine_subset_toKeyList :
    ∀ (t : BinaryTree) (x : Nat), x ∈ rightSpine t → x ∈ t.toKeyList
  | .empty, x, hx => by simp [rightSpine] at hx
  | .node l k r, x, hx => by
    simp only [rightSpine, List.mem_cons] at hx
    simp only [BinaryTree.toKeyList, List.mem_append, List.mem_singleton]
    rcases hx with rfl | hx
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr (rightSpine_subset_toKeyList r x hx)

private theorem vInvariantFull_frozen (T T' : List Nat) :
    ∀ (u : BinaryTree),
      (∀ x ∈ T, x ∈ T') →
      (∀ y ∈ u.toKeyList, y ∈ T' → y ∈ T) →
      vInvariantFull T u → vInvariantFull T' u
  | .empty => by intro _ _ _; trivial
  | .node l k r => by
    intro hsub hfrozen hinv
    simp only [vInvariantFull] at hinv ⊢
    obtain ⟨hvat, hl, hr⟩ := hinv
    have hmem_l : ∀ y ∈ l.toKeyList, y ∈ (BinaryTree.node l k r).toKeyList := by
      intro y hy
      simp only [BinaryTree.toKeyList, List.mem_append, List.mem_singleton]
      exact Or.inl (Or.inl hy)
    have hmem_r : ∀ y ∈ r.toKeyList, y ∈ (BinaryTree.node l k r).toKeyList := by
      intro y hy
      simp only [BinaryTree.toKeyList, List.mem_append, List.mem_singleton]
      exact Or.inr hy
    refine ⟨?_,
      vInvariantFull_frozen T T' l hsub (fun y hy => hfrozen y (hmem_l y hy)) hl,
      vInvariantFull_frozen T T' r hsub (fun y hy => hfrozen y (hmem_r y hy)) hr⟩
    intro hk'
    have hk_mem : k ∈ (BinaryTree.node l k r).toKeyList := by
      simp [BinaryTree.toKeyList]
    have hk : k ∈ T := hfrozen k hk_mem hk'
    have hfl : ∀ y ∈ rightSpine l, y ∈ T' → y ∈ T := fun y hy =>
      hfrozen y (hmem_l y (rightSpine_subset_toKeyList l y hy))
    have hfr : ∀ y ∈ rightSpine r, y ∈ T' → y ∈ T := fun y hy =>
      hfrozen y (hmem_r y (rightSpine_subset_toKeyList r y hy))
    rw [touchedCount_frozen T T' (rightSpine l) hsub hfl,
        boundaryBit_frozen T T' (rightSpine l) hsub hfl,
        touchedCount_frozen T T' (rightSpine r) hsub hfr]
    exact hvat hk

/-- Hereditary touch-closure (Elmasry's "the parent of a colored node is colored"):
untouched nodes have untouched subtrees. -/
private def touchedClosed (T : List Nat) : BinaryTree → Prop
  | .empty => True
  | .node l k r =>
      (k ∉ T → (∀ x ∈ l.toKeyList, x ∉ T) ∧ (∀ x ∈ r.toKeyList, x ∉ T))
      ∧ touchedClosed T l ∧ touchedClosed T r

private theorem touchedClosed_of_untouched (T : List Nat) :
    ∀ (u : BinaryTree), (∀ x ∈ u.toKeyList, x ∉ T) → touchedClosed T u := by
  intro u
  induction u with
  | empty => intro _; trivial
  | node l k r ihl ihr =>
    intro h
    have hl : ∀ x ∈ l.toKeyList, x ∉ T := fun x hx =>
      h x (by simp [BinaryTree.toKeyList, hx])
    have hr : ∀ x ∈ r.toKeyList, x ∉ T := fun x hx =>
      h x (by simp [BinaryTree.toKeyList, hx])
    exact ⟨fun _ => ⟨hl, hr⟩, ihl hl, ihr hr⟩

private theorem touchedClosed_frozen (T T' : List Nat) :
    ∀ (u : BinaryTree),
      (∀ x ∈ T, x ∈ T') →
      (∀ y ∈ u.toKeyList, y ∈ T' → y ∈ T) →
      touchedClosed T u → touchedClosed T' u := by
  intro u
  induction u with
  | empty => intro _ _ _; trivial
  | node l k r ihl ihr =>
    intro hmono hfroz hc
    obtain ⟨hk, hcl, hcr⟩ := hc
    have hfl : ∀ y ∈ l.toKeyList, y ∈ T' → y ∈ T := fun y hy =>
      hfroz y (by simp [BinaryTree.toKeyList, hy])
    have hfr : ∀ y ∈ r.toKeyList, y ∈ T' → y ∈ T := fun y hy =>
      hfroz y (by simp [BinaryTree.toKeyList, hy])
    refine ⟨?_, ihl hmono hfl hcl, ihr hmono hfr hcr⟩
    intro hk'
    have hkT : k ∉ T := fun h => hk' (hmono k h)
    obtain ⟨hlT, hrT⟩ := hk hkT
    exact ⟨fun x hx hxT' => hlT x hx (hfl x hx hxT'),
           fun x hx hxT' => hrT x hx (hfr x hx hxT')⟩

/-- **Release event, v-invariant** (the heart of F2): when the consumed min's cargo joins the
spine — all its left-spine keys newly touched, everything else frozen — the full invariant is
re-established. The boundary bit pays for the touched/untouched boundary exactly. -/
private theorem vInvariantFull_release (T T' : List Nat) :
    ∀ (u : BinaryTree),
      IsBST u →
      vInvariantFull T u →
      touchedClosed T u →
      (∀ x ∈ T, x ∈ T') →
      (∀ x ∈ leftSpine u, x ∈ T') →
      (∀ x, x ∈ u.toKeyList → x ∈ T' → x ∉ T → x ∈ leftSpine u) →
      vInvariantFull T' u := by
  intro u
  induction u with
  | empty =>
      intro _ _ _ _ _ _
      simp only [vInvariantFull]
  | node l k r ihl ihr =>
      intro hbst hv htc hTT' hls hconf
      have hfl : ForallTree (fun x => x < k) l := by cases hbst; assumption
      have hfr : ForallTree (fun x => k < x) r := by cases hbst; assumption
      have hbl : IsBST l := by cases hbst; assumption
      have hbr : IsBST r := by cases hbst; assumption
      have hkl : ∀ x ∈ l.toKeyList, x < k := forallTree_mem hfl
      have hkr : ∀ x ∈ r.toKeyList, k < x := forallTree_mem hfr
      have hknl : k ∉ l.toKeyList := fun h => absurd (hkl k h) (lt_irrefl k)
      simp only [vInvariantFull] at hv
      obtain ⟨hvAt, hvl, hvr⟩ := hv
      simp only [touchedClosed] at htc
      obtain ⟨hclose, htcl, htcr⟩ := htc
      have hr_not_ls : ∀ y ∈ r.toKeyList, y ∉ leftSpine (BinaryTree.node l k r) := by
        intro y hy hyls
        have h1 : k < y := hkr y hy
        simp only [leftSpine, List.mem_cons] at hyls
        rcases hyls with h | h
        · omega
        · have h2 : y < k := hkl y (leftSpine_subset_toKeyList l y h)
          omega
      have hr_frozen_keys : ∀ y ∈ r.toKeyList, y ∈ T' → y ∈ T := by
        intro y hy hyT'
        by_contra hyT
        exact hr_not_ls y hy
          (hconf y (by simp [BinaryTree.toKeyList, hy]) hyT' hyT)
      have hvr' : vInvariantFull T' r :=
        vInvariantFull_frozen T T' r hTT' hr_frozen_keys hvr
      have hlsl : ∀ x ∈ leftSpine l, x ∈ T' := by
        intro x hx
        exact hls x (by simp [leftSpine, hx])
      have hconfl : ∀ x, x ∈ l.toKeyList → x ∈ T' → x ∉ T → x ∈ leftSpine l := by
        intro x hx hxT' hxT
        have hxls := hconf x (by simp [BinaryTree.toKeyList, hx]) hxT' hxT
        simp only [leftSpine, List.mem_cons] at hxls
        rcases hxls with h | h
        · subst h; exact absurd hx hknl
        · exact h
      have hvl' : vInvariantFull T' l := ihl hbl hvl htcl hTT' hlsl hconfl
      have hr_chain : ∀ y ∈ rightSpine r, y ∈ T' → y ∈ T := fun y hy =>
        hr_frozen_keys y (rightSpine_subset_toKeyList r y hy)
      have hrEq : touchedCount T' (rightSpine r) = touchedCount T (rightSpine r) :=
        touchedCount_frozen T T' _ hTT' hr_chain
      have hvAt' : vAt T' l k r := by
        intro _
        cases l with
        | empty =>
            simp only [rightSpine, touchedCount, boundaryBit, List.filter_nil,
              List.length_nil]
            omega
        | node ll lk lr =>
            have hlkT' : lk ∈ T' := hls lk (by simp [leftSpine])
            have hfll : ForallTree (fun x => x < lk) ll := by cases hbl; assumption
            have hflr : ForallTree (fun x => lk < x) lr := by cases hbl; assumption
            have hlr_not_ls : ∀ y ∈ lr.toKeyList,
                y ∉ leftSpine (BinaryTree.node (BinaryTree.node ll lk lr) k r) := by
              intro y hy hyls
              have h1 : lk < y := forallTree_mem hflr y hy
              have h2 : y < k := hkl y (by simp [BinaryTree.toKeyList, hy])
              simp only [leftSpine, List.mem_cons] at hyls
              rcases hyls with h | h | h
              · omega
              · omega
              · have h3 : y < lk :=
                  forallTree_mem hfll y (leftSpine_subset_toKeyList ll y h)
                omega
            have hlr_frozen : ∀ y ∈ rightSpine lr, y ∈ T' → y ∈ T := by
              intro y hy hyT'
              by_contra hyT
              have hyk : y ∈ lr.toKeyList := rightSpine_subset_toKeyList lr y hy
              exact hlr_not_ls y hyk
                (hconf y (by simp [BinaryTree.toKeyList, hyk]) hyT' hyT)
            have hlrEq : touchedCount T' (rightSpine lr)
                = touchedCount T (rightSpine lr) :=
              touchedCount_frozen T T' _ hTT' hlr_frozen
            have h1 : touchedCount T' (lk :: rightSpine lr)
                = touchedCount T' (rightSpine lr) + 1 :=
              touchedCount_cons_of_mem T' (rightSpine lr) hlkT'
            have h2 : boundaryBit T' (lk :: rightSpine lr) = 0 := by
              simp [boundaryBit, hlkT']
            simp only [rightSpine]
            by_cases hkT : k ∈ T
            · have hold := hvAt hkT
              simp only [rightSpine] at hold
              by_cases hlkT : lk ∈ T
              · have h3 := touchedCount_cons_of_mem T (rightSpine lr) hlkT
                have h4 : boundaryBit T (lk :: rightSpine lr) = 0 := by
                  simp [boundaryBit, hlkT]
                omega
              · have h3 := touchedCount_cons_of_not_mem T (rightSpine lr) hlkT
                have h4 : boundaryBit T (lk :: rightSpine lr) = 1 := by
                  simp [boundaryBit, hlkT]
                omega
            · obtain ⟨hlnot, hrnot⟩ := hclose hkT
              have hz1 : touchedCount T (rightSpine lr) = 0 := by
                apply touchedCount_zero
                intro y hy
                apply hlnot
                have hyk : y ∈ lr.toKeyList := rightSpine_subset_toKeyList lr y hy
                simp [BinaryTree.toKeyList, hyk]
              have hz2 : touchedCount T (rightSpine r) = 0 := by
                apply touchedCount_zero
                intro y hy
                exact hrnot y (rightSpine_subset_toKeyList r y hy)
              omega
      simp only [vInvariantFull]
      exact ⟨hvAt', hvl', hvr'⟩

/-- **Release event, touch-closure**: `touchedClosed` survives the release. -/
private theorem touchedClosed_release (T T' : List Nat) :
    ∀ (u : BinaryTree),
      IsBST u →
      touchedClosed T u →
      (∀ x ∈ T, x ∈ T') →
      (∀ x ∈ leftSpine u, x ∈ T') →
      (∀ x, x ∈ u.toKeyList → x ∈ T' → x ∉ T → x ∈ leftSpine u) →
      touchedClosed T' u := by
  intro u
  induction u with
  | empty => intro _ _ _ _ _; trivial
  | node l k r ihl _ =>
      intro hbst htc hTT' hspine hconf
      cases hbst with
      | node _ _ _ hlk hrk hbl hbr =>
        obtain ⟨_, hl, hr⟩ := htc
        have hkT' : k ∈ T' := hspine k (by simp [leftSpine])
        refine ⟨?_, ?_, ?_⟩
        · intro hk'
          exact absurd hkT' hk'
        · refine ihl hbl hl hTT' ?_ ?_
          · intro x hx
            exact hspine x (by simp [leftSpine, List.mem_cons]; exact Or.inr hx)
          · intro x hxl hxT' hxT
            have hxu : x ∈ (BinaryTree.node l k r).toKeyList := by
              simp only [BinaryTree.toKeyList, List.mem_append, List.mem_singleton]
              exact Or.inl (Or.inl hxl)
            have hxs : x ∈ leftSpine (BinaryTree.node l k r) := hconf x hxu hxT' hxT
            simp only [leftSpine, List.mem_cons] at hxs
            rcases hxs with hxk | hxs
            · have hlt : x < k := forallTree_mem hlk x hxl
              omega
            · exact hxs
        · refine touchedClosed_frozen T T' r hTT' ?_ hr
          intro y hyr hyT'
          by_contra hyT
          have hyu : y ∈ (BinaryTree.node l k r).toKeyList := by
            simp only [BinaryTree.toKeyList, List.mem_append, List.mem_singleton]
            exact Or.inr hyr
          have hys : y ∈ leftSpine (BinaryTree.node l k r) := hconf y hyu hyT' hyT
          have hky : k < y := forallTree_mem hrk y hyr
          simp only [leftSpine, List.mem_cons] at hys
          rcases hys with hyk | hys
          · omega
          · have hyl : y ∈ l.toKeyList := leftSpine_subset_toKeyList l y hys
            have hlt : y < k := forallTree_mem hlk y hyl
            omega


/-- **Per-splay preservation, zig case** (the `x₂`-exception step): at the bottom of the splay,
`t = node (node empty q lr) k r` restructures to `node lr k r` — the base survivor `k` absorbs
the consumed min `q`'s cargo `lr`, whose left spine is released onto the new spine
`k :: leftSpine lr`. The invariant transfers: `lr` by the release lemma, `r` frozen, and the
base survivor's `vAt` follows from its old `vAt` (whose chain `q :: rightSpine lr` loses the
touched `q` — exactly compensating the newly-touched head of `rightSpine lr`). -/
private theorem vInv_preserved_zig (T T' : List Nat) (lr r : BinaryTree) (k q : Nat)
    (hbst : IsBST (BinaryTree.node (.node .empty q lr) k r))
    (hfullT : vInvariantFull T (BinaryTree.node (.node .empty q lr) k r))
    (hclosedT : touchedClosed T (BinaryTree.node (.node .empty q lr) k r))
    (hmono : ∀ x ∈ T, x ∈ T')
    (hkT : k ∈ T) (hqT : q ∈ T)
    (hnew : ∀ x ∈ leftSpine (BinaryTree.node lr k r), x ∈ T')
    (hconf : ∀ x, x ∈ (BinaryTree.node (.node .empty q lr) k r).toKeyList →
      x ∈ T' → x ∉ T → x ∈ leftSpine (BinaryTree.node lr k r)) :
    vInvariantFull T' (BinaryTree.node lr k r) := by
  -- BST facts
  have hfl : ForallTree (fun x => x < k) (BinaryTree.node .empty q lr) := by
    cases hbst; assumption
  have hfr : ForallTree (fun x => k < x) r := by cases hbst; assumption
  have hbl : IsBST (BinaryTree.node .empty q lr) := by cases hbst; assumption
  have hbr : IsBST r := by cases hbst; assumption
  have hflr : ForallTree (fun x => q < x) lr := by cases hbl; assumption
  have hblr : IsBST lr := by cases hbl; assumption
  have hlr_lt_k : ∀ x ∈ lr.toKeyList, x < k := fun x hx =>
    forallTree_mem hfl x (by simp [BinaryTree.toKeyList, hx])
  have hlr_gt_q : ∀ x ∈ lr.toKeyList, q < x := forallTree_mem hflr
  have hr_gt_k : ∀ x ∈ r.toKeyList, k < x := forallTree_mem hfr
  -- old invariants destructured
  obtain ⟨hvAtk, hfullL, hfullR⟩ := hfullT
  obtain ⟨hvAtq, _, hfullLr⟩ := hfullL
  obtain ⟨_, hclosedL, hclosedR⟩ := hclosedT
  obtain ⟨_, _, hclosedLr⟩ := hclosedL
  -- membership plumbing into the big tree's key list
  have hmem_lr : ∀ x ∈ lr.toKeyList,
      x ∈ (BinaryTree.node (.node .empty q lr) k r).toKeyList := by
    intro x hx
    rw [BinaryTree.toKeyList, BinaryTree.toKeyList]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
      (Or.inl (List.mem_append.mpr (Or.inr hx)))))
  have hmem_r : ∀ x ∈ r.toKeyList,
      x ∈ (BinaryTree.node (.node .empty q lr) k r).toKeyList := by
    intro x hx
    rw [BinaryTree.toKeyList]
    exact List.mem_append.mpr (Or.inr hx)
  -- 1. the released cargo lr
  have hfullLr' : vInvariantFull T' lr := by
    refine vInvariantFull_release T T' lr hblr hfullLr hclosedLr hmono ?_ ?_
    · intro x hx
      exact hnew x (by rw [leftSpine]; exact List.mem_cons_of_mem k hx)
    · intro x hx hxT' hxT
      have hxs := hconf x (hmem_lr x hx) hxT' hxT
      simp only [leftSpine, List.mem_cons] at hxs
      rcases hxs with rfl | hxs
      · exact absurd (hlr_lt_k x hx) (lt_irrefl x)
      · exact hxs
  -- 2. the frozen cargo r
  have hr_frozen : ∀ y ∈ r.toKeyList, y ∈ T' → y ∈ T := by
    intro y hy hyT'
    by_contra hyT
    have hys := hconf y (hmem_r y hy) hyT' hyT
    have hky : k < y := hr_gt_k y hy
    simp only [leftSpine, List.mem_cons] at hys
    rcases hys with rfl | hys
    · omega
    · have : y < k := hlr_lt_k y (leftSpine_subset_toKeyList lr y hys)
      omega
  have hfullR' : vInvariantFull T' r := vInvariantFull_frozen T T' r hmono hr_frozen hfullR
  -- 3. the base survivor's vAt
  have hrEq : touchedCount T' (rightSpine r) = touchedCount T (rightSpine r) :=
    touchedCount_frozen T T' _ hmono (fun y hy =>
      hr_frozen y (rightSpine_subset_toKeyList r y hy))
  have hvAt' : vAt T' lr k r := by
    intro _
    cases lr with
    | empty =>
        simp only [rightSpine, touchedCount, boundaryBit, List.filter_nil, List.length_nil]
        omega
    | node a b c =>
        have hbT' : b ∈ T' := hnew b (by simp [leftSpine])
        have hfab : ForallTree (fun x => x < b) a := by cases hblr; assumption
        have hfcb : ForallTree (fun x => b < x) c := by cases hblr; assumption
        have hc_frozen : ∀ y ∈ rightSpine c, y ∈ T' → y ∈ T := by
          intro y hy hyT'
          by_contra hyT
          have hyc : y ∈ c.toKeyList := rightSpine_subset_toKeyList c y hy
          have hyb : b < y := forallTree_mem hfcb y hyc
          have hylr : y ∈ (BinaryTree.node a b c).toKeyList := by
            rw [BinaryTree.toKeyList]; exact List.mem_append.mpr (Or.inr hyc)
          have hys := hconf y (hmem_lr y hylr) hyT' hyT
          simp only [leftSpine, List.mem_cons] at hys
          rcases hys with rfl | rfl | hys
          · exact absurd (hlr_lt_k y hylr) (lt_irrefl y)
          · omega
          · have : y < b := forallTree_mem hfab y (leftSpine_subset_toKeyList a y hys)
            omega
        have hcEq : touchedCount T' (rightSpine c) = touchedCount T (rightSpine c) :=
          touchedCount_frozen T T' _ hmono hc_frozen
        have h1 : touchedCount T' (b :: rightSpine c)
            = touchedCount T' (rightSpine c) + 1 :=
          touchedCount_cons_of_mem T' (rightSpine c) hbT'
        have h2 : boundaryBit T' (b :: rightSpine c) = 0 := by
          simp only [boundaryBit, hbT', ↓reduceIte]
        -- old vAt of k: chain q :: b :: rightSpine c
        have hold := hvAtk hkT
        simp only [rightSpine] at hold
        rw [touchedCount_cons_of_mem T _ hqT] at hold
        have h3 : boundaryBit T (q :: b :: rightSpine c) = 0 := by
          simp only [boundaryBit, hqT, ↓reduceIte]
        rw [h3] at hold
        simp only [rightSpine]
        by_cases hbT : b ∈ T
        · rw [touchedCount_cons_of_mem T _ hbT] at hold
          omega
        · rw [touchedCount_cons_of_not_mem T _ hbT] at hold
          omega
  exact ⟨hvAt', hfullLr', hfullR'⟩


private theorem touchedCount_cons_le (T : List Nat) (x : Nat) (c : List Nat) :
    touchedCount T (x :: c) ≤ touchedCount T c + 1 := by
  by_cases hx : x ∈ T
  · rw [touchedCount_cons_of_mem T c hx]
  · rw [touchedCount_cons_of_not_mem T c hx]; omega

private theorem minCargo_toKeyList_subset :
    ∀ (t : BinaryTree) (x : Nat), x ∈ (minCargo t).toKeyList → x ∈ t.toKeyList
  | .empty, x, hx => by simpa [minCargo] using hx
  | .node .empty k r, x, hx => by
      simp only [minCargo] at hx
      simp only [BinaryTree.toKeyList, List.mem_append, List.mem_singleton]
      tauto
  | .node (.node a b c) k r, x, hx => by
      simp only [minCargo] at hx
      have := minCargo_toKeyList_subset (BinaryTree.node a b c) x hx
      simp only [BinaryTree.toKeyList, List.mem_append, List.mem_singleton] at this ⊢
      tauto

/-- **Survivor chain bound** (shape-only, no touched-set hypotheses): the right spine of a
min-splay's right subtree extends the old right subtree's right spine by at most two spine
members, so its touched count grows by at most two. The three min-splay shapes give
`= rs c` (root), `b :: rs c` (zig), `ab :: b :: rs c` (zig-zig). -/
private theorem survivor_rsM_le (T' : List Nat) :
    ∀ (t : BinaryTree) (q : Nat), IsBST t → q ∈ t.toKeyList →
      (∀ y ∈ t.toKeyList, q ≤ y) →
      touchedCount T' (rightSpine (rightSubtree (splay t q)))
        ≤ 2 + touchedCount T' (rightSpine (rightSubtree t))
  | .empty, q, _, hmem, _ => by simp only [BinaryTree.toKeyList, List.not_mem_nil] at hmem
  | .node l k r, q, hbst, hmem, hmin => by
      rcases eq_or_ne q k with hqk | hqk
      · -- root: result right subtree is r = rightSubtree t
        subst hqk
        have hleq : l = .empty := by
          cases l with
          | empty => rfl
          | node la lx lb =>
              exfalso
              have hlx_lt : lx < q := by
                cases hbst with
                | node _ _ _ hfl _ _ _ =>
                    exact (forallTree_iff_forall_mem.mp hfl) lx (by simp [BinaryTree.toKeyList])
              have := hmin lx (by simp [BinaryTree.toKeyList])
              omega
        subst hleq
        have hsp : splay (BinaryTree.node .empty q r) q = BinaryTree.node .empty q r := by
          simp only [splay.eq_def, ↓reduceIte]
        rw [hsp]
        simp only [rightSubtree]
        omega
      · have hkmem : k ∈ (BinaryTree.node l k r).toKeyList := by simp [BinaryTree.toKeyList]
        have hqlt : q < k := lt_of_le_of_ne (hmin k hkmem) hqk
        have hql : q ∈ l.toKeyList := isBST_node_mem_left_of_lt_root hbst hmem hqlt
        have hbl : IsBST l := by cases hbst; assumption
        cases l with
        | empty => simp only [BinaryTree.toKeyList, List.not_mem_nil] at hql
        | node ll lk lr =>
            have hminl : ∀ y ∈ (BinaryTree.node ll lk lr).toKeyList, q ≤ y := by
              intro y hy
              refine hmin y ?_
              rw [BinaryTree.toKeyList]
              exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hy)))
            have hqlk : q ≤ lk := hminl lk (by simp [BinaryTree.toKeyList])
            rcases eq_or_ne q lk with hqeq | hqne
            · -- zig: result right subtree node lr k r; chain k :: rs r vs old k :: rs r
              subst hqeq
              have hlleq : ll = .empty := by
                cases ll with
                | empty => rfl
                | node a b c =>
                    exfalso
                    have hb_lt : b < q := by
                      cases hbl with
                      | node _ _ _ hfl _ _ _ =>
                          exact (forallTree_iff_forall_mem.mp hfl) b
                            (by simp [BinaryTree.toKeyList])
                    have := hminl b (by simp [BinaryTree.toKeyList])
                    omega
              subst hlleq
              have hnk : ¬ q = k := hqk
              have hnq : ¬ q < q := lt_irrefl q
              have hsp : splay (BinaryTree.node (.node .empty q lr) k r) q
                  = BinaryTree.node .empty q (.node lr k r) := by
                rw [splay.eq_def]
                simp only [hnk, ↓reduceIte, hqlt, lt_self_iff_false, rotate, rotateRight]
              rw [hsp]
              simp only [rightSubtree, rightSpine_node_eq]
              have := touchedCount_cons_le T' k (rightSpine r)
              omega
            · -- zig-zig: result right subtree node M lk (node lr k r);
              -- chain lk :: k :: rs r vs old k :: rs r — two cons
              have hqllt : q < lk := lt_of_le_of_ne hqlk hqne
              have hqll : q ∈ ll.toKeyList :=
                isBST_node_mem_left_of_lt_root hbl hql hqllt
              cases ll with
              | empty => simp [BinaryTree.toKeyList] at hqll
              | node a b c =>
                  have hbll : IsBST (BinaryTree.node a b c) := by cases hbl; assumption
                  have hminll : ∀ y ∈ (BinaryTree.node a b c).toKeyList, q ≤ y := by
                    intro y hy
                    refine hminl y ?_
                    rw [BinaryTree.toKeyList]
                    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hy)))
                  have hS := splay_min_eq_node_empty (BinaryTree.node a b c) q hbll hqll hminll
                  have hsp := splay_min_zigzig_shape a c lr r b lk k q hqk hqlt hqllt hS
                  rw [hsp]
                  simp only [rightSubtree, rightSpine_node_eq]
                  have h1 := touchedCount_cons_le T' lk
                    (k :: rightSpine r)
                  have h2 := touchedCount_cons_le T' k (rightSpine r)
                  omega


/-- **Per-splay preservation, zig-zig case**: `t = node (node (node a b c) lk lr) k r`
restructures to `node M lk (node lr k r)` with `M = rightSubtree (splay (node a b c) q)`.
Given the recursion's result `vInvariantFull T' M`, the invariant transfers to the whole:
`lr`, `r` are frozen blocks; the dropped parent `k`'s `vAt` follows from its old `vAt`
(losing the touched `lk` from its chain); the survivor `lk`'s `vAt` follows from both old
`vAt`s via the survivor chain bound (its new chain extends `rs c` by at most two touched
spine members). -/
private theorem vInv_preserved_zigzig (T T' : List Nat) (a c lr r : BinaryTree)
    (b lk k q : Nat)
    (hbst : IsBST (BinaryTree.node (.node (.node a b c) lk lr) k r))
    (hfullT : vInvariantFull T (BinaryTree.node (.node (.node a b c) lk lr) k r))
    (hmono : ∀ x ∈ T, x ∈ T')
    (hkT : k ∈ T) (hlkT : lk ∈ T) (hbT : b ∈ T)
    (hq : q ∈ (BinaryTree.node a b c).toKeyList)
    (hqmin : ∀ y ∈ (BinaryTree.node a b c).toKeyList, q ≤ y)
    (hfullM : vInvariantFull T'
      (rightSubtree (splay (BinaryTree.node a b c) q)))
    (hnew : ∀ x ∈ leftSpine (BinaryTree.node
      (rightSubtree (splay (BinaryTree.node a b c) q)) lk (.node lr k r)), x ∈ T')
    (hconf : ∀ x, x ∈ (BinaryTree.node (.node (.node a b c) lk lr) k r).toKeyList →
      x ∈ T' → x ∉ T →
      x ∈ leftSpine (BinaryTree.node
        (rightSubtree (splay (BinaryTree.node a b c) q)) lk (.node lr k r))) :
    vInvariantFull T'
      (BinaryTree.node (rightSubtree (splay (BinaryTree.node a b c) q)) lk
        (.node lr k r)) := by
  set M := rightSubtree (splay (BinaryTree.node a b c) q) with hM
  -- BST facts
  have hf_l : ForallTree (fun x => x < k) (BinaryTree.node (.node a b c) lk lr) := by
    cases hbst; assumption
  have hf_r : ForallTree (fun x => k < x) r := by cases hbst; assumption
  have hb_l : IsBST (BinaryTree.node (.node a b c) lk lr) := by cases hbst; assumption
  have hb_r : IsBST r := by cases hbst; assumption
  have hf_ll : ForallTree (fun x => x < lk) (BinaryTree.node a b c) := by
    cases hb_l; assumption
  have hf_lr : ForallTree (fun x => lk < x) lr := by cases hb_l; assumption
  have hb_ll : IsBST (BinaryTree.node a b c) := by cases hb_l; assumption
  have hb_lr : IsBST lr := by cases hb_l; assumption
  have hll_lt_lk : ∀ x ∈ (BinaryTree.node a b c).toKeyList, x < lk := forallTree_mem hf_ll
  have hlr_gt_lk : ∀ x ∈ lr.toKeyList, lk < x := forallTree_mem hf_lr
  have hlk_lt_k : lk < k := forallTree_mem hf_l lk (by simp [BinaryTree.toKeyList])
  have hlr_lt_k : ∀ x ∈ lr.toKeyList, x < k := fun x hx =>
    forallTree_mem hf_l x (by simp [BinaryTree.toKeyList, hx])
  have hr_gt_k : ∀ x ∈ r.toKeyList, k < x := forallTree_mem hf_r
  -- M's keys live in (node a b c)
  have hMkeys : ∀ x ∈ M.toKeyList, x ∈ (BinaryTree.node a b c).toKeyList := by
    intro x hx
    have h1 : x ∈ (splay (BinaryTree.node a b c) q).toKeyList :=
      mem_toKeyList_of_mem_rightSubtree hx
    rwa [splay_toKeyList] at h1
  have hLSM : ∀ x ∈ leftSpine M, x < lk := fun x hx =>
    hll_lt_lk x (hMkeys x (leftSpine_subset_toKeyList M x hx))
  -- old invariant destructured
  obtain ⟨hvAt_k, hfull_l, hfull_r⟩ := hfullT
  obtain ⟨hvAt_lk, hfull_ll, hfull_lr⟩ := hfull_l
  -- membership plumbing
  have hmem_lr : ∀ x ∈ lr.toKeyList,
      x ∈ (BinaryTree.node (.node (.node a b c) lk lr) k r).toKeyList := by
    intro x hx
    simp only [BinaryTree.toKeyList, List.mem_append, List.mem_singleton]
    exact Or.inl (Or.inl (Or.inr hx))
  have hmem_r : ∀ x ∈ r.toKeyList,
      x ∈ (BinaryTree.node (.node (.node a b c) lk lr) k r).toKeyList := by
    intro x hx
    simp only [BinaryTree.toKeyList, List.mem_append, List.mem_singleton]
    exact Or.inr hx
  have hmem_ll : ∀ x ∈ (BinaryTree.node a b c).toKeyList,
      x ∈ (BinaryTree.node (.node (.node a b c) lk lr) k r).toKeyList := by
    intro x hx
    simp only [BinaryTree.toKeyList, List.mem_append, List.mem_singleton] at hx ⊢
    exact Or.inl (Or.inl (Or.inl (Or.inl hx)))
  -- (A) lr frozen
  have hlr_frozen : ∀ y ∈ lr.toKeyList, y ∈ T' → y ∈ T := by
    intro y hy hyT'
    by_contra hyT
    have hys := hconf y (hmem_lr y hy) hyT' hyT
    simp only [leftSpine, List.mem_cons] at hys
    rcases hys with rfl | hys
    · exact absurd (hlr_gt_lk y hy) (lt_irrefl y)
    · have h1 : y < lk := hLSM y hys
      have h2 : lk < y := hlr_gt_lk y hy
      omega
  have hfullLr' : vInvariantFull T' lr :=
    vInvariantFull_frozen T T' lr hmono hlr_frozen hfull_lr
  -- (B) r frozen
  have hr_frozen : ∀ y ∈ r.toKeyList, y ∈ T' → y ∈ T := by
    intro y hy hyT'
    by_contra hyT
    have hys := hconf y (hmem_r y hy) hyT' hyT
    have hky : k < y := hr_gt_k y hy
    simp only [leftSpine, List.mem_cons] at hys
    rcases hys with rfl | hys
    · omega
    · have h1 : y < lk := hLSM y hys
      omega
  have hfullR' : vInvariantFull T' r := vInvariantFull_frozen T T' r hmono hr_frozen hfull_r
  -- frozen chains
  have hrsr_frozen : ∀ y ∈ rightSpine r, y ∈ T' → y ∈ T := fun y hy =>
    hr_frozen y (rightSpine_subset_toKeyList r y hy)
  have hrsrEq : touchedCount T' (rightSpine r) = touchedCount T (rightSpine r) :=
    touchedCount_frozen T T' _ hmono hrsr_frozen
  have hrslr_frozen : ∀ y ∈ rightSpine lr, y ∈ T' → y ∈ T := fun y hy =>
    hlr_frozen y (rightSpine_subset_toKeyList lr y hy)
  -- the old vAt of k, normalized: tc_T(rs lr) ≤ tc_T(rs r)
  have hwOld : touchedCount T (rightSpine lr) ≤ touchedCount T (rightSpine r) := by
    have hold := hvAt_k hkT
    simp only [rightSpine_node_eq] at hold
    rw [touchedCount_cons_of_mem T _ hlkT] at hold
    have hb0 : boundaryBit T (lk :: rightSpine lr) = 0 := by
      simp only [boundaryBit, hlkT, ↓reduceIte]
    rw [hb0] at hold
    omega
  -- (C) dropped parent k
  have hvAt_w : vAt T' lr k r := by
    intro _
    rw [touchedCount_frozen T T' _ hmono hrslr_frozen,
        boundaryBit_frozen T T' _ hmono hrslr_frozen, hrsrEq]
    have := boundaryBit_le_one T (rightSpine lr)
    omega
  -- (D) survivor lk
  have hvAt_z : vAt T' M lk (BinaryTree.node lr k r) := by
    intro _
    have hkT' : k ∈ T' := hmono k hkT
    rw [rightSpine_node_eq, touchedCount_cons_of_mem T' _ hkT', hrsrEq]
    -- bit of rs M is 0 (or M empty)
    cases hMshape : M with
    | empty =>
        simp only [rightSpine, touchedCount, boundaryBit, List.filter_nil, List.length_nil]
        omega
    | node m₁ mk m₂ =>
        have hmkT' : mk ∈ T' := by
          apply hnew mk
          rw [hMshape]
          simp only [leftSpine, List.mem_cons, true_or, or_true]
        have hbit : boundaryBit T' (rightSpine (BinaryTree.node m₁ mk m₂)) = 0 := by
          simp only [boundaryBit, rightSpine, hmkT', ↓reduceIte]
        rw [← hMshape] at hbit ⊢
        rw [hbit]
        -- survivor chain bound: tc'(rs M) ≤ 2 + tc'(rs c) (defeq: rightSubtree (node a b c) = c)
        have hsb : touchedCount T' (rightSpine M) ≤ 2 + touchedCount T' (rightSpine c) :=
          survivor_rsM_le T' (BinaryTree.node a b c) q hb_ll hq hqmin
        -- bound tc'(rs c) by cases on a
        cases a with
        | node a₁ ab a₂ =>
            -- interior: rs c fully frozen
            have hfcb : ForallTree (fun x => b < x) c := by cases hb_ll; assumption
            have hfab : ForallTree (fun x => x < b) (BinaryTree.node a₁ ab a₂) := by
              cases hb_ll; assumption
            have hc_frozen : ∀ y ∈ rightSpine c, y ∈ T' → y ∈ T := by
              intro y hy hyT'
              by_contra hyT
              have hyc : y ∈ c.toKeyList := rightSpine_subset_toKeyList c y hy
              have hyb : b < y := forallTree_mem hfcb y hyc
              have hyll : y ∈ (BinaryTree.node (.node a₁ ab a₂) b c).toKeyList := by
                simp only [BinaryTree.toKeyList, List.mem_append, List.mem_singleton]
                exact Or.inr hyc
              have hys := hconf y (hmem_ll y hyll) hyT' hyT
              simp only [leftSpine, List.mem_cons] at hys
              rcases hys with rfl | hys
              · exact absurd (hll_lt_lk y hyll) (lt_irrefl y)
              · rcases leftSpine_rightSubtree_splay_min_subset
                    (BinaryTree.node (.node a₁ ab a₂) b c) q hb_ll hq hqmin y hys with
                  hold | hcargo
                · simp only [leftSpine, List.mem_cons] at hold
                  rcases hold with rfl | rfl | hold
                  · omega
                  · have : y < b := forallTree_mem hfab y (by simp [BinaryTree.toKeyList])
                    omega
                  · have hy1 : y ∈ a₁.toKeyList := leftSpine_subset_toKeyList a₁ y hold
                    have : y < b := forallTree_mem hfab y
                      (by simp only [BinaryTree.toKeyList, List.mem_append,
                            List.mem_singleton]; exact Or.inl (Or.inl hy1))
                    omega
                · have h1 : y ∈ (minCargo (BinaryTree.node (.node a₁ ab a₂) b c)).toKeyList :=
                    leftSpine_subset_toKeyList _ y hcargo
                  have h2 : y ∈ (BinaryTree.node a₁ ab a₂).toKeyList := by
                    have := minCargo_toKeyList_subset (BinaryTree.node a₁ ab a₂) y
                      (by simpa [minCargo] using h1)
                    exact this
                  have : y < b := forallTree_mem hfab y h2
                  omega
            have hcEq : touchedCount T' (rightSpine c) = touchedCount T (rightSpine c) :=
              touchedCount_frozen T T' _ hmono hc_frozen
            -- old vAt of lk: tc_T(rs c) ≤ tc_T(rs lr)
            have hzOld := hvAt_lk hlkT
            simp only [rightSpine_node_eq] at hzOld
            rw [touchedCount_cons_of_mem T _ hbT] at hzOld
            have hb0 : boundaryBit T (b :: rightSpine c) = 0 := by
              simp only [boundaryBit, hbT, ↓reduceIte]
            rw [hb0] at hzOld
            omega
        | empty =>
            -- root subcase: q = b, M = c
            have hqb : q = b := by
              simp only [BinaryTree.toKeyList, List.mem_append, List.mem_singleton] at hq
              rcases hq with (h | rfl) | h
              · simp [BinaryTree.toKeyList] at h
              · rfl
              · exfalso
                have hfcb : ForallTree (fun x => b < x) c := by cases hb_ll; assumption
                have h1 : b < q := forallTree_mem hfcb q h
                have h2 : q ≤ b := hqmin b (by simp [BinaryTree.toKeyList])
                omega
            have hMc : M = c := by
              rw [hM, hqb]
              have hsp : splay (BinaryTree.node .empty b c) b
                  = BinaryTree.node .empty b c := by
                simp only [splay.eq_def, ↓reduceIte]
              rw [hsp]
              simp only [rightSubtree]
            -- with M = c: bound tc'(rs c) directly
            rw [hMc] at hsb hMshape ⊢
            -- c = node m₁ mk m₂ (from hMshape)
            subst hMshape
            have hfcb : ForallTree (fun x => b < x) (BinaryTree.node m₁ mk m₂) := by
              cases hb_ll; assumption
            have hb_c : IsBST (BinaryTree.node m₁ mk m₂) := by cases hb_ll; assumption
            have hf_m1 : ForallTree (fun x => x < mk) m₁ := by cases hb_c; assumption
            have hf_m2 : ForallTree (fun x => mk < x) m₂ := by cases hb_c; assumption
            -- rs m₂ is frozen
            have hm2_frozen : ∀ y ∈ rightSpine m₂, y ∈ T' → y ∈ T := by
              intro y hy hyT'
              by_contra hyT
              have hym2 : y ∈ m₂.toKeyList := rightSpine_subset_toKeyList m₂ y hy
              have hymk : mk < y := forallTree_mem hf_m2 y hym2
              have hyc : y ∈ (BinaryTree.node m₁ mk m₂).toKeyList := by
                simp only [BinaryTree.toKeyList, List.mem_append, List.mem_singleton]
                exact Or.inr hym2
              have hyll : y ∈ (BinaryTree.node .empty b (BinaryTree.node m₁ mk m₂)).toKeyList := by
                simp only [BinaryTree.toKeyList, List.mem_append, List.mem_singleton]
                exact Or.inr (Or.inr hym2)
              have hys := hconf y (hmem_ll y hyll) hyT' hyT
              rw [hMc] at hys
              simp only [leftSpine, List.mem_cons] at hys
              rcases hys with h1 | h2 | hys
              · have := hll_lt_lk y hyll
                omega
              · omega
              · have : y < mk := forallTree_mem hf_m1 y
                  (leftSpine_subset_toKeyList m₁ y hys)
                omega
            have hm2Eq : touchedCount T' (rightSpine m₂) = touchedCount T (rightSpine m₂) :=
              touchedCount_frozen T T' _ hmono hm2_frozen
            -- old vAt of lk over chain b :: mk :: rs m₂
            have hzOld := hvAt_lk hlkT
            simp only [rightSpine_node_eq] at hzOld
            rw [hqb] at *
            rw [touchedCount_cons_of_mem T _ hbT] at hzOld
            have hb0 : boundaryBit T (b :: mk :: rightSpine m₂) = 0 := by
              simp only [boundaryBit, hbT, ↓reduceIte]
            rw [hb0] at hzOld
            have hmk_le := touchedCount_cons_le T (mk) (rightSpine m₂)
            -- new chain: mk :: rs m₂ with mk ∈ T'
            simp only [rightSpine_node_eq]
            rw [touchedCount_cons_of_mem T' _ hmkT', hm2Eq]
            have hmk_ge : touchedCount T (mk :: rightSpine m₂) ≥ touchedCount T (rightSpine m₂) := by
              have := touchedCount_cons_le T mk (rightSpine m₂)
              by_cases hmkT : mk ∈ T
              · rw [touchedCount_cons_of_mem T _ hmkT]; omega
              · rw [touchedCount_cons_of_not_mem T _ hmkT]
            omega

  exact ⟨hvAt_z, hfullM, hvAt_w, hfullLr', hfullR'⟩


set_option maxHeartbeats 1000000 in
/-- **F2 MAIN: per-splay preservation of the v-invariant.** One min-splay step — restructuring
plus touched-set growth — carries `vInvariantFull` from `(T, t)` to `(T', rightSubtree (splay
t q))`. The recursion applies the release lemma at the root, the zig lemma at the base, and the
zig-zig lemma (fed by its own recursive result) at interior levels. -/
private theorem vInvariant_splay_preserved :
    ∀ (t : BinaryTree) (q : Nat) (T T' : List Nat),
      IsBST t → q ∈ t.toKeyList → (∀ y ∈ t.toKeyList, q ≤ y) →
      vInvariantFull T t →
      touchedClosed T t →
      (∀ x ∈ T, x ∈ T') →
      (∀ x ∈ leftSpine t, x ∈ T) →
      (∀ x ∈ leftSpine (rightSubtree (splay t q)), x ∈ T') →
      (∀ x, x ∈ t.toKeyList → x ∈ T' → x ∉ T →
        x ∈ leftSpine (rightSubtree (splay t q))) →
      vInvariantFull T' (rightSubtree (splay t q))
  | .empty, q, T, T', _, hmem, _, _, _, _, _, _, _ => by
      simp [BinaryTree.toKeyList] at hmem
  | .node l k r, q, T, T', hbst, hmem, hmin, hfullT, hclosedT, hmono, hspineT, hnew,
      hconf => by
      rcases eq_or_ne q k with hqk | hqk
      · -- root case: release on r
        subst hqk
        have hleq : l = .empty := by
          cases l with
          | empty => rfl
          | node la lx lb =>
              exfalso
              have hlx_lt : lx < q := by
                cases hbst with
                | node _ _ _ hfl _ _ _ =>
                    exact (forallTree_iff_forall_mem.mp hfl) lx (by simp [BinaryTree.toKeyList])
              have := hmin lx (by simp [BinaryTree.toKeyList])
              omega
        subst hleq
        have hsp : splay (BinaryTree.node .empty q r) q = BinaryTree.node .empty q r := by
          simp only [splay.eq_def, ↓reduceIte]
        rw [hsp] at hnew hconf ⊢
        simp only [rightSubtree] at hnew hconf ⊢
        obtain ⟨_, _, hfullR⟩ := hfullT
        obtain ⟨_, _, hclosedR⟩ := hclosedT
        have hbr : IsBST r := by cases hbst; assumption
        refine vInvariantFull_release T T' r hbr hfullR hclosedR hmono hnew ?_
        intro x hx hxT' hxT
        exact hconf x (by
          simp only [BinaryTree.toKeyList, List.mem_append, List.mem_singleton]; exact Or.inr hx)
          hxT' hxT
      · have hkmem : k ∈ (BinaryTree.node l k r).toKeyList := by simp [BinaryTree.toKeyList]
        have hqlt : q < k := lt_of_le_of_ne (hmin k hkmem) hqk
        have hql : q ∈ l.toKeyList := isBST_node_mem_left_of_lt_root hbst hmem hqlt
        have hbl : IsBST l := by cases hbst; assumption
        cases l with
        | empty => simp [BinaryTree.toKeyList] at hql
        | node ll lk lr =>
            have hminl : ∀ y ∈ (BinaryTree.node ll lk lr).toKeyList, q ≤ y := by
              intro y hy
              exact hmin y (by
                simp only [BinaryTree.toKeyList, List.mem_append] at hy ⊢; exact Or.inl (Or.inl hy))
            have hqlk : q ≤ lk := hminl lk (by simp [BinaryTree.toKeyList])
            have hkT : k ∈ T := hspineT k (by simp [leftSpine])
            rcases eq_or_ne q lk with hqeq | hqne
            · -- zig case
              subst hqeq
              have hlleq : ll = .empty := by
                cases ll with
                | empty => rfl
                | node a b c =>
                    exfalso
                    have hb_lt : b < q := by
                      cases hbl with
                      | node _ _ _ hfl _ _ _ =>
                          exact (forallTree_iff_forall_mem.mp hfl) b
                            (by simp [BinaryTree.toKeyList])
                    have := hminl b (by simp [BinaryTree.toKeyList])
                    omega
              subst hlleq
              have hnk : ¬ q = k := hqk
              have hnq : ¬ q < q := lt_irrefl q
              have hsp : splay (BinaryTree.node (.node .empty q lr) k r) q
                  = BinaryTree.node .empty q (.node lr k r) := by
                rw [splay.eq_def]
                simp only [hnk, ↓reduceIte, hqlt, lt_self_iff_false, rotate, rotateRight]
              rw [hsp] at hnew hconf ⊢
              simp only [rightSubtree] at hnew hconf ⊢
              have hqT : q ∈ T := hspineT q (by simp [leftSpine])
              exact vInv_preserved_zig T T' lr r k q hbst hfullT hclosedT hmono hkT hqT
                hnew hconf
            · -- zig-zig case
              have hqllt : q < lk := lt_of_le_of_ne hqlk hqne
              have hqll : q ∈ ll.toKeyList :=
                isBST_node_mem_left_of_lt_root hbl hql hqllt
              cases ll with
              | empty => simp [BinaryTree.toKeyList] at hqll
              | node a b c =>
                  have hbll : IsBST (BinaryTree.node a b c) := by cases hbl; assumption
                  have hminll : ∀ y ∈ (BinaryTree.node a b c).toKeyList, q ≤ y := by
                    intro y hy
                    exact hminl y (by
                      simp only [BinaryTree.toKeyList, List.mem_append] at hy ⊢; exact Or.inl (Or.inl hy))
                  have hS := splay_min_eq_node_empty (BinaryTree.node a b c) q hbll hqll hminll
                  have hsp := splay_min_zigzig_shape a c lr r b lk k q hqk hqlt hqllt hS
                  rw [hsp] at hnew hconf ⊢
                  simp only [rightSubtree] at hnew hconf ⊢
                  have hlkT : lk ∈ T := hspineT lk (by simp [leftSpine])
                  have hbT : b ∈ T := hspineT b (by simp [leftSpine])
                  have hll_lt_lk : ∀ x ∈ (BinaryTree.node a b c).toKeyList, x < lk := by
                    intro x hx
                    have hf : ForallTree (fun y => y < lk) (BinaryTree.node a b c) := by
                      cases hbl; assumption
                    exact forallTree_mem hf x hx
                  have hfull_ll : vInvariantFull T (BinaryTree.node a b c) :=
                    hfullT.2.1.2.1
                  have hclosed_ll : touchedClosed T (BinaryTree.node a b c) :=
                    hclosedT.2.1.2.1
                  -- the recursive call's hypotheses, with explicit types
                  have hspine_ll : ∀ x ∈ leftSpine (BinaryTree.node a b c), x ∈ T := by
                    intro x hx
                    exact hspineT x (by
                      simp only [leftSpine, List.mem_cons] at hx ⊢; exact Or.inr (Or.inr hx))
                  have hnew_ll : ∀ x ∈ leftSpine
                      (rightSubtree (splay (BinaryTree.node a b c) q)), x ∈ T' := by
                    intro x hx
                    exact hnew x (by
                      simp only [leftSpine, List.mem_cons]; exact Or.inr hx)
                  have hconf_ll : ∀ x, x ∈ (BinaryTree.node a b c).toKeyList → x ∈ T' →
                      x ∉ T → x ∈ leftSpine
                        (rightSubtree (splay (BinaryTree.node a b c) q)) := by
                    intro x hx hxT' hxT
                    have hxs := hconf x (by
                      simp only [BinaryTree.toKeyList, List.mem_append,
                        List.mem_singleton] at hx ⊢; exact Or.inl (Or.inl (Or.inl (Or.inl hx)))) hxT' hxT
                    simp only [leftSpine, List.mem_cons] at hxs
                    rcases hxs with rfl | hxs
                    · exact absurd (hll_lt_lk x hx) (lt_irrefl x)
                    · exact hxs
                  have hfullM : vInvariantFull T'
                      (rightSubtree (splay (BinaryTree.node a b c) q)) :=
                    vInvariant_splay_preserved (BinaryTree.node a b c) q T T'
                      hbll hqll hminll hfull_ll hclosed_ll hmono hspine_ll hnew_ll hconf_ll
                  exact vInv_preserved_zigzig T T' a c lr r b lk k q hbst hfullT hmono
                    hkT hlkT hbT hqll hminll hfullM hnew hconf


set_option maxHeartbeats 1000000 in
/-- **Per-splay preservation of touch-closure** (companion dispatcher): one min-splay step
carries `touchedClosed` from `(T, t)` to `(T', rightSubtree (splay t q))`. All result roots are
touched (making the closure implications vacuous); cargos are frozen; the released chain is
handled by `touchedClosed_release`. -/
private theorem touchedClosed_splay_preserved :
    ∀ (t : BinaryTree) (q : Nat) (T T' : List Nat),
      IsBST t → q ∈ t.toKeyList → (∀ y ∈ t.toKeyList, q ≤ y) →
      touchedClosed T t →
      (∀ x ∈ T, x ∈ T') →
      (∀ x ∈ leftSpine t, x ∈ T) →
      (∀ x ∈ leftSpine (rightSubtree (splay t q)), x ∈ T') →
      (∀ x, x ∈ t.toKeyList → x ∈ T' → x ∉ T →
        x ∈ leftSpine (rightSubtree (splay t q))) →
      touchedClosed T' (rightSubtree (splay t q))
  | .empty, q, T, T', _, hmem, _, _, _, _, _, _ => by
      simp only [BinaryTree.toKeyList, List.not_mem_nil] at hmem
  | .node l k r, q, T, T', hbst, hmem, hmin, hclosedT, hmono, hspineT, hnew, hconf => by
      rcases eq_or_ne q k with hqk | hqk
      · -- root case
        subst hqk
        have hleq : l = .empty := by
          cases l with
          | empty => rfl
          | node la lx lb =>
              exfalso
              have hlx_lt : lx < q := by
                cases hbst with
                | node _ _ _ hfl _ _ _ =>
                    exact (forallTree_iff_forall_mem.mp hfl) lx (by simp only [BinaryTree.toKeyList, List.append_assoc, List.cons_append, List.nil_append, List.mem_append, List.mem_cons, true_or, or_true])
              have := hmin lx (by simp only [BinaryTree.toKeyList, List.append_assoc, List.cons_append, List.nil_append, List.mem_append, List.mem_cons, true_or, or_true])
              omega
        subst hleq
        have hsp : splay (BinaryTree.node .empty q r) q = BinaryTree.node .empty q r := by
          simp only [splay.eq_def, ↓reduceIte]
        rw [hsp] at hnew hconf ⊢
        simp only [rightSubtree] at hnew hconf ⊢
        obtain ⟨_, _, hclosedR⟩ := hclosedT
        have hbr : IsBST r := by cases hbst; assumption
        refine touchedClosed_release T T' r hbr hclosedR hmono hnew ?_
        intro x hx hxT' hxT
        exact hconf x (by
          simp only [BinaryTree.toKeyList, List.mem_append, List.mem_singleton]; exact Or.inr hx)
          hxT' hxT
      · have hkmem : k ∈ (BinaryTree.node l k r).toKeyList := by simp only [BinaryTree.toKeyList, List.append_assoc, List.cons_append, List.nil_append, List.mem_append, List.mem_cons, true_or, or_true]
        have hqlt : q < k := lt_of_le_of_ne (hmin k hkmem) hqk
        have hql : q ∈ l.toKeyList := isBST_node_mem_left_of_lt_root hbst hmem hqlt
        have hbl : IsBST l := by cases hbst; assumption
        have hbr : IsBST r := by cases hbst; assumption
        have hf_l : ForallTree (fun x => x < k) l := by cases hbst; assumption
        have hf_r : ForallTree (fun x => k < x) r := by cases hbst; assumption
        have hkT : k ∈ T := hspineT k (by simp only [leftSpine, List.mem_cons, true_or])
        have hr_gt_k : ∀ x ∈ r.toKeyList, k < x := forallTree_mem hf_r
        cases l with
        | empty => simp only [BinaryTree.toKeyList, List.not_mem_nil] at hql
        | node ll lk lr =>
            have hminl : ∀ y ∈ (BinaryTree.node ll lk lr).toKeyList, q ≤ y := by
              intro y hy
              exact hmin y (by
                simp only [BinaryTree.toKeyList, List.mem_append] at hy ⊢; exact Or.inl (Or.inl hy))
            have hqlk : q ≤ lk := hminl lk (by simp only [BinaryTree.toKeyList, List.append_assoc, List.cons_append, List.nil_append, List.mem_append, List.mem_cons, true_or, or_true])
            have hlr_lt_k : ∀ x ∈ lr.toKeyList, x < k := fun x hx =>
              forallTree_mem hf_l x (by simp only [BinaryTree.toKeyList, List.append_assoc, List.cons_append, List.nil_append, List.mem_append, List.mem_cons, hx, or_true])
            have hf_lr : ForallTree (fun x => lk < x) lr := by cases hbl; assumption
            have hlr_gt_lk : ∀ x ∈ lr.toKeyList, lk < x := forallTree_mem hf_lr
            rcases eq_or_ne q lk with hqeq | hqne
            · -- zig case: result node lr k r
              subst hqeq
              have hlleq : ll = .empty := by
                cases ll with
                | empty => rfl
                | node a b c =>
                    exfalso
                    have hb_lt : b < q := by
                      cases hbl with
                      | node _ _ _ hfl _ _ _ =>
                          exact (forallTree_iff_forall_mem.mp hfl) b
                            (by simp only [BinaryTree.toKeyList, List.append_assoc, List.cons_append, List.nil_append, List.mem_append, List.mem_cons, true_or, or_true])
                    have := hminl b (by simp only [BinaryTree.toKeyList, List.append_assoc, List.cons_append, List.nil_append, List.mem_append, List.mem_cons, true_or, or_true])
                    omega
              subst hlleq
              have hnk : ¬ q = k := hqk
              have hnq : ¬ q < q := lt_irrefl q
              have hsp : splay (BinaryTree.node (.node .empty q lr) k r) q
                  = BinaryTree.node .empty q (.node lr k r) := by
                rw [splay.eq_def]
                simp only [hnk, ↓reduceIte, hqlt, lt_self_iff_false, rotate, rotateRight]
              rw [hsp] at hnew hconf ⊢
              simp only [rightSubtree] at hnew hconf ⊢
              obtain ⟨_, hclosedL, hclosedR⟩ := hclosedT
              obtain ⟨_, _, hclosedLr⟩ := hclosedL
              have hblr : IsBST lr := by cases hbl; assumption
              refine ⟨fun hk' => absurd (hmono k hkT) hk', ?_, ?_⟩
              · -- released cargo lr
                refine touchedClosed_release T T' lr hblr hclosedLr hmono ?_ ?_
                · intro x hx
                  exact hnew x (by simp only [leftSpine, List.mem_cons]; exact Or.inr hx)
                · intro x hx hxT' hxT
                  have hxs := hconf x (by
                    simp only [BinaryTree.toKeyList, List.mem_append,
                      List.mem_singleton]; exact Or.inl (Or.inl (Or.inr hx))) hxT' hxT
                  simp only [leftSpine, List.mem_cons] at hxs
                  rcases hxs with rfl | hxs
                  · exact absurd (hlr_lt_k x hx) (lt_irrefl x)
                  · exact hxs
              · -- frozen r
                refine touchedClosed_frozen T T' r hmono ?_ hclosedR
                intro y hy hyT'
                by_contra hyT
                have hys := hconf y (by
                  simp only [BinaryTree.toKeyList, List.mem_append,
                    List.mem_singleton]; exact Or.inr hy) hyT' hyT
                have hky : k < y := hr_gt_k y hy
                simp only [leftSpine, List.mem_cons] at hys
                rcases hys with rfl | hys
                · omega
                · have : y < k := hlr_lt_k y (leftSpine_subset_toKeyList lr y hys)
                  omega
            · -- zig-zig case: result node M lk (node lr k r)
              have hqllt : q < lk := lt_of_le_of_ne hqlk hqne
              have hqll : q ∈ ll.toKeyList :=
                isBST_node_mem_left_of_lt_root hbl hql hqllt
              cases ll with
              | empty => simp only [BinaryTree.toKeyList, List.not_mem_nil] at hqll
              | node a b c =>
                  have hbll : IsBST (BinaryTree.node a b c) := by cases hbl; assumption
                  have hminll : ∀ y ∈ (BinaryTree.node a b c).toKeyList, q ≤ y := by
                    intro y hy
                    exact hminl y (by
                      simp only [BinaryTree.toKeyList, List.mem_append] at hy ⊢; exact Or.inl (Or.inl hy))
                  have hS := splay_min_eq_node_empty (BinaryTree.node a b c) q hbll hqll hminll
                  have hsp := splay_min_zigzig_shape a c lr r b lk k q hqk hqlt hqllt hS
                  rw [hsp] at hnew hconf ⊢
                  simp only [rightSubtree] at hnew hconf ⊢
                  have hlkT : lk ∈ T := hspineT lk (by simp only [leftSpine, List.mem_cons, true_or, or_true])
                  have hll_lt_lk : ∀ x ∈ (BinaryTree.node a b c).toKeyList, x < lk := by
                    intro x hx
                    have hf : ForallTree (fun y => y < lk) (BinaryTree.node a b c) := by
                      cases hbl; assumption
                    exact forallTree_mem hf x hx
                  have hclosed_ll : touchedClosed T (BinaryTree.node a b c) :=
                    hclosedT.2.1.2.1
                  have hclosed_lr : touchedClosed T lr := hclosedT.2.1.2.2
                  have hclosed_r : touchedClosed T r := hclosedT.2.2
                  have hMkeys : ∀ x ∈ (rightSubtree
                      (splay (BinaryTree.node a b c) q)).toKeyList,
                      x ∈ (BinaryTree.node a b c).toKeyList := by
                    intro x hx
                    have h1 : x ∈ (splay (BinaryTree.node a b c) q).toKeyList :=
                      mem_toKeyList_of_mem_rightSubtree hx
                    rwa [splay_toKeyList] at h1
                  -- recursive call for M
                  have hspine_ll : ∀ x ∈ leftSpine (BinaryTree.node a b c), x ∈ T := by
                    intro x hx
                    exact hspineT x (by
                      simp only [leftSpine, List.mem_cons] at hx ⊢; exact Or.inr (Or.inr hx))
                  have hnew_ll : ∀ x ∈ leftSpine
                      (rightSubtree (splay (BinaryTree.node a b c) q)), x ∈ T' := by
                    intro x hx
                    exact hnew x (by
                      simp only [leftSpine, List.mem_cons]; exact Or.inr hx)
                  have hconf_ll : ∀ x, x ∈ (BinaryTree.node a b c).toKeyList → x ∈ T' →
                      x ∉ T → x ∈ leftSpine
                        (rightSubtree (splay (BinaryTree.node a b c) q)) := by
                    intro x hx hxT' hxT
                    have hxs := hconf x (by
                      simp only [BinaryTree.toKeyList, List.mem_append,
                        List.mem_singleton] at hx ⊢; exact Or.inl (Or.inl (Or.inl (Or.inl hx)))) hxT' hxT
                    simp only [leftSpine, List.mem_cons] at hxs
                    rcases hxs with rfl | hxs
                    · exact absurd (hll_lt_lk x hx) (lt_irrefl x)
                    · exact hxs
                  have hclosedM : touchedClosed T'
                      (rightSubtree (splay (BinaryTree.node a b c) q)) :=
                    touchedClosed_splay_preserved (BinaryTree.node a b c) q T T'
                      hbll hqll hminll hclosed_ll hmono hspine_ll hnew_ll hconf_ll
                  -- frozen lr / r facts
                  have hlr_frozen : ∀ y ∈ lr.toKeyList, y ∈ T' → y ∈ T := by
                    intro y hy hyT'
                    by_contra hyT
                    have hys := hconf y (by
                      simp only [BinaryTree.toKeyList, List.mem_append,
                        List.mem_singleton]; exact Or.inl (Or.inl (Or.inr hy))) hyT' hyT
                    simp only [leftSpine, List.mem_cons] at hys
                    rcases hys with rfl | hys
                    · exact absurd (hlr_gt_lk y hy) (lt_irrefl y)
                    · have h1 : y < lk := hll_lt_lk y
                        (hMkeys y (leftSpine_subset_toKeyList _ y hys))
                      have h2 : lk < y := hlr_gt_lk y hy
                      omega
                  have hr_frozen : ∀ y ∈ r.toKeyList, y ∈ T' → y ∈ T := by
                    intro y hy hyT'
                    by_contra hyT
                    have hys := hconf y (by
                      simp only [BinaryTree.toKeyList, List.mem_append,
                        List.mem_singleton]; exact Or.inr hy) hyT' hyT
                    have hky : k < y := hr_gt_k y hy
                    have hlkk : lk < k := forallTree_mem hf_l lk (by
                      simp only [BinaryTree.toKeyList, List.append_assoc, List.cons_append, List.nil_append, List.mem_append, List.mem_cons, true_or, or_true])
                    simp only [leftSpine, List.mem_cons] at hys
                    rcases hys with rfl | hys
                    · omega
                    · have h1 : y < lk := hll_lt_lk y
                        (hMkeys y (leftSpine_subset_toKeyList _ y hys))
                      omega
                  exact ⟨fun hlk' => absurd (hmono lk hlkT) hlk',
                    hclosedM,
                    fun hk' => absurd (hmono k hkT) hk',
                    touchedClosed_frozen T T' lr hmono hlr_frozen hclosed_lr,
                    touchedClosed_frozen T T' r hmono hr_frozen hclosed_r⟩


/-! ### NB-form and base-case lemmas (integrated from the fan-out) -/

private theorem mem_node_left {x : Nat} {l r : BinaryTree} {k : Nat}
    (hx : x ∈ l.toKeyList) : x ∈ (BinaryTree.node l k r).toKeyList := by
  simp only [BinaryTree.toKeyList, List.mem_append]
  exact Or.inl (Or.inl hx)

private theorem mem_node_right {x : Nat} {l r : BinaryTree} {k : Nat}
    (hx : x ∈ r.toKeyList) : x ∈ (BinaryTree.node l k r).toKeyList := by
  simp only [BinaryTree.toKeyList, List.mem_append]
  exact Or.inr hx

private theorem touchedCount_le_length (T : List Nat) (c : List Nat) :
    touchedCount T c ≤ c.length := by
  unfold touchedCount
  exact List.length_filter_le _ _

private theorem boundaryBit_zero_of_head_mem (T : List Nat) (x : Nat) (c : List Nat)
    (hx : x ∈ T) : boundaryBit T (x :: c) = 0 := by
  simp [boundaryBit, hx]

private theorem touchedCount_append (T : List Nat) (c d : List Nat) :
    touchedCount T (c ++ d) = touchedCount T c + touchedCount T d := by
  simp [touchedCount, List.filter_append]

private theorem vInvariantNB_of_full (T : List Nat) :
    ∀ (u : BinaryTree), vInvariantFull T u → vInvariantNB T u := by
  intro u
  induction u with
  | empty => intro _; trivial
  | node l k r ihl ihr =>
    intro h
    obtain ⟨_, hl, hr⟩ := h
    exact ⟨hl, ihr hr⟩

private theorem vInvariantNB_frozen (T T' : List Nat) :
    ∀ (u : BinaryTree),
      (∀ x ∈ T, x ∈ T') →
      (∀ y ∈ u.toKeyList, y ∈ T' → y ∈ T) →
      vInvariantNB T u → vInvariantNB T' u := by
  intro u
  induction u with
  | empty => intro _ _ _; trivial
  | node l k r ihl ihr =>
    intro hsub hfro h
    obtain ⟨hl, hr⟩ := h
    exact ⟨vInvariantFull_frozen T T' l hsub
        (fun y hy => hfro y (mem_node_left hy)) hl,
      ihr hsub (fun y hy => hfro y (mem_node_right hy)) hr⟩

/-- Base case: when the touched set is confined to the left spine and contains it, the full
invariant holds (every touched node is a spine node with `h = 1`, `bit = 0`, `g ≥ 1`). -/
private theorem vInvariantFull_of_spine (T : List Nat) :
    ∀ (u : BinaryTree), IsBST u →
      (∀ y ∈ u.toKeyList, y ∈ T → y ∈ leftSpine u) →
      (∀ x ∈ leftSpine u, x ∈ T) →
      vInvariantFull T u := by
  intro u
  induction u with
  | empty => intro _ _ _; simp only [vInvariantFull]
  | node l k r ihl ihr =>
    intro hbst hconf hspine
    rcases hbst with _ | ⟨_, _, _, hl, hr, bl, br⟩
    simp only [vInvariantFull]
    refine ⟨?_, ?_, ?_⟩
    · intro _hkT
      cases l with
      | empty =>
        simp only [touchedCount, rightSpine, List.filter_nil, List.length_nil, boundaryBit,
          add_zero, zero_le]
      | node l₁ lk₁ l₂ =>
        rcases bl with _ | ⟨_, _, _, hl₁, hl₂, bl₁, bl₂⟩
        have hlk₁T : lk₁ ∈ T := hspine lk₁ (by simp only [leftSpine, List.mem_cons, true_or, or_true])
        have hzero : touchedCount T (rightSpine l₂) = 0 := by
          apply touchedCount_zero
          intro y hy hyT
          have hykeys : y ∈ l₂.toKeyList := rightSpine_subset_toKeyList l₂ y hy
          have hlk₁y : lk₁ < y := forallTree_mem hl₂ y hykeys
          have hyk : y < k := forallTree_mem hl y (mem_node_right hykeys)
          have hyu : y ∈ (BinaryTree.node (BinaryTree.node l₁ lk₁ l₂) k r).toKeyList :=
            mem_node_left (mem_node_right hykeys)
          have hys := hconf y hyu hyT
          simp only [leftSpine, List.mem_cons] at hys
          rcases hys with h | h | h
          · omega
          · omega
          · have : y < lk₁ := forallTree_mem hl₁ y (leftSpine_subset_toKeyList l₁ y h)
            omega
        show touchedCount T (lk₁ :: rightSpine l₂) + boundaryBit T (lk₁ :: rightSpine l₂)
              ≤ 1 + touchedCount T (rightSpine r)
        rw [touchedCount_cons_of_mem T _ hlk₁T, hzero]
        simp only [zero_add, boundaryBit, hlk₁T, ↓reduceIte, add_zero, le_add_iff_nonneg_right,
          zero_le]
    · refine ihl bl ?_ ?_
      · intro y hy hyT
        have hyu : y ∈ (BinaryTree.node l k r).toKeyList := mem_node_left hy
        have hys := hconf y hyu hyT
        simp only [leftSpine, List.mem_cons] at hys
        rcases hys with h | h
        · exfalso
          have : y < k := forallTree_mem hl y hy
          omega
        · exact h
      · intro x hx
        exact hspine x (List.mem_cons_of_mem _ hx)
    · apply vInvariantFull_of_untouched
      intro y hy hyT
      have hky : k < y := forallTree_mem hr y hy
      have hyu : y ∈ (BinaryTree.node l k r).toKeyList := mem_node_right hy
      have hys := hconf y hyu hyT
      simp only [leftSpine, List.mem_cons] at hys
      rcases hys with h | h
      · omega
      · have : y < k := forallTree_mem hl y (leftSpine_subset_toKeyList l y h)
        omega

/-- Closure base case: when the touched set is confined to the left spine and contains it,
`touchedClosed` holds. -/
private theorem touchedClosed_of_spine (T : List Nat) :
    ∀ (u : BinaryTree), IsBST u →
      (∀ y ∈ u.toKeyList, y ∈ T → y ∈ leftSpine u) →
      (∀ x ∈ leftSpine u, x ∈ T) →
      touchedClosed T u := by
  intro u
  induction u with
  | empty => intro _ _ _; trivial
  | node l k r ihl ihr =>
    intro hbst hconf hspine
    cases hbst with
    | node _ _ _ hlk hkr hbl hbr =>
      have hkT : k ∈ T := hspine k (by simp [leftSpine])
      refine ⟨fun hk => absurd hkT hk, ?_, ?_⟩
      · apply ihl hbl
        · intro y hy hyT
          have hys : y ∈ leftSpine (BinaryTree.node l k r) :=
            hconf y (mem_node_left hy) hyT
          simp only [leftSpine, List.mem_cons] at hys
          rcases hys with rfl | h
          · exact absurd (forallTree_mem hlk _ hy) (lt_irrefl _)
          · exact h
        · intro x hx
          apply hspine x
          simp only [leftSpine, List.mem_cons]
          exact Or.inr hx
      · apply touchedClosed_of_untouched
        intro x hx hxT
        have hkx : k < x := forallTree_mem hkr x hx
        have hxs : x ∈ leftSpine (BinaryTree.node l k r) :=
          hconf x (mem_node_right hx) hxT
        simp only [leftSpine, List.mem_cons] at hxs
        rcases hxs with rfl | h
        · exact absurd hkx (lt_irrefl _)
        · have hxl : x ∈ l.toKeyList := leftSpine_subset_toKeyList l x h
          have hxk : x < k := forallTree_mem hlk x hxl
          omega


/-- **Process invariants, base case** (`k = 1`): after the first access the touched set is
exactly the new spine, so both invariants hold by the spine base lemmas. -/
private theorem process_invariants_base (init : BinaryTree) (hbst : IsBST init) :
    vInvariantNB (touchedKeys init 1) (rightSubtree (seqTree init 1))
    ∧ touchedClosed (touchedKeys init 1) (rightSubtree (seqTree init 1)) := by
  have hT1 : touchedKeys init 1 = leftSpine (rightSubtree (seqTree init 1)) := by
    show touchedKeys init 0 ++ leftSpine (rightSubtree (seqTree init 1))
        = leftSpine (rightSubtree (seqTree init 1))
    simp [touchedKeys]
  have hbR : IsBST (rightSubtree (seqTree init 1)) :=
    rightSubtree_isBST_of_isBST (seqTree_isBST init hbst 1)
  have hconf : ∀ y ∈ (rightSubtree (seqTree init 1)).toKeyList,
      y ∈ touchedKeys init 1 → y ∈ leftSpine (rightSubtree (seqTree init 1)) := by
    intro y _ hy; rwa [hT1] at hy
  have hspine : ∀ x ∈ leftSpine (rightSubtree (seqTree init 1)),
      x ∈ touchedKeys init 1 := by
    intro x hx; rwa [hT1]
  exact ⟨vInvariantNB_of_full _ _
      (vInvariantFull_of_spine _ (rightSubtree (seqTree init 1)) hbR hconf hspine),
    touchedClosed_of_spine _ (rightSubtree (seqTree init 1)) hbR hconf hspine⟩


set_option maxHeartbeats 1000000 in
/-- **Process invariants, step**: both invariants carry from step `k` to step `k+1`
(`1 ≤ k < n`). The real access of `k` descends through the root `k-1` into `Rₖ`: if `k` is at
`Rₖ`'s root, a single zag releases its cargo (case A); otherwise a zagZig wraps a min-splay of
`Rₖ`'s left child, handled by the per-splay preservation dispatchers (case B). -/
private theorem process_invariants_step (init : BinaryTree) (hbst : IsBST init)
    {n : Nat} (hkeys : ∀ m : Nat, m < n → m ∈ init.toKeyList)
    (k : Nat) (hk1 : 1 ≤ k) (hkn : k < n)
    (ihNB : vInvariantNB (touchedKeys init k) (rightSubtree (seqTree init k)))
    (ihC : touchedClosed (touchedKeys init k) (rightSubtree (seqTree init k))) :
    vInvariantNB (touchedKeys init (k + 1)) (rightSubtree (seqTree init (k + 1)))
    ∧ touchedClosed (touchedKeys init (k + 1)) (rightSubtree (seqTree init (k + 1))) := by
  -- the tree at step k
  have hroot : rootKey (seqTree init k) = some (k - 1) := by
    have h := seqTree_rootKey init hbst hkeys (k - 1) (by omega)
    rwa [Nat.sub_add_cancel hk1] at h
  obtain ⟨L, R, heq⟩ : ∃ L R, seqTree init k = .node L (k - 1) R := by
    cases hh : seqTree init k with
    | empty => rw [hh] at hroot; simp [rootKey] at hroot
    | node a b c =>
        rw [hh] at hroot; simp only [rootKey, Option.some.injEq] at hroot
        exact ⟨a, c, by rw [hroot]⟩
  have hbstk : IsBST (BinaryTree.node L (k - 1) R) := heq ▸ seqTree_isBST init hbst k
  have hbR : IsBST R := by cases hbstk; assumption
  have hmemiff : ∀ x, x ∈ R.toKeyList ↔ (k - 1 < x ∧ x ∈ init.toKeyList) := by
    intro x
    have h := rightSubtree_seqTree_succ_mem_iff init hbst hkeys (k - 1) (by omega) x
    rw [Nat.sub_add_cancel hk1, heq] at h
    simpa [rightSubtree] using h
  have hkR : k ∈ R.toKeyList := (hmemiff k).mpr ⟨by omega, hkeys k hkn⟩
  have hkminR : ∀ y ∈ R.toKeyList, k ≤ y := fun y hy => by
    have := (hmemiff y).mp hy; omega
  -- touched-set facts
  have hmono : ∀ x ∈ touchedKeys init k, x ∈ touchedKeys init (k + 1) :=
    touchedKeys_mono init k
  have hnewT' : ∀ x ∈ leftSpine (rightSubtree (seqTree init (k + 1))),
      x ∈ touchedKeys init (k + 1) :=
    spine_subset_touchedKeys init (k + 1) (by omega)
  have hconfT : ∀ x ∈ touchedKeys init (k + 1), x ∉ touchedKeys init k →
      x ∈ leftSpine (rightSubtree (seqTree init (k + 1))) :=
    touchedKeys_succ_diff init k
  have hRsub : rightSubtree (seqTree init k) = R := by rw [heq]; rfl
  have hRspine : ∀ x ∈ leftSpine R, x ∈ touchedKeys init k := by
    intro x hx
    exact spine_subset_touchedKeys init k hk1 x (by rwa [hRsub])
  rw [hRsub] at ihNB ihC
  have hstep : seqTree init (k + 1) = splay (seqTree init k) k := rfl
  have hnqm : ¬ k = k - 1 := by omega
  have hnqltm : ¬ k < k - 1 := by omega
  cases R with
  | empty => simp [BinaryTree.toKeyList] at hkR
  | node rl rk rr =>
      have hrk_ge : k ≤ rk := hkminR rk (by simp [BinaryTree.toKeyList])
      have hf_rl : ForallTree (fun x => x < rk) rl := by cases hbR; assumption
      have hf_rr : ForallTree (fun x => rk < x) rr := by cases hbR; assumption
      have hb_rl : IsBST rl := by cases hbR; assumption
      have hb_rr : IsBST rr := by cases hbR; assumption
      rcases eq_or_ne k rk with hkrk | hkrk
      · -- CASE A: min at R's root; single zag; R' = rr
        subst hkrk
        have hrleq : rl = .empty := by
          cases rl with
          | empty => rfl
          | node x y z =>
              exfalso
              have h1 : y < k := forallTree_mem hf_rl y (by simp [BinaryTree.toKeyList])
              have h2 : k ≤ y := hkminR y (by simp [BinaryTree.toKeyList])
              omega
        subst hrleq
        have hnq : ¬ k < k := lt_irrefl k
        have hsp : splay (BinaryTree.node L (k - 1) (.node .empty k rr)) k
            = BinaryTree.node (.node L (k - 1) .empty) k rr := by
          rw [splay.eq_def]
          simp only [hnqm, ↓reduceIte, hnqltm, lt_self_iff_false, rotate, rotateLeft]
        have hR' : rightSubtree (seqTree init (k + 1)) = rr := by
          rw [hstep, heq, hsp]; rfl
        rw [hR'] at hnewT' hconfT ⊢
        obtain ⟨_, ihNB_rr⟩ := ihNB
        have hcl_rr : touchedClosed (touchedKeys init k) rr := ihC.2.2
        have hconf_rr : ∀ x, x ∈ rr.toKeyList → x ∈ touchedKeys init (k + 1) →
            x ∉ touchedKeys init k → x ∈ leftSpine rr :=
          fun x _ hx' hxn => hconfT x hx' hxn
        refine ⟨?_, touchedClosed_release _ _ rr hb_rr hcl_rr hmono hnewT' hconf_rr⟩
        -- NB(T', rr)
        cases rr with
        | empty => trivial
        | node w₁ wk w₂ =>
            obtain ⟨ihFull_w₁, ihNB_w₂⟩ := ihNB_rr
            have hcl_w₁ : touchedClosed (touchedKeys init k) w₁ := hcl_rr.2.1
            have hf_w1 : ForallTree (fun x => x < wk) w₁ := by cases hb_rr; assumption
            have hf_w2 : ForallTree (fun x => wk < x) w₂ := by cases hb_rr; assumption
            have hbw₁ : IsBST w₁ := by cases hb_rr; assumption
            refine ⟨?_, ?_⟩
            · -- Full(T', w₁): release
              refine vInvariantFull_release _ _ w₁ hbw₁ ihFull_w₁ hcl_w₁ hmono ?_ ?_
              · intro x hx
                exact hnewT' x (by simp only [leftSpine, List.mem_cons]; exact Or.inr hx)
              · intro x hx hxT' hxT
                have hxs := hconfT x hxT' hxT
                simp only [leftSpine, List.mem_cons] at hxs
                rcases hxs with rfl | hxs
                · exact absurd (forallTree_mem hf_w1 x hx) (lt_irrefl x)
                · exact hxs
            · -- NB(T', w₂): frozen
              refine vInvariantNB_frozen _ _ w₂ hmono ?_ ihNB_w₂
              intro y hy hyT'
              by_contra hyT
              have hys := hconfT y hyT' hyT
              have hwy : wk < y := forallTree_mem hf_w2 y hy
              simp only [leftSpine, List.mem_cons] at hys
              rcases hys with rfl | hys
              · omega
              · have : y < wk := forallTree_mem hf_w1 y
                  (leftSpine_subset_toKeyList w₁ y hys)
                omega
      · -- CASE B: min strictly inside rl; zagZig around a min-splay of rl
        have hkltrk : k < rk := lt_of_le_of_ne hrk_ge hkrk
        have hkrl : k ∈ rl.toKeyList := isBST_node_mem_left_of_lt_root hbR hkR hkltrk
        cases rl with
        | empty => simp [BinaryTree.toKeyList] at hkrl
        | node a b c =>
            have hminrl : ∀ y ∈ (BinaryTree.node a b c).toKeyList, k ≤ y := by
              intro y hy
              exact hkminR y (by
                simp only [BinaryTree.toKeyList, List.mem_append] at hy ⊢; exact Or.inl (Or.inl hy))
            have hS := splay_min_eq_node_empty (BinaryTree.node a b c) k hb_rl hkrl hminrl
            have hsp : splay (BinaryTree.node L (k - 1)
                (.node (.node a b c) rk rr)) k
                = BinaryTree.node (.node L (k - 1) .empty) k
                    (.node (rightSubtree (splay (BinaryTree.node a b c) k)) rk rr) := by
              rw [splay.eq_def]
              simp only [if_neg hnqm, if_neg hnqltm, if_pos hkltrk]
              rw [hS]
              simp only [rotate, rotateLeft, rotateRight, rightSubtree]
            have hR' : rightSubtree (seqTree init (k + 1))
                = BinaryTree.node (rightSubtree (splay (BinaryTree.node a b c) k)) rk rr := by
              rw [hstep, heq, hsp]; rfl
            rw [hR'] at hnewT' hconfT ⊢
            obtain ⟨ihFull_rl, ihNB_rr⟩ := ihNB
            have hcl_rl : touchedClosed (touchedKeys init k) (BinaryTree.node a b c) :=
              ihC.2.1
            have hcl_rr : touchedClosed (touchedKeys init k) rr := ihC.2.2
            have hrkT : rk ∈ touchedKeys init k := hRspine rk (by simp [leftSpine])
            have hrlspine : ∀ x ∈ leftSpine (BinaryTree.node a b c),
                x ∈ touchedKeys init k := by
              intro x hx
              exact hRspine x (by
                simp only [leftSpine, List.mem_cons] at hx ⊢; exact Or.inr hx)
            have hrl_lt_rk : ∀ x ∈ (BinaryTree.node a b c).toKeyList, x < rk :=
              forallTree_mem hf_rl
            have hMkeys : ∀ x ∈ (rightSubtree
                (splay (BinaryTree.node a b c) k)).toKeyList,
                x ∈ (BinaryTree.node a b c).toKeyList := by
              intro x hx
              have h1 : x ∈ (splay (BinaryTree.node a b c) k).toKeyList :=
                mem_toKeyList_of_mem_rightSubtree hx
              rwa [splay_toKeyList] at h1
            -- shared hypotheses for the two dispatchers
            have hnew_M : ∀ x ∈ leftSpine
                (rightSubtree (splay (BinaryTree.node a b c) k)),
                x ∈ touchedKeys init (k + 1) := by
              intro x hx
              exact hnewT' x (by simp only [leftSpine, List.mem_cons]; exact Or.inr hx)
            have hconf_M : ∀ x, x ∈ (BinaryTree.node a b c).toKeyList →
                x ∈ touchedKeys init (k + 1) → x ∉ touchedKeys init k →
                x ∈ leftSpine (rightSubtree (splay (BinaryTree.node a b c) k)) := by
              intro x hx hxT' hxT
              have hxs := hconfT x hxT' hxT
              simp only [leftSpine, List.mem_cons] at hxs
              rcases hxs with rfl | hxs
              · exact absurd (hrl_lt_rk x hx) (lt_irrefl x)
              · exact hxs
            have hrr_frozen : ∀ y ∈ rr.toKeyList, y ∈ touchedKeys init (k + 1) →
                y ∈ touchedKeys init k := by
              intro y hy hyT'
              by_contra hyT
              have hys := hconfT y hyT' hyT
              have hky : rk < y := forallTree_mem hf_rr y hy
              simp only [leftSpine, List.mem_cons] at hys
              rcases hys with rfl | hys
              · omega
              · have : y < rk := hrl_lt_rk y
                  (hMkeys y (leftSpine_subset_toKeyList _ y hys))
                omega
            refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
            · -- Full(T', M)
              exact vInvariant_splay_preserved (BinaryTree.node a b c) k _ _
                hb_rl hkrl hminrl ihFull_rl hcl_rl hmono hrlspine hnew_M hconf_M
            · -- NB(T', rr): frozen
              exact vInvariantNB_frozen _ _ rr hmono hrr_frozen ihNB_rr
            · -- closure root conjunct at rk
              exact fun h' => absurd (hmono rk hrkT) h'
            · -- closed(T', M)
              exact touchedClosed_splay_preserved (BinaryTree.node a b c) k _ _
                hb_rl hkrl hminrl hcl_rl hmono hrlspine hnew_M hconf_M
            · -- closed(T', rr): frozen
              exact touchedClosed_frozen _ _ rr hmono hrr_frozen hcl_rr


/-- **F2 COMPLETE — the process invariants** (Elmasry's Lemma 1, repo-variant, with the
boundary-bit strengthening): at every step `1 ≤ k ≤ n` of the sequential process, every
touched non-black node has `v ≥ 0` (boundary-ready), and touch-closure holds. -/
private theorem process_invariants (init : BinaryTree) (hbst : IsBST init)
    {n : Nat} (hkeys : ∀ m : Nat, m < n → m ∈ init.toKeyList) :
    ∀ k, 1 ≤ k → k ≤ n →
      vInvariantNB (touchedKeys init k) (rightSubtree (seqTree init k))
      ∧ touchedClosed (touchedKeys init k) (rightSubtree (seqTree init k)) := by
  intro k
  induction k with
  | zero => omega
  | succ k ih =>
      intro _ hkn
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        exact process_invariants_base init hbst
      · obtain ⟨hNB, hC⟩ := ih hkpos (by omega)
        exact process_invariants_step init hbst hkeys k hkpos (by omega) hNB hC


/-! ### The counting layer: the two-potential pay-per-link arithmetic

Elmasry's A-link-once argument fails for this top-down variant (verified by counterexample:
cheap links per node grow ~log n). Replacement (new, validated exactly): with
`Ω = Σh² + 4·Σ max(0, 2−v)`, EVERY link pays at least 2 from `Ω`:
the dropped parent's `v` rises by exactly one (relations (2)+(3)), so for `v_w ≤ 1` its
`max(0,2−v)`-term drops; for `v_w ≥ 2` the survivor jumps past 2 (`v_z' ≥ v_z + v_w`) and its
term drops; for `v_z ≥ 2` the `h²`-pair-exchange itself pays. Below: the per-level pay
inequality as pure count arithmetic. Chain counts at one zig-zig level (`lk, k` touched):
`a = tc(rs ll)`, `b = tc(rs lr)`, `c = tc(rs r)`, `m = tc(rs M)`; then
`h_z = a, g_z = h_w = 1+b, g_w = 1+c, h_z' = m, h_w' = b, g_z' = 2+c, g_w' = 1+c`;
`v_z = 1+b−a ≥ 0` and `v_w = c−b ≥ 0` (the F2 invariant), `m ≤ a+1` (relation (5)). -/

/-- Per-node Φ₂-term: `max(0, 2 − v)` written in ℕ via truncated subtraction,
with `g = 1 + (right chain count)` and `h = (left chain count)` for a touched node. -/
private def phi2Term (hcnt gcnt : Nat) : Nat := (hcnt + 2) - gcnt
-- `max(0, 2 − v) = max(0, 2 − (gcnt − hcnt)) = (hcnt + 2) − gcnt` (ℕ-truncated)

/-- **The pay-per-link inequality** (pure arithmetic): at one zig-zig level, the doubled-`h²`
pair exchange plus four times the Φ₂-term changes plus the payment 2 is non-positive.
Counts: `h_z = a, g_z = 1+b, h_w = 1+b, g_w = 1+c, h_z' = m, g_z' = 2+c, h_w' = b,
g_w' = 1+c`; hypotheses are the F2 invariant (`v_z, v_w ≥ 0`) and relation (5). -/
private theorem pay_per_link (a b c m : Nat)
    (hvz : a ≤ 1 + b)        -- v_z ≥ 0 (F2 invariant at the survivor)
    (hvw : b ≤ c)            -- v_w ≥ 0 (F2 invariant at the dropped parent)
    (h5 : m ≤ a + 1) :       -- relation (5)
    m ^ 2 + b ^ 2 + 4 * (phi2Term m (2 + c)) + 4 * (phi2Term b (1 + c)) + 2
      ≤ a ^ 2 + (1 + b) ^ 2 + 4 * (phi2Term a (1 + b)) + 4 * (phi2Term (1 + b) (1 + c)) := by
  simp only [phi2Term]
  have hm2 : m ^ 2 ≤ a ^ 2 + 2 * a + 1 := by
    calc m ^ 2 ≤ (a + 1) ^ 2 := Nat.pow_le_pow_left h5 2
      _ = a ^ 2 + 2 * a + 1 := by ring
  have hb2 : (1 + b) ^ 2 = b ^ 2 + 2 * b + 1 := by ring
  have hlin : 2 * a + 4 * ((m + 2) - (2 + c)) + 4 * ((b + 2) - (1 + c)) + 2
      ≤ 2 * b + 4 * ((a + 2) - (1 + b)) + 4 * (((1 + b) + 2) - (1 + c)) := by omega
  omega


/-- The Φ₂ potential over all nodes: a touched node with left subtree `l`, right subtree `r`
contributes `max(0, 2−v) = phi2Term (tc (rs l)) (1 + tc (rs r))`; untouched nodes contribute 0. -/
private def phi2Full (T : List Nat) : BinaryTree → Nat
  | .empty => 0
  | .node l k r =>
      (if k ∈ T then phi2Term (touchedCount T (rightSpine l))
        (1 + touchedCount T (rightSpine r)) else 0)
      + phi2Full T l + phi2Full T r

/-- The Φ₂ potential excluding the root and its right chain (the blacks). -/
private def phi2NB (T : List Nat) : BinaryTree → Nat
  | .empty => 0
  | .node l _ r => phi2Full T l + phi2NB T r

/-- The grand potential: `Ω = Σh² + 4·Φ₂` (doubled-h² plus four times the cheapness credit).
Every link pays 2 from `Ω` (`pay_per_link`); injections are `O(1)` per fresh touch. -/
private def omegaPot (T : List Nat) (t : BinaryTree) : Nat :=
  hSqPotential T t + 4 * phi2NB T t

/-! ### Φ₂ stability lemmas (integrated from the fan-out) -/

private theorem isBST_node_inv {l : BinaryTree} {k : Nat} {r : BinaryTree}
    (h : IsBST (.node l k r)) :
    ForallTree (fun x => x < k) l ∧ ForallTree (fun x => k < x) r ∧ IsBST l ∧ IsBST r := by
  cases h
  exact ⟨‹_›, ‹_›, ‹_›, ‹_›⟩

private theorem phi2Term_le_two (hcnt gcnt : Nat) (h : hcnt ≤ gcnt) :
    phi2Term hcnt gcnt ≤ 2 := by
  simp only [phi2Term]
  omega

private theorem phi2Term_le (hcnt gcnt : Nat) : phi2Term hcnt gcnt ≤ hcnt + 2 := by
  simp only [phi2Term]
  omega

private theorem phi2Term_succ_le (hcnt gcnt : Nat) :
    phi2Term hcnt (1 + gcnt) ≤ hcnt + 1 := by
  simp only [phi2Term]
  omega

private theorem touchedCount_singleton (T : List Nat) (k : Nat) :
    touchedCount T [k] = if k ∈ T then 1 else 0 := by
  by_cases hk : k ∈ T <;> simp [touchedCount, hk]

private theorem touchedCount_node (T : List Nat) (l : BinaryTree) (k : Nat)
    (r : BinaryTree) :
    touchedCount T (BinaryTree.node l k r).toKeyList
      = touchedCount T l.toKeyList + (if k ∈ T then 1 else 0)
        + touchedCount T r.toKeyList := by
  show touchedCount T (l.toKeyList ++ [k] ++ r.toKeyList) = _
  rw [touchedCount_append, touchedCount_append, touchedCount_singleton]

private theorem touchedCount_rightSpine_node (T : List Nat) (l : BinaryTree) (k : Nat)
    (r : BinaryTree) :
    touchedCount T (rightSpine (BinaryTree.node l k r))
      = (if k ∈ T then 1 else 0) + touchedCount T (rightSpine r) := by
  by_cases hk : k ∈ T
  · simp [rightSpine, touchedCount_cons_of_mem T _ hk, hk]
    omega
  · simp [rightSpine, touchedCount_cons_of_not_mem T _ hk, hk]

private theorem phi2Full_frozen (T T' : List Nat) :
    ∀ (u : BinaryTree),
      (∀ x ∈ T, x ∈ T') →
      (∀ y ∈ u.toKeyList, y ∈ T' → y ∈ T) →
      phi2Full T' u = phi2Full T u := by
  intro u
  induction u with
  | empty => intro _ _; rfl
  | node l k r ihl ihr =>
      intro hTT' hu
      have hl : ∀ y ∈ l.toKeyList, y ∈ T' → y ∈ T := fun y hy => hu y (mem_node_left hy)
      have hr : ∀ y ∈ r.toKeyList, y ∈ T' → y ∈ T := fun y hy => hu y (mem_node_right hy)
      have hk : k ∈ (BinaryTree.node l k r).toKeyList := by simp [BinaryTree.toKeyList]
      have hcl : touchedCount T' (rightSpine l) = touchedCount T (rightSpine l) :=
        touchedCount_frozen T T' (rightSpine l) hTT'
          (fun y hy => hl y (rightSpine_subset_toKeyList l y hy))
      have hcr : touchedCount T' (rightSpine r) = touchedCount T (rightSpine r) :=
        touchedCount_frozen T T' (rightSpine r) hTT'
          (fun y hy => hr y (rightSpine_subset_toKeyList r y hy))
      have hkiff : (k ∈ T') ↔ (k ∈ T) := ⟨hu k hk, hTT' k⟩
      simp only [phi2Full, hcl, hcr, hkiff, ihl hTT' hl, ihr hTT' hr]

private theorem phi2NB_frozen (T T' : List Nat) :
    ∀ (u : BinaryTree),
      (∀ x ∈ T, x ∈ T') →
      (∀ y ∈ u.toKeyList, y ∈ T' → y ∈ T) →
      phi2NB T' u = phi2NB T u := by
  intro u
  induction u with
  | empty => intro _ _; rfl
  | node l k r _ ihr =>
      intro hTT' hu
      have hl : ∀ y ∈ l.toKeyList, y ∈ T' → y ∈ T := fun y hy => hu y (mem_node_left hy)
      have hr : ∀ y ∈ r.toKeyList, y ∈ T' → y ∈ T := fun y hy => hu y (mem_node_right hy)
      simp only [phi2NB, phi2Full_frozen T T' l hTT' hl, ihr hTT' hr]

private theorem phi2Full_add_rightSpine_le (T : List Nat) :
    ∀ u : BinaryTree,
      phi2Full T u + touchedCount T (rightSpine u)
        ≤ 2 * touchedCount T u.toKeyList := by
  intro u
  induction u with
  | empty => simp [phi2Full, rightSpine, BinaryTree.toKeyList, touchedCount]
  | node l k r ihl ihr =>
      have hterm := phi2Term_succ_le (touchedCount T (rightSpine l))
        (touchedCount T (rightSpine r))
      rw [touchedCount_node, touchedCount_rightSpine_node]
      simp only [phi2Full]
      by_cases hk : k ∈ T <;> simp only [hk, if_true, if_false] <;> omega

private theorem phi2Full_le (T : List Nat) :
    ∀ u : BinaryTree, phi2Full T u ≤ 2 * touchedCount T u.toKeyList := by
  intro u
  have h := phi2Full_add_rightSpine_le T u
  omega

private theorem phi2NB_le_phi2Full (T : List Nat) :
    ∀ u : BinaryTree, phi2NB T u ≤ phi2Full T u := by
  intro u
  induction u with
  | empty => simp [phi2NB, phi2Full]
  | node l k r ihl ihr =>
      simp only [phi2NB, phi2Full]
      omega

private theorem phi2NB_le (T : List Nat) :
    ∀ u : BinaryTree, phi2NB T u ≤ 2 * touchedCount T u.toKeyList := by
  intro u
  exact le_trans (phi2NB_le_phi2Full T u) (phi2Full_le T u)

private theorem phi2Full_zero_of_untouched (T : List Nat) :
    ∀ (t : BinaryTree), (∀ y ∈ t.toKeyList, y ∉ T) → phi2Full T t = 0 := by
  intro t
  induction t with
  | empty => intro _; simp [phi2Full]
  | node l k r ihl ihr =>
    intro h
    have hk : k ∉ T := h k (by simp [BinaryTree.toKeyList])
    have hl : ∀ y ∈ l.toKeyList, y ∉ T := fun y hy => h y (by simp [BinaryTree.toKeyList, hy])
    have hr : ∀ y ∈ r.toKeyList, y ∉ T := fun y hy => h y (by simp [BinaryTree.toKeyList, hy])
    simp [phi2Full, hk, ihl hl, ihr hr]

private theorem phi2Full_of_spine_le (T : List Nat) :
    ∀ (u : BinaryTree), IsBST u →
      (∀ y ∈ u.toKeyList, y ∈ T → y ∈ leftSpine u) →
      (∀ x ∈ leftSpine u, x ∈ T) →
      phi2Full T u ≤ 2 * (leftSpine u).length := by
  intro u
  induction u with
  | empty => intro _ _ _; simp [phi2Full, leftSpine]
  | node l k r ihl ihr =>
    intro hbst hclosed hspine
    obtain ⟨hlk, hkr, hbl, hbr⟩ := isBST_node_inv hbst
    have hkT : k ∈ T := hspine k (by simp [leftSpine])
    have hrU : ∀ y ∈ r.toKeyList, y ∉ T := by
      intro y hy hyT
      have hky : k < y := forallTree_mem hkr y hy
      have hmem := hclosed y (mem_node_right hy) hyT
      simp only [leftSpine, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact lt_irrefl _ hky
      · have h1 : y ∈ l.toKeyList := leftSpine_subset_toKeyList l y hmem
        have h2 : y < k := forallTree_mem hlk y h1
        omega
    have hr0 : phi2Full T r = 0 := phi2Full_zero_of_untouched T r hrU
    have hg0 : touchedCount T (rightSpine r) = 0 :=
      touchedCount_zero T _ (fun y hy => hrU y (rightSpine_subset_toKeyList r y hy))
    have hh1 : touchedCount T (rightSpine l) ≤ 1 := by
      cases l with
      | empty => simp [rightSpine, touchedCount]
      | node ll lk lr =>
        obtain ⟨hll, hlr, _, _⟩ := isBST_node_inv hbl
        have htail : ∀ y ∈ rightSpine lr, y ∉ T := by
          intro y hy hyT
          have hylr : y ∈ lr.toKeyList := rightSpine_subset_toKeyList lr y hy
          have hlky : lk < y := forallTree_mem hlr y hylr
          have hyl : y ∈ (BinaryTree.node ll lk lr).toKeyList := mem_node_right hylr
          have hyk : y < k := forallTree_mem hlk y hyl
          have hmem := hclosed y (mem_node_left hyl) hyT
          simp only [leftSpine, List.mem_cons] at hmem
          rcases hmem with rfl | rfl | hmem
          · omega
          · omega
          · have h1 : y ∈ ll.toKeyList := leftSpine_subset_toKeyList ll y hmem
            have h2 : y < lk := forallTree_mem hll y h1
            omega
        have htail0 : touchedCount T (rightSpine lr) = 0 := touchedCount_zero T _ htail
        simp only [rightSpine]
        by_cases hlkT : lk ∈ T
        · rw [touchedCount_cons_of_mem T _ hlkT, htail0]
        · rw [touchedCount_cons_of_not_mem T _ hlkT, htail0]
          omega
    have hclosed' : ∀ y ∈ l.toKeyList, y ∈ T → y ∈ leftSpine l := by
      intro y hy hyT
      have hyk : y < k := forallTree_mem hlk y hy
      have hmem := hclosed y (mem_node_left hy) hyT
      simp only [leftSpine, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · omega
      · exact hmem
    have hspine' : ∀ x ∈ leftSpine l, x ∈ T := fun x hx => hspine x (by simp [leftSpine, hx])
    have hl_le : phi2Full T l ≤ 2 * (leftSpine l).length := ihl hbl hclosed' hspine'
    simp only [phi2Full, leftSpine, List.length_cons]
    rw [if_pos hkT, hr0, hg0]
    simp only [phi2Term]
    omega


private theorem phi2Term_mono_left {h h' : Nat} (g : Nat) (hh : h ≤ h') :
    phi2Term h g ≤ phi2Term h' g := by
  simp only [phi2Term]; omega

set_option maxHeartbeats 1600000 in
/-- **The Ω-restructure telescope** (phase (a) of the counting step, at *fixed* touched set):
one min-splay pays 2 per link from the interior potential `Σh² + 4·Φ₂`. Per zig-zig level this
is exactly `pay_per_link` (fed by the F2 invariant and relation (5)) composed with the
recursion; the root and zig cases only drop or shrink terms. -/
private theorem omega_restructure :
    ∀ (t : BinaryTree) (q : Nat) (T : List Nat),
      IsBST t → q ∈ t.toKeyList → (∀ y ∈ t.toKeyList, q ≤ y) →
      vInvariantFull T t →
      (∀ x ∈ leftSpine t, x ∈ T) →
      hSqPotential T (rightSubtree (splay t q)) + 4 * phi2Full T (rightSubtree (splay t q))
        + 2 * splayLinks t q
      ≤ hSqPotential T t + 4 * phi2Full T t
  | .empty, q, T, _, hmem, _, _, _ => by
      simp [BinaryTree.toKeyList] at hmem
  | .node l k r, q, T, hbst, hmem, hmin, hfull, hspineT => by
      rcases eq_or_ne q k with hqk | hqk
      · -- root: result = r; q's terms are dropped
        subst hqk
        have hleq : l = .empty := by
          cases l with
          | empty => rfl
          | node la lx lb =>
              exfalso
              have hlx_lt : lx < q := by
                cases hbst with
                | node _ _ _ hfl _ _ _ =>
                    exact (forallTree_iff_forall_mem.mp hfl) lx (by simp [BinaryTree.toKeyList])
              have := hmin lx (by simp [BinaryTree.toKeyList])
              omega
        subst hleq
        have hsp : splay (BinaryTree.node .empty q r) q = BinaryTree.node .empty q r := by
          simp only [splay.eq_def, ↓reduceIte]
        have hlk : splayLinks (BinaryTree.node .empty q r) q = 0 := by
          rw [splayLinks.eq_def]; simp
        rw [hsp, hlk]
        simp only [rightSubtree, hSqPotential, phi2Full, rightSpine, touchedCount_nil]
        omega
      · have hkmem : k ∈ (BinaryTree.node l k r).toKeyList := by simp [BinaryTree.toKeyList]
        have hqlt : q < k := lt_of_le_of_ne (hmin k hkmem) hqk
        have hql : q ∈ l.toKeyList := isBST_node_mem_left_of_lt_root hbst hmem hqlt
        have hbl : IsBST l := by cases hbst; assumption
        have hkT : k ∈ T := hspineT k (by simp [leftSpine])
        cases l with
        | empty => simp [BinaryTree.toKeyList] at hql
        | node ll lk lr =>
            have hminl : ∀ y ∈ (BinaryTree.node ll lk lr).toKeyList, q ≤ y := by
              intro y hy
              exact hmin y (by
                simp only [BinaryTree.toKeyList, List.mem_append] at hy ⊢; exact Or.inl (Or.inl hy))
            have hqlk : q ≤ lk := hminl lk (by simp [BinaryTree.toKeyList])
            have hlkT : lk ∈ T := hspineT lk (by simp [leftSpine])
            rcases eq_or_ne q lk with hqeq | hqne
            · -- zig: result = node lr k r; links = 0; terms shrink
              subst hqeq
              have hlleq : ll = .empty := by
                cases ll with
                | empty => rfl
                | node a b c =>
                    exfalso
                    have hb_lt : b < q := by
                      cases hbl with
                      | node _ _ _ hfl _ _ _ =>
                          exact (forallTree_iff_forall_mem.mp hfl) b
                            (by simp [BinaryTree.toKeyList])
                    have := hminl b (by simp [BinaryTree.toKeyList])
                    omega
              subst hlleq
              have hnk : ¬ q = k := hqk
              have hnq : ¬ q < q := lt_irrefl q
              have hsp : splay (BinaryTree.node (.node .empty q lr) k r) q
                  = BinaryTree.node .empty q (.node lr k r) := by
                rw [splay.eq_def]
                simp only [hnk, ↓reduceIte, hqlt, lt_self_iff_false, rotate, rotateRight]
              have hlk0 : splayLinks (BinaryTree.node (.node .empty q lr) k r) q = 0 := by
                rw [splayLinks.eq_def]
                simp only [hnk, ↓reduceIte, hqlt, lt_self_iff_false]
              rw [hsp, hlk0]
              simp only [rightSubtree, hSqPotential, phi2Full,
                rightSpine, touchedCount_nil, if_pos hkT, if_pos hlkT]
              -- old k-chain: q :: rs lr (q touched); new: rs lr
              rw [touchedCount_cons_of_mem T _ (hspineT q (by simp [leftSpine]))]
              have hmono := phi2Term_mono_left
                (1 + touchedCount T (rightSpine r))
                (Nat.le_succ (touchedCount T (rightSpine lr)))
              have hsq : (touchedCount T (rightSpine lr) + 1) ^ 2
                  = touchedCount T (rightSpine lr) ^ 2
                    + 2 * touchedCount T (rightSpine lr) + 1 := by ring
              simp only [phi2Term] at hmono ⊢
              omega
            · -- zig-zig: pay_per_link + recursion
              have hqllt : q < lk := lt_of_le_of_ne hqlk hqne
              have hqll : q ∈ ll.toKeyList :=
                isBST_node_mem_left_of_lt_root hbl hql hqllt
              cases ll with
              | empty => simp [BinaryTree.toKeyList] at hqll
              | node A B C =>
                  have hbll : IsBST (BinaryTree.node A B C) := by cases hbl; assumption
                  have hminll : ∀ y ∈ (BinaryTree.node A B C).toKeyList, q ≤ y := by
                    intro y hy
                    exact hminl y (by
                      simp only [BinaryTree.toKeyList, List.mem_append] at hy ⊢; exact Or.inl (Or.inl hy))
                  have hS := splay_min_eq_node_empty (BinaryTree.node A B C) q hbll hqll hminll
                  have hsp := splay_min_zigzig_shape A C lr r B lk k q hqk hqlt hqllt hS
                  -- links: zig-zig level adds one
                  have hlks : splayLinks (BinaryTree.node (.node (.node A B C) lk lr) k r) q
                      = splayLinks (BinaryTree.node A B C) q + 1 := by
                    rw [splayLinks.eq_def]
                    simp only [hqk, ↓reduceIte, hqlt, hqllt]
                  -- spine of ll ⊆ T for the recursion and rel-5
                  have hspine_ll : ∀ x ∈ leftSpine (BinaryTree.node A B C), x ∈ T := by
                    intro x hx
                    exact hspineT x (by
                      simp only [leftSpine, List.mem_cons] at hx ⊢; exact Or.inr (Or.inr hx))
                  -- the F2 values: a ≤ 1 + b and b ≤ c
                  have hvz : touchedCount T (rightSpine (BinaryTree.node A B C))
                      ≤ 1 + touchedCount T (rightSpine lr) := by
                    have hvAt_lk : vAt T (BinaryTree.node A B C) lk lr := hfull.2.1.1
                    have := hvAt_lk hlkT
                    omega
                  have hvw : touchedCount T (rightSpine lr)
                      ≤ touchedCount T (rightSpine r) := by
                    have hvAt_k : vAt T (BinaryTree.node (.node A B C) lk lr) k r := hfull.1
                    have h0 := hvAt_k hkT
                    simp only [rightSpine_node_eq] at h0
                    rw [touchedCount_cons_of_mem T _ hlkT] at h0
                    omega
                  -- relation (5) for the recursive result
                  have h5 : touchedCount T (rightSpine
                        (rightSubtree (splay (BinaryTree.node A B C) q)))
                      ≤ touchedCount T (rightSpine (BinaryTree.node A B C)) + 1 :=
                    relation5_touchedCount_rightSpine_splay_min T (BinaryTree.node A B C) q
                      hbll hqll hminll hspine_ll
                  -- the keystone
                  have hpay := pay_per_link
                    (touchedCount T (rightSpine (BinaryTree.node A B C)))
                    (touchedCount T (rightSpine lr))
                    (touchedCount T (rightSpine r))
                    (touchedCount T (rightSpine
                      (rightSubtree (splay (BinaryTree.node A B C) q))))
                    hvz hvw h5
                  -- the recursion
                  have hIH := omega_restructure (BinaryTree.node A B C) q T
                    hbll hqll hminll hfull.2.1.2.1 hspine_ll
                  -- assemble: explicit one-level unfoldings (rfl), boundary chains only
                  have ek : touchedCount T (rightSpine (BinaryTree.node lr k r))
                      = 1 + touchedCount T (rightSpine r) := by
                    rw [rightSpine_node_eq, touchedCount_cons_of_mem T _ hkT]; omega
                  have el : touchedCount T
                        (rightSpine (BinaryTree.node (.node A B C) lk lr))
                      = 1 + touchedCount T (rightSpine lr) := by
                    rw [rightSpine_node_eq, touchedCount_cons_of_mem T _ hlkT]; omega
                  rw [hsp, hlks]
                  show hSqPotential T (BinaryTree.node
                        (rightSubtree (splay (BinaryTree.node A B C) q)) lk
                        (.node lr k r))
                      + 4 * phi2Full T (BinaryTree.node
                        (rightSubtree (splay (BinaryTree.node A B C) q)) lk
                        (.node lr k r))
                      + 2 * (splayLinks (BinaryTree.node A B C) q + 1)
                    ≤ hSqPotential T (BinaryTree.node (.node (.node A B C) lk lr) k r)
                      + 4 * phi2Full T (BinaryTree.node (.node (.node A B C) lk lr) k r)
                  have hsq_new : hSqPotential T (BinaryTree.node
                        (rightSubtree (splay (BinaryTree.node A B C) q)) lk
                        (.node lr k r))
                      = (touchedCount T (rightSpine
                          (rightSubtree (splay (BinaryTree.node A B C) q)))) ^ 2
                        + hSqPotential T (rightSubtree (splay (BinaryTree.node A B C) q))
                        + ((touchedCount T (rightSpine lr)) ^ 2
                          + hSqPotential T lr + hSqPotential T r) := rfl
                  have hsq_old : hSqPotential T
                        (BinaryTree.node (.node (.node A B C) lk lr) k r)
                      = (touchedCount T (rightSpine
                          (BinaryTree.node (.node A B C) lk lr))) ^ 2
                        + ((touchedCount T (rightSpine (BinaryTree.node A B C))) ^ 2
                          + hSqPotential T (BinaryTree.node A B C) + hSqPotential T lr)
                        + hSqPotential T r := rfl
                  have hp2_new : phi2Full T (BinaryTree.node
                        (rightSubtree (splay (BinaryTree.node A B C) q)) lk
                        (.node lr k r))
                      = (if lk ∈ T then phi2Term (touchedCount T (rightSpine
                            (rightSubtree (splay (BinaryTree.node A B C) q))))
                          (1 + touchedCount T (rightSpine (BinaryTree.node lr k r)))
                          else 0)
                        + phi2Full T (rightSubtree (splay (BinaryTree.node A B C) q))
                        + ((if k ∈ T then phi2Term (touchedCount T (rightSpine lr))
                            (1 + touchedCount T (rightSpine r)) else 0)
                          + phi2Full T lr + phi2Full T r) := rfl
                  have hp2_old : phi2Full T
                        (BinaryTree.node (.node (.node A B C) lk lr) k r)
                      = (if k ∈ T then phi2Term (touchedCount T (rightSpine
                            (BinaryTree.node (.node A B C) lk lr)))
                          (1 + touchedCount T (rightSpine r)) else 0)
                        + ((if lk ∈ T then phi2Term (touchedCount T (rightSpine
                              (BinaryTree.node A B C)))
                            (1 + touchedCount T (rightSpine lr)) else 0)
                          + phi2Full T (BinaryTree.node A B C) + phi2Full T lr)
                        + phi2Full T r := rfl
                  rw [hsq_new, hsq_old, hp2_new, hp2_old]
                  simp only [if_pos hkT, if_pos hlkT]
                  rw [ek, el]
                  have e1 : 1 + (1 + touchedCount T (rightSpine r))
                      = 2 + touchedCount T (rightSpine r) := by omega
                  rw [e1]
                  omega


/-- The h²-potential excluding the root and its right chain (the blacks): the root's h-term
can jump unboundedly per step, and black nodes never participate in links. -/
private def hSqNB (T : List Nat) : BinaryTree → Nat
  | .empty => 0
  | .node l _ r => hSqPotential T l + hSqNB T r

/-- The black-excluded grand potential `Ω = Σh² + 4·Φ₂` (doubled scale). -/
private def omegaNB (T : List Nat) (t : BinaryTree) : Nat :=
  hSqNB T t + 4 * phi2NB T t

set_option maxHeartbeats 800000 in
/-- **Real-shape restructure step** (phase (a) at fixed touched set): at step `k` the
black parts (`rk`, `rr`) cancel exactly, and the interior min-splay of `rl` pays via
`omega_restructure`; the zagZig wrapper link costs the per-splay constant 2. -/
private theorem omegaNB_step_restructure (init : BinaryTree) (hbst : IsBST init)
    {n : Nat} (hkeys : ∀ m : Nat, m < n → m ∈ init.toKeyList)
    (k : Nat) (hk1 : 1 ≤ k) (hkn : k < n)
    (ihNB : vInvariantNB (touchedKeys init k) (rightSubtree (seqTree init k))) :
    omegaNB (touchedKeys init k) (rightSubtree (seqTree init (k + 1)))
      + 2 * splayLinks (seqTree init k) k
    ≤ omegaNB (touchedKeys init k) (rightSubtree (seqTree init k)) + 2 := by
  have hroot : rootKey (seqTree init k) = some (k - 1) := by
    have h := seqTree_rootKey init hbst hkeys (k - 1) (by omega)
    rwa [Nat.sub_add_cancel hk1] at h
  obtain ⟨L, R, heq⟩ : ∃ L R, seqTree init k = .node L (k - 1) R := by
    cases hh : seqTree init k with
    | empty => rw [hh] at hroot; simp [rootKey] at hroot
    | node a b c =>
        rw [hh] at hroot; simp only [rootKey, Option.some.injEq] at hroot
        exact ⟨a, c, by rw [hroot]⟩
  have hbstk : IsBST (BinaryTree.node L (k - 1) R) := heq ▸ seqTree_isBST init hbst k
  have hbR : IsBST R := by cases hbstk; assumption
  have hmemiff : ∀ x, x ∈ R.toKeyList ↔ (k - 1 < x ∧ x ∈ init.toKeyList) := by
    intro x
    have h := rightSubtree_seqTree_succ_mem_iff init hbst hkeys (k - 1) (by omega) x
    rw [Nat.sub_add_cancel hk1, heq] at h
    simpa [rightSubtree] using h
  have hkR : k ∈ R.toKeyList := (hmemiff k).mpr ⟨by omega, hkeys k hkn⟩
  have hkminR : ∀ y ∈ R.toKeyList, k ≤ y := fun y hy => by
    have := (hmemiff y).mp hy; omega
  have hRsub : rightSubtree (seqTree init k) = R := by rw [heq]; rfl
  have hRspine : ∀ x ∈ leftSpine R, x ∈ touchedKeys init k := by
    intro x hx
    exact spine_subset_touchedKeys init k hk1 x (by rwa [hRsub])
  rw [hRsub] at ihNB ⊢
  have hstep : seqTree init (k + 1) = splay (seqTree init k) k := rfl
  have hnqm : ¬ k = k - 1 := by omega
  have hnqltm : ¬ k < k - 1 := by omega
  cases R with
  | empty => simp [BinaryTree.toKeyList] at hkR
  | node rl rk rr =>
      have hrk_ge : k ≤ rk := hkminR rk (by simp [BinaryTree.toKeyList])
      have hf_rl : ForallTree (fun x => x < rk) rl := by cases hbR; assumption
      have hb_rl : IsBST rl := by cases hbR; assumption
      rcases eq_or_ne k rk with hkrk | hkrk
      · -- case A: single zag; everything cancels; links = 0
        subst hkrk
        have hrleq : rl = .empty := by
          cases rl with
          | empty => rfl
          | node x y z =>
              exfalso
              have h1 : y < k := forallTree_mem hf_rl y (by simp [BinaryTree.toKeyList])
              have h2 : k ≤ y := hkminR y (by simp [BinaryTree.toKeyList])
              omega
        subst hrleq
        have hnq : ¬ k < k := lt_irrefl k
        have hsp : splay (BinaryTree.node L (k - 1) (.node .empty k rr)) k
            = BinaryTree.node (.node L (k - 1) .empty) k rr := by
          rw [splay.eq_def]
          simp only [hnqm, ↓reduceIte, hnqltm, lt_self_iff_false, rotate, rotateLeft]
        have hR' : rightSubtree (seqTree init (k + 1)) = rr := by
          rw [hstep, heq, hsp]; rfl
        have hlk0 : splayLinks (BinaryTree.node L (k - 1) (.node .empty k rr)) k = 0 := by
          rw [splayLinks.eq_def]
          simp only [hnqm, ↓reduceIte, hnqltm, lt_self_iff_false]
        rw [hR', heq, hlk0]
        simp only [omegaNB, hSqNB, phi2NB, hSqPotential, phi2Full]
        omega
      · -- case B: zagZig wrapper + interior min-splay of rl
        have hkltrk : k < rk := lt_of_le_of_ne hrk_ge hkrk
        have hkrl : k ∈ rl.toKeyList := isBST_node_mem_left_of_lt_root hbR hkR hkltrk
        cases rl with
        | empty => simp [BinaryTree.toKeyList] at hkrl
        | node a b c =>
            have hminrl : ∀ y ∈ (BinaryTree.node a b c).toKeyList, k ≤ y := by
              intro y hy
              refine hkminR y ?_
              rw [BinaryTree.toKeyList]
              exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hy)))
            have hS := splay_min_eq_node_empty (BinaryTree.node a b c) k hb_rl hkrl hminrl
            have hsp : splay (BinaryTree.node L (k - 1)
                (.node (.node a b c) rk rr)) k
                = BinaryTree.node (.node L (k - 1) .empty) k
                    (.node (rightSubtree (splay (BinaryTree.node a b c) k)) rk rr) := by
              rw [splay.eq_def]
              simp only [if_neg hnqm, if_neg hnqltm, if_pos hkltrk]
              rw [hS]
              simp only [rotate, rotateLeft, rotateRight, rightSubtree]
            have hR' : rightSubtree (seqTree init (k + 1))
                = BinaryTree.node (rightSubtree (splay (BinaryTree.node a b c) k)) rk rr := by
              rw [hstep, heq, hsp]; rfl
            have hlks : splayLinks (BinaryTree.node L (k - 1)
                (.node (.node a b c) rk rr)) k
                = splayLinks (BinaryTree.node a b c) k + 1 := by
              rw [splayLinks.eq_def]
              simp only [hnqm, ↓reduceIte, hnqltm, hkltrk]
            have hrlspine : ∀ x ∈ leftSpine (BinaryTree.node a b c),
                x ∈ touchedKeys init k := by
              intro x hx
              exact hRspine x (by
                simp only [leftSpine, List.mem_cons] at hx ⊢; tauto)
            have hfull_rl : vInvariantFull (touchedKeys init k) (BinaryTree.node a b c) :=
              ihNB.1
            have hcore := omega_restructure (BinaryTree.node a b c) k (touchedKeys init k)
              hb_rl hkrl hminrl hfull_rl hrlspine
            rw [hR', heq, hlks]
            simp only [omegaNB, hSqNB, phi2NB]
            omega



/-! ### Final-stretch lemmas (integrated from the fan-out) -/

private theorem touchedCountFrozenG (T T2 : List Nat) (hTT2 : ∀ x ∈ T, x ∈ T2) :
    ∀ (c : List Nat), (∀ y ∈ c, y ∈ T2 → y ∈ T) →
      touchedCount T2 c = touchedCount T c := by
  intro c
  induction c with
  | nil => intro _; rfl
  | cons y c ih =>
      intro h
      have hrest : ∀ z ∈ c, z ∈ T2 → z ∈ T := fun z hz => h z (by simp [hz])
      by_cases hy : y ∈ T2
      · have hyT : y ∈ T := h y (by simp) hy
        rw [touchedCount_cons_of_mem T2 c hy, touchedCount_cons_of_mem T c hyT, ih hrest]
      · have hyT : y ∉ T := fun hT => hy (hTT2 y hT)
        rw [touchedCount_cons_of_not_mem T2 c hy,
          touchedCount_cons_of_not_mem T c hyT, ih hrest]


private theorem phi2FullFrozenG (T T2 : List Nat) (hTT2 : ∀ x ∈ T, x ∈ T2) :
    ∀ (u : BinaryTree), (∀ y ∈ u.toKeyList, y ∈ T2 → y ∈ T) →
      phi2Full T2 u = phi2Full T u := by
  intro u
  induction u with
  | empty => intro _; rfl
  | node l k r ihl ihr =>
      intro h
      have hl : ∀ y ∈ l.toKeyList, y ∈ T2 → y ∈ T := by
        intro y hy; exact h y (by simp [BinaryTree.toKeyList]; tauto)
      have hr : ∀ y ∈ r.toKeyList, y ∈ T2 → y ∈ T := by
        intro y hy; exact h y (by simp [BinaryTree.toKeyList]; tauto)
      have hcl : touchedCount T2 (rightSpine l) = touchedCount T (rightSpine l) :=
        touchedCountFrozenG T T2 hTT2 _
          (fun y hy => hl y (rightSpine_subset_toKeyList l y hy))
      have hcr : touchedCount T2 (rightSpine r) = touchedCount T (rightSpine r) :=
        touchedCountFrozenG T T2 hTT2 _
          (fun y hy => hr y (rightSpine_subset_toKeyList r y hy))
      have hk : k ∈ T2 → k ∈ T := h k (by simp [BinaryTree.toKeyList])
      by_cases hkT : k ∈ T
      · have hkT2 : k ∈ T2 := hTT2 k hkT
        simp [phi2Full, hkT, hkT2, hcl, hcr, ihl hl, ihr hr]
      · have hkT2 : k ∉ T2 := fun h2 => hkT (hk h2)
        simp [phi2Full, hkT, hkT2, ihl hl, ihr hr]


private theorem hSq_frozen (T T2 : List Nat) (hTT2 : ∀ x ∈ T, x ∈ T2) :
    ∀ (u : BinaryTree), (∀ y ∈ u.toKeyList, y ∈ T2 → y ∈ T) →
      hSqPotential T2 u = hSqPotential T u := by
  intro u
  induction u with
  | empty => intro _; rfl
  | node l k r ihl ihr =>
      intro h
      have hl : ∀ y ∈ l.toKeyList, y ∈ T2 → y ∈ T := by
        intro y hy; exact h y (by simp [BinaryTree.toKeyList]; tauto)
      have hr : ∀ y ∈ r.toKeyList, y ∈ T2 → y ∈ T := by
        intro y hy; exact h y (by simp [BinaryTree.toKeyList]; tauto)
      have hcl : touchedCount T2 (rightSpine l) = touchedCount T (rightSpine l) :=
        touchedCountFrozenG T T2 hTT2 _
          (fun y hy => hl y (rightSpine_subset_toKeyList l y hy))
      simp [hSqPotential, hcl, ihl hl, ihr hr]


private theorem phi2Full_untouched (T : List Nat) :
    ∀ (u : BinaryTree), (∀ y ∈ u.toKeyList, y ∉ T) → phi2Full T u = 0 := by
  intro u
  induction u with
  | empty => intro _; rfl
  | node l k r ihl ihr =>
      intro h
      have hk : k ∉ T := h k (by simp [BinaryTree.toKeyList])
      have hl := ihl (fun y hy => h y (by simp [BinaryTree.toKeyList]; tauto))
      have hr := ihr (fun y hy => h y (by simp [BinaryTree.toKeyList]; tauto))
      simp [phi2Full, hk, hl, hr]


private theorem hSq_untouched (T : List Nat) :
    ∀ (u : BinaryTree), (∀ y ∈ u.toKeyList, y ∉ T) → hSqPotential T u = 0 := by
  intro u
  induction u with
  | empty => intro _; rfl
  | node l k r ihl ihr =>
      intro h
      have hl := ihl (fun y hy => h y (by simp [BinaryTree.toKeyList]; tauto))
      have hr := ihr (fun y hy => h y (by simp [BinaryTree.toKeyList]; tauto))
      have hc : touchedCount T (rightSpine l) = 0 :=
        touchedCount_zero T _ (fun y hy => h y (by
          have hmem := rightSpine_subset_toKeyList l y hy
          simp [BinaryTree.toKeyList]; tauto))
      simp [hSqPotential, hc, hl, hr]

/-! ### Left-chain comparison (the key root-term bound)

For a subtree `l` sitting under the access spine, with confinement of fresh
touched keys to `leftSpine l`:
* the new chain count grows by at most the reserved boundary bit, and
* when the boundary bit is 1 (fresh spine head), the old count is 0 and the
  new count is at most 1. -/


private theorem chain_compare (T T2 : List Nat) (hTT2 : ∀ x ∈ T, x ∈ T2) :
    ∀ (l : BinaryTree), IsBST l → touchedClosed T l →
      (∀ x ∈ leftSpine l, x ∈ T2) →
      (∀ x, x ∈ l.toKeyList → x ∈ T2 → x ∉ T → x ∈ leftSpine l) →
      touchedCount T2 (rightSpine l)
          ≤ touchedCount T (rightSpine l) + boundaryBit T (leftSpine l)
        ∧ (boundaryBit T (leftSpine l) = 1 →
            touchedCount T (rightSpine l) = 0 ∧ touchedCount T2 (rightSpine l) ≤ 1) := by
  intro l hbst htc hspine hconf
  cases l with
  | empty => simp [rightSpine, leftSpine, boundaryBit, touchedCount]
  | node l1 hd l2 =>
      have h1hd : ForallTree (fun x => x < hd) l1 := by cases hbst; assumption
      have hhd2 : ForallTree (fun x => hd < x) l2 := by cases hbst; assumption
      simp only [touchedClosed] at htc
      obtain ⟨hclosed, -, -⟩ := htc
      have hhdT2 : hd ∈ T2 := hspine hd (by simp [leftSpine])
      -- the tail of the right spine of l (inside l2) is frozen
      have hfroz : ∀ y ∈ rightSpine l2, y ∈ T2 → y ∈ T := by
        intro y hy hy2
        by_contra hyT
        have hyl2 : y ∈ l2.toKeyList := rightSpine_subset_toKeyList l2 y hy
        have hhdy : hd < y := forallTree_mem hhd2 y hyl2
        have hmem := hconf y (by simp [BinaryTree.toKeyList]; tauto) hy2 hyT
        simp only [leftSpine, List.mem_cons] at hmem
        rcases hmem with h | h
        · omega
        · have hyl1 : y ∈ l1.toKeyList := leftSpine_subset_toKeyList l1 y h
          have : y < hd := forallTree_mem h1hd y hyl1
          omega
      have hc2 : touchedCount T2 (rightSpine l2) = touchedCount T (rightSpine l2) :=
        touchedCountFrozenG T T2 hTT2 _ hfroz
      have hrsl : rightSpine (BinaryTree.node l1 hd l2) = hd :: rightSpine l2 := rfl
      have hA : touchedCount T2 (rightSpine (BinaryTree.node l1 hd l2))
          = touchedCount T (rightSpine l2) + 1 := by
        rw [hrsl, touchedCount_cons_of_mem T2 _ hhdT2, hc2]
      by_cases hhdT : hd ∈ T
      · have hB : touchedCount T (rightSpine (BinaryTree.node l1 hd l2))
            = touchedCount T (rightSpine l2) + 1 := by
          rw [hrsl, touchedCount_cons_of_mem T _ hhdT]
        have hbit : boundaryBit T (leftSpine (BinaryTree.node l1 hd l2)) = 0 := by
          simp [leftSpine, boundaryBit, hhdT]
        rw [hA, hB, hbit]
        omega
      · obtain ⟨-, hunt2⟩ := hclosed hhdT
        have hz : touchedCount T (rightSpine l2) = 0 :=
          touchedCount_zero T _ (fun y hy => hunt2 y (rightSpine_subset_toKeyList l2 y hy))
        have hB : touchedCount T (rightSpine (BinaryTree.node l1 hd l2)) = 0 := by
          rw [hrsl, touchedCount_cons_of_not_mem T _ hhdT, hz]
        have hbit : boundaryBit T (leftSpine (BinaryTree.node l1 hd l2)) = 1 := by
          simp [leftSpine, boundaryBit, hhdT]
        rw [hA, hB, hbit]
        omega

/-! ### Main growth deltas -/


private theorem phi2Full_growth_le (T T2 : List Nat) :
    ∀ (u : BinaryTree), IsBST u →
      touchedClosed T u →
      (∀ x ∈ T, x ∈ T2) →
      (∀ x ∈ leftSpine u, x ∈ T2) →
      (∀ x, x ∈ u.toKeyList → x ∈ T2 → x ∉ T → x ∈ leftSpine u) →
      phi2Full T2 u + boundaryBit T (leftSpine u)
        ≤ phi2Full T u + 3 * ((leftSpine u).filter (· ∉ T)).length := by
  intro u
  induction u with
  | empty => intro _ _ _ _ _
             simp only [phi2Full, boundaryBit, leftSpine, add_zero, decide_not, List.filter_nil,
               List.length_nil, mul_zero, le_refl]
  | node l k r ihl _ =>
    intro hbst htc hTT2 hspine hconf
    have hlk : ForallTree (fun x => x < k) l := by cases hbst; assumption
    have hkr : ForallTree (fun x => k < x) r := by cases hbst; assumption
    have hbstl : IsBST l := by cases hbst; assumption
    simp only [touchedClosed] at htc
    obtain ⟨hclosed, htcl, -⟩ := htc
    have hkT2 : k ∈ T2 := hspine k (by simp only [leftSpine, List.mem_cons, true_or])
    have hspinel : ∀ x ∈ leftSpine l, x ∈ T2 := by
      intro x hx; exact hspine x (by simp only [leftSpine, List.mem_cons, hx, or_true])
    have hconfl : ∀ x, x ∈ l.toKeyList → x ∈ T2 → x ∉ T → x ∈ leftSpine l := by
      intro x hxl hx2 hxT
      have hxk : x < k := forallTree_mem hlk x hxl
      have hmem := hconf x (mem_node_left hxl) hx2 hxT
      simp only [leftSpine, List.mem_cons] at hmem
      rcases hmem with h | h
      · omega
      · exact h
    -- the right subtree is frozen: a fresh touched r-key would be on the spine,
    -- impossible by BST order
    have hfrozenr : ∀ y ∈ r.toKeyList, y ∈ T2 → y ∈ T := by
      intro y hy hy2
      by_contra hyT
      have hky : k < y := forallTree_mem hkr y hy
      have hmem := hconf y (mem_node_right hy) hy2 hyT
      simp only [leftSpine, List.mem_cons] at hmem
      rcases hmem with h | h
      · omega
      · have hyl : y ∈ l.toKeyList := leftSpine_subset_toKeyList l y h
        have : y < k := forallTree_mem hlk y hyl
        omega
    have hPr : phi2Full T2 r = phi2Full T r := phi2FullFrozenG T T2 hTT2 r hfrozenr
    have hcr : touchedCount T2 (rightSpine r) = touchedCount T (rightSpine r) :=
      touchedCountFrozenG T T2 hTT2 _
        (fun y hy => hfrozenr y (rightSpine_subset_toKeyList r y hy))
    have ihl' := ihl hbstl htcl hTT2 hspinel hconfl
    have hchain := chain_compare T T2 hTT2 l hbstl htcl hspinel hconfl
    by_cases hkT : k ∈ T
    · -- root already touched: boundary bit 0, root key not in the filter
      have hbit : boundaryBit T (leftSpine (BinaryTree.node l k r)) = 0 := by
        simp only [boundaryBit, leftSpine, hkT, ↓reduceIte]
      have hfilter : ((leftSpine (BinaryTree.node l k r)).filter (· ∉ T)).length
          = ((leftSpine l).filter (· ∉ T)).length := by
        simp only [decide_not, leftSpine, hkT, decide_true, Bool.not_true, Bool.false_eq_true,
          not_false_eq_true, List.filter_cons_of_neg]
      have hterm : phi2Term (touchedCount T2 (rightSpine l))
            (1 + touchedCount T (rightSpine r))
          ≤ phi2Term (touchedCount T (rightSpine l))
              (1 + touchedCount T (rightSpine r))
            + boundaryBit T (leftSpine l) := by
        have h1 := hchain.1
        simp only [phi2Term]
        omega
      rw [hbit, hfilter]
      simp only [phi2Full]
      rw [if_pos hkT2, if_pos hkT, hcr, hPr]
      omega
    · -- fresh root: everything below is untouched in T; budget 3 pays
      obtain ⟨huntl, huntr⟩ := hclosed hkT
      have hbit : boundaryBit T (leftSpine (BinaryTree.node l k r)) = 1 := by
        simp only [boundaryBit, leftSpine, hkT, ↓reduceIte]
      have hfilter : ((leftSpine (BinaryTree.node l k r)).filter (· ∉ T)).length
          = ((leftSpine l).filter (· ∉ T)).length + 1 := by
        simp only [decide_not, leftSpine, hkT, decide_false, Bool.not_false,
          List.filter_cons_of_pos, List.length_cons]
      have hPl0 : phi2Full T l = 0 := phi2Full_untouched T l huntl
      have hPr0 : phi2Full T r = 0 := phi2Full_untouched T r huntr
      have hBl0 : touchedCount T (rightSpine l) = 0 :=
        touchedCount_zero T _ (fun y hy => huntl y (rightSpine_subset_toKeyList l y hy))
      have hbl1 : boundaryBit T (leftSpine l) ≤ 1 := boundaryBit_le_one T _
      have hA1 : touchedCount T2 (rightSpine l) ≤ 1 := by
        have h1 := hchain.1
        omega
      have hroot : phi2Term (touchedCount T2 (rightSpine l))
          (1 + touchedCount T2 (rightSpine r)) ≤ 2 := by
        simp only [phi2Term]
        omega
      rw [hbit, hfilter]
      simp only [phi2Full]
      rw [if_pos hkT2, if_neg hkT]
      omega


private theorem hSq_growth_le (T T2 : List Nat) :
    ∀ (u : BinaryTree), IsBST u →
      touchedClosed T u →
      (∀ x ∈ T, x ∈ T2) →
      (∀ x ∈ leftSpine u, x ∈ T2) →
      (∀ x, x ∈ u.toKeyList → x ∈ T2 → x ∉ T → x ∈ leftSpine u) →
      hSqPotential T2 u + boundaryBit T (leftSpine u)
        ≤ hSqPotential T u + 2 * ((leftSpine u).filter (· ∉ T)).length := by
  intro u
  induction u with
  | empty => intro _ _ _ _ _; simp [hSqPotential, leftSpine, boundaryBit]
  | node l k r ihl _ =>
    intro hbst htc hTT2 hspine hconf
    have hlk : ForallTree (fun x => x < k) l := by cases hbst; assumption
    have hkr : ForallTree (fun x => k < x) r := by cases hbst; assumption
    have hbstl : IsBST l := by cases hbst; assumption
    simp only [touchedClosed] at htc
    obtain ⟨hclosed, htcl, -⟩ := htc
    have hkT2 : k ∈ T2 := hspine k (by simp [leftSpine])
    have hspinel : ∀ x ∈ leftSpine l, x ∈ T2 := by
      intro x hx; exact hspine x (by simp [leftSpine, hx])
    have hconfl : ∀ x, x ∈ l.toKeyList → x ∈ T2 → x ∉ T → x ∈ leftSpine l := by
      intro x hxl hx2 hxT
      have hxk : x < k := forallTree_mem hlk x hxl
      have hmem := hconf x (by simp [BinaryTree.toKeyList]; tauto) hx2 hxT
      simp only [leftSpine, List.mem_cons] at hmem
      rcases hmem with h | h
      · omega
      · exact h
    have hfrozenr : ∀ y ∈ r.toKeyList, y ∈ T2 → y ∈ T := by
      intro y hy hy2
      by_contra hyT
      have hky : k < y := forallTree_mem hkr y hy
      have hmem := hconf y (by simp [BinaryTree.toKeyList]; tauto) hy2 hyT
      simp only [leftSpine, List.mem_cons] at hmem
      rcases hmem with h | h
      · omega
      · have hyl : y ∈ l.toKeyList := leftSpine_subset_toKeyList l y h
        have : y < k := forallTree_mem hlk y hyl
        omega
    have hSr : hSqPotential T2 r = hSqPotential T r := hSq_frozen T T2 hTT2 r hfrozenr
    have ihl' := ihl hbstl htcl hTT2 hspinel hconfl
    have hchain := chain_compare T T2 hTT2 l hbstl htcl hspinel hconfl
    have hbl1 : boundaryBit T (leftSpine l) ≤ 1 := boundaryBit_le_one T _
    -- squared root-term comparison: the bit pays the 0 → 1 jump
    have hsq : touchedCount T2 (rightSpine l) ^ 2
        ≤ touchedCount T (rightSpine l) ^ 2 + boundaryBit T (leftSpine l) := by
      obtain ⟨h1, h2⟩ := hchain
      by_cases hb : boundaryBit T (leftSpine l) = 1
      · obtain ⟨hB0, hA1⟩ := h2 hb
        rw [hB0, hb]
        have hcases : touchedCount T2 (rightSpine l) = 0
            ∨ touchedCount T2 (rightSpine l) = 1 := by omega
        rcases hcases with h | h <;> simp only [h] <;> omega
      · have hb0 : boundaryBit T (leftSpine l) = 0 := by omega
        rw [hb0] at h1 ⊢
        have h1' : touchedCount T2 (rightSpine l) ≤ touchedCount T (rightSpine l) := by
          omega
        simpa only [add_zero, ge_iff_le] using Nat.pow_le_pow_left h1' 2
    by_cases hkT : k ∈ T
    · have hbit : boundaryBit T (leftSpine (BinaryTree.node l k r)) = 0 := by
        simp only [boundaryBit, leftSpine, hkT, ↓reduceIte]
      have hfilter : ((leftSpine (BinaryTree.node l k r)).filter (· ∉ T)).length
          = ((leftSpine l).filter (· ∉ T)).length := by
        simp only [decide_not, leftSpine, hkT, decide_true, Bool.not_true, Bool.false_eq_true,
          not_false_eq_true, List.filter_cons_of_neg]
      rw [hbit, hfilter]
      simp only [hSqPotential]
      rw [hSr]
      omega
    · obtain ⟨huntl, huntr⟩ := hclosed hkT
      have hbit : boundaryBit T (leftSpine (BinaryTree.node l k r)) = 1 := by
        simp only [boundaryBit, leftSpine, hkT, ↓reduceIte]
      have hfilter : ((leftSpine (BinaryTree.node l k r)).filter (· ∉ T)).length
          = ((leftSpine l).filter (· ∉ T)).length + 1 := by
        simp only [decide_not, leftSpine, hkT, decide_false, Bool.not_false,
          List.filter_cons_of_pos, List.length_cons]
      have hSl0 : hSqPotential T l = 0 := hSq_untouched T l huntl
      have hSr0 : hSqPotential T r = 0 := hSq_untouched T r huntr
      have hBl0 : touchedCount T (rightSpine l) = 0 :=
        touchedCount_zero T _ (fun y hy => huntl y (rightSpine_subset_toKeyList l y hy))
      have hB20 : touchedCount T (rightSpine l) ^ 2 = 0 := by
        rw [hBl0]; rfl
      rw [hbit, hfilter]
      simp only [hSqPotential]
      rw [hSr]
      omega


private theorem forallTree_node_inv {p : Nat → Prop} {l : BinaryTree} {k : Nat} {r : BinaryTree}
    (h : ForallTree p (.node l k r)) :
    ForallTree p l ∧ p k ∧ ForallTree p r := by
  cases h
  exact ⟨by assumption, by assumption, by assumption⟩


private theorem mem_keyList_node {l : BinaryTree} {k : Nat} {r : BinaryTree} {x : Nat} :
    x ∈ (BinaryTree.node l k r).toKeyList ↔
      x ∈ l.toKeyList ∨ x = k ∨ x ∈ r.toKeyList := by
  show x ∈ l.toKeyList ++ [k] ++ r.toKeyList ↔ _
  constructor
  · intro h
    rcases List.mem_append.1 h with h | h
    · rcases List.mem_append.1 h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (List.mem_singleton.1 h))
    · exact Or.inr (Or.inr h)
  · intro h
    rcases h with h | h | h
    · exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl h)))
    · exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr (List.mem_singleton.2 h))))
    · exact List.mem_append.2 (Or.inr h)


private theorem touchedCountZeroImp {T : List Nat} : ∀ {c : List Nat},
    (∀ y ∈ c, y ∉ T) → touchedCount T c = 0 := by
  intro c
  induction c with
  | nil => intro _; rfl
  | cons a c ih =>
      intro h
      rw [touchedCount_cons_of_not_mem T c (h a (by simp))]
      exact ih (fun y hy => h y (by simp [hy]))


private theorem hSq_zero_of_untouched (T : List Nat) : ∀ (u : BinaryTree),
    (∀ x ∈ u.toKeyList, x ∉ T) → hSqPotential T u = 0 := by
  intro u
  induction u with
  | empty => intro _; rfl
  | node l k r ihl ihr =>
      intro h
      have hl : ∀ x ∈ l.toKeyList, x ∉ T := fun x hx =>
        h x (mem_keyList_node.2 (Or.inl hx))
      have hr : ∀ x ∈ r.toKeyList, x ∉ T := fun x hx =>
        h x (mem_keyList_node.2 (Or.inr (Or.inr hx)))
      have h0 : touchedCount T (rightSpine l) = 0 :=
        touchedCountZeroImp (fun y hy => hl y (rightSpine_subset_toKeyList l y hy))
      simp [hSqPotential, ihl hl, ihr hr, h0]

/-! ## Main theorem -/


private theorem hSq_of_spine_le (T : List Nat) :
    ∀ (u : BinaryTree), IsBST u →
      (∀ y ∈ u.toKeyList, y ∈ T → y ∈ leftSpine u) →
      (∀ x ∈ leftSpine u, x ∈ T) →
      hSqPotential T u ≤ (leftSpine u).length := by
  intro u
  induction u with
  | empty =>
      intro _ _ _
      simp [hSqPotential, leftSpine]
  | node l k r ihl ihr =>
      intro hbst hconf hspine
      obtain ⟨hlk, hkr, hbl, hbr⟩ := isBST_node_inv hbst
      have hLS : leftSpine (BinaryTree.node l k r) = k :: leftSpine l := rfl
      -- Every key of the right subtree is untouched.
      have hr_untouched : ∀ x ∈ r.toKeyList, x ∉ T := by
        intro x hxr hxT
        have hkx : k < x := forallTree_mem hkr x hxr
        have hxu : x ∈ (BinaryTree.node l k r).toKeyList :=
          mem_keyList_node.2 (Or.inr (Or.inr hxr))
        have hxs := hconf x hxu hxT
        rw [hLS] at hxs
        rcases List.mem_cons.1 hxs with h | h
        · omega
        · have hxl : x ∈ l.toKeyList := leftSpine_subset_toKeyList l x h
          have hxk : x < k := forallTree_mem hlk x hxl
          omega
      have hsr : hSqPotential T r = 0 := hSq_zero_of_untouched T r hr_untouched
      -- The root's history chain contains at most one touched element.
      have hroot : touchedCount T (rightSpine l) ≤ 1 := by
        cases l with
        | empty =>
            simp [rightSpine, touchedCount]
        | node l1 hd l2 =>
            obtain ⟨h1, h2, hb1, hb2⟩ := isBST_node_inv hbl
            obtain ⟨hlk1, hlkk, hlk2⟩ := forallTree_node_inv hlk
            have htail : ∀ y ∈ rightSpine l2, y ∉ T := by
              intro y hy hyT
              have hyl2 : y ∈ l2.toKeyList := rightSpine_subset_toKeyList l2 y hy
              have hhdy : hd < y := forallTree_mem h2 y hyl2
              have hyk : y < k := forallTree_mem hlk2 y hyl2
              have hyu : y ∈ (BinaryTree.node (BinaryTree.node l1 hd l2) k r).toKeyList :=
                mem_keyList_node.2 (Or.inl (mem_keyList_node.2 (Or.inr (Or.inr hyl2))))
              have hys := hconf y hyu hyT
              rw [show leftSpine (BinaryTree.node (BinaryTree.node l1 hd l2) k r)
                    = k :: hd :: leftSpine l1 from rfl] at hys
              rcases List.mem_cons.1 hys with h | h
              · omega
              · rcases List.mem_cons.1 h with h | h
                · omega
                · have hyl1 : y ∈ l1.toKeyList := leftSpine_subset_toKeyList l1 y h
                  have : y < hd := forallTree_mem h1 y hyl1
                  omega
            have h0 : touchedCount T (rightSpine l2) = 0 := touchedCountZeroImp htail
            have hRS : rightSpine (BinaryTree.node l1 hd l2) = hd :: rightSpine l2 := rfl
            rw [hRS]
            by_cases hhd : hd ∈ T
            · rw [touchedCount_cons_of_mem T _ hhd, h0]
            · rw [touchedCount_cons_of_not_mem T _ hhd, h0]
              omega
      -- Restricted hypotheses for the left subtree.
      have hconf_l : ∀ y ∈ l.toKeyList, y ∈ T → y ∈ leftSpine l := by
        intro y hyl hyT
        have hyu : y ∈ (BinaryTree.node l k r).toKeyList :=
          mem_keyList_node.2 (Or.inl hyl)
        have hys := hconf y hyu hyT
        rw [hLS] at hys
        rcases List.mem_cons.1 hys with h | h
        · exfalso
          have : y < k := forallTree_mem hlk y hyl
          omega
        · exact h
      have hspine_l : ∀ x ∈ leftSpine l, x ∈ T := by
        intro x hx
        apply hspine
        rw [hLS]
        exact List.mem_cons_of_mem _ hx
      have hle := ihl hbl hconf_l hspine_l
      have hpow : touchedCount T (rightSpine l) ^ 2 ≤ 1 := by
        calc touchedCount T (rightSpine l) ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left hroot 2
          _ = 1 := one_pow 2
      have hgoal : hSqPotential T (BinaryTree.node l k r)
          = touchedCount T (rightSpine l) ^ 2 + hSqPotential T l + hSqPotential T r := rfl
      rw [hgoal, hLS, hsr]
      simp only [List.length_cons]
      omega



private theorem leftSpine_chain_gt :
    ∀ (t : BinaryTree), IsBST t → (leftSpine t).IsChain (· > ·) := by
  intro t h
  induction h with
  | left => exact List.isChain_nil
  | node key l r hfl _hfr _hl _hr ihl _ihr =>
    cases l with
    | empty => exact List.isChain_singleton key
    | node ll lk lr =>
      cases hfl with
      | node _ _ _ _hfll hk _hflr =>
        simp only [leftSpine] at ihl ⊢
        exact List.isChain_cons_cons.mpr ⟨hk, ihl⟩


private theorem leftSpine_nodup (t : BinaryTree) (h : IsBST t) : (leftSpine t).Nodup := by
  have hpw : (leftSpine t).Pairwise (· > ·) :=
    List.isChain_iff_pairwise.mp (leftSpine_chain_gt t h)
  exact hpw.imp (fun {a b} hab => ne_of_gt hab)


private theorem filter_length_le_card (T : List Nat) (L : List Nat)
    (hN : L.Nodup) (S : Finset Nat) (hsub : ∀ x ∈ L, x ∉ T → x ∈ S) :
    (L.filter (· ∉ T)).length ≤ S.card := by
  classical
  have hfN : (L.filter (· ∉ T)).Nodup := hN.filter _
  have hmem : ∀ x ∈ L.filter (· ∉ T), x ∈ S := by
    intro x hx
    rw [List.mem_filter] at hx
    exact hsub x hx.1 (by simpa using hx.2)
  calc (L.filter (· ∉ T)).length
      = (L.filter (· ∉ T)).toFinset.card := (List.toFinset_card_of_nodup hfN).symm
    _ ≤ S.card := Finset.card_le_card (fun x hx => hmem x (List.mem_toFinset.mp hx))


set_option maxHeartbeats 800000 in
/-- Touch-closure is preserved by the restructure at a *fixed* touched set: every spine node is
touched, so the moved blocks all hang under touched nodes; no closure implication changes. -/
private theorem touchedClosed_restructure_fixedT :
    ∀ (t : BinaryTree) (q : Nat) (T : List Nat),
      IsBST t → q ∈ t.toKeyList → (∀ y ∈ t.toKeyList, q ≤ y) →
      touchedClosed T t →
      (∀ x ∈ leftSpine t, x ∈ T) →
      touchedClosed T (rightSubtree (splay t q))
  | .empty, q, T, _, hmem, _, _, _ => by
      simp [BinaryTree.toKeyList] at hmem
  | .node l k r, q, T, hbst, hmem, hmin, hclosed, hspineT => by
      rcases eq_or_ne q k with hqk | hqk
      · subst hqk
        have hleq : l = .empty := by
          cases l with
          | empty => rfl
          | node la lx lb =>
              exfalso
              have hlx_lt : lx < q := by
                cases hbst with
                | node _ _ _ hfl _ _ _ =>
                    exact (forallTree_iff_forall_mem.mp hfl) lx (by simp [BinaryTree.toKeyList])
              have := hmin lx (by simp [BinaryTree.toKeyList])
              omega
        subst hleq
        have hsp : splay (BinaryTree.node .empty q r) q = BinaryTree.node .empty q r := by
          simp only [splay.eq_def, ↓reduceIte]
        rw [hsp]
        exact hclosed.2.2
      · have hkmem : k ∈ (BinaryTree.node l k r).toKeyList := by simp [BinaryTree.toKeyList]
        have hqlt : q < k := lt_of_le_of_ne (hmin k hkmem) hqk
        have hql : q ∈ l.toKeyList := isBST_node_mem_left_of_lt_root hbst hmem hqlt
        have hbl : IsBST l := by cases hbst; assumption
        have hkT : k ∈ T := hspineT k (by simp [leftSpine])
        cases l with
        | empty => simp [BinaryTree.toKeyList] at hql
        | node ll lk lr =>
            have hminl : ∀ y ∈ (BinaryTree.node ll lk lr).toKeyList, q ≤ y := by
              intro y hy
              exact hmin y (by
                simp only [BinaryTree.toKeyList, List.mem_append] at hy ⊢; exact Or.inl (Or.inl hy))
            have hqlk : q ≤ lk := hminl lk (by simp [BinaryTree.toKeyList])
            have hlkT : lk ∈ T := hspineT lk (by simp [leftSpine])
            rcases eq_or_ne q lk with hqeq | hqne
            · subst hqeq
              have hlleq : ll = .empty := by
                cases ll with
                | empty => rfl
                | node a b c =>
                    exfalso
                    have hb_lt : b < q := by
                      cases hbl with
                      | node _ _ _ hfl _ _ _ =>
                          exact (forallTree_iff_forall_mem.mp hfl) b
                            (by simp [BinaryTree.toKeyList])
                    have := hminl b (by simp [BinaryTree.toKeyList])
                    omega
              subst hlleq
              have hnk : ¬ q = k := hqk
              have hnq : ¬ q < q := lt_irrefl q
              have hsp : splay (BinaryTree.node (.node .empty q lr) k r) q
                  = BinaryTree.node .empty q (.node lr k r) := by
                rw [splay.eq_def]
                simp only [hnk, ↓reduceIte, hqlt, lt_self_iff_false, rotate, rotateRight]
              rw [hsp]
              simp only [rightSubtree]
              exact ⟨fun hk' => absurd hkT hk', hclosed.2.1.2.2, hclosed.2.2⟩
            · have hqllt : q < lk := lt_of_le_of_ne hqlk hqne
              have hqll : q ∈ ll.toKeyList :=
                isBST_node_mem_left_of_lt_root hbl hql hqllt
              cases ll with
              | empty => simp [BinaryTree.toKeyList] at hqll
              | node a b c =>
                  have hbll : IsBST (BinaryTree.node a b c) := by cases hbl; assumption
                  have hminll : ∀ y ∈ (BinaryTree.node a b c).toKeyList, q ≤ y := by
                    intro y hy
                    exact hminl y (by
                      simp only [BinaryTree.toKeyList, List.mem_append] at hy ⊢; exact Or.inl (Or.inl hy))
                  have hS := splay_min_eq_node_empty (BinaryTree.node a b c) q hbll hqll hminll
                  have hsp := splay_min_zigzig_shape a c lr r b lk k q hqk hqlt hqllt hS
                  rw [hsp]
                  simp only [rightSubtree]
                  have hclosedM := touchedClosed_restructure_fixedT (BinaryTree.node a b c)
                    q T hbll hqll hminll hclosed.2.1.2.1
                    (fun x hx => hspineT x (by
                      simp only [leftSpine, List.mem_cons] at hx ⊢; exact Or.inr (Or.inr hx)))
                  exact ⟨fun hlk' => absurd hlkT hlk', hclosedM,
                    fun hk' => absurd hkT hk',
                    hclosed.2.1.2.2, hclosed.2.2⟩


private theorem hSqNB_frozen (T T' : List Nat) :
    ∀ (u : BinaryTree),
      (∀ x ∈ T, x ∈ T') →
      (∀ y ∈ u.toKeyList, y ∈ T' → y ∈ T) →
      hSqNB T' u = hSqNB T u := by
  intro u
  induction u with
  | empty => intro _ _; rfl
  | node l k r _ ihr =>
      intro hTT' hu
      have hl : ∀ y ∈ l.toKeyList, y ∈ T' → y ∈ T := fun y hy => hu y (mem_node_left hy)
      have hr : ∀ y ∈ r.toKeyList, y ∈ T' → y ∈ T := fun y hy => hu y (mem_node_right hy)
      simp only [hSqNB, hSq_frozen T T' hTT' l hl, ihr hTT' hr]

/-- **Ω growth bound** (phase (b)): extending the touched set, with new touches confined to the
left spine, costs at most `14` per fresh spine key. -/
private theorem omegaNB_growth (T T' : List Nat) (u : BinaryTree)
    (hbst : IsBST u)
    (hclosed : touchedClosed T u)
    (hmono : ∀ x ∈ T, x ∈ T')
    (hspine : ∀ x ∈ leftSpine u, x ∈ T')
    (hconf : ∀ x, x ∈ u.toKeyList → x ∈ T' → x ∉ T → x ∈ leftSpine u) :
    omegaNB T' u ≤ omegaNB T u + 14 * ((leftSpine u).filter (· ∉ T)).length := by
  cases u with
  | empty => simp [omegaNB, hSqNB, phi2NB]
  | node l k r =>
      have hf_l : ForallTree (fun x => x < k) l := by cases hbst; assumption
      have hf_r : ForallTree (fun x => k < x) r := by cases hbst; assumption
      have hb_l : IsBST l := by cases hbst; assumption
      have hcl_l : touchedClosed T l := hclosed.2.1
      have hspine_l : ∀ x ∈ leftSpine l, x ∈ T' := fun x hx =>
        hspine x (by simp only [leftSpine, List.mem_cons]; tauto)
      have hconf_l : ∀ x, x ∈ l.toKeyList → x ∈ T' → x ∉ T → x ∈ leftSpine l := by
        intro x hx hxT' hxT
        have hxs := hconf x (mem_node_left hx) hxT' hxT
        simp only [leftSpine, List.mem_cons] at hxs
        rcases hxs with rfl | hxs
        · exact absurd (forallTree_mem hf_l x hx) (lt_irrefl x)
        · exact hxs
      have hr_frozen : ∀ y ∈ r.toKeyList, y ∈ T' → y ∈ T := by
        intro y hy hyT'
        by_contra hyT
        have hys := hconf y (mem_node_right hy) hyT' hyT
        have hky : k < y := forallTree_mem hf_r y hy
        simp only [leftSpine, List.mem_cons] at hys
        rcases hys with rfl | hys
        · omega
        · have : y < k := forallTree_mem hf_l y (leftSpine_subset_toKeyList l y hys)
          omega
      have hg1 := phi2Full_growth_le T T' l hb_l hcl_l hmono hspine_l hconf_l
      have hg2 := hSq_growth_le T T' l hb_l hcl_l hmono hspine_l hconf_l
      have hfr1 : phi2NB T' r = phi2NB T r := phi2NB_frozen T T' r hmono hr_frozen
      have hfr2 : hSqNB T' r = hSqNB T r := hSqNB_frozen T T' r hmono hr_frozen
      have hfsub : ((leftSpine l).filter (· ∉ T)).length
          ≤ ((leftSpine (BinaryTree.node l k r)).filter (· ∉ T)).length := by
        simp only [leftSpine, List.filter_cons]
        split <;> simp
      simp only [omegaNB, hSqNB, phi2NB, hfr1, hfr2]
      omega


set_option maxHeartbeats 1000000 in
/-- **The combined per-step Ω bound**: restructure (phase (a)) plus touched-growth (phase (b)).
Every step pays its links from `Ω` up to `2 + 14·fresh`. -/
private theorem omegaNB_step (init : BinaryTree) (hbst : IsBST init)
    {n : Nat} (hkeys : ∀ m : Nat, m < n → m ∈ init.toKeyList)
    (k : Nat) (hk1 : 1 ≤ k) (hkn : k < n)
    (ihNB : vInvariantNB (touchedKeys init k) (rightSubtree (seqTree init k)))
    (ihC : touchedClosed (touchedKeys init k) (rightSubtree (seqTree init k))) :
    omegaNB (touchedKeys init (k + 1)) (rightSubtree (seqTree init (k + 1)))
      + 2 * splayLinks (seqTree init k) k
    ≤ omegaNB (touchedKeys init k) (rightSubtree (seqTree init k)) + 2
      + 14 * ((leftSpine (rightSubtree (seqTree init (k + 1)))).filter
          (· ∉ touchedKeys init k)).length := by
  -- phase (a)
  have hA := omegaNB_step_restructure init hbst hkeys k hk1 hkn ihNB
  -- closed (T_k, R_{k+1}) for phase (b): real-shape fixed-T closure
  have hclosed' : touchedClosed (touchedKeys init k)
      (rightSubtree (seqTree init (k + 1))) := by
    have hroot : rootKey (seqTree init k) = some (k - 1) := by
      have h := seqTree_rootKey init hbst hkeys (k - 1) (by omega)
      rwa [Nat.sub_add_cancel hk1] at h
    obtain ⟨L, R, heq⟩ : ∃ L R, seqTree init k = .node L (k - 1) R := by
      cases hh : seqTree init k with
      | empty => rw [hh] at hroot; simp [rootKey] at hroot
      | node a b c =>
          rw [hh] at hroot; simp only [rootKey, Option.some.injEq] at hroot
          exact ⟨a, c, by rw [hroot]⟩
    have hbstk : IsBST (BinaryTree.node L (k - 1) R) := heq ▸ seqTree_isBST init hbst k
    have hbR : IsBST R := by cases hbstk; assumption
    have hmemiff : ∀ x, x ∈ R.toKeyList ↔ (k - 1 < x ∧ x ∈ init.toKeyList) := by
      intro x
      have h := rightSubtree_seqTree_succ_mem_iff init hbst hkeys (k - 1) (by omega) x
      rw [Nat.sub_add_cancel hk1, heq] at h
      simpa [rightSubtree] using h
    have hkR : k ∈ R.toKeyList := (hmemiff k).mpr ⟨by omega, hkeys k hkn⟩
    have hkminR : ∀ y ∈ R.toKeyList, k ≤ y := fun y hy => by
      have := (hmemiff y).mp hy; omega
    have hRsub : rightSubtree (seqTree init k) = R := by rw [heq]; rfl
    have hRspine : ∀ x ∈ leftSpine R, x ∈ touchedKeys init k := by
      intro x hx
      exact spine_subset_touchedKeys init k hk1 x (by rwa [hRsub])
    rw [hRsub] at ihC
    have hstep : seqTree init (k + 1) = splay (seqTree init k) k := rfl
    have hnqm : ¬ k = k - 1 := by omega
    have hnqltm : ¬ k < k - 1 := by omega
    cases R with
    | empty => simp [BinaryTree.toKeyList] at hkR
    | node rl rk rr =>
        have hrk_ge : k ≤ rk := hkminR rk (by simp [BinaryTree.toKeyList])
        have hf_rl : ForallTree (fun x => x < rk) rl := by cases hbR; assumption
        have hb_rl : IsBST rl := by cases hbR; assumption
        rcases eq_or_ne k rk with hkrk | hkrk
        · subst hkrk
          have hrleq : rl = .empty := by
            cases rl with
            | empty => rfl
            | node x y z =>
                exfalso
                have h1 : y < k := forallTree_mem hf_rl y (by simp [BinaryTree.toKeyList])
                have h2 : k ≤ y := hkminR y (by simp [BinaryTree.toKeyList])
                omega
          subst hrleq
          have hnq : ¬ k < k := lt_irrefl k
          have hsp : splay (BinaryTree.node L (k - 1) (.node .empty k rr)) k
              = BinaryTree.node (.node L (k - 1) .empty) k rr := by
            rw [splay.eq_def]
            simp only [hnqm, ↓reduceIte, hnqltm, lt_self_iff_false, rotate, rotateLeft]
          have hR' : rightSubtree (seqTree init (k + 1)) = rr := by
            rw [hstep, heq, hsp]; rfl
          rw [hR']
          exact ihC.2.2
        · have hkltrk : k < rk := lt_of_le_of_ne hrk_ge hkrk
          have hkrl : k ∈ rl.toKeyList := isBST_node_mem_left_of_lt_root hbR hkR hkltrk
          cases rl with
          | empty => simp [BinaryTree.toKeyList] at hkrl
          | node a b c =>
              have hminrl : ∀ y ∈ (BinaryTree.node a b c).toKeyList, k ≤ y := by
                intro y hy
                exact hkminR y (by
                  simp only [BinaryTree.toKeyList, List.mem_append] at hy ⊢; exact Or.inl (Or.inl hy))
              have hS := splay_min_eq_node_empty (BinaryTree.node a b c) k hb_rl hkrl hminrl
              have hsp : splay (BinaryTree.node L (k - 1)
                  (.node (.node a b c) rk rr)) k
                  = BinaryTree.node (.node L (k - 1) .empty) k
                      (.node (rightSubtree (splay (BinaryTree.node a b c) k)) rk rr) := by
                rw [splay.eq_def]
                simp only [if_neg hnqm, if_neg hnqltm, if_pos hkltrk]
                rw [hS]
                simp only [rotate, rotateLeft, rotateRight, rightSubtree]
              have hR' : rightSubtree (seqTree init (k + 1))
                  = BinaryTree.node (rightSubtree (splay (BinaryTree.node a b c) k)) rk rr := by
                rw [hstep, heq, hsp]; rfl
              rw [hR']
              have hrkT : rk ∈ touchedKeys init k := hRspine rk (by simp [leftSpine])
              have hclosedM := touchedClosed_restructure_fixedT (BinaryTree.node a b c) k
                (touchedKeys init k) hb_rl hkrl hminrl ihC.2.1
                (fun x hx => hRspine x (by
                  simp only [leftSpine, List.mem_cons] at hx ⊢; exact Or.inr hx))
              exact ⟨fun h' => absurd hrkT h', hclosedM, ihC.2.2⟩
  -- phase (b)
  have hB := omegaNB_growth (touchedKeys init k) (touchedKeys init (k + 1))
    (rightSubtree (seqTree init (k + 1)))
    (rightSubtree_isBST_of_isBST (seqTree_isBST init hbst (k + 1)))
    hclosed'
    (touchedKeys_mono init k)
    (spine_subset_touchedKeys init (k + 1) (by omega))
    (fun x _ hxT' hxT => touchedKeys_succ_diff init k x hxT' hxT)
  omega


/-- Two links cost at most the rotation count. -/
private theorem two_splayLinks_le_cost :
    ∀ (t : BinaryTree) (q : Nat), (2 * splayLinks t q : ℝ) ≤ splay.cost t q
  | .empty, q => by simp [splay.cost, splayLinks]
  | .node l k r, q => by
      rw [splay.cost.eq_def, splayLinks.eq_def]
      by_cases hqk : q = k
      · simp [hqk]
      · by_cases hlt : q < k
        · cases l with
          | empty => simp [hqk, hlt]
          | node ll lk lr =>
              by_cases hqlk : q < lk
              · cases ll with
                | empty => simp [hqk, hlt, hqlk]
                | node a b c =>
                    have ih := two_splayLinks_le_cost (BinaryTree.node a b c) q
                    simp only [hqk, hlt, hqlk, if_neg, if_pos, if_true, if_false]
                    push_cast
                    linarith
              · by_cases hlkq : lk < q
                · cases lr with
                  | empty => simp [hqk, hlt, hqlk, hlkq]
                  | node a b c =>
                      have ih := two_splayLinks_le_cost (BinaryTree.node a b c) q
                      simp only [hqk, hlt, hqlk, hlkq, if_neg, if_pos, if_true, if_false]
                      push_cast
                      linarith
                · simp [hqk, hlt, hqlk, hlkq]
        · cases r with
          | empty => simp [hqk, hlt]
          | node rl rk rr =>
              by_cases hqrk : q < rk
              · cases rl with
                | empty => simp [hqk, hlt, hqrk]
                | node a b c =>
                    have ih := two_splayLinks_le_cost (BinaryTree.node a b c) q
                    simp only [hqk, hlt, hqrk, if_neg, if_pos, if_true, if_false]
                    push_cast
                    linarith
              · by_cases hrkq : rk < q
                · cases rr with
                  | empty => simp [hqk, hlt, hqrk, hrkq]
                  | node a b c =>
                      have ih := two_splayLinks_le_cost (BinaryTree.node a b c) q
                      simp only [hqk, hlt, hqrk, hrkq, if_neg, if_pos, if_true, if_false]
                      push_cast
                      linarith
                · simp [hqk, hlt, hqrk, hrkq]


private theorem hSqNB_le_hSq (T : List Nat) :
    ∀ u : BinaryTree, hSqNB T u ≤ hSqPotential T u := by
  intro u
  induction u with
  | empty => simp [hSqNB, hSqPotential]
  | node l k r _ ihr =>
      simp only [hSqNB, hSqPotential]
      omega

/-- The base bound: at step 1 the touched set is exactly the spine, so `Ω ≤ 9n`. -/
private theorem omegaNB_base_le (init : BinaryTree) (hbst : IsBST init) :
    omegaNB (touchedKeys init 1) (rightSubtree (seqTree init 1))
      ≤ 9 * init.num_nodes := by
  have hT1 : touchedKeys init 1 = leftSpine (rightSubtree (seqTree init 1)) := by
    show touchedKeys init 0 ++ leftSpine (rightSubtree (seqTree init 1))
        = leftSpine (rightSubtree (seqTree init 1))
    simp [touchedKeys]
  have hbR : IsBST (rightSubtree (seqTree init 1)) :=
    rightSubtree_isBST_of_isBST (seqTree_isBST init hbst 1)
  have hconf : ∀ y ∈ (rightSubtree (seqTree init 1)).toKeyList,
      y ∈ touchedKeys init 1 → y ∈ leftSpine (rightSubtree (seqTree init 1)) := by
    intro y _ hy; rwa [hT1] at hy
  have hspine : ∀ x ∈ leftSpine (rightSubtree (seqTree init 1)),
      x ∈ touchedKeys init 1 := by
    intro x hx; rwa [hT1]
  have h1 := hSq_of_spine_le (touchedKeys init 1) (rightSubtree (seqTree init 1))
    hbR hconf hspine
  have h2 := phi2Full_of_spine_le (touchedKeys init 1) (rightSubtree (seqTree init 1))
    hbR hconf hspine
  have h3 := hSqNB_le_hSq (touchedKeys init 1) (rightSubtree (seqTree init 1))
  have h4 := phi2NB_le_phi2Full (touchedKeys init 1) (rightSubtree (seqTree init 1))
  have h5 := leftSpine_length_le_num_nodes (rightSubtree (seqTree init 1))
  have h6 := rightSubtree_num_nodes_le (seqTree init 1)
  have h7 : (seqTree init 1).num_nodes = init.num_nodes := seqTree_num_nodes init 1
  simp only [omegaNB]
  omega

/-- Keys of the initial tree lie below `n`. -/
private theorem init_keys_lt (init : BinaryTree) (hbst : IsBST init)
    {n : Nat} (hnum : init.num_nodes = n)
    (hkeys : ∀ m : Nat, m < n → m ∈ init.toKeyList) :
    ∀ x ∈ init.toKeyList, x < n := by
  intro x hx
  by_contra hxn
  push_neg at hxn
  -- toFinset has ≥ n+1 elements (range n plus x) but length = n
  have hnodup : init.toKeyList.Nodup := isBST_toKeyList_nodup hbst
  have hlen : init.toKeyList.length = n := by rw [toKeyList_length, hnum]
  have hsub : Finset.range n ∪ {x} ⊆ init.toKeyList.toFinset := by
    intro y hy
    rw [Finset.mem_union] at hy
    rcases hy with hy | hy
    · rw [Finset.mem_range] at hy
      exact List.mem_toFinset.mpr (hkeys y hy)
    · rw [Finset.mem_singleton] at hy
      subst hy
      exact List.mem_toFinset.mpr hx
  have hcard1 : (Finset.range n ∪ {x}).card = n + 1 := by
    rw [Finset.union_comm, Finset.card_union_of_disjoint]
    · simp only [Finset.card_singleton, Finset.card_range]
      omega
    · simp [Finset.disjoint_singleton_left, Finset.mem_range]
      omega
  have hcard2 : init.toKeyList.toFinset.card = n := by
    rw [List.toFinset_card_of_nodup hnodup, hlen]
  have := Finset.card_le_card hsub
  omega

/-- Fresh keys at step `k` are paid by the growth of the distinct-touched measure. -/
private theorem fresh_le_mu (init : BinaryTree) (hbst : IsBST init)
    {n : Nat} (hnum : init.num_nodes = n)
    (hkeys : ∀ m : Nat, m < n → m ∈ init.toKeyList)
    (k : Nat) (hkn : k < n) :
    ((leftSpine (rightSubtree (seqTree init (k + 1)))).filter
        (· ∉ touchedKeys init k)).length
      + ((Finset.range n).filter (fun x => x ∈ touchedKeys init k)).card
    ≤ ((Finset.range n).filter (fun x => x ∈ touchedKeys init (k + 1))).card := by
  classical
  set L := leftSpine (rightSubtree (seqTree init (k + 1))) with hL
  have hbR : IsBST (rightSubtree (seqTree init (k + 1))) :=
    rightSubtree_isBST_of_isBST (seqTree_isBST init hbst (k + 1))
  have hN : L.Nodup := leftSpine_nodup _ hbR
  have hLkeys : ∀ x ∈ L, x < n := by
    intro x hx
    have h1 : x ∈ (rightSubtree (seqTree init (k + 1))).toKeyList :=
      leftSpine_subset_toKeyList _ x hx
    have h2 : x ∈ (seqTree init (k + 1)).toKeyList :=
      mem_toKeyList_of_mem_rightSubtree h1
    rw [seqTree_toKeyList] at h2
    exact init_keys_lt init hbst hnum hkeys x h2
  have hLT' : ∀ x ∈ L, x ∈ touchedKeys init (k + 1) :=
    spine_subset_touchedKeys init (k + 1) (by omega)
  set S := ((Finset.range n).filter (fun x => x ∈ touchedKeys init (k + 1)))
      \ ((Finset.range n).filter (fun x => x ∈ touchedKeys init k)) with hS
  have hsub : ∀ x ∈ L, x ∉ touchedKeys init k → x ∈ S := by
    intro x hx hxn
    rw [hS, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter]
    exact ⟨⟨Finset.mem_range.mpr (hLkeys x hx), hLT' x hx⟩,
      fun hc => hxn hc.2⟩
  have hmain := filter_length_le_card (touchedKeys init k) L hN S hsub
  have hsubset : ((Finset.range n).filter (fun x => x ∈ touchedKeys init k))
      ⊆ ((Finset.range n).filter (fun x => x ∈ touchedKeys init (k + 1))) := by
    intro y hy
    rw [Finset.mem_filter] at hy ⊢
    exact ⟨hy.1, touchedKeys_mono init k y hy.2⟩
  have hcard : S.card
      + ((Finset.range n).filter (fun x => x ∈ touchedKeys init k)).card
      = ((Finset.range n).filter (fun x => x ∈ touchedKeys init (k + 1))).card := by
    rw [hS]
    exact Finset.card_sdiff_add_card_eq_card hsubset
  omega

set_option maxHeartbeats 1600000 in
/-- **The link telescope**: total links over `[1, n)` are linear. -/
private theorem links_telescope (init : BinaryTree) (hbst : IsBST init)
    {n : Nat} (hnum : init.num_nodes = n)
    (hkeys : ∀ m : Nat, m < n → m ∈ init.toKeyList) :
    ∀ N, 1 ≤ N → N ≤ n →
      2 * (∑ k ∈ Finset.Ico 1 N, splayLinks (seqTree init k) k)
        + omegaNB (touchedKeys init N) (rightSubtree (seqTree init N))
        + 14 * ((Finset.range n).filter (fun x => x ∈ touchedKeys init 1)).card
      ≤ omegaNB (touchedKeys init 1) (rightSubtree (seqTree init 1))
        + 2 * (N - 1)
        + 14 * ((Finset.range n).filter (fun x => x ∈ touchedKeys init N)).card := by
  intro N
  induction N with
  | zero => omega
  | succ N ih =>
      intro _ hNn
      rcases Nat.eq_zero_or_pos N with hN0 | hNpos
      · subst hN0
        simp
      · have hIH := ih hNpos (by omega)
        obtain ⟨hNB, hC⟩ := process_invariants init hbst hkeys N hNpos (by omega)
        have hstep := omegaNB_step init hbst hkeys N hNpos (by omega) hNB hC
        have hfresh := fresh_le_mu init hbst hnum hkeys N (by omega)
        have h1N : 1 ≤ N := hNpos
        rw [Finset.sum_Ico_succ_top h1N]
        omega

/-- **Total links are linear**: `∑_{k<n} splayLinks (seqTree k) k ≤ 13·n`. -/
private theorem totalLinks_le (init : BinaryTree) (hbst : IsBST init)
    {n : Nat} (hn : 1 ≤ n) (hnum : init.num_nodes = n)
    (hkeys : ∀ m : Nat, m < n → m ∈ init.toKeyList) :
    (∑ k ∈ Finset.range n, splayLinks (seqTree init k) k) ≤ 13 * n := by
  -- the k = 0 term
  have hL0 : 2 * splayLinks (seqTree init 0) 0 ≤ n := by
    have h1 := two_splayLinks_le_cost (seqTree init 0) 0
    have h2 := splay_cost_le_search_path_len (seqTree init 0) 0
    have h3 := search_path_len_le_num_nodes (seqTree init 0) 0
    have h4 : (seqTree init 0).num_nodes = n := by rw [seqTree_num_nodes]; exact hnum
    rw [h4] at h3
    have : (2 * splayLinks (seqTree init 0) 0 : ℝ) ≤ (n : ℝ) := by
      calc (2 * splayLinks (seqTree init 0) 0 : ℝ) ≤ splay.cost (seqTree init 0) 0 := h1
        _ ≤ ((seqTree init 0).search_path_len 0 : ℝ) := h2
        _ ≤ (n : ℝ) := by exact_mod_cast h3
    exact_mod_cast this
  -- the telescope over [1, n)
  have htel := links_telescope init hbst hnum hkeys n hn le_rfl
  have hbase := omegaNB_base_le init hbst
  rw [hnum] at hbase
  have hmu : ((Finset.range n).filter (fun x => x ∈ touchedKeys init n)).card ≤ n := by
    calc ((Finset.range n).filter (fun x => x ∈ touchedKeys init n)).card
        ≤ (Finset.range n).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = n := Finset.card_range n
  have hsplit : ∑ k ∈ Finset.range n, splayLinks (seqTree init k) k
      = splayLinks (seqTree init 0) 0
        + ∑ k ∈ Finset.Ico 1 n, splayLinks (seqTree init k) k := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hn]
  omega

/-- **THE SEQUENTIAL ACCESS THEOREM** (machine-checked, direct, no conjecture dependency):
splaying `0, 1, …, n−1` on any `n`-node BST costs at most `27·n`. -/
private theorem sequential_access_theorem :
    ∃ c : ℝ, ∀ n : ℕ, ∀ init : BinaryTree, init.num_nodes = n → IsBST init →
      (∀ i : Fin n, (one_to_n n) i ∈ init.toKeyList) →
      splay.sequence_cost init (one_to_n n) ≤ c * n := by
  refine ⟨27, ?_⟩
  intro n init hnum hbst hmem
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    simp [splay.sequence_cost, List.finRange]
  · have hkeys : ∀ m : Nat, m < n → m ∈ init.toKeyList := by
      intro m hm
      have := hmem ⟨m, hm⟩
      simpa [one_to_n] using this
    have h1 := sequence_cost_le_two_mul_links_add_n init n
    have h2 := totalLinks_le init hbst hn hnum hkeys
    have h3 : ((∑ k ∈ Finset.range n, splayLinks (seqTree init k) k : ℕ) : ℝ)
        ≤ 13 * (n : ℝ) := by exact_mod_cast h2
    calc splay.sequence_cost init (one_to_n n)
        ≤ 2 * ((∑ k ∈ Finset.range n, splayLinks (seqTree init k) k : ℕ) : ℝ) + n := h1
      _ ≤ 2 * (13 * (n : ℝ)) + n := by linarith [h3]
      _ = 27 * n := by ring

/-- (50 pts) Sequential access on a splay tree. Prove that splaying the
access sequence `1, 2, ..., n` on any BST of `n` nodes containing those
keys takes total cost at most `c * n` for some constant `c`. The constant
`c` is the metric used for the Phase 2 tie break: among submissions
solving this problem, a smaller constant wins. -/
theorem sequential : ∃ c, ∀ n, let X := one_to_n n
    ∀ (init : BinaryTree), (h_size : init.num_nodes = n) →
    IsBST init → (∀ i : Fin n, (X i) ∈ init.toKeyList) →
    splay.sequence_cost init X ≤ c * n := sequential_access_theorem

end Splay
