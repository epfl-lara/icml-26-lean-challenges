import Challenges.Splay_Tree.Def_Containment
import Challenges.Splay_Tree.Def_Ackermann
import Challenges.Splay_Tree.Def_Splay

/-!
# POOLED invariant shell for the splay-tree deque programme

Replaces the per-side invariant shell of the development file with the POOLED
version matching the pooled capstone (`ledgerP`/`drawP`): ONE ghost state, no
side index.  On EVERY access the ghost takes the own-style step (greedy drain of
the doubled draw from the met claims, pool absorbs the remainder, debris claim
appended, prune to the live side of the accessed key) followed by the flat `+2`
pool inflow — replacing the per-side `+4` opposite inflow.

Deliverables:
* `ghostStepP`, `ghostAtP` — the pooled ghost fold;
* `INVP` — the three-clause pooled invariant
  (C1 conservation / C2 next-access cover, the next access at state `i` IS `i` /
   C3 chain cover over `ConsecOwnAfter` pairs, `b` ranging over both sides);
* `INVP_zero`, `INVP_all_of_steps` — base case and induction skeleton with the
  ONE step hypothesis `hstep : ∀ i < n, INVP i → INVP (i+1)`;
* `masterP_of_INVP` — the MASTER discharge (κ = 6) via
  `master_of_C1_C2_strict14` + path-length split + met-sum monotonicity +
  the fresh/filter bridge;
* `hmasterP_of_step` — the end-to-end conditional producing the pooled
  capstone's `hmaster` hypothesis (∀ i : Fin n form, κ = 6) verbatim;
* C1 step bridges `ghost_C1P_step` / `ghost_C1P_step_safe` /
  `INVP_C1_succ_of_cover` and the cover bridge `metSumP_eq_metTotal_path`
  for the step prover.

All component definitions (`touchedList`, `pathN`, `accessN`, `tcOf`,
`tcSuffixOf`, `sideF`, `ConsecOwnAfter`, the ghost-claim layer, the keystone
arithmetic and bridges) are copied verbatim from the development file / pooled
capstone; the file is self-contained over the three `Def` imports.
-/

set_option maxHeartbeats 2000000

namespace Splay

/-! ### Touched count -/

def touchedCount (T : List Nat) (c : List Nat) : Nat := (c.filter (fun x => x ∈ T)).length

theorem touchedCount_nil_T (c : List ℕ) : touchedCount [] c = 0 := by
  unfold touchedCount
  rw [List.filter_eq_nil_iff.mpr]
  · rfl
  · intro a _
    simp

/-! ### Basic counting -/

theorem toKeyList_length (t : BinaryTree) :
    t.toKeyList.length = t.num_nodes := by
  induction t with
  | empty =>
      simp [BinaryTree.toKeyList, BinaryTree.num_nodes]
  | node l k r ihl ihr =>
      simp [BinaryTree.toKeyList, BinaryTree.num_nodes, ihl, ihr]
      omega

theorem node_search_path_len_pos (l : BinaryTree) (k : Nat)
    (r : BinaryTree) (q : Nat) :
    0 < (BinaryTree.node l k r).search_path_len q := by
  simp only [BinaryTree.search_path_len]
  by_cases hqk : q < k
  · simp [hqk]
  · by_cases hkq : k < q
    · simp [hqk, hkq]
    · simp [hqk, hkq]

/-! ### Splay preserves the key list and the BST property -/

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

/-! ### The process tree -/

/-- `processTree init X i` is the tree obtained from `init` after performing the
first `i` splay accesses of the sequence `X`.  For `i ≥ n` it stabilizes. -/
def processTree {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ) : ℕ → BinaryTree
  | 0 => init
  | (i + 1) =>
      if h : i < n then splay (processTree init X i) (X ⟨i, h⟩)
      else processTree init X i

@[simp] theorem processTree_zero {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ) :
    processTree init X 0 = init := rfl

theorem processTree_succ_dite {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (i : ℕ) :
    processTree init X (i + 1) =
      if h : i < n then splay (processTree init X i) (X ⟨i, h⟩)
      else processTree init X i := rfl

/-- The process never changes the key set. -/
theorem processTree_toKeyList {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (m : ℕ) :
    (processTree init X m).toKeyList = init.toKeyList := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [processTree_succ_dite]
      by_cases h : m < n
      · rw [dif_pos h, splay_toKeyList, ih]
      · rw [dif_neg h, ih]

/-- The process preserves the BST property. -/
theorem processTree_isBST {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (hbst : IsBST init) (m : ℕ) :
    IsBST (processTree init X m) := by
  induction m with
  | zero => exact hbst
  | succ m ih =>
      rw [processTree_succ_dite]
      by_cases h : m < n
      · rw [dif_pos h]
        exact splay_isBST _ _ ih
      · rw [dif_neg h]
        exact ih

theorem processTree_ne_empty {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (hsize : init.num_nodes = n) (hn : 0 < n) (i : ℕ) :
    ∃ l k r, processTree init X i = BinaryTree.node l k r := by
  have hkeys := processTree_toKeyList init X i
  cases hpt : processTree init X i with
  | empty =>
      exfalso
      rw [hpt] at hkeys
      have hlen : init.toKeyList.length = n := by rw [toKeyList_length, hsize]
      rw [← hkeys] at hlen
      simp [BinaryTree.toKeyList] at hlen
      omega
  | node l k r => exact ⟨l, k, r, rfl⟩

/-! ### Search paths -/

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

theorem search_path_len_eq (q : ℕ) (t : BinaryTree) :
    t.search_path_len q = (searchPath q t).length := by
  induction t with
  | empty => simp [BinaryTree.search_path_len, searchPath]
  | node l k r ihl ihr =>
      by_cases h1 : q = k
      · subst h1
        simp [BinaryTree.search_path_len, searchPath]
      · by_cases h2 : q < k
        · simp only [BinaryTree.search_path_len, searchPath, if_neg h1,
            if_pos h2, List.length_cons, ihl]
          omega
        · have h3 : k < q := by omega
          have h2' : ¬ q < k := h2
          simp only [BinaryTree.search_path_len, searchPath, if_neg h1,
            if_neg h2', if_pos h3, List.length_cons, ihr]
          omega

/-- BST search paths are duplicate-free. -/
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

/-! ### Touched sets, cost and fresh budget (capstone-level, verbatim) -/

def touchedUpTo {n : ℕ} (t : ℕ → BinaryTree) (X : Fin n → ℕ) : ℕ → Finset Nat
  | 0 => ∅
  | (i+1) => if h : i < n then touchedUpTo t X i ∪ (searchPath (X ⟨i,h⟩) (t i)).toFinset
             else touchedUpTo t X i

/-- ℕ-level per-access cost: the number of links on the search path of the `i`-th
access in the process (`search_path_len - 1`); `0` out of range. -/
def costN {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ) (i : ℕ) : ℕ :=
  if h : i < n then (processTree init X i).search_path_len (X ⟨i, h⟩) - 1
  else 0

/-- ℕ-level fresh budget: the number of nodes on the `i`-th search path that were
never touched by an earlier access; `0` out of range. -/
def freshN {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ) (i : ℕ) : ℕ :=
  if h : i < n then
    ((searchPath (X ⟨i, h⟩) (processTree init X i)).toFinset
      \ touchedUpTo (processTree init X) X i).card
  else 0

/-! ### The pooled ledger (capstone-level, verbatim) -/

/-- Doubled draw, capped at the ledger (so the ledger never underflows).
`2 * c - min (2 * c) (2 * kap * (1 + f))` is the doubled excess `2*c ∸ 2*kap*(1+f)`. -/
def drawP (kap : ℕ) (c f D : ℕ) : ℕ := min D (2 * c - min (2 * c) (2 * kap * (1 + f)))

/-- The pooled doubled ledger: ONE ledger, no side index.  On EVERY access the
ledger pays out the capped draw, is repaid `c i`, and gains a flat `2`. -/
def ledgerP (kap : ℕ) (c f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | (i+1) => ledgerP kap c f i - drawP kap (c i) (f i) (ledgerP kap c f i) + c i + 2

@[simp] theorem ledgerP_zero (kap : ℕ) (c f : ℕ → ℕ) : ledgerP kap c f 0 = 0 := rfl

theorem ledgerP_succ (kap : ℕ) (c f : ℕ → ℕ) (i : ℕ) :
    ledgerP kap c f (i+1)
      = ledgerP kap c f i - drawP kap (c i) (f i) (ledgerP kap c f i) + c i + 2 := rfl

/-! ### Ghost state and claims (development file, verbatim) -/

/-- An interval claim: keys in `[lo, hi]` carry a (doubled) remnant budget `r`. -/
structure GhostClaim where
  lo : ℕ
  hi : ℕ
  /-- doubled budget -/
  r : ℕ

/-- Ghost state: a list of interval claims plus a scalar pool. -/
structure GhostState where
  claims : List GhostClaim
  pool : ℕ

/-- Total budget of a list of claims. -/
def claimsListTotal (cs : List GhostClaim) : ℕ := (cs.map (·.r)).sum

/-- Total budget of all claims of a ghost state. -/
def claimsTotal (g : GhostState) : ℕ := claimsListTotal g.claims

@[simp] theorem claimsListTotal_nil : claimsListTotal [] = 0 := rfl

@[simp] theorem claimsListTotal_cons (cl : GhostClaim) (cs : List GhostClaim) :
    claimsListTotal (cl :: cs) = cl.r + claimsListTotal cs := by
  simp [claimsListTotal]

@[simp] theorem claimsListTotal_append (cs ds : List GhostClaim) :
    claimsListTotal (cs ++ ds) = claimsListTotal cs + claimsListTotal ds := by
  simp [claimsListTotal]

/-- The filtered claims never carry more budget than the whole list. -/
theorem claimsListTotal_filter_le (met : GhostClaim → Bool) (cs : List GhostClaim) :
    claimsListTotal (cs.filter met) ≤ claimsListTotal cs := by
  induction cs with
  | nil => simp
  | cons cl rest ih =>
      cases hm : met cl with
      | false =>
          simp only [List.filter_cons, hm, Bool.false_eq_true, if_false,
            claimsListTotal_cons]
          omega
      | true =>
          simp only [List.filter_cons, hm, if_true, claimsListTotal_cons]
          omega

/-- A claim is met by the access path `P` (with touched set `T`) iff some touched
node of `P` lies in the claim's interval. -/
def claimMet (T : List ℕ) (P : List ℕ) (cl : GhostClaim) : Bool :=
  P.any (fun z => decide (z ∈ T) && decide (cl.lo ≤ z) && decide (z ≤ cl.hi))

/-- Greedily drain `amount` from the claims satisfying `met`, in list order; return
`(remaining undrained amount, updated claims)`. -/
def consumeGreedy (amount : ℕ) (cs : List GhostClaim) (met : GhostClaim → Bool) :
    ℕ × List GhostClaim :=
  match cs with
  | [] => (amount, [])
  | cl :: rest =>
      if met cl then
        let res := consumeGreedy (amount - min amount cl.r) rest met
        (res.1, { cl with r := cl.r - min amount cl.r } :: res.2)
      else
        let res := consumeGreedy amount rest met
        (res.1, cl :: res.2)

/-- The undrained remainder is exactly `amount` minus what the met claims could pay. -/
theorem consumeGreedy_fst (cs : List GhostClaim) (met : GhostClaim → Bool) :
    ∀ amount : ℕ, (consumeGreedy amount cs met).1
      = amount - min amount (claimsListTotal (cs.filter met)) := by
  induction cs with
  | nil => intro amount; simp [consumeGreedy]
  | cons cl rest ih =>
      intro amount
      cases hm : met cl with
      | false =>
          simp only [consumeGreedy, hm, Bool.false_eq_true, if_false, List.filter_cons]
          exact ih amount
      | true =>
          simp only [consumeGreedy, hm, if_true, List.filter_cons, claimsListTotal_cons]
          rw [ih]
          omega

/-- Greedy consumption removes exactly `min amount (met total)` from the claims. -/
theorem consumeGreedy_snd (cs : List GhostClaim) (met : GhostClaim → Bool) :
    ∀ amount : ℕ, claimsListTotal (consumeGreedy amount cs met).2
      = claimsListTotal cs - min amount (claimsListTotal (cs.filter met)) := by
  induction cs with
  | nil => intro amount; simp [consumeGreedy]
  | cons cl rest ih =>
      intro amount
      have hf := claimsListTotal_filter_le met rest
      cases hm : met cl with
      | false =>
          simp only [consumeGreedy, hm, Bool.false_eq_true, if_false, List.filter_cons,
            claimsListTotal_cons]
          rw [ih]
          omega
      | true =>
          simp only [consumeGreedy, hm, if_true, List.filter_cons, claimsListTotal_cons]
          rw [ih]
          omega

/-! ### Debris claim -/

/-- The live-side keys of the access path: for a min-side access at `x` the keys
`≥ x`, for a max-side access the keys `≤ x`. -/
def debrisKeys (P : List ℕ) (x : ℕ) (isMin : Bool) : List ℕ :=
  P.filter (fun z => if isMin then decide (x ≤ z) else decide (z ≤ x))

/-- Default-valued minimum of a list (`0` on `[]`). -/
def listMinD : List ℕ → ℕ
  | [] => 0
  | y :: ys => ys.foldl min y

/-- Default-valued maximum of a list (`0` on `[]`). -/
def listMaxD : List ℕ → ℕ
  | [] => 0
  | y :: ys => ys.foldl max y

/-- The debris claim of an own-side dive: if the path has at least two live-side keys,
a single claim spanning them with budget `c` (the repay); otherwise nothing. -/
def ghostDebris (P : List ℕ) (c x : ℕ) (isMin : Bool) : List GhostClaim :=
  if 2 ≤ (debrisKeys P x isMin).length then
    [⟨listMinD (debrisKeys P x isMin), listMaxD (debrisKeys P x isMin), c⟩]
  else []

/-- The debris adds at most `c` to the claims total (exactly `c` when present). -/
theorem ghostDebris_total_le (P : List ℕ) (c x : ℕ) (isMin : Bool) :
    claimsListTotal (ghostDebris P c x isMin) ≤ c := by
  unfold ghostDebris
  split
  · simp [claimsListTotal]
  · simp

/-! ### Pruning to the live side -/

/-- Clip a claim's interval to the live side: a min-side access at `x` kills all keys
below `x` (`lo := max lo x`); a max-side access kills all keys above (`hi := min hi x`).
The budget `r` is kept unchanged. -/
def clipClaim (isMin : Bool) (x : ℕ) (cl : GhostClaim) : GhostClaim :=
  if isMin then { cl with lo := max cl.lo x } else { cl with hi := min cl.hi x }

/-- A claim survives pruning iff its interval meets the live side. -/
def claimAlive (isMin : Bool) (x : ℕ) (cl : GhostClaim) : Bool :=
  if isMin then decide (x ≤ cl.hi) else decide (cl.lo ≤ x)

/-- Prune: drop fully-dead claims, clip the surviving ones (budgets unchanged). -/
def pruneClaims (isMin : Bool) (x : ℕ) (cs : List GhostClaim) : List GhostClaim :=
  (cs.filter (claimAlive isMin x)).map (clipClaim isMin x)

@[simp] theorem clipClaim_r (isMin : Bool) (x : ℕ) (cl : GhostClaim) :
    (clipClaim isMin x cl).r = cl.r := by
  cases isMin <;> simp [clipClaim]

theorem claimsListTotal_map_clip (isMin : Bool) (x : ℕ) (cs : List GhostClaim) :
    claimsListTotal (cs.map (clipClaim isMin x)) = claimsListTotal cs := by
  induction cs with
  | nil => rfl
  | cons cl rest ih => simp [ih]

/-- Pruning only decreases the claims total. -/
theorem claimsListTotal_prune_le (isMin : Bool) (x : ℕ) (cs : List GhostClaim) :
    claimsListTotal (pruneClaims isMin x cs) ≤ claimsListTotal cs := by
  unfold pruneClaims
  rw [claimsListTotal_map_clip]
  exact claimsListTotal_filter_le _ _

/-! ### The own-style ghost step (development file, verbatim) -/

/-- Ghost-state update of an own-style access (path `P`, touched set `T`, cost `c`,
fresh count `f`, accessed key `x`, live-side direction `isMin`):
1. `amount := 2*c - min (2*c) (2*kap*(1+f))` (the doubled draw, uncapped form);
2. drain `amount` greedily from the claims met by `P`, the remainder from the pool;
3. add the debris claim (span of `P`'s live-side keys, budget `c`);
4. prune all claims to the live side. -/
def ghostStepOwn (kap : ℕ) (T P : List ℕ) (c f x : ℕ) (isMin : Bool)
    (g : GhostState) : GhostState :=
  let amount := 2 * c - min (2 * c) (2 * kap * (1 + f))
  let res := consumeGreedy amount g.claims (claimMet T P)
  { claims := pruneClaims isMin x (res.2 ++ ghostDebris P c x isMin),
    pool := g.pool - res.1 }

/-- Total budget of the claims met by the current access (touched set `T`, path `P`):
the amount the greedy drain can take from claims before touching the pool. -/
def metTotal (T P : List ℕ) (g : GhostState) : ℕ :=
  claimsListTotal (g.claims.filter (claimMet T P))

/-- **C1 conservation, exact unconditional form.**  An own-style ghost step decreases
the ghost total by exactly `min amount (metTotal + pool)` before the `+ c` debris
repay (pruning can only lose more). -/
theorem ghost_C1_own_min (kap : ℕ) (T P : List ℕ) (c f x : ℕ) (isMin : Bool)
    (g : GhostState) (D : ℕ)
    (h : claimsTotal g + g.pool ≤ D) :
    claimsTotal (ghostStepOwn kap T P c f x isMin g)
      + (ghostStepOwn kap T P c f x isMin g).pool
      ≤ D - min D (min (2 * c - min (2 * c) (2 * kap * (1 + f)))
            (metTotal T P g + g.pool)) + c := by
  have hclaims : claimsTotal (ghostStepOwn kap T P c f x isMin g)
      = claimsListTotal (pruneClaims isMin x
          ((consumeGreedy (2 * c - min (2 * c) (2 * kap * (1 + f))) g.claims
              (claimMet T P)).2
            ++ ghostDebris P c x isMin)) := rfl
  have hpool : (ghostStepOwn kap T P c f x isMin g).pool
      = g.pool - (consumeGreedy (2 * c - min (2 * c) (2 * kap * (1 + f))) g.claims
          (claimMet T P)).1 := rfl
  have h' : claimsListTotal g.claims + g.pool ≤ D := h
  have hmt : metTotal T P g = claimsListTotal (g.claims.filter (claimMet T P)) := rfl
  have hres1 := consumeGreedy_fst g.claims (claimMet T P)
    (2 * c - min (2 * c) (2 * kap * (1 + f)))
  have hres2 := consumeGreedy_snd g.claims (claimMet T P)
    (2 * c - min (2 * c) (2 * kap * (1 + f)))
  have hflt := claimsListTotal_filter_le (claimMet T P) g.claims
  have hdeb := ghostDebris_total_le P c x isMin
  have hprune := claimsListTotal_prune_le isMin x
    ((consumeGreedy (2 * c - min (2 * c) (2 * kap * (1 + f))) g.claims
        (claimMet T P)).2
      ++ ghostDebris P c x isMin)
  rw [claimsListTotal_append] at hprune
  rw [hclaims, hpool, hmt]
  set K := 2 * kap * (1 + f) with hK
  omega

/-- **C1 conservation, ledger-matching form.**  Under the cover hypothesis
(supplied by the C2 invariant: the met claims plus the pool cover the uncapped
draw), an own-style ghost step keeps the ghost total below the ledger's update
`D - min D amount + c`. -/
theorem ghost_C1_own (kap : ℕ) (T P : List ℕ) (c f x : ℕ) (isMin : Bool)
    (g : GhostState) (D : ℕ)
    (h : claimsTotal g + g.pool ≤ D)
    (hcover : 2 * c - min (2 * c) (2 * kap * (1 + f)) ≤ metTotal T P g + g.pool) :
    claimsTotal (ghostStepOwn kap T P c f x isMin g)
      + (ghostStepOwn kap T P c f x isMin g).pool
      ≤ D - min D (2 * c - min (2 * c) (2 * kap * (1 + f))) + c := by
  have hmin := ghost_C1_own_min kap T P c f x isMin g D h
  rwa [min_eq_left hcover] at hmin

/-- Unconditional safety: even without the cover hypothesis, an own-style step never
pushes the ghost total above `D + c`. -/
theorem ghost_C1_own_safe (kap : ℕ) (T P : List ℕ) (c f x : ℕ) (isMin : Bool)
    (g : GhostState) (D : ℕ)
    (h : claimsTotal g + g.pool ≤ D) :
    claimsTotal (ghostStepOwn kap T P c f x isMin g)
      + (ghostStepOwn kap T P c f x isMin g).pool ≤ D + c := by
  have hmin := ghost_C1_own_min kap T P c f x isMin g D h
  set K := 2 * kap * (1 + f) with hK
  omega

/-! ### Master keystone and bridges (development file, verbatim) -/

theorem searchPath_length_split (T : List ℕ) (P : List ℕ) :
    P.length = touchedCount T P + (P.filter (fun z => z ∉ T)).length := by
  induction P with
  | nil => simp [touchedCount]
  | cons x xs ih =>
    by_cases hx : x ∈ T
    · have h1 : touchedCount T (x :: xs) = touchedCount T xs + 1 := by
        simp [touchedCount, hx]
      have h2 : (x :: xs).filter (fun z => z ∉ T) = xs.filter (fun z => z ∉ T) := by
        simp [hx]
      rw [List.length_cons, h1, h2]
      omega
    · have h1 : touchedCount T (x :: xs) = touchedCount T xs := by
        simp [touchedCount, hx]
      have h2 : (x :: xs).filter (fun z => z ∉ T)
          = x :: xs.filter (fun z => z ∉ T) := by
        simp [hx]
      rw [List.length_cons, h1, h2, List.length_cons]
      omega

/-- **MASTER derivation (keystone, `κ = 6`)**, strict-14 form of (C2). -/
theorem master_of_C1_C2_strict14 (D tc fr Sr p c : ℕ)
    (hC1 : Sr + p ≤ D)
    (hC2 : 2 * tc ≤ Sr + p + 14)
    (hlen : c + 1 = tc + fr) :
    2 * c ≤ D + 2 * 6 * (1 + fr) := by
  omega

/-- **Met-sum monotonicity.**  The sum of remnant budgets over any sub-selection
of claims is at most the sum over all claims. -/
theorem metSum_le_total (claims : List GhostClaim) (pred : GhostClaim → Bool) :
    ((claims.filter pred).map (·.r)).sum ≤ (claims.map (·.r)).sum := by
  induction claims with
  | nil => simp
  | cons cl cls ih =>
    by_cases hc : pred cl
    · simp only [List.filter_cons, hc, if_true, List.map_cons, List.sum_cons]
      exact Nat.add_le_add_left ih _
    · simp only [List.filter_cons, hc, List.map_cons, List.sum_cons]
      exact ih.trans (Nat.le_add_left _ _)

/-- **Fresh bridge.**  For a duplicate-free path `P`, the list-level fresh count
(nodes not in the touched set `T`) is exactly the `freshN`-style Finset
cardinality `(P.toFinset \ T).card` used by the capstone. -/
theorem fresh_filter_eq_card (P : List ℕ) (T : Finset ℕ) (hP : P.Nodup) :
    (P.filter (fun z => z ∉ T)).length = (P.toFinset \ T).card := by
  induction P with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at hP
    obtain ⟨hx, hxs⟩ := hP
    by_cases hxT : x ∈ T
    · have h1 : (x :: xs).filter (fun z => z ∉ T) = xs.filter (fun z => z ∉ T) := by
        simp [hxT]
      have h2 : (x :: xs).toFinset \ T = xs.toFinset \ T := by
        rw [List.toFinset_cons, Finset.insert_sdiff_of_mem _ hxT]
      rw [h1, h2, ih hxs]
    · have h1 : (x :: xs).filter (fun z => z ∉ T)
          = x :: xs.filter (fun z => z ∉ T) := by
        simp [hxT]
      have hxnot : x ∉ xs.toFinset \ T := fun hmem =>
        hx (List.mem_toFinset.mp (Finset.mem_sdiff.mp hmem).1)
      have h2 : ((x :: xs).toFinset \ T).card = (xs.toFinset \ T).card + 1 := by
        rw [List.toFinset_cons, Finset.insert_sdiff_of_notMem _ hxT,
          Finset.card_insert_of_notMem hxnot]
      rw [h1, List.length_cons, h2, ih hxs]

/-! ### The divergence suffix (development file, verbatim) -/

/-- `divergeSuffix y q t` is the part of `y`'s search path strictly below the point
where it separates from `q`'s search path. -/
def divergeSuffix (y q : Nat) : BinaryTree → List Nat
  | .empty => []
  | .node l k r =>
      if y = k then []
      else if q = k then (if y < k then searchPath y l else searchPath y r)
      else if y < k ∧ q < k then divergeSuffix y q l
      else if k < y ∧ k < q then divergeSuffix y q r
      else (if y < k then searchPath y l else searchPath y r)

/-! ### The side flag (development file, verbatim) -/

/-- `sideF X i = true` iff every later access is `≤ X i` (the future-max side);
`true` out of range. -/
def sideF {n : ℕ} (X : Fin n → ℕ) (i : ℕ) : Bool :=
  if h : i < n then
    decide (∀ j : Fin n, (⟨i, h⟩ : Fin n) < j → X j ≤ X ⟨i, h⟩)
  else true

/-! ### Totalized access data (development file, verbatim) -/

/-- The accessed key at position `i` (`0` out of range). -/
def accessN {n : ℕ} (X : Fin n → ℕ) (i : ℕ) : ℕ :=
  if h : i < n then X ⟨i, h⟩ else 0

/-- The search path of the `i`-th access in the process (`[]` out of range). -/
def pathN {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ) (i : ℕ) : List ℕ :=
  if h : i < n then searchPath (X ⟨i, h⟩) (processTree init X i) else []

/-- List-level touched set: the concatenation of all earlier search paths
(duplicates are fine — only membership matters). -/
def touchedList {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ) : ℕ → List ℕ
  | 0 => []
  | (i+1) => touchedList init X i ++ pathN init X i

@[simp] theorem touchedList_zero {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ) :
    touchedList init X 0 = [] := rfl

theorem touchedList_succ {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ) (i : ℕ) :
    touchedList init X (i+1) = touchedList init X i ++ pathN init X i := rfl

/-- Membership in the list-level touched set coincides with the Finset-level
`touchedUpTo` of the capstone. -/
theorem mem_touchedList_iff {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (m : ℕ) (z : ℕ) :
    z ∈ touchedList init X m ↔ z ∈ touchedUpTo (processTree init X) X m := by
  induction m with
  | zero =>
      simp [touchedUpTo]
  | succ i ih =>
      rw [touchedList_succ, List.mem_append]
      by_cases h : i < n
      · have ht : touchedUpTo (processTree init X) X (i+1)
            = touchedUpTo (processTree init X) X i
              ∪ (searchPath (X ⟨i, h⟩) (processTree init X i)).toFinset := by
          simp [touchedUpTo, h]
        have hp : pathN init X i = searchPath (X ⟨i, h⟩) (processTree init X i) := by
          unfold pathN
          rw [dif_pos h]
        rw [ht, hp, Finset.mem_union, List.mem_toFinset, ih]
      · have ht : touchedUpTo (processTree init X) X (i+1)
            = touchedUpTo (processTree init X) X i := by
          simp [touchedUpTo, h]
        have hp : pathN init X i = [] := by
          unfold pathN
          rw [dif_neg h]
        rw [ht, hp, ih]
        simp

/-! ### Invariant ingredients (development file, verbatim) -/

/-- Touched count of the `v`-search path in the current process tree, against the
current touched set. -/
def tcOf {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ) (v : ℕ) (i : ℕ) : ℕ :=
  touchedCount (touchedList init X i) (searchPath v (processTree init X i))

/-- Touched count of the diverge suffix of `vk` against `vj`'s path in the current
process tree. -/
def tcSuffixOf {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (vk vj : ℕ) (i : ℕ) : ℕ :=
  touchedCount (touchedList init X i) (divergeSuffix vk vj (processTree init X i))

/-- `(j, k)` is a pair of consecutive future side-`b` indices (both `≥ i`, in range,
with no side-`b` index strictly between). -/
def ConsecOwnAfter {n : ℕ} (X : Fin n → ℕ) (i : ℕ) (b : Bool) (j k : ℕ) : Prop :=
  i ≤ j ∧ j < k ∧ k < n ∧ sideF X j = b ∧ sideF X k = b ∧
    ∀ m, j < m → m < k → sideF X m ≠ b

/-! ### THE POOLED GHOST

ONE fold, no side index.  EVERY access takes the own-style step: greedy drain of
the doubled draw from the claims met by the current path (pool absorbs the
remainder), debris claim appended (live-side span of the path, budget = the
cost repay), prune to the live side of the accessed key (`isMin = !(sideF X i)`,
both directions occur as the side flag flips), then the flat `+2` pool inflow
(replacing the per-side `+4` opposite inflow). -/

/-- The pooled ghost step: the own-style pipeline followed by the `+2` inflow. -/
def ghostStepP (kap : ℕ) (T P : List ℕ) (c f x : ℕ) (isMin : Bool)
    (g : GhostState) : GhostState :=
  let amount := 2 * c - min (2 * c) (2 * kap * (1 + f))
  let res := consumeGreedy amount g.claims (claimMet T P)
  { claims := pruneClaims isMin x (res.2 ++ ghostDebris P c x isMin),
    pool := g.pool - res.1 + 2 }

theorem ghostStepP_claims (kap : ℕ) (T P : List ℕ) (c f x : ℕ) (isMin : Bool)
    (g : GhostState) :
    (ghostStepP kap T P c f x isMin g).claims
      = (ghostStepOwn kap T P c f x isMin g).claims := rfl

theorem ghostStepP_pool (kap : ℕ) (T P : List ℕ) (c f x : ℕ) (isMin : Bool)
    (g : GhostState) :
    (ghostStepP kap T P c f x isMin g).pool
      = (ghostStepOwn kap T P c f x isMin g).pool + 2 := rfl

/-- **C1 conservation for the pooled step, ledger-matching form.**  Under the cover
hypothesis (the met claims plus the pool cover the uncapped draw — supplied by the
C2 invariant), a pooled ghost step keeps the ghost total below the pooled ledger's
update `D - drawP + c + 2`. -/
theorem ghost_C1P_step (kap : ℕ) (T P : List ℕ) (c f x : ℕ) (isMin : Bool)
    (g : GhostState) (D : ℕ)
    (h : claimsTotal g + g.pool ≤ D)
    (hcover : 2 * c - min (2 * c) (2 * kap * (1 + f)) ≤ metTotal T P g + g.pool) :
    claimsTotal (ghostStepP kap T P c f x isMin g)
      + (ghostStepP kap T P c f x isMin g).pool
      ≤ D - drawP kap c f D + c + 2 := by
  have h1 := ghost_C1_own kap T P c f x isMin g D h hcover
  have hc : claimsTotal (ghostStepP kap T P c f x isMin g)
      = claimsTotal (ghostStepOwn kap T P c f x isMin g) := rfl
  have hp : (ghostStepP kap T P c f x isMin g).pool
      = (ghostStepOwn kap T P c f x isMin g).pool + 2 := rfl
  have hd : drawP kap c f D
      = min D (2 * c - min (2 * c) (2 * kap * (1 + f))) := rfl
  rw [hc, hp, hd]
  set K := 2 * kap * (1 + f) with hK
  omega

/-- Unconditional safety for the pooled step: the ghost total never exceeds
`D + c + 2`. -/
theorem ghost_C1P_step_safe (kap : ℕ) (T P : List ℕ) (c f x : ℕ) (isMin : Bool)
    (g : GhostState) (D : ℕ)
    (h : claimsTotal g + g.pool ≤ D) :
    claimsTotal (ghostStepP kap T P c f x isMin g)
      + (ghostStepP kap T P c f x isMin g).pool ≤ D + c + 2 := by
  have h1 := ghost_C1_own_safe kap T P c f x isMin g D h
  have hc : claimsTotal (ghostStepP kap T P c f x isMin g)
      = claimsTotal (ghostStepOwn kap T P c f x isMin g) := rfl
  have hp : (ghostStepP kap T P c f x isMin g).pool
      = (ghostStepOwn kap T P c f x isMin g).pool + 2 := rfl
  rw [hc, hp]
  omega

/-- The pooled ghost state after `i` accesses: ONE fold, every access takes the
own-style step with prune direction `!(sideF X i)` (the live side of `X i`),
plus the flat `+2` pool inflow. -/
def ghostAtP {n : ℕ} (kap : ℕ) (init : BinaryTree) (X : Fin n → ℕ) :
    ℕ → GhostState
  | 0 => ⟨[], 0⟩
  | (i+1) =>
      ghostStepP kap (touchedList init X i) (pathN init X i)
        (costN init X i) (freshN init X i) (accessN X i) (!(sideF X i))
        (ghostAtP kap init X i)

@[simp] theorem ghostAtP_zero {n : ℕ} (kap : ℕ) (init : BinaryTree)
    (X : Fin n → ℕ) :
    ghostAtP kap init X 0 = ⟨[], 0⟩ := rfl

theorem ghostAtP_succ {n : ℕ} (kap : ℕ) (init : BinaryTree) (X : Fin n → ℕ)
    (i : ℕ) :
    ghostAtP kap init X (i+1) =
      ghostStepP kap (touchedList init X i) (pathN init X i)
        (costN init X i) (freshN init X i) (accessN X i) (!(sideF X i))
        (ghostAtP kap init X i) := rfl

/-- Met-claims budget of the pooled ghost state against an arbitrary key list `L`
(with the current touched set as `T`). -/
def metSumOnP {n : ℕ} (kap : ℕ) (init : BinaryTree) (X : Fin n → ℕ)
    (i : ℕ) (L : List ℕ) : ℕ :=
  claimsListTotal
    ((ghostAtP kap init X i).claims.filter (claimMet (touchedList init X i) L))

/-- Met-claims budget against the `v`-search path of the current process tree. -/
def metSumP {n : ℕ} (kap : ℕ) (init : BinaryTree) (X : Fin n → ℕ)
    (i : ℕ) (v : ℕ) : ℕ :=
  metSumOnP kap init X i (searchPath v (processTree init X i))

/-- The met-claims budget is at most the total claims budget. -/
theorem metSumOnP_le_claimsTotal {n : ℕ} (kap : ℕ) (init : BinaryTree)
    (X : Fin n → ℕ) (i : ℕ) (L : List ℕ) :
    metSumOnP kap init X i L ≤ claimsTotal (ghostAtP kap init X i) :=
  claimsListTotal_filter_le _ _

/-- Cover bridge for the step prover: at an in-range index the met sum against the
current access path IS the `metTotal` of the pooled step about to happen. -/
theorem metSumP_eq_metTotal_path {n : ℕ} (kap : ℕ) (init : BinaryTree)
    (X : Fin n → ℕ) (i : ℕ) (hi : i < n) :
    metSumP kap init X i (accessN X i)
      = metTotal (touchedList init X i) (pathN init X i) (ghostAtP kap init X i) := by
  have hacc : accessN X i = X ⟨i, hi⟩ := by
    unfold accessN
    rw [dif_pos hi]
  have hpath : pathN init X i = searchPath (X ⟨i, hi⟩) (processTree init X i) := by
    unfold pathN
    rw [dif_pos hi]
  rw [hacc, hpath]
  rfl

/-- C1 propagation across one pooled step, given the cover (from C2). -/
theorem INVP_C1_succ_of_cover {n : ℕ} (kap : ℕ) (init : BinaryTree)
    (X : Fin n → ℕ) (i : ℕ)
    (hC1 : claimsTotal (ghostAtP kap init X i) + (ghostAtP kap init X i).pool
      ≤ ledgerP kap (costN init X) (freshN init X) i)
    (hcover : 2 * costN init X i
        - min (2 * costN init X i) (2 * kap * (1 + freshN init X i))
      ≤ metTotal (touchedList init X i) (pathN init X i) (ghostAtP kap init X i)
        + (ghostAtP kap init X i).pool) :
    claimsTotal (ghostAtP kap init X (i+1)) + (ghostAtP kap init X (i+1)).pool
      ≤ ledgerP kap (costN init X) (freshN init X) (i+1) := by
  rw [ghostAtP_succ, ledgerP_succ]
  exact ghost_C1P_step kap (touchedList init X i) (pathN init X i)
    (costN init X i) (freshN init X i) (accessN X i) (!(sideF X i))
    (ghostAtP kap init X i) (ledgerP kap (costN init X) (freshN init X) i)
    hC1 hcover

/-! ### The three-clause POOLED invariant -/

/-- The pooled invariant at step `i`:
* (C1) conservation: the total claims budget plus the pool is within the pooled
  ledger;
* (C2) next-access cover: the next access at state `i` is `i` itself — if `i` is
  in range, twice the touched count of its current path is covered by the met
  claims plus pool plus `14`;
* (C3) chain cover: for every pair of CONSECUTIVE future same-side accesses
  `(j, k)` (side `b` ranging over both Booleans), twice the touched count of
  `X k`'s diverge suffix against `X j`'s current path is covered by the
  suffix-met claims plus pool plus `8`. -/
def INVP {n : ℕ} (kap : ℕ) (init : BinaryTree) (X : Fin n → ℕ) (i : ℕ) : Prop :=
  (claimsTotal (ghostAtP kap init X i) + (ghostAtP kap init X i).pool
      ≤ ledgerP kap (costN init X) (freshN init X) i)
  ∧ (i < n →
      2 * tcOf init X (accessN X i) i
        ≤ metSumP kap init X i (accessN X i) + (ghostAtP kap init X i).pool + 14)
  ∧ (∀ (b : Bool) (j k : ℕ), ConsecOwnAfter X i b j k →
      2 * tcSuffixOf init X (accessN X k) (accessN X j) i
        ≤ metSumOnP kap init X i
            (divergeSuffix (accessN X k) (accessN X j) (processTree init X i))
          + (ghostAtP kap init X i).pool + 8)

/-! ### Base case -/

/-- **Base case**: the pooled invariant holds at step `0` (empty ghost, zero
ledger, empty touched set). -/
theorem INVP_zero {n : ℕ} (kap : ℕ) (init : BinaryTree) (X : Fin n → ℕ) :
    INVP kap init X 0 := by
  refine ⟨?_, ?_, ?_⟩
  · have hg : ghostAtP kap init X 0 = ⟨[], 0⟩ := rfl
    have hl : ledgerP kap (costN init X) (freshN init X) 0 = 0 := rfl
    rw [hg, hl]
    show claimsListTotal [] + 0 ≤ 0
    simp
  · intro _
    have h0 : tcOf init X (accessN X 0) 0 = 0 := by
      show touchedCount (touchedList init X 0) _ = 0
      rw [touchedList_zero, touchedCount_nil_T]
    rw [h0]
    omega
  · intro b j k _
    have h0 : tcSuffixOf init X (accessN X k) (accessN X j) 0 = 0 := by
      show touchedCount (touchedList init X 0) _ = 0
      rw [touchedList_zero, touchedCount_nil_T]
    rw [h0]
    omega

/-! ### The induction skeleton: ONE step hypothesis -/

/-- **Invariant propagation from the single reproduction hypothesis.**
`hstep` reproduces the pooled invariant across every access; it is the only
remaining proof obligation of the pooled ledger programme. -/
theorem INVP_all_of_steps {n : ℕ} (kap : ℕ) (init : BinaryTree) (X : Fin n → ℕ)
    (hstep : ∀ i, i < n → INVP kap init X i → INVP kap init X (i+1)) :
    ∀ i, i ≤ n → INVP kap init X i := by
  intro i
  induction i with
  | zero =>
      intro _
      exact INVP_zero kap init X
  | succ i ih =>
      intro hin
      have hi : i < n := hin
      exact hstep i hi (ih (Nat.le_of_succ_le hin))

/-! ### The MASTER discharge -/

/-- **MASTER discharge (`κ = 6`).**  At every in-range index `i`, the pooled
invariant at `i` implies the per-access MASTER inequality of the pooled ledger
capstone.  Chain: (C2) at the access itself (the next access at state `i` IS `i`)
+ met-sum monotonicity + (C1) + the path-length split + the fresh bridge +
the strict-14 keystone. -/
theorem masterP_of_INVP {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (hsize : init.num_nodes = n) (hbst : IsBST init)
    (i : ℕ) (hi : i < n) (hINV : INVP 6 init X i) :
    2 * costN init X i
      ≤ ledgerP 6 (costN init X) (freshN init X) i
        + 2 * 6 * (1 + freshN init X i) := by
  obtain ⟨hC1, hC2, _hC3⟩ := hINV
  -- unfold the dite-style access data at the in-range index `i`
  have hacc : accessN X i = X ⟨i, hi⟩ := by
    unfold accessN
    rw [dif_pos hi]
  have hcost : costN init X i
      = (processTree init X i).search_path_len (X ⟨i, hi⟩) - 1 := by
    unfold costN
    rw [dif_pos hi]
  have hfreshN : freshN init X i
      = ((searchPath (X ⟨i, hi⟩) (processTree init X i)).toFinset
          \ touchedUpTo (processTree init X) X i).card := by
    unfold freshN
    rw [dif_pos hi]
  -- (C2) at the access itself
  have hC2i := hC2 hi
  rw [hacc] at hC2i
  -- met-sum monotonicity gives (C1) for the met claims
  have hmono : metSumP 6 init X i (X ⟨i, hi⟩)
      ≤ claimsTotal (ghostAtP 6 init X i) :=
    metSumOnP_le_claimsTotal 6 init X i _
  have hC1' : metSumP 6 init X i (X ⟨i, hi⟩)
      + (ghostAtP 6 init X i).pool
      ≤ ledgerP 6 (costN init X) (freshN init X) i := by
    omega
  -- the path-length split: cost + 1 = touched + fresh
  obtain ⟨l, k, r, hnode⟩ :=
    processTree_ne_empty init X hsize (lt_of_le_of_lt (Nat.zero_le i) hi) i
  have hpos : 0 < (processTree init X i).search_path_len (X ⟨i, hi⟩) := by
    rw [hnode]
    exact node_search_path_len_pos l k r _
  have hsplen : (processTree init X i).search_path_len (X ⟨i, hi⟩)
      = (searchPath (X ⟨i, hi⟩) (processTree init X i)).length :=
    search_path_len_eq _ _
  have hlen1 : costN init X i + 1
      = (searchPath (X ⟨i, hi⟩) (processTree init X i)).length := by
    rw [hcost, ← hsplen]
    omega
  have hsplit := searchPath_length_split (touchedList init X i)
    (searchPath (X ⟨i, hi⟩) (processTree init X i))
  -- the fresh bridge: list-level fresh count = freshN
  have hbstI : IsBST (processTree init X i) := processTree_isBST init X hbst i
  have hnodup : (searchPath (X ⟨i, hi⟩) (processTree init X i)).Nodup :=
    searchPath_nodup _ _ hbstI
  have hfc : (searchPath (X ⟨i, hi⟩) (processTree init X i)).filter
        (fun z => z ∉ touchedList init X i)
      = (searchPath (X ⟨i, hi⟩) (processTree init X i)).filter
        (fun z => z ∉ touchedUpTo (processTree init X) X i) := by
    refine List.filter_congr ?_
    intro z _
    exact decide_eq_decide.mpr (not_congr (mem_touchedList_iff init X i z))
  have hfreshlen : ((searchPath (X ⟨i, hi⟩) (processTree init X i)).filter
        (fun z => z ∉ touchedList init X i)).length = freshN init X i := by
    rw [hfc, fresh_filter_eq_card _ _ hnodup, hfreshN]
  have hlen2 : costN init X i + 1
      = touchedCount (touchedList init X i)
          (searchPath (X ⟨i, hi⟩) (processTree init X i))
        + freshN init X i := by
    omega
  -- assemble via the strict-14 keystone
  exact master_of_C1_C2_strict14
    (ledgerP 6 (costN init X) (freshN init X) i)
    (touchedCount (touchedList init X i)
      (searchPath (X ⟨i, hi⟩) (processTree init X i)))
    (freshN init X i)
    (metSumP 6 init X i (X ⟨i, hi⟩))
    ((ghostAtP 6 init X i).pool)
    (costN init X i)
    hC1' hC2i hlen2

/-! ### The end-to-end conditional -/

/-- **THE COMPLETE POOLED CONDITIONAL (`κ = 6`).**  Given the single reproduction
hypothesis (pooled-step preservation of the three-clause invariant, allowed to
use all the deque-instance facts), the MASTER per-access inequality of the
POOLED ledger capstone holds in its exact `∀ i : Fin n` hypothesis shape.
Feeding this conclusion to the pooled capstone's
`deque_of_ledger_masterP` / `deque_conjecture_of_ledger_masterP` (with `kap = 6`)
closes both deque challenges. -/
theorem hmasterP_of_step
    (hstep : ∀ (n : ℕ) (X : Fin n → ℕ) (init : BinaryTree),
        init.num_nodes = n → IsBST init → (∀ i : Fin n, X i ∈ init.toKeyList) →
        (X avoids ![2, 1, 3]) → (X avoids ![2, 3, 1]) →
        ∀ i, i < n → INVP 6 init X i → INVP 6 init X (i+1)) :
    ∀ (n : ℕ) (X : Fin n → ℕ) (init : BinaryTree),
      init.num_nodes = n → IsBST init → (∀ i : Fin n, X i ∈ init.toKeyList) →
      (X avoids ![2, 1, 3]) → (X avoids ![2, 3, 1]) →
      ∀ i : Fin n, 2 * costN init X i ≤
        ledgerP 6 (costN init X) (freshN init X) i
          + 2 * 6 * (1 + freshN init X i) := by
  intro n X init hsize hbst hmem h213 h231 i
  have hINV : INVP 6 init X (i : ℕ) :=
    INVP_all_of_steps 6 init X
      (hstep n X init hsize hbst hmem h213 h231) (i : ℕ) (Nat.le_of_lt i.isLt)
  exact masterP_of_INVP init X hsize hbst (i : ℕ) i.isLt hINV

end Splay

#print axioms Splay.INVP_zero
#print axioms Splay.INVP_all_of_steps
#print axioms Splay.masterP_of_INVP
#print axioms Splay.hmasterP_of_step
#print axioms Splay.ghost_C1P_step
#print axioms Splay.ghost_C1P_step_safe
#print axioms Splay.INVP_C1_succ_of_cover
#print axioms Splay.metSumP_eq_metTotal_path
