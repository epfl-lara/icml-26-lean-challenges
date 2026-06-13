import Challenges.Splay_Tree.Def_Containment
import Challenges.Splay_Tree.Def_Ackermann
import Challenges.Splay_Tree.Def_Splay

/-!
# ATOMIC GHOST, PHASE A — per-key budgets for the splay-deque pooled ledger

The FINAL validated design (`/tmp/atomic3.py`, `/tmp/atomic_scale.py`; 160
adversarial runs, zero violations): per-KEY budgets `b : ℕ → ℕ` driven by a
DRAIN / REPAY-survivors / PRUNE step against the κ-parametric pooled ledger
`ledgerP` (κ = 8 in the validated instance).

The file is self-contained over the three challenge `Def` imports: the first
half copies (verbatim) the required process infrastructure from the compiled
development `.tmp_claude_hstep_v3.lean` (search paths, BST preservation,
process tree, `costN`/`freshN`/`accessN`/`pathN`/`touchedList`, `sideF`,
`drawP`/`ledgerP`, the `INVS` pair predicates); the second half is PHASE A:

* A.1  per-key budgets `KeyBudgets`, `bGet`/`bSet`/`bSum` and support algebra;
* A.2  `drainKeys` (path-ordered, amount-capped) + EXACT-DRAIN lemmas
       (`bGet_drain_of_not_mem`, `bSum_drainKeys`);
* A.3  `repaySurvivors` (order-processed, budget-capped) + repay bounds
       (`bSum_repay_le`, `bGet_repay_of_uncapped`, `mem_of_repay_changed`);
* A.4  `pruneDead` + monotonicity;
* A.5  the computable SURVIVOR predicate (`survKeys`) and its structure;
* A.6  `atomicStep` and the one-step C1 conservation `atomicStep_C1`;
* A.7  the process fold `batomicAt` and process-level C1 `batomicAt_C1`;
* A.8  the atomic clauses (`bSumOn`), the invariant `INVSA`, base `INVSA_zero`;
* A.9  the EMPIRICAL PINNING of the survivor count: `2·#surv ≤ c + 2` exactly
       on all BSTs with ≤ 9 keys, FALSE in general (pump counterexamples at
       10 and 11 keys included) — hence the explicit repay cap is kept, per
       the design's capped-construction carve-out.
-/

set_option maxHeartbeats 4000000

namespace Splay

def touchedCount (T : List Nat) (c : List Nat) : Nat := (c.filter (fun x => x ∈ T)).length

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

/-! ### The process tree: iterates of the splay process along an access sequence -/

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

/-- One step of the process: accessing `X i` splays the current tree at `X i`. -/
theorem processTree_succ {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (i : Fin n) :
    processTree init X (i + 1) = splay (processTree init X i) (X i) := by
  rw [processTree_succ_dite, dif_pos i.isLt]

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

def touchedUpTo {n : ℕ} (t : ℕ → BinaryTree) (X : Fin n → ℕ) : ℕ → Finset Nat
  | 0 => ∅
  | (i+1) => if h : i < n then touchedUpTo t X i ∪ (searchPath (X ⟨i,h⟩) (t i)).toFinset
             else touchedUpTo t X i

/-- Monotonicity of the touched-set iterates. -/
theorem touchedUpTo_subset_succ {n : ℕ} (t : ℕ → BinaryTree) (X : Fin n → ℕ) (i : ℕ) :
    touchedUpTo t X i ⊆ touchedUpTo t X (i + 1) := by
  by_cases h : i < n
  · simp only [touchedUpTo, dif_pos h]
    exact Finset.subset_union_left
  · simp only [touchedUpTo, dif_neg h]
    exact Finset.Subset.refl _

/-- All touched sets stay inside the key set of the initial tree. -/
theorem touchedUpTo_subset_keys {n : ℕ} (t : ℕ → BinaryTree) (X : Fin n → ℕ)
    (hkeys : ∀ i : Fin n, ∀ y ∈ searchPath (X i) (t i), y ∈ (t 0).toKeyList) :
    ∀ m : ℕ, touchedUpTo t X m ⊆ (t 0).toKeyList.toFinset := by
  intro m
  induction m with
  | zero =>
    simp [touchedUpTo]
  | succ i ih =>
    by_cases h : i < n
    · simp only [touchedUpTo, dif_pos h]
      intro y hy
      rcases Finset.mem_union.mp hy with hy | hy
      · exact ih hy
      · exact List.mem_toFinset.mpr (hkeys ⟨i, h⟩ y (List.mem_toFinset.mp hy))
    · simpa only [touchedUpTo, dif_neg h] using ih



-- ===== L1 deepening (depth lemmas) =====
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

/-! ### Fresh-count bridge: list filter ↔ Finset cardinality -/

/-- **Fresh bridge.**  For a duplicate-free path `P` (e.g. a BST search path,
by `searchPath_nodup`), the list-level fresh count (nodes not in the touched
set `T`) is exactly the `freshN`-style Finset cardinality `(P.toFinset \ T).card`
used by the capstone. -/

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

/-- The diverge suffix: the part of the `y`-search path strictly below the
divergence node from the `q`-search path (copied from the development file). -/
def divergeSuffix (y q : Nat) : BinaryTree → List Nat
  | .empty => []
  | .node l k r =>
      if y = k then []
      else if q = k then (if y < k then searchPath y l else searchPath y r)
      else if y < k ∧ q < k then divergeSuffix y q l
      else if k < y ∧ k < q then divergeSuffix y q r
      else (if y < k then searchPath y l else searchPath y r)

@[simp] theorem divergeSuffix_empty (y q : Nat) : divergeSuffix y q .empty = [] := rfl


-- ===== process-fact package (assembly stage A) =====
def sideF {n : ℕ} (X : Fin n → ℕ) (i : ℕ) : Bool :=
  if h : i < n then
    decide (∀ j : Fin n, (⟨i, h⟩ : Fin n) < j → X j ≤ X ⟨i, h⟩)
  else true

/-- The per-side capped doubled draw (needed by the two-sided ledger below). -/
def draw (kap : ℕ) (c f D : ℕ) : ℕ := min D (2 * c - min (2 * c) (2 * kap * (1 + f)))

-- ===== invariant shell + master discharge (assembly stage A) =====
theorem toKeyList_length (t : BinaryTree) :
    t.toKeyList.length = t.num_nodes := by
  induction t with
  | empty =>
      simp [BinaryTree.toKeyList, BinaryTree.num_nodes]
  | node l k r ihl ihr =>
      simp [BinaryTree.toKeyList, BinaryTree.num_nodes, ihl, ihr]
      omega

/-- Number of touched nodes (with multiplicity) on a list of keys. -/

theorem touchedCount_nil_T (c : List ℕ) : touchedCount [] c = 0 := by
  unfold touchedCount
  rw [List.filter_eq_nil_iff.mpr]
  · rfl
  · intro a _
    simp

/-! ### Search-path length bridges -/

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

/-- **Path-length split**: links + 1 = touched + fresh on any path. -/

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

/-- Doubled draw, capped at the ledger. -/

def ledger (kap : ℕ) (c f : ℕ → ℕ) (s : ℕ → Bool) : ℕ → Bool → ℕ
  | 0, _ => 0
  | (i+1), side =>
      let D := ledger kap c f s i side
      if s i = side then D - draw kap (c i) (f i) D + c i
      else D + 4

/-! ### Totalized access data -/

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

/-! ### Invariant ingredients -/

/-- Touched count of the `v`-search path in the current process tree, against the
current touched set. -/

def tcOf {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ) (v : ℕ) (i : ℕ) : ℕ :=
  touchedCount (touchedList init X i) (searchPath v (processTree init X i))

/-- `j` is the first index `≥ i` on side `b` (and in range). -/

def FirstOwnAfter {n : ℕ} (X : Fin n → ℕ) (i : ℕ) (b : Bool) (j : ℕ) : Prop :=
  i ≤ j ∧ j < n ∧ sideF X j = b ∧ ∀ k, i ≤ k → k < j → sideF X k ≠ b

/-- `(j, k)` is a pair of consecutive future side-`b` indices (both `≥ i`, in range,
with no side-`b` index strictly between). -/

def ConsecOwnAfter {n : ℕ} (X : Fin n → ℕ) (i : ℕ) (b : Bool) (j k : ℕ) : Prop :=
  i ≤ j ∧ j < k ∧ k < n ∧ sideF X j = b ∧ sideF X k = b ∧
    ∀ m, j < m → m < k → sideF X m ≠ b

/-- The access at `i` is itself the first own-side index `≥ i` for its own side. -/

theorem firstOwnAfter_self {n : ℕ} (X : Fin n → ℕ) (i : ℕ) (hi : i < n) :
    FirstOwnAfter X i (sideF X i) i := by
  unfold FirstOwnAfter
  exact ⟨le_rfl, hi, rfl, fun _ hik hki => absurd (lt_of_le_of_lt hik hki) (lt_irrefl i)⟩


-- ===== POOLED shell: ghostAtP/INVP/masterP/hmasterP_of_step =====
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

/-- `(j, k)` is a future pair with `k` the FIRST index after `j` on the OPPOSITE
side (both in range, `j ≥ i`). -/
def FirstOppAfter {n : ℕ} (X : Fin n → ℕ) (i : ℕ) (j k : ℕ) : Prop :=
  i ≤ j ∧ j < k ∧ k < n ∧ sideF X k ≠ sideF X j ∧
    ∀ m, j < m → m < k → sideF X m = sideF X j


/-!
# PHASE A: the per-key ATOMIC ghost (validated design `/tmp/atomic3.py` + `/tmp/atomic_scale.py`)

Per-KEY budgets replace the interval claims of the pooled ghost.  The state is a
finitely-supported budget function `b : ℕ → ℕ` (all nonzero budgets live inside the
key set of the initial tree); one STEP at an access `x` (path `P`, cost `c`, fresh
count `f`, live side `isMin`) is:

1. **DRAIN**: remove `min draw (Σ b on P)` from the path keys' budgets in path
   order, where `draw = 2c − min (2c) (2κ(1+f))` is the uncapped doubled draw;
   `shortfall := (draw − Σ b on P)⁺`.
2. **REPAY**: `+2` on each live-side path key `z` satisfying the SURVIVOR
   predicate `2·keyDepth z (splay t x) ≤ posP z + 3` (`posP` = index on `P`),
   processed in path order, capped at total `≤ c + 2 − shortfall`.
3. **PRUNE**: zero the budgets of all dead keys (`z < x` for a min-side access,
   mirror for max).

Clauses (κ = 8): (C1) `Σ b ≤ ledgerP 8 i`; (C2S) per side, first access `v` of
that side: `2·tc(P_v) ≤ Σ b over P_v's touched keys + 18`; (C3/C4)
suffix-quantified pair clauses over the `INVS` pairs:
`2·tc(suffix.drop e) ≤ Σ b over its touched keys + 12`.
-/

/-! ## A.1 Per-key budgets -/

/-- Per-key (doubled) budgets, modelled as a bare function `ℕ → ℕ`.  All
support-level facts are stated against explicit lists; along the process every
nonzero budget lives inside `keySupp init` (the deduplicated key list of the
initial tree), since only path keys are ever repaid. -/
abbrev KeyBudgets := ℕ → ℕ

/-- Budget lookup (assoc-list interface mirror). -/
def bGet (b : KeyBudgets) (z : ℕ) : ℕ := b z

/-- Point update. -/
def bSet (b : KeyBudgets) (z v : ℕ) : KeyBudgets := fun w => if w = z then v else b w

@[simp] theorem bGet_def (b : KeyBudgets) (z : ℕ) : bGet b z = b z := rfl

theorem bSet_same (b : KeyBudgets) (z v : ℕ) : bSet b z v z = v := by
  simp [bSet]

theorem bSet_other (b : KeyBudgets) (z v : ℕ) {w : ℕ} (h : w ≠ z) :
    bSet b z v w = b w := by
  simp [bSet, h]

/-- Total budget over a support list. -/
def bSum (L : List ℕ) (b : KeyBudgets) : ℕ := (L.map b).sum

@[simp] theorem bSum_nil (b : KeyBudgets) : bSum [] b = 0 := rfl

theorem bSum_cons (z : ℕ) (L : List ℕ) (b : KeyBudgets) :
    bSum (z :: L) b = b z + bSum L b := by
  simp [bSum]

theorem bSum_zero (L : List ℕ) : bSum L (fun _ => 0) = 0 := by
  induction L with
  | nil => rfl
  | cons z L ih => rw [bSum_cons, ih]

theorem bSum_congr {L : List ℕ} {b b' : KeyBudgets}
    (h : ∀ z ∈ L, b z = b' z) : bSum L b = bSum L b' := by
  induction L with
  | nil => rfl
  | cons z L ih =>
      rw [bSum_cons, bSum_cons, h z (by simp),
        ih (fun w hw => h w (by simp [hw]))]

theorem bSum_le_of_pointwise {L : List ℕ} {b b' : KeyBudgets}
    (h : ∀ z ∈ L, b z ≤ b' z) : bSum L b ≤ bSum L b' := by
  induction L with
  | nil => exact Nat.le_refl 0
  | cons z L ih =>
      rw [bSum_cons, bSum_cons]
      exact Nat.add_le_add (h z (by simp)) (ih (fun w hw => h w (by simp [hw])))

theorem bSum_perm (b : KeyBudgets) {K K' : List ℕ} (h : K.Perm K') :
    bSum K b = bSum K' b :=
  (h.map b).sum_eq

/-- Splitting one occurrence off the support. -/
theorem bSum_mem_split (b : KeyBudgets) {K : List ℕ} {z : ℕ} (hz : z ∈ K) :
    bSum K b = b z + bSum (K.erase z) b := by
  rw [bSum_perm b (List.perm_cons_erase hz), bSum_cons]

/-- A duplicate-free sub-support carries at most the full total. -/
theorem bSum_le_of_subset :
    ∀ (P K : List ℕ) (b : KeyBudgets), P.Nodup → (∀ z ∈ P, z ∈ K) →
      bSum P b ≤ bSum K b := by
  intro P
  induction P with
  | nil =>
      intro K b _ _
      exact Nat.zero_le _
  | cons z rest ih =>
      intro K b hP hPK
      rw [List.nodup_cons] at hP
      have hzK : z ∈ K := hPK z (by simp)
      rw [bSum_cons, bSum_mem_split b hzK]
      refine Nat.add_le_add_left (ih (K.erase z) b hP.2 ?_) _
      intro w hw
      have hwz : w ≠ z := fun he => hP.1 (he ▸ hw)
      exact (List.mem_erase_of_ne hwz).mpr (hPK w (by simp [hw]))

/-- Effect of a point update on a duplicate-free support total (additive form,
no truncation). -/
theorem bSum_bSet_add (b : KeyBudgets) (v : ℕ) :
    ∀ {K : List ℕ} {z : ℕ}, K.Nodup → z ∈ K →
      bSum K (bSet b z v) + b z = bSum K b + v := by
  intro K
  induction K with
  | nil =>
      intro z _ hz
      simp at hz
  | cons w rest ih =>
      intro z hK hz
      rw [List.nodup_cons] at hK
      rw [bSum_cons, bSum_cons]
      rcases List.mem_cons.mp hz with hzw | hzr
      · subst hzw
        rw [bSet_same]
        have hrest : bSum rest (bSet b z v) = bSum rest b :=
          bSum_congr (fun u hu => bSet_other b z v (fun he => hK.1 (he ▸ hu)))
        rw [hrest]
        omega
      · have hwz : w ≠ z := fun he => hK.1 (he ▸ hzr)
        rw [bSet_other b z v hwz]
        have h1 := ih hK.2 hzr
        omega

/-! ## A.2 DRAIN: path-ordered, amount-capped greedy drain -/

/-- Drain up to `amount` from the keys of `P`, in path order: each key pays
`min remaining (its budget)` — the per-key mirror of `consumeGreedy`. -/
def drainKeys : List ℕ → ℕ → KeyBudgets → KeyBudgets
  | [], _, b => b
  | z :: rest, amount, b =>
      drainKeys rest (amount - min amount (b z)) (bSet b z (b z - min amount (b z)))

@[simp] theorem drainKeys_nil (amount : ℕ) (b : KeyBudgets) :
    drainKeys [] amount b = b := rfl

theorem drainKeys_cons (z : ℕ) (rest : List ℕ) (amount : ℕ) (b : KeyBudgets) :
    drainKeys (z :: rest) amount b
      = drainKeys rest (amount - min amount (b z))
          (bSet b z (b z - min amount (b z))) := rfl

/-- **THE KEY DRAIN LEMMA**: keys off the path are untouched. -/
theorem bGet_drain_of_not_mem :
    ∀ (P : List ℕ) (amount : ℕ) (b : KeyBudgets) {w : ℕ}, w ∉ P →
      drainKeys P amount b w = b w := by
  intro P
  induction P with
  | nil =>
      intro amount b w _
      rfl
  | cons z rest ih =>
      intro amount b w hw
      rw [drainKeys_cons, ih _ _ (fun hmem => hw (by simp [hmem])),
        bSet_other b z _ (fun he => hw (by simp [he]))]

/-- The drain never increases a budget (pointwise). -/
theorem bGet_drain_le :
    ∀ (P : List ℕ) (amount : ℕ) (b : KeyBudgets) (w : ℕ),
      drainKeys P amount b w ≤ b w := by
  intro P
  induction P with
  | nil =>
      intro amount b w
      exact Nat.le_refl _
  | cons z rest ih =>
      intro amount b w
      rw [drainKeys_cons]
      refine Nat.le_trans (ih _ _ w) ?_
      by_cases hwz : w = z
      · rw [hwz, bSet_same]
        exact Nat.sub_le _ _
      · exact Nat.le_of_eq (bSet_other b z _ hwz)

/-- **EXACT DRAIN** (additive form, mirror of `consumeGreedy_fst`/`_snd`): over
any duplicate-free support `K` containing the duplicate-free path `P`, the
drain removes exactly `min amount (Σ b on P)` from the support total. -/
theorem bSum_drainKeys :
    ∀ (P K : List ℕ) (amount : ℕ) (b : KeyBudgets),
      P.Nodup → K.Nodup → (∀ z ∈ P, z ∈ K) →
      bSum K (drainKeys P amount b) + min amount (bSum P b) = bSum K b := by
  intro P
  induction P with
  | nil =>
      intro K amount b _ _ _
      simp
  | cons z rest ih =>
      intro K amount b hP hK hPK
      rw [List.nodup_cons] at hP
      have hzK : z ∈ K := hPK z (by simp)
      have hIH := ih K (amount - min amount (b z))
        (bSet b z (b z - min amount (b z))) hP.2 hK
        (fun w hw => hPK w (by simp [hw]))
      have hrest_eq : bSum rest (bSet b z (b z - min amount (b z))) = bSum rest b :=
        bSum_congr (fun u hu => bSet_other b z _ (fun he => hP.1 (he ▸ hu)))
      have hKset : bSum K (bSet b z (b z - min amount (b z))) + b z
          = bSum K b + (b z - min amount (b z)) :=
        bSum_bSet_add b _ hK hzK
      rw [hrest_eq] at hIH
      rw [drainKeys_cons, bSum_cons]
      omega

/-- Exact drain, subtraction form: post-drain support total. -/
theorem bSum_drainKeys_eq_sub (P K : List ℕ) (amount : ℕ) (b : KeyBudgets)
    (hP : P.Nodup) (hK : K.Nodup) (hPK : ∀ z ∈ P, z ∈ K) :
    bSum K (drainKeys P amount b) = bSum K b - min amount (bSum P b) := by
  have h := bSum_drainKeys P K amount b hP hK hPK
  omega

/-- Exact drain on the path itself: the drained total is `min amount (Σ b on P)`. -/
theorem bSum_drainKeys_path (P : List ℕ) (amount : ℕ) (b : KeyBudgets)
    (hP : P.Nodup) :
    bSum P (drainKeys P amount b) + min amount (bSum P b) = bSum P b :=
  bSum_drainKeys P P amount b hP hP (fun _ hz => hz)

/-! ## A.3 REPAY: order-processed, budget-capped `+2` on the survivors -/

/-- Pay `+2` to each listed key in order while at least `2` of the budget
remains (the harness loop never repays after the budget drops below `2`, since
the budget is non-increasing — so stopping early is equivalent). -/
def repaySurvivors : List ℕ → ℕ → KeyBudgets → KeyBudgets
  | [], _, b => b
  | z :: rest, budget, b =>
      if 2 ≤ budget then repaySurvivors rest (budget - 2) (bSet b z (b z + 2))
      else b

@[simp] theorem repaySurvivors_nil (budget : ℕ) (b : KeyBudgets) :
    repaySurvivors [] budget b = b := rfl

theorem repaySurvivors_cons (z : ℕ) (rest : List ℕ) (budget : ℕ) (b : KeyBudgets) :
    repaySurvivors (z :: rest) budget b
      = if 2 ≤ budget then repaySurvivors rest (budget - 2) (bSet b z (b z + 2))
        else b := rfl

/-- Keys off the survivor list are untouched by the repay. -/
theorem bGet_repay_of_not_mem :
    ∀ (S : List ℕ) (budget : ℕ) (b : KeyBudgets) {w : ℕ}, w ∉ S →
      repaySurvivors S budget b w = b w := by
  intro S
  induction S with
  | nil =>
      intro budget b w _
      rfl
  | cons z rest ih =>
      intro budget b w hw
      rw [repaySurvivors_cons]
      by_cases hb : 2 ≤ budget
      · rw [if_pos hb, ih _ _ (fun hmem => hw (by simp [hmem])),
          bSet_other b z _ (fun he => hw (by simp [he]))]
      · rw [if_neg hb]

/-- The repay only increases budgets (pointwise). -/
theorem bGet_le_repay :
    ∀ (S : List ℕ) (budget : ℕ) (b : KeyBudgets) (w : ℕ),
      b w ≤ repaySurvivors S budget b w := by
  intro S
  induction S with
  | nil =>
      intro budget b w
      exact Nat.le_refl _
  | cons z rest ih =>
      intro budget b w
      rw [repaySurvivors_cons]
      by_cases hb : 2 ≤ budget
      · rw [if_pos hb]
        refine Nat.le_trans ?_ (ih _ _ w)
        by_cases hwz : w = z
        · rw [hwz, bSet_same]
          omega
        · exact Nat.le_of_eq (bSet_other b z _ hwz).symm
      · rw [if_neg hb]

/-- **REPAY CAP**: the repay adds at most `budget` to a duplicate-free support
total (with `budget := c + 2 − shortfall` this is the requested
`repay total ≤ c + 2 − shortfall`). -/
theorem bSum_repay_le :
    ∀ (S : List ℕ) (budget : ℕ) (b : KeyBudgets) (K : List ℕ), K.Nodup →
      bSum K (repaySurvivors S budget b) ≤ bSum K b + budget := by
  intro S
  induction S with
  | nil =>
      intro budget b K _
      exact Nat.le_add_right _ _
  | cons z rest ih =>
      intro budget b K hK
      rw [repaySurvivors_cons]
      by_cases hb : 2 ≤ budget
      · rw [if_pos hb]
        have h1 := ih (budget - 2) (bSet b z (b z + 2)) K hK
        have h2 : bSum K (bSet b z (b z + 2)) ≤ bSum K b + 2 := by
          by_cases hzK : z ∈ K
          · have h3 := bSum_bSet_add b (b z + 2) hK hzK
            omega
          · have h3 : bSum K (bSet b z (b z + 2)) = bSum K b :=
              bSum_congr (fun u hu => bSet_other b z _ (fun he => hzK (he ▸ hu)))
            omega
        omega
      · rw [if_neg hb]
        exact Nat.le_add_right _ _

/-- **UNCAPPED REPAY**: when the budget covers the whole (duplicate-free)
survivor list, EVERY listed key gains exactly `+2`.  (Phase-B bridge: combine
with a local survivor-count bound to read off the repaid budgets.) -/
theorem bGet_repay_of_uncapped :
    ∀ (S : List ℕ) (budget : ℕ) (b : KeyBudgets), S.Nodup →
      2 * S.length ≤ budget → ∀ w ∈ S, repaySurvivors S budget b w = b w + 2 := by
  intro S
  induction S with
  | nil =>
      intro budget b _ _ w hw
      simp at hw
  | cons z rest ih =>
      intro budget b hS hlen w hw
      rw [List.nodup_cons] at hS
      have hb : 2 ≤ budget := by
        rw [List.length_cons] at hlen
        omega
      rw [repaySurvivors_cons, if_pos hb]
      rcases List.mem_cons.mp hw with hwz | hwr
      · subst hwz
        rw [bGet_repay_of_not_mem rest _ _ hS.1, bSet_same]
      · have hlen' : 2 * rest.length ≤ budget - 2 := by
          rw [List.length_cons] at hlen
          omega
        rw [ih (budget - 2) (bSet b z (b z + 2)) hS.2 hlen' w hwr,
          bSet_other b z _ (fun he => hS.1 (he ▸ hwr))]

/-- Keys changed by the repay lie in the survivor list (repaid ⊆ S). -/
theorem mem_of_repay_changed {S : List ℕ} {budget : ℕ} {b : KeyBudgets} {w : ℕ}
    (h : repaySurvivors S budget b w ≠ b w) : w ∈ S := by
  by_contra hw
  exact h (bGet_repay_of_not_mem S budget b hw)

/-! ## A.4 PRUNE: kill the dead side -/

/-- The live predicate of an access at `x`: a min-side access keeps `z ≥ x`,
a max-side access keeps `z ≤ x`. -/
def liveKey (isMin : Bool) (x z : ℕ) : Bool :=
  if isMin then decide (x ≤ z) else decide (z ≤ x)

/-- Prune: zero out every dead key. -/
def pruneDead (isMin : Bool) (x : ℕ) (b : KeyBudgets) : KeyBudgets :=
  fun z => if liveKey isMin x z then b z else 0

theorem pruneDead_le (isMin : Bool) (x : ℕ) (b : KeyBudgets) (z : ℕ) :
    pruneDead isMin x b z ≤ b z := by
  simp only [pruneDead]
  split
  · exact Nat.le_refl _
  · exact Nat.zero_le _

theorem pruneDead_live (isMin : Bool) (x : ℕ) (b : KeyBudgets) {z : ℕ}
    (h : liveKey isMin x z = true) : pruneDead isMin x b z = b z := by
  simp only [pruneDead]
  rw [if_pos h]

theorem pruneDead_dead (isMin : Bool) (x : ℕ) (b : KeyBudgets) {z : ℕ}
    (h : liveKey isMin x z = false) : pruneDead isMin x b z = 0 := by
  simp only [pruneDead]
  rw [if_neg (by simp [h])]

/-- **PRUNE MONOTONE**: pruning only loses budget. -/
theorem bSum_pruneDead_le (isMin : Bool) (x : ℕ) (b : KeyBudgets) (K : List ℕ) :
    bSum K (pruneDead isMin x b) ≤ bSum K b :=
  bSum_le_of_pointwise (fun z _ => pruneDead_le isMin x b z)

/-! ## A.5 The survivor predicate (computable) -/

/-- Live-side keys of the path, in path order. -/
def debrisKeys (P : List ℕ) (x : ℕ) (isMin : Bool) : List ℕ :=
  P.filter (liveKey isMin x)

/-- The SURVIVOR list: live-side path keys whose post-splay depth has halved
(`2·keyDepth z (splay t x) ≤ posP z + 3`), in path order.  Both `keyDepth`
and the `P`-position are computable. -/
def survKeys (t : BinaryTree) (P : List ℕ) (x : ℕ) (isMin : Bool) : List ℕ :=
  (debrisKeys P x isMin).filter
    (fun z => 2 * keyDepth z (splay t x) ≤ P.idxOf z + 3)

theorem mem_debrisKeys {P : List ℕ} {x : ℕ} {isMin : Bool} {z : ℕ} :
    z ∈ debrisKeys P x isMin ↔ z ∈ P ∧ liveKey isMin x z = true :=
  List.mem_filter

theorem mem_survKeys {t : BinaryTree} {P : List ℕ} {x : ℕ} {isMin : Bool} {z : ℕ} :
    z ∈ survKeys t P x isMin
      ↔ z ∈ P ∧ liveKey isMin x z = true
          ∧ 2 * keyDepth z (splay t x) ≤ P.idxOf z + 3 := by
  simp only [survKeys, List.mem_filter, mem_debrisKeys, decide_eq_true_eq, and_assoc]

/-- Survivors are live-side path keys (repaid ⊆ live-side `P`-keys, part 1). -/
theorem survKeys_subset_debris {t : BinaryTree} {P : List ℕ} {x : ℕ} {isMin : Bool} :
    ∀ z ∈ survKeys t P x isMin, z ∈ debrisKeys P x isMin :=
  fun _ hz => List.mem_of_mem_filter hz

/-- Live-side keys lie on the path (repaid ⊆ live-side `P`-keys, part 2). -/
theorem debrisKeys_subset_path {P : List ℕ} {x : ℕ} {isMin : Bool} :
    ∀ z ∈ debrisKeys P x isMin, z ∈ P :=
  fun _ hz => List.mem_of_mem_filter hz

theorem survKeys_subset_path {t : BinaryTree} {P : List ℕ} {x : ℕ} {isMin : Bool} :
    ∀ z ∈ survKeys t P x isMin, z ∈ P :=
  fun _ hz => List.mem_of_mem_filter (List.mem_of_mem_filter hz)

theorem survKeys_live {t : BinaryTree} {P : List ℕ} {x : ℕ} {isMin : Bool} :
    ∀ z ∈ survKeys t P x isMin, liveKey isMin x z = true :=
  fun _ hz => (mem_debrisKeys.mp (List.mem_of_mem_filter hz)).2

theorem survKeys_nodup (t : BinaryTree) {P : List ℕ} (x : ℕ) (isMin : Bool)
    (hP : P.Nodup) : (survKeys t P x isMin).Nodup :=
  (hP.filter _).filter _

theorem survKeys_length_le (t : BinaryTree) (P : List ℕ) (x : ℕ) (isMin : Bool) :
    (survKeys t P x isMin).length ≤ P.length :=
  Nat.le_trans (List.length_filter_le _ _) (List.length_filter_le _ _)

/-! ## A.6 The atomic step -/

/-- The uncapped doubled draw `(2c − 2κ(1+f))⁺`. -/
def drawA (kap c f : ℕ) : ℕ := 2 * c - min (2 * c) (2 * kap * (1 + f))

/-- The drain shortfall `(draw − Σ b on P)⁺`. -/
def shortfallA (kap : ℕ) (P : List ℕ) (c f : ℕ) (b : KeyBudgets) : ℕ :=
  drawA kap c f - min (drawA kap c f) (bSum P b)

/-- The repay cap `c + 2 − shortfall`. -/
def capA (kap : ℕ) (P : List ℕ) (c f : ℕ) (b : KeyBudgets) : ℕ :=
  c + 2 - shortfallA kap P c f b

/-- The ledger draw is the `D`-capped atomic draw. -/
theorem drawP_eq (kap c f D : ℕ) : drawP kap c f D = min D (drawA kap c f) := rfl

/-- One atomic step at an access (path `P`, survivor list `S`, cost `c`, fresh
count `f`, accessed key `x`, live side `isMin`): DRAIN the uncapped doubled
draw from the path keys in path order, REPAY `+2` to the survivors in order
under the cap `c + 2 − shortfall`, then PRUNE the dead side.  (The touched set
plays no role inside the step — it only enters the clauses.) -/
def atomicStep (kap : ℕ) (P S : List ℕ) (c f x : ℕ) (isMin : Bool)
    (b : KeyBudgets) : KeyBudgets :=
  pruneDead isMin x
    (repaySurvivors S (capA kap P c f b) (drainKeys P (drawA kap c f) b))

theorem atomicStep_def (kap : ℕ) (P S : List ℕ) (c f x : ℕ) (isMin : Bool)
    (b : KeyBudgets) :
    atomicStep kap P S c f x isMin b
      = pruneDead isMin x
          (repaySurvivors S (capA kap P c f b)
            (drainKeys P (drawA kap c f) b)) := rfl

/-- The pure arithmetic core of the one-step C1 conservation.  The COVER
hypothesis `A ≤ V + (c + 2)` (shortfall at most the flat repay credit) is
necessary: without it a draw exceeding the path budgets by more than `c + 2`
strands off-path budget above the ledger drop.  In the validated design the
cover is supplied by the C2S clause at κ = 8: `2·tc ≤ Σb_touched + 18` gives
`draw = (2·tc − 18 − 14·f)⁺ ≤ Σb_touched-on-P ≤ Σb-on-P`, i.e. shortfall `0`
(the same funnel as the pooled `ghost_C1P_step`'s `hcover`). -/
theorem atomic_C1_arith (A V SK D dRes rRes pRes c : ℕ)
    (hdrain : dRes + min A V = SK)
    (hb : SK ≤ D)
    (hrepay : rRes ≤ dRes + (c + 2 - (A - min A V)))
    (hprune : pRes ≤ rRes)
    (hcover : A ≤ V + (c + 2)) :
    pRes ≤ D - min D A + c + 2 := by
  omega

/-- **C1 CONSERVATION across one atomic step** (drain-exact + repay-cap +
prune-monotone): if the support total is within `D` and the cover holds
(shortfall `≤ c + 2`; the C2S clause gives shortfall `= 0` at κ = 8), after
the step the total is within the ledger update `D − drawP + c + 2`. -/
theorem atomicStep_C1 (kap : ℕ) (P S : List ℕ) (c f x : ℕ) (isMin : Bool)
    (b : KeyBudgets) (K : List ℕ) (D : ℕ)
    (hP : P.Nodup) (hK : K.Nodup) (hPK : ∀ z ∈ P, z ∈ K)
    (hb : bSum K b ≤ D)
    (hcover : drawA kap c f ≤ bSum P b + (c + 2)) :
    bSum K (atomicStep kap P S c f x isMin b) ≤ D - drawP kap c f D + c + 2 := by
  have hdrain := bSum_drainKeys P K (drawA kap c f) b hP hK hPK
  have hrepay := bSum_repay_le S (capA kap P c f b)
    (drainKeys P (drawA kap c f) b) K hK
  have hcap : capA kap P c f b
      = c + 2 - (drawA kap c f - min (drawA kap c f) (bSum P b)) := rfl
  rw [hcap] at hrepay
  have hprune := bSum_pruneDead_le isMin x
    (repaySurvivors S (capA kap P c f b) (drainKeys P (drawA kap c f) b)) K
  rw [atomicStep_def, drawP_eq]
  exact atomic_C1_arith (drawA kap c f) (bSum P b) (bSum K b) D
    (bSum K (drainKeys P (drawA kap c f) b))
    (bSum K (repaySurvivors S (capA kap P c f b) (drainKeys P (drawA kap c f) b)))
    (bSum K (pruneDead isMin x
      (repaySurvivors S (capA kap P c f b) (drainKeys P (drawA kap c f) b))))
    c hdrain hb hrepay hprune hcover

/-- Unconditional SAFETY for the atomic step: the support total never exceeds
`D + c + 2` (no cover, no nodup of `P` needed). -/
theorem atomicStep_C1_safe (kap : ℕ) (P S : List ℕ) (c f x : ℕ) (isMin : Bool)
    (b : KeyBudgets) (K : List ℕ) (D : ℕ) (hK : K.Nodup)
    (hb : bSum K b ≤ D) :
    bSum K (atomicStep kap P S c f x isMin b) ≤ D + c + 2 := by
  have hdrain : bSum K (drainKeys P (drawA kap c f) b) ≤ bSum K b :=
    bSum_le_of_pointwise (fun z _ => bGet_drain_le P _ b z)
  have hrepay := bSum_repay_le S (capA kap P c f b)
    (drainKeys P (drawA kap c f) b) K hK
  have hprune := bSum_pruneDead_le isMin x
    (repaySurvivors S (capA kap P c f b) (drainKeys P (drawA kap c f) b)) K
  have hcap : capA kap P c f b ≤ c + 2 := by
    unfold capA
    exact Nat.sub_le _ _
  rw [atomicStep_def]
  omega

/-- Off-path live keys are exactly preserved when not repaid. -/
theorem atomicStep_get_off_path (kap : ℕ) (P S : List ℕ) (c f x : ℕ)
    (isMin : Bool) (b : KeyBudgets) {w : ℕ} (hwP : w ∉ P) (hwS : w ∉ S)
    (hlive : liveKey isMin x w = true) :
    atomicStep kap P S c f x isMin b w = b w := by
  rw [atomicStep_def, pruneDead_live _ _ _ hlive,
    bGet_repay_of_not_mem _ _ _ hwS, bGet_drain_of_not_mem _ _ _ hwP]

/-- Dead keys are zeroed by the step. -/
theorem atomicStep_get_dead (kap : ℕ) (P S : List ℕ) (c f x : ℕ)
    (isMin : Bool) (b : KeyBudgets) {w : ℕ}
    (hdead : liveKey isMin x w = false) :
    atomicStep kap P S c f x isMin b w = 0 := by
  rw [atomicStep_def, pruneDead_dead _ _ _ hdead]

/-- Off-path live keys never lose budget across a step. -/
theorem bGet_le_atomicStep_off_path (kap : ℕ) (P S : List ℕ) (c f x : ℕ)
    (isMin : Bool) (b : KeyBudgets) {w : ℕ} (hwP : w ∉ P)
    (hlive : liveKey isMin x w = true) :
    b w ≤ atomicStep kap P S c f x isMin b w := by
  rw [atomicStep_def, pruneDead_live _ _ _ hlive]
  calc b w = drainKeys P (drawA kap c f) b w :=
        (bGet_drain_of_not_mem P _ b hwP).symm
    _ ≤ repaySurvivors S (capA kap P c f b) (drainKeys P (drawA kap c f) b) w :=
        bGet_le_repay _ _ _ _

/-! ## A.7 The process fold -/

/-- The survivor list of the `i`-th access in the process. -/
def survN {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ) (i : ℕ) : List ℕ :=
  survKeys (processTree init X i) (pathN init X i) (accessN X i) (!(sideF X i))

/-- The per-key ghost state after `i` accesses: every access takes the atomic
step with prune direction `!(sideF X i)` (the live side of `X i`). -/
def batomicAt {n : ℕ} (kap : ℕ) (init : BinaryTree) (X : Fin n → ℕ) :
    ℕ → KeyBudgets
  | 0 => fun _ => 0
  | (i+1) =>
      atomicStep kap (pathN init X i) (survN init X i) (costN init X i)
        (freshN init X i) (accessN X i) (!(sideF X i)) (batomicAt kap init X i)

@[simp] theorem batomicAt_zero {n : ℕ} (kap : ℕ) (init : BinaryTree)
    (X : Fin n → ℕ) : batomicAt kap init X 0 = fun _ => 0 := rfl

theorem batomicAt_succ {n : ℕ} (kap : ℕ) (init : BinaryTree) (X : Fin n → ℕ)
    (i : ℕ) :
    batomicAt kap init X (i+1)
      = atomicStep kap (pathN init X i) (survN init X i) (costN init X i)
          (freshN init X i) (accessN X i) (!(sideF X i))
          (batomicAt kap init X i) := rfl

/-- Support of the process budgets: the (deduplicated) key list of the initial
tree. -/
def keySupp (init : BinaryTree) : List ℕ := init.toKeyList.dedup

theorem keySupp_nodup (init : BinaryTree) : (keySupp init).Nodup :=
  List.nodup_dedup _

theorem mem_keySupp {init : BinaryTree} {z : ℕ} :
    z ∈ keySupp init ↔ z ∈ init.toKeyList :=
  List.mem_dedup

/-- The global budget total (`Σ b` of the design). -/
def bTotal (init : BinaryTree) (b : KeyBudgets) : ℕ := bSum (keySupp init) b

theorem pathN_nodup {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (hbst : IsBST init) (i : ℕ) : (pathN init X i).Nodup := by
  unfold pathN
  by_cases h : i < n
  · rw [dif_pos h]
    exact searchPath_nodup _ _ (processTree_isBST init X hbst i)
  · rw [dif_neg h]
    exact List.nodup_nil

theorem pathN_subset_keySupp {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (i : ℕ) : ∀ z ∈ pathN init X i, z ∈ keySupp init := by
  intro z hz
  unfold pathN at hz
  by_cases h : i < n
  · rw [dif_pos h] at hz
    have h1 := searchPath_subset_toKeyList (X ⟨i, h⟩) (processTree init X i) z hz
    rw [processTree_toKeyList] at h1
    exact mem_keySupp.mpr h1
  · rw [dif_neg h] at hz
    simp at hz

/-- C1 holds at the start of the process (empty budgets, zero ledger). -/
theorem batomicAt_C1_zero {n : ℕ} (kap : ℕ) (init : BinaryTree) (X : Fin n → ℕ) :
    bSum (keySupp init) (batomicAt kap init X 0)
      ≤ ledgerP kap (costN init X) (freshN init X) 0 := by
  rw [batomicAt_zero, bSum_zero]
  exact Nat.zero_le _

/-- **C1 propagation across one process step, given the cover** (the atomic
mirror of `INVP_C1_succ_of_cover`): the per-step cover is what the C2S clause
of `INVSA` supplies at κ = 8, so the C1 clause reproduces inside the
invariant induction of Phase B. -/
theorem batomicAt_C1_succ_of_cover {n : ℕ} (kap : ℕ) (init : BinaryTree)
    (X : Fin n → ℕ) (hbst : IsBST init) (i : ℕ)
    (hC1 : bSum (keySupp init) (batomicAt kap init X i)
      ≤ ledgerP kap (costN init X) (freshN init X) i)
    (hcover : drawA kap (costN init X i) (freshN init X i)
      ≤ bSum (pathN init X i) (batomicAt kap init X i) + (costN init X i + 2)) :
    bSum (keySupp init) (batomicAt kap init X (i+1))
      ≤ ledgerP kap (costN init X) (freshN init X) (i+1) := by
  rw [batomicAt_succ, ledgerP_succ]
  exact atomicStep_C1 kap (pathN init X i) (survN init X i) (costN init X i)
    (freshN init X i) (accessN X i) (!(sideF X i)) (batomicAt kap init X i)
    (keySupp init) (ledgerP kap (costN init X) (freshN init X) i)
    (pathN_nodup init X hbst i) (keySupp_nodup init)
    (pathN_subset_keySupp init X i) hC1 hcover

/-- Unconditional process safety: the budget total after `i` steps is at most
the running `Σ (c j + 2)` (no cover needed; bounds any C1 escape). -/
theorem batomicAt_le_costSum {n : ℕ} (kap : ℕ) (init : BinaryTree)
    (X : Fin n → ℕ) :
    ∀ i : ℕ, bSum (keySupp init) (batomicAt kap init X i)
      ≤ ∑ j ∈ Finset.range i, (costN init X j + 2) := by
  intro i
  induction i with
  | zero =>
      rw [batomicAt_zero, bSum_zero]
      exact Nat.zero_le _
  | succ i ih =>
      rw [batomicAt_succ, Finset.sum_range_succ]
      have h := atomicStep_C1_safe kap (pathN init X i) (survN init X i)
        (costN init X i) (freshN init X i) (accessN X i) (!(sideF X i))
        (batomicAt kap init X i) (keySupp init)
        (∑ j ∈ Finset.range i, (costN init X j + 2)) (keySupp_nodup init) ih
      omega

/-! ## A.8 The atomic clauses and the invariant -/

/-- Budget sum over the TOUCHED keys of a list (the atomic met-sum). -/
def bSumOn (T L : List ℕ) (b : KeyBudgets) : ℕ :=
  bSum (L.filter (fun z => z ∈ T)) b

/-- The ATOMIC strong invariant (κ-parametric; the validated design is κ = 8):
* (C1) conservation: `Σ b ≤ ledgerP κ i`;
* (C2S) per side, for the FIRST access `j ≥ i` of that side: twice the touched
  count of its current path is covered by the path's touched budgets `+18`;
* (C3) for every pair of CONSECUTIVE future same-side accesses `(j, k)` and
  every `e`: twice the touched count of `(divergeSuffix (X k) (X j)).drop e`
  is covered by its touched budgets `+12`;
* (C4) the same clause over the `FirstOppAfter` cross pairs.
The pairs and suffixes are EXACTLY those of the interval-ghost `INVS`. -/
def INVSA {n : ℕ} (kap : ℕ) (init : BinaryTree) (X : Fin n → ℕ) (i : ℕ) : Prop :=
  (bSum (keySupp init) (batomicAt kap init X i)
      ≤ ledgerP kap (costN init X) (freshN init X) i)
  ∧ (∀ (b : Bool) (j : ℕ), FirstOwnAfter X i b j →
      2 * tcOf init X (accessN X j) i
        ≤ bSumOn (touchedList init X i)
            (searchPath (accessN X j) (processTree init X i))
            (batomicAt kap init X i) + 18)
  ∧ (∀ (b : Bool) (j k : ℕ), ConsecOwnAfter X i b j k → ∀ (e : ℕ),
      2 * touchedCount (touchedList init X i)
          ((divergeSuffix (accessN X k) (accessN X j) (processTree init X i)).drop e)
        ≤ bSumOn (touchedList init X i)
            ((divergeSuffix (accessN X k) (accessN X j) (processTree init X i)).drop e)
            (batomicAt kap init X i) + 12)
  ∧ (∀ (j k : ℕ), FirstOppAfter X i j k → ∀ (e : ℕ),
      2 * touchedCount (touchedList init X i)
          ((divergeSuffix (accessN X k) (accessN X j) (processTree init X i)).drop e)
        ≤ bSumOn (touchedList init X i)
            ((divergeSuffix (accessN X k) (accessN X j) (processTree init X i)).drop e)
            (batomicAt kap init X i) + 12)

/-- **Base case**: the atomic invariant holds at step `0` (empty budgets, zero
ledger, empty touched set). -/
theorem INVSA_zero {n : ℕ} (kap : ℕ) (init : BinaryTree) (X : Fin n → ℕ) :
    INVSA kap init X 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [batomicAt_zero, bSum_zero]
    exact Nat.zero_le _
  · intro b j _
    have h0 : tcOf init X (accessN X j) 0 = 0 := by
      show touchedCount (touchedList init X 0) _ = 0
      rw [touchedList_zero, touchedCount_nil_T]
    rw [h0]
    omega
  · intro b j k _ e
    have h0 : touchedCount (touchedList init X 0)
        ((divergeSuffix (accessN X k) (accessN X j) (processTree init X 0)).drop e)
          = 0 := by
      rw [touchedList_zero, touchedCount_nil_T]
    rw [h0]
    omega
  · intro j k _ e
    have h0 : touchedCount (touchedList init X 0)
        ((divergeSuffix (accessN X k) (accessN X j) (processTree init X 0)).drop e)
          = 0 := by
      rw [touchedList_zero, touchedCount_nil_T]
    rw [h0]
    omega

/-! ## A.9 Empirical pinning of the survivor count (deliverable 5)

The conjectured structural bound was `#survivors ≤ (c + 3) / 2`, i.e.
`2·#surv ≤ c + 3`.  EXHAUSTIVE evaluation over ALL BSTs on `n ≤ 9` keys, all
accessed keys, both sides (see `survSlacks` below; `n ≤ 7` is re-checked
in-file, `n = 8, 9` were checked offline with the same code) pins the exact
small-tree bound as

  `2·#surv ≤ c + 2`   (tight, slack `0` is attained from `n = 2` on).

However the bound is FALSE for general BSTs: zag-zag steps above a deep
zig-zig spine RAISE the position of every spine key by `2` while keeping its
post-splay depth, pumping the survivor slack without limit:

* `pumpTree9` (10 keys, `c = 9`, one zag-zag pair over a 6-spine):
  `#surv = 6`, `2·#surv = 12 = c + 3` — the `c + 2` bound already fails;
* `pumpTree` (11 keys, `c = 10`, two zag-zag pairs over a 7-spine):
  `#surv = 7`, `2·#surv = 14 = c + 4 > c + 3` — the conjectured bound fails;
* extending the spine under two zag-zag pairs gives `2·#surv − c → ∞`.

Conclusion (per the design note): the CAPPED construction is the right one —
the explicit cap `c + 2 − shortfall` is kept in `atomicStep` (it is exactly
what `atomicStep_C1` consumes), the cap-free repay total bound is provably
unavailable, and Phase-B clause proofs should use `bGet_repay_of_uncapped`
together with per-instance survivor-count bounds (or track the capped prefix
of the survivor list directly). -/

/-- All BSTs on the key interval `[lo, lo+len)` (`fuel ≥ len` suffices). -/
def allBSTsAux : ℕ → ℕ → ℕ → List BinaryTree
  | 0, _, _ => [BinaryTree.empty]
  | fuel + 1, lo, len =>
      if len = 0 then [BinaryTree.empty]
      else
        (List.range len).flatMap (fun j =>
          (allBSTsAux fuel lo j).flatMap (fun l =>
            (allBSTsAux fuel (lo + j + 1) (len - j - 1)).map (fun r =>
              BinaryTree.node l (lo + j) r)))

/-- All BSTs on keys `{0, …, n−1}`. -/
def allBSTs (n : ℕ) : List BinaryTree := allBSTsAux n 0 n

/-- Survivor count of a single access. -/
def survCountOf (t : BinaryTree) (x : ℕ) (isMin : Bool) : ℕ :=
  (survKeys t (searchPath x t) x isMin).length

/-- All slacks `2·#surv − (c + 2)` over all BSTs on `n` keys, all accessed
keys, both sides. -/
def survSlacks (n : ℕ) : List ℤ :=
  (allBSTs n).flatMap (fun t =>
    (List.range n).flatMap (fun x =>
      [true, false].map (fun isMin =>
        (2 * survCountOf t x isMin : ℤ)
          - (((searchPath x t).length - 1 : ℕ) + 2 : ℤ))))

-- Exhaustive pinning, `n = 1, …, 7`: every maximum is `0`, i.e. `2·#surv ≤ c + 2`
-- on all BSTs with at most 7 keys (offline runs extend this to `n = 8, 9`).
#eval (List.range 7).map (fun n => (survSlacks (n + 1)).foldl max (-1000))
-- expected: [0, 0, 0, 0, 0, 0, 0]

/-- Left spine holding keys `k - m, …, k` with root `k` (deepest key `k − m`). -/
def spineDown : ℕ → ℕ → BinaryTree
  | 0, k => .node .empty k .empty
  | (m+1), k => .node (spineDown m (k-1)) k .empty

/-- 10 keys, `c = 9`: one zag-zag pair over a 6-spine; `2·#surv = c + 3`. -/
def pumpTree9 : BinaryTree :=
  .node .empty 0 (.node .empty 1 (.node .empty 2 (.node .empty 3 (spineDown 5 9))))

/-- 11 keys, `c = 10`: two zag-zag pairs over a 7-spine; `2·#surv = c + 4`. -/
def pumpTree : BinaryTree :=
  .node .empty 0 (.node .empty 1 (.node .empty 2 (.node .empty 3 (spineDown 6 10))))

#eval ((searchPath 4 pumpTree9).length - 1, survCountOf pumpTree9 4 true)
-- expected: (9, 6) — `2·6 = 12 = 9 + 3`: the `c + 2` pin breaks at `n = 10`
#eval ((searchPath 4 pumpTree).length - 1, survCountOf pumpTree 4 true)
-- expected: (10, 7) — `2·7 = 14 = 10 + 4 > c + 3`: the conjectured bound fails

end Splay

#print axioms Splay.bSum_drainKeys
#print axioms Splay.bGet_drain_of_not_mem
#print axioms Splay.bSum_repay_le
#print axioms Splay.bGet_repay_of_uncapped
#print axioms Splay.atomicStep_C1
#print axioms Splay.atomicStep_C1_safe
#print axioms Splay.batomicAt_C1_succ_of_cover
#print axioms Splay.batomicAt_le_costSum
#print axioms Splay.INVSA_zero
