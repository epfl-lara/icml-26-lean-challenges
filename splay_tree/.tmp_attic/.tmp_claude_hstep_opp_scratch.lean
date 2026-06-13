import Challenges.Splay_Tree.DevBase

set_option maxHeartbeats 4000000

namespace Splay

/-! # The opposite-side step lemma `hstepOpp` (conditional assembly)

An access at index `i` on side `sideF X i ≠ b` updates side `b`'s ghost by
`ghostStepOppPrune (accessN X i) (!(sideF X i))`: the pool gains `4` and the
claims are pruned to the live side of the accessed key.  The ledger gains `4`.

* (C1) is discharged UNCONDITIONALLY below (`INVside_C1_succ_opp`).
* (C2)/(C3) are discharged from four explicitly-named analytic kernels
  (`hC2tc`/`hC2met`/`hC3tc`/`hC3met`), each stated in exactly the shape consumed.
-/

/-! ## Boolean side bookkeeping -/

theorem not_sideF_eq_of_ne {n : ℕ} (X : Fin n → ℕ) (i : ℕ) (b : Bool)
    (h : sideF X i ≠ b) : (!(sideF X i)) = b := by
  cases hs : sideF X i <;> cases b <;> simp_all

/-! ## The ledger's opposite-side update -/

theorem ledger_succ_opp (kap : ℕ) (c f : ℕ → ℕ) (s : ℕ → Bool) (i : ℕ) (side : Bool)
    (h : s i ≠ side) :
    ledger kap c f s (i+1) side = ledger kap c f s i side + 4 := by
  simp only [ledger]
  rw [if_neg h]

/-! ## Ghost-state bookkeeping across an opposite-side step -/

theorem ghostAt_pool_succ_opp {n : ℕ} (kap : ℕ) (init : BinaryTree) (X : Fin n → ℕ)
    (i : ℕ) (b : Bool) (h : sideF X i ≠ b) :
    (ghostAt kap init X (i+1) b).pool = (ghostAt kap init X i b).pool + 4 := by
  rw [ghostAt_succ_opp kap init X i b h]
  rfl

theorem ghostAt_claims_succ_opp {n : ℕ} (kap : ℕ) (init : BinaryTree) (X : Fin n → ℕ)
    (i : ℕ) (b : Bool) (h : sideF X i ≠ b) :
    (ghostAt kap init X (i+1) b).claims
      = pruneClaims (!(sideF X i)) (accessN X i) (ghostAt kap init X i b).claims := by
  rw [ghostAt_succ_opp kap init X i b h]
  rfl

theorem claimsTotal_succ_opp_le {n : ℕ} (kap : ℕ) (init : BinaryTree) (X : Fin n → ℕ)
    (i : ℕ) (b : Bool) (h : sideF X i ≠ b) :
    claimsTotal (ghostAt kap init X (i+1) b) ≤ claimsTotal (ghostAt kap init X i b) := by
  show claimsListTotal (ghostAt kap init X (i+1) b).claims
      ≤ claimsListTotal (ghostAt kap init X i b).claims
  rw [ghostAt_claims_succ_opp kap init X i b h]
  exact claimsListTotal_prune_le _ _ _

/-! ## (C1) across an opposite-side step — UNCONDITIONAL -/

theorem INVside_C1_succ_opp {n : ℕ} (kap : ℕ) (init : BinaryTree) (X : Fin n → ℕ)
    (i : ℕ) (b : Bool) (h : sideF X i ≠ b)
    (hC1 : claimsTotal (ghostAt kap init X i b) + (ghostAt kap init X i b).pool
        ≤ ledger kap (costN init X) (freshN init X) (sideF X) i b) :
    claimsTotal (ghostAt kap init X (i+1) b) + (ghostAt kap init X (i+1) b).pool
      ≤ ledger kap (costN init X) (freshN init X) (sideF X) (i+1) b := by
  have h1 := claimsTotal_succ_opp_le kap init X i b h
  have h2 := ghostAt_pool_succ_opp kap init X i b h
  rw [ledger_succ_opp kap (costN init X) (freshN init X) (sideF X) i b h]
  omega

/-! ## Target-index transfer across an opposite-side step -/

theorem firstOwnAfter_succ_opp {n : ℕ} (X : Fin n → ℕ) (i : ℕ) (b : Bool)
    (h : sideF X i ≠ b) (j : ℕ) (hj : FirstOwnAfter X (i+1) b j) :
    FirstOwnAfter X i b j := by
  obtain ⟨h1, h2, h3, h4⟩ := hj
  refine ⟨by omega, h2, h3, ?_⟩
  intro k hik hkj
  rcases Nat.eq_or_lt_of_le hik with rfl | hlt
  · exact h
  · exact h4 k (by omega) hkj

theorem consecOwnAfter_succ_opp {n : ℕ} (X : Fin n → ℕ) (i : ℕ) (b : Bool)
    (j k : ℕ) (hjk : ConsecOwnAfter X (i+1) b j k) :
    ConsecOwnAfter X i b j k := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hjk
  exact ⟨by omega, h2, h3, h4, h5, h6⟩

/-! ## Totalized-data unfolds at in-range indices -/

theorem accessN_eq {n : ℕ} (X : Fin n → ℕ) (i : ℕ) (hi : i < n) :
    accessN X i = X ⟨i, hi⟩ := by
  unfold accessN
  rw [dif_pos hi]

theorem pathN_eq {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ) (i : ℕ) (hi : i < n) :
    pathN init X i = searchPath (accessN X i) (processTree init X i) := by
  unfold pathN
  rw [dif_pos hi, accessN_eq X i hi]

theorem touchedList_succ_eq {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (i : ℕ) (hi : i < n) :
    touchedList init X (i+1)
      = touchedList init X i ++ searchPath (accessN X i) (processTree init X i) := by
  rw [touchedList_succ, pathN_eq init X i hi]

theorem processTree_succ_eq {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (i : ℕ) (hi : i < n) :
    processTree init X (i+1) = splay (processTree init X i) (accessN X i) := by
  rw [processTree_succ_dite, dif_pos hi, accessN_eq X i hi]

theorem processTree_ne_empty' {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (hsize : init.num_nodes = n) (hn : 0 < n) (i : ℕ) :
    processTree init X i ≠ .empty := by
  obtain ⟨l, k, r, h⟩ := processTree_ne_empty init X hsize hn i
  rw [h]
  exact fun hc => BinaryTree.noConfusion hc

/-! ## The W6 route for the (C2) touched-count kernel

If every node shared by the current access path and the target's path is already
touched, the proven core `touchedCount_sharedTouched_splay_le` bounds the step
deepening by `+2` — i.e. exactly the `hC2tc` kernel consumed by `hstepOpp`. -/

theorem tcOf_succ_le_of_sharedTouched {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (hsize : init.num_nodes = n) (hbst : IsBST init)
    (i : ℕ) (hi : i < n) (v : ℕ)
    (hsh : ∀ z ∈ searchPath (accessN X i) (processTree init X i),
        z ∈ searchPath v (processTree init X i) → z ∈ touchedList init X i) :
    tcOf init X v (i+1) ≤ tcOf init X v i + 2 := by
  have hbstI : IsBST (processTree init X i) := processTree_isBST init X hbst i
  have hne : processTree init X i ≠ .empty :=
    processTree_ne_empty' init X hsize (by omega) i
  show touchedCount (touchedList init X (i+1))
        (searchPath v (processTree init X (i+1)))
      ≤ touchedCount (touchedList init X i)
          (searchPath v (processTree init X i)) + 2
  rw [touchedList_succ_eq init X i hi, processTree_succ_eq init X i hi]
  exact touchedCount_sharedTouched_splay_le _ _ _ _ hbstI hne hsh

/-! ## Partial met-sum preservation across the prune (root-witness form) -/

/-- A present key lies on its own search path (BST). -/

theorem self_mem_searchPath (q : ℕ) :
    ∀ (t : BinaryTree), IsBST t → q ∈ t.toKeyList → q ∈ searchPath q t := by
  intro t
  induction t with
  | empty => intro _ h; simp [BinaryTree.toKeyList] at h
  | node l k r ihl ihr =>
    intro hbst hmem
    rcases isBST_node_iff.mp hbst with ⟨hFl, hFr, hbl, hbr⟩
    by_cases h1 : q = k
    · rw [searchPath_node_self h1]
      simp [h1]
    · by_cases h2 : q < k
      · rw [searchPath_node_lt h2]
        exact List.mem_cons_of_mem _ (ihl hbl (mem_toKeyList_left hFr h2 hmem))
      · have h3 : k < q := by omega
        rw [searchPath_node_gt h3]
        exact List.mem_cons_of_mem _ (ihr hbr (mem_toKeyList_right hFl h3 hmem))

/-- Budget comparison: a sub-selection `p` of the original claims is dominated by a
selection `m` of the clipped survivors, provided every `p`-claim survives (`a`) and
its image is selected (`m`), with the budget field preserved by the clip `f`. -/

theorem claimsListTotal_filter_le_map_filter (cs : List GhostClaim)
    (p a m : GhostClaim → Bool) (f : GhostClaim → GhostClaim)
    (hf : ∀ cl, (f cl).r = cl.r)
    (h : ∀ cl, p cl = true → a cl = true ∧ m (f cl) = true) :
    claimsListTotal (cs.filter p)
      ≤ claimsListTotal (((cs.filter a).map f).filter m) := by
  induction cs with
  | nil => simp
  | cons cl rest ih =>
    rw [List.filter_cons]
    by_cases hp : p cl = true
    · obtain ⟨ha, hm⟩ := h cl hp
      rw [if_pos hp, List.filter_cons, if_pos ha, List.map_cons, List.filter_cons,
        if_pos hm, claimsListTotal_cons, claimsListTotal_cons, hf]
      exact Nat.add_le_add_left ih _
    · rw [if_neg hp]
      refine le_trans ih ?_
      rw [List.filter_cons]
      by_cases ha : a cl = true
      · rw [if_pos ha, List.map_cons, List.filter_cons]
        by_cases hm : m (f cl) = true
        · rw [if_pos hm, claimsListTotal_cons]
          exact Nat.le_add_left _ _
        · rw [if_neg hm]
      · rw [if_neg ha]

/-- **Partial met-sum preservation.**  After an opposite-side step, every claim of
the previous ghost state whose interval STRADDLES the accessed key survives the
prune and is met on EVERY search path of the new tree (witness: the new root
`accessN X i`, which is both touched and the head of every new search path).
The met-sum kernel `hC2met` of `hstepOpp` is thus open exactly for the claims
lying strictly on the far side of the accessed key. -/

theorem metSum_succ_opp_ge_straddle {n : ℕ} (kap : ℕ) (init : BinaryTree)
    (X : Fin n → ℕ) (hbst : IsBST init) (hmem : ∀ k : Fin n, X k ∈ init.toKeyList)
    (i : ℕ) (hi : i < n) (b : Bool) (h : sideF X i ≠ b) (v : ℕ) :
    claimsListTotal ((ghostAt kap init X i b).claims.filter
        (fun cl => decide (cl.lo ≤ accessN X i) && decide (accessN X i ≤ cl.hi)))
      ≤ metSum kap init X (i+1) b v := by
  have hbstI : IsBST (processTree init X i) := processTree_isBST init X hbst i
  have hqmem : accessN X i ∈ (processTree init X i).toKeyList := by
    rw [processTree_toKeyList, accessN_eq X i hi]
    exact hmem ⟨i, hi⟩
  obtain ⟨A, B, hsplay⟩ :=
    splay_root_of_mem (accessN X i) (processTree init X i) hbstI hqmem
  have hpt : processTree init X (i+1) = .node A (accessN X i) B := by
    rw [processTree_succ_eq init X i hi, hsplay]
  obtain ⟨rest, hrest⟩ := searchPath_node_head v (accessN X i) A B
  have hqP : accessN X i ∈ searchPath v (processTree init X (i+1)) := by
    rw [hpt, hrest]
    exact List.mem_cons_self
  have hqT : accessN X i ∈ touchedList init X (i+1) := by
    rw [touchedList_succ_eq init X i hi]
    exact List.mem_append_right _
      (self_mem_searchPath _ _ hbstI hqmem)
  show claimsListTotal _
      ≤ claimsListTotal ((ghostAt kap init X (i+1) b).claims.filter
          (claimMet (touchedList init X (i+1))
            (searchPath v (processTree init X (i+1)))))
  rw [ghostAt_claims_succ_opp kap init X i b h]
  unfold pruneClaims
  refine claimsListTotal_filter_le_map_filter _ _ _ _ _
    (fun cl => clipClaim_r _ _ cl) ?_
  intro cl hcl
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hcl
  obtain ⟨hlo, hhi⟩ := hcl
  have hlo' : (clipClaim (!(sideF X i)) (accessN X i) cl).lo ≤ accessN X i := by
    cases (!(sideF X i)) <;> simp [clipClaim] <;> omega
  have hhi' : accessN X i ≤ (clipClaim (!(sideF X i)) (accessN X i) cl).hi := by
    cases (!(sideF X i)) <;> simp [clipClaim] <;> omega
  constructor
  · unfold claimAlive
    cases (!(sideF X i)) <;> simp <;> omega
  · unfold claimMet
    rw [List.any_eq_true]
    refine ⟨accessN X i, hqP, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hqT, hlo'⟩, hhi'⟩

/-! ## THE OPPOSITE-SIDE STEP LEMMA (conditional assembly) -/

/-- **`hstepOpp`, the opposite-side reproduction hypothesis of
`hmaster_of_reproduction`, assembled from four named analytic kernels.**

Clause (C1) at `i+1` is proven unconditionally.  Clauses (C2)/(C3) are derived
from the invariant at `i` (via the `FirstOwnAfter`/`ConsecOwnAfter` transfer
lemmas) together with the kernels:

* `hC2tc`  : the step deepening bound `2·tc(i+1) ≤ 2·tc(i) + 4` for the first
  future side-`b` target — provable from the W6 (shared-prefix-touched) premise
  via `tcOf_succ_le_of_sharedTouched` above;
* `hC2met` : met-sum monotonicity across the prune for that target — partially
  provided by `metSum_succ_opp_ge_straddle` above (straddling claims);
* `hC3tc`  : the suffix analogue of `hC2tc` for consecutive future side-`b`
  pairs;
* `hC3met` : the suffix analogue of `hC2met`.

The kernels are NOT provable from `INV` alone: with `init` a 20-node left spine
`24 → 23 → ⋯ → 6 → 5` and `X = (5, 6, 6, …)`, the first access loads `v = 6`'s
path with ⌈m/2⌉ touched nodes while side `true`'s ghost holds no claims, so
(C2) at `i = 1` (which `hstepOpp` would output at `i = 0`) fails outright —
the invariant needs a fourth (shared-prefix/fresh-scaled) clause before the
kernels can be discharged. -/

theorem hstepOpp {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (hsize : init.num_nodes = n) (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (h213 : X avoids ![2, 1, 3]) (h231 : X avoids ![2, 3, 1])
    (hC2tc : ∀ i, i < n → INV 6 init X i → ∀ b, sideF X i ≠ b →
        ∀ j, FirstOwnAfter X (i+1) b j →
          2 * tcOf init X (accessN X j) (i+1)
            ≤ 2 * tcOf init X (accessN X j) i + 4)
    (hC2met : ∀ i, i < n → INV 6 init X i → ∀ b, sideF X i ≠ b →
        ∀ j, FirstOwnAfter X (i+1) b j →
          metSum 6 init X i b (accessN X j)
            ≤ metSum 6 init X (i+1) b (accessN X j))
    (hC3tc : ∀ i, i < n → INV 6 init X i → ∀ b, sideF X i ≠ b →
        ∀ j k, ConsecOwnAfter X (i+1) b j k →
          2 * tcSuffixOf init X (accessN X k) (accessN X j) (i+1)
            ≤ 2 * tcSuffixOf init X (accessN X k) (accessN X j) i + 4)
    (hC3met : ∀ i, i < n → INV 6 init X i → ∀ b, sideF X i ≠ b →
        ∀ j k, ConsecOwnAfter X (i+1) b j k →
          metSumOn 6 init X i b
              (divergeSuffix (accessN X k) (accessN X j) (processTree init X i))
            ≤ metSumOn 6 init X (i+1) b
              (divergeSuffix (accessN X k) (accessN X j)
                (processTree init X (i+1)))) :
    ∀ i, i < n → INV 6 init X i →
      ∀ b, sideF X i ≠ b → INVside 6 init X (i+1) b := by
  intro i hi hINV b hside
  obtain ⟨hC1, hC2, hC3⟩ := hINV b
  have hpool := ghostAt_pool_succ_opp 6 init X i b hside
  refine ⟨?_, ?_, ?_⟩
  · exact INVside_C1_succ_opp 6 init X i b hside hC1
  · intro j hj
    have hj' := firstOwnAfter_succ_opp X i b hside j hj
    have h2 := hC2 j hj'
    have htc := hC2tc i hi hINV b hside j hj
    have hmet := hC2met i hi hINV b hside j hj
    omega
  · intro j k hjk
    have hjk' := consecOwnAfter_succ_opp X i b j k hjk
    have h3 := hC3 j k hjk'
    have htc := hC3tc i hi hINV b hside j k hjk
    have hmet := hC3met i hi hINV b hside j k hjk
    omega

/-! ## FALSITY WITNESS: the kernel-free `hstepOpp` is FALSE

The four kernels are not removable: with `init` the 20-node left spine
`24 → 23 → ⋯ → 6 → 5` and `X = (5, 6, 6, …)` (which satisfies ALL the
process hypotheses), the access `X 0 = 5` touches the whole spine and the
splay then rebuilds `v = 6`'s search path out of 11 already-touched nodes,
while side `true`'s ghost state holds no claims and a pool of only `4`:
clause (C2) of `INVside 6 init X 1 true` demands `2·11 ≤ 0 + 4 + 14` — false.
Machine-checked below (`hstepOpp_kernelfree_false`). -/

/-- Left spine `(4+m) → ⋯ → 6 → 5` on `m` nodes. -/

def mkSpine : ℕ → BinaryTree
  | 0 => .empty
  | (m+1) => .node (mkSpine m) (5 + m) .empty

/-- The access sequence `5, 6, 6, …, 6` (a valid deque pattern). -/

def X20 : Fin 20 → ℕ := fun j => if (j : ℕ) = 0 then 5 else 6

theorem mkSpine_forall_lt :
    ∀ (m c : ℕ), 5 + m ≤ c → ForallTree (fun x => x < c) (mkSpine m)
  | 0, _, _ => ForallTree.left
  | (m+1), c, h =>
      ForallTree.node _ _ _ (mkSpine_forall_lt m c (by omega)) (by omega)
        ForallTree.left

theorem isBST_mkSpine (m : ℕ) : IsBST (mkSpine m) := by
  induction m with
  | zero => exact IsBST.left
  | succ m ih =>
      exact IsBST.node _ _ _ (mkSpine_forall_lt m (5+m) le_rfl) ForallTree.left
        ih IsBST.left

/-- Clause (C2) of the post-step invariant fails outright on the witness. -/

theorem INVside_X20_one_false : ¬ INVside 6 (mkSpine 20) X20 1 true := by
  intro hINV
  obtain ⟨_, hC2, _⟩ := hINV
  have h := hC2 1 ⟨le_rfl, by omega, by decide, fun k h1 h2 => by omega⟩
  revert h
  decide

theorem X20_avoids213 : X20 avoids ![2, 1, 3] := by
  rintro ⟨f, hmono, hiff⟩
  have h10 : X20 (f 1) < X20 (f 0) := (hiff 1 0).mp (by decide)
  have h1 : (f 0 : ℕ) < (f 1 : ℕ) := hmono (by decide : (0 : Fin 3) < 1)
  have h2 : X20 (f 1) = if (f 1 : ℕ) = 0 then 5 else 6 := rfl
  have h3 : X20 (f 0) = if (f 0 : ℕ) = 0 then 5 else 6 := rfl
  by_cases h : (f 1 : ℕ) = 0
  · omega
  · rw [if_neg h] at h2
    by_cases h' : (f 0 : ℕ) = 0
    · rw [if_pos h'] at h3
      omega
    · rw [if_neg h'] at h3
      omega

theorem X20_avoids231 : X20 avoids ![2, 3, 1] := by
  rintro ⟨f, hmono, hiff⟩
  have h20 : X20 (f 2) < X20 (f 0) := (hiff 2 0).mp (by decide)
  have h1 : (f 0 : ℕ) < (f 2 : ℕ) := hmono (by decide : (0 : Fin 3) < 2)
  have h2 : X20 (f 2) = if (f 2 : ℕ) = 0 then 5 else 6 := rfl
  have h3 : X20 (f 0) = if (f 0 : ℕ) = 0 then 5 else 6 := rfl
  by_cases h : (f 2 : ℕ) = 0
  · omega
  · rw [if_neg h] at h2
    by_cases h' : (f 0 : ℕ) = 0
    · rw [if_pos h'] at h3
      omega
    · rw [if_neg h'] at h3
      omega

/-- **The kernel-free opposite-side step lemma is FALSE.**  No proof of the
target can exist without strengthening `INV` (e.g. by a fourth shared-prefix
clause) or adding hypotheses like the four kernels of `hstepOpp`. -/

theorem hstepOpp_kernelfree_false :
    ¬ (∀ (n : ℕ) (init : BinaryTree) (X : Fin n → ℕ),
        init.num_nodes = n → IsBST init →
        (∀ i : Fin n, X i ∈ init.toKeyList) →
        (X avoids ![2, 1, 3]) → (X avoids ![2, 3, 1]) →
        ∀ i, i < n → INV 6 init X i →
          ∀ b, sideF X i ≠ b → INVside 6 init X (i+1) b) := by
  intro hstep
  exact INVside_X20_one_false
    (hstep 20 (mkSpine 20) X20 (by decide) (isBST_mkSpine 20) (by decide)
      X20_avoids213 X20_avoids231 0 (by omega) (INV_zero 6 _ _) true (by decide))

end Splay

#print axioms Splay.hstepOpp
#print axioms Splay.hstepOpp_kernelfree_false
#print axioms Splay.INVside_C1_succ_opp
#print axioms Splay.tcOf_succ_le_of_sharedTouched
#print axioms Splay.metSum_succ_opp_ge_straddle
