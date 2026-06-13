import Challenges.Splay_Tree.Def_Containment
import Challenges.Splay_Tree.Def_Ackermann
import Challenges.Splay_Tree.Def_Splay

/-!
# Conditional capstones for the splay-tree deque challenges

Assembles BOTH deque challenge statements — the `c · n · α(n)` form
(`Challenge_Splay_Deque`) and the Deque-Conjecture `c · n` form
(`Challenge_Splay_DequeConjecture`) — from the proven ledger summation lemma
(`ledger_sum_bound`) plus the development-file assets (process bridge, cost bridge,
fresh telescope).  The MASTER per-access inequality is the sole hypothesis.

Structure: a private shared core (`sequence_cost_linear_of_ledger_master`) gives the
pure-linear bound `sequence_cost ≤ ((6·κ + 8) · n : ℕ)` cast to `ℝ`; the two capstones
(`deque_of_ledger_master`, `deque_conjecture_of_ledger_master`, existential constant
over `ℕ`) are thin wrappers, and two adapters
(`deque_challenge_of_ledger_master`, `deque_conjecture_challenge_of_ledger_master`)
match the shipped challenge sorry-types verbatim (existential constant over `ℝ`,
named `h_size` binder).
-/

set_option maxHeartbeats 2000000

namespace Splay

/-! ### Basic counting -/

private theorem toKeyList_length (t : BinaryTree) :
    t.toKeyList.length = t.num_nodes := by
  induction t with
  | empty =>
      simp [BinaryTree.toKeyList, BinaryTree.num_nodes]
  | node l k r ihl ihr =>
      simp [BinaryTree.toKeyList, BinaryTree.num_nodes, ihl, ihr]
      omega

/-! ### Cost bridge: `splay.cost = search_path_len - 1` (over ℝ) -/

theorem cast_pred_add_two_of_pos (m : Nat) (hm : 0 < m) :
    (((m - 1 : Nat) : ℝ) + 2) = 1 + (m : ℝ) := by
  have hnat : (m - 1) + 2 = 1 + m := by omega
  exact_mod_cast hnat

theorem node_search_path_len_pos (l : BinaryTree) (k : Nat)
    (r : BinaryTree) (q : Nat) :
    0 < (BinaryTree.node l k r).search_path_len q := by
  simp only [BinaryTree.search_path_len]
  by_cases hqk : q < k
  · simp [hqk]
  · by_cases hkq : k < q
    · simp [hqk, hkq]
    · simp [hqk, hkq]

theorem splay_cost_eq_search_path_len_sub_one :
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

/-! ### Splay preserves the key list -/

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

/-! ### The process-sum bridge -/

/-- Totalized fold step over `ℕ` indices, agreeing with the `sequence_cost` fold
step on indices `< n` and acting as the identity otherwise. -/
private def stepNat {n : ℕ} (X : Fin n → ℕ) (acc : BinaryTree × ℝ) (j : ℕ) :
    BinaryTree × ℝ :=
  if h : j < n then
    (splay acc.1 (X ⟨j, h⟩), acc.2 + splay.cost acc.1 (X ⟨j, h⟩))
  else acc

private theorem foldl_stepNat_range {n : ℕ} (init : BinaryTree)
    (X : Fin n → ℕ) :
    ∀ m : ℕ,
      (List.range m).foldl (stepNat X) (init, (0 : ℝ)) =
        (processTree init X m,
          ∑ j ∈ Finset.range m,
            if h : j < n then
              splay.cost (processTree init X j) (X ⟨j, h⟩)
            else 0)
  | 0 => by simp
  | (m + 1) => by
      rw [List.range_succ, List.foldl_append, foldl_stepNat_range init X m,
        Finset.sum_range_succ]
      by_cases h : m < n
      · simp [stepNat, h, processTree_succ_dite]
      · simp [stepNat, h, processTree_succ_dite]

private theorem foldl_stepNat_range_snd {n : ℕ} (init : BinaryTree)
    (X : Fin n → ℕ) (m : ℕ) :
    ((List.range m).foldl (stepNat X) (init, (0 : ℝ))).2 =
      ∑ j ∈ Finset.range m,
        if h : j < n then
          splay.cost (processTree init X j) (X ⟨j, h⟩)
        else 0 := by
  rw [foldl_stepNat_range init X m]

/-- **Process-sum bridge.**  The total cost of splaying the access sequence `X`
starting from `init` is the sum, over all accesses, of the cost of splaying the
current process tree at the accessed key. -/
theorem sequence_cost_eq_process_sum {n : ℕ} (init : BinaryTree)
    (X : Fin n → ℕ) :
    splay.sequence_cost init X =
      ∑ i : Fin n, splay.cost (processTree init X i) (X i) := by
  have hfold :
      splay.sequence_cost init X =
        ((List.range n).foldl (stepNat X) (init, (0 : ℝ))).2 := by
    unfold splay.sequence_cost
    rw [← List.map_coe_finRange_eq_range, List.foldl_map]
    congr 1
    refine List.foldl_ext _ _ _ ?_
    intro acc i _
    obtain ⟨t, c⟩ := acc
    simp [stepNat, i.isLt]
  rw [hfold, foldl_stepNat_range_snd init X n,
    ← Fin.sum_univ_eq_sum_range
      (fun j =>
        if h : j < n then
          splay.cost (processTree init X j) (X ⟨j, h⟩)
        else 0) n]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [i.isLt]

/-! ### The fresh telescope -/

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

/-- The telescoping identity: the sum of fresh counts up to `m ≤ n` is exactly the size of
the `m`-th touched set. -/
theorem touchedUpTo_card_eq {n : ℕ} (t : ℕ → BinaryTree) (X : Fin n → ℕ) :
    ∀ m : ℕ, m ≤ n →
      (∑ i ∈ Finset.range m,
        if h : i < n then
          ((searchPath (X ⟨i, h⟩) (t i)).toFinset \ touchedUpTo t X i).card
        else 0)
      = (touchedUpTo t X m).card := by
  intro m
  induction m with
  | zero =>
    intro _
    simp [touchedUpTo]
  | succ i ih =>
    intro hm
    have hi : i < n := hm
    rw [Finset.sum_range_succ, ih (Nat.le_of_succ_le hm), dif_pos hi]
    have hunf : touchedUpTo t X (i + 1)
        = touchedUpTo t X i ∪ (searchPath (X ⟨i, hi⟩) (t i)).toFinset := by
      simp only [touchedUpTo, dif_pos hi]
    rw [hunf, Finset.union_comm, ← Finset.card_sdiff_add_card]
    omega

theorem fresh_sum_le {n : ℕ} (t : ℕ → BinaryTree) (X : Fin n → ℕ)
    (hkeys : ∀ i : Fin n, ∀ y ∈ searchPath (X i) (t i), y ∈ (t 0).toKeyList) :
    ∑ i : Fin n, ((searchPath (X i) (t i)).toFinset \ touchedUpTo t X i).card
      ≤ (t 0).toKeyList.length := by
  have hsum :
      (∑ i : Fin n, ((searchPath (X i) (t i)).toFinset \ touchedUpTo t X i).card)
        = ∑ i ∈ Finset.range n,
            (if h : i < n then
              ((searchPath (X ⟨i, h⟩) (t i)).toFinset \ touchedUpTo t X i).card
             else 0) := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dif_pos i.isLt]
  rw [hsum, touchedUpTo_card_eq t X n (Nat.le_refl n)]
  calc (touchedUpTo t X n).card
      ≤ (t 0).toKeyList.toFinset.card :=
        Finset.card_le_card (touchedUpTo_subset_keys t X hkeys n)
    _ ≤ (t 0).toKeyList.length := List.toFinset_card_le _

/-! ### The ledger summation lemma (proven; pasted verbatim) -/

/-- Doubled draw, capped at the ledger (so the ledger never underflows).
`2 * c - min (2 * c) (2 * kap * (1 + f))` is the doubled excess `2*c ∸ 2*kap*(1+f)`. -/
def draw (kap : ℕ) (c f D : ℕ) : ℕ := min D (2 * c - min (2 * c) (2 * kap * (1 + f)))

/-- The per-side doubled ledger. On an own-side access the ledger repays `c i`
after drawing; the other side gains `4`. -/
def ledger (kap : ℕ) (c f : ℕ → ℕ) (s : ℕ → Bool) : ℕ → Bool → ℕ
  | 0, _ => 0
  | (i+1), side =>
      let D := ledger kap c f s i side
      if s i = side then D - draw kap (c i) (f i) D + c i
      else D + 4

/-- The ledger summation theorem: under the master hypothesis, the total cost is
linearly bounded by `n` and the total fresh budget.  (The induction actually gives
the sharper constant `(2*kap + 4) * n`; we state the requested `(4*kap + 8) * n`.) -/
theorem ledger_sum_bound (n kap : ℕ) (c f : ℕ → ℕ) (s : ℕ → Bool)
    (hmaster : ∀ i, i < n → 2 * c i ≤ ledger kap c f s i (s i) + 2 * kap * (1 + f i)) :
    ∑ i ∈ Finset.range n, c i ≤ (4 * kap + 8) * n + 2 * kap * (∑ i ∈ Finset.range n, f i) := by
  -- Invariant: prefix cost plus both ledgers is linear in the prefix length and budget.
  have key : ∀ j, j ≤ n →
      (∑ i ∈ Finset.range j, c i) + (ledger kap c f s j true + ledger kap c f s j false)
        ≤ (2 * kap + 4) * j + 2 * kap * (∑ i ∈ Finset.range j, f i) := by
    intro j
    induction j with
    | zero => intro _; simp [ledger]
    | succ j ih =>
      intro hj
      have ihj := ih (Nat.le_of_succ_le hj)
      have hm := hmaster j (Nat.lt_of_succ_le hj)
      -- Per-step bound: the new cost plus the ledger increase is at most `4 + 2*kap*(1+f j)`.
      have hstep : c j + (ledger kap c f s (j+1) true + ledger kap c f s (j+1) false)
          ≤ (ledger kap c f s j true + ledger kap c f s j false)
            + (4 + 2 * kap * (1 + f j)) := by
        cases hsj : s j with
        | false =>
          have h1 : ledger kap c f s (j+1) true = ledger kap c f s j true + 4 := by
            simp [ledger, hsj]
          have h2 : ledger kap c f s (j+1) false
              = ledger kap c f s j false
                - draw kap (c j) (f j) (ledger kap c f s j false) + c j := by
            simp [ledger, hsj]
          rw [hsj] at hm
          rw [h1, h2]
          unfold draw
          set A := 2 * kap * (1 + f j)
          omega
        | true =>
          have h1 : ledger kap c f s (j+1) true
              = ledger kap c f s j true
                - draw kap (c j) (f j) (ledger kap c f s j true) + c j := by
            simp [ledger, hsj]
          have h2 : ledger kap c f s (j+1) false = ledger kap c f s j false + 4 := by
            simp [ledger, hsj]
          rw [hsj] at hm
          rw [h1, h2]
          unfold draw
          set A := 2 * kap * (1 + f j)
          omega
      calc (∑ i ∈ Finset.range (j+1), c i)
            + (ledger kap c f s (j+1) true + ledger kap c f s (j+1) false)
          = (∑ i ∈ Finset.range j, c i)
              + (c j + (ledger kap c f s (j+1) true + ledger kap c f s (j+1) false)) := by
            rw [Finset.sum_range_succ]; ring
        _ ≤ (∑ i ∈ Finset.range j, c i)
              + ((ledger kap c f s j true + ledger kap c f s j false)
                + (4 + 2 * kap * (1 + f j))) := Nat.add_le_add_left hstep _
        _ = ((∑ i ∈ Finset.range j, c i)
              + (ledger kap c f s j true + ledger kap c f s j false))
              + (4 + 2 * kap * (1 + f j)) := by ring
        _ ≤ ((2 * kap + 4) * j + 2 * kap * (∑ i ∈ Finset.range j, f i))
              + (4 + 2 * kap * (1 + f j)) := Nat.add_le_add_right ihj _
        _ = (2 * kap + 4) * (j+1) + 2 * kap * ((∑ i ∈ Finset.range j, f i) + f j) := by ring
        _ = (2 * kap + 4) * (j+1) + 2 * kap * (∑ i ∈ Finset.range (j+1), f i) := by
            rw [Finset.sum_range_succ]
  calc ∑ i ∈ Finset.range n, c i
      ≤ (∑ i ∈ Finset.range n, c i)
        + (ledger kap c f s n true + ledger kap c f s n false) := Nat.le_add_right _ _
    _ ≤ (2 * kap + 4) * n + 2 * kap * (∑ i ∈ Finset.range n, f i) := key n le_rfl
    _ ≤ (4 * kap + 8) * n + 2 * kap * (∑ i ∈ Finset.range n, f i) :=
        Nat.add_le_add_right (Nat.mul_le_mul (by omega) le_rfl) _

/-! ### Klazar's inverse Ackermann is at least 1 on positive inputs -/

private theorem one_le_alpha_of_pos {n : Nat} (hn : 0 < n) : 1 ≤ KlazarAckermann.alpha n := by
  rw [Nat.one_le_iff_ne_zero]
  intro hzero
  have hP : KlazarAckermann.P_omega n 0 := by
    unfold KlazarAckermann.alpha at hzero
    exact (Nat.find_eq_zero _).mp hzero
  simp [KlazarAckermann.P_omega, KlazarAckermann.F_omega, KlazarAckermann.F] at hP
  omega

/-! ### Concrete instantiation for the deque process -/

/-- Side selector for the access at position `i`: `true` iff the future of the
sequence is bounded above by `X i` (the future-max side; on deque sequences,
`deque_future_one_sided` shows the complement is the future-min side).
Out of range the value is irrelevant; we pick `true`. -/
def sideF {n : ℕ} (X : Fin n → ℕ) (i : ℕ) : Bool :=
  if h : i < n then
    decide (∀ j : Fin n, (⟨i, h⟩ : Fin n) < j → X j ≤ X ⟨i, h⟩)
  else true

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

/-! ### The shared linear core -/

/-- **Shared core for both capstones.**  Under the MASTER per-access inequality, the
total splay cost of any `{213, 231}`-avoiding access sequence on an `n`-node BST is at
most `(6·κ + 8) · n` (as a cast of the ℕ-level bound).  Both the `c · n · α(n)` deque
capstone and the `c · n` Deque-Conjecture capstone are thin wrappers around this lemma. -/
private theorem sequence_cost_linear_of_ledger_master (kap : ℕ)
    (hmaster : ∀ (n : ℕ) (X : Fin n → ℕ) (init : BinaryTree),
        init.num_nodes = n → IsBST init → (∀ i : Fin n, X i ∈ init.toKeyList) →
        (X avoids ![2, 1, 3]) → (X avoids ![2, 3, 1]) →
        ∀ i : Fin n, 2 * costN init X i ≤
          ledger kap (costN init X) (freshN init X) (sideF X) i (sideF X i)
            + 2 * kap * (1 + freshN init X i))
    (n : ℕ) (X : Fin n → ℕ)
    (h213 : X avoids ![2, 1, 3]) (h231 : X avoids ![2, 3, 1])
    (init : BinaryTree) (h_size : init.num_nodes = n) (hbst : IsBST init)
    (hmem : ∀ i : Fin n, (X i) ∈ init.toKeyList) :
    splay.sequence_cost init X ≤ (((6 * kap + 8) * n : ℕ) : ℝ) := by
  -- Cost bridge: the real-valued sequence cost is the cast of the ℕ-level cost sum.
  have hcost_eq : ∀ i : Fin n,
      splay.cost (processTree init X i) (X i) = ((costN init X i : ℕ) : ℝ) := by
    intro i
    rw [splay_cost_eq_search_path_len_sub_one]
    have hc : costN init X (i : ℕ)
        = (processTree init X i).search_path_len (X i) - 1 := by
      unfold costN
      rw [dif_pos i.isLt]
    rw [hc]
  have hbridge : splay.sequence_cost init X
      = ((∑ i ∈ Finset.range n, costN init X i : ℕ) : ℝ) := by
    rw [sequence_cost_eq_process_sum,
      ← Fin.sum_univ_eq_sum_range (costN init X) n, Nat.cast_sum]
    exact Finset.sum_congr rfl fun i _ => hcost_eq i
  -- The ledger summation under the master hypothesis.
  have hM := hmaster n X init h_size hbst hmem h213 h231
  have hsum := ledger_sum_bound n kap (costN init X) (freshN init X) (sideF X)
    (fun i hi => hM ⟨i, hi⟩)
  -- The total fresh budget is at most `n`.
  have hkeys : ∀ i : Fin n, ∀ y ∈ searchPath (X i) (processTree init X i),
      y ∈ (processTree init X 0).toKeyList := by
    intro i y hy
    have h1 := searchPath_subset_toKeyList (X i) (processTree init X i) y hy
    rwa [processTree_toKeyList] at h1
  have hfreshsum : ∑ i ∈ Finset.range n, freshN init X i ≤ n := by
    have heq : ∑ i ∈ Finset.range n, freshN init X i
        = ∑ i : Fin n, ((searchPath (X i) (processTree init X i)).toFinset
            \ touchedUpTo (processTree init X) X i).card := by
      rw [← Fin.sum_univ_eq_sum_range (freshN init X) n]
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold freshN
      rw [dif_pos i.isLt]
    have hle := fresh_sum_le (processTree init X) X hkeys
    rw [processTree_zero, toKeyList_length, h_size] at hle
    rw [heq]
    exact hle
  -- Assemble the ℕ-level linear bound.
  have htotal : ∑ i ∈ Finset.range n, costN init X i ≤ (6 * kap + 8) * n := by
    have h2 : 2 * kap * (∑ i ∈ Finset.range n, freshN init X i) ≤ 2 * kap * n :=
      Nat.mul_le_mul (Nat.le_refl (2 * kap)) hfreshsum
    calc ∑ i ∈ Finset.range n, costN init X i
        ≤ (4 * kap + 8) * n
            + 2 * kap * (∑ i ∈ Finset.range n, freshN init X i) := hsum
      _ ≤ (4 * kap + 8) * n + 2 * kap * n := Nat.add_le_add_left h2 _
      _ = (6 * kap + 8) * n := by ring
  rw [hbridge]
  exact_mod_cast htotal

/-! ### The conditional capstones -/

/-- **Conditional capstone for the deque challenge.**  Assume the MASTER per-access
inequality: on every deque-like instance, twice the access cost is covered by the
current own-side ledger plus the `κ`-scaled fresh budget.  Then the total splay cost
of any `{213, 231}`-avoiding access sequence is at most `c · n · α(n)` (indeed `c · n`)
with the explicit constant `c = 6·κ + 8`. -/
theorem deque_of_ledger_master (kap : ℕ)
    (hmaster : ∀ (n : ℕ) (X : Fin n → ℕ) (init : BinaryTree),
        init.num_nodes = n → IsBST init → (∀ i : Fin n, X i ∈ init.toKeyList) →
        (X avoids ![2, 1, 3]) → (X avoids ![2, 3, 1]) →
        ∀ i : Fin n, 2 * costN init X i ≤
          ledger kap (costN init X) (freshN init X) (sideF X) i (sideF X i)
            + 2 * kap * (1 + freshN init X i)) :
    ∃ c : ℕ, ∀ n, ∀ X : Fin n → ℕ,
      (X avoids ![2, 1, 3]) → (X avoids ![2, 3, 1]) →
      ∀ (init : BinaryTree), init.num_nodes = n → IsBST init →
      (∀ i : Fin n, (X i) ∈ init.toKeyList) →
      splay.sequence_cost init X ≤ c * n * (KlazarAckermann.alpha n) := by
  refine ⟨6 * kap + 8, ?_⟩
  intro n X h213 h231 init h_size hbst hmem
  have hcore := sequence_cost_linear_of_ledger_master kap hmaster n X
    h213 h231 init h_size hbst hmem
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simpa using hcore
  · have halpha : 1 ≤ KlazarAckermann.alpha n := one_le_alpha_of_pos hn
    have hfinal : ((6 * kap + 8) * n : ℕ)
        ≤ (6 * kap + 8) * n * KlazarAckermann.alpha n := by
      calc (6 * kap + 8) * n = (6 * kap + 8) * n * 1 := by ring
        _ ≤ (6 * kap + 8) * n * KlazarAckermann.alpha n :=
            Nat.mul_le_mul (Nat.le_refl ((6 * kap + 8) * n)) halpha
    calc splay.sequence_cost init X
        ≤ (((6 * kap + 8) * n : ℕ) : ℝ) := hcore
      _ ≤ _ := by exact_mod_cast hfinal

/-- **Conditional capstone for the Deque Conjecture challenge.**  Same MASTER
hypothesis, same chain, minus the `α` step: the internal bound is already linear,
so the total splay cost is at most `c · n` with `c = 6·κ + 8`. -/
theorem deque_conjecture_of_ledger_master (kap : ℕ)
    (hmaster : ∀ (n : ℕ) (X : Fin n → ℕ) (init : BinaryTree),
        init.num_nodes = n → IsBST init → (∀ i : Fin n, X i ∈ init.toKeyList) →
        (X avoids ![2, 1, 3]) → (X avoids ![2, 3, 1]) →
        ∀ i : Fin n, 2 * costN init X i ≤
          ledger kap (costN init X) (freshN init X) (sideF X) i (sideF X i)
            + 2 * kap * (1 + freshN init X i)) :
    ∃ c : ℕ, ∀ n, ∀ X : Fin n → ℕ,
      (X avoids ![2, 1, 3]) → (X avoids ![2, 3, 1]) →
      ∀ (init : BinaryTree), init.num_nodes = n → IsBST init →
      (∀ i : Fin n, (X i) ∈ init.toKeyList) →
      splay.sequence_cost init X ≤ c * n := by
  refine ⟨6 * kap + 8, ?_⟩
  intro n X h213 h231 init h_size hbst hmem
  have hcore := sequence_cost_linear_of_ledger_master kap hmaster n X
    h213 h231 init h_size hbst hmem
  exact_mod_cast hcore

/-! ### Adapters matching the shipped challenge statements verbatim

The shipped statements (`Challenge_Splay_Deque.lean`, `Challenge_Splay_DequeConjecture.lean`)
use a bare `∃ c` — which elaborates over `ℝ` since `splay.sequence_cost` is real-valued —
and a named `(h_size : init.num_nodes = n)` binder.  The only glue is the `ℕ → ℝ` cast of
the existential constant. -/

/-- Adapter with the exact type of `Challenge_Splay_Deque.lean`'s `theorem deque`. -/
theorem deque_challenge_of_ledger_master (kap : ℕ)
    (hmaster : ∀ (n : ℕ) (X : Fin n → ℕ) (init : BinaryTree),
        init.num_nodes = n → IsBST init → (∀ i : Fin n, X i ∈ init.toKeyList) →
        (X avoids ![2, 1, 3]) → (X avoids ![2, 3, 1]) →
        ∀ i : Fin n, 2 * costN init X i ≤
          ledger kap (costN init X) (freshN init X) (sideF X) i (sideF X i)
            + 2 * kap * (1 + freshN init X i)) :
    ∃ c, ∀ n, ∀ X : Fin n → ℕ,
    (X avoids ![2, 1, 3]) → (X avoids ![2, 3, 1]) →
    ∀ (init : BinaryTree), (h_size : init.num_nodes = n) → IsBST init →
    (∀ i : Fin n, (X i) ∈ init.toKeyList) →
    splay.sequence_cost init X ≤ c * n * (KlazarAckermann.alpha n) := by
  obtain ⟨c, hc⟩ := deque_of_ledger_master kap hmaster
  refine ⟨(c : ℝ), ?_⟩
  intro n X h213 h231 init h_size hbst hmem
  have hcn := hc n X h213 h231 init h_size hbst hmem
  exact_mod_cast hcn

/-- Adapter with the exact type of `Challenge_Splay_DequeConjecture.lean`'s
`theorem deque_conjecture`. -/
theorem deque_conjecture_challenge_of_ledger_master (kap : ℕ)
    (hmaster : ∀ (n : ℕ) (X : Fin n → ℕ) (init : BinaryTree),
        init.num_nodes = n → IsBST init → (∀ i : Fin n, X i ∈ init.toKeyList) →
        (X avoids ![2, 1, 3]) → (X avoids ![2, 3, 1]) →
        ∀ i : Fin n, 2 * costN init X i ≤
          ledger kap (costN init X) (freshN init X) (sideF X) i (sideF X i)
            + 2 * kap * (1 + freshN init X i)) :
    ∃ c, ∀ n, ∀ X : Fin n → ℕ,
    (X avoids ![2, 1, 3]) → (X avoids ![2, 3, 1]) →
    ∀ (init : BinaryTree), (h_size : init.num_nodes = n) → IsBST init →
    (∀ i : Fin n, (X i) ∈ init.toKeyList) →
    splay.sequence_cost init X ≤ c * n := by
  obtain ⟨c, hc⟩ := deque_conjecture_of_ledger_master kap hmaster
  refine ⟨(c : ℝ), ?_⟩
  intro n X h213 h231 init h_size hbst hmem
  have hcn := hc n X h213 h231 init h_size hbst hmem
  exact_mod_cast hcn

end Splay

#print axioms Splay.ledger_sum_bound
#print axioms Splay.deque_of_ledger_master
#print axioms Splay.deque_conjecture_of_ledger_master
#print axioms Splay.deque_challenge_of_ledger_master
#print axioms Splay.deque_conjecture_challenge_of_ledger_master
