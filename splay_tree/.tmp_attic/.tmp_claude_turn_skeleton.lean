/-
TURN-DECOMPOSITION SKELETON for the deque challenges (2026-06-12).

Replaces the falsified ZB conditional closure with a closure along the
Sundar-shaped route.  The splay cost on a `{213,231}`-avoiding sequence is
factored through the TURN structure of the access paths:

  * `turnsN`        — number of direction changes on the `i`-th access path;
  * `totalTurnsN`   — their process sum;
  * `TurnCostBridge`    (named core B): total cost ≤ c₂ · (n + total turns)
        [empirical: ratio ≤ 2.92, FLAT for n = 256 … 8192, adversarial battery
         incl. zigzag inits and frontier-jump patterns];
  * `TurnSumBoundAlpha` (named core T): total turns ≤ c₁ · n · α(n)
        [empirical: total turns ≤ 2.00 · n, FLAT — the α-form is the
         Sundar-grade statement, the linear form `TurnSumBoundLinear` is the
         stronger empirical truth];
  * capstones: the EXACT shipped statements of `Challenge_Splay_Deque.lean`
    (from B + T) and `Challenge_Splay_DequeConjecture.lean` (from B + linear T).

Compiles on the precompiled `Challenges.ZBK` base (the zb-closing arsenal).
-/
import Challenges.ZBK

namespace Splay
namespace Splay
namespace Splay
namespace Splay
namespace Splay
namespace Splay

/-! ## §1 Turn-structure definitions -/

/-- Direction taken at each non-terminal node of the `i`-th access path:
`true` = the target is smaller (descend left). -/
def pathDirsN {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ) (i : ℕ) : List Bool :=
  (pathN init X i).dropLast.map (fun k => decide (accessN X i < k))

/-- Number of adjacent direction changes in a direction list. -/
def turnCount : List Bool → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => (if a = b then 0 else 1) + turnCount (b :: rest)

/-- Turns of the `i`-th access path. -/
def turnsN {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ) (i : ℕ) : ℕ :=
  turnCount (pathDirsN init X i)

/-- Total turns over the whole access sequence. -/
def totalTurnsN {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, turnsN init X i

@[simp] theorem turnCount_nil : turnCount [] = 0 := rfl

@[simp] theorem turnCount_singleton (a : Bool) : turnCount [a] = 0 := rfl

theorem turnCount_cons_cons (a b : Bool) (rest : List Bool) :
    turnCount (a :: b :: rest)
      = (if a = b then 0 else 1) + turnCount (b :: rest) := rfl

/-- A turn-free (constant) direction list has zero turns. -/
theorem turnCount_replicate (m : ℕ) (a : Bool) :
    turnCount (List.replicate m a) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
      cases m with
      | zero => rfl
      | succ m' =>
          rw [List.replicate_succ, List.replicate_succ, turnCount_cons_cons,
            ← List.replicate_succ, if_pos rfl, ih, Nat.zero_add]

/-- Turns are bounded by the (edge) length of the direction list. -/
theorem turnCount_le_length (l : List Bool) : turnCount l ≤ l.length := by
  induction l with
  | nil => simp
  | cons a rest ih =>
      cases rest with
      | nil => simp
      | cons b rest' =>
          rw [turnCount_cons_cons]
          have h1 : turnCount (b :: rest') ≤ (b :: rest').length := ih
          by_cases hab : a = b
          · rw [if_pos hab]
            simp only [List.length_cons] at h1 ⊢
            omega
          · rw [if_neg hab]
            simp only [List.length_cons] at h1 ⊢
            omega

/-! ## §2 The named cores

Both cores are stated over EXACTLY the challenge-class hypotheses.  Empirical
status (faithful repo splay, adversarial battery — runs/rand/coll/jump families ×
spine/zigzag/V/W/random-BST inits, n = 256 … 8192, `/tmp/turns_pin.py`,
`/tmp/turns_stress.py`):

  * total turns / n ≤ 2.00, flat in n  (per-path turns are NOT uniformly bounded —
    a zigzag init gives the first access ~n/2 turns — but the sum amortizes);
  * total cost / (n + total turns) ≤ 2.92, flat in n.

`TurnCostBridge ∧ TurnSumBoundLinear` jointly imply the open Deque Conjecture, so
at least one of them is conjecture-hard; `TurnSumBoundAlpha` is the Sundar-grade
weakening sufficient for the 50-pt challenge. -/

/-- **Core T (α-form)**: the total number of turns is `O(n · α(n))` on the
deque class.  (Sundar-grade; empirically the stronger linear form holds.) -/
def TurnSumBoundAlpha : Prop :=
  ∃ c₁ : ℕ, ∀ (n : ℕ) (X : Fin n → ℕ) (init : BinaryTree),
    init.num_nodes = n → IsBST init → (∀ i : Fin n, X i ∈ init.toKeyList) →
    (X avoids ![2, 1, 3]) → (X avoids ![2, 3, 1]) →
    totalTurnsN init X ≤ c₁ * n * KlazarAckermann.alpha n

/-- **Core T (linear form)**: the total number of turns is `O(n)` on the deque
class.  (Empirically `≤ 2n`, flat through `n = 8192`.) -/
def TurnSumBoundLinear : Prop :=
  ∃ c₁ : ℕ, ∀ (n : ℕ) (X : Fin n → ℕ) (init : BinaryTree),
    init.num_nodes = n → IsBST init → (∀ i : Fin n, X i ∈ init.toKeyList) →
    (X avoids ![2, 1, 3]) → (X avoids ![2, 3, 1]) →
    totalTurnsN init X ≤ c₁ * n

/-- **Core B (the bridge)**: the total splay cost is `O(n + total turns)` on the
deque class.  (Empirically the ratio is ≤ 2.92, flat through `n = 8192`.) -/
def TurnCostBridge : Prop :=
  ∃ c₂ : ℕ, ∀ (n : ℕ) (X : Fin n → ℕ) (init : BinaryTree),
    init.num_nodes = n → IsBST init → (∀ i : Fin n, X i ∈ init.toKeyList) →
    (X avoids ![2, 1, 3]) → (X avoids ![2, 3, 1]) →
    (∑ i ∈ Finset.range n, costN init X i) ≤ c₂ * (n + totalTurnsN init X)

/-- The α-form of core T follows from the linear form (`α ≥ 1` on positive `n`;
the `n = 0` case is trivial since the turn sum is empty). -/
theorem turnSumBoundAlpha_of_linear (h : TurnSumBoundLinear) : TurnSumBoundAlpha := by
  obtain ⟨c₁, h⟩ := h
  refine ⟨c₁, ?_⟩
  intro n X init hsize hbst hmem h213 h231
  have hlin := h n X init hsize hbst hmem h213 h231
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h0 : totalTurnsN init X = 0 := by
      unfold totalTurnsN
      simp
    rw [h0]
    exact Nat.zero_le _
  · have halpha : 1 ≤ KlazarAckermann.alpha n := by
      rw [Nat.one_le_iff_ne_zero]
      intro hzero
      have hP : KlazarAckermann.P_omega n 0 := by
        unfold KlazarAckermann.alpha at hzero
        exact (Nat.find_eq_zero _).mp hzero
      simp [KlazarAckermann.P_omega, KlazarAckermann.F_omega, KlazarAckermann.F] at hP
      omega
    calc totalTurnsN init X ≤ c₁ * n := hlin
      _ = c₁ * n * 1 := by ring
      _ ≤ c₁ * n * KlazarAckermann.alpha n :=
          Nat.mul_le_mul (Nat.le_refl (c₁ * n)) halpha

/-! ## §3 The shared cost-cast core -/

/-- ℕ-level total-cost bound from the two cores (α-form). -/
private theorem costSum_le_of_turn_cores {c₁ c₂ : ℕ}
    (n : ℕ) (X : Fin n → ℕ) (init : BinaryTree)
    (hT : totalTurnsN init X ≤ c₁ * n * KlazarAckermann.alpha n)
    (hB : (∑ i ∈ Finset.range n, costN init X i) ≤ c₂ * (n + totalTurnsN init X))
    (hn : 0 < n) :
    (∑ i ∈ Finset.range n, costN init X i)
      ≤ c₂ * (1 + c₁) * n * KlazarAckermann.alpha n := by
  have halpha : 1 ≤ KlazarAckermann.alpha n := by
    rw [Nat.one_le_iff_ne_zero]
    intro hzero
    have hP : KlazarAckermann.P_omega n 0 := by
      unfold KlazarAckermann.alpha at hzero
      exact (Nat.find_eq_zero _).mp hzero
    simp [KlazarAckermann.P_omega, KlazarAckermann.F_omega, KlazarAckermann.F] at hP
    omega
  have hn_le : n ≤ n * KlazarAckermann.alpha n := by
    calc n = n * 1 := by ring
      _ ≤ n * KlazarAckermann.alpha n :=
          Nat.mul_le_mul (Nat.le_refl n) halpha
  calc (∑ i ∈ Finset.range n, costN init X i)
      ≤ c₂ * (n + totalTurnsN init X) := hB
    _ ≤ c₂ * (n * KlazarAckermann.alpha n + c₁ * n * KlazarAckermann.alpha n) := by
        refine Nat.mul_le_mul (Nat.le_refl c₂) ?_
        exact Nat.add_le_add hn_le hT
    _ = c₂ * (1 + c₁) * n * KlazarAckermann.alpha n := by ring

/-- The real-valued sequence cost is the cast of the ℕ-level cost sum
(verbatim plumbing of the ledger capstones). -/
private theorem sequence_cost_eq_costSum_cast (n : ℕ) (X : Fin n → ℕ)
    (init : BinaryTree) :
    splay.sequence_cost init X
      = ((∑ i ∈ Finset.range n, costN init X i : ℕ) : ℝ) := by
  have hcost_eq : ∀ i : Fin n,
      splay.cost (processTree init X i) (X i) = ((costN init X i : ℕ) : ℝ) := by
    intro i
    rw [splay_cost_eq_search_path_len_sub_one]
    have hc : costN init X (i : ℕ)
        = (processTree init X i).search_path_len (X i) - 1 := by
      unfold costN
      rw [dif_pos i.isLt]
    rw [hc]
  rw [sequence_cost_eq_process_sum,
    ← Fin.sum_univ_eq_sum_range (costN init X) n, Nat.cast_sum]
  exact Finset.sum_congr rfl fun i _ => hcost_eq i

/-! ## §4 The capstones (exact shipped statements) -/

/-- **DEQUE CHALLENGE (50 pt) from the two turn cores**: the exact statement of
`Challenge_Splay_Deque.lean`'s `theorem deque`, with `c = c₂ · (1 + c₁)`. -/
theorem deque_challenge_CLOSED_of_turn_cores
    (hB : TurnCostBridge) (hT : TurnSumBoundAlpha) :
    ∃ c, ∀ n, ∀ X : Fin n → ℕ,
    (X avoids ![2, 1, 3]) → (X avoids ![2, 3, 1]) →
    ∀ (init : BinaryTree), (h_size : init.num_nodes = n) → IsBST init →
    (∀ i : Fin n, (X i) ∈ init.toKeyList) →
    splay.sequence_cost init X ≤ c * n * (KlazarAckermann.alpha n) := by
  obtain ⟨c₂, hB⟩ := hB
  obtain ⟨c₁, hT⟩ := hT
  refine ⟨((c₂ * (1 + c₁) : ℕ) : ℝ), ?_⟩
  intro n X h213 h231 init h_size hbst hmem
  have hcast := sequence_cost_eq_costSum_cast n X init
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [hcast]
    simp
  · have hTb := hT n X init h_size hbst hmem h213 h231
    have hBb := hB n X init h_size hbst hmem h213 h231
    have htotal := costSum_le_of_turn_cores n X init hTb hBb hn
    rw [hcast]
    exact_mod_cast htotal

/-- **DEQUE CONJECTURE (100 pt) from the bridge + the LINEAR turn core**: the
exact statement of `Challenge_Splay_DequeConjecture.lean`'s `theorem
deque_conjecture`, with `c = c₂ · (1 + c₁)`.  (Both cores are empirically true
with flat constants; jointly they are exactly the open conjecture.) -/
theorem deque_conjecture_CLOSED_of_turn_cores
    (hB : TurnCostBridge) (hT : TurnSumBoundLinear) :
    ∃ c, ∀ n, ∀ X : Fin n → ℕ,
    (X avoids ![2, 1, 3]) → (X avoids ![2, 3, 1]) →
    ∀ (init : BinaryTree), (h_size : init.num_nodes = n) → IsBST init →
    (∀ i : Fin n, (X i) ∈ init.toKeyList) →
    splay.sequence_cost init X ≤ c * n := by
  obtain ⟨c₂, hB⟩ := hB
  obtain ⟨c₁, hT⟩ := hT
  refine ⟨((c₂ * (1 + c₁) : ℕ) : ℝ), ?_⟩
  intro n X h213 h231 init h_size hbst hmem
  have hcast := sequence_cost_eq_costSum_cast n X init
  have hTb := hT n X init h_size hbst hmem h213 h231
  have hBb := hB n X init h_size hbst hmem h213 h231
  have htotal : (∑ i ∈ Finset.range n, costN init X i)
      ≤ c₂ * (1 + c₁) * n := by
    calc (∑ i ∈ Finset.range n, costN init X i)
        ≤ c₂ * (n + totalTurnsN init X) := hBb
      _ ≤ c₂ * (n + c₁ * n) := by
          refine Nat.mul_le_mul (Nat.le_refl c₂) ?_
          exact Nat.add_le_add (Nat.le_refl n) hTb
      _ = c₂ * (1 + c₁) * n := by ring
  rw [hcast]
  exact_mod_cast htotal

end Splay
end Splay
end Splay
end Splay
end Splay
end Splay

#print axioms Splay.Splay.Splay.Splay.Splay.Splay.turnSumBoundAlpha_of_linear
#print axioms Splay.Splay.Splay.Splay.Splay.Splay.deque_challenge_CLOSED_of_turn_cores
#print axioms Splay.Splay.Splay.Splay.Splay.Splay.deque_conjecture_CLOSED_of_turn_cores
