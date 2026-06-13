import Challenges.Splay_Tree.Def_Containment
import Challenges.Splay_Tree.Def_Ackermann
import Challenges.Splay_Tree.Def_Splay

/-!
# Sequential Access Theorem (Elmasry 2004) — direct proof track for `Splay.sequential`

Goal: `splay.sequence_cost init (one_to_n n) ≤ c * n` with NO dependency on the open
traversal/deque conjecture. `splay.cost` counts rotations, so this is exactly Elmasry's
`≤ 4.5n` rotation bound (Thm 2, "On the sequential access theorem and deque conjecture
for splay trees", TCS 314 (2004) 459–466).

Architecture (Elmasry → Lean), see `NOTES_sequential_formalization.md`:
  A reframe: sequential access = repeated min-splay of the root's right subtree (left
    subtree is shed); track the "splaying spine".
  B coloring yellow/green/black; C counting g/h/v + relations (1)-(5);
  D Lemma 1 (v ≥ 0, monotone); E link count ≤ 4.5n via h²/2 credit accounting; F assemble.

This file: compiling foundation (no `sorry`). The target is stated at the bottom.
-/

namespace Splay

/-! ## Foundation: the access sequence and the rotation-cost being summed -/

/-- The sequential access sequence is the identity on values. -/
theorem one_to_n_apply (n : ℕ) (i : Fin n) : one_to_n n i = (i : ℕ) := rfl

theorem one_to_n_strictMono (n : ℕ) : StrictMono (one_to_n n) := by
  intro a b hab; simpa [one_to_n] using hab

/-- `splay.cost` (the per-access rotation count) is nonnegative. Proved with the
generated induction principle, which matches the grandchild recursion of `splay.cost`. -/
theorem splay_cost_nonneg (t : BinaryTree) (q : ℕ) : 0 ≤ splay.cost t q := by
  fun_induction splay.cost t q <;> simp_all <;> positivity

/-- The total cost of an access sequence is a nonnegative real. -/
theorem sequence_cost_nonneg {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ) :
    0 ≤ splay.sequence_cost init X := by
  unfold splay.sequence_cost
  -- the running accumulator (tree, cost) keeps cost ≥ 0 since every added term is ≥ 0
  suffices h : ∀ (l : List (Fin n)) (acc : BinaryTree × ℝ), 0 ≤ acc.2 →
      0 ≤ (l.foldl (fun acc i =>
        let (t, c) := acc; (splay t (X i), c + splay.cost t (X i))) acc).2 by
    simpa using h (List.finRange n) (init, 0) le_rfl
  intro l
  induction l with
  | nil => intro acc hacc; simpa using hacc
  | cons i xs ih =>
      intro acc hacc
      apply ih
      have := splay_cost_nonneg acc.1 (X i)
      dsimp; linarith

/-! ## Target (Elmasry Theorem 2 ⇒ the repo's `sequential`, with `c = 4.5`)

The theorem to prove (currently routed in the repo through the open conjecture):

  `theorem sequential_direct :
      ∃ c, ∀ n, ∀ (init : BinaryTree), init.num_nodes = n → IsBST init →
        (∀ i : Fin n, (one_to_n n) i ∈ init.toKeyList) →
        splay.sequence_cost init (one_to_n n) ≤ c * n`

Proof obligation reduces (architecture A–F) to bounding the total rotation count by
`4.5 n`. The crux components still to build: the reframing `A` (min-splay process +
shed-left-subtree invariant) and the `h²/2` credit accounting `E`. -/

end Splay
