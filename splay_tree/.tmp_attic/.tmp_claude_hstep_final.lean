import Challenges.Splay_Tree.Def_Containment
import Challenges.Splay_Tree.Def_Ackermann
import Challenges.Splay_Tree.Def_Splay

/-!
# Deque challenge development (c·n bound for {213,231}-avoiding access; α(n) ≥ 1 closes both
the 50-pt deque and 100-pt deque-conjecture).
Validated design: Ω = Σ over LIVE non-root nodes of [hL² + hR² + 4(φ₂L+φ₂R)], chains counting
touched∩live; live = strictly inside the future interval (lo,hi), monotone shrinking.
-/

set_option maxHeartbeats 4000000

namespace Splay

def touchedCount (T : List Nat) (c : List Nat) : Nat := (c.filter (fun x => x ∈ T)).length

def rightSpine : BinaryTree → List Nat
  | .empty => []
  | .node _ k r => k :: rightSpine r

def leftSpine : BinaryTree → List Nat
  | .empty => []
  | .node l k _ => k :: leftSpine l

def rightSubtree : BinaryTree → BinaryTree
  | .empty => .empty
  | .node _ _ r => r

def leftSubtree : BinaryTree → BinaryTree
  | .empty => .empty
  | .node l _ _ => l

theorem touchedCount_cons_le (T : List Nat) (x : Nat) (c : List Nat) :
    touchedCount T (x :: c) ≤ touchedCount T c + 1 := by
  simp only [touchedCount, List.filter_cons]
  split
  · simp only [List.length_cons]
    omega
  · omega

theorem touchedCount_le_cons (T : List Nat) (x : Nat) (c : List Nat) :
    touchedCount T c ≤ touchedCount T (x :: c) := by
  simp only [touchedCount, List.filter_cons]
  split
  · simp only [List.length_cons]
    omega
  · omega

/-- Fuel-indexed version of `rel5_right_general`, by strong induction on `num_nodes`. -/
theorem rel5_right_aux (T : List Nat) :
    ∀ (n : Nat) (t : BinaryTree), t.num_nodes ≤ n → ∀ (q : Nat),
      touchedCount T (rightSpine (rightSubtree (splay t q)))
        ≤ touchedCount T (rightSpine t) + 1 := by
  intro n
  induction n with
  | zero =>
    intro t ht q
    cases t with
    | empty => exact Nat.zero_le _
    | node l k r =>
      exfalso
      have hnn : (BinaryTree.node l k r).num_nodes = 1 + l.num_nodes + r.num_nodes := rfl
      omega
  | succ n ih =>
    intro t ht q
    cases t with
    | empty => exact Nat.zero_le _
    | node l k r =>
      by_cases hqk : q = k
      · -- found at root
        rw [splay.eq_def]
        simp only [if_pos hqk]
        show touchedCount T (rightSpine r) ≤ touchedCount T (k :: rightSpine r) + 1
        have h := touchedCount_le_cons T k (rightSpine r)
        omega
      · by_cases hqlt : q < k
        · cases l with
          | empty =>
            -- q not found, root unchanged
            rw [splay.eq_def]
            simp only [if_neg hqk, if_pos hqlt]
            show touchedCount T (rightSpine r) ≤ touchedCount T (k :: rightSpine r) + 1
            have h := touchedCount_le_cons T k (rightSpine r)
            omega
          | node ll lk lr =>
            by_cases hqlk : q < lk
            · cases ll with
              | empty =>
                -- zig (grandchild empty)
                rw [splay.eq_def]
                simp only [if_neg hqk, if_pos hqlt, if_pos hqlk]
                show touchedCount T (k :: rightSpine r) ≤ touchedCount T (k :: rightSpine r) + 1
                omega
              | node a x b =>
                -- zig-zig
                rw [splay.eq_def]
                simp only [if_neg hqk, if_pos hqlt, if_pos hqlk]
                cases hs : splay (BinaryTree.node a x b) q with
                | empty =>
                  show touchedCount T (k :: rightSpine r) ≤ touchedCount T (k :: rightSpine r) + 1
                  omega
                | node A qq B =>
                  show touchedCount T (lk :: k :: rightSpine r)
                      ≤ touchedCount T (k :: rightSpine r) + 1
                  exact touchedCount_cons_le T lk (k :: rightSpine r)
            · by_cases hlkq : lk < q
              · cases lr with
                | empty =>
                  -- zig (grandchild empty)
                  rw [splay.eq_def]
                  simp only [if_neg hqk, if_pos hqlt, if_neg hqlk, if_pos hlkq]
                  show touchedCount T (k :: rightSpine r) ≤ touchedCount T (k :: rightSpine r) + 1
                  omega
                | node a x b =>
                  -- zig-zag
                  rw [splay.eq_def]
                  simp only [if_neg hqk, if_pos hqlt, if_neg hqlk, if_pos hlkq]
                  cases hs : splay (BinaryTree.node a x b) q with
                  | empty =>
                    show touchedCount T (k :: rightSpine r)
                        ≤ touchedCount T (k :: rightSpine r) + 1
                    omega
                  | node A qq B =>
                    show touchedCount T (k :: rightSpine r)
                        ≤ touchedCount T (k :: rightSpine r) + 1
                    omega
              · -- found at left child (q = lk)
                rw [splay.eq_def]
                simp only [if_neg hqk, if_pos hqlt, if_neg hqlk, if_neg hlkq]
                show touchedCount T (k :: rightSpine r) ≤ touchedCount T (k :: rightSpine r) + 1
                omega
        · -- k < q
          cases r with
          | empty =>
            rw [splay.eq_def]
            simp only [if_neg hqk, if_neg hqlt]
            exact Nat.zero_le _
          | node rl rk rr =>
            by_cases hqrk : q < rk
            · cases rl with
              | empty =>
                -- zag (grandchild empty)
                rw [splay.eq_def]
                simp only [if_neg hqk, if_neg hqlt, if_pos hqrk]
                show touchedCount T (rightSpine rr)
                    ≤ touchedCount T (k :: rk :: rightSpine rr) + 1
                have h1 := touchedCount_le_cons T rk (rightSpine rr)
                have h2 := touchedCount_le_cons T k (rk :: rightSpine rr)
                omega
              | node a x b =>
                -- zag-zig
                rw [splay.eq_def]
                simp only [if_neg hqk, if_neg hqlt, if_pos hqrk]
                cases hs : splay (BinaryTree.node a x b) q with
                | empty =>
                  show touchedCount T (rightSpine rr)
                      ≤ touchedCount T (k :: rk :: rightSpine rr) + 1
                  have h1 := touchedCount_le_cons T rk (rightSpine rr)
                  have h2 := touchedCount_le_cons T k (rk :: rightSpine rr)
                  omega
                | node A qq B =>
                  show touchedCount T (rk :: rightSpine rr)
                      ≤ touchedCount T (k :: rk :: rightSpine rr) + 1
                  have h2 := touchedCount_le_cons T k (rk :: rightSpine rr)
                  omega
            · by_cases hrkq : rk < q
              · cases rr with
                | empty =>
                  -- zag (grandchild empty)
                  rw [splay.eq_def]
                  simp only [if_neg hqk, if_neg hqlt, if_neg hqrk, if_pos hrkq]
                  exact Nat.zero_le _
                | node a x b =>
                  -- zag-zag: the only branch that needs the induction hypothesis
                  have hsz : (BinaryTree.node a x b).num_nodes ≤ n := by
                    have hnn :
                        (BinaryTree.node l k
                          (BinaryTree.node rl rk (BinaryTree.node a x b))).num_nodes
                        = 1 + l.num_nodes
                            + (1 + rl.num_nodes + (BinaryTree.node a x b).num_nodes) := rfl
                    omega
                  have hrec := ih (BinaryTree.node a x b) hsz q
                  rw [splay.eq_def]
                  simp only [if_neg hqk, if_neg hqlt, if_neg hqrk, if_pos hrkq]
                  cases hs : splay (BinaryTree.node a x b) q with
                  | empty => exact Nat.zero_le _
                  | node A qq B =>
                    rw [hs] at hrec
                    have hrec' : touchedCount T (rightSpine B)
                        ≤ touchedCount T (x :: rightSpine b) + 1 := hrec
                    show touchedCount T (rightSpine B)
                        ≤ touchedCount T (k :: rk :: x :: rightSpine b) + 1
                    have h1 := touchedCount_le_cons T rk (x :: rightSpine b)
                    have h2 := touchedCount_le_cons T k (rk :: x :: rightSpine b)
                    omega
              · -- found at right child (q = rk)
                rw [splay.eq_def]
                simp only [if_neg hqk, if_neg hqlt, if_neg hqrk, if_neg hrkq]
                show touchedCount T (rightSpine rr)
                    ≤ touchedCount T (k :: rk :: rightSpine rr) + 1
                have h1 := touchedCount_le_cons T rk (rightSpine rr)
                have h2 := touchedCount_le_cons T k (rk :: rightSpine rr)
                omega

theorem rel5_right_general (T : List Nat) :
    ∀ (t : BinaryTree) (q : Nat),
      touchedCount T (rightSpine (rightSubtree (splay t q)))
        ≤ touchedCount T (rightSpine t) + 1 :=
  fun t q => rel5_right_aux T t.num_nodes t (Nat.le_refl _) q

/-- Fuel-indexed version of `rel5_left_general`, by strong induction on `num_nodes`. -/
theorem rel5_left_aux (T : List Nat) :
    ∀ (n : Nat) (t : BinaryTree), t.num_nodes ≤ n → ∀ (q : Nat),
      touchedCount T (leftSpine (leftSubtree (splay t q)))
        ≤ touchedCount T (leftSpine t) + 1 := by
  intro n
  induction n with
  | zero =>
    intro t ht q
    cases t with
    | empty => exact Nat.zero_le _
    | node l k r =>
      exfalso
      have hnn : (BinaryTree.node l k r).num_nodes = 1 + l.num_nodes + r.num_nodes := rfl
      omega
  | succ n ih =>
    intro t ht q
    cases t with
    | empty => exact Nat.zero_le _
    | node l k r =>
      by_cases hqk : q = k
      · -- found at root
        rw [splay.eq_def]
        simp only [if_pos hqk]
        show touchedCount T (leftSpine l) ≤ touchedCount T (k :: leftSpine l) + 1
        have h := touchedCount_le_cons T k (leftSpine l)
        omega
      · by_cases hqlt : q < k
        · cases l with
          | empty =>
            -- q not found, root unchanged
            rw [splay.eq_def]
            simp only [if_neg hqk, if_pos hqlt]
            exact Nat.zero_le _
          | node ll lk lr =>
            by_cases hqlk : q < lk
            · cases ll with
              | empty =>
                -- zig (grandchild empty)
                rw [splay.eq_def]
                simp only [if_neg hqk, if_pos hqlt, if_pos hqlk]
                exact Nat.zero_le _
              | node a x b =>
                -- zig-zig: the only branch that needs the induction hypothesis
                have hsz : (BinaryTree.node a x b).num_nodes ≤ n := by
                  have hnn :
                      (BinaryTree.node
                        (BinaryTree.node (BinaryTree.node a x b) lk lr) k r).num_nodes
                      = 1 + (1 + (BinaryTree.node a x b).num_nodes + lr.num_nodes)
                          + r.num_nodes := rfl
                  omega
                have hrec := ih (BinaryTree.node a x b) hsz q
                rw [splay.eq_def]
                simp only [if_neg hqk, if_pos hqlt, if_pos hqlk]
                cases hs : splay (BinaryTree.node a x b) q with
                | empty => exact Nat.zero_le _
                | node A qq B =>
                  rw [hs] at hrec
                  have hrec' : touchedCount T (leftSpine A)
                      ≤ touchedCount T (x :: leftSpine a) + 1 := hrec
                  show touchedCount T (leftSpine A)
                      ≤ touchedCount T (k :: lk :: x :: leftSpine a) + 1
                  have h1 := touchedCount_le_cons T lk (x :: leftSpine a)
                  have h2 := touchedCount_le_cons T k (lk :: x :: leftSpine a)
                  omega
            · by_cases hlkq : lk < q
              · cases lr with
                | empty =>
                  -- zig (grandchild empty)
                  rw [splay.eq_def]
                  simp only [if_neg hqk, if_pos hqlt, if_neg hqlk, if_pos hlkq]
                  show touchedCount T (leftSpine ll)
                      ≤ touchedCount T (k :: lk :: leftSpine ll) + 1
                  have h1 := touchedCount_le_cons T lk (leftSpine ll)
                  have h2 := touchedCount_le_cons T k (lk :: leftSpine ll)
                  omega
                | node a x b =>
                  -- zig-zag
                  rw [splay.eq_def]
                  simp only [if_neg hqk, if_pos hqlt, if_neg hqlk, if_pos hlkq]
                  cases hs : splay (BinaryTree.node a x b) q with
                  | empty =>
                    show touchedCount T (leftSpine ll)
                        ≤ touchedCount T (k :: lk :: leftSpine ll) + 1
                    have h1 := touchedCount_le_cons T lk (leftSpine ll)
                    have h2 := touchedCount_le_cons T k (lk :: leftSpine ll)
                    omega
                  | node A qq B =>
                    show touchedCount T (lk :: leftSpine ll)
                        ≤ touchedCount T (k :: lk :: leftSpine ll) + 1
                    have h := touchedCount_le_cons T k (lk :: leftSpine ll)
                    omega
              · -- found at left child (q = lk)
                rw [splay.eq_def]
                simp only [if_neg hqk, if_pos hqlt, if_neg hqlk, if_neg hlkq]
                show touchedCount T (leftSpine ll)
                    ≤ touchedCount T (k :: lk :: leftSpine ll) + 1
                have h1 := touchedCount_le_cons T lk (leftSpine ll)
                have h2 := touchedCount_le_cons T k (lk :: leftSpine ll)
                omega
        · -- k < q
          cases r with
          | empty =>
            rw [splay.eq_def]
            simp only [if_neg hqk, if_neg hqlt]
            show touchedCount T (leftSpine l) ≤ touchedCount T (k :: leftSpine l) + 1
            have h := touchedCount_le_cons T k (leftSpine l)
            omega
          | node rl rk rr =>
            by_cases hqrk : q < rk
            · cases rl with
              | empty =>
                -- zag (grandchild empty)
                rw [splay.eq_def]
                simp only [if_neg hqk, if_neg hqlt, if_pos hqrk]
                show touchedCount T (k :: leftSpine l) ≤ touchedCount T (k :: leftSpine l) + 1
                omega
              | node a x b =>
                -- zag-zig
                rw [splay.eq_def]
                simp only [if_neg hqk, if_neg hqlt, if_pos hqrk]
                cases hs : splay (BinaryTree.node a x b) q with
                | empty =>
                  show touchedCount T (k :: leftSpine l)
                      ≤ touchedCount T (k :: leftSpine l) + 1
                  omega
                | node A qq B =>
                  show touchedCount T (k :: leftSpine l)
                      ≤ touchedCount T (k :: leftSpine l) + 1
                  omega
            · by_cases hrkq : rk < q
              · cases rr with
                | empty =>
                  -- zag (grandchild empty)
                  rw [splay.eq_def]
                  simp only [if_neg hqk, if_neg hqlt, if_neg hqrk, if_pos hrkq]
                  show touchedCount T (k :: leftSpine l)
                      ≤ touchedCount T (k :: leftSpine l) + 1
                  omega
                | node a x b =>
                  -- zag-zag
                  rw [splay.eq_def]
                  simp only [if_neg hqk, if_neg hqlt, if_neg hqrk, if_pos hrkq]
                  cases hs : splay (BinaryTree.node a x b) q with
                  | empty =>
                    show touchedCount T (k :: leftSpine l)
                        ≤ touchedCount T (k :: leftSpine l) + 1
                    omega
                  | node A qq B =>
                    show touchedCount T (rk :: k :: leftSpine l)
                        ≤ touchedCount T (k :: leftSpine l) + 1
                    exact touchedCount_cons_le T rk (k :: leftSpine l)
              · -- found at right child (q = rk)
                rw [splay.eq_def]
                simp only [if_neg hqk, if_neg hqlt, if_neg hqrk, if_neg hrkq]
                show touchedCount T (k :: leftSpine l) ≤ touchedCount T (k :: leftSpine l) + 1
                omega

theorem rel5_left_general (T : List Nat) :
    ∀ (t : BinaryTree) (q : Nat),
      touchedCount T (leftSpine (leftSubtree (splay t q)))
        ≤ touchedCount T (leftSpine t) + 1 :=
  fun t q => rel5_left_aux T t.num_nodes t (Nat.le_refl _) q

theorem splay_zigzig_shape_general (ll lr r A B : BinaryTree) (lk k q : Nat)
    (hnk : q ≠ k) (hqlt : q < k) (hqllt : q < lk)
    (hll : ll ≠ .empty)
    (hS : splay ll q = .node A q B) :
    splay (.node (.node ll lk lr) k r) q
      = .node A q (.node B lk (.node lr k r)) := by
  cases ll with
  | empty => exact absurd rfl hll
  | node a b c =>
    rw [splay.eq_def]
    simp only [if_neg hnk, if_pos hqlt, if_pos hqllt]
    rw [hS]
    simp [rotate, rotateRight]

theorem splay_zigzag_shape_general (ll lr r A B : BinaryTree) (lk k q : Nat)
    (hnk : q ≠ k) (hqlt : q < k) (hlkq : lk < q)
    (hlr : lr ≠ .empty)
    (hS : splay lr q = .node A q B) :
    splay (.node (.node ll lk lr) k r) q
      = .node (.node ll lk A) q (.node B k r) := by
  have hnot : ¬ q < lk := by omega
  cases lr with
  | empty => exact absurd rfl hlr
  | node a b c =>
    rw [splay.eq_def]
    simp only [if_neg hnk, if_pos hqlt, if_neg hnot, if_pos hlkq]
    rw [hS]
    simp [rotate, rotateRight, rotateLeft]

theorem splay_zagzag_shape_general (l rl rr A B : BinaryTree) (rk k q : Nat)
    (hnk : q ≠ k) (hklt : k < q) (hrkq : rk < q)
    (hrr : rr ≠ .empty)
    (hS : splay rr q = .node A q B) :
    splay (.node l k (.node rl rk rr)) q
      = .node (.node (.node l k rl) rk A) q B := by
  have hnlt : ¬ q < k := by omega
  have hnqrk : ¬ q < rk := by omega
  cases rr with
  | empty => exact absurd rfl hrr
  | node a b c =>
    rw [splay.eq_def]
    simp only [if_neg hnk, if_neg hnlt, if_neg hnqrk, if_pos hrkq]
    rw [hS]
    simp [rotate, rotateLeft]

theorem splay_zagzig_shape_general (l rl rr A B : BinaryTree) (rk k q : Nat)
    (hnk : q ≠ k) (hklt : k < q) (hqrk : q < rk)
    (hrl : rl ≠ .empty)
    (hS : splay rl q = .node A q B) :
    splay (.node l k (.node rl rk rr)) q
      = .node (.node l k A) q (.node B rk rr) := by
  have hnlt : ¬ q < k := by omega
  cases rl with
  | empty => exact absurd rfl hrl
  | node a b c =>
    rw [splay.eq_def]
    simp only [if_neg hnk, if_neg hnlt, if_pos hqrk]
    rw [hS]
    simp [rotate, rotateLeft, rotateRight]


/-- Four-term node potential: hL² + hR² where hL counts a member-set M on the right spine of
the left child and hR on the left spine of the right child. (φ₂-terms handled separately.) -/
def hSq2 (T : List Nat) : BinaryTree → Nat
  | .empty => 0
  | .node l _ r =>
      (touchedCount T (rightSpine l)) ^ 2 + (touchedCount T (leftSpine r)) ^ 2
      + hSq2 T l + hSq2 T r

/-- Exact `hSq2`-exchange equation for the zig-zig interior result shape
`node A q (node B lk (node lr k r))`.  Given the shape equation as hypothesis, the
potential of the splay result decomposes into the three root-path node terms
(q-terms: `tcR A`² + `tcL (node B lk (node lr k r))`²; lk-terms: `tcR B`² +
`tcL (node lr k r)`²; k-terms: `tcR lr`² + `tcL r`²) plus the four subtree sums. -/
theorem hSq2_exchange_zigzig (T : List Nat) (ll lr r A B : BinaryTree) (lk k q : Nat)
    (hshape : splay (.node (.node ll lk lr) k r) q
      = .node A q (.node B lk (.node lr k r))) :
    hSq2 T (splay (.node (.node ll lk lr) k r) q)
      = hSq2 T A + hSq2 T B
        + (touchedCount T (rightSpine A)) ^ 2
        + (touchedCount T (leftSpine (.node B lk (.node lr k r)))) ^ 2
        + (touchedCount T (rightSpine B)) ^ 2
        + (touchedCount T (leftSpine (.node lr k r))) ^ 2
        + (touchedCount T (rightSpine lr)) ^ 2
        + (touchedCount T (leftSpine r)) ^ 2
        + hSq2 T lr + hSq2 T r := by
  rw [hshape]
  simp only [hSq2]
  ring

/-- The companion exact unfolding of `hSq2` on the ORIGINAL zig-side tree
`node (node ll lk lr) k r` (pure definitional unfolding). -/
theorem hSq2_orig_zig (T : List Nat) (ll lr r : BinaryTree) (lk k : Nat) :
    hSq2 T (.node (.node ll lk lr) k r)
      = (touchedCount T (rightSpine (.node ll lk lr))) ^ 2
        + (touchedCount T (leftSpine r)) ^ 2
        + ((touchedCount T (rightSpine ll)) ^ 2 + (touchedCount T (leftSpine lr)) ^ 2
          + hSq2 T ll + hSq2 T lr)
        + hSq2 T r := rfl

/-- Exact `hSq2`-exchange equation for the zig-zag interior result shape
`node (node ll lk A) q (node B k r)`.  The RHS is the true definitional unfolding:
q-terms: `tcR (node ll lk A)`² + `tcL (node B k r)`²; lk-terms: `tcR ll`² + `tcL A`²;
k-terms: `tcR B`² + `tcL r`²; plus the subtree sums for `ll`, `A`, `B`, `r`. -/
theorem hSq2_exchange_zigzag (T : List Nat) (ll lr r A B : BinaryTree) (lk k q : Nat)
    (hshape : splay (.node (.node ll lk lr) k r) q
      = .node (.node ll lk A) q (.node B k r)) :
    hSq2 T (splay (.node (.node ll lk lr) k r) q)
      = (touchedCount T (rightSpine (.node ll lk A))) ^ 2
        + (touchedCount T (leftSpine (.node B k r))) ^ 2
        + ((touchedCount T (rightSpine ll)) ^ 2 + (touchedCount T (leftSpine A)) ^ 2
          + hSq2 T ll + hSq2 T A)
        + ((touchedCount T (rightSpine B)) ^ 2 + (touchedCount T (leftSpine r)) ^ 2
          + hSq2 T B + hSq2 T r) := by
  rw [hshape]; rfl

/-- Zag-zag exchange: unfolding of `hSq2` on the splayed tree
`.node (.node (.node l k rl) rk A) q B`. -/
theorem hSq2_exchange_zagzag (T : List Nat) (l rl rr A B : BinaryTree) (rk k q : Nat)
    (hshape : splay (.node l k (.node rl rk rr)) q
      = .node (.node (.node l k rl) rk A) q B) :
    hSq2 T (splay (.node l k (.node rl rk rr)) q)
      = (touchedCount T (rightSpine (.node (.node l k rl) rk A))) ^ 2
        + (touchedCount T (leftSpine B)) ^ 2
        + ((touchedCount T (rightSpine (.node l k rl))) ^ 2
            + (touchedCount T (leftSpine A)) ^ 2
            + ((touchedCount T (rightSpine l)) ^ 2 + (touchedCount T (leftSpine rl)) ^ 2
                + hSq2 T l + hSq2 T rl)
            + hSq2 T A)
        + hSq2 T B := by
  rw [hshape]
  rfl

/-- Zag-zig exchange: unfolding of `hSq2` on the splayed tree
`.node (.node l k A) q (.node B rk rr)`. -/
theorem hSq2_exchange_zagzig (T : List Nat) (l rl rr A B : BinaryTree) (rk k q : Nat)
    (hshape : splay (.node l k (.node rl rk rr)) q
      = .node (.node l k A) q (.node B rk rr)) :
    hSq2 T (splay (.node l k (.node rl rk rr)) q)
      = (touchedCount T (rightSpine (.node l k A))) ^ 2
        + (touchedCount T (leftSpine (.node B rk rr))) ^ 2
        + ((touchedCount T (rightSpine l)) ^ 2 + (touchedCount T (leftSpine A)) ^ 2
            + hSq2 T l + hSq2 T A)
        + ((touchedCount T (rightSpine B)) ^ 2 + (touchedCount T (leftSpine rr)) ^ 2
            + hSq2 T B + hSq2 T rr) := by
  rw [hshape]
  rfl

/-- Original-tree unfolding for the zag configuration `.node l k (.node rl rk rr)`. -/
theorem hSq2_orig_zag (T : List Nat) (l rl rr : BinaryTree) (rk k : Nat) :
    hSq2 T (.node l k (.node rl rk rr))
      = (touchedCount T (rightSpine l)) ^ 2
        + (touchedCount T (leftSpine (.node rl rk rr))) ^ 2
        + hSq2 T l
        + ((touchedCount T (rightSpine rl)) ^ 2 + (touchedCount T (leftSpine rr)) ^ 2
            + hSq2 T rl + hSq2 T rr) := rfl



-- ===== {213,231} characterization layer =====
/-- A pattern contained in `X ∘ g` for strictly monotone `g` is contained in `X`;
hence avoidance is preserved under composition with strictly monotone maps. -/
theorem avoids_comp_strictMono {n m : ℕ} (X : Fin n → ℕ) (P : Fin 3 → ℕ)
    (h : X avoids P) (g : Fin m → Fin n) (hg : StrictMono g) :
    (fun i => X (g i)) avoids P := by
  intro hc
  obtain ⟨f, hf, hfp⟩ := hc
  exact h ⟨g ∘ f, hg.comp hf, fun x y => hfp x y⟩

/-- Prefix restriction preserves pattern avoidance. -/
theorem deque_tail_avoids {n : ℕ} (X : Fin n → ℕ) (P : Fin 3 → ℕ)
    (h : X avoids P) (m : ℕ) (hm : m ≤ n) :
    (fun i : Fin m => X (Fin.castLE hm i)) avoids P :=
  avoids_comp_strictMono X P h (Fin.castLE hm) (fun _ _ hab => hab)

/-- The characterization of deque sequences: if `X` avoids `213` and `231`, then from any
position `i` the future of the sequence is one-sided (all later values are `≤ X i`, or all
later values are `≥ X i`). -/
theorem deque_future_one_sided {n : ℕ} (X : Fin n → ℕ)
    (h213 : X avoids ![2, 1, 3]) (h231 : X avoids ![2, 3, 1]) :
    ∀ i : Fin n, (∀ j : Fin n, i < j → X j ≤ X i) ∨ (∀ j : Fin n, i < j → X i ≤ X j) := by
  intro i
  by_contra hcon
  push_neg at hcon
  obtain ⟨⟨j, hij, hXj⟩, ⟨k, hik, hXk⟩⟩ := hcon
  -- hXj : X i < X j,  hXk : X k < X i
  have hjk : j ≠ k := by
    intro hEq
    rw [hEq] at hXj
    omega
  rcases lt_or_gt_of_ne hjk with hjk' | hjk'
  · -- j < k : the triple (i, j, k) realizes the pattern 231 in X.
    apply h231
    refine ⟨![i, j, k], ?_, ?_⟩
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
    · intro x y
      fin_cases x <;> fin_cases y <;> simp_all <;> omega
  · -- k < j : the triple (i, k, j) realizes the pattern 213 in X.
    apply h213
    refine ⟨![i, k, j], ?_, ?_⟩
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
    · intro x y
      fin_cases x <;> fin_cases y <;> simp_all <;> omega

/-- Trivial corollary of `deque_future_one_sided` at the later index `j`. -/
theorem deque_lo_mono {n : ℕ} (X : Fin n → ℕ)
    (h213 : X avoids ![2, 1, 3]) (h231 : X avoids ![2, 3, 1])
    (i j : Fin n) (hij : i < j) :
    (∀ k : Fin n, i < k → X i ≤ X k) →
      (∀ k : Fin n, j < k → X k ≤ X j) ∨ (∀ k : Fin n, j < k → X j ≤ X k) :=
  fun _ => deque_future_one_sided X h213 h231 j


-- ===== cost bridge (ported from sequential development) =====
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

theorem splay_cost_le_search_path_len (t : BinaryTree) (q : Nat) :
    splay.cost t q ≤ t.search_path_len q := by
  rw [splay_cost_eq_search_path_len_sub_one]
  exact_mod_cast Nat.sub_le (t.search_path_len q) 1


-- search-path utilities (ported)
theorem search_path_len_le_num_nodes :
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

theorem search_path_len_node_of_lt {l r : BinaryTree}
    {k q : Nat} (hqk : q < k) :
    (BinaryTree.node l k r).search_path_len q =
      1 + l.search_path_len q := by
  simp [BinaryTree.search_path_len, hqk]

theorem search_path_len_node_of_gt {l r : BinaryTree}
    {k q : Nat} (hkq : k < q) :
    (BinaryTree.node l k r).search_path_len q =
      1 + r.search_path_len q := by
  have hnot : ¬ q < k := by omega
  simp [BinaryTree.search_path_len, hnot, hkq]

theorem search_path_len_node_of_eq {l r : BinaryTree}
    {k q : Nat} (hqk : q = k) :
    (BinaryTree.node l k r).search_path_len q = 1 := by
  subst q
  simp [BinaryTree.search_path_len]


-- ===== process bridge (assembly layer) =====


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

-- ===== fresh telescope (assembly layer) =====


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

-- ===== summation kit (assembly layer) =====


/-!
# Abstract run-summation kit (pure ℕ arithmetic)

(K1) `dropsum_le` : telescoping bound for truncated-subtraction drops along a chain.
(K2) `run_geometric_bound` : the two-lane geometric run bound.  Runs are triples
     `(side, cost, budget)`.  The list is in **reverse chronological order**
     (head = most recent run), so `lastCost s rest` scans backwards in time and
     returns the cost of the most recent earlier run on side `s` (0 if none).
     A chronological-order wrapper `run_geometric_bound_chronological` is also provided.

Final constant for (K2): from per-run `2·c_j ≤ prevSameSide_j + 2·b_j` we conclude
`2·Σc ≤ 4·Σb`, i.e. `Σc ≤ 2·Σb`.
-/

/-! ## (K1) The drop-sum telescope -/

/-- Exact ℕ-valued telescope identity: total (truncated) drop plus final value equals
initial value plus total (truncated) rise.  Over ℤ this is the telescoping identity
`Σ (a j - a (j+1)) = a 0 - a m` split into positive and negative parts. -/
theorem dropsum_eq (m : ℕ) (a : ℕ → ℕ) :
    ∑ j ∈ Finset.range m, (a j - a (j+1)) + a m
      = a 0 + ∑ j ∈ Finset.range m, (a (j+1) - a j) := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    omega

/-- (K1) The drop-sum telescope: the sum of truncated drops along a chain is bounded by
the initial value plus the sum of truncated rises. -/
theorem dropsum_le {m : ℕ} (a : ℕ → ℕ) :
    ∑ j ∈ Finset.range m, (a j - a (j+1))
      ≤ a 0 + ∑ j ∈ Finset.range m, (a (j+1) - a j) := by
  have h := dropsum_eq m a
  omega

/-! ## (K2) The two-lane geometric run bound -/

/-- Cost of the most recent run on side `s`, where the list is processed
most-recent-run-first (reverse chronological order); `0` if no such run exists. -/
def lastCost (s : Bool) : List (Bool × ℕ × ℕ) → ℕ
  | [] => 0
  | (s', c, _) :: rest => if s' = s then c else lastCost s rest

@[simp] theorem lastCost_nil (s : Bool) : lastCost s [] = 0 := rfl

theorem lastCost_cons_same (s : Bool) (c b : ℕ) (rest : List (Bool × ℕ × ℕ)) :
    lastCost s ((s, c, b) :: rest) = c := by
  simp [lastCost]

theorem lastCost_cons_diff {s s' : Bool} (h : s' ≠ s) (c b : ℕ)
    (rest : List (Bool × ℕ × ℕ)) :
    lastCost s ((s', c, b) :: rest) = lastCost s rest := by
  simp [lastCost, h]

/-- Strengthened invariant for the snoc-chronological (= cons on the reversed list)
induction:  `2·S + 2·cm + 2·cM ≤ 4·B`, where `S`/`B` are the cost/budget sums and
`cm`/`cM` are the costs of the most recent run on each side (0 if none).

Step check for a new most-recent run `(s, c, b)` on side `s` (say `s = false`) with
master bound `2c ≤ lastCost false tl + 2b`:
new LHS = `2(S + c) + 2·lastCost true tl + 2c = (2S + 2·LT) + 4c
        ≤ (2S + 2·LT + 2·LF) + 4b ≤ 4B + 4b = 4(B + b)`. -/
theorem run_geometric_bound_aux :
    ∀ runs : List (Bool × ℕ × ℕ),
      (∀ pre x post, runs = pre ++ x :: post →
          2 * x.2.1 ≤ lastCost x.1 post + 2 * x.2.2) →
      2 * (runs.map (fun r => r.2.1)).sum
          + 2 * lastCost true runs + 2 * lastCost false runs
        ≤ 4 * (runs.map (fun r => r.2.2)).sum := by
  intro runs
  induction runs with
  | nil => intro _; simp
  | cons hd tl ih =>
    intro hmaster
    obtain ⟨s, c, b⟩ := hd
    have hhd : 2 * c ≤ lastCost s tl + 2 * b := hmaster [] (s, c, b) tl rfl
    have ih' := ih (fun pre x post h => hmaster ((s, c, b) :: pre) x post (by rw [h]; rfl))
    simp only [List.map_cons, List.sum_cons]
    cases s with
    | false =>
      rw [lastCost_cons_diff (by decide), lastCost_cons_same]
      omega
    | true =>
      rw [lastCost_cons_same, lastCost_cons_diff (by decide)]
      omega

/-- (K2) The two-lane geometric run bound, list in **reverse chronological order**
(head = most recent run).  Hypothesis: every run's doubled cost is at most the cost of
the most recent earlier same-side run (0 if none) plus twice its own budget.
Conclusion (final constant: 2): `2·Σ cost ≤ 4·Σ budget`, i.e. `Σ cost ≤ 2·Σ budget`. -/
theorem run_geometric_bound (runs : List (Bool × ℕ × ℕ))
    (hmaster : ∀ pre x post, runs = pre ++ x :: post →
        2 * x.2.1 ≤ lastCost x.1 post + 2 * x.2.2) :
    2 * (runs.map (fun r => r.2.1)).sum ≤ 4 * (runs.map (fun r => r.2.2)).sum := by
  have h := run_geometric_bound_aux runs hmaster
  omega

/-- (K2), chronological orientation: the list is in **chronological order**
(head = earliest run); for a run `x` with chronological predecessors `pre`,
the previous same-side cost is `lastCost x.1 pre.reverse` (scan `pre` backwards). -/
theorem run_geometric_bound_chronological (runs : List (Bool × ℕ × ℕ))
    (hmaster : ∀ pre x post, runs = pre ++ x :: post →
        2 * x.2.1 ≤ lastCost x.1 pre.reverse + 2 * x.2.2) :
    2 * (runs.map (fun r => r.2.1)).sum ≤ 4 * (runs.map (fun r => r.2.2)).sum := by
  have h := run_geometric_bound runs.reverse ?_
  · simpa using h
  · intro pre x post hsplit
    have hr : runs = post.reverse ++ x :: pre.reverse := by
      have h2 := congrArg List.reverse hsplit
      simpa [List.reverse_append] using h2
    have h3 := hmaster post.reverse x pre.reverse hr
    simpa using h3


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

/-- Fuel-indexed: `splay` preserves any `ForallTree` predicate (it only rearranges keys). -/

theorem splay_forallTree_aux (p : Nat → Prop) :
    ∀ (n : Nat) (t : BinaryTree), t.num_nodes ≤ n → ∀ (q : Nat),
      ForallTree p t → ForallTree p (splay t q) := by
  intro n
  induction n with
  | zero =>
    intro t ht q hF
    cases t with
    | empty => exact hF
    | node l k r =>
      exfalso
      have hnn : (BinaryTree.node l k r).num_nodes = 1 + l.num_nodes + r.num_nodes := rfl
      omega
  | succ n ih =>
    intro t ht q hF
    cases t with
    | empty => exact hF
    | node l k r =>
      rw [forallTree_node_iff] at hF
      obtain ⟨hFl, hpk, hFr⟩ := hF
      by_cases hqk : q = k
      · rw [splay.eq_def]
        simp only [if_pos hqk]
        exact forallTree_node_iff.mpr ⟨hFl, hpk, hFr⟩
      · by_cases hqlt : q < k
        · cases l with
          | empty =>
            rw [splay.eq_def]
            simp only [if_neg hqk, if_pos hqlt]
            exact forallTree_node_iff.mpr ⟨hFl, hpk, hFr⟩
          | node ll lk lr =>
            rw [forallTree_node_iff] at hFl
            obtain ⟨hFll, hplk, hFlr⟩ := hFl
            by_cases hqlk : q < lk
            · cases ll with
              | empty =>
                rw [splay.eq_def]
                simp only [if_neg hqk, if_pos hqlt, if_pos hqlk]
                show ForallTree p (.node .empty lk (.node lr k r))
                exact forallTree_node_iff.mpr ⟨hFll, hplk,
                  forallTree_node_iff.mpr ⟨hFlr, hpk, hFr⟩⟩
              | node a x b =>
                have hsz : (BinaryTree.node a x b).num_nodes ≤ n := by
                  have hnn : (BinaryTree.node (BinaryTree.node (BinaryTree.node a x b) lk lr)
                      k r).num_nodes
                      = 1 + (1 + (BinaryTree.node a x b).num_nodes + lr.num_nodes)
                        + r.num_nodes := rfl
                  omega
                have hrec := ih (BinaryTree.node a x b) hsz q hFll
                rw [splay.eq_def]
                simp only [if_neg hqk, if_pos hqlt, if_pos hqlk]
                cases hs : splay (BinaryTree.node a x b) q with
                | empty =>
                  show ForallTree p (.node .empty lk (.node lr k r))
                  exact forallTree_node_iff.mpr ⟨ForallTree.left, hplk,
                    forallTree_node_iff.mpr ⟨hFlr, hpk, hFr⟩⟩
                | node A z B =>
                  rw [hs] at hrec
                  rw [forallTree_node_iff] at hrec
                  obtain ⟨hA, hz, hB⟩ := hrec
                  show ForallTree p (.node A z (.node B lk (.node lr k r)))
                  exact forallTree_node_iff.mpr ⟨hA, hz,
                    forallTree_node_iff.mpr ⟨hB, hplk,
                      forallTree_node_iff.mpr ⟨hFlr, hpk, hFr⟩⟩⟩
            · by_cases hlkq : lk < q
              · cases lr with
                | empty =>
                  rw [splay.eq_def]
                  simp only [if_neg hqk, if_pos hqlt, if_neg hqlk, if_pos hlkq]
                  show ForallTree p (.node ll lk (.node .empty k r))
                  exact forallTree_node_iff.mpr ⟨hFll, hplk,
                    forallTree_node_iff.mpr ⟨ForallTree.left, hpk, hFr⟩⟩
                | node a x b =>
                  have hsz : (BinaryTree.node a x b).num_nodes ≤ n := by
                    have hnn : (BinaryTree.node (BinaryTree.node ll lk
                        (BinaryTree.node a x b)) k r).num_nodes
                        = 1 + (1 + ll.num_nodes + (BinaryTree.node a x b).num_nodes)
                          + r.num_nodes := rfl
                    omega
                  have hrec := ih (BinaryTree.node a x b) hsz q hFlr
                  rw [splay.eq_def]
                  simp only [if_neg hqk, if_pos hqlt, if_neg hqlk, if_pos hlkq]
                  cases hs : splay (BinaryTree.node a x b) q with
                  | empty =>
                    show ForallTree p (.node ll lk (.node .empty k r))
                    exact forallTree_node_iff.mpr ⟨hFll, hplk,
                      forallTree_node_iff.mpr ⟨ForallTree.left, hpk, hFr⟩⟩
                  | node A z B =>
                    rw [hs] at hrec
                    rw [forallTree_node_iff] at hrec
                    obtain ⟨hA, hz, hB⟩ := hrec
                    show ForallTree p (.node (.node ll lk A) z (.node B k r))
                    exact forallTree_node_iff.mpr
                      ⟨forallTree_node_iff.mpr ⟨hFll, hplk, hA⟩, hz,
                        forallTree_node_iff.mpr ⟨hB, hpk, hFr⟩⟩
              · -- q = lk (found at left child)
                rw [splay.eq_def]
                simp only [if_neg hqk, if_pos hqlt, if_neg hqlk, if_neg hlkq]
                show ForallTree p (.node ll lk (.node lr k r))
                exact forallTree_node_iff.mpr ⟨hFll, hplk,
                  forallTree_node_iff.mpr ⟨hFlr, hpk, hFr⟩⟩
        · -- k < q
          cases r with
          | empty =>
            rw [splay.eq_def]
            simp only [if_neg hqk, if_neg hqlt]
            exact forallTree_node_iff.mpr ⟨hFl, hpk, hFr⟩
          | node rl rk rr =>
            rw [forallTree_node_iff] at hFr
            obtain ⟨hFrl, hprk, hFrr⟩ := hFr
            by_cases hqrk : q < rk
            · cases rl with
              | empty =>
                rw [splay.eq_def]
                simp only [if_neg hqk, if_neg hqlt, if_pos hqrk]
                show ForallTree p (.node (.node l k .empty) rk rr)
                exact forallTree_node_iff.mpr
                  ⟨forallTree_node_iff.mpr ⟨hFl, hpk, ForallTree.left⟩, hprk, hFrr⟩
              | node a x b =>
                have hsz : (BinaryTree.node a x b).num_nodes ≤ n := by
                  have hnn : (BinaryTree.node l k (BinaryTree.node (BinaryTree.node a x b)
                      rk rr)).num_nodes
                      = 1 + l.num_nodes
                        + (1 + (BinaryTree.node a x b).num_nodes + rr.num_nodes) := rfl
                  omega
                have hrec := ih (BinaryTree.node a x b) hsz q hFrl
                rw [splay.eq_def]
                simp only [if_neg hqk, if_neg hqlt, if_pos hqrk]
                cases hs : splay (BinaryTree.node a x b) q with
                | empty =>
                  show ForallTree p (.node (.node l k .empty) rk rr)
                  exact forallTree_node_iff.mpr
                    ⟨forallTree_node_iff.mpr ⟨hFl, hpk, ForallTree.left⟩, hprk, hFrr⟩
                | node A z B =>
                  rw [hs] at hrec
                  rw [forallTree_node_iff] at hrec
                  obtain ⟨hA, hz, hB⟩ := hrec
                  show ForallTree p (.node (.node l k A) z (.node B rk rr))
                  exact forallTree_node_iff.mpr
                    ⟨forallTree_node_iff.mpr ⟨hFl, hpk, hA⟩, hz,
                      forallTree_node_iff.mpr ⟨hB, hprk, hFrr⟩⟩
            · by_cases hrkq : rk < q
              · cases rr with
                | empty =>
                  rw [splay.eq_def]
                  simp only [if_neg hqk, if_neg hqlt, if_neg hqrk, if_pos hrkq]
                  show ForallTree p (.node (.node l k rl) rk .empty)
                  exact forallTree_node_iff.mpr
                    ⟨forallTree_node_iff.mpr ⟨hFl, hpk, hFrl⟩, hprk, ForallTree.left⟩
                | node a x b =>
                  have hsz : (BinaryTree.node a x b).num_nodes ≤ n := by
                    have hnn : (BinaryTree.node l k (BinaryTree.node rl rk
                        (BinaryTree.node a x b))).num_nodes
                        = 1 + l.num_nodes
                          + (1 + rl.num_nodes + (BinaryTree.node a x b).num_nodes) := rfl
                    omega
                  have hrec := ih (BinaryTree.node a x b) hsz q hFrr
                  rw [splay.eq_def]
                  simp only [if_neg hqk, if_neg hqlt, if_neg hqrk, if_pos hrkq]
                  cases hs : splay (BinaryTree.node a x b) q with
                  | empty =>
                    show ForallTree p (.node (.node l k rl) rk .empty)
                    exact forallTree_node_iff.mpr
                      ⟨forallTree_node_iff.mpr ⟨hFl, hpk, hFrl⟩, hprk, ForallTree.left⟩
                  | node A z B =>
                    rw [hs] at hrec
                    rw [forallTree_node_iff] at hrec
                    obtain ⟨hA, hz, hB⟩ := hrec
                    show ForallTree p (.node (.node (.node l k rl) rk A) z B)
                    exact forallTree_node_iff.mpr
                      ⟨forallTree_node_iff.mpr
                        ⟨forallTree_node_iff.mpr ⟨hFl, hpk, hFrl⟩, hprk, hA⟩, hz, hB⟩
              · -- q = rk (found at right child)
                rw [splay.eq_def]
                simp only [if_neg hqk, if_neg hqlt, if_neg hqrk, if_neg hrkq]
                show ForallTree p (.node (.node l k rl) rk rr)
                exact forallTree_node_iff.mpr
                  ⟨forallTree_node_iff.mpr ⟨hFl, hpk, hFrl⟩, hprk, hFrr⟩


theorem splay_forallTree_kd (p : Nat → Prop) (t : BinaryTree) (q : Nat)
    (hF : ForallTree p t) : ForallTree p (splay t q) :=
  splay_forallTree_aux p t.num_nodes t (Nat.le_refl _) q hF

theorem keyDepth_splay_le_aux :
    ∀ (n : Nat) (t : BinaryTree), t.num_nodes ≤ n → ∀ (q y : Nat),
      IsBST t → keyDepth y (splay t q) ≤ keyDepth y t + 2 := by
  intro n
  induction n with
  | zero =>
    intro t ht q y _
    cases t with
    | empty => exact Nat.le_add_right _ _
    | node l k r =>
      exfalso
      have hnn : (BinaryTree.node l k r).num_nodes = 1 + l.num_nodes + r.num_nodes := rfl
      omega
  | succ n ih =>
    intro t ht q y hbst
    cases t with
    | empty => exact Nat.le_add_right _ _
    | node l k r =>
      rw [isBST_node_iff] at hbst
      obtain ⟨hbL, hbR, hbstl, hbstr⟩ := hbst
      by_cases hqk : q = k
      · -- q found at root: tree unchanged
        rw [splay.eq_def]
        simp only [if_pos hqk]
        omega
      · by_cases hqlt : q < k
        · cases l with
          | empty =>
            -- q not found, root unchanged
            rw [splay.eq_def]
            simp only [if_neg hqk, if_pos hqlt]
            omega
          | node ll lk lr =>
            rw [forallTree_node_iff] at hbL
            obtain ⟨hbL_ll, hlk_k, hbL_lr⟩ := hbL
            rw [isBST_node_iff] at hbstl
            obtain ⟨hbLL, hbLR, hbstll, hbstlr⟩ := hbstl
            by_cases hqlk : q < lk
            · cases ll with
              | empty =>
                -- zig with empty grandchild
                rw [splay.eq_def]
                simp only [if_neg hqk, if_pos hqlt, if_pos hqlk]
                show keyDepth y (.node .empty lk (.node lr k r))
                    ≤ keyDepth y (.node (.node .empty lk lr) k r) + 2
                simp only [keyDepth_node, keyDepth_empty]
                split_ifs <;> omega
              | node a x b =>
                -- zig-zig
                have hsz : (BinaryTree.node a x b).num_nodes ≤ n := by
                  have hnn : (BinaryTree.node (BinaryTree.node (BinaryTree.node a x b) lk lr)
                      k r).num_nodes
                      = 1 + (1 + (BinaryTree.node a x b).num_nodes + lr.num_nodes)
                        + r.num_nodes := rfl
                  omega
                have hrec := ih (BinaryTree.node a x b) hsz q y hbstll
                have hFz := splay_forallTree_kd (fun w => w < lk) (BinaryTree.node a x b) q hbLL
                rw [splay.eq_def]
                simp only [if_neg hqk, if_pos hqlt, if_pos hqlk]
                cases hs : splay (BinaryTree.node a x b) q with
                | empty =>
                  show keyDepth y (.node .empty lk (.node lr k r))
                      ≤ keyDepth y (.node (.node (.node a x b) lk lr) k r) + 2
                  simp only [keyDepth_node, keyDepth_empty]
                  split_ifs <;> omega
                | node A z B =>
                  rw [hs] at hrec hFz
                  rw [forallTree_node_iff] at hFz
                  have hzlk : z < lk := hFz.2.1
                  show keyDepth y (.node A z (.node B lk (.node lr k r)))
                      ≤ keyDepth y (.node (.node (.node a x b) lk lr) k r) + 2
                  simp only [keyDepth_node] at hrec ⊢
                  split_ifs at hrec ⊢ <;> omega
            · by_cases hlkq : lk < q
              · cases lr with
                | empty =>
                  -- zig with empty grandchild
                  rw [splay.eq_def]
                  simp only [if_neg hqk, if_pos hqlt, if_neg hqlk, if_pos hlkq]
                  show keyDepth y (.node ll lk (.node .empty k r))
                      ≤ keyDepth y (.node (.node ll lk .empty) k r) + 2
                  simp only [keyDepth_node, keyDepth_empty]
                  split_ifs <;> omega
                | node a x b =>
                  -- zig-zag
                  have hsz : (BinaryTree.node a x b).num_nodes ≤ n := by
                    have hnn : (BinaryTree.node (BinaryTree.node ll lk
                        (BinaryTree.node a x b)) k r).num_nodes
                        = 1 + (1 + ll.num_nodes + (BinaryTree.node a x b).num_nodes)
                          + r.num_nodes := rfl
                    omega
                  have hrec := ih (BinaryTree.node a x b) hsz q y hbstlr
                  have hFz1 := splay_forallTree_kd (fun w => lk < w) (BinaryTree.node a x b) q hbLR
                  have hFz2 := splay_forallTree_kd (fun w => w < k) (BinaryTree.node a x b) q hbL_lr
                  rw [splay.eq_def]
                  simp only [if_neg hqk, if_pos hqlt, if_neg hqlk, if_pos hlkq]
                  cases hs : splay (BinaryTree.node a x b) q with
                  | empty =>
                    show keyDepth y (.node ll lk (.node .empty k r))
                        ≤ keyDepth y (.node (.node ll lk (.node a x b)) k r) + 2
                    simp only [keyDepth_node, keyDepth_empty]
                    split_ifs <;> omega
                  | node A z B =>
                    rw [hs] at hrec hFz1 hFz2
                    rw [forallTree_node_iff] at hFz1 hFz2
                    have hlkz : lk < z := hFz1.2.1
                    have hzk : z < k := hFz2.2.1
                    show keyDepth y (.node (.node ll lk A) z (.node B k r))
                        ≤ keyDepth y (.node (.node ll lk (.node a x b)) k r) + 2
                    simp only [keyDepth_node] at hrec ⊢
                    split_ifs at hrec ⊢ <;> omega
              · -- q = lk: found at left child, single zig
                rw [splay.eq_def]
                simp only [if_neg hqk, if_pos hqlt, if_neg hqlk, if_neg hlkq]
                show keyDepth y (.node ll lk (.node lr k r))
                    ≤ keyDepth y (.node (.node ll lk lr) k r) + 2
                simp only [keyDepth_node]
                split_ifs <;> omega
        · -- k < q
          cases r with
          | empty =>
            rw [splay.eq_def]
            simp only [if_neg hqk, if_neg hqlt]
            omega
          | node rl rk rr =>
            rw [forallTree_node_iff] at hbR
            obtain ⟨hbR_rl, hk_rk, hbR_rr⟩ := hbR
            rw [isBST_node_iff] at hbstr
            obtain ⟨hbRL, hbRR, hbstrl, hbstrr⟩ := hbstr
            by_cases hqrk : q < rk
            · cases rl with
              | empty =>
                -- zag with empty grandchild
                rw [splay.eq_def]
                simp only [if_neg hqk, if_neg hqlt, if_pos hqrk]
                show keyDepth y (.node (.node l k .empty) rk rr)
                    ≤ keyDepth y (.node l k (.node .empty rk rr)) + 2
                simp only [keyDepth_node, keyDepth_empty]
                split_ifs <;> omega
              | node a x b =>
                -- zag-zig
                have hsz : (BinaryTree.node a x b).num_nodes ≤ n := by
                  have hnn : (BinaryTree.node l k (BinaryTree.node (BinaryTree.node a x b)
                      rk rr)).num_nodes
                      = 1 + l.num_nodes
                        + (1 + (BinaryTree.node a x b).num_nodes + rr.num_nodes) := rfl
                  omega
                have hrec := ih (BinaryTree.node a x b) hsz q y hbstrl
                have hFz1 := splay_forallTree_kd (fun w => w < rk) (BinaryTree.node a x b) q hbRL
                have hFz2 := splay_forallTree_kd (fun w => k < w) (BinaryTree.node a x b) q hbR_rl
                rw [splay.eq_def]
                simp only [if_neg hqk, if_neg hqlt, if_pos hqrk]
                cases hs : splay (BinaryTree.node a x b) q with
                | empty =>
                  show keyDepth y (.node (.node l k .empty) rk rr)
                      ≤ keyDepth y (.node l k (.node (.node a x b) rk rr)) + 2
                  simp only [keyDepth_node, keyDepth_empty]
                  split_ifs <;> omega
                | node A z B =>
                  rw [hs] at hrec hFz1 hFz2
                  rw [forallTree_node_iff] at hFz1 hFz2
                  have hzrk : z < rk := hFz1.2.1
                  have hkz : k < z := hFz2.2.1
                  show keyDepth y (.node (.node l k A) z (.node B rk rr))
                      ≤ keyDepth y (.node l k (.node (.node a x b) rk rr)) + 2
                  simp only [keyDepth_node] at hrec ⊢
                  split_ifs at hrec ⊢ <;> omega
            · by_cases hrkq : rk < q
              · cases rr with
                | empty =>
                  -- zag with empty grandchild
                  rw [splay.eq_def]
                  simp only [if_neg hqk, if_neg hqlt, if_neg hqrk, if_pos hrkq]
                  show keyDepth y (.node (.node l k rl) rk .empty)
                      ≤ keyDepth y (.node l k (.node rl rk .empty)) + 2
                  simp only [keyDepth_node, keyDepth_empty]
                  split_ifs <;> omega
                | node a x b =>
                  -- zag-zag
                  have hsz : (BinaryTree.node a x b).num_nodes ≤ n := by
                    have hnn : (BinaryTree.node l k (BinaryTree.node rl rk
                        (BinaryTree.node a x b))).num_nodes
                        = 1 + l.num_nodes
                          + (1 + rl.num_nodes + (BinaryTree.node a x b).num_nodes) := rfl
                    omega
                  have hrec := ih (BinaryTree.node a x b) hsz q y hbstrr
                  have hFz := splay_forallTree_kd (fun w => rk < w) (BinaryTree.node a x b) q hbRR
                  rw [splay.eq_def]
                  simp only [if_neg hqk, if_neg hqlt, if_neg hqrk, if_pos hrkq]
                  cases hs : splay (BinaryTree.node a x b) q with
                  | empty =>
                    show keyDepth y (.node (.node l k rl) rk .empty)
                        ≤ keyDepth y (.node l k (.node rl rk (.node a x b))) + 2
                    simp only [keyDepth_node, keyDepth_empty]
                    split_ifs <;> omega
                  | node A z B =>
                    rw [hs] at hrec hFz
                    rw [forallTree_node_iff] at hFz
                    have hrkz : rk < z := hFz.2.1
                    show keyDepth y (.node (.node (.node l k rl) rk A) z B)
                        ≤ keyDepth y (.node l k (.node rl rk (.node a x b))) + 2
                    simp only [keyDepth_node] at hrec ⊢
                    split_ifs at hrec ⊢ <;> omega
              · -- q = rk: found at right child, single zag
                rw [splay.eq_def]
                simp only [if_neg hqk, if_neg hqlt, if_neg hqrk, if_neg hrkq]
                show keyDepth y (.node (.node l k rl) rk rr)
                    ≤ keyDepth y (.node l k (.node rl rk rr)) + 2
                simp only [keyDepth_node]
                split_ifs <;> omega

/-- DEEPENING LEMMA: a splay on a BST deepens no key by more than 2 (the constant 2 is
tight: in a zig-zig step the old root and keys in the far subtree go down by exactly 2). -/

theorem keyDepth_splay_le (q y : Nat) (t : BinaryTree) (hbst : IsBST t) :
    keyDepth y (splay t q) ≤ keyDepth y t + 2 :=
  keyDepth_splay_le_aux t.num_nodes t (Nat.le_refl _) q y hbst

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


-- ===== ghost state + C1 conservation =====
structure GhostClaim where
  lo : ℕ
  hi : ℕ
  /-- doubled budget -/
  r : ℕ

/-- Ghost state of one side: a list of interval claims plus a scalar pool. -/

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
`(remaining undrained amount, updated claims)`.  Claims not satisfying `met` are kept
untouched; a met claim pays `min` of what is still owed and its budget. -/

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

/-! ### The ghost-state maintenance steps -/

/-- Ghost-state update on an OWN-side access (path `P`, touched set `T`, cost `c`,
fresh count `f`, accessed key `x`, side `isMin`):
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

/-- Ghost-state update on an OPPOSITE-side access: the pool gains `4`
(the two doubled `+2` re-hang units of L1). -/

def ghostStepOpp (g : GhostState) : GhostState := { g with pool := g.pool + 4 }

/-- Total budget of the claims met by the current access (touched set `T`, path `P`):
the amount the greedy drain can take from claims before touching the pool. -/

def metTotal (T P : List ℕ) (g : GhostState) : ℕ :=
  claimsListTotal (g.claims.filter (claimMet T P))

/-- The capped doubled ledger draw (copied verbatim from the frozen ledger development):
`2 * c - min (2 * c) (2 * kap * (1 + f))` is the doubled excess `2*c ∸ 2*kap*(1+f)`,
capped at the current ledger `D` so the ledger never underflows. -/

def draw (kap : ℕ) (c f D : ℕ) : ℕ := min D (2 * c - min (2 * c) (2 * kap * (1 + f)))

/-! ### C1 conservation

The exact arithmetic content of an own-side step: writing
`amount = 2*c - min (2*c) (2*kap*(1+f))` for the uncapped doubled draw, the greedy
drain pays `min amount (metTotal + pool)` out of the ghost total (claims first, pool
for the remainder), the debris repays at most `c`, and pruning only loses budget.
Hence the unconditional, always-true form (`ghost_C1_own_min`) carries the inner
`min` with `metTotal + pool`; the requested ledger-matching form (`ghost_C1_own`,
RHS = `D - min D amount + c = D - draw + c`, the ledger's own-side update) follows
under the cover hypothesis `amount ≤ metTotal + pool` — which is exactly what the
C2-strict invariant supplies in the full proof (`2tc ≤ Σ_met r + p + 10 + 10f` gives
`draw ≤ Σ_met r + p − 4`).  Without the cover hypothesis the requested form is FALSE
(an unmet claim block can strand budget above `D − amount`), so the `min`-form below
is the exact statement. -/

/-- **C1 conservation, exact unconditional form.**  An own-side ghost step decreases
the ghost total by exactly `min amount (metTotal + pool)` before the `+ c` debris
repay (pruning can only lose more), so the total stays under the corresponding
ledger update. -/

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

/-- **C1 conservation, ledger-matching form (the requested statement).**  Under the
cover hypothesis (supplied by the C2-strict invariant: the met claims plus the pool
cover the uncapped draw), an own-side ghost step keeps the ghost total below the
ledger's own-side update `D - min D amount + c = D - draw + c`. -/

theorem ghost_C1_own (kap : ℕ) (T P : List ℕ) (c f x : ℕ) (isMin : Bool)
    (g : GhostState) (D : ℕ)
    (h : claimsTotal g + g.pool ≤ D)
    (hcover : 2 * c - min (2 * c) (2 * kap * (1 + f)) ≤ metTotal T P g + g.pool) :
    claimsTotal (ghostStepOwn kap T P c f x isMin g)
      + (ghostStepOwn kap T P c f x isMin g).pool
      ≤ D - min D (2 * c - min (2 * c) (2 * kap * (1 + f))) + c := by
  have hmin := ghost_C1_own_min kap T P c f x isMin g D h
  rwa [min_eq_left hcover] at hmin

/-- C1 conservation restated against the frozen ledger's `draw`: the RHS is literally
the ledger's own-side update `D - draw kap c f D + c`. -/

theorem ghost_C1_own_draw (kap : ℕ) (T P : List ℕ) (c f x : ℕ) (isMin : Bool)
    (g : GhostState) (D : ℕ)
    (h : claimsTotal g + g.pool ≤ D)
    (hcover : 2 * c - min (2 * c) (2 * kap * (1 + f)) ≤ metTotal T P g + g.pool) :
    claimsTotal (ghostStepOwn kap T P c f x isMin g)
      + (ghostStepOwn kap T P c f x isMin g).pool
      ≤ D - draw kap c f D + c :=
  ghost_C1_own kap T P c f x isMin g D h hcover

/-- Unconditional safety: even without the cover hypothesis, an own-side step never
pushes the ghost total above `D + c` (the ledger never repays more than `c`). -/

theorem ghost_C1_own_safe (kap : ℕ) (T P : List ℕ) (c f x : ℕ) (isMin : Bool)
    (g : GhostState) (D : ℕ)
    (h : claimsTotal g + g.pool ≤ D) :
    claimsTotal (ghostStepOwn kap T P c f x isMin g)
      + (ghostStepOwn kap T P c f x isMin g).pool ≤ D + c := by
  have hmin := ghost_C1_own_min kap T P c f x isMin g D h
  set K := 2 * kap * (1 + f) with hK
  omega

/-- **C1 conservation, opposite side.**  An opposite-side access adds exactly `4` to
the pool, matching the ledger's `D + 4` update. -/

theorem ghost_C1_opp (g : GhostState) (D : ℕ)
    (h : claimsTotal g + g.pool ≤ D) :
    claimsTotal (ghostStepOpp g) + (ghostStepOpp g).pool ≤ D + 4 := by
  have h1 : claimsTotal (ghostStepOpp g) = claimsTotal g := rfl
  have h2 : (ghostStepOpp g).pool = g.pool + 4 := rfl
  rw [h1, h2]
  omega

-- ===== master derivation keystone =====
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

/-! ### The keystone: MASTER from (C1) + (C2-strict) -/

/-- **MASTER derivation (keystone, `κ = 6`).**  From the conservation
inequality (C1) `Sr + p ≤ D` (met-claims sum plus pool within the ledger), the
strict cover inequality (C2) `2·tc ≤ Sr + p + 10 + 10·fr`, and the path-length
split `c + 1 = tc + fr` (links = touched + fresh − 1), the capstone's per-access
MASTER inequality follows:
`2c = 2tc + 2fr − 2 ≤ Sr + p + 8 + 12·fr ≤ D + 12·(1 + fr) = D + 2κ(1 + fr)`. -/

theorem master_of_C1_C2 (D tc fr Sr p c : ℕ)
    (hC1 : Sr + p ≤ D)
    (hC2 : 2 * tc ≤ Sr + p + 10 + 10 * fr)
    (hlen : c + 1 = tc + fr) :
    2 * c ≤ D + 2 * 6 * (1 + fr) := by
  omega

/-- **MASTER derivation, general form.**  Same as `master_of_C1_C2` for any
`kap ≥ 6`. -/

theorem master_of_C1_C2_general (kap D tc fr Sr p c : ℕ) (hkap : 6 ≤ kap)
    (hC1 : Sr + p ≤ D)
    (hC2 : 2 * tc ≤ Sr + p + 10 + 10 * fr)
    (hlen : c + 1 = tc + fr) :
    2 * c ≤ D + 2 * kap * (1 + fr) := by
  have h12 : 2 * c ≤ D + 2 * 6 * (1 + fr) := by omega
  have hmul : 2 * 6 * (1 + fr) ≤ 2 * kap * (1 + fr) :=
    Nat.mul_le_mul_right _ (by omega)
  exact h12.trans (Nat.add_le_add_left hmul D)

/-! ### Monotonicity: the met-claims sum is at most the full claims sum -/

/-- **Met-sum monotonicity.**  The sum of remnant budgets over any sub-selection
of claims (e.g. the claims met by a path) is at most the sum over all claims.
Together with (C1-full) `Σ_all r + p ≤ D` this yields the `hC1` hypothesis of
`master_of_C1_C2` for `Sr` = the met-claims sum. -/

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


-- ===== touched-deepening (R2 backbone) =====
def tc1 (T : List Nat) (k : Nat) : Nat := if k ∈ T then 1 else 0

theorem tc1_le_one (T : List Nat) (k : Nat) : tc1 T k ≤ 1 := by
  unfold tc1; split <;> omega

/-- Touched count along the `y`-search-path. -/

def pathCost (T : List Nat) (y : Nat) (t : BinaryTree) : Nat :=
  touchedCount T (searchPath y t)

theorem touchedCount_nil (T : List Nat) : touchedCount T [] = 0 := rfl

theorem touchedCount_cons (T : List Nat) (x : Nat) (c : List Nat) :
    touchedCount T (x :: c) = tc1 T x + touchedCount T c := by
  simp only [touchedCount, List.filter_cons, tc1]
  by_cases hx : x ∈ T
  · simp [hx]
    omega
  · simp [hx]

theorem pathCost_empty (T : List Nat) (y : Nat) : pathCost T y .empty = 0 := rfl

theorem pathCost_node (T : List Nat) (y k : Nat) (l r : BinaryTree) :
    pathCost T y (.node l k r)
      = if y = k then tc1 T k
        else if y < k then tc1 T k + pathCost T y l
        else tc1 T k + pathCost T y r := by
  simp only [pathCost, searchPath]
  split_ifs with h1 h2
  · rw [touchedCount_cons, touchedCount_nil]
    omega
  · rw [touchedCount_cons]
  · rw [touchedCount_cons]

theorem touchedCount_splay_le_aux (T : List Nat) :
    ∀ (n : Nat) (t : BinaryTree), t.num_nodes ≤ n → ∀ (q y : Nat),
      IsBST t → pathCost T y (splay t q) ≤ pathCost T y t + 2 := by
  intro n
  induction n with
  | zero =>
    intro t ht q y _
    cases t with
    | empty => exact Nat.le_add_right _ _
    | node l k r =>
      exfalso
      have hnn : (BinaryTree.node l k r).num_nodes = 1 + l.num_nodes + r.num_nodes := rfl
      omega
  | succ n ih =>
    intro t ht q y hbst
    cases t with
    | empty => exact Nat.le_add_right _ _
    | node l k r =>
      rw [isBST_node_iff] at hbst
      obtain ⟨hbL, hbR, hbstl, hbstr⟩ := hbst
      by_cases hqk : q = k
      · -- q found at root: tree unchanged
        rw [splay.eq_def]
        simp only [if_pos hqk]
        omega
      · by_cases hqlt : q < k
        · cases l with
          | empty =>
            -- q not found, root unchanged
            rw [splay.eq_def]
            simp only [if_neg hqk, if_pos hqlt]
            omega
          | node ll lk lr =>
            rw [forallTree_node_iff] at hbL
            obtain ⟨hbL_ll, hlk_k, hbL_lr⟩ := hbL
            rw [isBST_node_iff] at hbstl
            obtain ⟨hbLL, hbLR, hbstll, hbstlr⟩ := hbstl
            by_cases hqlk : q < lk
            · cases ll with
              | empty =>
                -- zig with empty grandchild
                rw [splay.eq_def]
                simp only [if_neg hqk, if_pos hqlt, if_pos hqlk]
                show pathCost T y (.node .empty lk (.node lr k r))
                    ≤ pathCost T y (.node (.node .empty lk lr) k r) + 2
                have hck := tc1_le_one T k
                have hclk := tc1_le_one T lk
                simp only [pathCost_node, pathCost_empty]
                split_ifs <;> omega
              | node a x b =>
                -- zig-zig
                have hsz : (BinaryTree.node a x b).num_nodes ≤ n := by
                  have hnn : (BinaryTree.node (BinaryTree.node (BinaryTree.node a x b) lk lr)
                      k r).num_nodes
                      = 1 + (1 + (BinaryTree.node a x b).num_nodes + lr.num_nodes)
                        + r.num_nodes := rfl
                  omega
                have hrec := ih (BinaryTree.node a x b) hsz q y hbstll
                have hFz := splay_forallTree_kd (fun w => w < lk) (BinaryTree.node a x b) q hbLL
                rw [splay.eq_def]
                simp only [if_neg hqk, if_pos hqlt, if_pos hqlk]
                cases hs : splay (BinaryTree.node a x b) q with
                | empty =>
                  show pathCost T y (.node .empty lk (.node lr k r))
                      ≤ pathCost T y (.node (.node (.node a x b) lk lr) k r) + 2
                  have hck := tc1_le_one T k
                  have hclk := tc1_le_one T lk
                  have hcx := tc1_le_one T x
                  simp only [pathCost_node, pathCost_empty]
                  split_ifs <;> omega
                | node A z B =>
                  rw [hs] at hrec hFz
                  rw [forallTree_node_iff] at hFz
                  have hzlk : z < lk := hFz.2.1
                  show pathCost T y (.node A z (.node B lk (.node lr k r)))
                      ≤ pathCost T y (.node (.node (.node a x b) lk lr) k r) + 2
                  have hck := tc1_le_one T k
                  have hclk := tc1_le_one T lk
                  have hcx := tc1_le_one T x
                  have hcz := tc1_le_one T z
                  simp only [pathCost_node] at hrec ⊢
                  split_ifs at hrec ⊢ <;> omega
            · by_cases hlkq : lk < q
              · cases lr with
                | empty =>
                  -- zig with empty grandchild
                  rw [splay.eq_def]
                  simp only [if_neg hqk, if_pos hqlt, if_neg hqlk, if_pos hlkq]
                  show pathCost T y (.node ll lk (.node .empty k r))
                      ≤ pathCost T y (.node (.node ll lk .empty) k r) + 2
                  have hck := tc1_le_one T k
                  have hclk := tc1_le_one T lk
                  simp only [pathCost_node, pathCost_empty]
                  split_ifs <;> omega
                | node a x b =>
                  -- zig-zag
                  have hsz : (BinaryTree.node a x b).num_nodes ≤ n := by
                    have hnn : (BinaryTree.node (BinaryTree.node ll lk
                        (BinaryTree.node a x b)) k r).num_nodes
                        = 1 + (1 + ll.num_nodes + (BinaryTree.node a x b).num_nodes)
                          + r.num_nodes := rfl
                    omega
                  have hrec := ih (BinaryTree.node a x b) hsz q y hbstlr
                  have hFz1 := splay_forallTree_kd (fun w => lk < w) (BinaryTree.node a x b) q hbLR
                  have hFz2 := splay_forallTree_kd (fun w => w < k) (BinaryTree.node a x b) q hbL_lr
                  rw [splay.eq_def]
                  simp only [if_neg hqk, if_pos hqlt, if_neg hqlk, if_pos hlkq]
                  cases hs : splay (BinaryTree.node a x b) q with
                  | empty =>
                    show pathCost T y (.node ll lk (.node .empty k r))
                        ≤ pathCost T y (.node (.node ll lk (.node a x b)) k r) + 2
                    have hck := tc1_le_one T k
                    have hclk := tc1_le_one T lk
                    have hcx := tc1_le_one T x
                    simp only [pathCost_node, pathCost_empty]
                    split_ifs <;> omega
                  | node A z B =>
                    rw [hs] at hrec hFz1 hFz2
                    rw [forallTree_node_iff] at hFz1 hFz2
                    have hlkz : lk < z := hFz1.2.1
                    have hzk : z < k := hFz2.2.1
                    show pathCost T y (.node (.node ll lk A) z (.node B k r))
                        ≤ pathCost T y (.node (.node ll lk (.node a x b)) k r) + 2
                    have hck := tc1_le_one T k
                    have hclk := tc1_le_one T lk
                    have hcx := tc1_le_one T x
                    have hcz := tc1_le_one T z
                    simp only [pathCost_node] at hrec ⊢
                    split_ifs at hrec ⊢ <;> omega
              · -- q = lk: found at left child, single zig
                rw [splay.eq_def]
                simp only [if_neg hqk, if_pos hqlt, if_neg hqlk, if_neg hlkq]
                show pathCost T y (.node ll lk (.node lr k r))
                    ≤ pathCost T y (.node (.node ll lk lr) k r) + 2
                have hck := tc1_le_one T k
                have hclk := tc1_le_one T lk
                simp only [pathCost_node]
                split_ifs <;> omega
        · -- k < q
          cases r with
          | empty =>
            rw [splay.eq_def]
            simp only [if_neg hqk, if_neg hqlt]
            omega
          | node rl rk rr =>
            rw [forallTree_node_iff] at hbR
            obtain ⟨hbR_rl, hk_rk, hbR_rr⟩ := hbR
            rw [isBST_node_iff] at hbstr
            obtain ⟨hbRL, hbRR, hbstrl, hbstrr⟩ := hbstr
            by_cases hqrk : q < rk
            · cases rl with
              | empty =>
                -- zag with empty grandchild
                rw [splay.eq_def]
                simp only [if_neg hqk, if_neg hqlt, if_pos hqrk]
                show pathCost T y (.node (.node l k .empty) rk rr)
                    ≤ pathCost T y (.node l k (.node .empty rk rr)) + 2
                have hck := tc1_le_one T k
                have hcrk := tc1_le_one T rk
                simp only [pathCost_node, pathCost_empty]
                split_ifs <;> omega
              | node a x b =>
                -- zag-zig
                have hsz : (BinaryTree.node a x b).num_nodes ≤ n := by
                  have hnn : (BinaryTree.node l k (BinaryTree.node (BinaryTree.node a x b)
                      rk rr)).num_nodes
                      = 1 + l.num_nodes
                        + (1 + (BinaryTree.node a x b).num_nodes + rr.num_nodes) := rfl
                  omega
                have hrec := ih (BinaryTree.node a x b) hsz q y hbstrl
                have hFz1 := splay_forallTree_kd (fun w => w < rk) (BinaryTree.node a x b) q hbRL
                have hFz2 := splay_forallTree_kd (fun w => k < w) (BinaryTree.node a x b) q hbR_rl
                rw [splay.eq_def]
                simp only [if_neg hqk, if_neg hqlt, if_pos hqrk]
                cases hs : splay (BinaryTree.node a x b) q with
                | empty =>
                  show pathCost T y (.node (.node l k .empty) rk rr)
                      ≤ pathCost T y (.node l k (.node (.node a x b) rk rr)) + 2
                  have hck := tc1_le_one T k
                  have hcrk := tc1_le_one T rk
                  have hcx := tc1_le_one T x
                  simp only [pathCost_node, pathCost_empty]
                  split_ifs <;> omega
                | node A z B =>
                  rw [hs] at hrec hFz1 hFz2
                  rw [forallTree_node_iff] at hFz1 hFz2
                  have hzrk : z < rk := hFz1.2.1
                  have hkz : k < z := hFz2.2.1
                  show pathCost T y (.node (.node l k A) z (.node B rk rr))
                      ≤ pathCost T y (.node l k (.node (.node a x b) rk rr)) + 2
                  have hck := tc1_le_one T k
                  have hcrk := tc1_le_one T rk
                  have hcx := tc1_le_one T x
                  have hcz := tc1_le_one T z
                  simp only [pathCost_node] at hrec ⊢
                  split_ifs at hrec ⊢ <;> omega
            · by_cases hrkq : rk < q
              · cases rr with
                | empty =>
                  -- zag with empty grandchild
                  rw [splay.eq_def]
                  simp only [if_neg hqk, if_neg hqlt, if_neg hqrk, if_pos hrkq]
                  show pathCost T y (.node (.node l k rl) rk .empty)
                      ≤ pathCost T y (.node l k (.node rl rk .empty)) + 2
                  have hck := tc1_le_one T k
                  have hcrk := tc1_le_one T rk
                  simp only [pathCost_node, pathCost_empty]
                  split_ifs <;> omega
                | node a x b =>
                  -- zag-zag
                  have hsz : (BinaryTree.node a x b).num_nodes ≤ n := by
                    have hnn : (BinaryTree.node l k (BinaryTree.node rl rk
                        (BinaryTree.node a x b))).num_nodes
                        = 1 + l.num_nodes
                          + (1 + rl.num_nodes + (BinaryTree.node a x b).num_nodes) := rfl
                    omega
                  have hrec := ih (BinaryTree.node a x b) hsz q y hbstrr
                  have hFz := splay_forallTree_kd (fun w => rk < w) (BinaryTree.node a x b) q hbRR
                  rw [splay.eq_def]
                  simp only [if_neg hqk, if_neg hqlt, if_neg hqrk, if_pos hrkq]
                  cases hs : splay (BinaryTree.node a x b) q with
                  | empty =>
                    show pathCost T y (.node (.node l k rl) rk .empty)
                        ≤ pathCost T y (.node l k (.node rl rk (.node a x b))) + 2
                    have hck := tc1_le_one T k
                    have hcrk := tc1_le_one T rk
                    have hcx := tc1_le_one T x
                    simp only [pathCost_node, pathCost_empty]
                    split_ifs <;> omega
                  | node A z B =>
                    rw [hs] at hrec hFz
                    rw [forallTree_node_iff] at hFz
                    have hrkz : rk < z := hFz.2.1
                    show pathCost T y (.node (.node (.node l k rl) rk A) z B)
                        ≤ pathCost T y (.node l k (.node rl rk (.node a x b))) + 2
                    have hck := tc1_le_one T k
                    have hcrk := tc1_le_one T rk
                    have hcx := tc1_le_one T x
                    have hcz := tc1_le_one T z
                    simp only [pathCost_node] at hrec ⊢
                    split_ifs at hrec ⊢ <;> omega
              · -- q = rk: found at right child, single zag
                rw [splay.eq_def]
                simp only [if_neg hqk, if_neg hqlt, if_neg hqrk, if_neg hrkq]
                show pathCost T y (.node (.node l k rl) rk rr)
                    ≤ pathCost T y (.node l k (.node rl rk rr)) + 2
                have hck := tc1_le_one T k
                have hcrk := tc1_le_one T rk
                simp only [pathCost_node]
                split_ifs <;> omega

set_option linter.unusedVariables false in
/-- TOUCHED-DEEPENING LEMMA (the +2 ledger justification), in the requested form.
Empirically pinned: the constant 2 is tight, and `hpath` is in fact NOT needed (see
`touchedCount_searchPath_splay_le'` below); it is kept here to match the target statement. -/

theorem touchedCount_searchPath_splay_le (q y : Nat) (t : BinaryTree) (T : List Nat)
    (hbst : IsBST t) (hpath : ∀ z ∈ searchPath q t, z ∈ T) :
    touchedCount T (searchPath y (splay t q))
      ≤ touchedCount T (searchPath y t) + 2 :=
  touchedCount_splay_le_aux T t.num_nodes t (Nat.le_refl _) q y hbst

/-- Hypothesis-free version: the `hpath` assumption is unnecessary. -/

theorem touchedCount_searchPath_splay_le' (q y : Nat) (t : BinaryTree) (T : List Nat)
    (hbst : IsBST t) :
    touchedCount T (searchPath y (splay t q))
      ≤ touchedCount T (searchPath y t) + 2 :=
  touchedCount_splay_le_aux T t.num_nodes t (Nat.le_refl _) q y hbst


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


-- ===== R2-core: mixed-T opposite-side deepening =====
def rootKey : BinaryTree → Nat
  | .empty => 0
  | .node _ k _ => k

/-! ## touchedCount toolkit -/

theorem touchedCount_cons_mem {T : List Nat} {x : Nat} (h : x ∈ T) (c : List Nat) :
    touchedCount T (x :: c) = touchedCount T c + 1 := by
  simp only [touchedCount, List.filter_cons]
  rw [if_pos (decide_eq_true h), List.length_cons]

theorem touchedCount_append (T a b : List Nat) :
    touchedCount T (a ++ b) = touchedCount T a + touchedCount T b := by
  simp [touchedCount, List.filter_append]

theorem touchedCount_le_length (T c : List Nat) : touchedCount T c ≤ c.length :=
  List.length_filter_le _ _

/-- Two touched-sets that agree on the members of `c` count `c` identically. -/

theorem touchedCount_congr {T T' c : List Nat}
    (h : ∀ z ∈ c, (z ∈ T') ↔ (z ∈ T)) : touchedCount T' c = touchedCount T c := by
  simp only [touchedCount]
  congr 1
  exact List.filter_congr (fun x hx => decide_eq_decide.mpr (h x hx))

/-! ## ForallTree / IsBST toolkit (ported verbatim from the development file) -/

theorem searchPath_left_irrel {k v : Nat} (hv : k ≤ v) (X Y r : BinaryTree) :
    searchPath v (.node X k r) = searchPath v (.node Y k r) := by
  rcases Nat.eq_or_lt_of_le hv with heq | hlt
  · rw [searchPath_node_self heq.symm, searchPath_node_self heq.symm]
  · rw [searchPath_node_gt hlt, searchPath_node_gt hlt]

/-- For `v` at-or-below the root key, the search path of `v` ignores the right subtree. -/

theorem searchPath_right_irrel {k v : Nat} (hv : v ≤ k) (l X Y : BinaryTree) :
    searchPath v (.node l k X) = searchPath v (.node l k Y) := by
  rcases Nat.eq_or_lt_of_le hv with heq | hlt
  · rw [searchPath_node_self heq, searchPath_node_self heq]
  · rw [searchPath_node_lt hlt, searchPath_node_lt hlt]

/-- A min-side (`q ≤ k`) search path stays at keys ≤ k. -/

theorem searchPath_all_le_of_left {l r : BinaryTree} {k q : Nat}
    (hL : ForallTree (fun x => x < k) l) (hq : q ≤ k) :
    ∀ w ∈ searchPath q (.node l k r), w ≤ k := by
  intro w hw
  rcases Nat.eq_or_lt_of_le hq with heq | hlt
  · rw [searchPath_node_self heq] at hw
    simp only [List.mem_singleton] at hw
    omega
  · rw [searchPath_node_lt hlt] at hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact Nat.le_refl _
    · exact Nat.le_of_lt (mem_searchPath_forall (p := fun x => x < k) hL hw)

/-- A max-side (`k ≤ q`) search path stays at keys ≥ k. -/

theorem searchPath_all_ge_of_right {l r : BinaryTree} {k q : Nat}
    (hR : ForallTree (fun x => k < x) r) (hq : k ≤ q) :
    ∀ w ∈ searchPath q (.node l k r), k ≤ w := by
  intro w hw
  rcases Nat.eq_or_lt_of_le hq with heq | hlt
  · rw [searchPath_node_self heq.symm] at hw
    simp only [List.mem_singleton] at hw
    omega
  · rw [searchPath_node_gt hlt] at hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact Nat.le_refl _
    · exact Nat.le_of_lt (mem_searchPath_forall hR hw)

/-! ## Splay toolkit (ported verbatim from the development file) -/

theorem newPath_prefix_left (l r : BinaryTree) (k q v : Nat)
    (hL : ForallTree (fun x => x < k) l) (hq : q ≤ k) (hv : k ≤ v) :
    ∃ p, searchPath v (splay (.node l k r) q) = p ++ searchPath v (.node l k r)
      ∧ p.length ≤ 2 := by
  by_cases hqk : q = k
  · -- found at root: splay is the identity
    refine ⟨[], ?_, by simp⟩
    rw [splay.eq_def]
    simp only [if_pos hqk, List.nil_append]
  · have hqlt : q < k := Nat.lt_of_le_of_ne hq hqk
    cases l with
    | empty =>
      -- q not found, root unchanged
      refine ⟨[], ?_, by simp⟩
      rw [splay.eq_def]
      simp only [if_neg hqk, if_pos hqlt, List.nil_append]
    | node ll lk lr =>
      rcases forallTree_node_iff.mp hL with ⟨hFll, hlkk, hFlr⟩
      have hlkv : lk < v := Nat.lt_of_lt_of_le hlkk hv
      by_cases hqlk : q < lk
      · cases ll with
        | empty =>
          -- zig with empty grandchild
          refine ⟨[lk], ?_, by simp⟩
          rw [splay.eq_def]
          simp only [if_neg hqk, if_pos hqlt, if_pos hqlk]
          show searchPath v (.node .empty lk (.node lr k r))
              = [lk] ++ searchPath v (.node (.node .empty lk lr) k r)
          rw [searchPath_node_gt hlkv, List.singleton_append]
          exact congrArg (List.cons lk) (searchPath_left_irrel hv lr (.node .empty lk lr) r)
        | node a x b =>
          -- zig-zig
          cases hS : splay (BinaryTree.node a x b) q with
          | empty => exact absurd hS (splay_ne_empty a b x q)
          | node A s B =>
            have hsk : s < k := by
              have hF := splay_forallTree_kd (fun z => z < k) (.node a x b) q hFll
              rw [hS] at hF
              exact (forallTree_node_iff.mp hF).2.1
            have hsv : s < v := Nat.lt_of_lt_of_le hsk hv
            refine ⟨[s, lk], ?_, by simp⟩
            rw [splay_zigzig_shape (.node a x b) lr r A B lk k q s hqk hqlt hqlk
                  (fun h => nomatch h) hS,
                searchPath_node_gt hsv, searchPath_node_gt hlkv,
                searchPath_left_irrel hv lr (.node (.node a x b) lk lr) r]
            rfl
      · by_cases hlkq : lk < q
        · cases lr with
          | empty =>
            -- zig with empty grandchild
            refine ⟨[lk], ?_, by simp⟩
            rw [splay.eq_def]
            simp only [if_neg hqk, if_pos hqlt, if_neg hqlk, if_pos hlkq]
            show searchPath v (.node ll lk (.node .empty k r))
                = [lk] ++ searchPath v (.node (.node ll lk .empty) k r)
            rw [searchPath_node_gt hlkv, List.singleton_append]
            exact congrArg (List.cons lk) (searchPath_left_irrel hv .empty (.node ll lk .empty) r)
          | node a x b =>
            -- zig-zag
            cases hS : splay (BinaryTree.node a x b) q with
            | empty => exact absurd hS (splay_ne_empty a b x q)
            | node A s B =>
              have hsk : s < k := by
                have hF := splay_forallTree_kd (fun z => z < k) (.node a x b) q hFlr
                rw [hS] at hF
                exact (forallTree_node_iff.mp hF).2.1
              have hsv : s < v := Nat.lt_of_lt_of_le hsk hv
              refine ⟨[s], ?_, by simp⟩
              rw [splay_zigzag_shape ll (.node a x b) r A B lk k q s hqk hqlt hlkq
                    (fun h => nomatch h) hS,
                  searchPath_node_gt hsv,
                  searchPath_left_irrel hv B (.node ll lk (.node a x b)) r]
              rfl
        · -- q = lk: found at left child, single zig
          refine ⟨[lk], ?_, by simp⟩
          rw [splay.eq_def]
          simp only [if_neg hqk, if_pos hqlt, if_neg hqlk, if_neg hlkq]
          show searchPath v (.node ll lk (.node lr k r))
              = [lk] ++ searchPath v (.node (.node ll lk lr) k r)
          rw [searchPath_node_gt hlkv, List.singleton_append]
          exact congrArg (List.cons lk) (searchPath_left_irrel hv lr (.node ll lk lr) r)

/-- Mirror of `newPath_prefix_left`: `v ≤ k ≤ q`. -/

theorem newPath_prefix_right (l r : BinaryTree) (k q v : Nat)
    (hR : ForallTree (fun x => k < x) r) (hq : k ≤ q) (hv : v ≤ k) :
    ∃ p, searchPath v (splay (.node l k r) q) = p ++ searchPath v (.node l k r)
      ∧ p.length ≤ 2 := by
  by_cases hqk : q = k
  · refine ⟨[], ?_, by simp⟩
    rw [splay.eq_def]
    simp only [if_pos hqk, List.nil_append]
  · have hklt : k < q := Nat.lt_of_le_of_ne hq (fun h => hqk h.symm)
    have hnqlt : ¬ q < k := by omega
    cases r with
    | empty =>
      refine ⟨[], ?_, by simp⟩
      rw [splay.eq_def]
      simp only [if_neg hqk, if_neg hnqlt, List.nil_append]
    | node rl rk rr =>
      rcases forallTree_node_iff.mp hR with ⟨hFrl, hrkk, hFrr⟩
      have hvrk : v < rk := Nat.lt_of_le_of_lt hv hrkk
      by_cases hqrk : q < rk
      · cases rl with
        | empty =>
          -- zag with empty grandchild
          refine ⟨[rk], ?_, by simp⟩
          rw [splay.eq_def]
          simp only [if_neg hqk, if_neg hnqlt, if_pos hqrk]
          show searchPath v (.node (.node l k .empty) rk rr)
              = [rk] ++ searchPath v (.node l k (.node .empty rk rr))
          rw [searchPath_node_lt hvrk, List.singleton_append]
          exact congrArg (List.cons rk) (searchPath_right_irrel hv l .empty (.node .empty rk rr))
        | node a x b =>
          -- zag-zig
          cases hS : splay (BinaryTree.node a x b) q with
          | empty => exact absurd hS (splay_ne_empty a b x q)
          | node A s B =>
            have hsk : k < s := by
              have hF := splay_forallTree_kd (fun z => k < z) (.node a x b) q hFrl
              rw [hS] at hF
              exact (forallTree_node_iff.mp hF).2.1
            have hvs : v < s := Nat.lt_of_le_of_lt hv hsk
            refine ⟨[s], ?_, by simp⟩
            rw [splay_zagzig_shape l (.node a x b) rr A B rk k q s hqk hklt hqrk
                  (fun h => nomatch h) hS,
                searchPath_node_lt hvs,
                searchPath_right_irrel hv l A (.node (.node a x b) rk rr)]
            rfl
      · by_cases hrkq : rk < q
        · cases rr with
          | empty =>
            -- zag with empty grandchild
            refine ⟨[rk], ?_, by simp⟩
            rw [splay.eq_def]
            simp only [if_neg hqk, if_neg hnqlt, if_neg hqrk, if_pos hrkq]
            show searchPath v (.node (.node l k rl) rk .empty)
                = [rk] ++ searchPath v (.node l k (.node rl rk .empty))
            rw [searchPath_node_lt hvrk, List.singleton_append]
            exact congrArg (List.cons rk) (searchPath_right_irrel hv l rl (.node rl rk .empty))
          | node a x b =>
            -- zag-zag
            cases hS : splay (BinaryTree.node a x b) q with
            | empty => exact absurd hS (splay_ne_empty a b x q)
            | node A s B =>
              have hsk : k < s := by
                have hF := splay_forallTree_kd (fun z => k < z) (.node a x b) q hFrr
                rw [hS] at hF
                exact (forallTree_node_iff.mp hF).2.1
              have hvs : v < s := Nat.lt_of_le_of_lt hv hsk
              refine ⟨[s, rk], ?_, by simp⟩
              rw [splay_zagzag_shape l rl (.node a x b) A B rk k q s hqk hklt hrkq
                    (fun h => nomatch h) hS,
                  searchPath_node_lt hvs, searchPath_node_lt hvrk,
                  searchPath_right_irrel hv l rl (.node rl rk (.node a x b))]
              rfl
        · -- q = rk: found at right child, single zag
          refine ⟨[rk], ?_, by simp⟩
          rw [splay.eq_def]
          simp only [if_neg hqk, if_neg hnqlt, if_neg hqrk, if_neg hrkq]
          show searchPath v (.node (.node l k rl) rk rr)
              = [rk] ++ searchPath v (.node l k (.node rl rk rr))
          rw [searchPath_node_lt hvrk, List.singleton_append]
          exact congrArg (List.cons rk) (searchPath_right_irrel hv l rl (.node rl rk rr))

/-! ## MAIN THEOREMS -/

/-- (R2) core, abstract touched-set form, min-dive / max-target direction.
`T'` is any set sandwiched between `T` and `T ∪ keys(searchPath q t)`. -/

theorem touchedCount_mixed_le_left (l r : BinaryTree) (k q v : Nat) (T T' : List Nat)
    (hL : ForallTree (fun x => x < k) l) (hR : ForallTree (fun x => k < x) r)
    (hq : q ≤ k) (hv : k ≤ v) (hroot : k ∈ T)
    (hTT' : ∀ z ∈ T, z ∈ T')
    (hT'T : ∀ z ∈ T', z ∈ T ∨ z ∈ searchPath q (.node l k r)) :
    touchedCount T' (searchPath v (splay (.node l k r) q))
      ≤ touchedCount T (searchPath v (.node l k r)) + 2 := by
  obtain ⟨p, hp, hplen⟩ := newPath_prefix_left l r k q v hL hq hv
  -- the OLD path of v: root k followed by a tail of keys > k
  obtain ⟨tail, hold, htailgt⟩ :
      ∃ tail, searchPath v (.node l k r) = k :: tail ∧ ∀ z ∈ tail, k < z := by
    rcases Nat.eq_or_lt_of_le hv with heq | hlt
    · exact ⟨[], searchPath_node_self heq.symm l r, by simp⟩
    · exact ⟨searchPath v r, searchPath_node_gt hlt l r,
        fun z hz => mem_searchPath_forall hR hz⟩
  -- the tail is disjoint from q's search path (keys ≤ k), so T'/T-indistinguishable
  have htail : ∀ z ∈ tail, (z ∈ T') ↔ (z ∈ T) := by
    intro z hz
    have hzk := htailgt z hz
    constructor
    · intro hzT'
      rcases hT'T z hzT' with h | h
      · exact h
      · have := searchPath_all_le_of_left hL hq z h
        omega
    · exact hTT' z
  have e1 : touchedCount T' (searchPath v (splay (.node l k r) q))
      = touchedCount T' p + touchedCount T' (k :: tail) := by
    rw [hp, hold, touchedCount_append]
  have e2 := touchedCount_cons_le T' k tail
  have e3 : touchedCount T' tail = touchedCount T tail := touchedCount_congr htail
  have e4 : touchedCount T' p ≤ 2 := le_trans (touchedCount_le_length T' p) hplen
  have e5 : touchedCount T (searchPath v (.node l k r)) = touchedCount T tail + 1 := by
    rw [hold, touchedCount_cons_mem hroot]
  omega

/-- (R2) core, abstract touched-set form, mirror direction (`v ≤ rootKey ≤ q`). -/

theorem touchedCount_mixed_le_right (l r : BinaryTree) (k q v : Nat) (T T' : List Nat)
    (hL : ForallTree (fun x => x < k) l) (hR : ForallTree (fun x => k < x) r)
    (hq : k ≤ q) (hv : v ≤ k) (hroot : k ∈ T)
    (hTT' : ∀ z ∈ T, z ∈ T')
    (hT'T : ∀ z ∈ T', z ∈ T ∨ z ∈ searchPath q (.node l k r)) :
    touchedCount T' (searchPath v (splay (.node l k r) q))
      ≤ touchedCount T (searchPath v (.node l k r)) + 2 := by
  obtain ⟨p, hp, hplen⟩ := newPath_prefix_right l r k q v hR hq hv
  obtain ⟨tail, hold, htaillt⟩ :
      ∃ tail, searchPath v (.node l k r) = k :: tail ∧ ∀ z ∈ tail, z < k := by
    rcases Nat.eq_or_lt_of_le hv with heq | hlt
    · exact ⟨[], searchPath_node_self heq l r, by simp⟩
    · exact ⟨searchPath v l, searchPath_node_lt hlt l r,
        fun z hz => mem_searchPath_forall (p := fun x => x < k) hL hz⟩
  have htail : ∀ z ∈ tail, (z ∈ T') ↔ (z ∈ T) := by
    intro z hz
    have hzk := htaillt z hz
    constructor
    · intro hzT'
      rcases hT'T z hzT' with h | h
      · exact h
      · have := searchPath_all_ge_of_right hR hq z h
        omega
    · exact hTT' z
  have e1 : touchedCount T' (searchPath v (splay (.node l k r) q))
      = touchedCount T' p + touchedCount T' (k :: tail) := by
    rw [hp, hold, touchedCount_append]
  have e2 := touchedCount_cons_le T' k tail
  have e3 : touchedCount T' tail = touchedCount T tail := touchedCount_congr htail
  have e4 : touchedCount T' p ≤ 2 := le_trans (touchedCount_le_length T' p) hplen
  have e5 : touchedCount T (searchPath v (.node l k r)) = touchedCount T tail + 1 := by
    rw [hold, touchedCount_cons_mem hroot]
  omega

/-- (R2) HEADLINE THEOREM — mixed-touched-set opposite-side deepening.

`t` a nonempty BST whose root key is already touched (`rootKey t ∈ T` — true from step 1
of the deque process on), `q` at-or-below the root and `v` at-or-beyond it (the
min-dive / max-target opposite-side shape) or the mirror.  Then v's search path in the
splayed tree, counted against the enlarged touched set `T ∪ keys(searchPath q t)`,
deepens by at most 2 over its old path counted against `T`.  `T` is otherwise ARBITRARY
(no path-closure needed).  The constant 2 is tight (zig-zig at the root). -/

theorem touchedCount_mixed_splay_le (t : BinaryTree) (q v : Nat) (T : List Nat)
    (hbst : IsBST t) (hne : t ≠ .empty) (hroot : rootKey t ∈ T)
    (hside : (q ≤ rootKey t ∧ rootKey t ≤ v) ∨ (v ≤ rootKey t ∧ rootKey t ≤ q)) :
    touchedCount (T ++ searchPath q t) (searchPath v (splay t q))
      ≤ touchedCount T (searchPath v t) + 2 := by
  cases t with
  | empty => exact absurd rfl hne
  | node l k r =>
    rcases isBST_node_iff.mp hbst with ⟨hL, hR, _, _⟩
    have hTT' : ∀ z ∈ T, z ∈ T ++ searchPath q (.node l k r) :=
      fun z hz => List.mem_append_left _ hz
    have hT'T : ∀ z ∈ T ++ searchPath q (.node l k r),
        z ∈ T ∨ z ∈ searchPath q (.node l k r) :=
      fun z hz => List.mem_append.mp hz
    rcases hside with ⟨hq, hv⟩ | ⟨hv, hq⟩
    · exact touchedCount_mixed_le_left l r k q v T _ hL hR hq hv hroot hTT' hT'T
    · exact touchedCount_mixed_le_right l r k q v T _ hL hR hq hv hroot hTT' hT'T

/-- Step-0 variant: with NOTHING touched yet (no `rootKey t ∈ T` hypothesis) the
deepening constant degrades from 2 to 3, and 3 is tight (zig-zig at the root, `T = ∅`). -/

theorem touchedCount_mixed_splay_le_step0 (t : BinaryTree) (q v : Nat) (T : List Nat)
    (hbst : IsBST t) (hne : t ≠ .empty)
    (hside : (q ≤ rootKey t ∧ rootKey t ≤ v) ∨ (v ≤ rootKey t ∧ rootKey t ≤ q)) :
    touchedCount (T ++ searchPath q t) (searchPath v (splay t q))
      ≤ touchedCount T (searchPath v t) + 3 := by
  cases t with
  | empty => exact absurd rfl hne
  | node l k r =>
    rcases isBST_node_iff.mp hbst with ⟨hL, hR, _, _⟩
    set T' := T ++ searchPath q (.node l k r) with hT'def
    have hTT' : ∀ z ∈ T, z ∈ T' := fun z hz => List.mem_append_left _ hz
    have hT'T : ∀ z ∈ T', z ∈ T ∨ z ∈ searchPath q (.node l k r) :=
      fun z hz => List.mem_append.mp hz
    rcases hside with ⟨hq, hv⟩ | ⟨hv, hq⟩
    · obtain ⟨p, hp, hplen⟩ := newPath_prefix_left l r k q v hL hq hv
      obtain ⟨tail, hold, htailgt⟩ :
          ∃ tail, searchPath v (.node l k r) = k :: tail ∧ ∀ z ∈ tail, k < z := by
        rcases Nat.eq_or_lt_of_le hv with heq | hlt
        · exact ⟨[], searchPath_node_self heq.symm l r, by simp⟩
        · exact ⟨searchPath v r, searchPath_node_gt hlt l r,
            fun z hz => mem_searchPath_forall hR hz⟩
      have htail : ∀ z ∈ tail, (z ∈ T') ↔ (z ∈ T) := by
        intro z hz
        have hzk := htailgt z hz
        constructor
        · intro hzT'
          rcases hT'T z hzT' with h | h
          · exact h
          · have := searchPath_all_le_of_left hL hq z h
            omega
        · exact hTT' z
      have e1 : touchedCount T' (searchPath v (splay (.node l k r) q))
          = touchedCount T' p + touchedCount T' (k :: tail) := by
        rw [hp, hold, touchedCount_append]
      have e2 := touchedCount_cons_le T' k tail
      have e3 : touchedCount T' tail = touchedCount T tail := touchedCount_congr htail
      have e4 : touchedCount T' p ≤ 2 := le_trans (touchedCount_le_length T' p) hplen
      have e5 : touchedCount T tail ≤ touchedCount T (searchPath v (.node l k r)) := by
        rw [hold]
        exact touchedCount_le_cons T k tail
      omega
    · obtain ⟨p, hp, hplen⟩ := newPath_prefix_right l r k q v hR hq hv
      obtain ⟨tail, hold, htaillt⟩ :
          ∃ tail, searchPath v (.node l k r) = k :: tail ∧ ∀ z ∈ tail, z < k := by
        rcases Nat.eq_or_lt_of_le hv with heq | hlt
        · exact ⟨[], searchPath_node_self heq l r, by simp⟩
        · exact ⟨searchPath v l, searchPath_node_lt hlt l r,
            fun z hz => mem_searchPath_forall (p := fun x => x < k) hL hz⟩
      have htail : ∀ z ∈ tail, (z ∈ T') ↔ (z ∈ T) := by
        intro z hz
        have hzk := htaillt z hz
        constructor
        · intro hzT'
          rcases hT'T z hzT' with h | h
          · exact h
          · have := searchPath_all_ge_of_right hR hq z h
            omega
        · exact hTT' z
      have e1 : touchedCount T' (searchPath v (splay (.node l k r) q))
          = touchedCount T' p + touchedCount T' (k :: tail) := by
        rw [hp, hold, touchedCount_append]
      have e2 := touchedCount_cons_le T' k tail
      have e3 : touchedCount T' tail = touchedCount T tail := touchedCount_congr htail
      have e4 : touchedCount T' p ≤ 2 := le_trans (touchedCount_le_length T' p) hplen
      have e5 : touchedCount T tail ≤ touchedCount T (searchPath v (.node l k r)) := by
        rw [hold]
        exact touchedCount_le_cons T k tail
      omega

/-! ## Tightness witnesses (from the empirical pinning harness)

Zig-zig at the root: `t = node (node (node ∅ 2 ∅) 3 ∅) 4 ∅`, `q = 0`, `v = 4 = rootKey`,
`T = [4]`: new v-path `[2,3,4]` is fully `T'`-touched (3) vs old `[4]` `T`-count 1 → excess
exactly 2.  Same instance with `T = []`: 3 vs 0 → excess exactly 3 for the step-0 form. -/

example :
    touchedCount ([4] ++ searchPath 0 (.node (.node (.node .empty 2 .empty) 3 .empty) 4 .empty))
        (searchPath 4 (splay (.node (.node (.node .empty 2 .empty) 3 .empty) 4 .empty) 0))
      = touchedCount [4] (searchPath 4 (.node (.node (.node .empty 2 .empty) 3 .empty) 4 .empty))
        + 2 := by decide

example :
    touchedCount ([] ++ searchPath 0 (.node (.node (.node .empty 2 .empty) 3 .empty) 4 .empty))
        (searchPath 4 (splay (.node (.node (.node .empty 2 .empty) 3 .empty) 4 .empty) 0))
      = touchedCount [] (searchPath 4 (.node (.node (.node .empty 2 .empty) 3 .empty) 4 .empty))
        + 3 := by decide


-- ===== R1-core: generalized halving =====
theorem sp_len (y : Nat) (t : BinaryTree) : (searchPath y t).length = keyDepth y t := rfl

/-- Fuel-indexed version of `keyDepth_splay_le_shared`, strong induction on `num_nodes`. -/

theorem keyDepth_splay_le_shared_aux :
    ∀ (n : Nat) (t : BinaryTree), t.num_nodes ≤ n → ∀ (q y : Nat),
      IsBST t →
      2 * keyDepth y (splay t q) ≤ keyDepth y t + (divergeSuffix y q t).length + 5 := by
  intro n
  induction n with
  | zero =>
    intro t ht q y _
    cases t with
    | empty =>
      have h0 : splay BinaryTree.empty q = BinaryTree.empty := rfl
      rw [h0]
      simp only [keyDepth_empty, divergeSuffix_empty, List.length_nil]
      omega
    | node l k r =>
      exfalso
      have hnn : (BinaryTree.node l k r).num_nodes = 1 + l.num_nodes + r.num_nodes := rfl
      omega
  | succ n ih =>
    intro t ht q y hbst
    cases t with
    | empty =>
      have h0 : splay BinaryTree.empty q = BinaryTree.empty := rfl
      rw [h0]
      simp only [keyDepth_empty, divergeSuffix_empty, List.length_nil]
      omega
    | node l k r =>
      rcases isBST_node_iff.mp hbst with ⟨hfl, hfr, hbl, hbr⟩
      by_cases hqk : q = k
      · -- (1) q found at the root: splay returns t
        rw [splay.eq_def]
        simp only [if_pos hqk]
        by_cases hyk : y = k
        · rw [ds_self hyk]
          have h1 : keyDepth y (BinaryTree.node l k r) = 1 := keyDepth_node_self hyk _ _
          simp only [List.length_nil]
          omega
        · by_cases hylt : y < k
          · rw [ds_qroot_lt hqk hylt, sp_len]
            have h1 : keyDepth y (BinaryTree.node l k r) = keyDepth y l + 1 :=
              keyDepth_node_lt hylt _ _
            omega
          · have hkly : k < y := by omega
            rw [ds_qroot_gt hqk hkly, sp_len]
            have h1 : keyDepth y (BinaryTree.node l k r) = keyDepth y r + 1 :=
              keyDepth_node_gt hkly _ _
            omega
      · by_cases hqlt : q < k
        · cases l with
          | empty =>
            -- (2) q not found, root unchanged
            rw [splay.eq_def]
            simp only [if_neg hqk, if_pos hqlt]
            by_cases hyk : y = k
            · rw [ds_self hyk]
              have h1 : keyDepth y (BinaryTree.node BinaryTree.empty k r) = 1 :=
                keyDepth_node_self hyk _ _
              simp only [List.length_nil]
              omega
            · by_cases hylt : y < k
              · rw [ds_both_lt hylt hqlt, divergeSuffix_empty]
                have h1 : keyDepth y (BinaryTree.node BinaryTree.empty k r)
                    = keyDepth y BinaryTree.empty + 1 := keyDepth_node_lt hylt _ _
                have h2 : keyDepth y BinaryTree.empty = 0 := rfl
                simp only [List.length_nil]
                omega
              · have hkly : k < y := by omega
                rw [ds_div_gt hkly hqlt, sp_len]
                have h1 : keyDepth y (BinaryTree.node BinaryTree.empty k r)
                    = keyDepth y r + 1 := keyDepth_node_gt hkly _ _
                omega
          | node ll lk lr =>
            rcases forallTree_node_iff.mp hfl with ⟨hfll, hlkk, hflr⟩
            rcases isBST_node_iff.mp hbl with ⟨hll_lt, hlr_gt, hbll, hblr⟩
            by_cases hqlk : q < lk
            · cases ll with
              | empty =>
                -- (3) ZIG with empty grandchild: result = node empty lk (node lr k r)
                rw [splay.eq_def]
                simp only [if_neg hqk, if_pos hqlt, if_pos hqlk]
                show 2 * keyDepth y (BinaryTree.node BinaryTree.empty lk (BinaryTree.node lr k r))
                    ≤ keyDepth y (BinaryTree.node (BinaryTree.node BinaryTree.empty lk lr) k r)
                      + (divergeSuffix y q
                          (BinaryTree.node (BinaryTree.node BinaryTree.empty lk lr) k r)).length
                      + 5
                by_cases hyk : y = k
                · rw [ds_self hyk]
                  have h1 : keyDepth y
                      (BinaryTree.node BinaryTree.empty lk (BinaryTree.node lr k r))
                      = keyDepth y (BinaryTree.node lr k r) + 1 :=
                    keyDepth_node_gt (by omega) _ _
                  have h2 : keyDepth y (BinaryTree.node lr k r) = 1 := keyDepth_node_self hyk _ _
                  have h3 : keyDepth y
                      (BinaryTree.node (BinaryTree.node BinaryTree.empty lk lr) k r) = 1 :=
                    keyDepth_node_self hyk _ _
                  simp only [List.length_nil]
                  omega
                · by_cases hylt : y < k
                  · by_cases hylk : y = lk
                    · rw [ds_both_lt hylt hqlt, ds_self hylk]
                      have h1 : keyDepth y
                          (BinaryTree.node BinaryTree.empty lk (BinaryTree.node lr k r)) = 1 :=
                        keyDepth_node_self hylk _ _
                      simp only [List.length_nil]
                      omega
                    · by_cases hylk2 : y < lk
                      · rw [ds_both_lt hylt hqlt, ds_both_lt hylk2 hqlk, divergeSuffix_empty]
                        have h1 : keyDepth y
                            (BinaryTree.node BinaryTree.empty lk (BinaryTree.node lr k r))
                            = keyDepth y BinaryTree.empty + 1 := keyDepth_node_lt hylk2 _ _
                        have h2 : keyDepth y BinaryTree.empty = 0 := rfl
                        simp only [List.length_nil]
                        omega
                      · have hlky : lk < y := by omega
                        rw [ds_both_lt hylt hqlt, ds_div_gt hlky hqlk, sp_len]
                        have h1 : keyDepth y
                            (BinaryTree.node BinaryTree.empty lk (BinaryTree.node lr k r))
                            = keyDepth y (BinaryTree.node lr k r) + 1 :=
                          keyDepth_node_gt hlky _ _
                        have h2 : keyDepth y (BinaryTree.node lr k r) = keyDepth y lr + 1 :=
                          keyDepth_node_lt hylt _ _
                        have h3 : keyDepth y
                            (BinaryTree.node (BinaryTree.node BinaryTree.empty lk lr) k r)
                            = keyDepth y (BinaryTree.node BinaryTree.empty lk lr) + 1 :=
                          keyDepth_node_lt hylt _ _
                        have h4 : keyDepth y (BinaryTree.node BinaryTree.empty lk lr)
                            = keyDepth y lr + 1 := keyDepth_node_gt hlky _ _
                        omega
                  · have hkly : k < y := by omega
                    rw [ds_div_gt hkly hqlt, sp_len]
                    have h1 : keyDepth y
                        (BinaryTree.node BinaryTree.empty lk (BinaryTree.node lr k r))
                        = keyDepth y (BinaryTree.node lr k r) + 1 :=
                      keyDepth_node_gt (by omega) _ _
                    have h2 : keyDepth y (BinaryTree.node lr k r) = keyDepth y r + 1 :=
                      keyDepth_node_gt hkly _ _
                    have h3 : keyDepth y
                        (BinaryTree.node (BinaryTree.node BinaryTree.empty lk lr) k r)
                        = keyDepth y r + 1 := keyDepth_node_gt hkly _ _
                    omega
              | node a x b =>
                -- (4) ZIG-ZIG
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
                  by_cases hyk : y = k
                  · -- y = k : depth 1 → 3 (tight, 2*3 = 1 + 0 + 5)
                    rw [ds_self hyk]
                    have h1 : keyDepth y
                        (BinaryTree.node A s (BinaryTree.node B lk (BinaryTree.node lr k r)))
                        = keyDepth y (BinaryTree.node B lk (BinaryTree.node lr k r)) + 1 :=
                      keyDepth_node_gt (by omega) _ _
                    have h2 : keyDepth y (BinaryTree.node B lk (BinaryTree.node lr k r))
                        = keyDepth y (BinaryTree.node lr k r) + 1 :=
                      keyDepth_node_gt (by omega) _ _
                    have h3 : keyDepth y (BinaryTree.node lr k r) = 1 :=
                      keyDepth_node_self hyk _ _
                    have h4 : keyDepth y (BinaryTree.node
                        (BinaryTree.node (BinaryTree.node a x b) lk lr) k r) = 1 :=
                      keyDepth_node_self hyk _ _
                    simp only [List.length_nil]
                    omega
                  · by_cases hylt : y < k
                    · by_cases hylk : y = lk
                      · rw [ds_both_lt hylt hqlt, ds_self hylk]
                        have h1 : keyDepth y
                            (BinaryTree.node A s (BinaryTree.node B lk (BinaryTree.node lr k r)))
                            = keyDepth y (BinaryTree.node B lk (BinaryTree.node lr k r)) + 1 :=
                          keyDepth_node_gt (by omega) _ _
                        have h2 : keyDepth y (BinaryTree.node B lk (BinaryTree.node lr k r)) = 1 :=
                          keyDepth_node_self hylk _ _
                        simp only [List.length_nil]
                        omega
                      · by_cases hylk2 : y < lk
                        · -- y in the recursion zone: IH on the grandchild
                          rw [ds_both_lt hylt hqlt, ds_both_lt hylk2 hqlk]
                          have hIH := ih _ hsz q y hbll
                          rw [hs] at hIH
                          have h3 : keyDepth y (BinaryTree.node
                              (BinaryTree.node (BinaryTree.node a x b) lk lr) k r)
                              = keyDepth y (BinaryTree.node (BinaryTree.node a x b) lk lr) + 1 :=
                            keyDepth_node_lt hylt _ _
                          have h4 : keyDepth y (BinaryTree.node (BinaryTree.node a x b) lk lr)
                              = keyDepth y (BinaryTree.node a x b) + 1 :=
                            keyDepth_node_lt hylk2 _ _
                          rcases Nat.lt_trichotomy y s with hys | hys | hys
                          · have h1 : keyDepth y (BinaryTree.node A s
                                (BinaryTree.node B lk (BinaryTree.node lr k r)))
                                = keyDepth y A + 1 := keyDepth_node_lt hys _ _
                            have h2 : keyDepth y (BinaryTree.node A s B) = keyDepth y A + 1 :=
                              keyDepth_node_lt hys _ _
                            omega
                          · have h1 : keyDepth y (BinaryTree.node A s
                                (BinaryTree.node B lk (BinaryTree.node lr k r)))
                                = 1 := keyDepth_node_self hys _ _
                            omega
                          · have h1 : keyDepth y (BinaryTree.node A s
                                (BinaryTree.node B lk (BinaryTree.node lr k r)))
                                = keyDepth y (BinaryTree.node B lk (BinaryTree.node lr k r)) + 1 :=
                              keyDepth_node_gt hys _ _
                            have h2 : keyDepth y (BinaryTree.node B lk (BinaryTree.node lr k r))
                                = keyDepth y B + 1 := keyDepth_node_lt hylk2 _ _
                            have h5 : keyDepth y (BinaryTree.node A s B) = keyDepth y B + 1 :=
                              keyDepth_node_gt hys _ _
                            omega
                        · -- lk < y < k : y lands in the cargo subtree lr
                          have hlky : lk < y := by omega
                          rw [ds_both_lt hylt hqlt, ds_div_gt hlky hqlk, sp_len]
                          have h1 : keyDepth y (BinaryTree.node A s
                              (BinaryTree.node B lk (BinaryTree.node lr k r)))
                              = keyDepth y (BinaryTree.node B lk (BinaryTree.node lr k r)) + 1 :=
                            keyDepth_node_gt (by omega) _ _
                          have h2 : keyDepth y (BinaryTree.node B lk (BinaryTree.node lr k r))
                              = keyDepth y (BinaryTree.node lr k r) + 1 :=
                            keyDepth_node_gt hlky _ _
                          have h3 : keyDepth y (BinaryTree.node lr k r)
                              = keyDepth y lr + 1 := keyDepth_node_lt hylt _ _
                          have h4 : keyDepth y (BinaryTree.node
                              (BinaryTree.node (BinaryTree.node a x b) lk lr) k r)
                              = keyDepth y (BinaryTree.node (BinaryTree.node a x b) lk lr) + 1 :=
                            keyDepth_node_lt hylt _ _
                          have h5 : keyDepth y (BinaryTree.node (BinaryTree.node a x b) lk lr)
                              = keyDepth y lr + 1 := keyDepth_node_gt hlky _ _
                          omega
                    · -- k < y : y lands in the cargo subtree r (tight: 2d+6 ≤ 2d+6)
                      have hkly : k < y := by omega
                      rw [ds_div_gt hkly hqlt, sp_len]
                      have h1 : keyDepth y (BinaryTree.node A s
                          (BinaryTree.node B lk (BinaryTree.node lr k r)))
                          = keyDepth y (BinaryTree.node B lk (BinaryTree.node lr k r)) + 1 :=
                        keyDepth_node_gt (by omega) _ _
                      have h2 : keyDepth y (BinaryTree.node B lk (BinaryTree.node lr k r))
                          = keyDepth y (BinaryTree.node lr k r) + 1 :=
                        keyDepth_node_gt (by omega) _ _
                      have h3 : keyDepth y (BinaryTree.node lr k r)
                          = keyDepth y r + 1 := keyDepth_node_gt hkly _ _
                      have h4 : keyDepth y (BinaryTree.node
                          (BinaryTree.node (BinaryTree.node a x b) lk lr) k r)
                          = keyDepth y r + 1 := keyDepth_node_gt hkly _ _
                      omega
            · by_cases hlkq : lk < q
              · cases lr with
                | empty =>
                  -- (5) ZIG with empty grandchild: result = node ll lk (node empty k r)
                  rw [splay.eq_def]
                  simp only [if_neg hqk, if_pos hqlt, if_neg hqlk, if_pos hlkq]
                  show 2 * keyDepth y (BinaryTree.node ll lk (BinaryTree.node BinaryTree.empty k r))
                      ≤ keyDepth y (BinaryTree.node (BinaryTree.node ll lk BinaryTree.empty) k r)
                        + (divergeSuffix y q
                            (BinaryTree.node (BinaryTree.node ll lk BinaryTree.empty) k r)).length
                        + 5
                  by_cases hyk : y = k
                  · rw [ds_self hyk]
                    have h1 : keyDepth y
                        (BinaryTree.node ll lk (BinaryTree.node BinaryTree.empty k r))
                        = keyDepth y (BinaryTree.node BinaryTree.empty k r) + 1 :=
                      keyDepth_node_gt (by omega) _ _
                    have h2 : keyDepth y (BinaryTree.node BinaryTree.empty k r) = 1 :=
                      keyDepth_node_self hyk _ _
                    have h3 : keyDepth y
                        (BinaryTree.node (BinaryTree.node ll lk BinaryTree.empty) k r) = 1 :=
                      keyDepth_node_self hyk _ _
                    simp only [List.length_nil]
                    omega
                  · by_cases hylt : y < k
                    · by_cases hylk : y = lk
                      · rw [ds_both_lt hylt hqlt, ds_self hylk]
                        have h1 : keyDepth y
                            (BinaryTree.node ll lk (BinaryTree.node BinaryTree.empty k r)) = 1 :=
                          keyDepth_node_self hylk _ _
                        simp only [List.length_nil]
                        omega
                      · by_cases hylk2 : y < lk
                        · rw [ds_both_lt hylt hqlt, ds_div_lt hylk2 hlkq, sp_len]
                          have h1 : keyDepth y
                              (BinaryTree.node ll lk (BinaryTree.node BinaryTree.empty k r))
                              = keyDepth y ll + 1 := keyDepth_node_lt hylk2 _ _
                          have h2 : keyDepth y
                              (BinaryTree.node (BinaryTree.node ll lk BinaryTree.empty) k r)
                              = keyDepth y (BinaryTree.node ll lk BinaryTree.empty) + 1 :=
                            keyDepth_node_lt hylt _ _
                          have h3 : keyDepth y (BinaryTree.node ll lk BinaryTree.empty)
                              = keyDepth y ll + 1 := keyDepth_node_lt hylk2 _ _
                          omega
                        · have hlky : lk < y := by omega
                          rw [ds_both_lt hylt hqlt, ds_both_gt hlky hlkq, divergeSuffix_empty]
                          have h1 : keyDepth y
                              (BinaryTree.node ll lk (BinaryTree.node BinaryTree.empty k r))
                              = keyDepth y (BinaryTree.node BinaryTree.empty k r) + 1 :=
                            keyDepth_node_gt hlky _ _
                          have h2 : keyDepth y (BinaryTree.node BinaryTree.empty k r)
                              = keyDepth y BinaryTree.empty + 1 := keyDepth_node_lt hylt _ _
                          have h3 : keyDepth y BinaryTree.empty = 0 := rfl
                          simp only [List.length_nil]
                          omega
                    · have hkly : k < y := by omega
                      rw [ds_div_gt hkly hqlt, sp_len]
                      have h1 : keyDepth y
                          (BinaryTree.node ll lk (BinaryTree.node BinaryTree.empty k r))
                          = keyDepth y (BinaryTree.node BinaryTree.empty k r) + 1 :=
                        keyDepth_node_gt (by omega) _ _
                      have h2 : keyDepth y (BinaryTree.node BinaryTree.empty k r)
                          = keyDepth y r + 1 := keyDepth_node_gt hkly _ _
                      have h3 : keyDepth y
                          (BinaryTree.node (BinaryTree.node ll lk BinaryTree.empty) k r)
                          = keyDepth y r + 1 := keyDepth_node_gt hkly _ _
                      omega
                | node a x b =>
                  -- (6) ZIG-ZAG
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
                    by_cases hyk : y = k
                    · rw [ds_self hyk]
                      have h1 : keyDepth y
                          (BinaryTree.node (BinaryTree.node ll lk A) s (BinaryTree.node B k r))
                          = keyDepth y (BinaryTree.node B k r) + 1 :=
                        keyDepth_node_gt (by omega) _ _
                      have h2 : keyDepth y (BinaryTree.node B k r) = 1 :=
                        keyDepth_node_self hyk _ _
                      have h3 : keyDepth y (BinaryTree.node
                          (BinaryTree.node ll lk (BinaryTree.node a x b)) k r) = 1 :=
                        keyDepth_node_self hyk _ _
                      simp only [List.length_nil]
                      omega
                    · by_cases hylt : y < k
                      · by_cases hylk : y = lk
                        · rw [ds_both_lt hylt hqlt, ds_self hylk]
                          have h1 : keyDepth y
                              (BinaryTree.node (BinaryTree.node ll lk A) s (BinaryTree.node B k r))
                              = keyDepth y (BinaryTree.node ll lk A) + 1 :=
                            keyDepth_node_lt (by omega) _ _
                          have h2 : keyDepth y (BinaryTree.node ll lk A) = 1 :=
                            keyDepth_node_self hylk _ _
                          simp only [List.length_nil]
                          omega
                        · by_cases hylk2 : y < lk
                          · -- y < lk : y lands in the cargo subtree ll
                            rw [ds_both_lt hylt hqlt, ds_div_lt hylk2 hlkq, sp_len]
                            have h1 : keyDepth y (BinaryTree.node
                                (BinaryTree.node ll lk A) s (BinaryTree.node B k r))
                                = keyDepth y (BinaryTree.node ll lk A) + 1 :=
                              keyDepth_node_lt (by omega) _ _
                            have h2 : keyDepth y (BinaryTree.node ll lk A)
                                = keyDepth y ll + 1 := keyDepth_node_lt hylk2 _ _
                            have h3 : keyDepth y (BinaryTree.node
                                (BinaryTree.node ll lk (BinaryTree.node a x b)) k r)
                                = keyDepth y (BinaryTree.node ll lk (BinaryTree.node a x b)) + 1 :=
                              keyDepth_node_lt hylt _ _
                            have h4 : keyDepth y (BinaryTree.node ll lk (BinaryTree.node a x b))
                                = keyDepth y ll + 1 := keyDepth_node_lt hylk2 _ _
                            omega
                          · -- lk < y < k : y in the recursion zone
                            have hlky : lk < y := by omega
                            rw [ds_both_lt hylt hqlt, ds_both_gt hlky hlkq]
                            have hIH := ih _ hsz q y hblr
                            rw [hs] at hIH
                            have h3 : keyDepth y (BinaryTree.node
                                (BinaryTree.node ll lk (BinaryTree.node a x b)) k r)
                                = keyDepth y (BinaryTree.node ll lk (BinaryTree.node a x b)) + 1 :=
                              keyDepth_node_lt hylt _ _
                            have h4 : keyDepth y (BinaryTree.node ll lk (BinaryTree.node a x b))
                                = keyDepth y (BinaryTree.node a x b) + 1 :=
                              keyDepth_node_gt hlky _ _
                            rcases Nat.lt_trichotomy y s with hys | hys | hys
                            · have h1 : keyDepth y (BinaryTree.node
                                  (BinaryTree.node ll lk A) s (BinaryTree.node B k r))
                                  = keyDepth y (BinaryTree.node ll lk A) + 1 :=
                                keyDepth_node_lt hys _ _
                              have h2 : keyDepth y (BinaryTree.node ll lk A)
                                  = keyDepth y A + 1 := keyDepth_node_gt hlky _ _
                              have h5 : keyDepth y (BinaryTree.node A s B) = keyDepth y A + 1 :=
                                keyDepth_node_lt hys _ _
                              omega
                            · have h1 : keyDepth y (BinaryTree.node
                                  (BinaryTree.node ll lk A) s (BinaryTree.node B k r))
                                  = 1 := keyDepth_node_self hys _ _
                              omega
                            · have h1 : keyDepth y (BinaryTree.node
                                  (BinaryTree.node ll lk A) s (BinaryTree.node B k r))
                                  = keyDepth y (BinaryTree.node B k r) + 1 :=
                                keyDepth_node_gt hys _ _
                              have h2 : keyDepth y (BinaryTree.node B k r)
                                  = keyDepth y B + 1 := keyDepth_node_lt hylt _ _
                              have h5 : keyDepth y (BinaryTree.node A s B) = keyDepth y B + 1 :=
                                keyDepth_node_gt hys _ _
                              omega
                      · -- k < y : y lands in the cargo subtree r
                        have hkly : k < y := by omega
                        rw [ds_div_gt hkly hqlt, sp_len]
                        have h1 : keyDepth y (BinaryTree.node
                            (BinaryTree.node ll lk A) s (BinaryTree.node B k r))
                            = keyDepth y (BinaryTree.node B k r) + 1 :=
                          keyDepth_node_gt (by omega) _ _
                        have h2 : keyDepth y (BinaryTree.node B k r)
                            = keyDepth y r + 1 := keyDepth_node_gt hkly _ _
                        have h3 : keyDepth y (BinaryTree.node
                            (BinaryTree.node ll lk (BinaryTree.node a x b)) k r)
                            = keyDepth y r + 1 := keyDepth_node_gt hkly _ _
                        omega
              · -- (7) q found at the left child (q = lk): single ZIG
                have hqlk_eq : q = lk := by omega
                rw [splay.eq_def]
                simp only [if_neg hqk, if_pos hqlt, if_neg hqlk, if_neg hlkq]
                show 2 * keyDepth y (BinaryTree.node ll lk (BinaryTree.node lr k r))
                    ≤ keyDepth y (BinaryTree.node (BinaryTree.node ll lk lr) k r)
                      + (divergeSuffix y q
                          (BinaryTree.node (BinaryTree.node ll lk lr) k r)).length + 5
                by_cases hyk : y = k
                · rw [ds_self hyk]
                  have h1 : keyDepth y (BinaryTree.node ll lk (BinaryTree.node lr k r))
                      = keyDepth y (BinaryTree.node lr k r) + 1 :=
                    keyDepth_node_gt (by omega) _ _
                  have h2 : keyDepth y (BinaryTree.node lr k r) = 1 := keyDepth_node_self hyk _ _
                  have h3 : keyDepth y (BinaryTree.node (BinaryTree.node ll lk lr) k r) = 1 :=
                    keyDepth_node_self hyk _ _
                  simp only [List.length_nil]
                  omega
                · by_cases hylt : y < k
                  · by_cases hylk : y = lk
                    · rw [ds_both_lt hylt hqlt, ds_self hylk]
                      have h1 : keyDepth y (BinaryTree.node ll lk (BinaryTree.node lr k r)) = 1 :=
                        keyDepth_node_self hylk _ _
                      simp only [List.length_nil]
                      omega
                    · by_cases hylk2 : y < lk
                      · rw [ds_both_lt hylt hqlt, ds_qroot_lt hqlk_eq hylk2, sp_len]
                        have h1 : keyDepth y (BinaryTree.node ll lk (BinaryTree.node lr k r))
                            = keyDepth y ll + 1 := keyDepth_node_lt hylk2 _ _
                        have h2 : keyDepth y (BinaryTree.node (BinaryTree.node ll lk lr) k r)
                            = keyDepth y (BinaryTree.node ll lk lr) + 1 :=
                          keyDepth_node_lt hylt _ _
                        have h3 : keyDepth y (BinaryTree.node ll lk lr)
                            = keyDepth y ll + 1 := keyDepth_node_lt hylk2 _ _
                        omega
                      · have hlky : lk < y := by omega
                        rw [ds_both_lt hylt hqlt, ds_qroot_gt hqlk_eq hlky, sp_len]
                        have h1 : keyDepth y (BinaryTree.node ll lk (BinaryTree.node lr k r))
                            = keyDepth y (BinaryTree.node lr k r) + 1 :=
                          keyDepth_node_gt hlky _ _
                        have h2 : keyDepth y (BinaryTree.node lr k r)
                            = keyDepth y lr + 1 := keyDepth_node_lt hylt _ _
                        have h3 : keyDepth y (BinaryTree.node (BinaryTree.node ll lk lr) k r)
                            = keyDepth y (BinaryTree.node ll lk lr) + 1 :=
                          keyDepth_node_lt hylt _ _
                        have h4 : keyDepth y (BinaryTree.node ll lk lr)
                            = keyDepth y lr + 1 := keyDepth_node_gt hlky _ _
                        omega
                  · have hkly : k < y := by omega
                    rw [ds_div_gt hkly hqlt, sp_len]
                    have h1 : keyDepth y (BinaryTree.node ll lk (BinaryTree.node lr k r))
                        = keyDepth y (BinaryTree.node lr k r) + 1 :=
                      keyDepth_node_gt (by omega) _ _
                    have h2 : keyDepth y (BinaryTree.node lr k r)
                        = keyDepth y r + 1 := keyDepth_node_gt hkly _ _
                    have h3 : keyDepth y (BinaryTree.node (BinaryTree.node ll lk lr) k r)
                        = keyDepth y r + 1 := keyDepth_node_gt hkly _ _
                    omega
        · -- k < q : symmetric (zag) side
          have hklt : k < q := by omega
          cases r with
          | empty =>
            -- (8) q not found, root unchanged
            rw [splay.eq_def]
            simp only [if_neg hqk, if_neg hqlt]
            by_cases hyk : y = k
            · rw [ds_self hyk]
              have h1 : keyDepth y (BinaryTree.node l k BinaryTree.empty) = 1 :=
                keyDepth_node_self hyk _ _
              simp only [List.length_nil]
              omega
            · by_cases hylt : y < k
              · rw [ds_div_lt hylt hklt, sp_len]
                have h1 : keyDepth y (BinaryTree.node l k BinaryTree.empty)
                    = keyDepth y l + 1 := keyDepth_node_lt hylt _ _
                omega
              · have hkly : k < y := by omega
                rw [ds_both_gt hkly hklt, divergeSuffix_empty]
                have h1 : keyDepth y (BinaryTree.node l k BinaryTree.empty)
                    = keyDepth y BinaryTree.empty + 1 := keyDepth_node_gt hkly _ _
                have h2 : keyDepth y BinaryTree.empty = 0 := rfl
                simp only [List.length_nil]
                omega
          | node rl rk rr =>
            rcases forallTree_node_iff.mp hfr with ⟨hfrl, hkrk, hfrr⟩
            rcases isBST_node_iff.mp hbr with ⟨hrl_lt, hrr_gt, hbrl, hbrr⟩
            by_cases hqrk : q < rk
            · cases rl with
              | empty =>
                -- (9) ZAG with empty grandchild: result = node (node l k empty) rk rr
                rw [splay.eq_def]
                simp only [if_neg hqk, if_neg hqlt, if_pos hqrk]
                show 2 * keyDepth y (BinaryTree.node (BinaryTree.node l k BinaryTree.empty) rk rr)
                    ≤ keyDepth y (BinaryTree.node l k (BinaryTree.node BinaryTree.empty rk rr))
                      + (divergeSuffix y q
                          (BinaryTree.node l k (BinaryTree.node BinaryTree.empty rk rr))).length
                      + 5
                by_cases hyk : y = k
                · rw [ds_self hyk]
                  have h1 : keyDepth y
                      (BinaryTree.node (BinaryTree.node l k BinaryTree.empty) rk rr)
                      = keyDepth y (BinaryTree.node l k BinaryTree.empty) + 1 :=
                    keyDepth_node_lt (by omega) _ _
                  have h2 : keyDepth y (BinaryTree.node l k BinaryTree.empty) = 1 :=
                    keyDepth_node_self hyk _ _
                  have h3 : keyDepth y
                      (BinaryTree.node l k (BinaryTree.node BinaryTree.empty rk rr)) = 1 :=
                    keyDepth_node_self hyk _ _
                  simp only [List.length_nil]
                  omega
                · by_cases hylt : y < k
                  · rw [ds_div_lt hylt hklt, sp_len]
                    have h1 : keyDepth y
                        (BinaryTree.node (BinaryTree.node l k BinaryTree.empty) rk rr)
                        = keyDepth y (BinaryTree.node l k BinaryTree.empty) + 1 :=
                      keyDepth_node_lt (by omega) _ _
                    have h2 : keyDepth y (BinaryTree.node l k BinaryTree.empty)
                        = keyDepth y l + 1 := keyDepth_node_lt hylt _ _
                    have h3 : keyDepth y
                        (BinaryTree.node l k (BinaryTree.node BinaryTree.empty rk rr))
                        = keyDepth y l + 1 := keyDepth_node_lt hylt _ _
                    omega
                  · have hkly : k < y := by omega
                    by_cases hyrk : y = rk
                    · rw [ds_both_gt hkly hklt, ds_self hyrk]
                      have h1 : keyDepth y
                          (BinaryTree.node (BinaryTree.node l k BinaryTree.empty) rk rr) = 1 :=
                        keyDepth_node_self hyrk _ _
                      simp only [List.length_nil]
                      omega
                    · by_cases hyrk2 : y < rk
                      · rw [ds_both_gt hkly hklt, ds_both_lt hyrk2 hqrk, divergeSuffix_empty]
                        have h1 : keyDepth y
                            (BinaryTree.node (BinaryTree.node l k BinaryTree.empty) rk rr)
                            = keyDepth y (BinaryTree.node l k BinaryTree.empty) + 1 :=
                          keyDepth_node_lt hyrk2 _ _
                        have h2 : keyDepth y (BinaryTree.node l k BinaryTree.empty)
                            = keyDepth y BinaryTree.empty + 1 := keyDepth_node_gt hkly _ _
                        have h3 : keyDepth y BinaryTree.empty = 0 := rfl
                        simp only [List.length_nil]
                        omega
                      · have hrky : rk < y := by omega
                        rw [ds_both_gt hkly hklt, ds_div_gt hrky hqrk, sp_len]
                        have h1 : keyDepth y
                            (BinaryTree.node (BinaryTree.node l k BinaryTree.empty) rk rr)
                            = keyDepth y rr + 1 := keyDepth_node_gt hrky _ _
                        have h2 : keyDepth y
                            (BinaryTree.node l k (BinaryTree.node BinaryTree.empty rk rr))
                            = keyDepth y (BinaryTree.node BinaryTree.empty rk rr) + 1 :=
                          keyDepth_node_gt hkly _ _
                        have h3 : keyDepth y (BinaryTree.node BinaryTree.empty rk rr)
                            = keyDepth y rr + 1 := keyDepth_node_gt hrky _ _
                        omega
              | node a x b =>
                -- (10) ZAG-ZIG
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
                  by_cases hyk : y = k
                  · rw [ds_self hyk]
                    have h1 : keyDepth y
                        (BinaryTree.node (BinaryTree.node l k A) s (BinaryTree.node B rk rr))
                        = keyDepth y (BinaryTree.node l k A) + 1 :=
                      keyDepth_node_lt (by omega) _ _
                    have h2 : keyDepth y (BinaryTree.node l k A) = 1 :=
                      keyDepth_node_self hyk _ _
                    have h3 : keyDepth y (BinaryTree.node l k
                        (BinaryTree.node (BinaryTree.node a x b) rk rr)) = 1 :=
                      keyDepth_node_self hyk _ _
                    simp only [List.length_nil]
                    omega
                  · by_cases hylt : y < k
                    · -- y < k : y lands in the cargo subtree l
                      rw [ds_div_lt hylt hklt, sp_len]
                      have h1 : keyDepth y
                          (BinaryTree.node (BinaryTree.node l k A) s (BinaryTree.node B rk rr))
                          = keyDepth y (BinaryTree.node l k A) + 1 :=
                        keyDepth_node_lt (by omega) _ _
                      have h2 : keyDepth y (BinaryTree.node l k A)
                          = keyDepth y l + 1 := keyDepth_node_lt hylt _ _
                      have h3 : keyDepth y (BinaryTree.node l k
                          (BinaryTree.node (BinaryTree.node a x b) rk rr))
                          = keyDepth y l + 1 := keyDepth_node_lt hylt _ _
                      omega
                    · have hkly : k < y := by omega
                      by_cases hyrk : y = rk
                      · rw [ds_both_gt hkly hklt, ds_self hyrk]
                        have h1 : keyDepth y
                            (BinaryTree.node (BinaryTree.node l k A) s (BinaryTree.node B rk rr))
                            = keyDepth y (BinaryTree.node B rk rr) + 1 :=
                          keyDepth_node_gt (by omega) _ _
                        have h2 : keyDepth y (BinaryTree.node B rk rr) = 1 :=
                          keyDepth_node_self hyrk _ _
                        simp only [List.length_nil]
                        omega
                      · by_cases hyrk2 : y < rk
                        · -- k < y < rk : y in the recursion zone
                          rw [ds_both_gt hkly hklt, ds_both_lt hyrk2 hqrk]
                          have hIH := ih _ hsz q y hbrl
                          rw [hs] at hIH
                          have h3 : keyDepth y (BinaryTree.node l k
                              (BinaryTree.node (BinaryTree.node a x b) rk rr))
                              = keyDepth y (BinaryTree.node (BinaryTree.node a x b) rk rr) + 1 :=
                            keyDepth_node_gt hkly _ _
                          have h4 : keyDepth y (BinaryTree.node (BinaryTree.node a x b) rk rr)
                              = keyDepth y (BinaryTree.node a x b) + 1 :=
                            keyDepth_node_lt hyrk2 _ _
                          rcases Nat.lt_trichotomy y s with hys | hys | hys
                          · have h1 : keyDepth y (BinaryTree.node
                                (BinaryTree.node l k A) s (BinaryTree.node B rk rr))
                                = keyDepth y (BinaryTree.node l k A) + 1 :=
                              keyDepth_node_lt hys _ _
                            have h2 : keyDepth y (BinaryTree.node l k A)
                                = keyDepth y A + 1 := keyDepth_node_gt hkly _ _
                            have h5 : keyDepth y (BinaryTree.node A s B) = keyDepth y A + 1 :=
                              keyDepth_node_lt hys _ _
                            omega
                          · have h1 : keyDepth y (BinaryTree.node
                                (BinaryTree.node l k A) s (BinaryTree.node B rk rr))
                                = 1 := keyDepth_node_self hys _ _
                            omega
                          · have h1 : keyDepth y (BinaryTree.node
                                (BinaryTree.node l k A) s (BinaryTree.node B rk rr))
                                = keyDepth y (BinaryTree.node B rk rr) + 1 :=
                              keyDepth_node_gt hys _ _
                            have h2 : keyDepth y (BinaryTree.node B rk rr)
                                = keyDepth y B + 1 := keyDepth_node_lt hyrk2 _ _
                            have h5 : keyDepth y (BinaryTree.node A s B) = keyDepth y B + 1 :=
                              keyDepth_node_gt hys _ _
                            omega
                        · -- rk < y : y lands in the cargo subtree rr
                          have hrky : rk < y := by omega
                          rw [ds_both_gt hkly hklt, ds_div_gt hrky hqrk, sp_len]
                          have h1 : keyDepth y (BinaryTree.node
                              (BinaryTree.node l k A) s (BinaryTree.node B rk rr))
                              = keyDepth y (BinaryTree.node B rk rr) + 1 :=
                            keyDepth_node_gt (by omega) _ _
                          have h2 : keyDepth y (BinaryTree.node B rk rr)
                              = keyDepth y rr + 1 := keyDepth_node_gt hrky _ _
                          have h3 : keyDepth y (BinaryTree.node l k
                              (BinaryTree.node (BinaryTree.node a x b) rk rr))
                              = keyDepth y (BinaryTree.node (BinaryTree.node a x b) rk rr) + 1 :=
                            keyDepth_node_gt hkly _ _
                          have h4 : keyDepth y (BinaryTree.node (BinaryTree.node a x b) rk rr)
                              = keyDepth y rr + 1 := keyDepth_node_gt hrky _ _
                          omega
            · by_cases hrkq : rk < q
              · cases rr with
                | empty =>
                  -- (11) ZAG with empty grandchild: result = node (node l k rl) rk empty
                  rw [splay.eq_def]
                  simp only [if_neg hqk, if_neg hqlt, if_neg hqrk, if_pos hrkq]
                  show 2 * keyDepth y
                      (BinaryTree.node (BinaryTree.node l k rl) rk BinaryTree.empty)
                      ≤ keyDepth y (BinaryTree.node l k (BinaryTree.node rl rk BinaryTree.empty))
                        + (divergeSuffix y q
                            (BinaryTree.node l k (BinaryTree.node rl rk BinaryTree.empty))).length
                        + 5
                  by_cases hyk : y = k
                  · rw [ds_self hyk]
                    have h1 : keyDepth y
                        (BinaryTree.node (BinaryTree.node l k rl) rk BinaryTree.empty)
                        = keyDepth y (BinaryTree.node l k rl) + 1 :=
                      keyDepth_node_lt (by omega) _ _
                    have h2 : keyDepth y (BinaryTree.node l k rl) = 1 :=
                      keyDepth_node_self hyk _ _
                    have h3 : keyDepth y
                        (BinaryTree.node l k (BinaryTree.node rl rk BinaryTree.empty)) = 1 :=
                      keyDepth_node_self hyk _ _
                    simp only [List.length_nil]
                    omega
                  · by_cases hylt : y < k
                    · rw [ds_div_lt hylt hklt, sp_len]
                      have h1 : keyDepth y
                          (BinaryTree.node (BinaryTree.node l k rl) rk BinaryTree.empty)
                          = keyDepth y (BinaryTree.node l k rl) + 1 :=
                        keyDepth_node_lt (by omega) _ _
                      have h2 : keyDepth y (BinaryTree.node l k rl)
                          = keyDepth y l + 1 := keyDepth_node_lt hylt _ _
                      have h3 : keyDepth y
                          (BinaryTree.node l k (BinaryTree.node rl rk BinaryTree.empty))
                          = keyDepth y l + 1 := keyDepth_node_lt hylt _ _
                      omega
                    · have hkly : k < y := by omega
                      by_cases hyrk : y = rk
                      · rw [ds_both_gt hkly hklt, ds_self hyrk]
                        have h1 : keyDepth y
                            (BinaryTree.node (BinaryTree.node l k rl) rk BinaryTree.empty) = 1 :=
                          keyDepth_node_self hyrk _ _
                        simp only [List.length_nil]
                        omega
                      · by_cases hyrk2 : y < rk
                        · rw [ds_both_gt hkly hklt, ds_div_lt hyrk2 hrkq, sp_len]
                          have h1 : keyDepth y
                              (BinaryTree.node (BinaryTree.node l k rl) rk BinaryTree.empty)
                              = keyDepth y (BinaryTree.node l k rl) + 1 :=
                            keyDepth_node_lt hyrk2 _ _
                          have h2 : keyDepth y (BinaryTree.node l k rl)
                              = keyDepth y rl + 1 := keyDepth_node_gt hkly _ _
                          have h3 : keyDepth y
                              (BinaryTree.node l k (BinaryTree.node rl rk BinaryTree.empty))
                              = keyDepth y (BinaryTree.node rl rk BinaryTree.empty) + 1 :=
                            keyDepth_node_gt hkly _ _
                          have h4 : keyDepth y (BinaryTree.node rl rk BinaryTree.empty)
                              = keyDepth y rl + 1 := keyDepth_node_lt hyrk2 _ _
                          omega
                        · have hrky : rk < y := by omega
                          rw [ds_both_gt hkly hklt, ds_both_gt hrky hrkq, divergeSuffix_empty]
                          have h1 : keyDepth y
                              (BinaryTree.node (BinaryTree.node l k rl) rk BinaryTree.empty)
                              = keyDepth y BinaryTree.empty + 1 := keyDepth_node_gt hrky _ _
                          have h2 : keyDepth y BinaryTree.empty = 0 := rfl
                          simp only [List.length_nil]
                          omega
                | node a x b =>
                  -- (12) ZAG-ZAG
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
                    by_cases hyk : y = k
                    · -- y = k : depth 1 → 3 (tight, 2*3 = 1 + 0 + 5)
                      rw [ds_self hyk]
                      have h1 : keyDepth y (BinaryTree.node
                          (BinaryTree.node (BinaryTree.node l k rl) rk A) s B)
                          = keyDepth y (BinaryTree.node (BinaryTree.node l k rl) rk A) + 1 :=
                        keyDepth_node_lt (by omega) _ _
                      have h2 : keyDepth y (BinaryTree.node (BinaryTree.node l k rl) rk A)
                          = keyDepth y (BinaryTree.node l k rl) + 1 :=
                        keyDepth_node_lt (by omega) _ _
                      have h3 : keyDepth y (BinaryTree.node l k rl) = 1 :=
                        keyDepth_node_self hyk _ _
                      have h4 : keyDepth y (BinaryTree.node l k
                          (BinaryTree.node rl rk (BinaryTree.node a x b))) = 1 :=
                        keyDepth_node_self hyk _ _
                      simp only [List.length_nil]
                      omega
                    · by_cases hylt : y < k
                      · -- y < k : y lands in the cargo subtree l (tight: 2d+6 ≤ 2d+6)
                        rw [ds_div_lt hylt hklt, sp_len]
                        have h1 : keyDepth y (BinaryTree.node
                            (BinaryTree.node (BinaryTree.node l k rl) rk A) s B)
                            = keyDepth y (BinaryTree.node (BinaryTree.node l k rl) rk A) + 1 :=
                          keyDepth_node_lt (by omega) _ _
                        have h2 : keyDepth y (BinaryTree.node (BinaryTree.node l k rl) rk A)
                            = keyDepth y (BinaryTree.node l k rl) + 1 :=
                          keyDepth_node_lt (by omega) _ _
                        have h3 : keyDepth y (BinaryTree.node l k rl)
                            = keyDepth y l + 1 := keyDepth_node_lt hylt _ _
                        have h4 : keyDepth y (BinaryTree.node l k
                            (BinaryTree.node rl rk (BinaryTree.node a x b)))
                            = keyDepth y l + 1 := keyDepth_node_lt hylt _ _
                        omega
                      · have hkly : k < y := by omega
                        by_cases hyrk : y = rk
                        · rw [ds_both_gt hkly hklt, ds_self hyrk]
                          have h1 : keyDepth y (BinaryTree.node
                              (BinaryTree.node (BinaryTree.node l k rl) rk A) s B)
                              = keyDepth y (BinaryTree.node (BinaryTree.node l k rl) rk A) + 1 :=
                            keyDepth_node_lt (by omega) _ _
                          have h2 : keyDepth y (BinaryTree.node (BinaryTree.node l k rl) rk A)
                              = 1 := keyDepth_node_self hyrk _ _
                          simp only [List.length_nil]
                          omega
                        · by_cases hyrk2 : y < rk
                          · -- k < y < rk : y lands in the cargo subtree rl
                            rw [ds_both_gt hkly hklt, ds_div_lt hyrk2 hrkq, sp_len]
                            have h1 : keyDepth y (BinaryTree.node
                                (BinaryTree.node (BinaryTree.node l k rl) rk A) s B)
                                = keyDepth y
                                    (BinaryTree.node (BinaryTree.node l k rl) rk A) + 1 :=
                              keyDepth_node_lt (by omega) _ _
                            have h2 : keyDepth y (BinaryTree.node (BinaryTree.node l k rl) rk A)
                                = keyDepth y (BinaryTree.node l k rl) + 1 :=
                              keyDepth_node_lt hyrk2 _ _
                            have h3 : keyDepth y (BinaryTree.node l k rl)
                                = keyDepth y rl + 1 := keyDepth_node_gt hkly _ _
                            have h4 : keyDepth y (BinaryTree.node l k
                                (BinaryTree.node rl rk (BinaryTree.node a x b)))
                                = keyDepth y (BinaryTree.node rl rk (BinaryTree.node a x b)) + 1 :=
                              keyDepth_node_gt hkly _ _
                            have h5 : keyDepth y (BinaryTree.node rl rk (BinaryTree.node a x b))
                                = keyDepth y rl + 1 := keyDepth_node_lt hyrk2 _ _
                            omega
                          · -- rk < y : y in the recursion zone
                            have hrky : rk < y := by omega
                            rw [ds_both_gt hkly hklt, ds_both_gt hrky hrkq]
                            have hIH := ih _ hsz q y hbrr
                            rw [hs] at hIH
                            have h3 : keyDepth y (BinaryTree.node l k
                                (BinaryTree.node rl rk (BinaryTree.node a x b)))
                                = keyDepth y
                                    (BinaryTree.node rl rk (BinaryTree.node a x b)) + 1 :=
                              keyDepth_node_gt hkly _ _
                            have h4 : keyDepth y (BinaryTree.node rl rk (BinaryTree.node a x b))
                                = keyDepth y (BinaryTree.node a x b) + 1 :=
                              keyDepth_node_gt hrky _ _
                            rcases Nat.lt_trichotomy y s with hys | hys | hys
                            · have h1 : keyDepth y (BinaryTree.node
                                  (BinaryTree.node (BinaryTree.node l k rl) rk A) s B)
                                  = keyDepth y
                                      (BinaryTree.node (BinaryTree.node l k rl) rk A) + 1 :=
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
              · -- (13) q found at the right child (q = rk): single ZAG
                have hqrk_eq : q = rk := by omega
                rw [splay.eq_def]
                simp only [if_neg hqk, if_neg hqlt, if_neg hqrk, if_neg hrkq]
                show 2 * keyDepth y (BinaryTree.node (BinaryTree.node l k rl) rk rr)
                    ≤ keyDepth y (BinaryTree.node l k (BinaryTree.node rl rk rr))
                      + (divergeSuffix y q
                          (BinaryTree.node l k (BinaryTree.node rl rk rr))).length + 5
                by_cases hyk : y = k
                · rw [ds_self hyk]
                  have h1 : keyDepth y (BinaryTree.node (BinaryTree.node l k rl) rk rr)
                      = keyDepth y (BinaryTree.node l k rl) + 1 :=
                    keyDepth_node_lt (by omega) _ _
                  have h2 : keyDepth y (BinaryTree.node l k rl) = 1 :=
                    keyDepth_node_self hyk _ _
                  have h3 : keyDepth y (BinaryTree.node l k (BinaryTree.node rl rk rr)) = 1 :=
                    keyDepth_node_self hyk _ _
                  simp only [List.length_nil]
                  omega
                · by_cases hylt : y < k
                  · rw [ds_div_lt hylt hklt, sp_len]
                    have h1 : keyDepth y (BinaryTree.node (BinaryTree.node l k rl) rk rr)
                        = keyDepth y (BinaryTree.node l k rl) + 1 :=
                      keyDepth_node_lt (by omega) _ _
                    have h2 : keyDepth y (BinaryTree.node l k rl)
                        = keyDepth y l + 1 := keyDepth_node_lt hylt _ _
                    have h3 : keyDepth y (BinaryTree.node l k (BinaryTree.node rl rk rr))
                        = keyDepth y l + 1 := keyDepth_node_lt hylt _ _
                    omega
                  · have hkly : k < y := by omega
                    by_cases hyrk : y = rk
                    · rw [ds_both_gt hkly hklt, ds_self hyrk]
                      have h1 : keyDepth y (BinaryTree.node (BinaryTree.node l k rl) rk rr) = 1 :=
                        keyDepth_node_self hyrk _ _
                      simp only [List.length_nil]
                      omega
                    · by_cases hyrk2 : y < rk
                      · rw [ds_both_gt hkly hklt, ds_qroot_lt hqrk_eq hyrk2, sp_len]
                        have h1 : keyDepth y (BinaryTree.node (BinaryTree.node l k rl) rk rr)
                            = keyDepth y (BinaryTree.node l k rl) + 1 :=
                          keyDepth_node_lt hyrk2 _ _
                        have h2 : keyDepth y (BinaryTree.node l k rl)
                            = keyDepth y rl + 1 := keyDepth_node_gt hkly _ _
                        have h3 : keyDepth y (BinaryTree.node l k (BinaryTree.node rl rk rr))
                            = keyDepth y (BinaryTree.node rl rk rr) + 1 :=
                          keyDepth_node_gt hkly _ _
                        have h4 : keyDepth y (BinaryTree.node rl rk rr)
                            = keyDepth y rl + 1 := keyDepth_node_lt hyrk2 _ _
                        omega
                      · have hrky : rk < y := by omega
                        rw [ds_both_gt hkly hklt, ds_qroot_gt hqrk_eq hrky, sp_len]
                        have h1 : keyDepth y (BinaryTree.node (BinaryTree.node l k rl) rk rr)
                            = keyDepth y rr + 1 := keyDepth_node_gt hrky _ _
                        have h2 : keyDepth y (BinaryTree.node l k (BinaryTree.node rl rk rr))
                            = keyDepth y (BinaryTree.node rl rk rr) + 1 :=
                          keyDepth_node_gt hkly _ _
                        have h3 : keyDepth y (BinaryTree.node rl rk rr)
                            = keyDepth y rr + 1 := keyDepth_node_gt hrky _ _
                        omega

/-- **GENERALIZED HALVING (R1 core).** After splaying `q` in a BST, the depth of an
ARBITRARY key `y` (no membership/on-path hypothesis) satisfies
`2 * keyDepth y (splay t q) ≤ keyDepth y t + (divergeSuffix y q t).length + 5`.
Via `searchPath_eq_shared_append_suffix` / `searchPath_splay_decomp` this is exactly
`2 * |new prefix| ≤ |shared prefix| + 5`.  Constant 5 is tight. -/

theorem keyDepth_splay_le_shared (q y : Nat) (t : BinaryTree) (hbst : IsBST t) :
    2 * keyDepth y (splay t q) ≤ keyDepth y t + (divergeSuffix y q t).length + 5 :=
  keyDepth_splay_le_shared_aux t.num_nodes t (Nat.le_refl _) q y hbst

/-- On-path keys have empty divergence suffix (in a BST). -/

theorem divergeSuffix_eq_nil_of_mem (q y : Nat) :
    ∀ (t : BinaryTree), IsBST t → y ∈ searchPath q t → divergeSuffix y q t = [] := by
  intro t
  induction t with
  | empty => intro _ hy; simp [searchPath] at hy
  | node l k r ihl ihr =>
    intro hbst hy
    rcases isBST_node_iff.mp hbst with ⟨hfl, hfr, hbl, hbr⟩
    by_cases hyk : y = k
    · exact ds_self hyk
    · by_cases hqk : q = k
      · rw [searchPath_node_self hqk] at hy
        simp only [List.mem_singleton] at hy
        exact absurd hy hyk
      · by_cases hqlt : q < k
        · rw [searchPath_node_lt hqlt] at hy
          rcases List.mem_cons.mp hy with h | h
          · exact absurd h hyk
          · have hyl : y < k := mem_searchPath_forall (p := fun z => z < k) hfl h
            rw [ds_both_lt hyl hqlt]
            exact ihl hbl h
        · have hklt : k < q := by omega
          rw [searchPath_node_gt hklt] at hy
          rcases List.mem_cons.mp hy with h | h
          · exact absurd h hyk
          · have hyr : k < y := mem_searchPath_forall hfr h
            rw [ds_both_gt hyr hklt]
            exact ihr hbr h

/-- Sanity check: the proven on-path halving lemma is the suffix-free special case. -/

theorem keyDepth_splay_halving_of_shared (q y : Nat) (t : BinaryTree)
    (hbst : IsBST t) (hy : y ∈ searchPath q t) :
    2 * keyDepth y (splay t q) ≤ keyDepth y t + 5 := by
  have h := keyDepth_splay_le_shared q y t hbst
  rw [divergeSuffix_eq_nil_of_mem q y t hbst hy] at h
  simpa using h


-- ===== R2 within-run + general sharedTouched lemma =====
theorem touchedCount_eq_length {T c : List Nat} (h : ∀ z ∈ c, z ∈ T) :
    touchedCount T c = c.length := by
  simp only [touchedCount]
  congr 1
  exact List.filter_eq_self.mpr (fun a ha => decide_eq_true (h a ha))

/-- Every search path into a node starts with its root key. -/

theorem searchPath_node_head (v k : Nat) (l r : BinaryTree) :
    ∃ rest, searchPath v (.node l k r) = k :: rest := by
  by_cases h1 : v = k
  · exact ⟨[], searchPath_node_self h1 l r⟩
  · by_cases h2 : v < k
    · exact ⟨searchPath v l, searchPath_node_lt h2 l r⟩
    · exact ⟨searchPath v r, searchPath_node_gt (by omega) l r⟩

/-- CORE SKELETON.  Under the shared-prefix-touched hypothesis the new/old touched
counts differ exactly by `|p'| − |sh|`, and the generalized halving lemma bounds
`2|p'| ≤ |sh| + 5`.  Everything else is arithmetic on `|sh|`. -/

theorem touchedCount_shared_decomp (t : BinaryTree) (q v : Nat) (T : List Nat)
    (hbst : IsBST t)
    (hsh : ∀ z ∈ searchPath q t, z ∈ searchPath v t → z ∈ T) :
    ∃ p' sh : List Nat,
      searchPath v t = sh ++ divergeSuffix v q t
      ∧ touchedCount (T ++ searchPath q t) (searchPath v (splay t q)) + sh.length
          = touchedCount T (searchPath v t) + p'.length
      ∧ 2 * p'.length ≤ sh.length + 5 := by
  obtain ⟨p', hnew, hp'⟩ := searchPath_splay_decomp q v t hbst
  obtain ⟨sh, hold, hshq⟩ := searchPath_eq_shared_append_suffix q v t
  refine ⟨p', sh, hold, ?_, ?_⟩
  · -- counting: T' fully covers p', T fully covers sh (hypothesis W6),
    -- and the divergence suffix is T'/T-indistinguishable.
    have e1 : touchedCount (T ++ searchPath q t) (searchPath v (splay t q))
        = p'.length + touchedCount T (divergeSuffix v q t) := by
      rw [hnew, touchedCount_append]
      congr 1
      · exact touchedCount_eq_length (fun z hz => List.mem_append_right T (hp' z hz))
      · exact touchedCount_congr (fun z hz => by
          constructor
          · intro hzT'
            rcases List.mem_append.mp hzT' with h | h
            · exact h
            · exact absurd h (divergeSuffix_disjoint t hbst z hz)
          · exact fun h => List.mem_append_left _ h)
    have e2 : touchedCount T (searchPath v t)
        = sh.length + touchedCount T (divergeSuffix v q t) := by
      rw [hold, touchedCount_append]
      congr 1
      exact touchedCount_eq_length (fun z hz =>
        hsh z (hshq z hz) (by rw [hold]; exact List.mem_append_left _ hz))
    omega
  · -- halving: 2·|p' ++ ds| ≤ |sh ++ ds| + |ds| + 5
    have h5 := keyDepth_splay_le_shared q v t hbst
    rw [← sp_len, ← sp_len, hnew, hold] at h5
    simp only [List.length_append] at h5
    omega

/-- **GENERAL SHARED-PREFIX-TOUCHED DEEPENING (+2, no side condition).**
If every node lying on BOTH `q`'s and `v`'s old search paths is already touched, then
`v`'s search path in the splayed tree, counted against `T ∪ keys(searchPath q t)`,
deepens by at most 2 over its old path counted against `T` — for ARBITRARY `q, v`.
In the opposite-side geometry the shared prefix is just the root, so this subsumes the
sibling theorem `touchedCount_mixed_splay_le`; the constant 2 is tight there. -/

theorem touchedCount_sharedTouched_splay_le (t : BinaryTree) (q v : Nat) (T : List Nat)
    (hbst : IsBST t) (hne : t ≠ .empty)
    (hsh : ∀ z ∈ searchPath q t, z ∈ searchPath v t → z ∈ T) :
    touchedCount (T ++ searchPath q t) (searchPath v (splay t q))
      ≤ touchedCount T (searchPath v t) + 2 := by
  obtain ⟨p', sh, hold, hcount, hhalf⟩ := touchedCount_shared_decomp t q v T hbst hsh
  cases t with
  | empty => exact absurd rfl hne
  | node l k r =>
    have hkq : k ∈ searchPath q (.node l k r) := root_mem_searchPath q k l r
    have hkv : k ∈ searchPath v (.node l k r) := root_mem_searchPath v k l r
    have h1 : 1 ≤ sh.length := by
      rw [hold] at hkv
      rcases List.mem_append.mp hkv with h | h
      · exact List.length_pos_of_mem h
      · exact absurd hkq (divergeSuffix_disjoint _ hbst k h)
    omega

/-- Degenerate within-run shapes: when the splay is the identity AND `q`'s search path is
just the root, the enlarged touched set counts any path exactly as `T` does. -/

theorem touchedCount_splay_id_case (l r : BinaryTree) (k q v : Nat) (T : List Nat)
    (hkT : k ∈ T)
    (hid : splay (.node l k r) q = .node l k r)
    (hpq : searchPath q (.node l k r) = [k]) :
    touchedCount (T ++ searchPath q (.node l k r)) (searchPath v (splay (.node l k r) q))
      = touchedCount T (searchPath v (.node l k r)) := by
  rw [hid, hpq]
  exact touchedCount_congr (fun z hz => by
    constructor
    · intro h
      rcases List.mem_append.mp h with h | h
      · exact h
      · simp only [List.mem_singleton] at h
        exact h ▸ hkT
    · exact fun h => List.mem_append_left _ h)

/-- **(R2-within) HEADLINE, SHARP FORM (+1).**  Within-run geometry: the previous access
(= the root) and the current access `q` on the same side, the next opposite-side target
`v` beyond both (`rootKey t ≤ q ≤ v`, or the mirror `v ≤ q ≤ rootKey t`).  Touched-set
hypothesis (W6): every node shared by `q`'s and `v`'s old search paths is in `T`.
Then the deepening constant is 1 — one better than the opposite-side case — and 1 is
tight (5-key zig-zig witness below). -/

theorem touchedCount_within_run_splay_le_one (t : BinaryTree) (q v : Nat) (T : List Nat)
    (hbst : IsBST t) (hne : t ≠ .empty)
    (hside : (rootKey t ≤ q ∧ q ≤ v) ∨ (v ≤ q ∧ q ≤ rootKey t))
    (hsh : ∀ z ∈ searchPath q t, z ∈ searchPath v t → z ∈ T) :
    touchedCount (T ++ searchPath q t) (searchPath v (splay t q))
      ≤ touchedCount T (searchPath v t) + 1 := by
  cases t with
  | empty => exact absurd rfl hne
  | node l k r =>
    simp only [rootKey] at hside
    have hkT : k ∈ T := hsh k (root_mem_searchPath q k l r) (root_mem_searchPath v k l r)
    by_cases hqk : q = k
    · -- q found at the root: splay is the identity, q's path is [k]
      rw [touchedCount_splay_id_case l r k q v T hkT
        (by rw [splay.eq_def]; simp only [if_pos hqk])
        (searchPath_node_self hqk l r)]
      omega
    · rcases hside with ⟨hq, hv⟩ | ⟨hv, hq⟩
      · -- k < q ≤ v
        have hklt : k < q := by omega
        cases r with
        | empty =>
          -- q exits at the root: splay is the identity, q's path is [k]
          rw [touchedCount_splay_id_case l .empty k q v T hkT
            (by rw [splay.eq_def]; simp only [if_neg hqk, if_neg (by omega : ¬ q < k)])
            (by rw [searchPath_node_gt hklt]; rfl)]
          omega
        | node rl rk rr =>
          obtain ⟨p', sh, hold, hcount, hhalf⟩ :=
            touchedCount_shared_decomp (.node l k (.node rl rk rr)) q v T hbst hsh
          have hkv : k < v := by omega
          obtain ⟨rest, hrest⟩ := searchPath_node_head v rk rl rr
          have hvpath : searchPath v (.node l k (.node rl rk rr)) = k :: rk :: rest := by
            rw [searchPath_node_gt hkv, hrest]
          have hkq : k ∈ searchPath q (.node l k (.node rl rk rr)) :=
            root_mem_searchPath q k _ _
          have hrkq : rk ∈ searchPath q (.node l k (.node rl rk rr)) := by
            rw [searchPath_node_gt hklt]
            exact List.mem_cons_of_mem _ (root_mem_searchPath q rk rl rr)
          rw [hvpath] at hold
          -- both q and v route rightward at the root: the first TWO nodes are shared
          have h2 : 2 ≤ sh.length := by
            rcases sh with _ | ⟨z0, _ | ⟨z1, sh'⟩⟩
            · exfalso
              simp only [List.nil_append] at hold
              exact divergeSuffix_disjoint (q := q) (y := v) _ hbst k
                (by rw [← hold]; exact List.mem_cons_self) hkq
            · exfalso
              simp only [List.cons_append, List.nil_append] at hold
              injection hold with h1 htl
              exact divergeSuffix_disjoint (q := q) (y := v) _ hbst rk
                (by rw [← htl]; exact List.mem_cons_self) hrkq
            · simp only [List.length_cons]
              omega
          omega
      · -- mirror: v ≤ q < k
        have hklt : q < k := by omega
        cases l with
        | empty =>
          rw [touchedCount_splay_id_case .empty r k q v T hkT
            (by rw [splay.eq_def]; simp only [if_neg hqk, if_pos hklt])
            (by rw [searchPath_node_lt hklt]; rfl)]
          omega
        | node ll lk lr =>
          obtain ⟨p', sh, hold, hcount, hhalf⟩ :=
            touchedCount_shared_decomp (.node (.node ll lk lr) k r) q v T hbst hsh
          have hvk : v < k := by omega
          obtain ⟨rest, hrest⟩ := searchPath_node_head v lk ll lr
          have hvpath : searchPath v (.node (.node ll lk lr) k r) = k :: lk :: rest := by
            rw [searchPath_node_lt hvk, hrest]
          have hkq : k ∈ searchPath q (.node (.node ll lk lr) k r) :=
            root_mem_searchPath q k _ _
          have hlkq : lk ∈ searchPath q (.node (.node ll lk lr) k r) := by
            rw [searchPath_node_lt hklt]
            exact List.mem_cons_of_mem _ (root_mem_searchPath q lk ll lr)
          rw [hvpath] at hold
          have h2 : 2 ≤ sh.length := by
            rcases sh with _ | ⟨z0, _ | ⟨z1, sh'⟩⟩
            · exfalso
              simp only [List.nil_append] at hold
              exact divergeSuffix_disjoint (q := q) (y := v) _ hbst k
                (by rw [← hold]; exact List.mem_cons_self) hkq
            · exfalso
              simp only [List.cons_append, List.nil_append] at hold
              injection hold with h1 htl
              exact divergeSuffix_disjoint (q := q) (y := v) _ hbst lk
                (by rw [← htl]; exact List.mem_cons_self) hlkq
            · simp only [List.length_cons]
              omega
          omega

/-- **(R2-within) HEADLINE, REQUESTED FORM (+2).**  Drop-in sibling of
`touchedCount_mixed_splay_le` for the within-run case, weakened to the requested
constant 2. -/

theorem touchedCount_within_run_splay_le (t : BinaryTree) (q v : Nat) (T : List Nat)
    (hbst : IsBST t) (hne : t ≠ .empty)
    (hside : (rootKey t ≤ q ∧ q ≤ v) ∨ (v ≤ q ∧ q ≤ rootKey t))
    (hsh : ∀ z ∈ searchPath q t, z ∈ searchPath v t → z ∈ T) :
    touchedCount (T ++ searchPath q t) (searchPath v (splay t q))
      ≤ touchedCount T (searchPath v t) + 2 := by
  have := touchedCount_within_run_splay_le_one t q v T hbst hne hside hsh
  omega

/-! ## Subsumption check: the sibling's opposite-side theorem from the general one

For `q ≤ rootKey t ≤ v` (or the mirror) the two paths separate at the root, so the
shared prefix is `[rootKey t]` and W6 degenerates to the sibling's `rootKey t ∈ T`. -/

/-- A min-side (`q ≤ k`) search path stays at keys ≤ k. -/

theorem touchedCount_mixed_splay_le_of_shared (t : BinaryTree) (q v : Nat) (T : List Nat)
    (hbst : IsBST t) (hne : t ≠ .empty) (hroot : rootKey t ∈ T)
    (hside : (q ≤ rootKey t ∧ rootKey t ≤ v) ∨ (v ≤ rootKey t ∧ rootKey t ≤ q)) :
    touchedCount (T ++ searchPath q t) (searchPath v (splay t q))
      ≤ touchedCount T (searchPath v t) + 2 := by
  apply touchedCount_sharedTouched_splay_le t q v T hbst hne
  intro z hzq hzv
  cases t with
  | empty => exact absurd rfl hne
  | node l k r =>
    simp only [rootKey] at hside hroot
    rcases isBST_node_iff.mp hbst with ⟨hL, hR, _, _⟩
    rcases hside with ⟨hq, hv⟩ | ⟨hv, hq⟩
    · have h1 : z ≤ k := searchPath_all_le_of_left hL hq z hzq
      have h2 : k ≤ z := searchPath_all_ge_of_right hR hv z hzv
      have : z = k := by omega
      rwa [this]
    · have h1 : k ≤ z := searchPath_all_ge_of_right hR hq z hzq
      have h2 : z ≤ k := searchPath_all_le_of_left hL hv z hzv
      have : z = k := by omega
      rwa [this]

/-! ## Tightness / failure witnesses (from the pinning harness, machine-checked)

`t₁ = node ∅ 0 (node (node (node (node ∅ 1 ∅) 2 ∅) 3 ∅) 4 ∅)` (right zig-zig chain),
`q = 1`, `v = 3`: within-run (0 ≤ 1 ≤ 3).  Shared prefix of the two old paths = {0,4,3}.

* With `T = [0,3,4]` (W6 satisfied) the excess is EXACTLY 1 — the `+1` is tight.
* With `T = [0]` (W1 = root-touched, W6 violated) the excess is 3 — already beats `+2`
  on 5 keys; on the 16-key zig-zag comb it reaches 8, growing ~n/2.  No constant works
  without W6.

`t₂ = node ∅ 2 (node ∅ 3 (node ∅ 4 ∅))`, `q = 4`, `v = 0`, `T = [2]`: opposite-side
shape; the general (side-condition-free) `+2` is tight. -/

example :
    touchedCount ([0,3,4] ++ searchPath 1
        (.node .empty 0 (.node (.node (.node (.node .empty 1 .empty) 2 .empty) 3 .empty)
          4 .empty)))
      (searchPath 3 (splay
        (.node .empty 0 (.node (.node (.node (.node .empty 1 .empty) 2 .empty) 3 .empty)
          4 .empty)) 1))
    = touchedCount [0,3,4] (searchPath 3
        (.node .empty 0 (.node (.node (.node (.node .empty 1 .empty) 2 .empty) 3 .empty)
          4 .empty))) + 1 := by decide

example :
    touchedCount ([0] ++ searchPath 1
        (.node .empty 0 (.node (.node (.node (.node .empty 1 .empty) 2 .empty) 3 .empty)
          4 .empty)))
      (searchPath 3 (splay
        (.node .empty 0 (.node (.node (.node (.node .empty 1 .empty) 2 .empty) 3 .empty)
          4 .empty)) 1))
    = touchedCount [0] (searchPath 3
        (.node .empty 0 (.node (.node (.node (.node .empty 1 .empty) 2 .empty) 3 .empty)
          4 .empty))) + 3 := by decide

example :
    touchedCount ([2] ++ searchPath 4 (.node .empty 2 (.node .empty 3 (.node .empty 4 .empty))))
      (searchPath 0 (splay (.node .empty 2 (.node .empty 3 (.node .empty 4 .empty))) 4))
    = touchedCount [2] (searchPath 0
        (.node .empty 2 (.node .empty 3 (.node .empty 4 .empty)))) + 2 := by decide


-- ===== C3 opposite-side verbatim preservation =====
theorem ds_left_irrel {k b y : Nat} (hb : k ≤ b) (hy : k ≤ y) (X l r : BinaryTree) :
    divergeSuffix y b (.node X k r) = divergeSuffix y b (.node l k r) := by
  by_cases hyk : y = k
  · rw [ds_self hyk, ds_self hyk]
  · have hky : k < y := Nat.lt_of_le_of_ne hy (fun h => hyk h.symm)
    by_cases hbk : b = k
    · rw [ds_qroot_gt hbk hky, ds_qroot_gt hbk hky]
    · have hkb : k < b := Nat.lt_of_le_of_ne hb (fun h => hbk h.symm)
      rw [ds_both_gt hky hkb, ds_both_gt hky hkb]

theorem ds_right_irrel {k b y : Nat} (hb : b ≤ k) (hy : y ≤ k) (l X r : BinaryTree) :
    divergeSuffix y b (.node l k X) = divergeSuffix y b (.node l k r) := by
  by_cases hyk : y = k
  · rw [ds_self hyk, ds_self hyk]
  · have hyk' : y < k := Nat.lt_of_le_of_ne hy hyk
    by_cases hbk : b = k
    · rw [ds_qroot_lt hbk hyk', ds_qroot_lt hbk hyk']
    · have hbk' : b < k := Nat.lt_of_le_of_ne hb hbk
      rw [ds_both_lt hyk' hbk', ds_both_lt hyk' hbk']

/-! ## NEW: the opposite-side structure lemma

For `q ≤ k` (root key), the top-level splay step leaves the old root `k` with its
right subtree `r` VERBATIM at depth ≤ 2, with every new ancestor key < k.
Non-recursive case analysis on the five outermost shapes. -/

theorem splay_left_structure (l r : BinaryTree) (k q : Nat)
    (hL : ForallTree (fun x => x < k) l) (hq : q ≤ k) :
    splay (.node l k r) q = .node l k r
    ∨ (∃ X w Y, w < k ∧ splay (.node l k r) q = .node X w (.node Y k r))
    ∨ (∃ X w Y u Z, w < k ∧ u < k ∧
        splay (.node l k r) q = .node X w (.node Y u (.node Z k r))) := by
  by_cases hqk : q = k
  · -- found at root: identity
    left
    rw [splay.eq_def]
    simp only [if_pos hqk]
  · have hqlt : q < k := Nat.lt_of_le_of_ne hq hqk
    cases l with
    | empty =>
      -- q not found, tree unchanged
      left
      rw [splay.eq_def]
      simp only [if_neg hqk, if_pos hqlt]
    | node ll lk lr =>
      rcases forallTree_node_iff.mp hL with ⟨hFll, hlkk, hFlr⟩
      by_cases hqlk : q < lk
      · cases ll with
        | empty =>
          -- zig with empty grandchild
          right; left
          refine ⟨.empty, lk, lr, hlkk, ?_⟩
          rw [splay.eq_def]
          simp only [if_neg hqk, if_pos hqlt, if_pos hqlk]
          rfl
        | node a x b =>
          -- zig-zig
          cases hS : splay (BinaryTree.node a x b) q with
          | empty => exact absurd hS (splay_ne_empty a b x q)
          | node A s B =>
            have hsk : s < k := by
              have hF := splay_forallTree_kd (fun z => z < k) (.node a x b) q hFll
              rw [hS] at hF
              exact (forallTree_node_iff.mp hF).2.1
            right; right
            exact ⟨A, s, B, lk, lr, hsk, hlkk,
              splay_zigzig_shape (.node a x b) lr r A B lk k q s hqk hqlt hqlk
                (fun h => nomatch h) hS⟩
      · by_cases hlkq : lk < q
        · cases lr with
          | empty =>
            -- zig with empty grandchild
            right; left
            refine ⟨ll, lk, .empty, hlkk, ?_⟩
            rw [splay.eq_def]
            simp only [if_neg hqk, if_pos hqlt, if_neg hqlk, if_pos hlkq]
            rfl
          | node a x b =>
            -- zig-zag
            cases hS : splay (BinaryTree.node a x b) q with
            | empty => exact absurd hS (splay_ne_empty a b x q)
            | node A s B =>
              have hsk : s < k := by
                have hF := splay_forallTree_kd (fun z => z < k) (.node a x b) q hFlr
                rw [hS] at hF
                exact (forallTree_node_iff.mp hF).2.1
              right; left
              exact ⟨.node ll lk A, s, B, hsk,
                splay_zigzag_shape ll (.node a x b) r A B lk k q s hqk hqlt hlkq
                  (fun h => nomatch h) hS⟩
        · -- q = lk: found at left child, single zig
          right; left
          refine ⟨ll, lk, lr, hlkk, ?_⟩
          rw [splay.eq_def]
          simp only [if_neg hqk, if_pos hqlt, if_neg hqlk, if_neg hlkq]
          rfl

/-- Mirror of `splay_left_structure`: for `k ≤ q` the old root `k` keeps its LEFT
subtree `l` verbatim at depth ≤ 2, with every new ancestor key > k. -/

theorem splay_right_structure (l r : BinaryTree) (k q : Nat)
    (hR : ForallTree (fun x => k < x) r) (hq : k ≤ q) :
    splay (.node l k r) q = .node l k r
    ∨ (∃ X w Y, k < w ∧ splay (.node l k r) q = .node (.node l k Y) w X)
    ∨ (∃ X w Y u Z, k < w ∧ k < u ∧
        splay (.node l k r) q = .node (.node (.node l k Z) u Y) w X) := by
  by_cases hqk : q = k
  · left
    rw [splay.eq_def]
    simp only [if_pos hqk]
  · have hklt : k < q := Nat.lt_of_le_of_ne hq (fun h => hqk h.symm)
    have hnqlt : ¬ q < k := by omega
    cases r with
    | empty =>
      left
      rw [splay.eq_def]
      simp only [if_neg hqk, if_neg hnqlt]
    | node rl rk rr =>
      rcases forallTree_node_iff.mp hR with ⟨hFrl, hrkk, hFrr⟩
      by_cases hqrk : q < rk
      · cases rl with
        | empty =>
          -- zag with empty grandchild
          right; left
          refine ⟨rr, rk, .empty, hrkk, ?_⟩
          rw [splay.eq_def]
          simp only [if_neg hqk, if_neg hnqlt, if_pos hqrk]
          rfl
        | node a x b =>
          -- zag-zig
          cases hS : splay (BinaryTree.node a x b) q with
          | empty => exact absurd hS (splay_ne_empty a b x q)
          | node A s B =>
            have hks : k < s := by
              have hF := splay_forallTree_kd (fun z => k < z) (.node a x b) q hFrl
              rw [hS] at hF
              exact (forallTree_node_iff.mp hF).2.1
            right; left
            exact ⟨.node B rk rr, s, A, hks,
              splay_zagzig_shape l (.node a x b) rr A B rk k q s hqk hklt hqrk
                (fun h => nomatch h) hS⟩
      · by_cases hrkq : rk < q
        · cases rr with
          | empty =>
            -- zag with empty grandchild
            right; left
            refine ⟨.empty, rk, rl, hrkk, ?_⟩
            rw [splay.eq_def]
            simp only [if_neg hqk, if_neg hnqlt, if_neg hqrk, if_pos hrkq]
            rfl
          | node a x b =>
            -- zag-zag
            cases hS : splay (BinaryTree.node a x b) q with
            | empty => exact absurd hS (splay_ne_empty a b x q)
            | node A s B =>
              have hks : k < s := by
                have hF := splay_forallTree_kd (fun z => k < z) (.node a x b) q hFrr
                rw [hS] at hF
                exact (forallTree_node_iff.mp hF).2.1
              right; right
              exact ⟨B, s, A, rk, rl, hks, hrkk,
                splay_zagzag_shape l rl (.node a x b) A B rk k q s hqk hklt hrkq
                  (fun h => nomatch h) hS⟩
        · -- q = rk: found at right child, single zag
          right; left
          refine ⟨rr, rk, rl, hrkk, ?_⟩
          rw [splay.eq_def]
          simp only [if_neg hqk, if_neg hnqlt, if_neg hqrk, if_neg hrkq]
          rfl

/-! ## (P1) MAIN THEOREM — verbatim preservation of the divergence suffix

Opposite-side dive: splaying `q` with `q ≤ rootKey t ≤ b` and `rootKey t ≤ y`
(`b`, `y` future max-side targets) preserves `divergeSuffix y b` EXACTLY. -/

theorem divergeSuffix_splay_opposite_left (t : BinaryTree) (q b y : Nat)
    (hbst : IsBST t)
    (hq : q ≤ rootKey t) (hb : rootKey t ≤ b) (hy : rootKey t ≤ y) :
    divergeSuffix y b (splay t q) = divergeSuffix y b t := by
  cases t with
  | empty => rfl
  | node l k r =>
    rcases isBST_node_iff.mp hbst with ⟨hL, _, _, _⟩
    have hq' : q ≤ k := hq
    have hb' : k ≤ b := hb
    have hy' : k ≤ y := hy
    rcases splay_left_structure l r k q hL hq' with
      h | ⟨X, w, Y, hwk, h⟩ | ⟨X, w, Y, u, Z, hwk, huk, h⟩
    · rw [h]
    · rw [h, ds_both_gt (Nat.lt_of_lt_of_le hwk hy') (Nat.lt_of_lt_of_le hwk hb')]
      exact ds_left_irrel hb' hy' Y l r
    · rw [h, ds_both_gt (Nat.lt_of_lt_of_le hwk hy') (Nat.lt_of_lt_of_le hwk hb'),
          ds_both_gt (Nat.lt_of_lt_of_le huk hy') (Nat.lt_of_lt_of_le huk hb')]
      exact ds_left_irrel hb' hy' Z l r

/-- Mirror: `b, y ≤ rootKey t ≤ q` (min-side targets, max-side dive). -/

theorem divergeSuffix_splay_opposite_right (t : BinaryTree) (q b y : Nat)
    (hbst : IsBST t)
    (hq : rootKey t ≤ q) (hb : b ≤ rootKey t) (hy : y ≤ rootKey t) :
    divergeSuffix y b (splay t q) = divergeSuffix y b t := by
  cases t with
  | empty => rfl
  | node l k r =>
    rcases isBST_node_iff.mp hbst with ⟨_, hR, _, _⟩
    have hq' : k ≤ q := hq
    have hb' : b ≤ k := hb
    have hy' : y ≤ k := hy
    rcases splay_right_structure l r k q hR hq' with
      h | ⟨X, w, Y, hkw, h⟩ | ⟨X, w, Y, u, Z, hkw, hku, h⟩
    · rw [h]
    · rw [h, ds_both_lt (Nat.lt_of_le_of_lt hy' hkw) (Nat.lt_of_le_of_lt hb' hkw)]
      exact ds_right_irrel hb' hy' l Y r
    · rw [h, ds_both_lt (Nat.lt_of_le_of_lt hy' hkw) (Nat.lt_of_le_of_lt hb' hkw),
          ds_both_lt (Nat.lt_of_le_of_lt hy' hku) (Nat.lt_of_le_of_lt hb' hku)]
      exact ds_right_irrel hb' hy' l Z r

/-! ## (P2) COUNT COROLLARY — exact equality (constant 0, beating the asked-for +2)

The suffix lives strictly beyond the root (keys > k) while `searchPath q t` only
holds keys ≤ k, so enlarging the touched set by `searchPath q t` changes nothing. -/

theorem touchedCount_divergeSuffix_splay_opposite_left (t : BinaryTree) (q b y : Nat)
    (T : List Nat) (hbst : IsBST t)
    (hq : q ≤ rootKey t) (hb : rootKey t ≤ b) (hy : rootKey t ≤ y) :
    touchedCount (T ++ searchPath q t) (divergeSuffix y b (splay t q))
      = touchedCount T (divergeSuffix y b t) := by
  rw [divergeSuffix_splay_opposite_left t q b y hbst hq hb hy]
  apply touchedCount_congr
  intro z hz
  cases t with
  | empty => simp at hz
  | node l k r =>
    rcases isBST_node_iff.mp hbst with ⟨hL, hR, _, _⟩
    have hq' : q ≤ k := hq
    have hb' : k ≤ b := hb
    have hy' : k ≤ y := hy
    have hzk : k < z := by
      by_cases hyk : y = k
      · rw [ds_self hyk] at hz; simp at hz
      · have hky : k < y := Nat.lt_of_le_of_ne hy' (fun h => hyk h.symm)
        by_cases hbk : b = k
        · rw [ds_qroot_gt hbk hky] at hz
          exact mem_searchPath_forall hR hz
        · have hkb : k < b := Nat.lt_of_le_of_ne hb' (fun h => hbk h.symm)
          rw [ds_both_gt hky hkb] at hz
          exact mem_divergeSuffix_forall r hR z hz
    constructor
    · intro hzT'
      rcases List.mem_append.mp hzT' with h | h
      · exact h
      · have hle := searchPath_all_le_of_left hL hq' z h
        omega
    · intro h
      exact List.mem_append_left _ h

theorem touchedCount_divergeSuffix_splay_opposite_right (t : BinaryTree) (q b y : Nat)
    (T : List Nat) (hbst : IsBST t)
    (hq : rootKey t ≤ q) (hb : b ≤ rootKey t) (hy : y ≤ rootKey t) :
    touchedCount (T ++ searchPath q t) (divergeSuffix y b (splay t q))
      = touchedCount T (divergeSuffix y b t) := by
  rw [divergeSuffix_splay_opposite_right t q b y hbst hq hb hy]
  apply touchedCount_congr
  intro z hz
  cases t with
  | empty => simp at hz
  | node l k r =>
    rcases isBST_node_iff.mp hbst with ⟨hL, hR, _, _⟩
    have hq' : k ≤ q := hq
    have hb' : b ≤ k := hb
    have hy' : y ≤ k := hy
    have hzk : z < k := by
      by_cases hyk : y = k
      · rw [ds_self hyk] at hz; simp at hz
      · have hky : y < k := Nat.lt_of_le_of_ne hy' hyk
        by_cases hbk : b = k
        · rw [ds_qroot_lt hbk hky] at hz
          exact mem_searchPath_forall (p := fun x => x < k) hL hz
        · have hkb : b < k := Nat.lt_of_le_of_ne hb' hbk
          rw [ds_both_lt hky hkb] at hz
          exact mem_divergeSuffix_forall (p := fun x => x < k) l hL z hz
    constructor
    · intro hzT'
      rcases List.mem_append.mp hzT' with h | h
      · exact h
      · have hge := searchPath_all_ge_of_right hR hq' z h
        omega
    · intro h
      exact List.mem_append_left _ h

/-- (P2) in the literal "≤ + 2" form requested (immediate from the equality). -/

theorem touchedCount_divergeSuffix_splay_opposite_left_le (t : BinaryTree) (q b y : Nat)
    (T : List Nat) (hbst : IsBST t)
    (hq : q ≤ rootKey t) (hb : rootKey t ≤ b) (hy : rootKey t ≤ y) :
    touchedCount (T ++ searchPath q t) (divergeSuffix y b (splay t q))
      ≤ touchedCount T (divergeSuffix y b t) + 2 := by
  rw [touchedCount_divergeSuffix_splay_opposite_left t q b y T hbst hq hb hy]
  omega

theorem touchedCount_divergeSuffix_splay_opposite_right_le (t : BinaryTree) (q b y : Nat)
    (T : List Nat) (hbst : IsBST t)
    (hq : rootKey t ≤ q) (hb : b ≤ rootKey t) (hy : y ≤ rootKey t) :
    touchedCount (T ++ searchPath q t) (divergeSuffix y b (splay t q))
      ≤ touchedCount T (divergeSuffix y b t) + 2 := by
  rw [touchedCount_divergeSuffix_splay_opposite_right t q b y T hbst hq hb hy]
  omega

/-! ## Witnesses from the pinning harness

Non-trivial application: `t = node (node ∅ 0 ∅) 1 (node ∅ 2 (node ∅ 3 ∅))`, `q = 0`,
`b = 2`, `y = 3` — the splay rearranges the tree (zig at the root), yet the suffix `[3]`
is preserved verbatim.

Necessity of root-between: `t = node (node ∅ 1 (node ∅ 3 ∅)) 5 ∅`, `q = 0 ≤ b = 1`,
`q ≤ y = 3` but `b, y < rootKey t = 5`: the suffix changes from `[3]` to `[5, 3]`. -/

example :
    divergeSuffix 3 2
        (splay (.node (.node .empty 0 .empty) 1 (.node .empty 2 (.node .empty 3 .empty))) 0)
      = divergeSuffix 3 2
        (.node (.node .empty 0 .empty) 1 (.node .empty 2 (.node .empty 3 .empty))) := by
  decide

example :
    divergeSuffix 3 2
        (.node (.node .empty 0 .empty) 1 (.node .empty 2 (.node .empty 3 .empty)))
      = [3] := by decide

example :
    divergeSuffix 3 1 (splay (.node (.node .empty 1 (.node .empty 3 .empty)) 5 .empty) 0)
      ≠ divergeSuffix 3 1 (.node (.node .empty 1 (.node .empty 3 .empty)) 5 .empty) := by
  decide


-- ===== C3 same-side dive preservation =====
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

/-! ## splay preserves ForallTree (ported) -/

theorem splay_root_spec :
    ∀ (n : Nat) (t : BinaryTree), t.num_nodes ≤ n → ∀ (q : Nat), IsBST t →
      ∀ (A B : BinaryTree) (s : Nat), splay t q = .node A s B →
        s ∈ searchPath q t ∧ ∀ w ∈ searchPath q t, q < w → s ≤ w := by
  intro n
  induction n with
  | zero =>
    intro t ht q _ A B s hsp
    cases t with
    | empty =>
      have h0 : splay .empty q = .empty := rfl
      rw [h0] at hsp
      exact absurd hsp (fun h => nomatch h)
    | node l k r =>
      exfalso
      have hnn : (BinaryTree.node l k r).num_nodes = 1 + l.num_nodes + r.num_nodes := rfl
      omega
  | succ n ih =>
    intro t ht q hbst A B s hsp
    cases t with
    | empty =>
      have h0 : splay .empty q = .empty := rfl
      rw [h0] at hsp
      exact absurd hsp (fun h => nomatch h)
    | node l k r =>
      rcases isBST_node_iff.mp hbst with ⟨hFl, hFr, hbl, hbr⟩
      by_cases hqk : q = k
      · rw [splay_eq_of_eq hqk l r] at hsp
        injection hsp with h1 h2 h3
        subst h2
        refine ⟨?_, ?_⟩
        · rw [searchPath_node_self hqk]; exact List.mem_singleton.mpr rfl
        · intro w hw hqw
          rw [searchPath_node_self hqk] at hw
          simp only [List.mem_singleton] at hw
          omega
      · by_cases hqlt : q < k
        · cases l with
          | empty =>
            rw [splay_left_empty hqlt r] at hsp
            injection hsp with h1 h2 h3
            subst h2
            refine ⟨?_, ?_⟩
            · rw [searchPath_node_lt hqlt]; exact List.mem_cons_self
            · intro w hw hqw
              rw [searchPath_node_lt hqlt] at hw
              rcases List.mem_cons.mp hw with rfl | hw
              · omega
              · simp at hw
          | node ll lk lr =>
            rcases forallTree_node_iff.mp hFl with ⟨hFllk, hlkk, hFlrk⟩
            rcases isBST_node_iff.mp hbl with ⟨hFll, hFlr, hbll, hblr⟩
            have hpath : searchPath q (BinaryTree.node (BinaryTree.node ll lk lr) k r)
                = k :: searchPath q (BinaryTree.node ll lk lr) :=
              searchPath_node_lt hqlt _ _
            by_cases hqlk : q < lk
            · have hpath2 : searchPath q (BinaryTree.node ll lk lr)
                  = lk :: searchPath q ll := searchPath_node_lt hqlk _ _
              cases ll with
              | empty =>
                rw [splay_zig_ll_empty hqlt hqlk lr r] at hsp
                injection hsp with h1 h2 h3
                subst h2
                refine ⟨?_, ?_⟩
                · rw [hpath, hpath2]
                  exact List.mem_cons_of_mem _ (List.mem_cons_self)
                · intro w hw hqw
                  rw [hpath, hpath2] at hw
                  rcases List.mem_cons.mp hw with rfl | hw
                  · omega
                  · rcases List.mem_cons.mp hw with rfl | hw
                    · omega
                    · simp at hw
              | node a x c =>
                have hsz : (BinaryTree.node a x c).num_nodes ≤ n := by
                  have hnn : (BinaryTree.node (BinaryTree.node (BinaryTree.node a x c) lk lr)
                      k r).num_nodes
                      = 1 + (1 + (BinaryTree.node a x c).num_nodes + lr.num_nodes)
                        + r.num_nodes := rfl
                  omega
                cases hS : splay (BinaryTree.node a x c) q with
                | empty => exact absurd hS (splay_ne_empty a c x q)
                | node A0 s0 B0 =>
                  rw [splay_zigzig_shape (BinaryTree.node a x c) lr r A0 B0 lk k q s0
                        hqk hqlt hqlk (fun h => nomatch h) hS] at hsp
                  injection hsp with h1 h2 h3
                  subst h2
                  obtain ⟨hmem0, hmin0⟩ := ih (BinaryTree.node a x c) hsz q hbll A0 B0 s0 hS
                  have hs_lk : s0 < lk := by
                    have hF := splay_forallTree_kd (fun z => z < lk) (BinaryTree.node a x c) q hFll
                    rw [hS] at hF
                    exact (forallTree_node_iff.mp hF).2.1
                  refine ⟨?_, ?_⟩
                  · rw [hpath, hpath2]
                    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmem0)
                  · intro w hw hqw
                    rw [hpath, hpath2] at hw
                    rcases List.mem_cons.mp hw with rfl | hw
                    · omega
                    · rcases List.mem_cons.mp hw with rfl | hw
                      · omega
                      · exact hmin0 w hw hqw
            · by_cases hlkq : lk < q
              · have hpath2 : searchPath q (BinaryTree.node ll lk lr)
                    = lk :: searchPath q lr := searchPath_node_gt hlkq _ _
                cases lr with
                | empty =>
                  rw [splay_zig_lr_empty hqlt hlkq ll r] at hsp
                  injection hsp with h1 h2 h3
                  subst h2
                  refine ⟨?_, ?_⟩
                  · rw [hpath, hpath2]
                    exact List.mem_cons_of_mem _ (List.mem_cons_self)
                  · intro w hw hqw
                    rw [hpath, hpath2] at hw
                    rcases List.mem_cons.mp hw with rfl | hw
                    · omega
                    · rcases List.mem_cons.mp hw with rfl | hw
                      · omega
                      · simp at hw
                | node a x c =>
                  have hsz : (BinaryTree.node a x c).num_nodes ≤ n := by
                    have hnn : (BinaryTree.node (BinaryTree.node ll lk
                        (BinaryTree.node a x c)) k r).num_nodes
                        = 1 + (1 + ll.num_nodes + (BinaryTree.node a x c).num_nodes)
                          + r.num_nodes := rfl
                    omega
                  cases hS : splay (BinaryTree.node a x c) q with
                  | empty => exact absurd hS (splay_ne_empty a c x q)
                  | node A0 s0 B0 =>
                    rw [splay_zigzag_shape ll (BinaryTree.node a x c) r A0 B0 lk k q s0
                          hqk hqlt hlkq (fun h => nomatch h) hS] at hsp
                    injection hsp with h1 h2 h3
                    subst h2
                    obtain ⟨hmem0, hmin0⟩ := ih (BinaryTree.node a x c) hsz q hblr A0 B0 s0 hS
                    have hs_k : s0 < k := by
                      have hF := splay_forallTree_kd (fun z => z < k) (BinaryTree.node a x c) q hFlrk
                      rw [hS] at hF
                      exact (forallTree_node_iff.mp hF).2.1
                    refine ⟨?_, ?_⟩
                    · rw [hpath, hpath2]
                      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmem0)
                    · intro w hw hqw
                      rw [hpath, hpath2] at hw
                      rcases List.mem_cons.mp hw with rfl | hw
                      · omega
                      · rcases List.mem_cons.mp hw with rfl | hw
                        · omega
                        · exact hmin0 w hw hqw
              · -- q = lk: found at left child
                have hqlk_eq : q = lk := by omega
                rw [splay_zig_found hqlt hqlk hlkq ll lr r] at hsp
                injection hsp with h1 h2 h3
                subst h2
                have hpath2 : searchPath q (BinaryTree.node ll lk lr) = [lk] :=
                  searchPath_node_self hqlk_eq _ _
                refine ⟨?_, ?_⟩
                · rw [hpath, hpath2]
                  exact List.mem_cons_of_mem _ (List.mem_cons_self)
                · intro w hw hqw
                  rw [hpath, hpath2] at hw
                  rcases List.mem_cons.mp hw with rfl | hw
                  · omega
                  · simp only [List.mem_singleton] at hw
                    omega
        · have hklt : k < q := by omega
          cases r with
          | empty =>
            rw [splay_right_empty hklt l] at hsp
            injection hsp with h1 h2 h3
            subst h2
            refine ⟨?_, ?_⟩
            · rw [searchPath_node_gt hklt]; exact List.mem_cons_self
            · intro w hw hqw
              rw [searchPath_node_gt hklt] at hw
              rcases List.mem_cons.mp hw with rfl | hw
              · omega
              · simp at hw
          | node rl rk rr =>
            rcases forallTree_node_iff.mp hFr with ⟨hFrlk, hkrk, hFrrk⟩
            rcases isBST_node_iff.mp hbr with ⟨hFrl, hFrr, hbrl, hbrr⟩
            have hpath : searchPath q (BinaryTree.node l k (BinaryTree.node rl rk rr))
                = k :: searchPath q (BinaryTree.node rl rk rr) :=
              searchPath_node_gt hklt _ _
            by_cases hqrk : q < rk
            · have hpath2 : searchPath q (BinaryTree.node rl rk rr)
                  = rk :: searchPath q rl := searchPath_node_lt hqrk _ _
              cases rl with
              | empty =>
                rw [splay_zag_rl_empty hklt hqrk l rr] at hsp
                injection hsp with h1 h2 h3
                subst h2
                refine ⟨?_, ?_⟩
                · rw [hpath, hpath2]
                  exact List.mem_cons_of_mem _ (List.mem_cons_self)
                · intro w hw hqw
                  rw [hpath, hpath2] at hw
                  rcases List.mem_cons.mp hw with rfl | hw
                  · omega
                  · rcases List.mem_cons.mp hw with rfl | hw
                    · omega
                    · simp at hw
              | node a x c =>
                have hsz : (BinaryTree.node a x c).num_nodes ≤ n := by
                  have hnn : (BinaryTree.node l k (BinaryTree.node (BinaryTree.node a x c)
                      rk rr)).num_nodes
                      = 1 + l.num_nodes
                        + (1 + (BinaryTree.node a x c).num_nodes + rr.num_nodes) := rfl
                  omega
                cases hS : splay (BinaryTree.node a x c) q with
                | empty => exact absurd hS (splay_ne_empty a c x q)
                | node A0 s0 B0 =>
                  rw [splay_zagzig_shape l (BinaryTree.node a x c) rr A0 B0 rk k q s0
                        hqk hklt hqrk (fun h => nomatch h) hS] at hsp
                  injection hsp with h1 h2 h3
                  subst h2
                  obtain ⟨hmem0, hmin0⟩ := ih (BinaryTree.node a x c) hsz q hbrl A0 B0 s0 hS
                  have hs_rk : s0 < rk := by
                    have hF := splay_forallTree_kd (fun z => z < rk) (BinaryTree.node a x c) q hFrl
                    rw [hS] at hF
                    exact (forallTree_node_iff.mp hF).2.1
                  refine ⟨?_, ?_⟩
                  · rw [hpath, hpath2]
                    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmem0)
                  · intro w hw hqw
                    rw [hpath, hpath2] at hw
                    rcases List.mem_cons.mp hw with rfl | hw
                    · omega
                    · rcases List.mem_cons.mp hw with rfl | hw
                      · omega
                      · exact hmin0 w hw hqw
            · by_cases hrkq : rk < q
              · have hpath2 : searchPath q (BinaryTree.node rl rk rr)
                    = rk :: searchPath q rr := searchPath_node_gt hrkq _ _
                cases rr with
                | empty =>
                  rw [splay_zag_rr_empty hklt hrkq l rl] at hsp
                  injection hsp with h1 h2 h3
                  subst h2
                  refine ⟨?_, ?_⟩
                  · rw [hpath, hpath2]
                    exact List.mem_cons_of_mem _ (List.mem_cons_self)
                  · intro w hw hqw
                    rw [hpath, hpath2] at hw
                    rcases List.mem_cons.mp hw with rfl | hw
                    · omega
                    · rcases List.mem_cons.mp hw with rfl | hw
                      · omega
                      · simp at hw
                | node a x c =>
                  have hsz : (BinaryTree.node a x c).num_nodes ≤ n := by
                    have hnn : (BinaryTree.node l k (BinaryTree.node rl rk
                        (BinaryTree.node a x c))).num_nodes
                        = 1 + l.num_nodes
                          + (1 + rl.num_nodes + (BinaryTree.node a x c).num_nodes) := rfl
                    omega
                  cases hS : splay (BinaryTree.node a x c) q with
                  | empty => exact absurd hS (splay_ne_empty a c x q)
                  | node A0 s0 B0 =>
                    rw [splay_zagzag_shape l rl (BinaryTree.node a x c) A0 B0 rk k q s0
                          hqk hklt hrkq (fun h => nomatch h) hS] at hsp
                    injection hsp with h1 h2 h3
                    subst h2
                    obtain ⟨hmem0, hmin0⟩ := ih (BinaryTree.node a x c) hsz q hbrr A0 B0 s0 hS
                    have hrk_s : rk < s0 := by
                      have hF := splay_forallTree_kd (fun z => rk < z) (BinaryTree.node a x c) q hFrr
                      rw [hS] at hF
                      exact (forallTree_node_iff.mp hF).2.1
                    refine ⟨?_, ?_⟩
                    · rw [hpath, hpath2]
                      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hmem0)
                    · intro w hw hqw
                      rw [hpath, hpath2] at hw
                      rcases List.mem_cons.mp hw with rfl | hw
                      · omega
                      · rcases List.mem_cons.mp hw with rfl | hw
                        · omega
                        · exact hmin0 w hw hqw
              · -- q = rk: found at right child
                have hqrk_eq : q = rk := by omega
                rw [splay_zag_found hklt hqrk hrkq l rl rr] at hsp
                injection hsp with h1 h2 h3
                subst h2
                have hpath2 : searchPath q (BinaryTree.node rl rk rr) = [rk] :=
                  searchPath_node_self hqrk_eq _ _
                refine ⟨?_, ?_⟩
                · rw [hpath, hpath2]
                  exact List.mem_cons_of_mem _ (List.mem_cons_self)
                · intro w hw hqw
                  rw [hpath, hpath2] at hw
                  rcases List.mem_cons.mp hw with rfl | hw
                  · omega
                  · simp only [List.mem_singleton] at hw
                    omega


/-! ## (P1) VERBATIM PRESERVATION under interval-avoidance

If every node of q's search path lies outside the closed interval `[min b y, max b y]`
(equivalently: the y/b mutual divergence node is off q's search path), splaying `q`
preserves `divergeSuffix y b` verbatim.  No ordering of `q` versus `b, y` is needed. -/

theorem avoid_pair {w b y : Nat} (h : w < min b y ∨ max b y < w) :
    (w < b ∧ w < y) ∨ (b < w ∧ y < w) := by
  rcases h with h | h
  · exact Or.inl ⟨lt_of_lt_of_le h (Nat.min_le_left _ _), lt_of_lt_of_le h (Nat.min_le_right _ _)⟩
  · exact Or.inr ⟨lt_of_le_of_lt (Nat.le_max_left _ _) h, lt_of_le_of_lt (Nat.le_max_right _ _) h⟩

theorem ds_splay_avoid_aux :
    ∀ (n : Nat) (t : BinaryTree), t.num_nodes ≤ n → ∀ (q b y : Nat),
      IsBST t → (∀ w ∈ searchPath q t, w < min b y ∨ max b y < w) →
      divergeSuffix y b (splay t q) = divergeSuffix y b t := by
  intro n
  induction n with
  | zero =>
    intro t ht q b y _ _
    cases t with
    | empty => rfl
    | node l k r =>
      exfalso
      have hnn : (BinaryTree.node l k r).num_nodes = 1 + l.num_nodes + r.num_nodes := rfl
      omega
  | succ n ih =>
    intro t ht q b y hbst hav
    cases t with
    | empty => rfl
    | node l k r =>
      rcases isBST_node_iff.mp hbst with ⟨hFl, hFr, hbl, hbr⟩
      by_cases hqk : q = k
      · rw [splay_eq_of_eq hqk l r]
      · by_cases hqlt : q < k
        · -- ===== q descends LEFT =====
          have hpath : searchPath q (BinaryTree.node l k r) = k :: searchPath q l :=
            searchPath_node_lt hqlt _ _
          have hk_av := avoid_pair (hav k (by rw [hpath]; exact List.mem_cons_self))
          cases l with
          | empty => rw [splay_left_empty hqlt r]
          | node ll lk lr =>
            rcases forallTree_node_iff.mp hFl with ⟨hFllk, hlkk, hFlrk⟩
            rcases isBST_node_iff.mp hbl with ⟨hFll, hFlr, hbll, hblr⟩
            by_cases hqlk : q < lk
            · have hpath2 : searchPath q (BinaryTree.node ll lk lr) = lk :: searchPath q ll :=
                searchPath_node_lt hqlk _ _
              have hlk_av := avoid_pair (hav lk
                (by rw [hpath, hpath2]; exact List.mem_cons_of_mem _ List.mem_cons_self))
              cases ll with
              | empty =>
                -- zig with empty grandchild
                rw [splay_zig_ll_empty hqlt hqlk lr r]
                rcases hk_av with ⟨hkb, hky⟩ | ⟨hbk, hyk⟩
                · rw [ds_both_gt (by omega : lk < y) (by omega : lk < b),
                      ds_both_gt (by omega : k < y) (by omega : k < b),
                      ds_both_gt (by omega : k < y) (by omega : k < b)]
                · rcases hlk_av with ⟨hlkb, hlky⟩ | ⟨hblk, hylk⟩
                  · rw [ds_both_gt (by omega : lk < y) (by omega : lk < b),
                        ds_both_lt (by omega : y < k) (by omega : b < k),
                        ds_both_lt (by omega : y < k) (by omega : b < k),
                        ds_both_gt (by omega : lk < y) (by omega : lk < b)]
                  · rw [ds_both_lt (by omega : y < lk) (by omega : b < lk),
                        ds_both_lt (by omega : y < k) (by omega : b < k),
                        ds_both_lt (by omega : y < lk) (by omega : b < lk)]
              | node a x c =>
                -- zig-zig
                have hsz : (BinaryTree.node a x c).num_nodes ≤ n := by
                  have hnn : (BinaryTree.node (BinaryTree.node (BinaryTree.node a x c) lk lr)
                      k r).num_nodes
                      = 1 + (1 + (BinaryTree.node a x c).num_nodes + lr.num_nodes)
                        + r.num_nodes := rfl
                  omega
                cases hS : splay (BinaryTree.node a x c) q with
                | empty => exact absurd hS (splay_ne_empty a c x q)
                | node A0 s0 B0 =>
                  rw [splay_zigzig_shape (BinaryTree.node a x c) lr r A0 B0 lk k q s0
                        hqk hqlt hqlk (fun h => nomatch h) hS]
                  obtain ⟨hsmem, _⟩ := splay_root_spec (BinaryTree.node a x c).num_nodes
                    (BinaryTree.node a x c) (Nat.le_refl _) q hbll A0 B0 s0 hS
                  have hs_av := avoid_pair (hav s0
                    (by rw [hpath, hpath2]
                        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hsmem)))
                  have hs_lk : s0 < lk := by
                    have hF := splay_forallTree_kd (fun z => z < lk)
                      (BinaryTree.node a x c) q hFll
                    rw [hS] at hF
                    exact (forallTree_node_iff.mp hF).2.1
                  have hav_ll : ∀ w ∈ searchPath q (BinaryTree.node a x c),
                      w < min b y ∨ max b y < w := fun w hw => hav w
                    (by rw [hpath, hpath2]
                        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))
                  have ihll := ih (BinaryTree.node a x c) hsz q b y hbll hav_ll
                  rw [hS] at ihll
                  rcases hk_av with ⟨hkb, hky⟩ | ⟨hbk, hyk⟩
                  · rw [ds_both_gt (by omega : s0 < y) (by omega : s0 < b),
                        ds_both_gt (by omega : lk < y) (by omega : lk < b),
                        ds_both_gt (by omega : k < y) (by omega : k < b),
                        ds_both_gt (by omega : k < y) (by omega : k < b)]
                  · rcases hlk_av with ⟨hlkb, hlky⟩ | ⟨hblk, hylk⟩
                    · rw [ds_both_gt (by omega : s0 < y) (by omega : s0 < b),
                          ds_both_gt (by omega : lk < y) (by omega : lk < b),
                          ds_both_lt (by omega : y < k) (by omega : b < k),
                          ds_both_lt (by omega : y < k) (by omega : b < k),
                          ds_both_gt (by omega : lk < y) (by omega : lk < b)]
                    · rcases hs_av with ⟨hsb, hsy⟩ | ⟨hbs, hys⟩
                      · rw [ds_both_gt (by omega : s0 < y) (by omega : s0 < b)] at ihll
                        rw [ds_both_gt (by omega : s0 < y) (by omega : s0 < b),
                            ds_both_lt (by omega : y < lk) (by omega : b < lk),
                            ds_both_lt (by omega : y < k) (by omega : b < k),
                            ds_both_lt (by omega : y < lk) (by omega : b < lk)]
                        exact ihll
                      · rw [ds_both_lt (by omega : y < s0) (by omega : b < s0)] at ihll
                        rw [ds_both_lt (by omega : y < s0) (by omega : b < s0),
                            ds_both_lt (by omega : y < k) (by omega : b < k),
                            ds_both_lt (by omega : y < lk) (by omega : b < lk)]
                        exact ihll
            · by_cases hlkq : lk < q
              · have hpath2 : searchPath q (BinaryTree.node ll lk lr) = lk :: searchPath q lr :=
                  searchPath_node_gt hlkq _ _
                have hlk_av := avoid_pair (hav lk
                  (by rw [hpath, hpath2]; exact List.mem_cons_of_mem _ List.mem_cons_self))
                cases lr with
                | empty =>
                  -- zig with empty grandchild (right)
                  rw [splay_zig_lr_empty hqlt hlkq ll r]
                  rcases hk_av with ⟨hkb, hky⟩ | ⟨hbk, hyk⟩
                  · rw [ds_both_gt (by omega : lk < y) (by omega : lk < b),
                        ds_both_gt (by omega : k < y) (by omega : k < b),
                        ds_both_gt (by omega : k < y) (by omega : k < b)]
                  · rcases hlk_av with ⟨hlkb, hlky⟩ | ⟨hblk, hylk⟩
                    · rw [ds_both_gt (by omega : lk < y) (by omega : lk < b),
                          ds_both_lt (by omega : y < k) (by omega : b < k),
                          ds_both_lt (by omega : y < k) (by omega : b < k),
                          ds_both_gt (by omega : lk < y) (by omega : lk < b)]
                    · rw [ds_both_lt (by omega : y < lk) (by omega : b < lk),
                          ds_both_lt (by omega : y < k) (by omega : b < k),
                          ds_both_lt (by omega : y < lk) (by omega : b < lk)]
                | node a x c =>
                  -- zig-zag
                  have hsz : (BinaryTree.node a x c).num_nodes ≤ n := by
                    have hnn : (BinaryTree.node (BinaryTree.node ll lk
                        (BinaryTree.node a x c)) k r).num_nodes
                        = 1 + (1 + ll.num_nodes + (BinaryTree.node a x c).num_nodes)
                          + r.num_nodes := rfl
                    omega
                  cases hS : splay (BinaryTree.node a x c) q with
                  | empty => exact absurd hS (splay_ne_empty a c x q)
                  | node A0 s0 B0 =>
                    rw [splay_zigzag_shape ll (BinaryTree.node a x c) r A0 B0 lk k q s0
                          hqk hqlt hlkq (fun h => nomatch h) hS]
                    obtain ⟨hsmem, _⟩ := splay_root_spec (BinaryTree.node a x c).num_nodes
                      (BinaryTree.node a x c) (Nat.le_refl _) q hblr A0 B0 s0 hS
                    have hs_av := avoid_pair (hav s0
                      (by rw [hpath, hpath2]
                          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hsmem)))
                    have hlk_s : lk < s0 := by
                      have hF := splay_forallTree_kd (fun z => lk < z)
                        (BinaryTree.node a x c) q hFlr
                      rw [hS] at hF
                      exact (forallTree_node_iff.mp hF).2.1
                    have hs_k : s0 < k := by
                      have hF := splay_forallTree_kd (fun z => z < k)
                        (BinaryTree.node a x c) q hFlrk
                      rw [hS] at hF
                      exact (forallTree_node_iff.mp hF).2.1
                    have hav_lr : ∀ w ∈ searchPath q (BinaryTree.node a x c),
                        w < min b y ∨ max b y < w := fun w hw => hav w
                      (by rw [hpath, hpath2]
                          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))
                    have ihlr := ih (BinaryTree.node a x c) hsz q b y hblr hav_lr
                    rw [hS] at ihlr
                    rcases hk_av with ⟨hkb, hky⟩ | ⟨hbk, hyk⟩
                    · rw [ds_both_gt (by omega : s0 < y) (by omega : s0 < b),
                          ds_both_gt (by omega : k < y) (by omega : k < b),
                          ds_both_gt (by omega : k < y) (by omega : k < b)]
                    · rcases hlk_av with ⟨hlkb, hlky⟩ | ⟨hblk, hylk⟩
                      · rcases hs_av with ⟨hsb, hsy⟩ | ⟨hbs, hys⟩
                        · rw [ds_both_gt (by omega : s0 < y) (by omega : s0 < b)] at ihlr
                          rw [ds_both_gt (by omega : s0 < y) (by omega : s0 < b),
                              ds_both_lt (by omega : y < k) (by omega : b < k),
                              ds_both_lt (by omega : y < k) (by omega : b < k),
                              ds_both_gt (by omega : lk < y) (by omega : lk < b)]
                          exact ihlr
                        · rw [ds_both_lt (by omega : y < s0) (by omega : b < s0)] at ihlr
                          rw [ds_both_lt (by omega : y < s0) (by omega : b < s0),
                              ds_both_gt (by omega : lk < y) (by omega : lk < b),
                              ds_both_lt (by omega : y < k) (by omega : b < k),
                              ds_both_gt (by omega : lk < y) (by omega : lk < b)]
                          exact ihlr
                      · rw [ds_both_lt (by omega : y < s0) (by omega : b < s0),
                            ds_both_lt (by omega : y < lk) (by omega : b < lk),
                            ds_both_lt (by omega : y < k) (by omega : b < k),
                            ds_both_lt (by omega : y < lk) (by omega : b < lk)]
              · -- q = lk: found at left child, single zig
                have hpath2 : searchPath q (BinaryTree.node ll lk lr) = [lk] :=
                  searchPath_node_self (by omega) _ _
                have hlk_av := avoid_pair (hav lk
                  (by rw [hpath, hpath2]; exact List.mem_cons_of_mem _ List.mem_cons_self))
                rw [splay_zig_found hqlt hqlk hlkq ll lr r]
                rcases hk_av with ⟨hkb, hky⟩ | ⟨hbk, hyk⟩
                · rw [ds_both_gt (by omega : lk < y) (by omega : lk < b),
                      ds_both_gt (by omega : k < y) (by omega : k < b),
                      ds_both_gt (by omega : k < y) (by omega : k < b)]
                · rcases hlk_av with ⟨hlkb, hlky⟩ | ⟨hblk, hylk⟩
                  · rw [ds_both_gt (by omega : lk < y) (by omega : lk < b),
                        ds_both_lt (by omega : y < k) (by omega : b < k),
                        ds_both_lt (by omega : y < k) (by omega : b < k),
                        ds_both_gt (by omega : lk < y) (by omega : lk < b)]
                  · rw [ds_both_lt (by omega : y < lk) (by omega : b < lk),
                        ds_both_lt (by omega : y < k) (by omega : b < k),
                        ds_both_lt (by omega : y < lk) (by omega : b < lk)]
        · -- ===== q descends RIGHT =====
          have hklt : k < q := by omega
          have hpath : searchPath q (BinaryTree.node l k r) = k :: searchPath q r :=
            searchPath_node_gt hklt _ _
          have hk_av := avoid_pair (hav k (by rw [hpath]; exact List.mem_cons_self))
          cases r with
          | empty => rw [splay_right_empty hklt l]
          | node rl rk rr =>
            rcases forallTree_node_iff.mp hFr with ⟨hFrlk, hkrk, hFrrk⟩
            rcases isBST_node_iff.mp hbr with ⟨hFrl, hFrr, hbrl, hbrr⟩
            by_cases hqrk : q < rk
            · have hpath2 : searchPath q (BinaryTree.node rl rk rr) = rk :: searchPath q rl :=
                searchPath_node_lt hqrk _ _
              have hrk_av := avoid_pair (hav rk
                (by rw [hpath, hpath2]; exact List.mem_cons_of_mem _ List.mem_cons_self))
              cases rl with
              | empty =>
                -- zag with empty grandchild
                rw [splay_zag_rl_empty hklt hqrk l rr]
                rcases hk_av with ⟨hkb, hky⟩ | ⟨hbk, hyk⟩
                · rcases hrk_av with ⟨hrkb, hrky⟩ | ⟨hbrk, hyrk⟩
                  · rw [ds_both_gt (by omega : rk < y) (by omega : rk < b),
                        ds_both_gt (by omega : k < y) (by omega : k < b),
                        ds_both_gt (by omega : rk < y) (by omega : rk < b)]
                  · rw [ds_both_lt (by omega : y < rk) (by omega : b < rk),
                        ds_both_gt (by omega : k < y) (by omega : k < b),
                        ds_both_gt (by omega : k < y) (by omega : k < b),
                        ds_both_lt (by omega : y < rk) (by omega : b < rk)]
                · rw [ds_both_lt (by omega : y < rk) (by omega : b < rk),
                      ds_both_lt (by omega : y < k) (by omega : b < k),
                      ds_both_lt (by omega : y < k) (by omega : b < k)]
              | node a x c =>
                -- zag-zig
                have hsz : (BinaryTree.node a x c).num_nodes ≤ n := by
                  have hnn : (BinaryTree.node l k (BinaryTree.node (BinaryTree.node a x c)
                      rk rr)).num_nodes
                      = 1 + l.num_nodes
                        + (1 + (BinaryTree.node a x c).num_nodes + rr.num_nodes) := rfl
                  omega
                cases hS : splay (BinaryTree.node a x c) q with
                | empty => exact absurd hS (splay_ne_empty a c x q)
                | node A0 s0 B0 =>
                  rw [splay_zagzig_shape l (BinaryTree.node a x c) rr A0 B0 rk k q s0
                        hqk hklt hqrk (fun h => nomatch h) hS]
                  obtain ⟨hsmem, _⟩ := splay_root_spec (BinaryTree.node a x c).num_nodes
                    (BinaryTree.node a x c) (Nat.le_refl _) q hbrl A0 B0 s0 hS
                  have hs_av := avoid_pair (hav s0
                    (by rw [hpath, hpath2]
                        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hsmem)))
                  have hk_s : k < s0 := by
                    have hF := splay_forallTree_kd (fun z => k < z)
                      (BinaryTree.node a x c) q hFrlk
                    rw [hS] at hF
                    exact (forallTree_node_iff.mp hF).2.1
                  have hs_rk : s0 < rk := by
                    have hF := splay_forallTree_kd (fun z => z < rk)
                      (BinaryTree.node a x c) q hFrl
                    rw [hS] at hF
                    exact (forallTree_node_iff.mp hF).2.1
                  have hav_rl : ∀ w ∈ searchPath q (BinaryTree.node a x c),
                      w < min b y ∨ max b y < w := fun w hw => hav w
                    (by rw [hpath, hpath2]
                        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))
                  have ihrl := ih (BinaryTree.node a x c) hsz q b y hbrl hav_rl
                  rw [hS] at ihrl
                  rcases hk_av with ⟨hkb, hky⟩ | ⟨hbk, hyk⟩
                  · rcases hrk_av with ⟨hrkb, hrky⟩ | ⟨hbrk, hyrk⟩
                    · rw [ds_both_gt (by omega : s0 < y) (by omega : s0 < b),
                          ds_both_gt (by omega : rk < y) (by omega : rk < b),
                          ds_both_gt (by omega : k < y) (by omega : k < b),
                          ds_both_gt (by omega : rk < y) (by omega : rk < b)]
                    · rcases hs_av with ⟨hsb, hsy⟩ | ⟨hbs, hys⟩
                      · rw [ds_both_gt (by omega : s0 < y) (by omega : s0 < b)] at ihrl
                        rw [ds_both_gt (by omega : s0 < y) (by omega : s0 < b),
                            ds_both_lt (by omega : y < rk) (by omega : b < rk),
                            ds_both_gt (by omega : k < y) (by omega : k < b),
                            ds_both_lt (by omega : y < rk) (by omega : b < rk)]
                        exact ihrl
                      · rw [ds_both_lt (by omega : y < s0) (by omega : b < s0)] at ihrl
                        rw [ds_both_lt (by omega : y < s0) (by omega : b < s0),
                            ds_both_gt (by omega : k < y) (by omega : k < b),
                            ds_both_gt (by omega : k < y) (by omega : k < b),
                            ds_both_lt (by omega : y < rk) (by omega : b < rk)]
                        exact ihrl
                  · rw [ds_both_lt (by omega : y < s0) (by omega : b < s0),
                        ds_both_lt (by omega : y < k) (by omega : b < k),
                        ds_both_lt (by omega : y < k) (by omega : b < k)]
            · by_cases hrkq : rk < q
              · have hpath2 : searchPath q (BinaryTree.node rl rk rr) = rk :: searchPath q rr :=
                  searchPath_node_gt hrkq _ _
                have hrk_av := avoid_pair (hav rk
                  (by rw [hpath, hpath2]; exact List.mem_cons_of_mem _ List.mem_cons_self))
                cases rr with
                | empty =>
                  -- zag with empty grandchild (right)
                  rw [splay_zag_rr_empty hklt hrkq l rl]
                  rcases hk_av with ⟨hkb, hky⟩ | ⟨hbk, hyk⟩
                  · rcases hrk_av with ⟨hrkb, hrky⟩ | ⟨hbrk, hyrk⟩
                    · rw [ds_both_gt (by omega : rk < y) (by omega : rk < b),
                          ds_both_gt (by omega : k < y) (by omega : k < b),
                          ds_both_gt (by omega : rk < y) (by omega : rk < b)]
                    · rw [ds_both_lt (by omega : y < rk) (by omega : b < rk),
                          ds_both_gt (by omega : k < y) (by omega : k < b),
                          ds_both_gt (by omega : k < y) (by omega : k < b),
                          ds_both_lt (by omega : y < rk) (by omega : b < rk)]
                  · rw [ds_both_lt (by omega : y < rk) (by omega : b < rk),
                        ds_both_lt (by omega : y < k) (by omega : b < k),
                        ds_both_lt (by omega : y < k) (by omega : b < k)]
                | node a x c =>
                  -- zag-zag
                  have hsz : (BinaryTree.node a x c).num_nodes ≤ n := by
                    have hnn : (BinaryTree.node l k (BinaryTree.node rl rk
                        (BinaryTree.node a x c))).num_nodes
                        = 1 + l.num_nodes
                          + (1 + rl.num_nodes + (BinaryTree.node a x c).num_nodes) := rfl
                    omega
                  cases hS : splay (BinaryTree.node a x c) q with
                  | empty => exact absurd hS (splay_ne_empty a c x q)
                  | node A0 s0 B0 =>
                    rw [splay_zagzag_shape l rl (BinaryTree.node a x c) A0 B0 rk k q s0
                          hqk hklt hrkq (fun h => nomatch h) hS]
                    obtain ⟨hsmem, _⟩ := splay_root_spec (BinaryTree.node a x c).num_nodes
                      (BinaryTree.node a x c) (Nat.le_refl _) q hbrr A0 B0 s0 hS
                    have hs_av := avoid_pair (hav s0
                      (by rw [hpath, hpath2]
                          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hsmem)))
                    have hrk_s : rk < s0 := by
                      have hF := splay_forallTree_kd (fun z => rk < z)
                        (BinaryTree.node a x c) q hFrr
                      rw [hS] at hF
                      exact (forallTree_node_iff.mp hF).2.1
                    have hav_rr : ∀ w ∈ searchPath q (BinaryTree.node a x c),
                        w < min b y ∨ max b y < w := fun w hw => hav w
                      (by rw [hpath, hpath2]
                          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))
                    have ihrr := ih (BinaryTree.node a x c) hsz q b y hbrr hav_rr
                    rw [hS] at ihrr
                    rcases hk_av with ⟨hkb, hky⟩ | ⟨hbk, hyk⟩
                    · rcases hrk_av with ⟨hrkb, hrky⟩ | ⟨hbrk, hyrk⟩
                      · rcases hs_av with ⟨hsb, hsy⟩ | ⟨hbs, hys⟩
                        · rw [ds_both_gt (by omega : s0 < y) (by omega : s0 < b)] at ihrr
                          rw [ds_both_gt (by omega : s0 < y) (by omega : s0 < b),
                              ds_both_gt (by omega : k < y) (by omega : k < b),
                              ds_both_gt (by omega : rk < y) (by omega : rk < b)]
                          exact ihrr
                        · rw [ds_both_lt (by omega : y < s0) (by omega : b < s0)] at ihrr
                          rw [ds_both_lt (by omega : y < s0) (by omega : b < s0),
                              ds_both_gt (by omega : rk < y) (by omega : rk < b),
                              ds_both_gt (by omega : k < y) (by omega : k < b),
                              ds_both_gt (by omega : rk < y) (by omega : rk < b)]
                          exact ihrr
                      · rw [ds_both_lt (by omega : y < s0) (by omega : b < s0),
                            ds_both_lt (by omega : y < rk) (by omega : b < rk),
                            ds_both_gt (by omega : k < y) (by omega : k < b),
                            ds_both_gt (by omega : k < y) (by omega : k < b),
                            ds_both_lt (by omega : y < rk) (by omega : b < rk)]
                    · rw [ds_both_lt (by omega : y < s0) (by omega : b < s0),
                          ds_both_lt (by omega : y < rk) (by omega : b < rk),
                          ds_both_lt (by omega : y < k) (by omega : b < k),
                          ds_both_lt (by omega : y < k) (by omega : b < k)]
              · -- q = rk: found at right child, single zag
                have hpath2 : searchPath q (BinaryTree.node rl rk rr) = [rk] :=
                  searchPath_node_self (by omega) _ _
                have hrk_av := avoid_pair (hav rk
                  (by rw [hpath, hpath2]; exact List.mem_cons_of_mem _ List.mem_cons_self))
                rw [splay_zag_found hklt hqrk hrkq l rl rr]
                rcases hk_av with ⟨hkb, hky⟩ | ⟨hbk, hyk⟩
                · rcases hrk_av with ⟨hrkb, hrky⟩ | ⟨hbrk, hyrk⟩
                  · rw [ds_both_gt (by omega : rk < y) (by omega : rk < b),
                        ds_both_gt (by omega : k < y) (by omega : k < b),
                        ds_both_gt (by omega : rk < y) (by omega : rk < b)]
                  · rw [ds_both_lt (by omega : y < rk) (by omega : b < rk),
                        ds_both_gt (by omega : k < y) (by omega : k < b),
                        ds_both_gt (by omega : k < y) (by omega : k < b),
                        ds_both_lt (by omega : y < rk) (by omega : b < rk)]
                · rw [ds_both_lt (by omega : y < rk) (by omega : b < rk),
                      ds_both_lt (by omega : y < k) (by omega : b < k),
                      ds_both_lt (by omega : y < k) (by omega : b < k)]

/-- (P1) headline: if q's search path avoids the closed interval `[min b y, max b y]`
(equivalently: the mutual y/b divergence node lies OFF q's search path, in a cargo
subtree), then splaying `q` preserves the divergence suffix VERBATIM.
No ordering between `q` and `b, y` is required. -/

theorem divergeSuffix_splay_of_avoid (q b y : Nat) (t : BinaryTree) (hbst : IsBST t)
    (hav : ∀ w ∈ searchPath q t, w < min b y ∨ max b y < w) :
    divergeSuffix y b (splay t q) = divergeSuffix y b t :=
  ds_splay_avoid_aux t.num_nodes t (Nat.le_refl _) q b y hbst hav

/-! ## Canonical-order disjointness: under `q ≤ b ≤ y` the suffix avoids q's path -/

theorem divergeSuffix_disjoint_dive :
    ∀ (t : BinaryTree), IsBST t → ∀ (q b y : Nat), q ≤ b → b ≤ y →
      ∀ z ∈ divergeSuffix y b t, z ∉ searchPath q t := by
  intro t
  induction t with
  | empty => intro _ q b y _ _ z hz; simp at hz
  | node l k r ihl ihr =>
    intro hbst q b y hqb hby z hz
    rcases isBST_node_iff.mp hbst with ⟨hFl, hFr, hbl, hbr⟩
    by_cases hyk : y = k
    · rw [ds_self hyk] at hz; simp at hz
    · by_cases hbk : b = k
      · have hky : k < y := by omega
        rw [ds_qroot_gt hbk hky] at hz
        have hkz : k < z := mem_searchPath_forall hFr hz
        intro hmem
        by_cases hqk : q = k
        · rw [searchPath_node_self hqk] at hmem
          simp only [List.mem_singleton] at hmem
          omega
        · have hqlt : q < k := by omega
          rw [searchPath_node_lt hqlt] at hmem
          rcases List.mem_cons.mp hmem with rfl | hmem
          · omega
          · have := mem_searchPath_forall (p := fun u => u < k) hFl hmem
            omega
      · by_cases hkb : k < b
        · have hky : k < y := by omega
          rw [ds_both_gt hky hkb] at hz
          have hkz : k < z := mem_divergeSuffix_forall r hFr z hz
          intro hmem
          by_cases hqk : q = k
          · rw [searchPath_node_self hqk] at hmem
            simp only [List.mem_singleton] at hmem
            omega
          · by_cases hqlt : q < k
            · rw [searchPath_node_lt hqlt] at hmem
              rcases List.mem_cons.mp hmem with rfl | hmem
              · omega
              · have := mem_searchPath_forall (p := fun u => u < k) hFl hmem
                omega
            · have hklt : k < q := by omega
              rw [searchPath_node_gt hklt] at hmem
              rcases List.mem_cons.mp hmem with rfl | hmem
              · omega
              · exact ihr hbr q b y hqb hby z hz hmem
        · have hbk3 : b < k := by omega
          have hqlt : q < k := by omega
          by_cases hyk2 : y < k
          · rw [ds_both_lt hyk2 hbk3] at hz
            have hzk : z < k := mem_divergeSuffix_forall l hFl z hz
            intro hmem
            rw [searchPath_node_lt hqlt] at hmem
            rcases List.mem_cons.mp hmem with rfl | hmem
            · omega
            · exact ihl hbl q b y hqb hby z hz hmem
          · have hky : k < y := by omega
            rw [ds_div_gt hky hbk3] at hz
            have hkz : k < z := mem_searchPath_forall hFr hz
            intro hmem
            rw [searchPath_node_lt hqlt] at hmem
            rcases List.mem_cons.mp hmem with rfl | hmem
            · omega
            · have := mem_searchPath_forall (p := fun u => u < k) hFl hmem
              omega

/-! ## (P2) SAME-SIDE DIVE: the divergence suffix gains at most ONE on-path cons -/

theorem ds_splay_dive_aux :
    ∀ (n : Nat) (t : BinaryTree), t.num_nodes ≤ n → ∀ (q b y : Nat),
      IsBST t → q ≤ b → b ≤ y → b ∉ searchPath q t →
      (∃ w ∈ searchPath q t, q < w ∧ w ≤ b) →
      divergeSuffix y b (splay t q) = divergeSuffix y b t
      ∨ ∃ x ∈ searchPath q t, divergeSuffix y b (splay t q) = x :: divergeSuffix y b t := by
  intro n
  induction n with
  | zero =>
    intro t ht q b y _ _ _ _ _
    cases t with
    | empty => exact Or.inl rfl
    | node l k r =>
      exfalso
      have hnn : (BinaryTree.node l k r).num_nodes = 1 + l.num_nodes + r.num_nodes := rfl
      omega
  | succ n ih =>
    intro t ht q b y hbst hqb hby hboff hw
    cases t with
    | empty => exact Or.inl rfl
    | node l k r =>
      rcases isBST_node_iff.mp hbst with ⟨hFl, hFr, hbl, hbr⟩
      obtain ⟨w, hwmem, hqw, hwb⟩ := hw
      by_cases hqk : q = k
      · exfalso
        rw [searchPath_node_self hqk] at hwmem
        simp only [List.mem_singleton] at hwmem
        omega
      · by_cases hqlt : q < k
        · -- ===== q descends LEFT =====
          have hpath : searchPath q (BinaryTree.node l k r) = k :: searchPath q l :=
            searchPath_node_lt hqlt _ _
          rw [hpath] at hwmem hboff
          simp only [List.mem_cons, not_or] at hboff
          obtain ⟨hbnk, hbnl⟩ := hboff
          cases l with
          | empty => exact Or.inl (by rw [splay_left_empty hqlt r])
          | node ll lk lr =>
            rcases forallTree_node_iff.mp hFl with ⟨hFllk, hlkk, hFlrk⟩
            rcases isBST_node_iff.mp hbl with ⟨hFll, hFlr, hbll, hblr⟩
            by_cases hqlk : q < lk
            · have hpath2 : searchPath q (BinaryTree.node ll lk lr) = lk :: searchPath q ll :=
                searchPath_node_lt hqlk _ _
              rw [hpath2] at hwmem hbnl
              simp only [List.mem_cons, not_or] at hbnl
              obtain ⟨hbnlk, hbnll⟩ := hbnl
              cases ll with
              | empty =>
                -- zig with empty grandchild: always verbatim here
                have hlkb : lk < b := by
                  rcases List.mem_cons.mp hwmem with rfl | h1
                  · omega
                  · rcases List.mem_cons.mp h1 with rfl | h2
                    · omega
                    · simp at h2
                refine Or.inl ?_
                rw [splay_zig_ll_empty hqlt hqlk lr r]
                by_cases hbk2 : k < b
                · rw [ds_both_gt (by omega : lk < y) (by omega : lk < b),
                      ds_both_gt (by omega : k < y) (by omega : k < b),
                      ds_both_gt (by omega : k < y) (by omega : k < b)]
                · have hbk3 : b < k := by omega
                  by_cases hyk : y < k
                  · rw [ds_both_gt (by omega : lk < y) (by omega : lk < b),
                        ds_both_lt (by omega : y < k) (by omega : b < k),
                        ds_both_lt (by omega : y < k) (by omega : b < k),
                        ds_both_gt (by omega : lk < y) (by omega : lk < b)]
                  · by_cases hyk2 : y = k
                    · rw [ds_both_gt (by omega : lk < y) (by omega : lk < b),
                          ds_self hyk2, ds_self hyk2]
                    · rw [ds_both_gt (by omega : lk < y) (by omega : lk < b),
                          ds_div_gt (by omega : k < y) (by omega : b < k),
                          ds_div_gt (by omega : k < y) (by omega : b < k)]
              | node a x c =>
                -- zig-zig
                have hsz : (BinaryTree.node a x c).num_nodes ≤ n := by
                  have hnn : (BinaryTree.node (BinaryTree.node (BinaryTree.node a x c) lk lr)
                      k r).num_nodes
                      = 1 + (1 + (BinaryTree.node a x c).num_nodes + lr.num_nodes)
                        + r.num_nodes := rfl
                  omega
                cases hS : splay (BinaryTree.node a x c) q with
                | empty => exact absurd hS (splay_ne_empty a c x q)
                | node A0 s0 B0 =>
                  have hShape := splay_zigzig_shape (BinaryTree.node a x c) lr r A0 B0 lk k q s0
                    hqk hqlt hqlk (fun h => nomatch h) hS
                  obtain ⟨hsmem, hsmin⟩ := splay_root_spec (BinaryTree.node a x c).num_nodes
                    (BinaryTree.node a x c) (Nat.le_refl _) q hbll A0 B0 s0 hS
                  have hs_lk : s0 < lk := by
                    have hF := splay_forallTree_kd (fun z => z < lk)
                      (BinaryTree.node a x c) q hFll
                    rw [hS] at hF
                    exact (forallTree_node_iff.mp hF).2.1
                  by_cases hbk2 : k < b
                  · refine Or.inl ?_
                    rw [hShape,
                        ds_both_gt (by omega : s0 < y) (by omega : s0 < b),
                        ds_both_gt (by omega : lk < y) (by omega : lk < b),
                        ds_both_gt (by omega : k < y) (by omega : k < b),
                        ds_both_gt (by omega : k < y) (by omega : k < b)]
                  · have hbk3 : b < k := by omega
                    by_cases hblk2 : lk < b
                    · -- b ∈ (lk, k): always verbatim
                      refine Or.inl ?_
                      by_cases hyk : y < k
                      · rw [hShape,
                            ds_both_gt (by omega : s0 < y) (by omega : s0 < b),
                            ds_both_gt (by omega : lk < y) (by omega : lk < b),
                            ds_both_lt (by omega : y < k) (by omega : b < k),
                            ds_both_lt (by omega : y < k) (by omega : b < k),
                            ds_both_gt (by omega : lk < y) (by omega : lk < b)]
                      · by_cases hyk2 : y = k
                        · rw [hShape,
                              ds_both_gt (by omega : s0 < y) (by omega : s0 < b),
                              ds_both_gt (by omega : lk < y) (by omega : lk < b),
                              ds_self hyk2, ds_self hyk2]
                        · rw [hShape,
                              ds_both_gt (by omega : s0 < y) (by omega : s0 < b),
                              ds_both_gt (by omega : lk < y) (by omega : lk < b),
                              ds_div_gt (by omega : k < y) (by omega : b < k),
                              ds_div_gt (by omega : k < y) (by omega : b < k)]
                    · -- b < lk: the witness must be deep, so s0 < b
                      have hblk3 : b < lk := by omega
                      have hwll : w ∈ searchPath q (BinaryTree.node a x c) := by
                        rcases List.mem_cons.mp hwmem with rfl | h1
                        · exfalso; omega
                        · rcases List.mem_cons.mp h1 with rfl | h2
                          · exfalso; omega
                          · exact h2
                      have hsb : s0 < b := by
                        have h1 : s0 ≤ w := hsmin w hwll hqw
                        have h2 : b ≠ s0 := fun h => hbnll (h ▸ hsmem)
                        omega
                      by_cases hylk : y < lk
                      · -- both below lk: recurse
                        have ihll := ih (BinaryTree.node a x c) hsz q b y hbll hqb hby hbnll
                          ⟨w, hwll, hqw, hwb⟩
                        rw [hS, ds_both_gt (by omega : s0 < y) (by omega : s0 < b)] at ihll
                        rw [hShape,
                            ds_both_gt (by omega : s0 < y) (by omega : s0 < b),
                            ds_both_lt (by omega : y < lk) (by omega : b < lk),
                            ds_both_lt (by omega : y < k) (by omega : b < k),
                            ds_both_lt (by omega : y < lk) (by omega : b < lk)]
                        rcases ihll with h | ⟨x0, hx0, hxe⟩
                        · exact Or.inl h
                        · refine Or.inr ⟨x0, ?_, hxe⟩
                          rw [hpath, hpath2]
                          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx0)
                      · by_cases hylk2 : y = lk
                        · refine Or.inl ?_
                          rw [hShape,
                              ds_both_gt (by omega : s0 < y) (by omega : s0 < b),
                              ds_self hylk2,
                              ds_both_lt (by omega : y < k) (by omega : b < k),
                              ds_self hylk2]
                        · have hlky : lk < y := by omega
                          by_cases hyk : y < k
                          · -- CONS k: lk < y < k
                            refine Or.inr ⟨k, by rw [hpath]; exact List.mem_cons_self, ?_⟩
                            rw [hShape,
                                ds_both_gt (by omega : s0 < y) (by omega : s0 < b),
                                ds_div_gt (by omega : lk < y) (by omega : b < lk),
                                searchPath_node_lt hyk,
                                ds_both_lt (by omega : y < k) (by omega : b < k),
                                ds_div_gt (by omega : lk < y) (by omega : b < lk)]
                          · by_cases hyk2 : y = k
                            · -- CONS k: y = k
                              refine Or.inr ⟨k, by rw [hpath]; exact List.mem_cons_self, ?_⟩
                              rw [hShape,
                                  ds_both_gt (by omega : s0 < y) (by omega : s0 < b),
                                  ds_div_gt (by omega : lk < y) (by omega : b < lk),
                                  searchPath_node_self hyk2,
                                  ds_self hyk2]
                            · -- CONS k: y > k
                              have hky : k < y := by omega
                              refine Or.inr ⟨k, by rw [hpath]; exact List.mem_cons_self, ?_⟩
                              rw [hShape,
                                  ds_both_gt (by omega : s0 < y) (by omega : s0 < b),
                                  ds_div_gt (by omega : lk < y) (by omega : b < lk),
                                  searchPath_node_gt hky,
                                  ds_div_gt (by omega : k < y) (by omega : b < k)]
            · by_cases hlkq : lk < q
              · have hpath2 : searchPath q (BinaryTree.node ll lk lr) = lk :: searchPath q lr :=
                  searchPath_node_gt hlkq _ _
                rw [hpath2] at hwmem hbnl
                simp only [List.mem_cons, not_or] at hbnl
                obtain ⟨hbnlk, hbnlr⟩ := hbnl
                have hlkb : lk < b := by omega
                cases lr with
                | empty =>
                  -- zig (lr empty): witness forces k < b; always verbatim
                  have hkb : k < b := by
                    rcases List.mem_cons.mp hwmem with rfl | h1
                    · omega
                    · rcases List.mem_cons.mp h1 with rfl | h2
                      · exfalso; omega
                      · simp at h2
                  refine Or.inl ?_
                  rw [splay_zig_lr_empty hqlt hlkq ll r,
                      ds_both_gt (by omega : lk < y) (by omega : lk < b),
                      ds_both_gt (by omega : k < y) (by omega : k < b),
                      ds_both_gt (by omega : k < y) (by omega : k < b)]
                | node a x c =>
                  -- zig-zag
                  have hsz : (BinaryTree.node a x c).num_nodes ≤ n := by
                    have hnn : (BinaryTree.node (BinaryTree.node ll lk
                        (BinaryTree.node a x c)) k r).num_nodes
                        = 1 + (1 + ll.num_nodes + (BinaryTree.node a x c).num_nodes)
                          + r.num_nodes := rfl
                    omega
                  cases hS : splay (BinaryTree.node a x c) q with
                  | empty => exact absurd hS (splay_ne_empty a c x q)
                  | node A0 s0 B0 =>
                    have hShape := splay_zigzag_shape ll (BinaryTree.node a x c) r A0 B0 lk k q s0
                      hqk hqlt hlkq (fun h => nomatch h) hS
                    obtain ⟨hsmem, hsmin⟩ := splay_root_spec (BinaryTree.node a x c).num_nodes
                      (BinaryTree.node a x c) (Nat.le_refl _) q hblr A0 B0 s0 hS
                    have hlk_s : lk < s0 := by
                      have hF := splay_forallTree_kd (fun z => lk < z)
                        (BinaryTree.node a x c) q hFlr
                      rw [hS] at hF
                      exact (forallTree_node_iff.mp hF).2.1
                    have hs_k : s0 < k := by
                      have hF := splay_forallTree_kd (fun z => z < k)
                        (BinaryTree.node a x c) q hFlrk
                      rw [hS] at hF
                      exact (forallTree_node_iff.mp hF).2.1
                    by_cases hbk2 : k < b
                    · refine Or.inl ?_
                      rw [hShape,
                          ds_both_gt (by omega : s0 < y) (by omega : s0 < b),
                          ds_both_gt (by omega : k < y) (by omega : k < b),
                          ds_both_gt (by omega : k < y) (by omega : k < b)]
                    · have hbk3 : b < k := by omega
                      -- witness deep
                      have hwlr : w ∈ searchPath q (BinaryTree.node a x c) := by
                        rcases List.mem_cons.mp hwmem with rfl | h1
                        · exfalso; omega
                        · rcases List.mem_cons.mp h1 with rfl | h2
                          · exfalso; omega
                          · exact h2
                      have hsb : s0 < b := by
                        have h1 : s0 ≤ w := hsmin w hwlr hqw
                        have h2 : b ≠ s0 := fun h => hbnlr (h ▸ hsmem)
                        omega
                      by_cases hyk : y < k
                      · -- both in (s0, k): recurse
                        have ihlr := ih (BinaryTree.node a x c) hsz q b y hblr hqb hby hbnlr
                          ⟨w, hwlr, hqw, hwb⟩
                        rw [hS, ds_both_gt (by omega : s0 < y) (by omega : s0 < b)] at ihlr
                        rw [hShape,
                            ds_both_gt (by omega : s0 < y) (by omega : s0 < b),
                            ds_both_lt (by omega : y < k) (by omega : b < k),
                            ds_both_lt (by omega : y < k) (by omega : b < k),
                            ds_both_gt (by omega : lk < y) (by omega : lk < b)]
                        rcases ihlr with h | ⟨x0, hx0, hxe⟩
                        · exact Or.inl h
                        · refine Or.inr ⟨x0, ?_, hxe⟩
                          rw [hpath, hpath2]
                          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx0)
                      · by_cases hyk2 : y = k
                        · refine Or.inl ?_
                          rw [hShape,
                              ds_both_gt (by omega : s0 < y) (by omega : s0 < b),
                              ds_self hyk2, ds_self hyk2]
                        · have hky : k < y := by omega
                          refine Or.inl ?_
                          rw [hShape,
                              ds_both_gt (by omega : s0 < y) (by omega : s0 < b),
                              ds_div_gt (by omega : k < y) (by omega : b < k),
                              ds_div_gt (by omega : k < y) (by omega : b < k)]
              · -- q = lk: found at left child; witness forces k < b; verbatim
                have hpath2 : searchPath q (BinaryTree.node ll lk lr) = [lk] :=
                  searchPath_node_self (by omega) _ _
                rw [hpath2] at hwmem
                have hkb : k < b := by
                  rcases List.mem_cons.mp hwmem with rfl | h1
                  · omega
                  · simp only [List.mem_singleton] at h1
                    exfalso; omega
                refine Or.inl ?_
                rw [splay_zig_found hqlt hqlk hlkq ll lr r,
                    ds_both_gt (by omega : lk < y) (by omega : lk < b),
                    ds_both_gt (by omega : k < y) (by omega : k < b),
                    ds_both_gt (by omega : k < y) (by omega : k < b)]
        · -- ===== q descends RIGHT =====
          have hklt : k < q := by omega
          have hkb : k < b := by omega
          have hpath : searchPath q (BinaryTree.node l k r) = k :: searchPath q r :=
            searchPath_node_gt hklt _ _
          rw [hpath] at hwmem hboff
          simp only [List.mem_cons, not_or] at hboff
          obtain ⟨hbnk, hbnr⟩ := hboff
          cases r with
          | empty => exact Or.inl (by rw [splay_right_empty hklt l])
          | node rl rk rr =>
            rcases forallTree_node_iff.mp hFr with ⟨hFrlk, hkrk, hFrrk⟩
            rcases isBST_node_iff.mp hbr with ⟨hFrl, hFrr, hbrl, hbrr⟩
            by_cases hqrk : q < rk
            · have hpath2 : searchPath q (BinaryTree.node rl rk rr) = rk :: searchPath q rl :=
                searchPath_node_lt hqrk _ _
              rw [hpath2] at hwmem hbnr
              simp only [List.mem_cons, not_or] at hbnr
              obtain ⟨hbnrk, hbnrl⟩ := hbnr
              cases rl with
              | empty =>
                -- zag (rl empty): witness forces rk < b; verbatim
                have hrkb : rk < b := by
                  rcases List.mem_cons.mp hwmem with rfl | h1
                  · exfalso; omega
                  · rcases List.mem_cons.mp h1 with rfl | h2
                    · omega
                    · simp at h2
                refine Or.inl ?_
                rw [splay_zag_rl_empty hklt hqrk l rr,
                    ds_both_gt (by omega : rk < y) (by omega : rk < b),
                    ds_both_gt (by omega : k < y) (by omega : k < b),
                    ds_both_gt (by omega : rk < y) (by omega : rk < b)]
              | node a x c =>
                -- zag-zig
                have hsz : (BinaryTree.node a x c).num_nodes ≤ n := by
                  have hnn : (BinaryTree.node l k (BinaryTree.node (BinaryTree.node a x c)
                      rk rr)).num_nodes
                      = 1 + l.num_nodes
                        + (1 + (BinaryTree.node a x c).num_nodes + rr.num_nodes) := rfl
                  omega
                cases hS : splay (BinaryTree.node a x c) q with
                | empty => exact absurd hS (splay_ne_empty a c x q)
                | node A0 s0 B0 =>
                  have hShape := splay_zagzig_shape l (BinaryTree.node a x c) rr A0 B0 rk k q s0
                    hqk hklt hqrk (fun h => nomatch h) hS
                  obtain ⟨hsmem, hsmin⟩ := splay_root_spec (BinaryTree.node a x c).num_nodes
                    (BinaryTree.node a x c) (Nat.le_refl _) q hbrl A0 B0 s0 hS
                  have hk_s : k < s0 := by
                    have hF := splay_forallTree_kd (fun z => k < z)
                      (BinaryTree.node a x c) q hFrlk
                    rw [hS] at hF
                    exact (forallTree_node_iff.mp hF).2.1
                  have hs_rk : s0 < rk := by
                    have hF := splay_forallTree_kd (fun z => z < rk)
                      (BinaryTree.node a x c) q hFrl
                    rw [hS] at hF
                    exact (forallTree_node_iff.mp hF).2.1
                  by_cases hbrk2 : rk < b
                  · refine Or.inl ?_
                    rw [hShape,
                        ds_both_gt (by omega : s0 < y) (by omega : s0 < b),
                        ds_both_gt (by omega : rk < y) (by omega : rk < b),
                        ds_both_gt (by omega : k < y) (by omega : k < b),
                        ds_both_gt (by omega : rk < y) (by omega : rk < b)]
                  · have hbrk3 : b < rk := by omega
                    have hwrl : w ∈ searchPath q (BinaryTree.node a x c) := by
                      rcases List.mem_cons.mp hwmem with rfl | h1
                      · exfalso; omega
                      · rcases List.mem_cons.mp h1 with rfl | h2
                        · exfalso; omega
                        · exact h2
                    have hsb : s0 < b := by
                      have h1 : s0 ≤ w := hsmin w hwrl hqw
                      have h2 : b ≠ s0 := fun h => hbnrl (h ▸ hsmem)
                      omega
                    by_cases hyrk : y < rk
                    · -- both in (s0, rk): recurse
                      have ihrl := ih (BinaryTree.node a x c) hsz q b y hbrl hqb hby hbnrl
                        ⟨w, hwrl, hqw, hwb⟩
                      rw [hS, ds_both_gt (by omega : s0 < y) (by omega : s0 < b)] at ihrl
                      rw [hShape,
                          ds_both_gt (by omega : s0 < y) (by omega : s0 < b),
                          ds_both_lt (by omega : y < rk) (by omega : b < rk),
                          ds_both_gt (by omega : k < y) (by omega : k < b),
                          ds_both_lt (by omega : y < rk) (by omega : b < rk)]
                      rcases ihrl with h | ⟨x0, hx0, hxe⟩
                      · exact Or.inl h
                      · refine Or.inr ⟨x0, ?_, hxe⟩
                        rw [hpath, hpath2]
                        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx0)
                    · by_cases hyrk2 : y = rk
                      · refine Or.inl ?_
                        rw [hShape,
                            ds_both_gt (by omega : s0 < y) (by omega : s0 < b),
                            ds_self hyrk2,
                            ds_both_gt (by omega : k < y) (by omega : k < b),
                            ds_self hyrk2]
                      · have hrky : rk < y := by omega
                        refine Or.inl ?_
                        rw [hShape,
                            ds_both_gt (by omega : s0 < y) (by omega : s0 < b),
                            ds_div_gt (by omega : rk < y) (by omega : b < rk),
                            ds_both_gt (by omega : k < y) (by omega : k < b),
                            ds_div_gt (by omega : rk < y) (by omega : b < rk)]
            · by_cases hrkq : rk < q
              · have hpath2 : searchPath q (BinaryTree.node rl rk rr) = rk :: searchPath q rr :=
                  searchPath_node_gt hrkq _ _
                rw [hpath2] at hwmem hbnr
                simp only [List.mem_cons, not_or] at hbnr
                obtain ⟨hbnrk, hbnrr⟩ := hbnr
                cases rr with
                | empty =>
                  -- no admissible witness: w = k and w = rk both contradict q < w ≤ b
                  exfalso
                  rcases List.mem_cons.mp hwmem with rfl | h1
                  · omega
                  · rcases List.mem_cons.mp h1 with rfl | h2
                    · omega
                    · simp at h2
                | node a x c =>
                  -- zag-zag: witness always deep
                  have hsz : (BinaryTree.node a x c).num_nodes ≤ n := by
                    have hnn : (BinaryTree.node l k (BinaryTree.node rl rk
                        (BinaryTree.node a x c))).num_nodes
                        = 1 + l.num_nodes
                          + (1 + rl.num_nodes + (BinaryTree.node a x c).num_nodes) := rfl
                    omega
                  cases hS : splay (BinaryTree.node a x c) q with
                  | empty => exact absurd hS (splay_ne_empty a c x q)
                  | node A0 s0 B0 =>
                    have hShape := splay_zagzag_shape l rl (BinaryTree.node a x c) A0 B0 rk k q s0
                      hqk hklt hrkq (fun h => nomatch h) hS
                    obtain ⟨hsmem, hsmin⟩ := splay_root_spec (BinaryTree.node a x c).num_nodes
                      (BinaryTree.node a x c) (Nat.le_refl _) q hbrr A0 B0 s0 hS
                    have hrk_s : rk < s0 := by
                      have hF := splay_forallTree_kd (fun z => rk < z)
                        (BinaryTree.node a x c) q hFrr
                      rw [hS] at hF
                      exact (forallTree_node_iff.mp hF).2.1
                    have hrkb : rk < b := by omega
                    have hwrr : w ∈ searchPath q (BinaryTree.node a x c) := by
                      rcases List.mem_cons.mp hwmem with rfl | h1
                      · exfalso; omega
                      · rcases List.mem_cons.mp h1 with rfl | h2
                        · exfalso; omega
                        · exact h2
                    have hsb : s0 < b := by
                      have h1 : s0 ≤ w := hsmin w hwrr hqw
                      have h2 : b ≠ s0 := fun h => hbnrr (h ▸ hsmem)
                      omega
                    have ihrr := ih (BinaryTree.node a x c) hsz q b y hbrr hqb hby hbnrr
                      ⟨w, hwrr, hqw, hwb⟩
                    rw [hS, ds_both_gt (by omega : s0 < y) (by omega : s0 < b)] at ihrr
                    rw [hShape,
                        ds_both_gt (by omega : s0 < y) (by omega : s0 < b),
                        ds_both_gt (by omega : k < y) (by omega : k < b),
                        ds_both_gt (by omega : rk < y) (by omega : rk < b)]
                    rcases ihrr with h | ⟨x0, hx0, hxe⟩
                    · exact Or.inl h
                    · refine Or.inr ⟨x0, ?_, hxe⟩
                      rw [hpath, hpath2]
                      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx0)
              · -- q = rk: found at right child; no admissible witness
                have hpath2 : searchPath q (BinaryTree.node rl rk rr) = [rk] :=
                  searchPath_node_self (by omega) _ _
                rw [hpath2] at hwmem
                exfalso
                rcases List.mem_cons.mp hwmem with rfl | h1
                · omega
                · simp only [List.mem_singleton] at h1
                  omega

/-- (P2) headline, structural form.  SAME-SIDE DIVE `q ≤ b ≤ y` (canonical: future
min-side accesses ascend; `b` earlier, `y` later, `q` the current dive), with `b` off
q's search path and the path separating from `b` strictly above the landing zone
(`∃ w ∈ searchPath q t, q < w ≤ b`).  Then the divergence suffix is either preserved
verbatim or gains exactly one cons, and the new head is a node of q's ORIGINAL path. -/

theorem divergeSuffix_splay_dive (q b y : Nat) (t : BinaryTree) (hbst : IsBST t)
    (hqb : q ≤ b) (hby : b ≤ y) (hboff : b ∉ searchPath q t)
    (hw : ∃ w ∈ searchPath q t, q < w ∧ w ≤ b) :
    divergeSuffix y b (splay t q) = divergeSuffix y b t
    ∨ ∃ x ∈ searchPath q t, divergeSuffix y b (splay t q) = x :: divergeSuffix y b t :=
  ds_splay_dive_aux t.num_nodes t (Nat.le_refl _) q b y hbst hqb hby hboff hw

/-! ## touched-count corollaries -/

theorem touchedCount_divergeSuffix_extend (q b y : Nat) (t : BinaryTree) (T : List Nat)
    (hbst : IsBST t) (hqb : q ≤ b) (hby : b ≤ y) :
    touchedCount (T ++ searchPath q t) (divergeSuffix y b t)
      = touchedCount T (divergeSuffix y b t) :=
  touchedCount_congr (fun z hz => by
    have hzn := divergeSuffix_disjoint_dive t hbst q b y hqb hby z hz
    simp only [List.mem_append]
    exact ⟨fun h => h.resolve_right hzn, Or.inl⟩)

/-- (P2) count form: against the enlarged touched set `T ++ searchPath q t`, the new
divergence suffix costs at most ONE more than the old suffix against `T`.
(The pinned constant is 1, beating the conjectured 2; without the two side conditions
NO constant works — see the counterexample at the bottom.) -/

theorem touchedCount_divergeSuffix_splay_le (q b y : Nat) (t : BinaryTree) (T : List Nat)
    (hbst : IsBST t) (hqb : q ≤ b) (hby : b ≤ y) (hboff : b ∉ searchPath q t)
    (hw : ∃ w ∈ searchPath q t, q < w ∧ w ≤ b) :
    touchedCount (T ++ searchPath q t) (divergeSuffix y b (splay t q))
      ≤ touchedCount T (divergeSuffix y b t) + 1 := by
  rcases divergeSuffix_splay_dive q b y t hbst hqb hby hboff hw with heq | ⟨x, hx, heq⟩
  · rw [heq, touchedCount_divergeSuffix_extend q b y t T hbst hqb hby]
    omega
  · rw [heq, touchedCount_cons_mem (List.mem_append_right T hx),
        touchedCount_divergeSuffix_extend q b y t T hbst hqb hby]

/-- (P1) count form: in the off-path (cargo) case the touched-count of the suffix is
preserved EXACTLY (+0), provided the canonical ordering holds. -/

theorem touchedCount_divergeSuffix_splay_eq_of_avoid (q b y : Nat) (t : BinaryTree)
    (T : List Nat) (hbst : IsBST t) (hqb : q ≤ b) (hby : b ≤ y)
    (hav : ∀ w ∈ searchPath q t, w < min b y ∨ max b y < w) :
    touchedCount (T ++ searchPath q t) (divergeSuffix y b (splay t q))
      = touchedCount T (divergeSuffix y b t) := by
  rw [divergeSuffix_splay_of_avoid q b y t hbst hav]
  exact touchedCount_divergeSuffix_extend q b y t T hbst hqb hby

/-! ## Pinning witnesses (machine-checked instances from the empirical scan) -/

-- (P1) verbatim cargo case: q = 0, b = 2, y = 3; divergence node 2 hangs off q's path [4,1].

example :
    divergeSuffix 3 2 (splay (.node (.node .empty 1 (.node .empty 2 (.node .empty 3 .empty)))
        4 .empty) 0)
      = divergeSuffix 3 2 (.node (.node .empty 1 (.node .empty 2 (.node .empty 3 .empty)))
        4 .empty) := by decide

-- (P2) the one-cons case is realized: q = 0 < b = 2 ≤ y = 5, witness w = 1.

example :
    divergeSuffix 5 2 (splay (.node (.node (.node .empty 1 .empty) 3 .empty) 4 .empty) 0)
      = 4 :: divergeSuffix 5 2 (.node (.node (.node .empty 1 .empty) 3 .empty) 4 .empty) := by
  decide

-- (P2) count form: the constant 1 is TIGHT.

example :
    touchedCount ([] ++ searchPath 0 (.node (.node (.node .empty 1 .empty) 3 .empty) 4 .empty))
        (divergeSuffix 5 2 (splay (.node (.node (.node .empty 1 .empty) 3 .empty) 4 .empty) 0))
      = touchedCount []
          (divergeSuffix 5 2 (.node (.node (.node .empty 1 .empty) 3 .empty) 4 .empty)) + 1 := by
  decide

-- NECESSITY of `b ∉ searchPath q t`: with b = 2 ON q's path (q = 1 < b = 2 ≤ y = 4 all
-- canonical), the excess is already 3; on n-node spine variants it grows without bound.

example :
    touchedCount ([] ++ searchPath 1 (.node .empty 0 (.node (.node (.node (.node .empty 2
          .empty) 3 .empty) 4 .empty) 5 .empty)))
        (divergeSuffix 4 2 (splay (.node .empty 0 (.node (.node (.node (.node .empty 2 .empty)
          3 .empty) 4 .empty) 5 .empty)) 1))
      = touchedCount [] (divergeSuffix 4 2 (.node .empty 0 (.node (.node (.node (.node .empty 2
          .empty) 3 .empty) 4 .empty) 5 .empty))) + 3 := by
  decide


-- ===== process-fact package (assembly stage A) =====
def sideF {n : ℕ} (X : Fin n → ℕ) (i : ℕ) : Bool :=
  if h : i < n then
    decide (∀ j : Fin n, (⟨i, h⟩ : Fin n) < j → X j ≤ X ⟨i, h⟩)
  else true

/-! ## Copied infrastructure: root after splaying a present key (Option form) -/

private def rootKeyO : BinaryTree → Option Nat
| .empty => none
| .node _ k _ => some k

private theorem splay_rootKeyO_eq_some_of_mem_isBST :
    ∀ (t : BinaryTree) (q : Nat), IsBST t → q ∈ t.toKeyList →
      rootKeyO (splay t q) = some q
| .empty, q, _hbst, hmem => by
    simp [BinaryTree.toKeyList] at hmem
| .node l k r, q, hbst, hmem => by
    rw [splay.eq_def]
    cases hbst with
    | node _ _ _ hleft hright hbst_left hbst_right =>
        by_cases hqk : q = k
        · subst q
          simp [rootKeyO]
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
                            splay_rootKeyO_eq_some_of_mem_isBST
                              (.node a x b) q hbst_ll hllmem
                          cases hs : splay (.node a x b) q with
                          | empty =>
                              simp [rootKeyO, hs] at ih
                          | node sl sk sr =>
                              simp [rootKeyO, hs] at ih
                              subst sk
                              simp [hqk, hq_lt_k, hq_lt_lk, hs, rootKeyO,
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
                              splay_rootKeyO_eq_some_of_mem_isBST
                                (.node a x b) q hbst_lr hlrmem
                            cases hs : splay (.node a x b) q with
                            | empty =>
                                simp [rootKeyO, hs] at ih
                            | node sl sk sr =>
                                simp [rootKeyO, hs] at ih
                                subst sk
                                simp [hqk, hq_lt_k, hq_lt_lk, hlk_lt_q, hs,
                                  rootKeyO, rotate, rotateLeft, rotateRight]
                      · have : q = lk := by omega
                        subst q
                        simp [hqk, hq_lt_k, rootKeyO, rotate, rotateRight]
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
                            splay_rootKeyO_eq_some_of_mem_isBST
                              (.node a x b) q hbst_rl hrlmem
                          cases hs : splay (.node a x b) q with
                          | empty =>
                              simp [rootKeyO, hs] at ih
                          | node sl sk sr =>
                              simp [rootKeyO, hs] at ih
                              subst sk
                              simp [hqk, hq_lt_k, hq_lt_rk, hs, rootKeyO,
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
                              splay_rootKeyO_eq_some_of_mem_isBST
                                (.node a x b) q hbst_rr hrrmem
                            cases hs : splay (.node a x b) q with
                            | empty =>
                                simp [rootKeyO, hs] at ih
                            | node sl sk sr =>
                                simp [rootKeyO, hs] at ih
                                subst sk
                                simp [hqk, hq_lt_k, hq_lt_rk, hrk_lt_q, hs,
                                  rootKeyO, rotate, rotateLeft]
                      · have : q = rk := by omega
                        subst q
                        simp [hqk, hq_lt_k, rootKeyO, rotate, rotateLeft]

/-! ## Part 1: `sideF` basics -/

/-- `sideF X i = true` iff every later access is `≤ X i` (the future-max side). -/

theorem sideF_true_iff {n : ℕ} (X : Fin n → ℕ) (i : Fin n) :
    sideF X (i : ℕ) = true ↔ ∀ j : Fin n, i < j → X j ≤ X i := by
  unfold sideF
  rw [dif_pos i.isLt]
  simp only [Fin.eta, decide_eq_true_eq]

/-- If `sideF X i = true`, every later access is `≤ X i`. -/

theorem sideF_true_le {n : ℕ} (X : Fin n → ℕ) (i : Fin n)
    (h : sideF X (i : ℕ) = true) :
    ∀ j : Fin n, i < j → X j ≤ X i :=
  (sideF_true_iff X i).mp h

/-- `sideF X i = false` iff some later access exceeds `X i` (no avoidance needed). -/

theorem sideF_false_iff {n : ℕ} (X : Fin n → ℕ) (i : Fin n) :
    sideF X (i : ℕ) = false ↔ ¬ ∀ j : Fin n, i < j → X j ≤ X i := by
  constructor
  · intro hf hall
    rw [(sideF_true_iff X i).mpr hall] at hf
    exact Bool.noConfusion hf
  · intro hnot
    cases hb : sideF X (i : ℕ) with
    | false => rfl
    | true => exact absurd (sideF_true_le X i hb) hnot

/-- On a `{213, 231}`-avoiding sequence, `sideF X i = false` means the future is
bounded BELOW by `X i` (the future-min side), via `deque_future_one_sided`.
(This is the task's `sideF_false_lt`, stated — correctly — with `≤`.) -/

theorem sideF_false_le {n : ℕ} (X : Fin n → ℕ)
    (h213 : X avoids ![2, 1, 3]) (h231 : X avoids ![2, 3, 1])
    (i : Fin n) (h : sideF X (i : ℕ) = false) :
    ∀ j : Fin n, i < j → X i ≤ X j := by
  rcases deque_future_one_sided X h213 h231 i with hmax | hmin
  · exact absurd hmax ((sideF_false_iff X i).mp h)
  · exact hmin

/-! ## Part 2: same-side monotonicity -/

/-- Two min-side accesses appear in increasing value order. -/

theorem sideF_min_min_mono {n : ℕ} (X : Fin n → ℕ)
    (h213 : X avoids ![2, 1, 3]) (h231 : X avoids ![2, 3, 1])
    (i j : Fin n) (hij : i < j)
    (hi : sideF X (i : ℕ) = false) (_hj : sideF X (j : ℕ) = false) :
    X i ≤ X j :=
  sideF_false_le X h213 h231 i hi j hij

/-- Two max-side accesses appear in decreasing value order. -/

theorem sideF_max_max_anti {n : ℕ} (X : Fin n → ℕ)
    (i j : Fin n) (hij : i < j)
    (hi : sideF X (i : ℕ) = true) (_hj : sideF X (j : ℕ) = true) :
    X j ≤ X i :=
  sideF_true_le X i hi j hij

/-! ## Part 3: cross-side bounds -/

/-- A min-side access is `≤` any later max-side access. -/

theorem sideF_min_max_le {n : ℕ} (X : Fin n → ℕ)
    (h213 : X avoids ![2, 1, 3]) (h231 : X avoids ![2, 3, 1])
    (i j : Fin n) (hij : i < j)
    (hi : sideF X (i : ℕ) = false) (_hj : sideF X (j : ℕ) = true) :
    X i ≤ X j :=
  sideF_false_le X h213 h231 i hi j hij

/-- A later min-side access is `≤` any earlier max-side access (mirror). -/

theorem sideF_max_min_le {n : ℕ} (X : Fin n → ℕ)
    (i j : Fin n) (hij : i < j)
    (hi : sideF X (i : ℕ) = true) (_hj : sideF X (j : ℕ) = false) :
    X j ≤ X i :=
  sideF_true_le X i hi j hij

/-! ## Part 4: root tracking -/

/-- The root key of a tree (`0` for the empty tree). -/

@[simp] theorem rootKey_node (l : BinaryTree) (k : ℕ) (r : BinaryTree) :
    rootKey (.node l k r) = k := rfl

/-- Splaying a present key of a BST brings it to the root. -/

theorem splay_rootKey (t : BinaryTree) (q : ℕ)
    (hmem : q ∈ t.toKeyList) (hbst : IsBST t) :
    rootKey (splay t q) = q := by
  have h := splay_rootKeyO_eq_some_of_mem_isBST t q hbst hmem
  cases hs : splay t q with
  | empty =>
      rw [hs] at h
      simp [rootKeyO] at h
  | node l k r =>
      rw [hs] at h
      simp only [rootKeyO, Option.some.injEq] at h
      simpa [rootKey] using h

/-! ## Part 5: root tracking along the process, and the four root orderings -/

/-- After the access at position `i`, the accessed key `X i` is the root. -/

theorem processTree_rootKey_succ {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (hbst : IsBST init) (hmem : ∀ k : Fin n, X k ∈ init.toKeyList)
    (i : Fin n) :
    rootKey (processTree init X ((i : ℕ) + 1)) = X i := by
  rw [processTree_succ]
  exact splay_rootKey _ _
    (by rw [processTree_toKeyList]; exact hmem i)
    (processTree_isBST init X hbst i)

/-- At any step `i ≥ 1` of the process, the root is the previous access `X (i-1)`. -/

theorem processTree_rootKey {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (hbst : IsBST init) (hmem : ∀ k : Fin n, X k ∈ init.toKeyList)
    (i : ℕ) (h1 : 1 ≤ i) (hi1 : i - 1 < n) :
    rootKey (processTree init X i) = X ⟨i - 1, hi1⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  have hm : m < n := by omega
  have hfin : (⟨m + 1 - 1, hi1⟩ : Fin n) = ⟨m, hm⟩ := by
    simp
  rw [hfin]
  exact processTree_rootKey_succ init X hbst hmem ⟨m, hm⟩

/-- **(min, min)**: previous and current accesses both min-side.  With
`r0 = rootKey (processTree init X i)`, `q = X i`, `v = X j` (any later access):
`r0 ≤ q ≤ v`. -/

theorem deque_root_order_min_min {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (h213 : X avoids ![2, 1, 3]) (h231 : X avoids ![2, 3, 1])
    (hbst : IsBST init) (hmem : ∀ k : Fin n, X k ∈ init.toKeyList)
    (i j : Fin n) (h0 : 1 ≤ (i : ℕ)) (hij : i < j)
    (hprev : sideF X ((i : ℕ) - 1) = false) (hcur : sideF X (i : ℕ) = false) :
    rootKey (processTree init X (i : ℕ)) ≤ X i ∧ X i ≤ X j := by
  have hin : (i : ℕ) < n := i.isLt
  have hi1 : (i : ℕ) - 1 < n := by omega
  have hpi : (⟨(i : ℕ) - 1, hi1⟩ : Fin n) < i := by
    rw [Fin.lt_def]
    exact Nat.sub_lt (by omega) Nat.one_pos
  have hroot := processTree_rootKey init X hbst hmem (i : ℕ) h0 hi1
  constructor
  · rw [hroot]
    exact sideF_false_le X h213 h231 ⟨(i : ℕ) - 1, hi1⟩ hprev i hpi
  · exact sideF_false_le X h213 h231 i hcur j hij

/-- **(max, max)**: previous and current accesses both max-side: `v ≤ q ≤ r0`. -/

theorem deque_root_order_max_max {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (hbst : IsBST init) (hmem : ∀ k : Fin n, X k ∈ init.toKeyList)
    (i j : Fin n) (h0 : 1 ≤ (i : ℕ)) (hij : i < j)
    (hprev : sideF X ((i : ℕ) - 1) = true) (hcur : sideF X (i : ℕ) = true) :
    X j ≤ X i ∧ X i ≤ rootKey (processTree init X (i : ℕ)) := by
  have hin : (i : ℕ) < n := i.isLt
  have hi1 : (i : ℕ) - 1 < n := by omega
  have hpi : (⟨(i : ℕ) - 1, hi1⟩ : Fin n) < i := by
    rw [Fin.lt_def]
    exact Nat.sub_lt (by omega) Nat.one_pos
  have hroot := processTree_rootKey init X hbst hmem (i : ℕ) h0 hi1
  constructor
  · exact sideF_true_le X i hcur j hij
  · rw [hroot]
    exact sideF_true_le X ⟨(i : ℕ) - 1, hi1⟩ hprev i hpi

/-- **(min, max)**: previous access min-side, current access max-side:
`r0 ≤ v ≤ q`. -/

theorem deque_root_order_min_max {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (h213 : X avoids ![2, 1, 3]) (h231 : X avoids ![2, 3, 1])
    (hbst : IsBST init) (hmem : ∀ k : Fin n, X k ∈ init.toKeyList)
    (i j : Fin n) (h0 : 1 ≤ (i : ℕ)) (hij : i < j)
    (hprev : sideF X ((i : ℕ) - 1) = false) (hcur : sideF X (i : ℕ) = true) :
    rootKey (processTree init X (i : ℕ)) ≤ X j ∧ X j ≤ X i := by
  have hin : (i : ℕ) < n := i.isLt
  have hi1 : (i : ℕ) - 1 < n := by omega
  have hij' : (i : ℕ) < (j : ℕ) := hij
  have hpj : (⟨(i : ℕ) - 1, hi1⟩ : Fin n) < j := by
    rw [Fin.lt_def]
    exact lt_of_le_of_lt (Nat.sub_le _ _) hij'
  have hroot := processTree_rootKey init X hbst hmem (i : ℕ) h0 hi1
  constructor
  · rw [hroot]
    exact sideF_false_le X h213 h231 ⟨(i : ℕ) - 1, hi1⟩ hprev j hpj
  · exact sideF_true_le X i hcur j hij

/-- **(max, min)**: previous access max-side, current access min-side:
`q ≤ v ≤ r0`. -/

theorem deque_root_order_max_min {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (h213 : X avoids ![2, 1, 3]) (h231 : X avoids ![2, 3, 1])
    (hbst : IsBST init) (hmem : ∀ k : Fin n, X k ∈ init.toKeyList)
    (i j : Fin n) (h0 : 1 ≤ (i : ℕ)) (hij : i < j)
    (hprev : sideF X ((i : ℕ) - 1) = true) (hcur : sideF X (i : ℕ) = false) :
    X i ≤ X j ∧ X j ≤ rootKey (processTree init X (i : ℕ)) := by
  have hin : (i : ℕ) < n := i.isLt
  have hi1 : (i : ℕ) - 1 < n := by omega
  have hij' : (i : ℕ) < (j : ℕ) := hij
  have hpj : (⟨(i : ℕ) - 1, hi1⟩ : Fin n) < j := by
    rw [Fin.lt_def]
    exact lt_of_le_of_lt (Nat.sub_le _ _) hij'
  have hroot := processTree_rootKey init X hbst hmem (i : ℕ) h0 hi1
  constructor
  · exact sideF_false_le X h213 h231 i hcur j hij
  · rw [hroot]
    exact sideF_true_le X ⟨(i : ℕ) - 1, hi1⟩ hprev j hpj

/-! ## Part 6: path-window unfolds at the root -/

/-- Searching for the root key of a nonempty tree touches only the root. -/

theorem searchPath_root_self (t : BinaryTree) (hne : t ≠ .empty) :
    searchPath (rootKey t) t = [rootKey t] := by
  cases t with
  | empty => exact absurd rfl hne
  | node l k r => exact searchPath_node_self rfl l r

/-- For `v` above the root key, the search path is the root followed by the
search path in the right subtree. -/

theorem searchPath_root_cons_right {v : ℕ} (t : BinaryTree) (hne : t ≠ .empty)
    (h : rootKey t < v) :
    searchPath v t = rootKey t :: searchPath v (rightSubtree t) := by
  cases t with
  | empty => exact absurd rfl hne
  | node l k r =>
      simp only [rootKey] at h
      exact searchPath_node_gt h l r

/-- For `v` below the root key, the search path is the root followed by the
search path in the left subtree. -/

theorem searchPath_root_cons_left {v : ℕ} (t : BinaryTree) (hne : t ≠ .empty)
    (h : v < rootKey t) :
    searchPath v t = rootKey t :: searchPath v (leftSubtree t) := by
  cases t with
  | empty => exact absurd rfl hne
  | node l k r =>
      simp only [rootKey] at h
      exact searchPath_node_lt h l r


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

/-! ### Ghost claims (copied verbatim from the development file) -/

/-- An interval claim: keys in `[lo, hi]` carry a (doubled) remnant budget `r`. -/

def ghostStepOppPrune (x : ℕ) (isMin : Bool) (g : GhostState) : GhostState :=
  { claims := pruneClaims isMin x g.claims, pool := g.pool + 4 }

/-- **Met-sum monotonicity.**  The sum of remnant budgets over any sub-selection of
claims is at most the sum over all claims. -/

def ghostAt {n : ℕ} (kap : ℕ) (init : BinaryTree) (X : Fin n → ℕ) :
    ℕ → Bool → GhostState
  | 0, _ => ⟨[], 0⟩
  | (i+1), b =>
      if sideF X i = b then
        ghostStepOwn kap (touchedList init X i) (pathN init X i)
          (costN init X i) (freshN init X i) (accessN X i) (!b)
          (ghostAt kap init X i b)
      else
        ghostStepOppPrune (accessN X i) (!(sideF X i)) (ghostAt kap init X i b)

@[simp] theorem ghostAt_zero {n : ℕ} (kap : ℕ) (init : BinaryTree)
    (X : Fin n → ℕ) (b : Bool) :
    ghostAt kap init X 0 b = ⟨[], 0⟩ := rfl

theorem ghostAt_succ {n : ℕ} (kap : ℕ) (init : BinaryTree) (X : Fin n → ℕ)
    (i : ℕ) (b : Bool) :
    ghostAt kap init X (i+1) b =
      if sideF X i = b then
        ghostStepOwn kap (touchedList init X i) (pathN init X i)
          (costN init X i) (freshN init X i) (accessN X i) (!b)
          (ghostAt kap init X i b)
      else
        ghostStepOppPrune (accessN X i) (!(sideF X i)) (ghostAt kap init X i b) := rfl

theorem ghostAt_succ_own {n : ℕ} (kap : ℕ) (init : BinaryTree) (X : Fin n → ℕ)
    (i : ℕ) (b : Bool) (h : sideF X i = b) :
    ghostAt kap init X (i+1) b =
      ghostStepOwn kap (touchedList init X i) (pathN init X i)
        (costN init X i) (freshN init X i) (accessN X i) (!b)
        (ghostAt kap init X i b) := by
  rw [ghostAt_succ, if_pos h]

theorem ghostAt_succ_opp {n : ℕ} (kap : ℕ) (init : BinaryTree) (X : Fin n → ℕ)
    (i : ℕ) (b : Bool) (h : sideF X i ≠ b) :
    ghostAt kap init X (i+1) b =
      ghostStepOppPrune (accessN X i) (!(sideF X i)) (ghostAt kap init X i b) := by
  rw [ghostAt_succ, if_neg h]

/-! ### Invariant ingredients -/

/-- Touched count of the `v`-search path in the current process tree, against the
current touched set. -/

def tcOf {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ) (v : ℕ) (i : ℕ) : ℕ :=
  touchedCount (touchedList init X i) (searchPath v (processTree init X i))

/-- Met-claims budget of side `b`'s ghost state against an arbitrary key list `L`
(with the current touched set as `T`). -/

def metSumOn {n : ℕ} (kap : ℕ) (init : BinaryTree) (X : Fin n → ℕ)
    (i : ℕ) (b : Bool) (L : List ℕ) : ℕ :=
  claimsListTotal
    ((ghostAt kap init X i b).claims.filter (claimMet (touchedList init X i) L))

/-- Met-claims budget against the `v`-search path of the current process tree. -/

def metSum {n : ℕ} (kap : ℕ) (init : BinaryTree) (X : Fin n → ℕ)
    (i : ℕ) (b : Bool) (v : ℕ) : ℕ :=
  metSumOn kap init X i b (searchPath v (processTree init X i))

/-- Touched count of the diverge suffix of `vk` against `vj`'s path in the current
process tree. -/

def tcSuffixOf {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (vk vj : ℕ) (i : ℕ) : ℕ :=
  touchedCount (touchedList init X i) (divergeSuffix vk vj (processTree init X i))

/-- The met-claims budget is at most the total claims budget. -/

theorem metSumOn_le_claimsTotal {n : ℕ} (kap : ℕ) (init : BinaryTree)
    (X : Fin n → ℕ) (i : ℕ) (b : Bool) (L : List ℕ) :
    metSumOn kap init X i b L ≤ claimsTotal (ghostAt kap init X i b) :=
  claimsListTotal_filter_le _ _

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
    FirstOwnAfter X i (sideF X i) i :=
  ⟨le_rfl, hi, rfl, fun _ hik hki => absurd (lt_of_le_of_lt hik hki) (lt_irrefl i)⟩

/-! ### The three-clause invariant -/

/-- The per-side invariant at step `i` for side `b`:
* (C1) conservation: the total claims budget plus the pool is within the ledger;
* (C2) next-own cover: for the FIRST side-`b` access `j ≥ i`, twice the touched
  count of its current path is covered by the met claims plus pool plus `14`;
* (C3) chain cover: for every pair of CONSECUTIVE future side-`b` accesses
  `(j, k)`, twice the touched count of `X k`'s diverge suffix against `X j`'s
  current path is covered by the suffix-met claims plus pool plus `8`. -/

def INVside {n : ℕ} (kap : ℕ) (init : BinaryTree) (X : Fin n → ℕ)
    (i : ℕ) (b : Bool) : Prop :=
  (claimsTotal (ghostAt kap init X i b) + (ghostAt kap init X i b).pool
      ≤ ledger kap (costN init X) (freshN init X) (sideF X) i b)
  ∧ (∀ j : ℕ, FirstOwnAfter X i b j →
      2 * tcOf init X (accessN X j) i
        ≤ metSum kap init X i b (accessN X j) + (ghostAt kap init X i b).pool + 14)
  ∧ (∀ j k : ℕ, ConsecOwnAfter X i b j k →
      2 * tcSuffixOf init X (accessN X k) (accessN X j) i
        ≤ metSumOn kap init X i b
            (divergeSuffix (accessN X k) (accessN X j) (processTree init X i))
          + (ghostAt kap init X i b).pool + 8)

/-- The full invariant: both sides. -/

def INV {n : ℕ} (kap : ℕ) (init : BinaryTree) (X : Fin n → ℕ) (i : ℕ) : Prop :=
  ∀ b : Bool, INVside kap init X i b

/-! ### The keystone arithmetic -/

/-- **MASTER derivation (original keystone, `κ = 6`)**, with the
`10 + 10·fr` form of (C2). -/

theorem master_of_C1_C2_strict14 (D tc fr Sr p c : ℕ)
    (hC1 : Sr + p ≤ D)
    (hC2 : 2 * tc ≤ Sr + p + 14)
    (hlen : c + 1 = tc + fr) :
    2 * c ≤ D + 2 * 6 * (1 + fr) := by
  omega

/-! ### Base case -/

/-- **Base case**: the invariant holds at step `0` (empty ghost, zero ledger,
empty touched set). -/

theorem INV_zero {n : ℕ} (kap : ℕ) (init : BinaryTree) (X : Fin n → ℕ) :
    INV kap init X 0 := by
  intro b
  refine ⟨?_, ?_, ?_⟩
  · have hg : ghostAt kap init X 0 b = ⟨[], 0⟩ := rfl
    have hl : ledger kap (costN init X) (freshN init X) (sideF X) 0 b = 0 := rfl
    rw [hg, hl]
    show claimsListTotal [] + 0 ≤ 0
    simp
  · intro j _
    have h0 : tcOf init X (accessN X j) 0 = 0 := by
      show touchedCount (touchedList init X 0) _ = 0
      rw [touchedList_zero, touchedCount_nil_T]
    rw [h0]
    omega
  · intro j k _
    have h0 : tcSuffixOf init X (accessN X k) (accessN X j) 0 = 0 := by
      show touchedCount (touchedList init X 0) _ = 0
      rw [touchedList_zero, touchedCount_nil_T]
    rw [h0]
    omega

/-! ### The MASTER discharge -/

/-- **MASTER discharge (`κ = 6`).**  At every in-range index `i`, the invariant at
`i` implies the per-access MASTER inequality of the ledger capstone:
twice the access cost is covered by the own-side ledger plus the `κ`-scaled fresh
budget.  Chain: (C2) at `j = i` (the access is its own first own-side index) +
met-sum monotonicity + (C1) + the path-length split + the fresh bridge +
the strict-14 keystone. -/

theorem master_of_INV {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (hsize : init.num_nodes = n) (hbst : IsBST init)
    (i : ℕ) (hi : i < n) (hINV : INV 6 init X i) :
    2 * costN init X i
      ≤ ledger 6 (costN init X) (freshN init X) (sideF X) i (sideF X i)
        + 2 * 6 * (1 + freshN init X i) := by
  obtain ⟨hC1, hC2, _hC3⟩ := hINV (sideF X i)
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
  -- (C2) at j = i: the access is the first own-side index ≥ i
  have hC2i := hC2 i (firstOwnAfter_self X i hi)
  rw [hacc] at hC2i
  -- met-sum monotonicity gives (C1) for the met claims
  have hmono : metSum 6 init X i (sideF X i) (X ⟨i, hi⟩)
      ≤ claimsTotal (ghostAt 6 init X i (sideF X i)) :=
    metSumOn_le_claimsTotal 6 init X i (sideF X i) _
  have hC1' : metSum 6 init X i (sideF X i) (X ⟨i, hi⟩)
      + (ghostAt 6 init X i (sideF X i)).pool
      ≤ ledger 6 (costN init X) (freshN init X) (sideF X) i (sideF X i) := by
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
    (ledger 6 (costN init X) (freshN init X) (sideF X) i (sideF X i))
    (touchedCount (touchedList init X i)
      (searchPath (X ⟨i, hi⟩) (processTree init X i)))
    (freshN init X i)
    (metSum 6 init X i (sideF X i) (X ⟨i, hi⟩))
    ((ghostAt 6 init X i (sideF X i)).pool)
    (costN init X i)
    hC1' hC2i hlen2

/-! ### The conditional skeleton: reproduction as the only holes -/

/-- **Invariant propagation from the two reproduction hypotheses.**
`hstepOwn` reproduces side `b`'s invariant across an own-side access
(`sideF X i = b`), `hstepOpp` across an opposite-side access; both may use the
FULL invariant (both sides) at `i`.  These are the only remaining proof
obligations of the deque ledger programme. -/

theorem INV_all_of_steps {n : ℕ} (kap : ℕ) (init : BinaryTree) (X : Fin n → ℕ)
    (hstepOwn : ∀ i, i < n → INV kap init X i →
        ∀ b, sideF X i = b → INVside kap init X (i+1) b)
    (hstepOpp : ∀ i, i < n → INV kap init X i →
        ∀ b, sideF X i ≠ b → INVside kap init X (i+1) b) :
    ∀ i, i ≤ n → INV kap init X i := by
  intro i
  induction i with
  | zero =>
      intro _
      exact INV_zero kap init X
  | succ i ih =>
      intro hin
      have hi : i < n := hin
      have hINVi : INV kap init X i := ih (Nat.le_of_succ_le hin)
      intro b
      by_cases hside : sideF X i = b
      · exact hstepOwn i hi hINVi b hside
      · exact hstepOpp i hi hINVi b hside

/-- **THE COMPLETE CONDITIONAL SKELETON (`κ = 6`).**  Given the two reproduction
hypotheses (own-side and opposite-side step preservation of the three-clause
invariant), the MASTER per-access inequality of the ledger capstone holds at
every index `i < n`.  Feeding this conclusion to the capstone's
`deque_of_ledger_master` / `deque_conjecture_of_ledger_master` (with
`kap = 6`) closes both deque challenges. -/

theorem hmaster_of_reproduction {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (hsize : init.num_nodes = n) (hbst : IsBST init)
    (hstepOwn : ∀ i, i < n → INV 6 init X i →
        ∀ b, sideF X i = b → INVside 6 init X (i+1) b)
    (hstepOpp : ∀ i, i < n → INV 6 init X i →
        ∀ b, sideF X i ≠ b → INVside 6 init X (i+1) b) :
    ∀ i, i < n →
      2 * costN init X i
        ≤ ledger 6 (costN init X) (freshN init X) (sideF X) i (sideF X i)
          + 2 * 6 * (1 + freshN init X i) := by
  intro i hi
  exact master_of_INV init X hsize hbst i hi
    (INV_all_of_steps 6 init X hstepOwn hstepOpp i (Nat.le_of_lt hi))

/-- `Fin`-indexed form of the conclusion, matching the capstone's `hmaster`
hypothesis shape verbatim (at `kap = 6`). -/

theorem hmaster_fin_of_reproduction {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (hsize : init.num_nodes = n) (hbst : IsBST init)
    (hstepOwn : ∀ i, i < n → INV 6 init X i →
        ∀ b, sideF X i = b → INVside 6 init X (i+1) b)
    (hstepOpp : ∀ i, i < n → INV 6 init X i →
        ∀ b, sideF X i ≠ b → INVside 6 init X (i+1) b) :
    ∀ i : Fin n,
      2 * costN init X i
        ≤ ledger 6 (costN init X) (freshN init X) (sideF X) i (sideF X i)
          + 2 * 6 * (1 + freshN init X i) := fun i =>
  hmaster_of_reproduction init X hsize hbst hstepOwn hstepOpp i i.isLt


-- ===== STEP-OPP part 1: within-run C3 cores + root spec =====
theorem forallTree_mem {p : Nat → Prop} :
    ∀ {t : BinaryTree}, ForallTree p t → ∀ x ∈ t.toKeyList, p x := by
  intro t h
  induction h with
  | left => intro x hx; simp [BinaryTree.toKeyList] at hx
  | node l k r hl hk hr ihl ihr =>
    intro x hx
    simp only [BinaryTree.toKeyList, List.append_assoc, List.mem_append,
      List.mem_singleton] at hx
    rcases hx with h | h | h
    · exact ihl x h
    · exact h ▸ hk
    · exact ihr x h

theorem mem_toKeyList_node {l r : BinaryTree} {k q : Nat} :
    q ∈ (BinaryTree.node l k r).toKeyList
      ↔ q ∈ l.toKeyList ∨ q = k ∨ q ∈ r.toKeyList := by
  simp only [BinaryTree.toKeyList, List.append_assoc, List.mem_append,
    List.mem_singleton]

theorem mem_toKeyList_left {l r : BinaryTree} {k q : Nat}
    (hFr : ForallTree (fun x => k < x) r) (hq : q < k)
    (hmem : q ∈ (BinaryTree.node l k r).toKeyList) : q ∈ l.toKeyList := by
  rcases mem_toKeyList_node.mp hmem with h | h | h
  · exact h
  · omega
  · have := forallTree_mem hFr q h; omega

theorem mem_toKeyList_right {l r : BinaryTree} {k q : Nat}
    (hFl : ForallTree (fun x => x < k) l) (hq : k < q)
    (hmem : q ∈ (BinaryTree.node l k r).toKeyList) : q ∈ r.toKeyList := by
  rcases mem_toKeyList_node.mp hmem with h | h | h
  · have := forallTree_mem hFl q h; omega
  · omega
  · exact h

/-! ## §B  Splaying a PRESENT key brings exactly that key to the root -/

theorem splay_root_of_mem_aux :
    ∀ (n : Nat) (t : BinaryTree), t.num_nodes ≤ n → ∀ (q : Nat),
      IsBST t → q ∈ t.toKeyList → ∃ A B, splay t q = .node A q B := by
  intro n
  induction n with
  | zero =>
    intro t ht q _ hmem
    cases t with
    | empty => simp [BinaryTree.toKeyList] at hmem
    | node l k r =>
      exfalso
      have hnn : (BinaryTree.node l k r).num_nodes = 1 + l.num_nodes + r.num_nodes := rfl
      omega
  | succ n ih =>
    intro t ht q hbst hmem
    cases t with
    | empty => simp [BinaryTree.toKeyList] at hmem
    | node l k r =>
      rcases isBST_node_iff.mp hbst with ⟨hFl, hFr, hbl, hbr⟩
      have hnn : (BinaryTree.node l k r).num_nodes = 1 + l.num_nodes + r.num_nodes := rfl
      by_cases hqk : q = k
      · subst hqk
        exact ⟨l, r, splay_eq_of_eq rfl l r⟩
      · by_cases hqlt : q < k
        · have hql : q ∈ l.toKeyList := mem_toKeyList_left hFr hqlt hmem
          cases l with
          | empty => simp [BinaryTree.toKeyList] at hql
          | node ll lk lr =>
            rcases isBST_node_iff.mp hbl with ⟨hFll, hFlr, hbll, hblr⟩
            have hnn2 : (BinaryTree.node ll lk lr).num_nodes
                = 1 + ll.num_nodes + lr.num_nodes := rfl
            by_cases hqlk : q < lk
            · have hqll : q ∈ ll.toKeyList := mem_toKeyList_left hFlr hqlk hql
              cases ll with
              | empty => simp [BinaryTree.toKeyList] at hqll
              | node la lx lb =>
                obtain ⟨A, B, hS⟩ := ih (BinaryTree.node la lx lb) (by
                  have : (BinaryTree.node la lx lb).num_nodes
                      = 1 + la.num_nodes + lb.num_nodes := rfl
                  omega) q hbll hqll
                exact ⟨A, .node B lk (.node lr k r),
                  splay_zigzig_shape (.node la lx lb) lr r A B lk k q q hqk hqlt hqlk
                    (fun h => nomatch h) hS⟩
            · by_cases hlkq : lk < q
              · have hqlr : q ∈ lr.toKeyList := mem_toKeyList_right hFll hlkq hql
                cases lr with
                | empty => simp [BinaryTree.toKeyList] at hqlr
                | node la lx lb =>
                  obtain ⟨A, B, hS⟩ := ih (BinaryTree.node la lx lb) (by
                    have : (BinaryTree.node la lx lb).num_nodes
                        = 1 + la.num_nodes + lb.num_nodes := rfl
                    omega) q hblr hqlr
                  exact ⟨.node ll lk A, .node B k r,
                    splay_zigzag_shape ll (.node la lx lb) r A B lk k q q hqk hqlt hlkq
                      (fun h => nomatch h) hS⟩
              · have hqlk2 : q = lk := by omega
                subst hqlk2
                exact ⟨ll, .node lr k r, splay_zig_found hqlt hqlk hlkq ll lr r⟩
        · have hklt : k < q := by omega
          have hqr : q ∈ r.toKeyList := mem_toKeyList_right hFl hklt hmem
          cases r with
          | empty => simp [BinaryTree.toKeyList] at hqr
          | node rl rk rr =>
            rcases isBST_node_iff.mp hbr with ⟨hFrl, hFrr, hbrl, hbrr⟩
            have hnn2 : (BinaryTree.node rl rk rr).num_nodes
                = 1 + rl.num_nodes + rr.num_nodes := rfl
            by_cases hqrk : q < rk
            · have hqrl : q ∈ rl.toKeyList := mem_toKeyList_left hFrr hqrk hqr
              cases rl with
              | empty => simp [BinaryTree.toKeyList] at hqrl
              | node ra rx rb =>
                obtain ⟨A, B, hS⟩ := ih (BinaryTree.node ra rx rb) (by
                  have : (BinaryTree.node ra rx rb).num_nodes
                      = 1 + ra.num_nodes + rb.num_nodes := rfl
                  omega) q hbrl hqrl
                exact ⟨.node l k A, .node B rk rr,
                  splay_zagzig_shape l (.node ra rx rb) rr A B rk k q q hqk hklt hqrk
                    (fun h => nomatch h) hS⟩
            · by_cases hrkq : rk < q
              · have hqrr : q ∈ rr.toKeyList := mem_toKeyList_right hFrl hrkq hqr
                cases rr with
                | empty => simp [BinaryTree.toKeyList] at hqrr
                | node ra rx rb =>
                  obtain ⟨A, B, hS⟩ := ih (BinaryTree.node ra rx rb) (by
                    have : (BinaryTree.node ra rx rb).num_nodes
                        = 1 + ra.num_nodes + rb.num_nodes := rfl
                    omega) q hbrr hqrr
                  exact ⟨.node (.node l k rl) rk A, B,
                    splay_zagzag_shape l rl (.node ra rx rb) A B rk k q q hqk hklt hrkq
                      (fun h => nomatch h) hS⟩
              · have hqrk2 : q = rk := by omega
                subst hqrk2
                exact ⟨.node l k rl, rr, splay_zag_found hklt hqrk hrkq l rl rr⟩

/-- **Root spec for present keys.**  Splaying a key that is IN the (BST) tree puts
exactly that key at the root. -/

theorem splay_root_of_mem (q : Nat) (t : BinaryTree) (hbst : IsBST t)
    (hmem : q ∈ t.toKeyList) : ∃ A B, splay t q = .node A q B :=
  splay_root_of_mem_aux t.num_nodes t (Nat.le_refl _) q hbst hmem


namespace Splay

/-! ## §C  WITHIN-RUN CORE (forward): splaying a PRESENT key `q` strictly below the
opposite-side pair `b ≤ v` changes `divergeSuffix v b` by AT MOST ONE on-path cons. -/

theorem ds_splay_found_aux :
    ∀ (n : Nat) (t : BinaryTree), t.num_nodes ≤ n → ∀ (q b v : Nat),
      IsBST t → q ∈ t.toKeyList → q < b → b ≤ v →
      divergeSuffix v b (splay t q) = divergeSuffix v b t
      ∨ ∃ x ∈ searchPath q t,
          divergeSuffix v b (splay t q) = x :: divergeSuffix v b t := by
  intro n
  induction n with
  | zero =>
    intro t ht q b v _ hmem _ _
    cases t with
    | empty => simp [BinaryTree.toKeyList] at hmem
    | node l k r =>
      exfalso
      have hnn : (BinaryTree.node l k r).num_nodes = 1 + l.num_nodes + r.num_nodes := rfl
      omega
  | succ n ih =>
    intro t ht q b v hbst hmem hqb hbv
    have hqv : q < v := by omega
    cases t with
    | empty => simp [BinaryTree.toKeyList] at hmem
    | node l k r =>
      rcases isBST_node_iff.mp hbst with ⟨hFl, hFr, hbl, hbr⟩
      have hnn : (BinaryTree.node l k r).num_nodes = 1 + l.num_nodes + r.num_nodes := rfl
      by_cases hqk : q = k
      · rw [splay_eq_of_eq hqk]
        exact Or.inl rfl
      · by_cases hqlt : q < k
        · -- ===== q descends LEFT =====
          have hql : q ∈ l.toKeyList := mem_toKeyList_left hFr hqlt hmem
          have hpathq : searchPath q (BinaryTree.node l k r) = k :: searchPath q l :=
            searchPath_node_lt hqlt _ _
          cases l with
          | empty => simp [BinaryTree.toKeyList] at hql
          | node ll lk lr =>
            rcases isBST_node_iff.mp hbl with ⟨hFll, hFlr, hbll, hblr⟩
            have hlkk : lk < k := (forallTree_node_iff.mp hFl).2.1
            have hnn2 : (BinaryTree.node ll lk lr).num_nodes
                = 1 + ll.num_nodes + lr.num_nodes := rfl
            by_cases hqlk : q < lk
            · -- ---- zig-zig ----
              have hqll : q ∈ ll.toKeyList := mem_toKeyList_left hFlr hqlk hql
              cases ll with
              | empty => simp [BinaryTree.toKeyList] at hqll
              | node la lx lb =>
                obtain ⟨A, B, hS⟩ :=
                  splay_root_of_mem q (BinaryTree.node la lx lb) hbll hqll
                have hT : splay (BinaryTree.node
                      (BinaryTree.node (BinaryTree.node la lx lb) lk lr) k r) q
                    = BinaryTree.node A q
                        (BinaryTree.node B lk (BinaryTree.node lr k r)) :=
                  splay_zigzig_shape (BinaryTree.node la lx lb) lr r A B lk k q q
                    hqk hqlt hqlk (fun h => nomatch h) hS
                by_cases hkb : k < b
                · -- k < b ≤ v : verbatim
                  refine Or.inl ?_
                  rw [hT, ds_both_gt hqv hqb,
                      ds_both_gt (show lk < v by omega) (show lk < b by omega),
                      ds_both_gt (show k < v by omega) hkb,
                      ds_both_gt (show k < v by omega) hkb]
                · by_cases hbk : b = k
                  · -- b = k : verbatim
                    by_cases hvk : v = k
                    · refine Or.inl ?_
                      rw [hT, ds_both_gt hqv hqb,
                          ds_both_gt (show lk < v by omega) (show lk < b by omega),
                          ds_self hvk, ds_self hvk]
                    · have hkv : k < v := by omega
                      refine Or.inl ?_
                      rw [hT, ds_both_gt hqv hqb,
                          ds_both_gt (show lk < v by omega) (show lk < b by omega),
                          ds_qroot_gt hbk hkv, ds_qroot_gt hbk hkv]
                  · have hbk2 : b < k := by omega
                    by_cases hlkb : lk < b
                    · -- lk < b < k : verbatim
                      rcases Nat.lt_trichotomy v k with hvk | hvk | hvk
                      · refine Or.inl ?_
                        rw [hT, ds_both_gt hqv hqb,
                            ds_both_gt (show lk < v by omega) hlkb,
                            ds_both_lt hvk hbk2, ds_both_lt hvk hbk2,
                            ds_both_gt (show lk < v by omega) hlkb]
                      · refine Or.inl ?_
                        rw [hT, ds_both_gt hqv hqb,
                            ds_both_gt (show lk < v by omega) hlkb,
                            ds_self hvk, ds_self hvk]
                      · refine Or.inl ?_
                        rw [hT, ds_both_gt hqv hqb,
                            ds_both_gt (show lk < v by omega) hlkb,
                            ds_div_gt hvk hbk2, ds_div_gt hvk hbk2]
                    · by_cases hblk : b = lk
                      · -- b = lk : ONE k-cons appears whenever v ≠ lk
                        by_cases hvlk : v = lk
                        · refine Or.inl ?_
                          rw [hT, ds_both_gt hqv hqb, ds_self hvlk,
                              ds_both_lt (show v < k by omega) hbk2, ds_self hvlk]
                        · have hlkv : lk < v := by omega
                          rcases Nat.lt_trichotomy v k with hvk | hvk | hvk
                          · refine Or.inr ⟨k, ?_, ?_⟩
                            · rw [hpathq]; exact List.mem_cons_self
                            · rw [hT, ds_both_gt hqv hqb, ds_qroot_gt hblk hlkv,
                                  searchPath_node_lt hvk,
                                  ds_both_lt hvk hbk2, ds_qroot_gt hblk hlkv]
                          · refine Or.inr ⟨k, ?_, ?_⟩
                            · rw [hpathq]; exact List.mem_cons_self
                            · rw [hT, ds_both_gt hqv hqb, ds_qroot_gt hblk hlkv,
                                  searchPath_node_self hvk, ds_self hvk]
                          · refine Or.inr ⟨k, ?_, ?_⟩
                            · rw [hpathq]; exact List.mem_cons_self
                            · rw [hT, ds_both_gt hqv hqb, ds_qroot_gt hblk hlkv,
                                  searchPath_node_gt hvk, ds_div_gt hvk hbk2]
                      · have hblk2 : b < lk := by omega
                        -- b < lk
                        by_cases hvlk : v < lk
                        · -- recurse: pair lives inside the splayed-left grandchild
                          have hsz : (BinaryTree.node la lx lb).num_nodes ≤ n := by
                            have : (BinaryTree.node la lx lb).num_nodes
                                = 1 + la.num_nodes + lb.num_nodes := rfl
                            omega
                          have hLHS : divergeSuffix v b (splay (BinaryTree.node
                                (BinaryTree.node (BinaryTree.node la lx lb) lk lr) k r) q)
                              = divergeSuffix v b
                                  (splay (BinaryTree.node la lx lb) q) := by
                            rw [hT, ds_both_gt hqv hqb, ds_both_lt hvlk hblk2, hS,
                                ds_both_gt hqv hqb]
                          have hRHS : divergeSuffix v b (BinaryTree.node
                                (BinaryTree.node (BinaryTree.node la lx lb) lk lr) k r)
                              = divergeSuffix v b (BinaryTree.node la lx lb) := by
                            rw [ds_both_lt (show v < k by omega) hbk2,
                                ds_both_lt hvlk hblk2]
                          rcases ih (BinaryTree.node la lx lb) hsz q b v hbll hqll hqb hbv
                            with h | ⟨x, hx, h⟩
                          · exact Or.inl (by rw [hLHS, h, hRHS])
                          · refine Or.inr ⟨x, ?_, ?_⟩
                            · rw [hpathq, searchPath_node_lt hqlk]
                              exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)
                            · rw [hLHS, h, hRHS]
                        · by_cases hvlk2 : v = lk
                          · refine Or.inl ?_
                            rw [hT, ds_both_gt hqv hqb, ds_self hvlk2,
                                ds_both_lt (show v < k by omega) hbk2, ds_self hvlk2]
                          · have hlkv : lk < v := by omega
                            rcases Nat.lt_trichotomy v k with hvk | hvk | hvk
                            · refine Or.inr ⟨k, ?_, ?_⟩
                              · rw [hpathq]; exact List.mem_cons_self
                              · rw [hT, ds_both_gt hqv hqb, ds_div_gt hlkv hblk2,
                                    searchPath_node_lt hvk,
                                    ds_both_lt hvk hbk2, ds_div_gt hlkv hblk2]
                            · refine Or.inr ⟨k, ?_, ?_⟩
                              · rw [hpathq]; exact List.mem_cons_self
                              · rw [hT, ds_both_gt hqv hqb, ds_div_gt hlkv hblk2,
                                    searchPath_node_self hvk, ds_self hvk]
                            · refine Or.inr ⟨k, ?_, ?_⟩
                              · rw [hpathq]; exact List.mem_cons_self
                              · rw [hT, ds_both_gt hqv hqb, ds_div_gt hlkv hblk2,
                                    searchPath_node_gt hvk, ds_div_gt hvk hbk2]
            · by_cases hlkq : lk < q
              · -- ---- zig-zag ----
                have hqlr : q ∈ lr.toKeyList := mem_toKeyList_right hFll hlkq hql
                cases lr with
                | empty => simp [BinaryTree.toKeyList] at hqlr
                | node la lx lb =>
                  obtain ⟨A, B, hS⟩ :=
                    splay_root_of_mem q (BinaryTree.node la lx lb) hblr hqlr
                  have hT : splay (BinaryTree.node
                        (BinaryTree.node ll lk (BinaryTree.node la lx lb)) k r) q
                      = BinaryTree.node (BinaryTree.node ll lk A) q
                          (BinaryTree.node B k r) :=
                    splay_zigzag_shape ll (BinaryTree.node la lx lb) r A B lk k q q
                      hqk hqlt hlkq (fun h => nomatch h) hS
                  by_cases hkb : k < b
                  · refine Or.inl ?_
                    rw [hT, ds_both_gt hqv hqb,
                        ds_both_gt (show k < v by omega) hkb,
                        ds_both_gt (show k < v by omega) hkb]
                  · by_cases hbk : b = k
                    · by_cases hvk : v = k
                      · refine Or.inl ?_
                        rw [hT, ds_both_gt hqv hqb, ds_self hvk, ds_self hvk]
                      · have hkv : k < v := by omega
                        refine Or.inl ?_
                        rw [hT, ds_both_gt hqv hqb, ds_qroot_gt hbk hkv,
                            ds_qroot_gt hbk hkv]
                    · have hbk2 : b < k := by omega
                      rcases Nat.lt_trichotomy v k with hvk | hvk | hvk
                      · -- recurse into the splayed right grandchild
                        have hsz : (BinaryTree.node la lx lb).num_nodes ≤ n := by
                          have : (BinaryTree.node la lx lb).num_nodes
                              = 1 + la.num_nodes + lb.num_nodes := rfl
                          omega
                        have hLHS : divergeSuffix v b (splay (BinaryTree.node
                              (BinaryTree.node ll lk (BinaryTree.node la lx lb)) k r) q)
                            = divergeSuffix v b
                                (splay (BinaryTree.node la lx lb) q) := by
                          rw [hT, ds_both_gt hqv hqb, ds_both_lt hvk hbk2, hS,
                              ds_both_gt hqv hqb]
                        have hRHS : divergeSuffix v b (BinaryTree.node
                              (BinaryTree.node ll lk (BinaryTree.node la lx lb)) k r)
                            = divergeSuffix v b (BinaryTree.node la lx lb) := by
                          rw [ds_both_lt hvk hbk2,
                              ds_both_gt (show lk < v by omega) (show lk < b by omega)]
                        rcases ih (BinaryTree.node la lx lb) hsz q b v hblr hqlr hqb hbv
                          with h | ⟨x, hx, h⟩
                        · exact Or.inl (by rw [hLHS, h, hRHS])
                        · refine Or.inr ⟨x, ?_, ?_⟩
                          · rw [hpathq, searchPath_node_gt hlkq]
                            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)
                          · rw [hLHS, h, hRHS]
                      · refine Or.inl ?_
                        rw [hT, ds_both_gt hqv hqb, ds_self hvk, ds_self hvk]
                      · refine Or.inl ?_
                        rw [hT, ds_both_gt hqv hqb, ds_div_gt hvk hbk2,
                            ds_div_gt hvk hbk2]
              · -- ---- zig (q found at left child) ----
                have hqlk2 : q = lk := by omega
                have hT : splay (BinaryTree.node (BinaryTree.node ll lk lr) k r) q
                    = BinaryTree.node ll lk (BinaryTree.node lr k r) :=
                  splay_zig_found hqlt hqlk hlkq ll lr r
                have hlkb : lk < b := by omega
                have hlkv : lk < v := by omega
                by_cases hkb : k < b
                · refine Or.inl ?_
                  rw [hT, ds_both_gt hlkv hlkb,
                      ds_both_gt (show k < v by omega) hkb,
                      ds_both_gt (show k < v by omega) hkb]
                · by_cases hbk : b = k
                  · by_cases hvk : v = k
                    · refine Or.inl ?_
                      rw [hT, ds_both_gt hlkv hlkb, ds_self hvk, ds_self hvk]
                    · have hkv : k < v := by omega
                      refine Or.inl ?_
                      rw [hT, ds_both_gt hlkv hlkb, ds_qroot_gt hbk hkv,
                          ds_qroot_gt hbk hkv]
                  · have hbk2 : b < k := by omega
                    rcases Nat.lt_trichotomy v k with hvk | hvk | hvk
                    · refine Or.inl ?_
                      rw [hT, ds_both_gt hlkv hlkb, ds_both_lt hvk hbk2,
                          ds_both_lt hvk hbk2, ds_both_gt hlkv hlkb]
                    · refine Or.inl ?_
                      rw [hT, ds_both_gt hlkv hlkb, ds_self hvk, ds_self hvk]
                    · refine Or.inl ?_
                      rw [hT, ds_both_gt hlkv hlkb, ds_div_gt hvk hbk2,
                          ds_div_gt hvk hbk2]
        · -- ===== q descends RIGHT (k < q < b ≤ v) =====
          have hklt : k < q := by omega
          have hkb : k < b := by omega
          have hkv : k < v := by omega
          have hqr : q ∈ r.toKeyList := mem_toKeyList_right hFl hklt hmem
          have hpathq : searchPath q (BinaryTree.node l k r) = k :: searchPath q r :=
            searchPath_node_gt hklt _ _
          cases r with
          | empty => simp [BinaryTree.toKeyList] at hqr
          | node rl rk rr =>
            rcases isBST_node_iff.mp hbr with ⟨hFrl, hFrr, hbrl, hbrr⟩
            have hkrk : k < rk := (forallTree_node_iff.mp hFr).2.1
            have hnn2 : (BinaryTree.node rl rk rr).num_nodes
                = 1 + rl.num_nodes + rr.num_nodes := rfl
            by_cases hqrk : q < rk
            · -- ---- zag-zig ----
              have hqrl : q ∈ rl.toKeyList := mem_toKeyList_left hFrr hqrk hqr
              cases rl with
              | empty => simp [BinaryTree.toKeyList] at hqrl
              | node ra rx rb =>
                obtain ⟨A, B, hS⟩ :=
                  splay_root_of_mem q (BinaryTree.node ra rx rb) hbrl hqrl
                have hT : splay (BinaryTree.node l k
                      (BinaryTree.node (BinaryTree.node ra rx rb) rk rr)) q
                    = BinaryTree.node (BinaryTree.node l k A) q
                        (BinaryTree.node B rk rr) :=
                  splay_zagzig_shape l (BinaryTree.node ra rx rb) rr A B rk k q q
                    hqk hklt hqrk (fun h => nomatch h) hS
                by_cases hrkb : rk < b
                · refine Or.inl ?_
                  rw [hT, ds_both_gt hqv hqb,
                      ds_both_gt (show rk < v by omega) hrkb,
                      ds_both_gt hkv hkb, ds_both_gt (show rk < v by omega) hrkb]
                · by_cases hbrk : b = rk
                  · by_cases hvrk : v = rk
                    · refine Or.inl ?_
                      rw [hT, ds_both_gt hqv hqb, ds_self hvrk,
                          ds_both_gt hkv hkb, ds_self hvrk]
                    · have hrkv : rk < v := by omega
                      refine Or.inl ?_
                      rw [hT, ds_both_gt hqv hqb, ds_qroot_gt hbrk hrkv,
                          ds_both_gt hkv hkb, ds_qroot_gt hbrk hrkv]
                  · have hbrk2 : b < rk := by omega
                    rcases Nat.lt_trichotomy v rk with hvrk | hvrk | hvrk
                    · -- recurse
                      have hsz : (BinaryTree.node ra rx rb).num_nodes ≤ n := by
                        have : (BinaryTree.node ra rx rb).num_nodes
                            = 1 + ra.num_nodes + rb.num_nodes := rfl
                        omega
                      have hLHS : divergeSuffix v b (splay (BinaryTree.node l k
                            (BinaryTree.node (BinaryTree.node ra rx rb) rk rr)) q)
                          = divergeSuffix v b
                              (splay (BinaryTree.node ra rx rb) q) := by
                        rw [hT, ds_both_gt hqv hqb, ds_both_lt hvrk hbrk2, hS,
                            ds_both_gt hqv hqb]
                      have hRHS : divergeSuffix v b (BinaryTree.node l k
                            (BinaryTree.node (BinaryTree.node ra rx rb) rk rr))
                          = divergeSuffix v b (BinaryTree.node ra rx rb) := by
                        rw [ds_both_gt hkv hkb, ds_both_lt hvrk hbrk2]
                      rcases ih (BinaryTree.node ra rx rb) hsz q b v hbrl hqrl hqb hbv
                        with h | ⟨x, hx, h⟩
                      · exact Or.inl (by rw [hLHS, h, hRHS])
                      · refine Or.inr ⟨x, ?_, ?_⟩
                        · rw [hpathq, searchPath_node_lt hqrk]
                          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)
                        · rw [hLHS, h, hRHS]
                    · refine Or.inl ?_
                      rw [hT, ds_both_gt hqv hqb, ds_self hvrk,
                          ds_both_gt hkv hkb, ds_self hvrk]
                    · refine Or.inl ?_
                      rw [hT, ds_both_gt hqv hqb, ds_div_gt hvrk hbrk2,
                          ds_both_gt hkv hkb, ds_div_gt hvrk hbrk2]
            · by_cases hrkq : rk < q
              · -- ---- zag-zag ----
                have hqrr : q ∈ rr.toKeyList := mem_toKeyList_right hFrl hrkq hqr
                cases rr with
                | empty => simp [BinaryTree.toKeyList] at hqrr
                | node ra rx rb =>
                  obtain ⟨A, B, hS⟩ :=
                    splay_root_of_mem q (BinaryTree.node ra rx rb) hbrr hqrr
                  have hT : splay (BinaryTree.node l k
                        (BinaryTree.node rl rk (BinaryTree.node ra rx rb))) q
                      = BinaryTree.node (BinaryTree.node
                          (BinaryTree.node l k rl) rk A) q B :=
                    splay_zagzag_shape l rl (BinaryTree.node ra rx rb) A B rk k q q
                      hqk hklt hrkq (fun h => nomatch h) hS
                  have hsz : (BinaryTree.node ra rx rb).num_nodes ≤ n := by
                    have : (BinaryTree.node ra rx rb).num_nodes
                        = 1 + ra.num_nodes + rb.num_nodes := rfl
                    omega
                  have hLHS : divergeSuffix v b (splay (BinaryTree.node l k
                        (BinaryTree.node rl rk (BinaryTree.node ra rx rb))) q)
                      = divergeSuffix v b (splay (BinaryTree.node ra rx rb) q) := by
                    rw [hT, ds_both_gt hqv hqb, hS, ds_both_gt hqv hqb]
                  have hRHS : divergeSuffix v b (BinaryTree.node l k
                        (BinaryTree.node rl rk (BinaryTree.node ra rx rb)))
                      = divergeSuffix v b (BinaryTree.node ra rx rb) := by
                    rw [ds_both_gt hkv hkb,
                        ds_both_gt (show rk < v by omega) (show rk < b by omega)]
                  rcases ih (BinaryTree.node ra rx rb) hsz q b v hbrr hqrr hqb hbv
                    with h | ⟨x, hx, h⟩
                  · exact Or.inl (by rw [hLHS, h, hRHS])
                  · refine Or.inr ⟨x, ?_, ?_⟩
                    · rw [hpathq, searchPath_node_gt hrkq]
                      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)
                    · rw [hLHS, h, hRHS]
              · -- ---- zag (q found at right child) ----
                have hqrk2 : q = rk := by omega
                have hT : splay (BinaryTree.node l k (BinaryTree.node rl rk rr)) q
                    = BinaryTree.node (BinaryTree.node l k rl) rk rr :=
                  splay_zag_found hklt hqrk hrkq l rl rr
                have hrkb : rk < b := by omega
                have hrkv : rk < v := by omega
                refine Or.inl ?_
                rw [hT, ds_both_gt hrkv hrkb, ds_both_gt hkv hkb,
                    ds_both_gt hrkv hrkb]

/-- **(WITHIN-RUN CORE, min-side dive.)**  `q` present in the BST, strictly below the
future opposite-side pair `b ≤ v`: the divergence suffix is preserved verbatim or
gains exactly ONE cons drawn from `q`'s search path. -/

theorem divergeSuffix_splay_found (q b v : Nat) (t : BinaryTree) (hbst : IsBST t)
    (hmem : q ∈ t.toKeyList) (hqb : q < b) (hbv : b ≤ v) :
    divergeSuffix v b (splay t q) = divergeSuffix v b t
    ∨ ∃ x ∈ searchPath q t,
        divergeSuffix v b (splay t q) = x :: divergeSuffix v b t :=
  ds_splay_found_aux t.num_nodes t (Nat.le_refl _) q b v hbst hmem hqb hbv


namespace Splay

/-! ## §D  WITHIN-RUN CORE (mirror): max-side dive `q` strictly above the
opposite-side pair `v ≤ b`. -/

theorem ds_splay_found_mirror_aux :
    ∀ (n : Nat) (t : BinaryTree), t.num_nodes ≤ n → ∀ (q b v : Nat),
      IsBST t → q ∈ t.toKeyList → b < q → v ≤ b →
      divergeSuffix v b (splay t q) = divergeSuffix v b t
      ∨ ∃ x ∈ searchPath q t,
          divergeSuffix v b (splay t q) = x :: divergeSuffix v b t := by
  intro n
  induction n with
  | zero =>
    intro t ht q b v _ hmem _ _
    cases t with
    | empty => simp [BinaryTree.toKeyList] at hmem
    | node l k r =>
      exfalso
      have hnn : (BinaryTree.node l k r).num_nodes = 1 + l.num_nodes + r.num_nodes := rfl
      omega
  | succ n ih =>
    intro t ht q b v hbst hmem hbq hvb
    have hvq : v < q := by omega
    cases t with
    | empty => simp [BinaryTree.toKeyList] at hmem
    | node l k r =>
      rcases isBST_node_iff.mp hbst with ⟨hFl, hFr, hbl, hbr⟩
      have hnn : (BinaryTree.node l k r).num_nodes = 1 + l.num_nodes + r.num_nodes := rfl
      by_cases hqk : q = k
      · rw [splay_eq_of_eq hqk]
        exact Or.inl rfl
      · by_cases hqlt : q < k
        · -- ===== q descends LEFT (v ≤ b < q < k) =====
          have hbk : b < k := by omega
          have hvk : v < k := by omega
          have hql : q ∈ l.toKeyList := mem_toKeyList_left hFr hqlt hmem
          have hpathq : searchPath q (BinaryTree.node l k r) = k :: searchPath q l :=
            searchPath_node_lt hqlt _ _
          cases l with
          | empty => simp [BinaryTree.toKeyList] at hql
          | node ll lk lr =>
            rcases isBST_node_iff.mp hbl with ⟨hFll, hFlr, hbll, hblr⟩
            have hlkk : lk < k := (forallTree_node_iff.mp hFl).2.1
            have hnn2 : (BinaryTree.node ll lk lr).num_nodes
                = 1 + ll.num_nodes + lr.num_nodes := rfl
            by_cases hqlk : q < lk
            · -- ---- zig-zig: straight recursion ----
              have hqll : q ∈ ll.toKeyList := mem_toKeyList_left hFlr hqlk hql
              cases ll with
              | empty => simp [BinaryTree.toKeyList] at hqll
              | node la lx lb =>
                obtain ⟨A, B, hS⟩ :=
                  splay_root_of_mem q (BinaryTree.node la lx lb) hbll hqll
                have hT : splay (BinaryTree.node
                      (BinaryTree.node (BinaryTree.node la lx lb) lk lr) k r) q
                    = BinaryTree.node A q
                        (BinaryTree.node B lk (BinaryTree.node lr k r)) :=
                  splay_zigzig_shape (BinaryTree.node la lx lb) lr r A B lk k q q
                    hqk hqlt hqlk (fun h => nomatch h) hS
                have hsz : (BinaryTree.node la lx lb).num_nodes ≤ n := by
                  have : (BinaryTree.node la lx lb).num_nodes
                      = 1 + la.num_nodes + lb.num_nodes := rfl
                  omega
                have hLHS : divergeSuffix v b (splay (BinaryTree.node
                      (BinaryTree.node (BinaryTree.node la lx lb) lk lr) k r) q)
                    = divergeSuffix v b (splay (BinaryTree.node la lx lb) q) := by
                  rw [hT, ds_both_lt hvq hbq, hS, ds_both_lt hvq hbq]
                have hRHS : divergeSuffix v b (BinaryTree.node
                      (BinaryTree.node (BinaryTree.node la lx lb) lk lr) k r)
                    = divergeSuffix v b (BinaryTree.node la lx lb) := by
                  rw [ds_both_lt hvk hbk,
                      ds_both_lt (show v < lk by omega) (show b < lk by omega)]
                rcases ih (BinaryTree.node la lx lb) hsz q b v hbll hqll hbq hvb
                  with h | ⟨x, hx, h⟩
                · exact Or.inl (by rw [hLHS, h, hRHS])
                · refine Or.inr ⟨x, ?_, ?_⟩
                  · rw [hpathq, searchPath_node_lt hqlk]
                    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)
                  · rw [hLHS, h, hRHS]
            · by_cases hlkq : lk < q
              · -- ---- zig-zag ----
                have hqlr : q ∈ lr.toKeyList := mem_toKeyList_right hFll hlkq hql
                cases lr with
                | empty => simp [BinaryTree.toKeyList] at hqlr
                | node la lx lb =>
                  obtain ⟨A, B, hS⟩ :=
                    splay_root_of_mem q (BinaryTree.node la lx lb) hblr hqlr
                  have hT : splay (BinaryTree.node
                        (BinaryTree.node ll lk (BinaryTree.node la lx lb)) k r) q
                      = BinaryTree.node (BinaryTree.node ll lk A) q
                          (BinaryTree.node B k r) :=
                    splay_zigzag_shape ll (BinaryTree.node la lx lb) r A B lk k q q
                      hqk hqlt hlkq (fun h => nomatch h) hS
                  by_cases hlkb : lk < b
                  · by_cases hlkv : lk < v
                    · -- recurse
                      have hsz : (BinaryTree.node la lx lb).num_nodes ≤ n := by
                        have : (BinaryTree.node la lx lb).num_nodes
                            = 1 + la.num_nodes + lb.num_nodes := rfl
                        omega
                      have hLHS : divergeSuffix v b (splay (BinaryTree.node
                            (BinaryTree.node ll lk (BinaryTree.node la lx lb)) k r) q)
                          = divergeSuffix v b
                              (splay (BinaryTree.node la lx lb) q) := by
                        rw [hT, ds_both_lt hvq hbq, ds_both_gt hlkv hlkb, hS,
                            ds_both_lt hvq hbq]
                      have hRHS : divergeSuffix v b (BinaryTree.node
                            (BinaryTree.node ll lk (BinaryTree.node la lx lb)) k r)
                          = divergeSuffix v b (BinaryTree.node la lx lb) := by
                        rw [ds_both_lt hvk hbk, ds_both_gt hlkv hlkb]
                      rcases ih (BinaryTree.node la lx lb) hsz q b v hblr hqlr hbq hvb
                        with h | ⟨x, hx, h⟩
                      · exact Or.inl (by rw [hLHS, h, hRHS])
                      · refine Or.inr ⟨x, ?_, ?_⟩
                        · rw [hpathq, searchPath_node_gt hlkq]
                          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)
                        · rw [hLHS, h, hRHS]
                    · by_cases hvlk : v = lk
                      · refine Or.inl ?_
                        rw [hT, ds_both_lt hvq hbq, ds_self hvlk,
                            ds_both_lt hvk hbk, ds_self hvlk]
                      · have hvlk2 : v < lk := by omega
                        refine Or.inl ?_
                        rw [hT, ds_both_lt hvq hbq, ds_div_lt hvlk2 hlkb,
                            ds_both_lt hvk hbk, ds_div_lt hvlk2 hlkb]
                  · by_cases hblk : b = lk
                    · by_cases hvlk : v = lk
                      · refine Or.inl ?_
                        rw [hT, ds_both_lt hvq hbq, ds_self hvlk,
                            ds_both_lt hvk hbk, ds_self hvlk]
                      · have hvlk2 : v < lk := by omega
                        refine Or.inl ?_
                        rw [hT, ds_both_lt hvq hbq, ds_qroot_lt hblk hvlk2,
                            ds_both_lt hvk hbk, ds_qroot_lt hblk hvlk2]
                    · have hblk2 : b < lk := by omega
                      refine Or.inl ?_
                      rw [hT, ds_both_lt hvq hbq,
                          ds_both_lt (show v < lk by omega) hblk2,
                          ds_both_lt hvk hbk,
                          ds_both_lt (show v < lk by omega) hblk2]
              · -- ---- zig (q found at left child) ----
                have hqlk2 : q = lk := by omega
                have hT : splay (BinaryTree.node (BinaryTree.node ll lk lr) k r) q
                    = BinaryTree.node ll lk (BinaryTree.node lr k r) :=
                  splay_zig_found hqlt hqlk hlkq ll lr r
                have hblk : b < lk := by omega
                have hvlk : v < lk := by omega
                refine Or.inl ?_
                rw [hT, ds_both_lt hvlk hblk, ds_both_lt hvk hbk,
                    ds_both_lt hvlk hblk]
        · -- ===== q descends RIGHT (k < q) =====
          have hklt : k < q := by omega
          have hqr : q ∈ r.toKeyList := mem_toKeyList_right hFl hklt hmem
          have hpathq : searchPath q (BinaryTree.node l k r) = k :: searchPath q r :=
            searchPath_node_gt hklt _ _
          cases r with
          | empty => simp [BinaryTree.toKeyList] at hqr
          | node rl rk rr =>
            rcases isBST_node_iff.mp hbr with ⟨hFrl, hFrr, hbrl, hbrr⟩
            have hkrk : k < rk := (forallTree_node_iff.mp hFr).2.1
            have hnn2 : (BinaryTree.node rl rk rr).num_nodes
                = 1 + rl.num_nodes + rr.num_nodes := rfl
            by_cases hqrk : q < rk
            · -- ---- zag-zig ----
              have hqrl : q ∈ rl.toKeyList := mem_toKeyList_left hFrr hqrk hqr
              cases rl with
              | empty => simp [BinaryTree.toKeyList] at hqrl
              | node ra rx rb =>
                obtain ⟨A, B, hS⟩ :=
                  splay_root_of_mem q (BinaryTree.node ra rx rb) hbrl hqrl
                have hT : splay (BinaryTree.node l k
                      (BinaryTree.node (BinaryTree.node ra rx rb) rk rr)) q
                    = BinaryTree.node (BinaryTree.node l k A) q
                        (BinaryTree.node B rk rr) :=
                  splay_zagzig_shape l (BinaryTree.node ra rx rb) rr A B rk k q q
                    hqk hklt hqrk (fun h => nomatch h) hS
                by_cases hbk : b < k
                · refine Or.inl ?_
                  rw [hT, ds_both_lt hvq hbq,
                      ds_both_lt (show v < k by omega) hbk,
                      ds_both_lt (show v < k by omega) hbk]
                · by_cases hbk2 : b = k
                  · by_cases hvk : v = k
                    · refine Or.inl ?_
                      rw [hT, ds_both_lt hvq hbq, ds_self hvk, ds_self hvk]
                    · have hvk2 : v < k := by omega
                      refine Or.inl ?_
                      rw [hT, ds_both_lt hvq hbq, ds_qroot_lt hbk2 hvk2,
                          ds_qroot_lt hbk2 hvk2]
                  · have hkb : k < b := by omega
                    rcases Nat.lt_trichotomy v k with hvk | hvk | hvk
                    · refine Or.inl ?_
                      rw [hT, ds_both_lt hvq hbq, ds_div_lt hvk hkb,
                          ds_div_lt hvk hkb]
                    · refine Or.inl ?_
                      rw [hT, ds_both_lt hvq hbq, ds_self hvk, ds_self hvk]
                    · -- recurse
                      have hsz : (BinaryTree.node ra rx rb).num_nodes ≤ n := by
                        have : (BinaryTree.node ra rx rb).num_nodes
                            = 1 + ra.num_nodes + rb.num_nodes := rfl
                        omega
                      have hLHS : divergeSuffix v b (splay (BinaryTree.node l k
                            (BinaryTree.node (BinaryTree.node ra rx rb) rk rr)) q)
                          = divergeSuffix v b
                              (splay (BinaryTree.node ra rx rb) q) := by
                        rw [hT, ds_both_lt hvq hbq, ds_both_gt hvk hkb, hS,
                            ds_both_lt hvq hbq]
                      have hRHS : divergeSuffix v b (BinaryTree.node l k
                            (BinaryTree.node (BinaryTree.node ra rx rb) rk rr))
                          = divergeSuffix v b (BinaryTree.node ra rx rb) := by
                        rw [ds_both_gt hvk hkb,
                            ds_both_lt (show v < rk by omega) (show b < rk by omega)]
                      rcases ih (BinaryTree.node ra rx rb) hsz q b v hbrl hqrl hbq hvb
                        with h | ⟨x, hx, h⟩
                      · exact Or.inl (by rw [hLHS, h, hRHS])
                      · refine Or.inr ⟨x, ?_, ?_⟩
                        · rw [hpathq, searchPath_node_lt hqrk]
                          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)
                        · rw [hLHS, h, hRHS]
            · by_cases hrkq : rk < q
              · -- ---- zag-zag: the k-cons cases live here ----
                have hqrr : q ∈ rr.toKeyList := mem_toKeyList_right hFrl hrkq hqr
                cases rr with
                | empty => simp [BinaryTree.toKeyList] at hqrr
                | node ra rx rb =>
                  obtain ⟨A, B, hS⟩ :=
                    splay_root_of_mem q (BinaryTree.node ra rx rb) hbrr hqrr
                  have hT : splay (BinaryTree.node l k
                        (BinaryTree.node rl rk (BinaryTree.node ra rx rb))) q
                      = BinaryTree.node (BinaryTree.node
                          (BinaryTree.node l k rl) rk A) q B :=
                    splay_zagzag_shape l rl (BinaryTree.node ra rx rb) A B rk k q q
                      hqk hklt hrkq (fun h => nomatch h) hS
                  by_cases hrkb : rk < b
                  · by_cases hrkv : rk < v
                    · -- recurse
                      have hsz : (BinaryTree.node ra rx rb).num_nodes ≤ n := by
                        have : (BinaryTree.node ra rx rb).num_nodes
                            = 1 + ra.num_nodes + rb.num_nodes := rfl
                        omega
                      have hLHS : divergeSuffix v b (splay (BinaryTree.node l k
                            (BinaryTree.node rl rk (BinaryTree.node ra rx rb))) q)
                          = divergeSuffix v b
                              (splay (BinaryTree.node ra rx rb) q) := by
                        rw [hT, ds_both_lt hvq hbq, ds_both_gt hrkv hrkb, hS,
                            ds_both_lt hvq hbq]
                      have hRHS : divergeSuffix v b (BinaryTree.node l k
                            (BinaryTree.node rl rk (BinaryTree.node ra rx rb)))
                          = divergeSuffix v b (BinaryTree.node ra rx rb) := by
                        rw [ds_both_gt (show k < v by omega) (show k < b by omega),
                            ds_both_gt hrkv hrkb]
                      rcases ih (BinaryTree.node ra rx rb) hsz q b v hbrr hqrr hbq hvb
                        with h | ⟨x, hx, h⟩
                      · exact Or.inl (by rw [hLHS, h, hRHS])
                      · refine Or.inr ⟨x, ?_, ?_⟩
                        · rw [hpathq, searchPath_node_gt hrkq]
                          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)
                        · rw [hLHS, h, hRHS]
                    · by_cases hvrk : v = rk
                      · refine Or.inl ?_
                        rw [hT, ds_both_lt hvq hbq, ds_self hvrk,
                            ds_both_gt (show k < v by omega) (show k < b by omega),
                            ds_self hvrk]
                      · have hvrk2 : v < rk := by omega
                        -- ONE k-cons appears
                        rcases Nat.lt_trichotomy v k with hvk | hvk | hvk
                        · refine Or.inr ⟨k, ?_, ?_⟩
                          · rw [hpathq]; exact List.mem_cons_self
                          · rw [hT, ds_both_lt hvq hbq, ds_div_lt hvrk2 hrkb,
                                searchPath_node_lt hvk,
                                ds_div_lt hvk (show k < b by omega)]
                        · refine Or.inr ⟨k, ?_, ?_⟩
                          · rw [hpathq]; exact List.mem_cons_self
                          · rw [hT, ds_both_lt hvq hbq, ds_div_lt hvrk2 hrkb,
                                searchPath_node_self hvk, ds_self hvk]
                        · refine Or.inr ⟨k, ?_, ?_⟩
                          · rw [hpathq]; exact List.mem_cons_self
                          · rw [hT, ds_both_lt hvq hbq, ds_div_lt hvrk2 hrkb,
                                searchPath_node_gt hvk,
                                ds_both_gt hvk (show k < b by omega),
                                ds_div_lt hvrk2 hrkb]
                  · by_cases hbrk : b = rk
                    · by_cases hvrk : v = rk
                      · refine Or.inl ?_
                        rw [hT, ds_both_lt hvq hbq, ds_self hvrk,
                            ds_both_gt (show k < v by omega) (show k < b by omega),
                            ds_self hvrk]
                      · have hvrk2 : v < rk := by omega
                        rcases Nat.lt_trichotomy v k with hvk | hvk | hvk
                        · refine Or.inr ⟨k, ?_, ?_⟩
                          · rw [hpathq]; exact List.mem_cons_self
                          · rw [hT, ds_both_lt hvq hbq, ds_qroot_lt hbrk hvrk2,
                                searchPath_node_lt hvk,
                                ds_div_lt hvk (show k < b by omega)]
                        · refine Or.inr ⟨k, ?_, ?_⟩
                          · rw [hpathq]; exact List.mem_cons_self
                          · rw [hT, ds_both_lt hvq hbq, ds_qroot_lt hbrk hvrk2,
                                searchPath_node_self hvk, ds_self hvk]
                        · refine Or.inr ⟨k, ?_, ?_⟩
                          · rw [hpathq]; exact List.mem_cons_self
                          · rw [hT, ds_both_lt hvq hbq, ds_qroot_lt hbrk hvrk2,
                                searchPath_node_gt hvk,
                                ds_both_gt hvk (show k < b by omega),
                                ds_qroot_lt hbrk hvrk2]
                    · have hbrk2 : b < rk := by omega
                      by_cases hkb : k < b
                      · rcases Nat.lt_trichotomy v k with hvk | hvk | hvk
                        · refine Or.inl ?_
                          rw [hT, ds_both_lt hvq hbq,
                              ds_both_lt (show v < rk by omega) hbrk2,
                              ds_div_lt hvk hkb, ds_div_lt hvk hkb]
                        · refine Or.inl ?_
                          rw [hT, ds_both_lt hvq hbq,
                              ds_both_lt (show v < rk by omega) hbrk2,
                              ds_self hvk, ds_self hvk]
                        · refine Or.inl ?_
                          rw [hT, ds_both_lt hvq hbq,
                              ds_both_lt (show v < rk by omega) hbrk2,
                              ds_both_gt hvk hkb, ds_both_gt hvk hkb,
                              ds_both_lt (show v < rk by omega) hbrk2]
                      · by_cases hbk : b = k
                        · by_cases hvk : v = k
                          · refine Or.inl ?_
                            rw [hT, ds_both_lt hvq hbq,
                                ds_both_lt (show v < rk by omega) hbrk2,
                                ds_self hvk, ds_self hvk]
                          · have hvk2 : v < k := by omega
                            refine Or.inl ?_
                            rw [hT, ds_both_lt hvq hbq,
                                ds_both_lt (show v < rk by omega) hbrk2,
                                ds_qroot_lt hbk hvk2, ds_qroot_lt hbk hvk2]
                        · have hbk2 : b < k := by omega
                          refine Or.inl ?_
                          rw [hT, ds_both_lt hvq hbq,
                              ds_both_lt (show v < rk by omega) hbrk2,
                              ds_both_lt (show v < k by omega) hbk2,
                              ds_both_lt (show v < k by omega) hbk2]
              · -- ---- zag (q found at right child) ----
                have hqrk2 : q = rk := by omega
                have hT : splay (BinaryTree.node l k (BinaryTree.node rl rk rr)) q
                    = BinaryTree.node (BinaryTree.node l k rl) rk rr :=
                  splay_zag_found hklt hqrk hrkq l rl rr
                have hbrk : b < rk := by omega
                have hvrk : v < rk := by omega
                by_cases hkb : k < b
                · rcases Nat.lt_trichotomy v k with hvk | hvk | hvk
                  · refine Or.inl ?_
                    rw [hT, ds_both_lt hvrk hbrk, ds_div_lt hvk hkb,
                        ds_div_lt hvk hkb]
                  · refine Or.inl ?_
                    rw [hT, ds_both_lt hvrk hbrk, ds_self hvk, ds_self hvk]
                  · refine Or.inl ?_
                    rw [hT, ds_both_lt hvrk hbrk, ds_both_gt hvk hkb,
                        ds_both_gt hvk hkb, ds_both_lt hvrk hbrk]
                · by_cases hbk : b = k
                  · by_cases hvk : v = k
                    · refine Or.inl ?_
                      rw [hT, ds_both_lt hvrk hbrk, ds_self hvk, ds_self hvk]
                    · have hvk2 : v < k := by omega
                      refine Or.inl ?_
                      rw [hT, ds_both_lt hvrk hbrk, ds_qroot_lt hbk hvk2,
                          ds_qroot_lt hbk hvk2]
                  · have hbk2 : b < k := by omega
                    refine Or.inl ?_
                    rw [hT, ds_both_lt hvrk hbrk,
                        ds_both_lt (show v < k by omega) hbk2,
                        ds_both_lt (show v < k by omega) hbk2]

/-- **(WITHIN-RUN CORE, max-side dive.)**  Mirror of `divergeSuffix_splay_found`. -/

theorem divergeSuffix_splay_found_mirror (q b v : Nat) (t : BinaryTree)
    (hbst : IsBST t) (hmem : q ∈ t.toKeyList) (hbq : b < q) (hvb : v ≤ b) :
    divergeSuffix v b (splay t q) = divergeSuffix v b t
    ∨ ∃ x ∈ searchPath q t,
        divergeSuffix v b (splay t q) = x :: divergeSuffix v b t :=
  ds_splay_found_mirror_aux t.num_nodes t (Nat.le_refl _) q b v hbst hmem hbq hvb


-- ===== STEP-OPP complete: oppC2/oppC3 + ordering packages =====
example :
    touchedCount ([4] ++ searchPath 0 (.node (.node (.node .empty 2 .empty) 3 .empty) 4 .empty))
        (searchPath 4 (splay (.node (.node (.node .empty 2 .empty) 3 .empty) 4 .empty) 0))
      = touchedCount [4] (searchPath 4 (.node (.node (.node .empty 2 .empty) 3 .empty) 4 .empty))
        + 2 := by decide

example :
    touchedCount ([] ++ searchPath 0 (.node (.node (.node .empty 2 .empty) 3 .empty) 4 .empty))
        (searchPath 4 (splay (.node (.node (.node .empty 2 .empty) 3 .empty) 4 .empty) 0))
      = touchedCount [] (searchPath 4 (.node (.node (.node .empty 2 .empty) 3 .empty) 4 .empty))
        + 3 := by decide


-- ===== R1-core: generalized halving =====

example :
    touchedCount ([0,3,4] ++ searchPath 1
        (.node .empty 0 (.node (.node (.node (.node .empty 1 .empty) 2 .empty) 3 .empty)
          4 .empty)))
      (searchPath 3 (splay
        (.node .empty 0 (.node (.node (.node (.node .empty 1 .empty) 2 .empty) 3 .empty)
          4 .empty)) 1))
    = touchedCount [0,3,4] (searchPath 3
        (.node .empty 0 (.node (.node (.node (.node .empty 1 .empty) 2 .empty) 3 .empty)
          4 .empty))) + 1 := by decide

example :
    touchedCount ([0] ++ searchPath 1
        (.node .empty 0 (.node (.node (.node (.node .empty 1 .empty) 2 .empty) 3 .empty)
          4 .empty)))
      (searchPath 3 (splay
        (.node .empty 0 (.node (.node (.node (.node .empty 1 .empty) 2 .empty) 3 .empty)
          4 .empty)) 1))
    = touchedCount [0] (searchPath 3
        (.node .empty 0 (.node (.node (.node (.node .empty 1 .empty) 2 .empty) 3 .empty)
          4 .empty))) + 3 := by decide

example :
    touchedCount ([2] ++ searchPath 4 (.node .empty 2 (.node .empty 3 (.node .empty 4 .empty))))
      (searchPath 0 (splay (.node .empty 2 (.node .empty 3 (.node .empty 4 .empty))) 4))
    = touchedCount [2] (searchPath 0
        (.node .empty 2 (.node .empty 3 (.node .empty 4 .empty)))) + 2 := by decide


-- ===== C3 opposite-side verbatim preservation =====

example :
    divergeSuffix 3 2
        (splay (.node (.node .empty 0 .empty) 1 (.node .empty 2 (.node .empty 3 .empty))) 0)
      = divergeSuffix 3 2
        (.node (.node .empty 0 .empty) 1 (.node .empty 2 (.node .empty 3 .empty))) := by
  decide

example :
    divergeSuffix 3 2
        (.node (.node .empty 0 .empty) 1 (.node .empty 2 (.node .empty 3 .empty)))
      = [3] := by decide

example :
    divergeSuffix 3 1 (splay (.node (.node .empty 1 (.node .empty 3 .empty)) 5 .empty) 0)
      ≠ divergeSuffix 3 1 (.node (.node .empty 1 (.node .empty 3 .empty)) 5 .empty) := by
  decide


-- ===== C3 same-side dive preservation =====

example :
    divergeSuffix 3 2 (splay (.node (.node .empty 1 (.node .empty 2 (.node .empty 3 .empty)))
        4 .empty) 0)
      = divergeSuffix 3 2 (.node (.node .empty 1 (.node .empty 2 (.node .empty 3 .empty)))
        4 .empty) := by decide

-- (P2) the one-cons case is realized: q = 0 < b = 2 ≤ y = 5, witness w = 1.

example :
    divergeSuffix 5 2 (splay (.node (.node (.node .empty 1 .empty) 3 .empty) 4 .empty) 0)
      = 4 :: divergeSuffix 5 2 (.node (.node (.node .empty 1 .empty) 3 .empty) 4 .empty) := by
  decide

-- (P2) count form: the constant 1 is TIGHT.

example :
    touchedCount ([] ++ searchPath 0 (.node (.node (.node .empty 1 .empty) 3 .empty) 4 .empty))
        (divergeSuffix 5 2 (splay (.node (.node (.node .empty 1 .empty) 3 .empty) 4 .empty) 0))
      = touchedCount []
          (divergeSuffix 5 2 (.node (.node (.node .empty 1 .empty) 3 .empty) 4 .empty)) + 1 := by
  decide

-- NECESSITY of `b ∉ searchPath q t`: with b = 2 ON q's path (q = 1 < b = 2 ≤ y = 4 all
-- canonical), the excess is already 3; on n-node spine variants it grows without bound.

example :
    touchedCount ([] ++ searchPath 1 (.node .empty 0 (.node (.node (.node (.node .empty 2
          .empty) 3 .empty) 4 .empty) 5 .empty)))
        (divergeSuffix 4 2 (splay (.node .empty 0 (.node (.node (.node (.node .empty 2 .empty)
          3 .empty) 4 .empty) 5 .empty)) 1))
      = touchedCount [] (divergeSuffix 4 2 (.node .empty 0 (.node (.node (.node (.node .empty 2
          .empty) 3 .empty) 4 .empty) 5 .empty))) + 3 := by
  decide


/-! # ============================================================
    # STEP-OPP REPRODUCTION: new material starts here
    # ============================================================ -/

namespace Splay

/-! ## §A  Membership / ForallTree helpers -/

theorem touchedCount_or_split_le (T P c : List Nat) :
    touchedCount (T ++ P) c ≤ touchedCount T c + touchedCount P c := by
  induction c with
  | nil => simp [touchedCount_nil]
  | cons x c ih =>
    rw [touchedCount_cons, touchedCount_cons, touchedCount_cons]
    have h1 : tc1 (T ++ P) x ≤ tc1 T x + tc1 P x := by
      by_cases hT : x ∈ T
      · have h2 : tc1 T x = 1 := by simp [tc1, hT]
        have h3 := tc1_le_one (T ++ P) x
        omega
      · by_cases hP : x ∈ P
        · have h2 : tc1 P x = 1 := by simp [tc1, hP]
          have h3 := tc1_le_one (T ++ P) x
          omega
        · have h2 : tc1 (T ++ P) x = 0 := by
            simp [tc1, List.mem_append, hT, hP]
          omega
    omega

theorem nodup_allEq_length_le_one {l : List Nat} (hnd : l.Nodup)
    (h : ∀ x ∈ l, ∀ y ∈ l, x = y) : l.length ≤ 1 := by
  match l with
  | [] => simp
  | [x] => simp
  | x :: y :: rest =>
    exfalso
    have hxy : x = y :=
      h x List.mem_cons_self y (List.mem_cons_of_mem _ List.mem_cons_self)
    rw [List.nodup_cons] at hnd
    exact hnd.1 (hxy ▸ List.mem_cons_self)

theorem touchedCount_singleton_le_one {c : List Nat} (hnd : c.Nodup) (k : Nat) :
    touchedCount [k] c ≤ 1 := by
  simp only [touchedCount]
  apply nodup_allEq_length_le_one (hnd.filter _)
  intro x hx y hy
  have hx' := List.of_mem_filter hx
  have hy' := List.of_mem_filter hy
  simp only [List.mem_singleton, decide_eq_true_eq] at hx' hy'
  rw [hx', hy']

theorem touchedCount_append_singleton_le (T : List Nat) (k : Nat) {c : List Nat}
    (hnd : c.Nodup) :
    touchedCount (T ++ [k]) c ≤ touchedCount T c + 1 := by
  have h1 := touchedCount_or_split_le T [k] c
  have h2 := touchedCount_singleton_le_one hnd k
  omega

theorem length_filter_split (p : Nat → Bool) (l : List Nat) :
    (l.filter p).length + (l.filter (fun x => !(p x))).length = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases h : p x = true
    · rw [List.filter_cons, List.filter_cons, if_pos h, if_neg (by simp [h])]
      simp only [List.length_cons]
      omega
    · rw [List.filter_cons, List.filter_cons, if_neg h, if_pos (by simp [h])]
      simp only [List.length_cons]
      omega

/-! ## §F  OPP-C2: per-clause preservation of the v-path cost at an opposite access -/

/-- Decomposition skeleton under the weakened touched hypothesis (W6'):
at most ONE key shared by the two old search paths lies outside `T`. -/

theorem touchedCount_shared_decomp_W6 (t : BinaryTree) (q v : Nat) (T : List Nat)
    (hbst : IsBST t)
    (hW6' : ∀ z₁ ∈ searchPath q t, z₁ ∈ searchPath v t → z₁ ∉ T →
            ∀ z₂ ∈ searchPath q t, z₂ ∈ searchPath v t → z₂ ∉ T → z₁ = z₂) :
    ∃ p' sh : List Nat,
      searchPath v t = sh ++ divergeSuffix v q t
      ∧ touchedCount (T ++ searchPath q t) (searchPath v (splay t q))
          ≤ p'.length + touchedCount T (divergeSuffix v q t)
      ∧ sh.length + touchedCount T (divergeSuffix v q t)
          ≤ touchedCount T (searchPath v t) + 1
      ∧ 2 * p'.length ≤ sh.length + 5 := by
  obtain ⟨p', hnew, hp'⟩ := searchPath_splay_decomp q v t hbst
  obtain ⟨sh, hold, hshq⟩ := searchPath_eq_shared_append_suffix q v t
  refine ⟨p', sh, hold, ?_, ?_, ?_⟩
  · -- new-path cost: at most |p'| on-path nodes plus the (T-counted) suffix
    have e1 : touchedCount (T ++ searchPath q t) (searchPath v (splay t q))
        = touchedCount (T ++ searchPath q t) p'
          + touchedCount T (divergeSuffix v q t) := by
      rw [hnew, touchedCount_append]
      congr 1
      exact touchedCount_congr (fun z hz => by
        constructor
        · intro hzT'
          rcases List.mem_append.mp hzT' with h | h
          · exact h
          · exact absurd h (divergeSuffix_disjoint t hbst z hz)
        · exact fun h => List.mem_append_left _ h)
    have e3 := touchedCount_le_length (T ++ searchPath q t) p'
    omega
  · -- old-path cost: the shared prefix is fully T-touched up to ONE exception
    have e2 : touchedCount T (searchPath v t)
        = touchedCount T sh + touchedCount T (divergeSuffix v q t) := by
      rw [hold, touchedCount_append]
    have hnd : sh.Nodup := by
      have h := searchPath_nodup v t hbst
      rw [hold] at h
      exact h.of_append_left
    have hsplit := length_filter_split (fun x => decide (x ∈ T)) sh
    have hle : (sh.filter (fun x => !(decide (x ∈ T)))).length ≤ 1 := by
      apply nodup_allEq_length_le_one (hnd.filter _)
      intro x hx y hy
      have hxsh := List.mem_of_mem_filter hx
      have hysh := List.mem_of_mem_filter hy
      have hxT : x ∉ T := by
        have := List.of_mem_filter hx
        simpa using this
      have hyT : y ∉ T := by
        have := List.of_mem_filter hy
        simpa using this
      exact hW6' x (hshq x hxsh)
        (by rw [hold]; exact List.mem_append_left _ hxsh) hxT
        y (hshq y hysh)
        (by rw [hold]; exact List.mem_append_left _ hysh) hyT
    have htc : touchedCount T sh = (sh.filter (fun x => decide (x ∈ T))).length := rfl
    omega
  · -- generalized halving
    have h5 := keyDepth_splay_le_shared q v t hbst
    rw [← sp_len, ← sp_len, hnew, hold] at h5
    simp only [List.length_append] at h5
    omega

/-- **(OPP-C2, WITHIN-RUN under W6').**  Run-interior geometry
(`rootKey t ≤ q ≤ v` or the mirror) with at most ONE untouched key shared by the
two old search paths: the doubled v-path cost grows by at most 4. -/

theorem touchedCount_within_run_splay_le_W6 (t : BinaryTree) (q v : Nat) (T : List Nat)
    (hbst : IsBST t) (hne : t ≠ .empty)
    (hside : (rootKey t ≤ q ∧ q ≤ v) ∨ (v ≤ q ∧ q ≤ rootKey t))
    (hW6' : ∀ z₁ ∈ searchPath q t, z₁ ∈ searchPath v t → z₁ ∉ T →
            ∀ z₂ ∈ searchPath q t, z₂ ∈ searchPath v t → z₂ ∉ T → z₁ = z₂) :
    2 * touchedCount (T ++ searchPath q t) (searchPath v (splay t q))
      ≤ 2 * touchedCount T (searchPath v t) + 4 := by
  cases t with
  | empty => exact absurd rfl hne
  | node l k r =>
    simp only [rootKey] at hside
    by_cases hqk : q = k
    · -- q at the root: identity splay, q-path = [k]
      rw [splay_eq_of_eq hqk l r, searchPath_node_self hqk l r]
      have := touchedCount_append_singleton_le T k
        (searchPath_nodup v (BinaryTree.node l k r) hbst)
      omega
    · rcases hside with ⟨hq, hv⟩ | ⟨hv, hq⟩
      · have hklt : k < q := by omega
        cases r with
        | empty =>
          rw [splay_right_empty hklt l,
              show searchPath q (BinaryTree.node l k .empty) = [k] by
                rw [searchPath_node_gt hklt]; rfl]
          have := touchedCount_append_singleton_le T k
            (searchPath_nodup v (BinaryTree.node l k .empty) hbst)
          omega
        | node rl rk rr =>
          obtain ⟨p', sh, hold, hX, hO, hhalf⟩ :=
            touchedCount_shared_decomp_W6 (BinaryTree.node l k (BinaryTree.node rl rk rr))
              q v T hbst hW6'
          have hkv : k < v := by omega
          obtain ⟨rest, hrest⟩ := searchPath_node_head v rk rl rr
          have hvpath : searchPath v (BinaryTree.node l k (BinaryTree.node rl rk rr))
              = k :: rk :: rest := by
            rw [searchPath_node_gt hkv, hrest]
          have hkq : k ∈ searchPath q (BinaryTree.node l k (BinaryTree.node rl rk rr)) :=
            root_mem_searchPath q k _ _
          have hrkq : rk ∈ searchPath q (BinaryTree.node l k (BinaryTree.node rl rk rr)) := by
            rw [searchPath_node_gt hklt]
            exact List.mem_cons_of_mem _ (root_mem_searchPath q rk rl rr)
          rw [hvpath] at hold
          have h2 : 2 ≤ sh.length := by
            rcases sh with _ | ⟨z0, _ | ⟨z1, sh'⟩⟩
            · exfalso
              simp only [List.nil_append] at hold
              exact divergeSuffix_disjoint (q := q) (y := v) _ hbst k
                (by rw [← hold]; exact List.mem_cons_self) hkq
            · exfalso
              simp only [List.cons_append, List.nil_append] at hold
              injection hold with h1 htl
              exact divergeSuffix_disjoint (q := q) (y := v) _ hbst rk
                (by rw [← htl]; exact List.mem_cons_self) hrkq
            · simp only [List.length_cons]
              omega
          omega
      · have hklt : q < k := by omega
        cases l with
        | empty =>
          rw [splay_left_empty hklt r,
              show searchPath q (BinaryTree.node .empty k r) = [k] by
                rw [searchPath_node_lt hklt]; rfl]
          have := touchedCount_append_singleton_le T k
            (searchPath_nodup v (BinaryTree.node .empty k r) hbst)
          omega
        | node ll lk lr =>
          obtain ⟨p', sh, hold, hX, hO, hhalf⟩ :=
            touchedCount_shared_decomp_W6 (BinaryTree.node (BinaryTree.node ll lk lr) k r)
              q v T hbst hW6'
          have hvk : v < k := by omega
          obtain ⟨rest, hrest⟩ := searchPath_node_head v lk ll lr
          have hvpath : searchPath v (BinaryTree.node (BinaryTree.node ll lk lr) k r)
              = k :: lk :: rest := by
            rw [searchPath_node_lt hvk, hrest]
          have hkq : k ∈ searchPath q (BinaryTree.node (BinaryTree.node ll lk lr) k r) :=
            root_mem_searchPath q k _ _
          have hlkq : lk ∈ searchPath q (BinaryTree.node (BinaryTree.node ll lk lr) k r) := by
            rw [searchPath_node_lt hklt]
            exact List.mem_cons_of_mem _ (root_mem_searchPath q lk ll lr)
          rw [hvpath] at hold
          have h2 : 2 ≤ sh.length := by
            rcases sh with _ | ⟨z0, _ | ⟨z1, sh'⟩⟩
            · exfalso
              simp only [List.nil_append] at hold
              exact divergeSuffix_disjoint (q := q) (y := v) _ hbst k
                (by rw [← hold]; exact List.mem_cons_self) hkq
            · exfalso
              simp only [List.cons_append, List.nil_append] at hold
              injection hold with h1 htl
              exact divergeSuffix_disjoint (q := q) (y := v) _ hbst lk
                (by rw [← htl]; exact List.mem_cons_self) hlkq
            · simp only [List.length_cons]
              omega
          omega

/-- **(OPP-C2, RUN BOUNDARY.)**  Root between `q` and `v`, root touched:
doubled deepening ≤ 4 (from the proven `+2` core). -/

theorem touchedCount_boundary_splay_le_two (t : BinaryTree) (q v : Nat) (T : List Nat)
    (hbst : IsBST t) (hne : t ≠ .empty) (hroot : rootKey t ∈ T)
    (hside : (q ≤ rootKey t ∧ rootKey t ≤ v) ∨ (v ≤ rootKey t ∧ rootKey t ≤ q)) :
    2 * touchedCount (T ++ searchPath q t) (searchPath v (splay t q))
      ≤ 2 * touchedCount T (searchPath v t) + 4 := by
  have := touchedCount_mixed_splay_le t q v T hbst hne hroot hside
  omega

/-- **(OPP-C2), all four ordering packages.**
`T' := T ++ searchPath q t`; the process supplies either a run-boundary package
(root between, root touched) or a within-run package (W6'). -/

theorem oppC2_step (t : BinaryTree) (q v : Nat) (T : List Nat)
    (hbst : IsBST t) (hne : t ≠ .empty)
    (hpkg :
      (((q ≤ rootKey t ∧ rootKey t ≤ v) ∨ (v ≤ rootKey t ∧ rootKey t ≤ q))
          ∧ rootKey t ∈ T)
      ∨ (((rootKey t ≤ q ∧ q ≤ v) ∨ (v ≤ q ∧ q ≤ rootKey t))
          ∧ (∀ z₁ ∈ searchPath q t, z₁ ∈ searchPath v t → z₁ ∉ T →
             ∀ z₂ ∈ searchPath q t, z₂ ∈ searchPath v t → z₂ ∉ T → z₁ = z₂))) :
    2 * touchedCount (T ++ searchPath q t) (searchPath v (splay t q))
      ≤ 2 * touchedCount T (searchPath v t) + 4 := by
  rcases hpkg with ⟨hside, hroot⟩ | ⟨hside, hW6'⟩
  · exact touchedCount_boundary_splay_le_two t q v T hbst hne hroot hside
  · exact touchedCount_within_run_splay_le_W6 t q v T hbst hne hside hW6'


namespace Splay

/-! ## §G  OPP-C3: suffix-change bound for the future pair (b, v) at an opposite access -/

/-- Mirror of `divergeSuffix_disjoint_dive`: under `y ≤ b ≤ q` the old divergence
suffix avoids `q`'s search path. -/

theorem divergeSuffix_disjoint_dive_mirror :
    ∀ (t : BinaryTree), IsBST t → ∀ (q b y : Nat), b ≤ q → y ≤ b →
      ∀ z ∈ divergeSuffix y b t, z ∉ searchPath q t := by
  intro t
  induction t with
  | empty => intro _ q b y _ _ z hz; simp at hz
  | node l k r ihl ihr =>
    intro hbst q b y hbq hyb z hz
    rcases isBST_node_iff.mp hbst with ⟨hFl, hFr, hbl, hbr⟩
    by_cases hyk : y = k
    · rw [ds_self hyk] at hz; simp at hz
    · by_cases hbk : b = k
      · have hky : y < k := by omega
        rw [ds_qroot_lt hbk hky] at hz
        have hzk : z < k := mem_searchPath_forall (p := fun u => u < k) hFl hz
        intro hmem
        by_cases hqk : q = k
        · rw [searchPath_node_self hqk] at hmem
          simp only [List.mem_singleton] at hmem
          omega
        · have hklt : k < q := by omega
          rw [searchPath_node_gt hklt] at hmem
          rcases List.mem_cons.mp hmem with rfl | hmem
          · omega
          · have : k < z := mem_searchPath_forall hFr hmem
            omega
      · by_cases hbk2 : b < k
        · have hyk2 : y < k := by omega
          rw [ds_both_lt hyk2 hbk2] at hz
          have hzk : z < k := mem_divergeSuffix_forall l hFl z hz
          intro hmem
          by_cases hqk : q = k
          · rw [searchPath_node_self hqk] at hmem
            simp only [List.mem_singleton] at hmem
            omega
          · by_cases hqlt : q < k
            · rw [searchPath_node_lt hqlt] at hmem
              rcases List.mem_cons.mp hmem with rfl | hmem
              · omega
              · exact ihl hbl q b y hbq hyb z hz hmem
            · have hklt : k < q := by omega
              rw [searchPath_node_gt hklt] at hmem
              rcases List.mem_cons.mp hmem with rfl | hmem
              · omega
              · have : k < z := mem_searchPath_forall hFr hmem
                omega
        · have hkb : k < b := by omega
          have hklt : k < q := by omega
          by_cases hyk2 : k < y
          · rw [ds_both_gt hyk2 hkb] at hz
            have hzk : k < z := mem_divergeSuffix_forall r hFr z hz
            intro hmem
            rw [searchPath_node_gt hklt] at hmem
            rcases List.mem_cons.mp hmem with rfl | hmem
            · omega
            · exact ihr hbr q b y hbq hyb z hz hmem
          · have hyk3 : y < k := by omega
            rw [ds_div_lt hyk3 hkb] at hz
            have hzk : z < k := mem_searchPath_forall (p := fun u => u < k) hFl hz
            intro hmem
            rw [searchPath_node_gt hklt] at hmem
            rcases List.mem_cons.mp hmem with rfl | hmem
            · omega
            · have : k < z := mem_searchPath_forall hFr hmem
              omega

theorem touchedCount_divergeSuffix_extend_mirror (q b y : Nat) (t : BinaryTree)
    (T : List Nat) (hbst : IsBST t) (hbq : b ≤ q) (hyb : y ≤ b) :
    touchedCount (T ++ searchPath q t) (divergeSuffix y b t)
      = touchedCount T (divergeSuffix y b t) :=
  touchedCount_congr (fun z hz => by
    have hzn := divergeSuffix_disjoint_dive_mirror t hbst q b y hbq hyb z hz
    simp only [List.mem_append]
    exact ⟨fun h => h.resolve_right hzn, Or.inl⟩)

/-- **(OPP-C3), all four ordering packages, STRUCTURAL form.**
After the opposite-side access `q`, the divergence suffix of the future same-side
pair `(b, v)` is `heads ++ tail` with `tail` a suffix of the OLD divergence suffix,
`|heads| ≤ 1` (one better than the conjectured 2), and every head on `q`'s search
path.  Boundary packages give `heads = []` (verbatim preservation). -/

theorem oppC3_step (t : BinaryTree) (q b v : Nat) (hbst : IsBST t)
    (hpkg :
      (q ≤ rootKey t ∧ rootKey t ≤ b ∧ rootKey t ≤ v)
      ∨ (rootKey t ≤ q ∧ b ≤ rootKey t ∧ v ≤ rootKey t)
      ∨ (q ∈ t.toKeyList ∧ q < b ∧ b ≤ v)
      ∨ (q ∈ t.toKeyList ∧ b < q ∧ v ≤ b)) :
    ∃ heads tail,
      divergeSuffix v b (splay t q) = heads ++ tail
      ∧ tail.IsSuffix (divergeSuffix v b t)
      ∧ heads.length ≤ 1
      ∧ ∀ z ∈ heads, z ∈ searchPath q t := by
  rcases hpkg with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine ⟨[], divergeSuffix v b t, ?_, List.suffix_refl _, by simp, by simp⟩
    rw [divergeSuffix_splay_opposite_left t q b v hbst h1 h2 h3, List.nil_append]
  · refine ⟨[], divergeSuffix v b t, ?_, List.suffix_refl _, by simp, by simp⟩
    rw [divergeSuffix_splay_opposite_right t q b v hbst h1 h2 h3, List.nil_append]
  · rcases divergeSuffix_splay_found q b v t hbst h1 h2 h3 with h | ⟨x, hx, h⟩
    · refine ⟨[], divergeSuffix v b t, ?_, List.suffix_refl _, by simp, by simp⟩
      rw [h, List.nil_append]
    · refine ⟨[x], divergeSuffix v b t, ?_, List.suffix_refl _, by simp, ?_⟩
      · rw [h, List.singleton_append]
      · intro z hz
        simp only [List.mem_singleton] at hz
        exact hz ▸ hx
  · rcases divergeSuffix_splay_found_mirror q b v t hbst h1 h2 h3 with h | ⟨x, hx, h⟩
    · refine ⟨[], divergeSuffix v b t, ?_, List.suffix_refl _, by simp, by simp⟩
      rw [h, List.nil_append]
    · refine ⟨[x], divergeSuffix v b t, ?_, List.suffix_refl _, by simp, ?_⟩
      · rw [h, List.singleton_append]
      · intro z hz
        simp only [List.mem_singleton] at hz
        exact hz ▸ hx

/-- **(OPP-C3), COUNT COROLLARY, all four packages.**
`T' := T ++ searchPath q t`; the doubled touched-count of the (b,v)-divergence
suffix grows by at most 4 (in fact at most 2). -/

theorem oppC3_count (t : BinaryTree) (q b v : Nat) (T : List Nat) (hbst : IsBST t)
    (hpkg :
      (q ≤ rootKey t ∧ rootKey t ≤ b ∧ rootKey t ≤ v)
      ∨ (rootKey t ≤ q ∧ b ≤ rootKey t ∧ v ≤ rootKey t)
      ∨ (q ∈ t.toKeyList ∧ q < b ∧ b ≤ v)
      ∨ (q ∈ t.toKeyList ∧ b < q ∧ v ≤ b)) :
    2 * touchedCount (T ++ searchPath q t) (divergeSuffix v b (splay t q))
      ≤ 2 * touchedCount T (divergeSuffix v b t) + 4 := by
  rcases hpkg with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · rw [touchedCount_divergeSuffix_splay_opposite_left t q b v T hbst h1 h2 h3]
    omega
  · rw [touchedCount_divergeSuffix_splay_opposite_right t q b v T hbst h1 h2 h3]
    omega
  · rcases divergeSuffix_splay_found q b v t hbst h1 h2 h3 with h | ⟨x, hx, h⟩
    · rw [h, touchedCount_divergeSuffix_extend q b v t T hbst (Nat.le_of_lt h2) h3]
      omega
    · rw [h, touchedCount_cons_mem (List.mem_append_right T hx),
          touchedCount_divergeSuffix_extend q b v t T hbst (Nat.le_of_lt h2) h3]
      omega
  · rcases divergeSuffix_splay_found_mirror q b v t hbst h1 h2 h3 with h | ⟨x, hx, h⟩
    · rw [h, touchedCount_divergeSuffix_extend_mirror q b v t T hbst (Nat.le_of_lt h2) h3]
      omega
    · rw [h, touchedCount_cons_mem (List.mem_append_right T hx),
          touchedCount_divergeSuffix_extend_mirror q b v t T hbst (Nat.le_of_lt h2) h3]
      omega

/-- Requested weaker form of the heads bound (≤ 2), immediate from the sharp form. -/

theorem oppC3_step_two (t : BinaryTree) (q b v : Nat) (hbst : IsBST t)
    (hpkg :
      (q ≤ rootKey t ∧ rootKey t ≤ b ∧ rootKey t ≤ v)
      ∨ (rootKey t ≤ q ∧ b ≤ rootKey t ∧ v ≤ rootKey t)
      ∨ (q ∈ t.toKeyList ∧ q < b ∧ b ≤ v)
      ∨ (q ∈ t.toKeyList ∧ b < q ∧ v ≤ b)) :
    ∃ heads tail,
      divergeSuffix v b (splay t q) = heads ++ tail
      ∧ tail.IsSuffix (divergeSuffix v b t)
      ∧ heads.length ≤ 2
      ∧ ∀ z ∈ heads, z ∈ searchPath q t := by
  obtain ⟨heads, tail, h1, h2, h3, h4⟩ := oppC3_step t q b v hbst hpkg
  exact ⟨heads, tail, h1, h2, by omega, h4⟩


namespace Splay

/-! ## §H  Necessity of STRICT `q < b` (resp. `b < q`) in the within-run packages.

At `q = b` the suffix can gain THREE on-path heads: left spine 9-7-5-3-1,
`q = b = 1`, `v = 6` — old suffix `[]`, new suffix `[7,3,5]` (all on `q`'s search
path).  So neither `heads ≤ 2` nor the doubled `+4` count bound survives at `q = b`;
the empirical scan shows the excess grows with the spine length.  Machine-checked: -/

example :
    divergeSuffix 6 1 (.node (.node (.node (.node (.node .empty 1 .empty) 3 .empty)
        5 .empty) 7 .empty) 9 .empty) = [] := by decide

example :
    divergeSuffix 6 1 (splay (.node (.node (.node (.node (.node .empty 1 .empty) 3 .empty)
        5 .empty) 7 .empty) 9 .empty) 1) = [7, 3, 5] := by decide

example :
    2 * touchedCount
        ([] ++ searchPath 1 (.node (.node (.node (.node (.node .empty 1 .empty) 3 .empty)
            5 .empty) 7 .empty) 9 .empty))
        (divergeSuffix 6 1 (splay (.node (.node (.node (.node (.node .empty 1 .empty)
            3 .empty) 5 .empty) 7 .empty) 9 .empty) 1))
      = 2 * touchedCount []
          (divergeSuffix 6 1 (.node (.node (.node (.node (.node .empty 1 .empty) 3 .empty)
              5 .empty) 7 .empty) 9 .empty)) + 6 := by decide


-- ===== ordered-drain ghost (hstepOwn prerequisite) =====
@[simp] theorem claimMet_update_r (T L : List ℕ) (cl : GhostClaim) (r' : ℕ) :
    claimMet T L { cl with r := r' } = claimMet T L cl := rfl

/-- Filter-split: a `metP`-filter splits disjointly into the `metP ∧ ¬metS` part and
the `metP ∧ metS` part, and `claimsListTotal` splits accordingly. -/

theorem claimsListTotal_filter_split (metP metS : GhostClaim → Bool)
    (cs : List GhostClaim) :
    claimsListTotal (cs.filter metP)
      = claimsListTotal (cs.filter (fun cl => metP cl && !metS cl))
        + claimsListTotal (cs.filter (fun cl => metP cl && metS cl)) := by
  induction cs with
  | nil => simp
  | cons cl rest ih =>
      cases hP : metP cl <;> cases hS : metS cl <;>
        simp only [List.filter_cons, hP, hS, Bool.not_true, Bool.not_false,
          Bool.and_true, Bool.and_false,
          Bool.false_eq_true, if_false, if_true, claimsListTotal_cons] <;>
        omega

/-- Filter monotonicity on totals: a sub-predicate filters out no more budget. -/

theorem claimsListTotal_filter_subset (p q : GhostClaim → Bool)
    (hpq : ∀ cl, p cl = true → q cl = true) (cs : List GhostClaim) :
    claimsListTotal (cs.filter p) ≤ claimsListTotal (cs.filter q) := by
  induction cs with
  | nil => simp
  | cons cl rest ih =>
      cases hp : p cl with
      | false =>
          cases hq : q cl with
          | false =>
              simp only [List.filter_cons, hp, hq, Bool.false_eq_true, if_false]
              exact ih
          | true =>
              simp only [List.filter_cons, hp, hq, Bool.false_eq_true, if_false,
                if_true, claimsListTotal_cons]
              omega
      | true =>
          have hq : q cl = true := hpq cl hp
          simp only [List.filter_cons, hp, hq, if_true, claimsListTotal_cons]
          omega

/-- Pass-through: a greedy drain along `p` leaves the `q`-filtered sublist untouched
whenever every `p`-claim is (and stays, under any budget update) a non-`q`-claim. -/

theorem consumeGreedy_filter_disjoint (cs : List GhostClaim) (p q : GhostClaim → Bool)
    (hpq' : ∀ (cl : GhostClaim) (r' : ℕ), p cl = true → q { cl with r := r' } = false)
    (hpq : ∀ cl : GhostClaim, p cl = true → q cl = false) :
    ∀ amount : ℕ, ((consumeGreedy amount cs p).2).filter q = cs.filter q := by
  induction cs with
  | nil => intro amount; simp [consumeGreedy]
  | cons cl rest ih =>
      intro amount
      cases hp : p cl with
      | false =>
          simp only [consumeGreedy, hp, Bool.false_eq_true, if_false]
          rw [List.filter_cons, List.filter_cons, ih amount]
      | true =>
          have hqc : q cl = false := hpq cl hp
          have hqm : q { cl with r := cl.r - min amount cl.r } = false :=
            hpq' cl (cl.r - min amount cl.r) hp
          simp only [consumeGreedy, hp, if_true, List.filter_cons, hqm, hqc,
            Bool.false_eq_true, if_false]
          exact ih _

/-- Exact drain on a `q`-filtered total, for a drain predicate `p` BELOW `q`: when
every `p`-claim is (and stays, under any budget update) a `q`-claim, the greedy drain
along `p` removes exactly `min amount (p-total)` from the `q`-filtered total. -/

theorem consumeGreedy_snd_filter (cs : List GhostClaim) (p q : GhostClaim → Bool)
    (hpq' : ∀ (cl : GhostClaim) (r' : ℕ), p cl = true → q { cl with r := r' } = true)
    (hpq : ∀ cl : GhostClaim, p cl = true → q cl = true) :
    ∀ amount : ℕ, claimsListTotal (((consumeGreedy amount cs p).2).filter q)
      = claimsListTotal (cs.filter q) - min amount (claimsListTotal (cs.filter p)) := by
  induction cs with
  | nil => intro amount; simp [consumeGreedy]
  | cons cl rest ih =>
      intro amount
      have hsub := claimsListTotal_filter_subset p q hpq rest
      cases hp : p cl with
      | false =>
          cases hqc : q cl with
          | false =>
              simp only [consumeGreedy, hp, Bool.false_eq_true, if_false,
                List.filter_cons, hqc]
              exact ih amount
          | true =>
              simp only [consumeGreedy, hp, Bool.false_eq_true, if_false,
                List.filter_cons, hqc, if_true, claimsListTotal_cons]
              rw [ih amount]
              omega
      | true =>
          have hqc : q cl = true := hpq cl hp
          have hqm : q { cl with r := cl.r - min amount cl.r } = true :=
            hpq' cl (cl.r - min amount cl.r) hp
          simp only [consumeGreedy, hp, if_true, List.filter_cons, hqm, hqc,
            claimsListTotal_cons]
          rw [ih (amount - min amount cl.r)]
          have hm2 := Nat.min_le_right (amount - min amount cl.r)
            (claimsListTotal (rest.filter p))
          omega

/-! ### The two-phase ordered consume -/

/-- Ordered two-phase drain.  Phase 1: drain the claims with
`metP cl = true ∧ metS cl = false` (in list order); phase 2: drain the pool;
phase 3: drain the claims with `metP cl = true ∧ metS cl = true` (in list order).
Returns `(undrained remainder, updated claims, updated pool)`.  Implemented as two
`consumeGreedy` passes with pool arithmetic in between. -/

def consumeOrdered (amount : ℕ) (cs : List GhostClaim) (metP metS : GhostClaim → Bool)
    (pool : ℕ) : ℕ × List GhostClaim × ℕ :=
  let res1 := consumeGreedy amount cs (fun cl => metP cl && !metS cl)
  let res2 := consumeGreedy (res1.1 - min res1.1 pool) res1.2
    (fun cl => metP cl && metS cl)
  (res2.1, res2.2, pool - res1.1)

/-- The undrained remainder of the ordered drain is exactly `amount` minus what the
`metP`-claims plus the pool could pay together (the suffix split is invisible to the
remainder).  Requires `metS` to ignore budgets (true for `claimMet`). -/

theorem consumeOrdered_fst (amount : ℕ) (cs : List GhostClaim)
    (metP metS : GhostClaim → Bool) (pool : ℕ)
    (hS : ∀ (cl : GhostClaim) (r' : ℕ), metS { cl with r := r' } = metS cl) :
    (consumeOrdered amount cs metP metS pool).1
      = amount - min amount (claimsListTotal (cs.filter metP) + pool) := by
  show (consumeGreedy
      ((consumeGreedy amount cs (fun cl => metP cl && !metS cl)).1
        - min (consumeGreedy amount cs (fun cl => metP cl && !metS cl)).1 pool)
      (consumeGreedy amount cs (fun cl => metP cl && !metS cl)).2
      (fun cl => metP cl && metS cl)).1
    = amount - min amount (claimsListTotal (cs.filter metP) + pool)
  set R1 := consumeGreedy amount cs (fun cl => metP cl && !metS cl) with hR1
  have h1f : R1.1 = amount
      - min amount (claimsListTotal (cs.filter (fun cl => metP cl && !metS cl))) := by
    rw [hR1]; exact consumeGreedy_fst cs _ amount
  have hpass : (R1.2).filter (fun cl => metP cl && metS cl)
      = cs.filter (fun cl => metP cl && metS cl) := by
    rw [hR1]
    refine consumeGreedy_filter_disjoint cs _ _ ?_ ?_ amount
    · intro cl r' hp
      have hs : metS cl = false := by
        cases h : metS cl
        · rfl
        · rw [h] at hp; simp at hp
      simp [hS, hs]
    · intro cl hp
      have hs : metS cl = false := by
        cases h : metS cl
        · rfl
        · rw [h] at hp; simp at hp
      simp [hs]
  have h2f : (consumeGreedy (R1.1 - min R1.1 pool) R1.2
        (fun cl => metP cl && metS cl)).1
      = (R1.1 - min R1.1 pool)
        - min (R1.1 - min R1.1 pool)
            (claimsListTotal ((R1.2).filter (fun cl => metP cl && metS cl))) :=
    consumeGreedy_fst R1.2 _ (R1.1 - min R1.1 pool)
  rw [h2f, hpass]
  have hsplit := claimsListTotal_filter_split metP metS cs
  omega

/-- **Exact-drain totals for the ordered consume.**  The surviving total budget
(claims plus pool) drops by exactly `min amount (metP-total + pool)` — identical to
the unordered greedy drain; the ordering only redistributes WHICH claims pay.
Requires `metS` to ignore budgets (true for `claimMet`). -/

theorem consumeOrdered_total (amount : ℕ) (cs : List GhostClaim)
    (metP metS : GhostClaim → Bool) (pool : ℕ)
    (hS : ∀ (cl : GhostClaim) (r' : ℕ), metS { cl with r := r' } = metS cl) :
    claimsListTotal (consumeOrdered amount cs metP metS pool).2.1
      + (consumeOrdered amount cs metP metS pool).2.2
      = claimsListTotal cs + pool
        - min amount (claimsListTotal (cs.filter metP) + pool) := by
  show claimsListTotal (consumeGreedy
        ((consumeGreedy amount cs (fun cl => metP cl && !metS cl)).1
          - min (consumeGreedy amount cs (fun cl => metP cl && !metS cl)).1 pool)
        (consumeGreedy amount cs (fun cl => metP cl && !metS cl)).2
        (fun cl => metP cl && metS cl)).2
      + (pool - (consumeGreedy amount cs (fun cl => metP cl && !metS cl)).1)
    = claimsListTotal cs + pool
        - min amount (claimsListTotal (cs.filter metP) + pool)
  set R1 := consumeGreedy amount cs (fun cl => metP cl && !metS cl) with hR1
  have h1f : R1.1 = amount
      - min amount (claimsListTotal (cs.filter (fun cl => metP cl && !metS cl))) := by
    rw [hR1]; exact consumeGreedy_fst cs _ amount
  have h1s : claimsListTotal R1.2 = claimsListTotal cs
      - min amount (claimsListTotal (cs.filter (fun cl => metP cl && !metS cl))) := by
    rw [hR1]; exact consumeGreedy_snd cs _ amount
  have hpass : (R1.2).filter (fun cl => metP cl && metS cl)
      = cs.filter (fun cl => metP cl && metS cl) := by
    rw [hR1]
    refine consumeGreedy_filter_disjoint cs _ _ ?_ ?_ amount
    · intro cl r' hp
      have hs : metS cl = false := by
        cases h : metS cl
        · rfl
        · rw [h] at hp; simp at hp
      simp [hS, hs]
    · intro cl hp
      have hs : metS cl = false := by
        cases h : metS cl
        · rfl
        · rw [h] at hp; simp at hp
      simp [hs]
  have h2s : claimsListTotal (consumeGreedy (R1.1 - min R1.1 pool) R1.2
        (fun cl => metP cl && metS cl)).2
      = claimsListTotal R1.2
        - min (R1.1 - min R1.1 pool)
            (claimsListTotal ((R1.2).filter (fun cl => metP cl && metS cl))) :=
    consumeGreedy_snd R1.2 _ (R1.1 - min R1.1 pool)
  rw [h2s, hpass]
  have hsplit := claimsListTotal_filter_split metP metS cs
  have hPle := claimsListTotal_filter_le metP cs
  omega

/-- **Phase-3 bound (surviving `metS`-budget).**  The `metS`-claims drain only AFTER
the `metP ∧ ¬metS` claims and the pool are exhausted, so the surviving `metS`-budget
is at least the original minus the post-phase-1/2 residue
`amount − min amount ((metP∧¬metS)-total + pool)`.  Requires `metS` to ignore budgets
(true for `claimMet`). -/

theorem consumeOrdered_phase3_le (amount : ℕ) (cs : List GhostClaim)
    (metP metS : GhostClaim → Bool) (pool : ℕ)
    (hS : ∀ (cl : GhostClaim) (r' : ℕ), metS { cl with r := r' } = metS cl) :
    claimsListTotal (cs.filter metS)
      - (amount - min amount
          (claimsListTotal (cs.filter (fun cl => metP cl && !metS cl)) + pool))
      ≤ claimsListTotal ((consumeOrdered amount cs metP metS pool).2.1.filter metS) := by
  show claimsListTotal (cs.filter metS)
      - (amount - min amount
          (claimsListTotal (cs.filter (fun cl => metP cl && !metS cl)) + pool))
    ≤ claimsListTotal (((consumeGreedy
        ((consumeGreedy amount cs (fun cl => metP cl && !metS cl)).1
          - min (consumeGreedy amount cs (fun cl => metP cl && !metS cl)).1 pool)
        (consumeGreedy amount cs (fun cl => metP cl && !metS cl)).2
        (fun cl => metP cl && metS cl)).2).filter metS)
  set R1 := consumeGreedy amount cs (fun cl => metP cl && !metS cl) with hR1
  have h1f : R1.1 = amount
      - min amount (claimsListTotal (cs.filter (fun cl => metP cl && !metS cl))) := by
    rw [hR1]; exact consumeGreedy_fst cs _ amount
  have hph1 : (R1.2).filter metS = cs.filter metS := by
    rw [hR1]
    refine consumeGreedy_filter_disjoint cs _ _ ?_ ?_ amount
    · intro cl r' hp
      have hs : metS cl = false := by
        cases h : metS cl
        · rfl
        · rw [h] at hp; simp at hp
      rw [hS]; exact hs
    · intro cl hp
      cases h : metS cl
      · rfl
      · rw [h] at hp; simp at hp
  have hph3 : claimsListTotal (((consumeGreedy (R1.1 - min R1.1 pool) R1.2
        (fun cl => metP cl && metS cl)).2).filter metS)
      = claimsListTotal ((R1.2).filter metS)
        - min (R1.1 - min R1.1 pool)
            (claimsListTotal ((R1.2).filter (fun cl => metP cl && metS cl))) := by
    refine consumeGreedy_snd_filter R1.2 _ _ ?_ ?_ (R1.1 - min R1.1 pool)
    · intro cl r' hp
      have hs : metS cl = true := by
        cases h : metS cl
        · rw [h] at hp; simp at hp
        · rfl
      rw [hS]; exact hs
    · intro cl hp
      cases h : metS cl
      · rw [h] at hp; simp at hp
      · rfl
  rw [hph3, hph1]
  have hm := Nat.min_le_left (R1.1 - min R1.1 pool)
    (claimsListTotal ((R1.2).filter (fun cl => metP cl && metS cl)))
  omega

/-! ### The ordered own-step and its C1 conservation -/

/-- Ghost-state update on an OWN-side access, ORDERED variant (path `P`, suffix keys
`S`, touched set `T`, cost `c`, fresh count `f`, accessed key `x`, side `isMin`):
identical pipeline to the unordered own-step —
1. `amount := 2*c - min (2*c) (2*kap*(1+f))` (the doubled draw, uncapped form);
2. drain `amount` via the ORDERED two-phase consume: `P`-met-but-not-`S`-met claims
   first, then the pool, then the `S`-met claims last;
3. add the debris claim (span of `P`'s live-side keys, budget `c`);
4. prune all claims to the live side. -/

def ghostStepOwnOrdered (kap : ℕ) (T P S : List ℕ) (c f x : ℕ) (isMin : Bool)
    (g : GhostState) : GhostState :=
  let amount := 2 * c - min (2 * c) (2 * kap * (1 + f))
  let res := consumeOrdered amount g.claims (claimMet T P) (claimMet T S) g.pool
  { claims := pruneClaims isMin x (res.2.1 ++ ghostDebris P c x isMin),
    pool := res.2.2 }

/-- **C1 conservation for the ordered own-step, exact unconditional form.**  An
ordered own-side ghost step decreases the ghost total by exactly
`min amount (metTotal + pool)` before the `+ c` debris repay (pruning can only lose
more) — the ordering of the drain is invisible to the conservation ledger. -/

theorem ghost_C1_own_ordered_min (kap : ℕ) (T P S : List ℕ) (c f x : ℕ) (isMin : Bool)
    (g : GhostState) (D : ℕ)
    (h : claimsTotal g + g.pool ≤ D) :
    claimsTotal (ghostStepOwnOrdered kap T P S c f x isMin g)
      + (ghostStepOwnOrdered kap T P S c f x isMin g).pool
      ≤ D - min D (min (2 * c - min (2 * c) (2 * kap * (1 + f)))
            (metTotal T P g + g.pool)) + c := by
  have hclaims : claimsTotal (ghostStepOwnOrdered kap T P S c f x isMin g)
      = claimsListTotal (pruneClaims isMin x
          ((consumeOrdered (2 * c - min (2 * c) (2 * kap * (1 + f))) g.claims
              (claimMet T P) (claimMet T S) g.pool).2.1
            ++ ghostDebris P c x isMin)) := rfl
  have hpool : (ghostStepOwnOrdered kap T P S c f x isMin g).pool
      = (consumeOrdered (2 * c - min (2 * c) (2 * kap * (1 + f))) g.claims
          (claimMet T P) (claimMet T S) g.pool).2.2 := rfl
  have h' : claimsListTotal g.claims + g.pool ≤ D := h
  have hmt : metTotal T P g = claimsListTotal (g.claims.filter (claimMet T P)) := rfl
  have htot := consumeOrdered_total (2 * c - min (2 * c) (2 * kap * (1 + f)))
    g.claims (claimMet T P) (claimMet T S) g.pool
    (fun cl r' => claimMet_update_r T S cl r')
  have hflt := claimsListTotal_filter_le (claimMet T P) g.claims
  have hdeb := ghostDebris_total_le P c x isMin
  have hprune := claimsListTotal_prune_le isMin x
    ((consumeOrdered (2 * c - min (2 * c) (2 * kap * (1 + f))) g.claims
        (claimMet T P) (claimMet T S) g.pool).2.1
      ++ ghostDebris P c x isMin)
  rw [claimsListTotal_append] at hprune
  rw [hclaims, hpool, hmt]
  set K := 2 * kap * (1 + f) with hK
  omega

/-- **C1 conservation for the ordered own-step, ledger-matching form** (EXACT mirror
of `ghost_C1_own`).  Under the cover hypothesis (supplied by the C2-strict invariant:
the met claims plus the pool cover the uncapped draw), an ordered own-side ghost step
keeps the ghost total below the ledger's own-side update
`D - min D amount + c = D - draw + c`. -/

theorem ghost_C1_own_ordered (kap : ℕ) (T P S : List ℕ) (c f x : ℕ) (isMin : Bool)
    (g : GhostState) (D : ℕ)
    (h : claimsTotal g + g.pool ≤ D)
    (hcover : 2 * c - min (2 * c) (2 * kap * (1 + f)) ≤ metTotal T P g + g.pool) :
    claimsTotal (ghostStepOwnOrdered kap T P S c f x isMin g)
      + (ghostStepOwnOrdered kap T P S c f x isMin g).pool
      ≤ D - min D (2 * c - min (2 * c) (2 * kap * (1 + f))) + c := by
  have hmin := ghost_C1_own_ordered_min kap T P S c f x isMin g D h
  rwa [min_eq_left hcover] at hmin

/-- C1 conservation restated against the frozen ledger's `draw`: the RHS is literally
the ledger's own-side update `D - draw kap c f D + c`. -/

theorem ghost_C1_own_ordered_draw (kap : ℕ) (T P S : List ℕ) (c f x : ℕ)
    (isMin : Bool) (g : GhostState) (D : ℕ)
    (h : claimsTotal g + g.pool ≤ D)
    (hcover : 2 * c - min (2 * c) (2 * kap * (1 + f)) ≤ metTotal T P g + g.pool) :
    claimsTotal (ghostStepOwnOrdered kap T P S c f x isMin g)
      + (ghostStepOwnOrdered kap T P S c f x isMin g).pool
      ≤ D - draw kap c f D + c :=
  ghost_C1_own_ordered kap T P S c f x isMin g D h hcover

/-- Unconditional safety: even without the cover hypothesis, an ordered own-side step
never pushes the ghost total above `D + c`. -/

theorem ghost_C1_own_ordered_safe (kap : ℕ) (T P S : List ℕ) (c f x : ℕ)
    (isMin : Bool) (g : GhostState) (D : ℕ)
    (h : claimsTotal g + g.pool ≤ D) :
    claimsTotal (ghostStepOwnOrdered kap T P S c f x isMin g)
      + (ghostStepOwnOrdered kap T P S c f x isMin g).pool ≤ D + c := by
  have hmin := ghost_C1_own_ordered_min kap T P S c f x isMin g D h
  set K := 2 * kap * (1 + f) with hK
  omega


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

/-! ### Ghost state and claims (development file, verbatim) -/

/-- An interval claim: keys in `[lo, hi]` carry a (doubled) remnant budget `r`. -/

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


-- ===== hstepP: the final-lemma development (this session) =====
/-! # hstepP development: the pooled-invariant step

Strategy: the pooled `INVP`'s C2 clause (current access only) is too weak to
reproduce across an opposite-side step, so we strengthen the induction with the
per-side-next form `INVS` (validated empirically: /tmp/pooled_strong.py, zero
violations, slack 12).  `INVS i → INVP i`, `INVS` reproduces, and `hstepP`
follows by an inner induction from `0` (the ghost state is a function of
`(init, X, i)`, so the `INVP i` hypothesis can be ignored). -/

/-- The STRONG pooled invariant: C1 conservation; C2S next-access cover for the
first access of EACH side; C3 chain cover (same as `INVP`). -/
def INVS {n : ℕ} (kap : ℕ) (init : BinaryTree) (X : Fin n → ℕ) (i : ℕ) : Prop :=
  (claimsTotal (ghostAtP kap init X i) + (ghostAtP kap init X i).pool
      ≤ ledgerP kap (costN init X) (freshN init X) i)
  ∧ (∀ (b : Bool) (j : ℕ), FirstOwnAfter X i b j →
      2 * tcOf init X (accessN X j) i
        ≤ metSumP kap init X i (accessN X j) + (ghostAtP kap init X i).pool + 14)
  ∧ (∀ (b : Bool) (j k : ℕ), ConsecOwnAfter X i b j k →
      2 * tcSuffixOf init X (accessN X k) (accessN X j) i
        ≤ metSumOnP kap init X i
            (divergeSuffix (accessN X k) (accessN X j) (processTree init X i))
          + (ghostAtP kap init X i).pool + 8)

/-- Base case for the strong invariant. -/
theorem INVS_zero {n : ℕ} (kap : ℕ) (init : BinaryTree) (X : Fin n → ℕ) :
    INVS kap init X 0 := by
  refine ⟨?_, ?_, ?_⟩
  · have hg : ghostAtP kap init X 0 = ⟨[], 0⟩ := rfl
    have hl : ledgerP kap (costN init X) (freshN init X) 0 = 0 := rfl
    rw [hg, hl]
    show claimsListTotal [] + 0 ≤ 0
    simp
  · intro b j _
    have h0 : tcOf init X (accessN X j) 0 = 0 := by
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

/-- The strong invariant implies the pooled invariant. -/
theorem INVS_imp_INVP {n : ℕ} (kap : ℕ) (init : BinaryTree) (X : Fin n → ℕ)
    (i : ℕ) (h : INVS kap init X i) : INVP kap init X i := by
  obtain ⟨hC1, hC2S, hC3⟩ := h
  exact ⟨hC1, fun hi => hC2S (sideF X i) i (firstOwnAfter_self X i hi), hC3⟩

/-! ## Plumbing: the path-length split at an in-range index -/

/-- Path-length split at an in-range index: `cost + 1 = touched + fresh`. -/
theorem costN_split {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (hsize : init.num_nodes = n) (hbst : IsBST init) (i : ℕ) (hi : i < n) :
    costN init X i + 1 = tcOf init X (accessN X i) i + freshN init X i := by
  have hacc : accessN X i = X ⟨i, hi⟩ := by
    unfold accessN; rw [dif_pos hi]
  have hcost : costN init X i
      = (processTree init X i).search_path_len (X ⟨i, hi⟩) - 1 := by
    unfold costN; rw [dif_pos hi]
  have hfreshN : freshN init X i
      = ((searchPath (X ⟨i, hi⟩) (processTree init X i)).toFinset
          \ touchedUpTo (processTree init X) X i).card := by
    unfold freshN; rw [dif_pos hi]
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
  have : tcOf init X (accessN X i) i
      = touchedCount (touchedList init X i)
          (searchPath (X ⟨i, hi⟩) (processTree init X i)) := by
    unfold tcOf
    rw [hacc]
  omega

/-- The cover inequality from the strong C2 clause at the access itself. -/
theorem cover_of_C2S {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (hsize : init.num_nodes = n) (hbst : IsBST init) (i : ℕ) (hi : i < n)
    (hC2S : ∀ (b : Bool) (j : ℕ), FirstOwnAfter X i b j →
      2 * tcOf init X (accessN X j) i
        ≤ metSumP 6 init X i (accessN X j) + (ghostAtP 6 init X i).pool + 14) :
    2 * costN init X i
        - min (2 * costN init X i) (2 * 6 * (1 + freshN init X i))
      ≤ metTotal (touchedList init X i) (pathN init X i) (ghostAtP 6 init X i)
        + (ghostAtP 6 init X i).pool := by
  have h2 := hC2S (sideF X i) i (firstOwnAfter_self X i hi)
  have hmet := metSumP_eq_metTotal_path 6 init X i hi
  have hsplit := costN_split init X hsize hbst i hi
  rw [hmet] at h2
  omega

/-! ## Batch 1: list-level and claims-level helpers -/

/-- A zero-amount greedy drain leaves the claims untouched. -/
theorem consumeGreedy_zero (cs : List GhostClaim) (met : GhostClaim → Bool) :
    (consumeGreedy 0 cs met).2 = cs := by
  induction cs with
  | nil => rfl
  | cons cl rest ih =>
      cases hm : met cl with
      | false => simp only [consumeGreedy, hm, Bool.false_eq_true, if_false, ih]
      | true =>
          simp only [consumeGreedy, hm, if_true, ih, Nat.zero_min, Nat.sub_zero]

/-- A zero-amount greedy drain has zero remainder. -/
theorem consumeGreedy_zero_fst (cs : List GhostClaim) (met : GhostClaim → Bool) :
    (consumeGreedy 0 cs met).1 = 0 := by
  rw [consumeGreedy_fst]
  omega

/-- `pruneClaims` distributes over append. -/
theorem pruneClaims_append (isMin : Bool) (x : ℕ) (cs ds : List GhostClaim) :
    pruneClaims isMin x (cs ++ ds) = pruneClaims isMin x cs ++ pruneClaims isMin x ds := by
  unfold pruneClaims
  rw [List.filter_append, List.map_append]

/-- Nodup sublist-of-members length bound: a duplicate-free list whose members
all lie in `l'` is no longer than `l'`. -/
theorem nodup_length_le_of_subset {l l' : List ℕ} (hnd : l.Nodup)
    (hsub : ∀ z ∈ l, z ∈ l') : l.length ≤ l'.length := by
  classical
  calc l.length = l.toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ ≤ l'.toFinset.card := by
        apply Finset.card_le_card
        intro z hz
        rw [List.mem_toFinset] at hz ⊢
        exact hsub z hz
    _ ≤ l'.length := l'.toFinset_card_le

/-- Folded min is below the seed. -/
theorem foldl_min_le_init (l : List ℕ) : ∀ a : ℕ, l.foldl min a ≤ a := by
  induction l with
  | nil => intro a; simp
  | cons u us ih =>
      intro a
      simp only [List.foldl_cons]
      exact le_trans (ih (min a u)) (min_le_left a u)

/-- Folded min is below every member. -/
theorem foldl_min_le_of_mem {l : List ℕ} {z : ℕ} (hz : z ∈ l) :
    ∀ a : ℕ, l.foldl min a ≤ z := by
  induction l with
  | nil => simp at hz
  | cons u us ih =>
      intro a
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hz with rfl | hz'
      · exact le_trans (foldl_min_le_init us (min a z)) (min_le_right a z)
      · exact ih hz' (min a u)

/-- Folded max is above the seed. -/
theorem le_foldl_max_init (l : List ℕ) : ∀ a : ℕ, a ≤ l.foldl max a := by
  induction l with
  | nil => intro a; simp
  | cons u us ih =>
      intro a
      simp only [List.foldl_cons]
      exact le_trans (le_max_left a u) (ih (max a u))

/-- Folded max is above every member. -/
theorem le_foldl_max_of_mem {l : List ℕ} {z : ℕ} (hz : z ∈ l) :
    ∀ a : ℕ, z ≤ l.foldl max a := by
  induction l with
  | nil => simp at hz
  | cons u us ih =>
      intro a
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hz with rfl | hz'
      · exact le_trans (le_max_right a z) (le_foldl_max_init us (max a z))
      · exact ih hz' (max a u)

/-- `listMinD` lower-bounds every member. -/
theorem listMinD_le_of_mem {l : List ℕ} {z : ℕ} (hz : z ∈ l) : listMinD l ≤ z := by
  cases l with
  | nil => simp at hz
  | cons y ys =>
      show ys.foldl min y ≤ z
      rcases List.mem_cons.mp hz with rfl | hz'
      · exact foldl_min_le_init ys z
      · exact foldl_min_le_of_mem hz' y

/-- `listMaxD` upper-bounds every member. -/
theorem le_listMaxD_of_mem {l : List ℕ} {z : ℕ} (hz : z ∈ l) : z ≤ listMaxD l := by
  cases l with
  | nil => simp at hz
  | cons y ys =>
      show z ≤ ys.foldl max y
      rcases List.mem_cons.mp hz with rfl | hz'
      · exact le_foldl_max_init ys z
      · exact le_foldl_max_of_mem hz' y

/-- Appending to the touched set does not change the count of a list disjoint
from the appended part. -/
theorem touchedCount_append_T_of_disjoint {T P c : List ℕ}
    (h : ∀ z ∈ c, z ∉ P) :
    touchedCount (T ++ P) c = touchedCount T c := by
  apply touchedCount_congr
  intro z hz
  rw [List.mem_append]
  constructor
  · rintro (hT | hP)
    · exact hT
    · exact absurd hP (h z hz)
  · exact Or.inl

/-- **Prune-filter survival.**  If every claim satisfying `p` is alive and its
clip satisfies `p'`, the `p'`-met budget of the pruned list is at least the
`p`-met budget of the original. -/
theorem prune_filter_total_ge (isMin : Bool) (x : ℕ)
    (p p' : GhostClaim → Bool) (cs : List GhostClaim)
    (h : ∀ cl, p cl = true →
      claimAlive isMin x cl = true ∧ p' (clipClaim isMin x cl) = true) :
    claimsListTotal (cs.filter p)
      ≤ claimsListTotal ((pruneClaims isMin x cs).filter p') := by
  induction cs with
  | nil => simp [pruneClaims]
  | cons cl rest ih =>
      unfold pruneClaims at ih ⊢
      cases hp : p cl with
      | false =>
          simp only [List.filter_cons, hp, Bool.false_eq_true, if_false]
          cases ha : claimAlive isMin x cl with
          | false =>
              simp only [ha, Bool.false_eq_true, if_false]
              exact ih
          | true =>
              simp only [ha, if_true, List.map_cons, List.filter_cons]
              cases hp' : p' (clipClaim isMin x cl) with
              | false =>
                  simp only [Bool.false_eq_true, if_false]
                  exact ih
              | true =>
                  simp only [if_true, claimsListTotal_cons]
                  omega
      | true =>
          obtain ⟨ha, hp'⟩ := h cl hp
          simp only [List.filter_cons, hp, if_true, ha, List.map_cons,
            hp', claimsListTotal_cons, clipClaim_r]
          omega

/-! ## Batch 1b: diverge-suffix key bounds -/

/-- Keys on the diverge suffix of `y` past `q` lie strictly above `q`
when `q ≤ y` (BST). -/
theorem mem_divergeSuffix_gt {q y : ℕ} (hqy : q ≤ y) :
    ∀ (t : BinaryTree), IsBST t → ∀ z ∈ divergeSuffix y q t, q < z := by
  intro t
  induction t with
  | empty => intro _ z hz; simp at hz
  | node l k r ihl ihr =>
      intro hbst z hz
      rcases isBST_node_iff.mp hbst with ⟨hFl, hFr, hbl, hbr⟩
      by_cases hyk : y = k
      · rw [ds_self hyk] at hz; simp at hz
      · by_cases hqk : q = k
        · have hky : k < y := by omega
          rw [ds_qroot_gt hqk hky] at hz
          have := mem_searchPath_forall hFr hz
          omega
        · by_cases hyl : y < k
          · have hql : q < k := by omega
            rw [ds_both_lt hyl hql] at hz
            exact ihl hbl z hz
          · have hky : k < y := by omega
            by_cases hqr : k < q
            · rw [ds_both_gt hky hqr] at hz
              exact ihr hbr z hz
            · have hql : q < k := by omega
              rw [ds_div_gt hky hql] at hz
              have := mem_searchPath_forall hFr hz
              omega

/-- Mirror: keys on the diverge suffix of `y` past `q` lie strictly below `q`
when `y ≤ q` (BST). -/
theorem mem_divergeSuffix_lt {q y : ℕ} (hyq : y ≤ q) :
    ∀ (t : BinaryTree), IsBST t → ∀ z ∈ divergeSuffix y q t, z < q := by
  intro t
  induction t with
  | empty => intro _ z hz; simp at hz
  | node l k r ihl ihr =>
      intro hbst z hz
      rcases isBST_node_iff.mp hbst with ⟨hFl, hFr, hbl, hbr⟩
      by_cases hyk : y = k
      · rw [ds_self hyk] at hz; simp at hz
      · by_cases hqk : q = k
        · have hyk' : y < k := by omega
          rw [ds_qroot_lt hqk hyk'] at hz
          have := mem_searchPath_forall (p := fun w => w < k) hFl hz
          omega
        · by_cases hyl : y < k
          · by_cases hql : q < k
            · rw [ds_both_lt hyl hql] at hz
              exact ihl hbl z hz
            · have hkq : k < q := by omega
              rw [ds_div_lt hyl hkq] at hz
              have := mem_searchPath_forall (p := fun w => w < k) hFl hz
              omega
          · have hky : k < y := by omega
            have hkq : k < q := by omega
            rw [ds_both_gt hky hkq] at hz
            exact ihr hbr z hz


/-! ## Batch 3: claim decoding and the debris-met lemma -/

/-- Decoding `claimMet`. -/
theorem claimMet_iff {T L : List ℕ} {cl : GhostClaim} :
    claimMet T L cl = true ↔ ∃ z ∈ L, z ∈ T ∧ cl.lo ≤ z ∧ z ≤ cl.hi := by
  unfold claimMet
  rw [List.any_eq_true]
  constructor
  · rintro ⟨z, hzL, hz⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hz
    exact ⟨z, hzL, hz.1.1, hz.1.2, hz.2⟩
  · rintro ⟨z, hzL, hzT, hlo, hhi⟩
    refine ⟨z, hzL, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hzT, hlo⟩, hhi⟩

/-- Monotonicity of `claimMet` in both list arguments. -/
theorem claimMet_mono {T T' L L' : List ℕ} {cl : GhostClaim}
    (hT : ∀ z, z ∈ T → z ∈ T') (hL : ∀ z, z ∈ L → z ∈ L')
    (h : claimMet T L cl = true) : claimMet T' L' cl = true := by
  rw [claimMet_iff] at h ⊢
  obtain ⟨z, hzL, hzT, hlo, hhi⟩ := h
  exact ⟨z, hL z hzL, hT z hzT, hlo, hhi⟩

/-- Membership in the live keys, min side. -/
theorem mem_debrisKeys_true {P : List ℕ} {x z : ℕ} :
    z ∈ debrisKeys P x true ↔ z ∈ P ∧ x ≤ z := by
  unfold debrisKeys
  rw [List.mem_filter]
  simp only [if_true, decide_eq_true_eq]

/-- Membership in the live keys, max side. -/
theorem mem_debrisKeys_false {P : List ℕ} {x z : ℕ} :
    z ∈ debrisKeys P x false ↔ z ∈ P ∧ z ≤ x := by
  unfold debrisKeys
  rw [List.mem_filter]
  simp only [Bool.false_eq_true, if_false, decide_eq_true_eq]

/-- The accessed key is always a live key of its own path. -/
theorem accessKey_mem_debrisKeys {P : List ℕ} {x : ℕ} (hx : x ∈ P)
    (isMin : Bool) : x ∈ debrisKeys P x isMin := by
  cases isMin
  · exact mem_debrisKeys_false.mpr ⟨hx, le_rfl⟩
  · exact mem_debrisKeys_true.mpr ⟨hx, le_rfl⟩

/-- **The debris claim survives the prune and is met by any touched list and
path containing the accessed key** (when present, carrying exactly `c`). -/
theorem debris_met_total_witness (isMin : Bool) (P : List ℕ) (c q z : ℕ)
    (T' newpath : List ℕ)
    (hzlive : z ∈ debrisKeys P q isMin) (hznew : z ∈ newpath) (hzT' : z ∈ T')
    (hL : 2 ≤ (debrisKeys P q isMin).length) :
    claimsListTotal ((pruneClaims isMin q (ghostDebris P c q isMin)).filter
        (claimMet T' newpath)) = c := by
  have hlo : listMinD (debrisKeys P q isMin) ≤ z := listMinD_le_of_mem hzlive
  have hhi : z ≤ listMaxD (debrisKeys P q isMin) := le_listMaxD_of_mem hzlive
  have hzside : (isMin = true → q ≤ z) ∧ (isMin = false → z ≤ q) := by
    constructor
    · intro h; rw [h] at hzlive; exact (mem_debrisKeys_true.mp hzlive).2
    · intro h; rw [h] at hzlive; exact (mem_debrisKeys_false.mp hzlive).2
  unfold ghostDebris
  rw [if_pos hL]
  set cl : GhostClaim :=
    ⟨listMinD (debrisKeys P q isMin), listMaxD (debrisKeys P q isMin), c⟩ with hcl
  have halive : claimAlive isMin q cl = true := by
    unfold claimAlive
    cases hM : isMin
    · simp only [Bool.false_eq_true, if_false, decide_eq_true_eq]
      have := hzside.2 hM
      show listMinD (debrisKeys P q isMin) ≤ q
      omega
    · simp only [if_true, decide_eq_true_eq]
      have := hzside.1 hM
      show q ≤ listMaxD (debrisKeys P q isMin)
      omega
  have hmet : claimMet T' newpath (clipClaim isMin q cl) = true := by
    rw [claimMet_iff]
    refine ⟨z, hznew, hzT', ?_, ?_⟩
    · unfold clipClaim
      cases hM : isMin
      · simpa using hlo
      · simp only [if_true]
        have := hzside.1 hM
        show max (listMinD (debrisKeys P q isMin)) q ≤ z
        omega
    · unfold clipClaim
      cases hM : isMin
      · simp only [Bool.false_eq_true, if_false]
        have := hzside.2 hM
        show z ≤ min (listMaxD (debrisKeys P q isMin)) q
        omega
      · simpa using hhi
  unfold pruneClaims
  simp only [List.filter_singleton, halive, cond_true, List.map_cons,
    List.map_nil, List.filter_cons, hmet, if_true, List.filter_nil]
  show (clipClaim isMin q cl).r + 0 = c
  rw [clipClaim_r]
  rfl

/-- The accessed-key special case of the debris-met lemma. -/
theorem debris_met_total (isMin : Bool) (P : List ℕ) (c q : ℕ)
    (T' newpath : List ℕ)
    (hqP : q ∈ P) (hqnew : q ∈ newpath) (hqT' : q ∈ T')
    (hL : 2 ≤ (debrisKeys P q isMin).length) :
    claimsListTotal ((pruneClaims isMin q (ghostDebris P c q isMin)).filter
        (claimMet T' newpath)) = c :=
  debris_met_total_witness isMin P c q q T' newpath
    (accessKey_mem_debrisKeys hqP isMin) hqnew hqT' hL

/-- **Suffix-met survival across a zero-drain step**: claims met by a stable
sublist `ds` of both the touched set's complement and the new path survive
pruning and stay met. -/
theorem metSum_survives_prune (isMin : Bool) (q : ℕ) (T P ds newpath : List ℕ)
    (cs : List GhostClaim)
    (hdsnew : ∀ z ∈ ds, z ∈ newpath)
    (hdsLive : ∀ z ∈ ds, (isMin = true → q ≤ z) ∧ (isMin = false → z ≤ q)) :
    claimsListTotal (cs.filter (claimMet T ds))
      ≤ claimsListTotal ((pruneClaims isMin q cs).filter
          (claimMet (T ++ P) newpath)) := by
  apply prune_filter_total_ge
  intro cl hcl
  rw [claimMet_iff] at hcl
  obtain ⟨z, hzds, hzT, hzlo, hzhi⟩ := hcl
  constructor
  · unfold claimAlive
    cases isMin
    · simp only [Bool.false_eq_true, if_false, decide_eq_true_eq]
      have := (hdsLive z hzds).2 rfl
      omega
    · simp only [if_true, decide_eq_true_eq]
      have := (hdsLive z hzds).1 rfl
      omega
  · rw [claimMet_iff]
    refine ⟨z, hdsnew z hzds, List.mem_append_left _ hzT, ?_, ?_⟩
    · unfold clipClaim
      cases isMin
      · simpa using hzlo
      · simp only [if_true]
        have := (hdsLive z hzds).1 rfl
        exact max_le hzlo this
    · unfold clipClaim
      cases isMin
      · simp only [Bool.false_eq_true, if_false]
        have := (hdsLive z hzds).2 rfl
        exact le_min hzhi this
      · simpa using hzhi


/-! ## The drain amount -/

/-- The (uncapped, doubled) drain amount of the pooled step at index `i`,
`κ = 6`. -/
def amountN {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ) (i : ℕ) : ℕ :=
  2 * costN init X i
    - min (2 * costN init X i) (2 * 6 * (1 + freshN init X i))

/-! ## Batch 2: process-level plumbing -/

theorem accessN_lt {n : ℕ} (X : Fin n → ℕ) {i : ℕ} (hi : i < n) :
    accessN X i = X ⟨i, hi⟩ := by
  unfold accessN; rw [dif_pos hi]

theorem pathN_lt {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ) {i : ℕ} (hi : i < n) :
    pathN init X i = searchPath (accessN X i) (processTree init X i) := by
  unfold pathN
  rw [dif_pos hi, accessN_lt X hi]

/-- One ℕ-level process step. -/
theorem processTree_succ_nat {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    {i : ℕ} (hi : i < n) :
    processTree init X (i+1) = splay (processTree init X i) (accessN X i) := by
  rw [processTree_succ_dite, dif_pos hi, accessN_lt X hi]

/-- The accessed key is in the (invariant) key set of every process tree. -/
theorem accessN_mem_keys {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList) {j : ℕ} (hj : j < n) (m : ℕ) :
    accessN X j ∈ (processTree init X m).toKeyList := by
  rw [processTree_toKeyList, accessN_lt X hj]
  exact hmem ⟨j, hj⟩

/-- A present key lies on its own search path. -/
theorem self_mem_searchPath {q : ℕ} {t : BinaryTree} (hbst : IsBST t)
    (hmem : q ∈ t.toKeyList) : q ∈ searchPath q t := by
  obtain ⟨A, B, hAB⟩ := splay_root_of_mem q t hbst hmem
  exact (splay_root_spec t.num_nodes t (Nat.le_refl _) q hbst A B q hAB).1

/-- Length of the in-range access path. -/
theorem pathN_length {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (hsize : init.num_nodes = n) {i : ℕ} (hi : i < n) :
    (pathN init X i).length = costN init X i + 1 := by
  have hcost : costN init X i
      = (processTree init X i).search_path_len (X ⟨i, hi⟩) - 1 := by
    unfold costN; rw [dif_pos hi]
  obtain ⟨l, k, r, hnode⟩ :=
    processTree_ne_empty init X hsize (lt_of_le_of_lt (Nat.zero_le i) hi) i
  have hpos : 0 < (processTree init X i).search_path_len (X ⟨i, hi⟩) := by
    rw [hnode]
    exact node_search_path_len_pos l k r _
  have hsplen : (processTree init X i).search_path_len (X ⟨i, hi⟩)
      = (searchPath (X ⟨i, hi⟩) (processTree init X i)).length :=
    search_path_len_eq _ _
  have hpath : pathN init X i = searchPath (X ⟨i, hi⟩) (processTree init X i) := by
    rw [pathN_lt init X hi, accessN_lt X hi]
  rw [hpath, ← hsplen, hcost]
  omega

/-- First-own-after at `i+1` for the dive's own side yields the adjacent
consecutive-pair at `i`. -/
theorem FOA_succ_to_COA {n : ℕ} (X : Fin n → ℕ) {i j : ℕ}
    (h : FirstOwnAfter X (i+1) (sideF X i) j) :
    ConsecOwnAfter X i (sideF X i) i j := by
  obtain ⟨hij, hjn, hbj, hno⟩ := h
  exact ⟨le_rfl, by omega, hjn, rfl, hbj, fun m him hmj => hno m (by omega) hmj⟩

/-- Consecutive pairs at `i+1` are consecutive pairs at `i`. -/
theorem COA_succ_weaken {n : ℕ} (X : Fin n → ℕ) {b : Bool} {i j k : ℕ}
    (h : ConsecOwnAfter X (i+1) b j k) : ConsecOwnAfter X i b j k := by
  obtain ⟨hij, hjk, hkn, hbj, hbk, hno⟩ := h
  exact ⟨by omega, hjk, hkn, hbj, hbk, hno⟩

/-- ℕ-level same-side monotonicity from the avoidance pattern: a `false`-side
(future-min) access is below every later access. -/
theorem accessN_le_of_sideF_false {n : ℕ} (X : Fin n → ℕ)
    (h213 : X avoids ![2, 1, 3]) (h231 : X avoids ![2, 3, 1])
    {i j : ℕ} (hi : i < n) (hj : j < n) (hij : i < j)
    (hb : sideF X i = false) : accessN X i ≤ accessN X j := by
  rw [accessN_lt X hi, accessN_lt X hj]
  exact sideF_false_le X h213 h231 ⟨i, hi⟩ hb ⟨j, hj⟩ hij

/-- ℕ-level: a `true`-side (future-max) access is above every later access. -/
theorem accessN_ge_of_sideF_true {n : ℕ} (X : Fin n → ℕ)
    {i j : ℕ} (hi : i < n) (hj : j < n) (hij : i < j)
    (hb : sideF X i = true) : accessN X j ≤ accessN X i := by
  rw [accessN_lt X hi, accessN_lt X hj]
  exact sideF_true_le X ⟨i, hi⟩ hb ⟨j, hj⟩ hij

/-- A zero-amount pooled ghost step: claims gain the debris and are pruned;
the pool gains the flat `2`. -/
theorem ghostStepP_zero (kap : ℕ) (T P : List ℕ) (c f x : ℕ) (isMin : Bool)
    (g : GhostState) (h0 : 2 * c - min (2 * c) (2 * kap * (1 + f)) = 0) :
    ghostStepP kap T P c f x isMin g
      = ⟨pruneClaims isMin x (g.claims ++ ghostDebris P c x isMin),
          g.pool + 2⟩ := by
  show (⟨pruneClaims isMin x
        ((consumeGreedy (2 * c - min (2 * c) (2 * kap * (1 + f))) g.claims
            (claimMet T P)).2 ++ ghostDebris P c x isMin),
      g.pool - (consumeGreedy (2 * c - min (2 * c) (2 * kap * (1 + f))) g.claims
            (claimMet T P)).1 + 2⟩ : GhostState) = _
  rw [h0, consumeGreedy_zero, consumeGreedy_zero_fst, Nat.sub_zero]

/-- The pooled ghost state after a zero-drain step. -/
theorem ghostAtP_succ_zero {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ) (i : ℕ)
    (h0 : amountN init X i = 0) :
    ghostAtP 6 init X (i+1)
      = ⟨pruneClaims (!(sideF X i)) (accessN X i)
            ((ghostAtP 6 init X i).claims
              ++ ghostDebris (pathN init X i) (costN init X i) (accessN X i)
                  (!(sideF X i))),
          (ghostAtP 6 init X i).pool + 2⟩ := by
  rw [ghostAtP_succ]
  exact ghostStepP_zero 6 _ _ _ _ _ _ _ h0

/-- New-path key dichotomy, right side: searching `v > q` from the root `q`
meets only `q` and live (`> q`) keys. -/
theorem mem_searchPath_root_right {q v : ℕ} {A B : BinaryTree}
    (hbst : IsBST (BinaryTree.node A q B)) (hqv : q < v) :
    ∀ z ∈ searchPath v (BinaryTree.node A q B), z = q ∨ q < z := by
  intro z hz
  rcases isBST_node_iff.mp hbst with ⟨_, hFr, _, _⟩
  rw [searchPath_node_gt hqv] at hz
  rcases List.mem_cons.mp hz with rfl | hz'
  · exact Or.inl rfl
  · exact Or.inr (mem_searchPath_forall hFr hz')

/-- New-path key dichotomy, left side. -/
theorem mem_searchPath_root_left {q v : ℕ} {A B : BinaryTree}
    (hbst : IsBST (BinaryTree.node A q B)) (hvq : v < q) :
    ∀ z ∈ searchPath v (BinaryTree.node A q B), z = q ∨ z < q := by
  intro z hz
  rcases isBST_node_iff.mp hbst with ⟨hFl, _, _, _⟩
  rw [searchPath_node_lt hvq] at hz
  rcases List.mem_cons.mp hz with rfl | hz'
  · exact Or.inl rfl
  · exact Or.inr (mem_searchPath_forall (p := fun w => w < q) hFl hz')


/-! ## Batch 4: the same-side C2S reproduction at zero drain (tree-level core) -/

/-- A positive touched count exhibits a touched member. -/
theorem touchedCount_pos_witness {T c : List ℕ} (h : 0 < touchedCount T c) :
    ∃ z ∈ c, z ∈ T := by
  unfold touchedCount at h
  cases hf : c.filter (fun x => decide (x ∈ T)) with
  | nil => rw [hf] at h; simp at h
  | cons a l =>
      have ha : a ∈ c.filter (fun x => decide (x ∈ T)) := by
        rw [hf]; exact List.mem_cons_self
      have := List.mem_filter.mp ha
      exact ⟨a, this.1, by simpa using this.2⟩

/-- **New-path head bounds.**  After splaying a present key `q`, the search
path of any `v ≠ q` (on the live side for `isMin`) decomposes as an on-path
head `p'` followed by the old diverge suffix, with the head short (halving)
and entirely made of live keys. -/
theorem splay_newpath_bounds (isMin : Bool) (t : BinaryTree) (q v : ℕ) (c : ℕ)
    (hbst : IsBST t) (hqmem : q ∈ t.toKeyList) (hvq : v ≠ q)
    (hside : (isMin = true → q < v) ∧ (isMin = false → v < q))
    (hPlen : (searchPath q t).length = c + 1) :
    ∃ p', searchPath v (splay t q) = p' ++ divergeSuffix v q t
      ∧ (∀ z ∈ p', z ∈ searchPath q t)
      ∧ 2 * p'.length ≤ c + 6
      ∧ p'.length ≤ (debrisKeys (searchPath q t) q isMin).length
      ∧ (∀ z ∈ searchPath v (splay t q),
          z ∈ searchPath q t → z ∈ debrisKeys (searchPath q t) q isMin) := by
  obtain ⟨A, B, hAB⟩ := splay_root_of_mem q t hbst hqmem
  have hbst' : IsBST (splay t q) := splay_isBST t q hbst
  obtain ⟨p', hdecomp, hp'sub⟩ := searchPath_splay_decomp q v t hbst
  obtain ⟨sh, hshdecomp, hshsub⟩ := searchPath_eq_shared_append_suffix q v t
  -- halving bound
  have hkd := keyDepth_splay_le_shared q v t hbst
  have hlen' : keyDepth v (splay t q)
      = p'.length + (divergeSuffix v q t).length := by
    rw [← sp_len, hdecomp, List.length_append]
  have hlenv : keyDepth v t = sh.length + (divergeSuffix v q t).length := by
    rw [← sp_len, hshdecomp, List.length_append]
  have hshnodup : sh.Nodup := by
    have hnd : (searchPath v t).Nodup := searchPath_nodup v t hbst
    rw [hshdecomp] at hnd
    exact (List.nodup_append.mp hnd).1
  have hshlen : sh.length ≤ c + 1 := by
    have := nodup_length_le_of_subset hshnodup hshsub
    omega
  have hp'len1 : 2 * p'.length ≤ c + 6 := by omega
  -- live dichotomy on the new path
  have hnewlive : ∀ z ∈ searchPath v (splay t q),
      z ∈ searchPath q t → z ∈ debrisKeys (searchPath q t) q isMin := by
    intro z hz hzP
    have hdico : z = q ∨ ((isMin = true → q < z) ∧ (isMin = false → z < q)) := by
      rw [hAB] at hz hbst'
      cases hMin : isMin
      · have hvq' : v < q := hside.2 hMin
        rcases mem_searchPath_root_left hbst' hvq' z hz with h | h
        · exact Or.inl h
        · exact Or.inr ⟨fun hcon => Bool.noConfusion hcon, fun _ => h⟩
      · have hqv : q < v := hside.1 hMin
        rcases mem_searchPath_root_right hbst' hqv z hz with h | h
        · exact Or.inl h
        · exact Or.inr ⟨fun _ => h, fun hcon => Bool.noConfusion hcon⟩
    rcases hdico with rfl | ⟨h1, h2⟩
    · exact accessKey_mem_debrisKeys hzP isMin
    · cases hMin : isMin
      · exact mem_debrisKeys_false.mpr ⟨hzP, le_of_lt (h2 hMin)⟩
      · exact mem_debrisKeys_true.mpr ⟨hzP, le_of_lt (h1 hMin)⟩
  -- p'-length live bound
  have hp'nodup : p'.Nodup := by
    have hnd : (searchPath v (splay t q)).Nodup := searchPath_nodup v _ hbst'
    rw [hdecomp] at hnd
    exact (List.nodup_append.mp hnd).1
  have hp'len2 : p'.length ≤ (debrisKeys (searchPath q t) q isMin).length := by
    refine nodup_length_le_of_subset hp'nodup ?_
    intro z hz
    refine hnewlive z ?_ (hp'sub z hz)
    rw [hdecomp]
    exact List.mem_append_left _ hz
  exact ⟨p', hdecomp, hp'sub, hp'len1, hp'len2, hnewlive⟩


/-- **Tree-level core of the own-side C2 chain (right chirality, `q < v`).**
After splaying a present key `q`, the `v`-path's doubled touched count is
covered by: the surviving suffix-met claims, the debris claim, the pool flat
`+2`, and the `+14` constant.  `S` is the pre-step suffix-met budget; the
pre-clause `hpre` is (C3)@i at the adjacent pair. -/
theorem C2own_core (isMin : Bool) (t : BinaryTree) (q v : ℕ) (T : List ℕ)
    (g : GhostState) (c : ℕ)
    (hbst : IsBST t) (hqmem : q ∈ t.toKeyList) (hvq : v ≠ q)
    (hside : (isMin = true → q < v) ∧ (isMin = false → v < q))
    (hPlen : (searchPath q t).length = c + 1)
    (hpre : 2 * touchedCount T (divergeSuffix v q t)
      ≤ claimsListTotal (g.claims.filter (claimMet T (divergeSuffix v q t)))
        + g.pool + 8) :
    2 * touchedCount (T ++ searchPath q t) (searchPath v (splay t q))
      ≤ claimsListTotal ((pruneClaims isMin q
            (g.claims ++ ghostDebris (searchPath q t) c q isMin)).filter
          (claimMet (T ++ searchPath q t) (searchPath v (splay t q))))
        + (g.pool + 2) + 14 := by
  -- structure of the splayed tree and the new path
  obtain ⟨A, B, hAB⟩ := splay_root_of_mem q t hbst hqmem
  have hbst' : IsBST (splay t q) := splay_isBST t q hbst
  have hqP : q ∈ searchPath q t := self_mem_searchPath hbst hqmem
  obtain ⟨p', hdecomp, hp'sub⟩ := searchPath_splay_decomp q v t hbst
  obtain ⟨sh, hshdecomp, hshsub⟩ := searchPath_eq_shared_append_suffix q v t
  -- suffix facts
  have hdsdisj : ∀ z ∈ divergeSuffix v q t, z ∉ searchPath q t :=
    divergeSuffix_disjoint t hbst
  have hdsLive : ∀ z ∈ divergeSuffix v q t,
      (isMin = true → q ≤ z) ∧ (isMin = false → z ≤ q) := by
    intro z hz
    constructor
    · intro hMin
      have hqv : q < v := hside.1 hMin
      exact le_of_lt (mem_divergeSuffix_gt (le_of_lt hqv) t hbst z hz)
    · intro hMax
      have hvq' : v < q := hside.2 hMax
      exact le_of_lt (mem_divergeSuffix_lt (le_of_lt hvq') t hbst z hz)
  -- count split
  have htc_split : touchedCount (T ++ searchPath q t) (searchPath v (splay t q))
      = touchedCount (T ++ searchPath q t) p'
        + touchedCount T (divergeSuffix v q t) := by
    rw [hdecomp, touchedCount_append,
      touchedCount_append_T_of_disjoint hdsdisj]
  -- p'-length bound (a): the halving route
  have hkd := keyDepth_splay_le_shared q v t hbst
  have hlen' : keyDepth v (splay t q) = p'.length + (divergeSuffix v q t).length := by
    rw [← sp_len, hdecomp, List.length_append]
  have hlenv : keyDepth v t = sh.length + (divergeSuffix v q t).length := by
    rw [← sp_len, hshdecomp, List.length_append]
  have hshnodup : sh.Nodup := by
    have hnd : (searchPath v t).Nodup := searchPath_nodup v t hbst
    rw [hshdecomp] at hnd
    exact (List.nodup_append.mp hnd).1
  have hshlen : sh.length ≤ c + 1 := by
    have := nodup_length_le_of_subset hshnodup hshsub
    omega
  have hp'len1 : 2 * p'.length ≤ c + 6 := by omega
  -- p'-length bound (b): every p'-key is live
  have hnewdico : ∀ z ∈ searchPath v (splay t q),
      z = q ∨ ((isMin = true → q < z) ∧ (isMin = false → z < q)) := by
    intro z hz
    rw [hAB] at hz hbst'
    cases hMin : isMin
    · have hvq' : v < q := hside.2 hMin
      rcases mem_searchPath_root_left hbst' hvq' z hz with h | h
      · exact Or.inl h
      · exact Or.inr ⟨fun hcon => Bool.noConfusion hcon, fun _ => h⟩
    · have hqv : q < v := hside.1 hMin
      rcases mem_searchPath_root_right hbst' hqv z hz with h | h
      · exact Or.inl h
      · exact Or.inr ⟨fun _ => h, fun hcon => Bool.noConfusion hcon⟩
  have hp'live : ∀ z ∈ p', z ∈ debrisKeys (searchPath q t) q isMin := by
    intro z hz
    have hzP : z ∈ searchPath q t := hp'sub z hz
    have hznew : z ∈ searchPath v (splay t q) := by
      rw [hdecomp]
      exact List.mem_append_left _ hz
    rcases hnewdico z hznew with rfl | ⟨h1, h2⟩
    · exact accessKey_mem_debrisKeys hzP isMin
    · cases hMin : isMin
      · exact mem_debrisKeys_false.mpr ⟨hzP, le_of_lt (h2 hMin)⟩
      · exact mem_debrisKeys_true.mpr ⟨hzP, le_of_lt (h1 hMin)⟩
  have hp'nodup : p'.Nodup := by
    have hnd : (searchPath v (splay t q)).Nodup := searchPath_nodup v _ hbst'
    rw [hdecomp] at hnd
    exact (List.nodup_append.mp hnd).1
  have hp'len2 : p'.length ≤ (debrisKeys (searchPath q t) q isMin).length :=
    nodup_length_le_of_subset hp'nodup hp'live
  -- count bound for the head
  have hp'count : touchedCount (T ++ searchPath q t) p' ≤ p'.length :=
    touchedCount_le_length _ _
  -- met split
  have hmet_split : claimsListTotal ((pruneClaims isMin q
        (g.claims ++ ghostDebris (searchPath q t) c q isMin)).filter
      (claimMet (T ++ searchPath q t) (searchPath v (splay t q))))
      = claimsListTotal ((pruneClaims isMin q g.claims).filter
          (claimMet (T ++ searchPath q t) (searchPath v (splay t q))))
        + claimsListTotal ((pruneClaims isMin q
              (ghostDebris (searchPath q t) c q isMin)).filter
            (claimMet (T ++ searchPath q t) (searchPath v (splay t q)))) := by
    rw [pruneClaims_append, List.filter_append, claimsListTotal_append]
  -- survival of the suffix-met budget
  have hsurv := metSum_survives_prune isMin q T (searchPath q t)
    (divergeSuffix v q t) (searchPath v (splay t q)) g.claims
    (by
      intro z hz
      rw [hdecomp]
      exact List.mem_append_right _ hz)
    hdsLive
  -- the debris by cases
  by_cases hL : 2 ≤ (debrisKeys (searchPath q t) q isMin).length
  · -- debris present and met
    have hqnew : q ∈ searchPath v (splay t q) := by
      rw [hAB]
      exact root_mem_searchPath v q A B
    have hdebris : claimsListTotal ((pruneClaims isMin q
          (ghostDebris (searchPath q t) c q isMin)).filter
        (claimMet (T ++ searchPath q t) (searchPath v (splay t q)))) = c :=
      debris_met_total isMin (searchPath q t) c q
        (T ++ searchPath q t) (searchPath v (splay t q))
        hqP hqnew (List.mem_append_right _ hqP) hL
    omega
  · -- no debris: |p'| ≤ 1 suffices
    have hp'le1 : p'.length ≤ 1 := by omega
    omega


/-- **C2S reproduction, own side, zero drain** (process level): the
first own-side access after the dive is covered via the decomposition,
(C3)@i at the adjacent pair, the debris claim, and met-survival. -/
theorem C2_zero_step {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (hsize : init.num_nodes = n) (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (h213 : X avoids ![2, 1, 3]) (h231 : X avoids ![2, 3, 1])
    (i : ℕ) (hi : i < n) (h0 : amountN init X i = 0)
    (j : ℕ) (hij : i < j) (hjn : j < n)
    (hpre : 2 * touchedCount (touchedList init X i)
          (divergeSuffix (accessN X j) (accessN X i) (processTree init X i))
        ≤ claimsListTotal ((ghostAtP 6 init X i).claims.filter
            (claimMet (touchedList init X i)
              (divergeSuffix (accessN X j) (accessN X i)
                (processTree init X i))))
          + (ghostAtP 6 init X i).pool + 8) :
    2 * tcOf init X (accessN X j) (i+1)
      ≤ metSumP 6 init X (i+1) (accessN X j)
        + (ghostAtP 6 init X (i+1)).pool + 14 := by
  have hbstT : IsBST (processTree init X i) := processTree_isBST init X hbst i
  have hqmem : accessN X i ∈ (processTree init X i).toKeyList :=
    accessN_mem_keys init X hmem hi i
  have ht' : processTree init X (i+1)
      = splay (processTree init X i) (accessN X i) :=
    processTree_succ_nat init X hi
  have hT' : touchedList init X (i+1)
      = touchedList init X i ++ pathN init X i := touchedList_succ init X i
  have hP : pathN init X i
      = searchPath (accessN X i) (processTree init X i) := pathN_lt init X hi
  have hg' := ghostAtP_succ_zero init X i h0
  have hpool' : (ghostAtP 6 init X (i+1)).pool
      = (ghostAtP 6 init X i).pool + 2 := by rw [hg']
  have htc : tcOf init X (accessN X j) (i+1)
      = touchedCount
          (touchedList init X i
            ++ searchPath (accessN X i) (processTree init X i))
          (searchPath (accessN X j)
            (splay (processTree init X i) (accessN X i))) := by
    unfold tcOf
    rw [hT', hP, ht']
  have hmet : metSumP 6 init X (i+1) (accessN X j)
      = claimsListTotal ((pruneClaims (!(sideF X i)) (accessN X i)
            ((ghostAtP 6 init X i).claims
              ++ ghostDebris (searchPath (accessN X i) (processTree init X i))
                  (costN init X i) (accessN X i) (!(sideF X i)))).filter
          (claimMet
            (touchedList init X i
              ++ searchPath (accessN X i) (processTree init X i))
            (searchPath (accessN X j)
              (splay (processTree init X i) (accessN X i))))) := by
    unfold metSumP metSumOnP
    rw [hg', hT', hP, ht']
  by_cases hvq : accessN X j = accessN X i
  · -- repeat access: the new path is the bare root
    obtain ⟨A, B, hAB⟩ := splay_root_of_mem _ _ hbstT hqmem
    have hpath1 : searchPath (accessN X j)
        (splay (processTree init X i) (accessN X i)) = [accessN X i] := by
      rw [hAB, hvq]
      exact searchPath_node_self rfl A B
    have h1 : tcOf init X (accessN X j) (i+1) ≤ 1 := by
      rw [htc, hpath1]
      have := touchedCount_le_length
        (touchedList init X i
          ++ searchPath (accessN X i) (processTree init X i))
        [accessN X i]
      simpa using this
    omega
  · -- strict case: the tree-level core
    have hsides : ((!(sideF X i)) = true → accessN X i < accessN X j)
        ∧ ((!(sideF X i)) = false → accessN X j < accessN X i) := by
      constructor
      · intro hMin
        have hbf : sideF X i = false := by simpa using hMin
        have := accessN_le_of_sideF_false X h213 h231 hi hjn hij hbf
        omega
      · intro hMax
        have hbt : sideF X i = true := by simpa using hMax
        have := accessN_ge_of_sideF_true X hi hjn hij hbt
        omega
    have hPlen : (searchPath (accessN X i) (processTree init X i)).length
        = costN init X i + 1 := by
      have := pathN_length init X hsize hi
      rw [hP] at this
      exact this
    have hcore := C2own_core (!(sideF X i)) (processTree init X i)
      (accessN X i) (accessN X j) (touchedList init X i)
      (ghostAtP 6 init X i) (costN init X i)
      hbstT hqmem hvq hsides hPlen hpre
    rw [htc, hmet, hpool']
    exact hcore


/-- **C3 reproduction, own side, zero drain, non-repeat pairs** (process
level): same-side future pairs survive the dive via the found-lemma (at most
one on-path head), dive-disjointness, and met-survival through the prune. -/
theorem C3own_zero_step {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (hsize : init.num_nodes = n) (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (h213 : X avoids ![2, 1, 3]) (h231 : X avoids ![2, 3, 1])
    (i : ℕ) (hi : i < n) (h0 : amountN init X i = 0)
    (hC3 : ∀ (b : Bool) (j k : ℕ), ConsecOwnAfter X i b j k →
      2 * tcSuffixOf init X (accessN X k) (accessN X j) i
        ≤ metSumOnP 6 init X i
            (divergeSuffix (accessN X k) (accessN X j) (processTree init X i))
          + (ghostAtP 6 init X i).pool + 8)
    (j k : ℕ) (hCOA1 : ConsecOwnAfter X (i+1) (sideF X i) j k)
    (hrep : accessN X j ≠ accessN X i) :
    2 * tcSuffixOf init X (accessN X k) (accessN X j) (i+1)
      ≤ metSumOnP 6 init X (i+1)
          (divergeSuffix (accessN X k) (accessN X j) (processTree init X (i+1)))
        + (ghostAtP 6 init X (i+1)).pool + 8 := by
  have hbstT : IsBST (processTree init X i) := processTree_isBST init X hbst i
  have hqmem : accessN X i ∈ (processTree init X i).toKeyList :=
    accessN_mem_keys init X hmem hi i
  have hCOA0 : ConsecOwnAfter X i (sideF X i) j k := COA_succ_weaken X hCOA1
  obtain ⟨hij1, hjk, hkn, hbj, hbk, hbet⟩ := hCOA1
  have hij : i < j := by omega
  have hjn : j < n := by omega
  have ht' : processTree init X (i+1)
      = splay (processTree init X i) (accessN X i) :=
    processTree_succ_nat init X hi
  have hT' : touchedList init X (i+1)
      = touchedList init X i ++ pathN init X i := touchedList_succ init X i
  have hP : pathN init X i
      = searchPath (accessN X i) (processTree init X i) := pathN_lt init X hi
  have hg' := ghostAtP_succ_zero init X i h0
  have hpool' : (ghostAtP 6 init X (i+1)).pool
      = (ghostAtP 6 init X i).pool + 2 := by rw [hg']
  -- the pre-clause at the SAME pair
  have hpre := hC3 (sideF X i) j k hCOA0
  -- degenerate pair
  by_cases hvv : accessN X k = accessN X j
  · have hnil : divergeSuffix (accessN X k) (accessN X j)
        (processTree init X (i+1)) = [] := by
      rw [hvv]
      exact divergeSuffix_self_q _ _
    have htc0 : tcSuffixOf init X (accessN X k) (accessN X j) (i+1) = 0 := by
      show touchedCount _ _ = 0
      rw [hnil]
      rfl
    rw [htc0]
    omega
  · -- the structural step: at most one on-path head, tail = the old suffix
    have hstep : divergeSuffix (accessN X k) (accessN X j)
          (splay (processTree init X i) (accessN X i))
        = divergeSuffix (accessN X k) (accessN X j) (processTree init X i)
      ∨ ∃ x ∈ searchPath (accessN X i) (processTree init X i),
          divergeSuffix (accessN X k) (accessN X j)
            (splay (processTree init X i) (accessN X i))
          = x :: divergeSuffix (accessN X k) (accessN X j)
              (processTree init X i) := by
      cases hsf : sideF X i
      · -- min side: q < vj ≤ vk
        have hqj : accessN X i ≤ accessN X j :=
          accessN_le_of_sideF_false X h213 h231 hi hjn hij hsf
        have hqj' : accessN X i < accessN X j :=
          lt_of_le_of_ne hqj (fun h => hrep h.symm)
        have hjk' : accessN X j ≤ accessN X k := by
          rw [hsf] at hbj
          exact accessN_le_of_sideF_false X h213 h231 hjn hkn hjk hbj
        exact divergeSuffix_splay_found (accessN X i) (accessN X j)
          (accessN X k) (processTree init X i) hbstT hqmem hqj' hjk'
      · -- max side: vk ≤ vj < q
        have hqj : accessN X j ≤ accessN X i :=
          accessN_ge_of_sideF_true X hi hjn hij hsf
        have hqj' : accessN X j < accessN X i := lt_of_le_of_ne hqj hrep
        have hjk' : accessN X k ≤ accessN X j := by
          rw [hsf] at hbj
          exact accessN_ge_of_sideF_true X hjn hkn hjk hbj
        exact divergeSuffix_splay_found_mirror (accessN X i) (accessN X j)
          (accessN X k) (processTree init X i) hbstT hqmem hqj' hjk'
    -- dive-disjointness of the OLD suffix from the dive path
    have hdsdisj : ∀ z ∈ divergeSuffix (accessN X k) (accessN X j)
          (processTree init X i),
        z ∉ searchPath (accessN X i) (processTree init X i) := by
      cases hsf : sideF X i
      · have hqj : accessN X i ≤ accessN X j :=
          accessN_le_of_sideF_false X h213 h231 hi hjn hij hsf
        have hjk' : accessN X j ≤ accessN X k := by
          rw [hsf] at hbj
          exact accessN_le_of_sideF_false X h213 h231 hjn hkn hjk hbj
        exact divergeSuffix_disjoint_dive (processTree init X i) hbstT
          (accessN X i) (accessN X j) (accessN X k) hqj hjk'
      · have hqj : accessN X j ≤ accessN X i :=
          accessN_ge_of_sideF_true X hi hjn hij hsf
        have hjk' : accessN X k ≤ accessN X j := by
          rw [hsf] at hbj
          exact accessN_ge_of_sideF_true X hjn hkn hjk hbj
        exact divergeSuffix_disjoint_dive_mirror (processTree init X i) hbstT
          (accessN X i) (accessN X j) (accessN X k) hqj hjk'
    -- live-side bound for the old-suffix keys
    have hdsLive : ∀ z ∈ divergeSuffix (accessN X k) (accessN X j)
          (processTree init X i),
        ((!(sideF X i)) = true → accessN X i ≤ z)
          ∧ ((!(sideF X i)) = false → z ≤ accessN X i) := by
      intro z hz
      constructor
      · intro hMin
        have hsf : sideF X i = false := by simpa using hMin
        have hqj : accessN X i ≤ accessN X j :=
          accessN_le_of_sideF_false X h213 h231 hi hjn hij hsf
        have hjk' : accessN X j ≤ accessN X k := by
          have hbj' : sideF X j = false := by rw [hbj, hsf]
          exact accessN_le_of_sideF_false X h213 h231 hjn hkn hjk hbj'
        have := mem_divergeSuffix_gt hjk' (processTree init X i) hbstT z hz
        omega
      · intro hMax
        have hsf : sideF X i = true := by simpa using hMax
        have hqj : accessN X j ≤ accessN X i :=
          accessN_ge_of_sideF_true X hi hjn hij hsf
        have hjk' : accessN X k ≤ accessN X j := by
          have hbj' : sideF X j = true := by rw [hbj, hsf]
          exact accessN_ge_of_sideF_true X hjn hkn hjk hbj'
        have := mem_divergeSuffix_lt hjk' (processTree init X i) hbstT z hz
        omega
    -- met-survival into the new suffix
    have hsub : ∀ z ∈ divergeSuffix (accessN X k) (accessN X j)
          (processTree init X i),
        z ∈ divergeSuffix (accessN X k) (accessN X j)
          (processTree init X (i+1)) := by
      intro z hz
      rw [ht']
      rcases hstep with heq | ⟨x, _, hcons⟩
      · rw [heq]; exact hz
      · rw [hcons]; exact List.mem_cons_of_mem _ hz
    have hsurv := metSum_survives_prune (!(sideF X i)) (accessN X i)
      (touchedList init X i) (searchPath (accessN X i) (processTree init X i))
      (divergeSuffix (accessN X k) (accessN X j) (processTree init X i))
      (divergeSuffix (accessN X k) (accessN X j) (processTree init X (i+1)))
      (ghostAtP 6 init X i).claims hsub hdsLive
    -- count chain
    have htcnew : tcSuffixOf init X (accessN X k) (accessN X j) (i+1)
        ≤ tcSuffixOf init X (accessN X k) (accessN X j) i + 1 := by
      show touchedCount (touchedList init X (i+1))
          (divergeSuffix (accessN X k) (accessN X j) (processTree init X (i+1)))
        ≤ touchedCount (touchedList init X i)
          (divergeSuffix (accessN X k) (accessN X j) (processTree init X i)) + 1
      rw [hT', hP, ht']
      rcases hstep with heq | ⟨x, _, hcons⟩
      · rw [heq, touchedCount_append_T_of_disjoint hdsdisj]
        omega
      · rw [hcons]
        have h1 := touchedCount_cons_le
          (touchedList init X i
            ++ searchPath (accessN X i) (processTree init X i)) x
          (divergeSuffix (accessN X k) (accessN X j) (processTree init X i))
        rw [touchedCount_append_T_of_disjoint hdsdisj] at h1
        exact h1
    -- the met sum at i+1 dominates the survived budget
    have hmetge : claimsListTotal ((ghostAtP 6 init X i).claims.filter
          (claimMet (touchedList init X i)
            (divergeSuffix (accessN X k) (accessN X j) (processTree init X i))))
        ≤ metSumOnP 6 init X (i+1)
            (divergeSuffix (accessN X k) (accessN X j)
              (processTree init X (i+1))) := by
      unfold metSumOnP
      rw [hg', hT', hP]
      rw [pruneClaims_append, List.filter_append, claimsListTotal_append]
      have := hsurv
      omega
    -- assemble
    have hpre' : 2 * tcSuffixOf init X (accessN X k) (accessN X j) i
        ≤ claimsListTotal ((ghostAtP 6 init X i).claims.filter
            (claimMet (touchedList init X i)
              (divergeSuffix (accessN X k) (accessN X j)
                (processTree init X i))))
          + (ghostAtP 6 init X i).pool + 8 := hpre
    rw [hpool']
    omega


/-- The very first access never draws (everything on its path is fresh). -/
theorem amountN_zero {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (hbst : IsBST init) : amountN init X 0 = 0 := by
  unfold amountN
  by_cases h0 : 0 < n
  · have hc : costN init X 0
        = (processTree init X 0).search_path_len (X ⟨0, h0⟩) - 1 := by
      unfold costN; rw [dif_pos h0]
    have hf : freshN init X 0
        = ((searchPath (X ⟨0, h0⟩) (processTree init X 0)).toFinset
            \ touchedUpTo (processTree init X) X 0).card := by
      unfold freshN; rw [dif_pos h0]
    have htouch0 : touchedUpTo (processTree init X) X 0 = ∅ := rfl
    have hnodup : (searchPath (X ⟨0, h0⟩) (processTree init X 0)).Nodup :=
      searchPath_nodup _ _ (processTree_isBST init X hbst 0)
    have hcard : ((searchPath (X ⟨0, h0⟩) (processTree init X 0)).toFinset
          \ touchedUpTo (processTree init X) X 0).card
        = (searchPath (X ⟨0, h0⟩) (processTree init X 0)).length := by
      rw [htouch0, Finset.sdiff_empty, List.toFinset_card_of_nodup hnodup]
    have hlen : (processTree init X 0).search_path_len (X ⟨0, h0⟩)
        = (searchPath (X ⟨0, h0⟩) (processTree init X 0)).length :=
      search_path_len_eq _ _
    rw [hc, hf, hcard, hlen]
    omega
  · have hc : costN init X 0 = 0 := by
      unfold costN; rw [dif_neg h0]
    rw [hc]
    omega


/-- **C3 at the very first step, ALL pairs (both sides, any base).**  The new
suffix sits inside the target's new path; its old-suffix part is untouched
(nothing was touched before step 0), and any touched node on it is a live
on-path key witnessing the debris claim. -/
theorem C3_step_index0 {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (hsize : init.num_nodes = n) (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (h213 : X avoids ![2, 1, 3]) (h231 : X avoids ![2, 3, 1])
    (h0n : 0 < n) (base : ℕ) (k : ℕ) (h0k : 0 < k) (hkn : k < n) :
    2 * touchedCount (touchedList init X 1)
        (divergeSuffix (accessN X k) base (processTree init X 1))
      ≤ metSumOnP 6 init X 1
          (divergeSuffix (accessN X k) base (processTree init X 1))
        + (ghostAtP 6 init X 1).pool + 8 := by
  have hbstT : IsBST (processTree init X 0) := processTree_isBST init X hbst 0
  have hqmem : accessN X 0 ∈ (processTree init X 0).toKeyList :=
    accessN_mem_keys init X hmem h0n 0
  have ht' : processTree init X 1
      = splay (processTree init X 0) (accessN X 0) :=
    processTree_succ_nat init X h0n
  have hT' : touchedList init X 1
      = ([] : List ℕ) ++ pathN init X 0 := touchedList_succ init X 0
  have hP : pathN init X 0
      = searchPath (accessN X 0) (processTree init X 0) := pathN_lt init X h0n
  have hg' := ghostAtP_succ_zero init X 0 (amountN_zero init X hbst)
  have hpool' : (ghostAtP 6 init X 1).pool = 2 := by rw [hg']; rfl
  have hPlen : (searchPath (accessN X 0) (processTree init X 0)).length
      = costN init X 0 + 1 := by
    have := pathN_length init X hsize h0n
    rw [hP] at this
    exact this
  -- the new suffix is a suffix of the target's new path
  obtain ⟨sh', hsh'⟩ := searchPath_eq_shared_append_suffix base (accessN X k)
    (processTree init X 1)
  rw [hpool']
  by_cases htc0 : touchedCount (touchedList init X 1)
      (divergeSuffix (accessN X k) base (processTree init X 1)) = 0
  · rw [htc0]
    omega
  · -- a touched witness on the new suffix
    obtain ⟨z, hzds, hzT⟩ :=
      touchedCount_pos_witness (Nat.pos_of_ne_zero htc0)
    have hzP : z ∈ searchPath (accessN X 0) (processTree init X 0) := by
      rw [hT', hP] at hzT
      simpa using hzT
    by_cases hvq : accessN X k = accessN X 0
    · -- target is the accessed key: its new path is the bare root
      obtain ⟨A, B, hAB⟩ := splay_root_of_mem _ _ hbstT hqmem
      have hpath1 : searchPath (accessN X k) (processTree init X 1)
          = [accessN X 0] := by
        rw [ht', hAB, hvq]
        exact searchPath_node_self rfl A B
      have hcount : touchedCount (touchedList init X 1)
          (divergeSuffix (accessN X k) base (processTree init X 1)) ≤ 1 := by
        have h1 : touchedCount (touchedList init X 1)
            (divergeSuffix (accessN X k) base (processTree init X 1))
            ≤ touchedCount (touchedList init X 1)
                (searchPath (accessN X k) (processTree init X 1)) := by
          rw [hsh'.1, touchedCount_append]
          omega
        have h2 := touchedCount_le_length (touchedList init X 1) [accessN X 0]
        rw [hpath1] at h1
        simp only [List.length_cons, List.length_nil] at h2
        omega
      omega
    · -- main case: head bounds for the target's new path
      have hside : ((!(sideF X 0)) = true → accessN X 0 < accessN X k)
          ∧ ((!(sideF X 0)) = false → accessN X k < accessN X 0) := by
        constructor
        · intro hMin
          have hbf : sideF X 0 = false := by simpa using hMin
          have := accessN_le_of_sideF_false X h213 h231 h0n hkn h0k hbf
          omega
        · intro hMax
          have hbt : sideF X 0 = true := by simpa using hMax
          have := accessN_ge_of_sideF_true X h0n hkn h0k hbt
          omega
      obtain ⟨p', hdecomp, hp'sub, hp'len1, hp'len2, hnewlive⟩ :=
        splay_newpath_bounds (!(sideF X 0)) (processTree init X 0)
          (accessN X 0) (accessN X k) (costN init X 0)
          hbstT hqmem hvq hside hPlen
      -- the suffix count is bounded by the head length
      have hdsdisj : ∀ w ∈ divergeSuffix (accessN X k) (accessN X 0)
            (processTree init X 0),
          w ∉ searchPath (accessN X 0) (processTree init X 0) :=
        divergeSuffix_disjoint (processTree init X 0) hbstT
      have hcount : touchedCount (touchedList init X 1)
          (divergeSuffix (accessN X k) base (processTree init X 1))
          ≤ p'.length := by
        have h1 : touchedCount (touchedList init X 1)
            (divergeSuffix (accessN X k) base (processTree init X 1))
            ≤ touchedCount (touchedList init X 1)
                (searchPath (accessN X k) (processTree init X 1)) := by
          rw [hsh'.1, touchedCount_append]
          omega
        have h2 : touchedCount (touchedList init X 1)
            (searchPath (accessN X k) (processTree init X 1))
            = touchedCount (touchedList init X 1) p'
              + touchedCount ([] : List ℕ)
                  (divergeSuffix (accessN X k) (accessN X 0)
                    (processTree init X 0)) := by
          rw [ht', hdecomp, touchedCount_append, hT', hP,
            touchedCount_append_T_of_disjoint hdsdisj]
        have h3 : touchedCount ([] : List ℕ)
            (divergeSuffix (accessN X k) (accessN X 0)
              (processTree init X 0)) = 0 := touchedCount_nil_T _
        have h4 := touchedCount_le_length (touchedList init X 1) p'
        omega
      -- the witness is on the target's new path and on the old path: live
      have hznew : z ∈ searchPath (accessN X k) (processTree init X 1) := by
        rw [hsh'.1]
        exact List.mem_append_right _ hzds
      have hzlive : z ∈ debrisKeys
          (searchPath (accessN X 0) (processTree init X 0)) (accessN X 0)
          (!(sideF X 0)) := by
        refine hnewlive z ?_ hzP
        rw [← ht']
        exact hznew
      -- debris present (the witness and the accessed key are distinct live keys
      -- unless they coincide; in the latter case fall back to counting)
      by_cases hL : 2 ≤ (debrisKeys
          (searchPath (accessN X 0) (processTree init X 0)) (accessN X 0)
          (!(sideF X 0))).length
      · -- met sum contains the debris claim, worth c
        have hmet : metSumOnP 6 init X 1
            (divergeSuffix (accessN X k) base (processTree init X 1))
            = costN init X 0 := by
          show claimsListTotal ((ghostAtP 6 init X 1).claims.filter
            (claimMet (touchedList init X 1)
              (divergeSuffix (accessN X k) base (processTree init X 1))))
            = costN init X 0
          rw [hg']
          show claimsListTotal ((pruneClaims (!(sideF X 0)) (accessN X 0)
              (((ghostAtP 6 init X 0).claims)
                ++ ghostDebris (pathN init X 0) (costN init X 0) (accessN X 0)
                    (!(sideF X 0)))).filter
            (claimMet (touchedList init X 1)
              (divergeSuffix (accessN X k) base (processTree init X 1))))
            = costN init X 0
          have hcl0 : (ghostAtP 6 init X 0).claims = [] := rfl
          rw [hcl0, List.nil_append, hP]
          exact debris_met_total_witness (!(sideF X 0))
            (searchPath (accessN X 0) (processTree init X 0))
            (costN init X 0) (accessN X 0) z
            (touchedList init X 1)
            (divergeSuffix (accessN X k) base (processTree init X 1))
            hzlive hzds hzT hL
        rw [hmet]
        omega
      · -- no debris: the head is at most one node
        have : p'.length ≤ 1 := by omega
        omega

/-! ## The step theorem, kernel-parameterized

The four named kernels isolate the open drain-overlap / cross-side-suffix
arithmetic; everything else (C1, and the no-drain own-side C2/C3 reproduction)
is proven outright. -/

/-- The strong-invariant step. -/
theorem hstepS {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (hsize : init.num_nodes = n) (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (h213 : X avoids ![2, 1, 3]) (h231 : X avoids ![2, 3, 1])
    (hkC2opp : ∀ i, i < n → 1 ≤ i → ∀ (b' : Bool) (j : ℕ), b' ≠ sideF X i →
      FirstOwnAfter X (i+1) b' j →
      2 * tcOf init X (accessN X j) (i+1)
        ≤ metSumP 6 init X (i+1) (accessN X j)
          + (ghostAtP 6 init X (i+1)).pool + 14)
    (hkC2own : ∀ i, i < n → 1 ≤ i → 0 < amountN init X i →
      ∀ j, FirstOwnAfter X (i+1) (sideF X i) j →
      2 * tcOf init X (accessN X j) (i+1)
        ≤ metSumP 6 init X (i+1) (accessN X j)
          + (ghostAtP 6 init X (i+1)).pool + 14)
    (hkC3cross : ∀ i, i < n → 1 ≤ i → ∀ (b' : Bool) (j k : ℕ), b' ≠ sideF X i →
      ConsecOwnAfter X (i+1) b' j k →
      2 * tcSuffixOf init X (accessN X k) (accessN X j) (i+1)
        ≤ metSumOnP 6 init X (i+1)
            (divergeSuffix (accessN X k) (accessN X j) (processTree init X (i+1)))
          + (ghostAtP 6 init X (i+1)).pool + 8)
    (hkC3own : ∀ i, i < n → 1 ≤ i → 0 < amountN init X i →
      ∀ (j k : ℕ), ConsecOwnAfter X (i+1) (sideF X i) j k →
      2 * tcSuffixOf init X (accessN X k) (accessN X j) (i+1)
        ≤ metSumOnP 6 init X (i+1)
            (divergeSuffix (accessN X k) (accessN X j) (processTree init X (i+1)))
          + (ghostAtP 6 init X (i+1)).pool + 8)
    (hkC3rep0 : ∀ i, i < n → 1 ≤ i → amountN init X i = 0 →
      ∀ (j k : ℕ), ConsecOwnAfter X (i+1) (sideF X i) j k →
      accessN X j = accessN X i →
      2 * tcSuffixOf init X (accessN X k) (accessN X j) (i+1)
        ≤ metSumOnP 6 init X (i+1)
            (divergeSuffix (accessN X k) (accessN X j) (processTree init X (i+1)))
          + (ghostAtP 6 init X (i+1)).pool + 8) :
    ∀ i, i < n → INVS 6 init X i → INVS 6 init X (i+1) := by
  intro i hi hINV
  obtain ⟨hC1, hC2S, hC3⟩ := hINV
  refine ⟨?_, ?_, ?_⟩
  · -- (C1) via the cover from C2S at the access itself
    exact INVP_C1_succ_of_cover 6 init X i hC1
      (cover_of_C2S init X hsize hbst i hi hC2S)
  · -- (C2S) at i+1
    intro b' j hFOA
    have hjn : j < n := hFOA.2.1
    have hij : i < j := by have := hFOA.1; omega
    by_cases hi0 : i = 0
    · -- the very first step: zero drain and trivially-zero pre-clause
      subst hi0
      refine C2_zero_step init X hsize hbst hmem h213 h231 0 hi
        (amountN_zero init X hbst) j hij hjn ?_
      have ht0 : touchedCount (touchedList init X 0)
          (divergeSuffix (accessN X j) (accessN X 0) (processTree init X 0))
          = 0 := by
        rw [touchedList_zero, touchedCount_nil_T]
      rw [ht0]
      omega
    · by_cases hb' : b' = sideF X i
      · subst hb'
        rcases Nat.eq_zero_or_pos (amountN init X i) with h0 | hpos
        · exact C2_zero_step init X hsize hbst hmem h213 h231 i hi h0 j hij hjn
            (hC3 (sideF X i) i j (FOA_succ_to_COA X hFOA))
        · exact hkC2own i hi (by omega) hpos j hFOA
      · exact hkC2opp i hi (by omega) b' j hb' hFOA
  · -- (C3) at i+1
    intro b' j k hCOA
    by_cases hi0 : i = 0
    · -- the very first step: every pair clause closes structurally
      subst hi0
      have h0k : 0 < k := by have := hCOA.2.1; have := hCOA.1; omega
      exact C3_step_index0 init X hsize hbst hmem h213 h231 hi
        (accessN X j) k h0k hCOA.2.2.1
    · by_cases hb' : b' = sideF X i
      · subst hb'
        rcases Nat.eq_zero_or_pos (amountN init X i) with h0 | hpos
        · by_cases hrep : accessN X j = accessN X i
          · exact hkC3rep0 i hi (by omega) h0 j k hCOA hrep
          · exact C3own_zero_step init X hsize hbst hmem h213 h231 i hi h0 hC3
              j k hCOA hrep
        · exact hkC3own i hi (by omega) hpos j k hCOA
      · exact hkC3cross i hi (by omega) b' j k hb' hCOA

/-! ## The outer wiring: `hstepP` -/

/-- **`hstepP` from the kernels.**  The `INVP i` hypothesis is not needed: the
ghost state is a function of `(init, X, i)`, so the strong invariant is
re-derived from `0` by the inner induction and projected. -/
theorem hstepP_of_kernels {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (hsize : init.num_nodes = n) (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (h213 : X avoids ![2, 1, 3]) (h231 : X avoids ![2, 3, 1])
    (hkC2opp : ∀ i, i < n → 1 ≤ i → ∀ (b' : Bool) (j : ℕ), b' ≠ sideF X i →
      FirstOwnAfter X (i+1) b' j →
      2 * tcOf init X (accessN X j) (i+1)
        ≤ metSumP 6 init X (i+1) (accessN X j)
          + (ghostAtP 6 init X (i+1)).pool + 14)
    (hkC2own : ∀ i, i < n → 1 ≤ i → 0 < amountN init X i →
      ∀ j, FirstOwnAfter X (i+1) (sideF X i) j →
      2 * tcOf init X (accessN X j) (i+1)
        ≤ metSumP 6 init X (i+1) (accessN X j)
          + (ghostAtP 6 init X (i+1)).pool + 14)
    (hkC3cross : ∀ i, i < n → 1 ≤ i → ∀ (b' : Bool) (j k : ℕ), b' ≠ sideF X i →
      ConsecOwnAfter X (i+1) b' j k →
      2 * tcSuffixOf init X (accessN X k) (accessN X j) (i+1)
        ≤ metSumOnP 6 init X (i+1)
            (divergeSuffix (accessN X k) (accessN X j) (processTree init X (i+1)))
          + (ghostAtP 6 init X (i+1)).pool + 8)
    (hkC3own : ∀ i, i < n → 1 ≤ i → 0 < amountN init X i →
      ∀ (j k : ℕ), ConsecOwnAfter X (i+1) (sideF X i) j k →
      2 * tcSuffixOf init X (accessN X k) (accessN X j) (i+1)
        ≤ metSumOnP 6 init X (i+1)
            (divergeSuffix (accessN X k) (accessN X j) (processTree init X (i+1)))
          + (ghostAtP 6 init X (i+1)).pool + 8)
    (hkC3rep0 : ∀ i, i < n → 1 ≤ i → amountN init X i = 0 →
      ∀ (j k : ℕ), ConsecOwnAfter X (i+1) (sideF X i) j k →
      accessN X j = accessN X i →
      2 * tcSuffixOf init X (accessN X k) (accessN X j) (i+1)
        ≤ metSumOnP 6 init X (i+1)
            (divergeSuffix (accessN X k) (accessN X j) (processTree init X (i+1)))
          + (ghostAtP 6 init X (i+1)).pool + 8) :
    ∀ i, i < n → INVP 6 init X i → INVP 6 init X (i+1) := by
  intro i hi _
  have hstep := hstepS init X hsize hbst hmem h213 h231
    hkC2opp hkC2own hkC3cross hkC3own hkC3rep0
  have hS : ∀ m, m ≤ i + 1 → INVS 6 init X m := by
    intro m
    induction m with
    | zero => intro _; exact INVS_zero 6 init X
    | succ m ih =>
        intro hm
        have hmn : m < n := by omega
        exact hstep m hmn (ih (by omega))
  exact INVS_imp_INVP 6 init X (i+1) (hS (i+1) le_rfl)


/-! ## THE TARGET: `hstepP`

The sole remaining obligation of the pooled-ledger programme, here proven
modulo five explicitly-named kernel hypotheses (`hkC2opp`, `hkC2own`,
`hkC3cross`, `hkC3own`, `hkC3rep0`) that isolate the open drain-overlap and
cross-side-suffix arithmetic of the empirically-validated design
(/tmp/pooled_ledger.py, zero violations).  Everything else — the C1
conservation clause, the own-side C2/C3 reproduction at zero drain, the
strengthened-invariant wiring, and the base case — is proven outright. -/

theorem hstepP {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (hsize : init.num_nodes = n) (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (h213 : X avoids ![2, 1, 3]) (h231 : X avoids ![2, 3, 1])
    (hkC2opp : ∀ i, i < n → 1 ≤ i → ∀ (b' : Bool) (j : ℕ), b' ≠ sideF X i →
      FirstOwnAfter X (i+1) b' j →
      2 * tcOf init X (accessN X j) (i+1)
        ≤ metSumP 6 init X (i+1) (accessN X j)
          + (ghostAtP 6 init X (i+1)).pool + 14)
    (hkC2own : ∀ i, i < n → 1 ≤ i → 0 < amountN init X i →
      ∀ j, FirstOwnAfter X (i+1) (sideF X i) j →
      2 * tcOf init X (accessN X j) (i+1)
        ≤ metSumP 6 init X (i+1) (accessN X j)
          + (ghostAtP 6 init X (i+1)).pool + 14)
    (hkC3cross : ∀ i, i < n → 1 ≤ i → ∀ (b' : Bool) (j k : ℕ), b' ≠ sideF X i →
      ConsecOwnAfter X (i+1) b' j k →
      2 * tcSuffixOf init X (accessN X k) (accessN X j) (i+1)
        ≤ metSumOnP 6 init X (i+1)
            (divergeSuffix (accessN X k) (accessN X j) (processTree init X (i+1)))
          + (ghostAtP 6 init X (i+1)).pool + 8)
    (hkC3own : ∀ i, i < n → 1 ≤ i → 0 < amountN init X i →
      ∀ (j k : ℕ), ConsecOwnAfter X (i+1) (sideF X i) j k →
      2 * tcSuffixOf init X (accessN X k) (accessN X j) (i+1)
        ≤ metSumOnP 6 init X (i+1)
            (divergeSuffix (accessN X k) (accessN X j) (processTree init X (i+1)))
          + (ghostAtP 6 init X (i+1)).pool + 8)
    (hkC3rep0 : ∀ i, i < n → 1 ≤ i → amountN init X i = 0 →
      ∀ (j k : ℕ), ConsecOwnAfter X (i+1) (sideF X i) j k →
      accessN X j = accessN X i →
      2 * tcSuffixOf init X (accessN X k) (accessN X j) (i+1)
        ≤ metSumOnP 6 init X (i+1)
            (divergeSuffix (accessN X k) (accessN X j) (processTree init X (i+1)))
          + (ghostAtP 6 init X (i+1)).pool + 8) :
    ∀ i, i < n → INVP 6 init X i → INVP 6 init X (i+1) :=
  hstepP_of_kernels init X hsize hbst hmem h213 h231
    hkC2opp hkC2own hkC3cross hkC3own hkC3rep0

end Splay

#print axioms Splay.Splay.Splay.Splay.Splay.Splay.hstepP
