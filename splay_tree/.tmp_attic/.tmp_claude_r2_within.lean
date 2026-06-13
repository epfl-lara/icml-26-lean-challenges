import Challenges.Splay_Tree.Def_Containment
import Challenges.Splay_Tree.Def_Ackermann
import Challenges.Splay_Tree.Def_Splay

set_option maxHeartbeats 2000000

namespace Splay

/-!
# (R2-within) WITHIN-RUN MIXED-TOUCHED-SET DEEPENING

Sibling of the proven `touchedCount_mixed_splay_le` (root BETWEEN `q` and `v`).  Here the
previous access (= the root) and the current access `q` lie on the SAME side, with the
next opposite-side target `v` beyond both:

    rootKey t ≤ q ≤ v        (or the mirror  v ≤ q ≤ rootKey t).

## Empirical pinning (exhaustive `#eval` harness, /tmp/r2w_pin.lean)

Scanned: all 188 BSTs with keys ⊆ {0..4} × q,v ∈ {0..5} × all 64 unstructured T ⊆ {0..5};
all 731 BSTs with keys ⊆ {0..5} × q,v ∈ {0..6} × process-shaped T (unions of ≤ 2 search
paths); zig-zag combs and right spines with 8–24 nodes.  Max excess
`touchedCount T' newPath − touchedCount T oldPath`, `T' = T ++ searchPath q t`:

* (W1) `rootKey t ∈ T`, arbitrary T:        3 small, **12 on the 24-comb — GROWS ~n/2**.
* (W2) W1 + path-closure of T:              3 small, 12 on combs — grows.
* (W3) W1 + T-members of v's old path ≤ q:  3 small — fails.
* (W5) W1 + T ≤ v:                          3 small — fails.  (W2∧W3∧W5 likewise 3/12.)
* (W4) W1 + v ≥ all keys (calibration):     2 small (too strong for the process anyway).
* **(W6) SHARED-PREFIX-TOUCHED** — every node on BOTH `searchPath q t` and
  `searchPath v t` is in `T`:               max excess **1** within-run (tight), **0** on
  the big combs, **2** without any side condition (tight; the sibling's zig-zig witness).
  W6 with the root exempted degrades to 3.

So W1–W5 admit NO constant; W6 is the load-bearing hypothesis.  Note that in the sibling's
opposite-side geometry (q ≤ root ≤ v) the shared prefix is exactly `[rootKey t]`, so W6
degenerates to `rootKey t ∈ T` — the sibling's hypothesis.  W6 is the common generalization.

## Proof route (route (b), non-recursive on top of two ported backbone theorems)

`searchPath_splay_decomp`  : new path = p' ++ divergeSuffix v q t,   p' ⊆ searchPath q t,
`searchPath_eq_shared_append_suffix` : old path = sh ++ divergeSuffix v q t, sh ⊆ searchPath q t,
`divergeSuffix_disjoint`   : the suffix avoids `searchPath q t` (so it is T'/T-blind),
`keyDepth_splay_le_shared` : 2·|new path| ≤ |old path| + |divergeSuffix| + 5.

Counting: `T'` covers all of p' (p' ⊆ q-path), W6 covers all of sh, the suffix counts
identically under T and T', so

    excess = |p'| − |sh|,  and the halving lemma gives  2|p'| ≤ |sh| + 5.

`|sh| ≥ 1` (the root is shared) yields the GENERAL `+2`; within-run with `rootKey t < q`
and a nonempty inner subtree the first TWO nodes are shared (`|sh| ≥ 2`), and the
remaining degenerate shapes are splay-identities — yielding the sharper `+1`.

The two ~1000-line backbone aux theorems (`searchPath_splay_decomp_aux`,
`keyDepth_splay_le_shared_aux`) are ported verbatim from the proven development file.
-/

def touchedCount (T : List Nat) (c : List Nat) : Nat := (c.filter (fun x => x ∈ T)).length

def searchPath (q : Nat) : BinaryTree → List Nat
  | .empty => []
  | .node l k r =>
      if q = k then [k]
      else if q < k then k :: searchPath q l
      else k :: searchPath q r

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

/-! #####################################################################
## NEW MATERIAL: the within-run theorems
##################################################################### -/

/-- A `touchedCount` over a list wholly inside `T` is just its length. -/
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

/-- The proven sibling theorem (`touchedCount_mixed_splay_le`, root between `q` and `v`)
re-derived as a corollary of the general shared-prefix-touched theorem. -/
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

#print axioms touchedCount_within_run_splay_le
#print axioms touchedCount_within_run_splay_le_one
#print axioms touchedCount_sharedTouched_splay_le
#print axioms touchedCount_shared_decomp
#print axioms touchedCount_mixed_splay_le_of_shared

end Splay
