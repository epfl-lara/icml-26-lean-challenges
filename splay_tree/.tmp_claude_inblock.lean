/- PUBLICATION HEADER
  Splay Deque — STEP 1 of the in-block recursion (depth-projection identity)

  Public result: inblock_touched_eq_depth_projection — the in-block touched count of an
  access equals the search-path length in the restricted tree `restrict T lo hi`.
  Also: restrict (def, isBST, right-spine identity) and search-path/size bounds.
  Axioms: {propext, Classical.choice, Quot.sound}; no sorry.
-/

/-
DEPTH-PROJECTION STRUCTURAL LEMMA (STEP 1 of the inblock-recursion bypass).

A pure BST fact (no amortization):  the number of in-[lo,hi] nodes on the full
search path `searchPath x T` equals the search-path length in the BST-restriction
of `T` to the key interval [lo,hi].

We use the recursive BST-filter definition of `restrict`:

  restrict empty            lo hi = empty
  restrict (node l k r)     lo hi =
    if k < lo  then restrict r lo hi          -- whole left subtree is < lo, dropped
    else if hi < k then restrict l lo hi      -- whole right subtree is > hi, dropped
    else node (restrict l lo hi) k (restrict r lo hi)

The three restrict-recursion equations (`restrict_node_lt/_gt/_mem`) hold by
definition; the search-path equality is then a direct induction on the
`searchPath` recursion, using `lo ≤ x ≤ hi` to pick the surviving child.

Compiles on the precompiled `Challenges.ZBK` base.
-/
import Challenges.ZBK

set_option linter.dupNamespace false
set_option maxHeartbeats 1000000

namespace Splay

/-! ## §1 The recursive BST-restriction `restrict T lo hi`. -/

/-- `restrict T lo hi` is the BST induced from `T` by deleting every node whose
key is outside the interval `[lo,hi]` and splicing children.  The definition is
purely structural; BST-ness of `T` is only needed for `restrict_isBST`. -/
def restrict : BinaryTree → ℕ → ℕ → BinaryTree
  | .empty, _, _ => .empty
  | .node l k r, lo, hi =>
      if k < lo then restrict r lo hi
      else if hi < k then restrict l lo hi
      else .node (restrict l lo hi) k (restrict r lo hi)

@[simp] theorem restrict_empty (lo hi : ℕ) : restrict .empty lo hi = .empty := rfl

/-- Restriction recursion, low-cut branch: a node with `k < lo` is dropped and
its (entirely-`< lo`) left subtree disappears; we keep `restrict r lo hi`. -/
theorem restrict_node_lt {k : ℕ} (l r : BinaryTree) {lo hi : ℕ} (h : k < lo) :
    restrict (.node l k r) lo hi = restrict r lo hi := by
  simp only [restrict, if_pos h]

/-- Restriction recursion, high-cut branch: a node with `hi < k` is dropped and
its (entirely-`> hi`) right subtree disappears; we keep `restrict l lo hi`. -/
theorem restrict_node_gt {k : ℕ} (l r : BinaryTree) {lo hi : ℕ}
    (h1 : ¬ k < lo) (h2 : hi < k) :
    restrict (.node l k r) lo hi = restrict l lo hi := by
  simp only [restrict, if_neg h1, if_pos h2]

/-- Restriction recursion, kept branch: a node with `lo ≤ k ≤ hi` survives, both
children are restricted recursively. -/
theorem restrict_node_mem {k : ℕ} (l r : BinaryTree) {lo hi : ℕ}
    (h1 : ¬ k < lo) (h2 : ¬ hi < k) :
    restrict (.node l k r) lo hi = .node (restrict l lo hi) k (restrict r lo hi) := by
  simp only [restrict, if_neg h1, if_neg h2]

/-! ## §2 `restrict` preserves `ForallTree` and `IsBST`. -/

/-- Restriction preserves any `ForallTree` predicate (it only deletes nodes). -/
theorem restrict_forall (p : ℕ → Prop) :
    ∀ (T : BinaryTree) (lo hi : ℕ), ForallTree p T → ForallTree p (restrict T lo hi)
  | .empty, lo, hi, _ => by simpa using ForallTree.left
  | .node l k r, lo, hi, h => by
      obtain ⟨hl, hk, hr⟩ : ForallTree p l ∧ p k ∧ ForallTree p r := by
        cases h with | node _ _ _ hl hk hr => exact ⟨hl, hk, hr⟩
      by_cases hlt : k < lo
      · rw [restrict_node_lt l r hlt]; exact restrict_forall p r lo hi hr
      · by_cases hgt : hi < k
        · rw [restrict_node_gt l r hlt hgt]; exact restrict_forall p l lo hi hl
        · rw [restrict_node_mem l r hlt hgt]
          exact ForallTree.node _ _ _ (restrict_forall p l lo hi hl) hk
            (restrict_forall p r lo hi hr)

/-- Restriction preserves BST-ness. -/
theorem restrict_isBST :
    ∀ (T : BinaryTree) (lo hi : ℕ), IsBST T → IsBST (restrict T lo hi)
  | .empty, lo, hi, _ => by simpa using IsBST.left
  | .node l k r, lo, hi, h => by
      obtain ⟨hfl, hfr, hbl, hbr⟩ :
          ForallTree (fun j => j < k) l ∧ ForallTree (fun j => k < j) r ∧
            IsBST l ∧ IsBST r := by
        cases h with | node _ _ _ hfl hfr hbl hbr => exact ⟨hfl, hfr, hbl, hbr⟩
      by_cases hlt : k < lo
      · rw [restrict_node_lt l r hlt]; exact restrict_isBST r lo hi hbr
      · by_cases hgt : hi < k
        · rw [restrict_node_gt l r hlt hgt]; exact restrict_isBST l lo hi hbl
        · rw [restrict_node_mem l r hlt hgt]
          exact IsBST.node _ _ _
            (restrict_forall _ l lo hi hfl) (restrict_forall _ r lo hi hfr)
            (restrict_isBST l lo hi hbl) (restrict_isBST r lo hi hbr)

/-! ## §3 The depth-projection equality.

The number of in-`[lo,hi]` nodes on `searchPath x T` is the `countP` of the
interval-membership predicate over the search path. -/

/-- Interval-membership Bool predicate on a key. -/
def inBlock (lo hi : ℕ) (k : ℕ) : Bool := decide (lo ≤ k ∧ k ≤ hi)

/-- The in-block count on `x`'s full search path equals the search-path length in
the restricted tree.  Pure BST/search structural identity. -/
theorem inblock_touched_eq_depth_projection :
    ∀ (T : BinaryTree) (x lo hi : ℕ), lo ≤ x → x ≤ hi →
      ((searchPath x T).countP (inBlock lo hi)) = (searchPath x (restrict T lo hi)).length
  | .empty, x, lo, hi, _, _ => by
      rw [searchPath_empty, restrict_empty, searchPath_empty]; rfl
  | .node l k r, x, lo, hi, hlox, hxhi => by
      -- Compare key `k` with the query `x` to direct the full search path.
      rcases lt_trichotomy x k with hxk | hxk | hxk
      · -- x < k : full path goes left, head is k.
        rw [searchPath_node_lt hxk l r]
        by_cases hlt : k < lo
        · -- impossible: lo ≤ x < k < lo
          exact (by omega : False).elim
        · by_cases hgt : hi < k
          · -- k > hi : node dropped, right subtree (all > hi) gone, keep restrict l.
            rw [restrict_node_gt l r hlt hgt]
            -- k is NOT in block (hi < k), so head contributes 0 to countP.
            have hkblock : ¬ inBlock lo hi k = true := by
              simp only [inBlock, decide_eq_true_eq, not_and, not_le]
              intro _; exact hgt
            rw [List.countP_cons_of_neg hkblock]
            exact inblock_touched_eq_depth_projection l x lo hi hlox hxhi
          · -- lo ≤ k ≤ hi : node kept, recurse left.
            rw [restrict_node_mem l r hlt hgt, searchPath_node_lt hxk]
            have hkblock : inBlock lo hi k = true := by
              simp only [inBlock, decide_eq_true_eq]
              exact ⟨Nat.le_of_not_lt hlt, Nat.le_of_not_lt hgt⟩
            rw [List.countP_cons_of_pos hkblock, List.length_cons]
            rw [inblock_touched_eq_depth_projection l x lo hi hlox hxhi]
      · -- x = k : path stops at [k]; k is in block (lo ≤ x = k ≤ hi).
        rw [searchPath_node_self hxk l r]
        have hlt : ¬ k < lo := by omega
        have hgt : ¬ hi < k := by omega
        rw [restrict_node_mem l r hlt hgt, searchPath_node_self hxk]
        have hkblock : inBlock lo hi k = true := by
          simp only [inBlock, decide_eq_true_eq]
          exact ⟨Nat.le_of_not_lt hlt, Nat.le_of_not_lt hgt⟩
        rw [List.countP_cons_of_pos hkblock]
        simp
      · -- k < x : full path goes right, head is k.
        rw [searchPath_node_gt hxk l r]
        by_cases hlt : k < lo
        · -- k < lo : node dropped, left subtree (all < lo) gone, keep restrict r.
          rw [restrict_node_lt l r hlt]
          have hkblock : ¬ inBlock lo hi k = true := by
            simp only [inBlock, decide_eq_true_eq, not_and, not_le]
            intro hk; exact absurd hk (not_le.mpr hlt)
          rw [List.countP_cons_of_neg hkblock]
          exact inblock_touched_eq_depth_projection r x lo hi hlox hxhi
        · by_cases hgt : hi < k
          · -- impossible: x ≤ hi < k < x
            exact (by omega : False).elim
          · -- lo ≤ k ≤ hi : node kept, recurse right.
            rw [restrict_node_mem l r hlt hgt, searchPath_node_gt hxk]
            have hkblock : inBlock lo hi k = true := by
              simp only [inBlock, decide_eq_true_eq]
              exact ⟨Nat.le_of_not_lt hlt, Nat.le_of_not_lt hgt⟩
            rw [List.countP_cons_of_pos hkblock, List.length_cons]
            rw [inblock_touched_eq_depth_projection r x lo hi hlox hxhi]

/-! ## §4 Right-spine restriction identity.

A right spine on keys `[a, a+1, …]` of length `n` (each node has empty left
child, the right child being the rest of the spine).  Restriction of a right
spine to `[lo,hi]` is again a right spine: it keeps exactly the prefix-of-keys
that lie in the interval, in order.  We make this precise for the canonical
increasing right spine `rightSpineTree base n` (keys `base, base+1, …, base+n-1`),
showing its restriction to `[lo,hi]` equals the right spine on the sub-interval. -/

/-- Canonical increasing right spine: keys `base, base+1, …, base+n-1`, each node
having an empty left child. -/
def rightSpineTree (base : ℕ) : ℕ → BinaryTree
  | 0 => .empty
  | n + 1 => .node .empty base (rightSpineTree (base + 1) n)

@[simp] theorem rightSpineTree_zero (base : ℕ) : rightSpineTree base 0 = .empty := rfl

theorem rightSpineTree_succ (base n : ℕ) :
    rightSpineTree base (n + 1) = .node .empty base (rightSpineTree (base + 1) n) := rfl

/-- Predicate weakening for `ForallTree`. -/
theorem forallTree_imp {p q : ℕ → Prop} (hpq : ∀ k, p k → q k) :
    ∀ {T : BinaryTree}, ForallTree p T → ForallTree q T
  | .empty, _ => ForallTree.left
  | .node l k r, h => by
      obtain ⟨hl, hk, hr⟩ : ForallTree p l ∧ p k ∧ ForallTree p r := by
        cases h with | node _ _ _ hl hk hr => exact ⟨hl, hk, hr⟩
      exact ForallTree.node _ _ _ (forallTree_imp hpq hl) (hpq k hk) (forallTree_imp hpq hr)

/-- A right spine starting at `base` has every key `≥ base`. -/
theorem rightSpineTree_forall_ge (base : ℕ) :
    ∀ n, ForallTree (fun k => base ≤ k) (rightSpineTree base n)
  | 0 => by simpa using ForallTree.left
  | n + 1 => by
      rw [rightSpineTree_succ]
      refine ForallTree.node _ _ _ ForallTree.left (le_refl base) ?_
      exact forallTree_imp (fun k hk => by omega) (rightSpineTree_forall_ge (base + 1) n)

/-- The canonical right spine is a BST. -/
theorem rightSpineTree_isBST (base : ℕ) : ∀ n, IsBST (rightSpineTree base n)
  | 0 => by simpa using IsBST.left
  | n + 1 => by
      rw [rightSpineTree_succ]
      refine IsBST.node _ _ _ ForallTree.left ?_ IsBST.left (rightSpineTree_isBST (base + 1) n)
      exact forallTree_imp (fun k hk => by omega) (rightSpineTree_forall_ge (base + 1) n)

/-- Restriction of a right spine by cutting **above** at `hi` only (low cut
inactive, `lo ≤ base`): the spine of length `n` from `base` restricted to
`[lo,hi]` is the right spine from `base` of length `min n (hi + 1 - base)` —
i.e. it keeps exactly the in-interval prefix.  Stated in the clean low-open form
`lo ≤ base`, which is the case used by the inblock recursion (the interval's low
end never cuts a spine that already starts at `base ≥ lo`). -/
theorem restrict_rightSpineTree_le (lo hi : ℕ) :
    ∀ (base n : ℕ), lo ≤ base →
      restrict (rightSpineTree base n) lo hi
        = rightSpineTree base (min n (hi + 1 - base))
  | _, 0, _ => by simp
  | base, n + 1, hlb => by
      rw [rightSpineTree_succ]
      by_cases hk : hi < base
      · -- base already above hi: node and everything below it is dropped.
        rw [restrict_node_gt _ _ (by omega) hk]
        -- left child is empty, so restrict of empty is empty = spine of length 0.
        have : min (n + 1) (hi + 1 - base) = 0 := by omega
        rw [this]; simp
      · -- base ≤ hi (and lo ≤ base): node kept, recurse into the right child.
        rw [restrict_node_mem _ _ (by omega) (by omega)]
        rw [restrict_rightSpineTree_le lo hi (base + 1) n (by omega)]
        -- empty left child restricts to empty.
        have hmin : min (n + 1) (hi + 1 - base) = min n (hi + 1 - (base + 1)) + 1 := by omega
        rw [hmin, rightSpineTree_succ, restrict_empty]

/-! ## §5 STEP-2 structural bounds on `restrict` (the scaffolding any STEP-2
amortization needs).

STEP-1 (`inblock_touched_eq_depth_projection`) reduced the per-access in-block
touched count to a search-path length in the static restriction
`restrict T lo hi`.  STEP-2 must SUM these over a period's accesses and bound the
total by a per-block sub-cost `g b`.  This section establishes the self-contained
size facts those arguments rely on: a search path is no longer than the tree
(`searchPath_length_le_num_nodes`), the restriction keeps EXACTLY the in-interval
keys (`restrict_num_nodes_eq_filter`, hence `restrict_search_le_blockKeys`), a
BST key list is duplicate-free (`toKeyList_nodup`), and the in-interval keys of a
nodup list number at most the interval width (`filter_inBlock_length_le`).  Their
composition gives the per-access "free" bound `≤ B` (the block size). -/

/-- §5 **(1a) A search path is no longer than the tree.**  Pure structural fact:
each step descends one level, consuming a node. -/
theorem searchPath_length_le_num_nodes (x : ℕ) :
    ∀ (T : BinaryTree), (searchPath x T).length ≤ T.num_nodes
  | .empty => by rw [searchPath_empty]; simp [BinaryTree.num_nodes]
  | .node l k r => by
      rcases lt_trichotomy x k with hxk | hxk | hxk
      · rw [searchPath_node_lt hxk l r, List.length_cons]
        have := searchPath_length_le_num_nodes x l
        simp only [BinaryTree.num_nodes]; omega
      · rw [searchPath_node_self hxk l r]
        simp only [BinaryTree.num_nodes, List.length_singleton]; omega
      · rw [searchPath_node_gt hxk l r, List.length_cons]
        have := searchPath_length_le_num_nodes x r
        simp only [BinaryTree.num_nodes]; omega

/-- §5 **(1b) `restrict` keeps exactly the in-interval keys.**  Its node count
equals the number of `T`-keys in `[lo,hi]`.  BST-ness is essential: a dropped
out-of-range node carries with it an entire subtree, and BST order guarantees
that subtree is itself entirely out of range. -/
theorem restrict_num_nodes_eq_filter :
    ∀ (T : BinaryTree) (lo hi : ℕ), IsBST T →
      (restrict T lo hi).num_nodes = (T.toKeyList.filter (inBlock lo hi)).length
  | .empty, lo, hi, _ => by
      rw [restrict_empty]; simp [BinaryTree.num_nodes, BinaryTree.toKeyList]
  | .node l k r, lo, hi, h => by
      obtain ⟨hfl, hfr, hbl, hbr⟩ :
          ForallTree (fun j => j < k) l ∧ ForallTree (fun j => k < j) r ∧
            IsBST l ∧ IsBST r := by
        cases h with | node _ _ _ hfl hfr hbl hbr => exact ⟨hfl, hfr, hbl, hbr⟩
      have htk : (BinaryTree.node l k r).toKeyList
          = l.toKeyList ++ [k] ++ r.toKeyList := rfl
      by_cases hlt : k < lo
      · rw [restrict_node_lt l r hlt, restrict_num_nodes_eq_filter r lo hi hbr]
        rw [htk, List.filter_append, List.filter_append]
        have hlnil : l.toKeyList.filter (inBlock lo hi) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro a ha
          have : a < k := forallTree_mem hfl a ha
          simp only [inBlock, decide_eq_true_eq, not_and, not_le]; intro _; omega
        have hknil : ([k] : List ℕ).filter (inBlock lo hi) = [] := by
          have hneg : ¬ inBlock lo hi k = true := by
            simp only [inBlock, decide_eq_true_eq]; intro ⟨h1, _⟩; omega
          rw [List.filter_cons_of_neg hneg]; rfl
        rw [hlnil, hknil]; simp
      · by_cases hgt : hi < k
        · rw [restrict_node_gt l r hlt hgt, restrict_num_nodes_eq_filter l lo hi hbl]
          rw [htk, List.filter_append, List.filter_append]
          have hknil : ([k] : List ℕ).filter (inBlock lo hi) = [] := by
            have hneg : ¬ inBlock lo hi k = true := by
              simp only [inBlock, decide_eq_true_eq]; intro ⟨_, h2⟩; omega
            rw [List.filter_cons_of_neg hneg]; rfl
          have hrnil : r.toKeyList.filter (inBlock lo hi) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro a ha
            have : k < a := forallTree_mem hfr a ha
            simp only [inBlock, decide_eq_true_eq, not_and, not_le]; intro h1; omega
          rw [hknil, hrnil]; simp
        · rw [restrict_node_mem l r hlt hgt]
          simp only [BinaryTree.num_nodes]
          rw [restrict_num_nodes_eq_filter l lo hi hbl,
              restrict_num_nodes_eq_filter r lo hi hbr]
          rw [htk, List.filter_append, List.filter_append]
          have hkpos : ([k] : List ℕ).filter (inBlock lo hi) = [k] := by
            have hpos : inBlock lo hi k = true := by
              simp only [inBlock, decide_eq_true_eq]
              exact ⟨Nat.le_of_not_lt hlt, Nat.le_of_not_lt hgt⟩
            rw [List.filter_cons_of_pos hpos]; rfl
          rw [hkpos]
          simp only [List.length_append, List.length_cons, List.length_nil]; omega

/-- §5 **(1c) Per-access search bound in the restriction.**  The projected path
length is at most the number of in-interval keys.  (Combines 1a + 1b.) -/
theorem restrict_search_le_blockKeys (T : BinaryTree) (x lo hi : ℕ) (hbst : IsBST T) :
    (searchPath x (restrict T lo hi)).length
      ≤ (T.toKeyList.filter (inBlock lo hi)).length := by
  calc (searchPath x (restrict T lo hi)).length
      ≤ (restrict T lo hi).num_nodes := searchPath_length_le_num_nodes x (restrict T lo hi)
    _ = (T.toKeyList.filter (inBlock lo hi)).length :=
        restrict_num_nodes_eq_filter T lo hi hbst

/-- §5 **(1d) A BST key list is duplicate-free.**  Left keys `< k <` right keys
keep the three pieces pairwise disjoint. -/
theorem toKeyList_nodup :
    ∀ (T : BinaryTree), IsBST T → T.toKeyList.Nodup
  | .empty, _ => by simp [BinaryTree.toKeyList]
  | .node l k r, h => by
      obtain ⟨hfl, hfr, hbl, hbr⟩ :
          ForallTree (fun j => j < k) l ∧ ForallTree (fun j => k < j) r ∧
            IsBST l ∧ IsBST r := by
        cases h with | node _ _ _ hfl hfr hbl hbr => exact ⟨hfl, hfr, hbl, hbr⟩
      have htk : (BinaryTree.node l k r).toKeyList
          = l.toKeyList ++ ([k] ++ r.toKeyList) := by
        simp [BinaryTree.toKeyList, List.append_assoc]
      rw [htk]
      have hndl : l.toKeyList.Nodup := toKeyList_nodup l hbl
      have hndr : r.toKeyList.Nodup := toKeyList_nodup r hbr
      have hlmem : ∀ a ∈ l.toKeyList, a < k := fun a ha => forallTree_mem hfl a ha
      have hrmem : ∀ a ∈ r.toKeyList, k < a := fun a ha => forallTree_mem hfr a ha
      rw [List.nodup_append]
      refine ⟨hndl, ?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨by simp, hndr, ?_⟩
        intro a ha b hb
        simp only [List.mem_singleton] at ha; subst ha
        have := hrmem b hb; omega
      · intro a ha b hb
        have h1 := hlmem a ha
        simp only [List.mem_append, List.mem_singleton] at hb
        rcases hb with hbk | hbr2
        · omega
        · have := hrmem b hbr2; omega

/-- §5 **(1e) The in-interval keys of a nodup list number at most the interval
width.**  Distinct integers in `[lo,hi]` inject into `Finset.Icc lo hi`. -/
theorem filter_inBlock_length_le (L : List ℕ) (lo hi : ℕ) (hnd : L.Nodup) :
    (L.filter (inBlock lo hi)).length ≤ hi + 1 - lo := by
  have hfnd : (L.filter (inBlock lo hi)).Nodup := hnd.filter _
  rw [← List.toFinset_card_of_nodup hfnd]
  have hsub : (L.filter (inBlock lo hi)).toFinset ⊆ Finset.Icc lo hi := by
    intro a ha
    rw [List.mem_toFinset, List.mem_filter] at ha
    obtain ⟨_, hb⟩ := ha
    simp only [inBlock, decide_eq_true_eq] at hb
    rw [Finset.mem_Icc]; exact hb
  calc (L.filter (inBlock lo hi)).toFinset.card
      ≤ (Finset.Icc lo hi).card := Finset.card_le_card hsub
    _ = hi + 1 - lo := Nat.card_Icc lo hi

/-- §5 **(1f) Right-spine node count.**  `rightSpineTree base n` has `n` nodes;
the base case of the recursion's leaf sub-instance. -/
theorem rightSpineTree_num_nodes (base : ℕ) :
    ∀ n, (rightSpineTree base n).num_nodes = n
  | 0 => by simp [rightSpineTree, BinaryTree.num_nodes]
  | n + 1 => by
      show (BinaryTree.node .empty base (rightSpineTree (base+1) n)).num_nodes = n + 1
      simp only [BinaryTree.num_nodes]
      rw [rightSpineTree_num_nodes (base+1) n]; omega

/-! ## §6 STEP-2: block intervals and the in-block projected path length.

We now build the STEP-2 object on the ZBK access machinery
(`accessN`, `processTree`).  Block `b` of size `B` owns the key interval
`[b·B, b·B+B-1]`.  Access `i` is assigned a frontier block by an (abstract)
`blk : ℕ → ℕ`; in the recursion wiring `blk i = frontierN X i / B`. -/

/-- Low endpoint of frontier block `b` for block size `B`. -/
def blockLo (B b : ℕ) : ℕ := b * B
/-- High endpoint of frontier block `b` (interval `[b·B, b·B+B-1]`). -/
def blockHi (B b : ℕ) : ℕ := b * B + (B - 1)

/-- A block of size `B ≥ 1` has interval width exactly `B`. -/
theorem blockHi_sub_blockLo (B b : ℕ) (hB : 1 ≤ B) :
    blockHi B b + 1 - blockLo B b = B := by
  unfold blockLo blockHi; omega

/-- §6 **The in-block projected path length of access `i`.**  By STEP-1 this
equals the number of access `i`'s in-block touched nodes; the search runs in the
static restriction of the current state to access `i`'s frontier-block interval. -/
def inBlockProj (B : ℕ) {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (blk : ℕ → ℕ) (i : ℕ) : ℕ :=
  (searchPath (accessN X i)
    (restrict (processTree init X i) (blockLo B (blk i)) (blockHi B (blk i)))).length

/-- §6 **(STEP-1 BRIDGE) `inBlockProj` IS the in-block touched count** (PROVEN).
When access `i`'s key lies in its own frontier block
(`blockLo ≤ accessN X i ≤ blockHi` — automatic for `blk i = accessN X i / B`),
the in-block projection equals the `inBlock`-count over access `i`'s FULL search
path.  Turn_main's `inBlockTp i` is the count over the TOUCHED PREFIX, a sublist
of that path, so `inBlockTp i ≤ inBlockProj i` — the inequality that feeds this
ZBK-side residual into `Blocking_inblock_recursion`. -/
theorem inBlockProj_eq_countP (B : ℕ) {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (blk : ℕ → ℕ) (i : ℕ)
    (hlo : blockLo B (blk i) ≤ accessN X i) (hhi : accessN X i ≤ blockHi B (blk i)) :
    inBlockProj B init X blk i
      = (searchPath (accessN X i) (processTree init X i)).countP
          (inBlock (blockLo B (blk i)) (blockHi B (blk i))) := by
  unfold inBlockProj
  exact (inblock_touched_eq_depth_projection (processTree init X i) (accessN X i)
    (blockLo B (blk i)) (blockHi B (blk i)) hlo hhi).symm

/-- §6 **(STEP-2a) PER-ACCESS BOUND ≤ B** (PROVEN).  The in-block projected path
length of any access is at most the block size `B`: `≤` the number of state keys
in the block interval, which (keys distinct, BST `toKeyList` nodup) is `≤` the
width `B`.  This is the unconditional "free" size bound — but it only yields
`Σ ≤ n·B`, far above the target `n·α`; the slack is exactly what the recursion
must reclaim. -/
theorem inBlockProj_le_B (B : ℕ) {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (blk : ℕ → ℕ) (i : ℕ) (hB : 1 ≤ B) (hbst : IsBST init) :
    inBlockProj B init X blk i ≤ B := by
  unfold inBlockProj
  have hptbst : IsBST (processTree init X i) := processTree_isBST init X hbst i
  calc (searchPath (accessN X i)
          (restrict (processTree init X i)
            (blockLo B (blk i)) (blockHi B (blk i)))).length
      ≤ ((processTree init X i).toKeyList.filter
          (inBlock (blockLo B (blk i)) (blockHi B (blk i)))).length :=
        restrict_search_le_blockKeys (processTree init X i) (accessN X i)
          (blockLo B (blk i)) (blockHi B (blk i)) hptbst
    _ ≤ blockHi B (blk i) + 1 - blockLo B (blk i) :=
        filter_inBlock_length_le _ _ _ (toKeyList_nodup _ hptbst)
    _ = B := blockHi_sub_blockLo B (blk i) hB

/-- §6 The set of frontier blocks the access sequence visits (matches turn_main
`blockIdxSet`): the `(· / B)`-image of the key range `0 … n-1`. -/
def blockIdxSet (B : ℕ) (n : ℕ) : Finset ℕ :=
  (Finset.range n).image (· / B)

/-- §6 **(STEP-2b) THE BLOCK PARTITION OF THE IN-BLOCK SUM** (PROVEN).  When the
block assignment maps the accessed range into a block set `S`, the total in-block
projected work splits, over blocks, into per-block fiber sums — the regrouping
the recurrence consumes. -/
theorem inBlockProjSum_split (B : ℕ) {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (blk : ℕ → ℕ) (S : Finset ℕ) (hS : ∀ i ∈ Finset.range n, blk i ∈ S) :
    (∑ i ∈ Finset.range n, inBlockProj B init X blk i)
      = ∑ b ∈ S, ∑ i ∈ (Finset.range n).filter (fun i => blk i = b),
          inBlockProj B init X blk i :=
  (Finset.sum_fiberwise_of_maps_to hS _).symm

/-! ## §7 STEP-2: the residual — the genuinely hard Pettie §5 sub-instance
correspondence, isolated as a sharp named `Prop`, plus the PROVEN reduction.

The recursion needs `Σ_i inBlockProj ≤ Σ_b g b` (the `Blocking_inblock_recursion`
shape, matched verbatim below).  The §6 block partition reduces this to a
PER-BLOCK inequality: each block's fiber sum is bounded by `g b`.  That per-block
inequality is the EMBEDDING — the in-block touched walk of the accesses whose
frontier lies in block `b` is a touched walk of the block-`b` sub-process (a
deque-class access sequence on `≤ B` keys), whose touched-sum is `g b`.

The probe verdict (and the campaign's WAVE-7/8 analysis) is that establishing
this embedding is NOT a mechanical potential argument: the projection sequence is
a DRIFTING BST, not a splay process; `splay` does not commute with `restrict`, and
the naive size/log potential gives only `n·B` (the per-block budget would have to
absorb the `~B·log B` minted across a block period).  This is the inverse-Ackermann
heart.  We isolate it sharply and PROVE the reduction from it. -/

/-- §7 **THE PER-BLOCK EMBEDDING RESIDUAL** (SHARP — the Pettie §5 core).  For
every frontier block `b`, the total in-block projected work of the accesses whose
frontier lies in block `b` is bounded by the per-block sub-cost `g b`.  This is
the recursive sub-instance correspondence: the genuine α-incidence content. -/
def InblockBlockEmbeds (B : ℕ) {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (blk : ℕ → ℕ) (g : ℕ → ℕ) : Prop :=
  ∀ b ∈ blockIdxSet B n,
    (∑ i ∈ (Finset.range n).filter (fun i => blk i = b),
      inBlockProj B init X blk i) ≤ g b

/-- §7 **THE STEP-2 TARGET**, in the exact `Blocking_inblock_recursion` shape
(`Σ over accesses ≤ Σ over blocks of g b`), stated over the ZBK access objects
via the STEP-1 in-block projection. -/
def Blocking_inblock_step2 (B : ℕ) {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (blk : ℕ → ℕ) (g : ℕ → ℕ) : Prop :=
  (∑ i ∈ Finset.range n, inBlockProj B init X blk i)
    ≤ ∑ b ∈ blockIdxSet B n, g b

/-- §7 **THE STEP-2 REDUCTION** (PROVEN).  Given the per-block embedding residual
and that the block assignment maps the accessed range into `blockIdxSet`, the
STEP-2 target holds.  Everything except `InblockBlockEmbeds` is mechanical: the
§6 block partition turns the access sum into a sum of fiber sums, and the
embedding dominates each fiber sum termwise.  This pins the ENTIRE STEP-2
difficulty onto the single sharp residual `InblockBlockEmbeds`. -/
theorem inblock_step2_of_embedding (B : ℕ) {n : ℕ} (init : BinaryTree)
    (X : Fin n → ℕ) (blk : ℕ → ℕ) (g : ℕ → ℕ)
    (hmaps : ∀ i ∈ Finset.range n, blk i ∈ blockIdxSet B n)
    (hemb : InblockBlockEmbeds B init X blk g) :
    Blocking_inblock_step2 B init X blk g := by
  unfold Blocking_inblock_step2
  rw [inBlockProjSum_split B init X blk (blockIdxSet B n) hmaps]
  exact Finset.sum_le_sum hemb

/-- §7 **The canonical block assignment maps into `blockIdxSet`** (PROVEN).  For a
frontier function `fr : ℕ → ℕ` with `fr i < n` (the deque normalization,
`fr = frontierN X`), `blk i = fr i / B` lands in `blockIdxSet B n` — discharging
the `hmaps` hypothesis of the reduction. -/
theorem blk_maps_to_blockIdxSet (B : ℕ) (n : ℕ) (fr : ℕ → ℕ)
    (hfr : ∀ i ∈ Finset.range n, fr i < n) :
    ∀ i ∈ Finset.range n, (fun i => fr i / B) i ∈ blockIdxSet B n := by
  intro i hi
  unfold blockIdxSet
  rw [Finset.mem_image]
  exact ⟨fr i, Finset.mem_range.mpr (hfr i hi), rfl⟩

/-! ## §8 STEP-2 part (3): the drifting-BST potential test and the EXACT failing
inequality.

We test whether a static potential closes the telescope.  The "free" facts hold:
every access' projected length is `≤ B` (§6), and the block partition is exact.
The naive AMORTIZED claim — that a single per-block budget `g b = c·α(B)·B`
dominates the fiber sum — is precisely `InblockBlockEmbeds` specialised to that
`g`, and is what FAILS for any constant/log potential (the drifting BST mints
`~B·log B` over a block period; probe-confirmed).  We record the size-potential
bound that DOES hold and isolate the gap: the residual content is reducing the
per-block budget from `Θ(B·|fiber b|)` (proven below) down to the sub-instance
touched-sum `Θ(α(B)·|fiber b|)` (the residual). -/

/-- §8 **The size-potential bound on a block fiber sum** (PROVEN, but WEAK).  Each
fiber sum is `≤ B · (#accesses with frontier in block b)` (every term `≤ B`).
Summed over blocks this is `≤ B·n` — the ceiling the recursion must beat. -/
theorem fiberSum_le_sizeBudget (B : ℕ) {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (blk : ℕ → ℕ) (b : ℕ) (hB : 1 ≤ B) (hbst : IsBST init) :
    (∑ i ∈ (Finset.range n).filter (fun i => blk i = b), inBlockProj B init X blk i)
      ≤ B * ((Finset.range n).filter (fun i => blk i = b)).card := by
  calc (∑ i ∈ (Finset.range n).filter (fun i => blk i = b), inBlockProj B init X blk i)
      ≤ ∑ _i ∈ (Finset.range n).filter (fun i => blk i = b), B :=
        Finset.sum_le_sum (fun i _ => inBlockProj_le_B B init X blk i hB hbst)
    _ = B * ((Finset.range n).filter (fun i => blk i = b)).card := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- §8 **The UNCONDITIONAL size-budget STEP-2 instance** (PROVEN).  Taking
`g b = B · |fiber b|`, the STEP-2 target holds with NO embedding hypothesis — the
honest unconditional fallback bounding the in-block sum by `B·n`.  This is the
proven analogue of the `classesSum_le_sq` quadratic fallback: the channel is
unconditionally `O(B·n)`, and the residual `InblockBlockEmbeds` (for an α-sized
`g`) is exactly the gap from `B·n` down to `α·n`. -/
theorem inblock_step2_sizeBudget (B : ℕ) {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (blk : ℕ → ℕ) (hB : 1 ≤ B) (hbst : IsBST init)
    (hmaps : ∀ i ∈ Finset.range n, blk i ∈ blockIdxSet B n) :
    Blocking_inblock_step2 B init X blk
      (fun b => B * ((Finset.range n).filter (fun i => blk i = b)).card) := by
  apply inblock_step2_of_embedding B init X blk _ hmaps
  intro b _
  exact fiberSum_le_sizeBudget B init X blk b hB hbst

/-! ## §9 Axiom audit. -/

#print axioms restrict_empty
#print axioms restrict_node_lt
#print axioms restrict_node_gt
#print axioms restrict_node_mem
#print axioms restrict_forall
#print axioms forallTree_imp
#print axioms restrict_isBST
#print axioms inblock_touched_eq_depth_projection
#print axioms rightSpineTree_forall_ge
#print axioms rightSpineTree_isBST
#print axioms restrict_rightSpineTree_le
-- STEP-2 additions:
#print axioms searchPath_length_le_num_nodes
#print axioms restrict_num_nodes_eq_filter
#print axioms restrict_search_le_blockKeys
#print axioms toKeyList_nodup
#print axioms filter_inBlock_length_le
#print axioms rightSpineTree_num_nodes
#print axioms blockHi_sub_blockLo
#print axioms inBlockProj_eq_countP
#print axioms inBlockProj_le_B
#print axioms inBlockProjSum_split
#print axioms inblock_step2_of_embedding
#print axioms blk_maps_to_blockIdxSet
#print axioms fiberSum_le_sizeBudget
#print axioms inblock_step2_sizeBudget

end Splay
