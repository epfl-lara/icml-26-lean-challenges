import Challenges.BinaryHeap_Dijkstra.Def_DijkstraComposite

open BinaryTree BinaryHeap Finset SimpleGraph

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedDecidableInType false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

namespace BinaryTree

lemma containsb_eq_true_iff_contains {α : Type u} [DecidableEq α] :
    ∀ (t : BinaryTree α) (x : α), containsb t x = true ↔ contains t x := by
  intro t x
  induction t with
  | leaf => simp [containsb, contains]
  | node l v r ihl ihr => simp [containsb, contains, ihl, ihr]

lemma contains_insert_iff {α : Type u} [DecidableEq α] :
    ∀ (t : BinaryTree α) (x y : α) (f : α → ENat),
      contains (insert t y f) x ↔ contains t x ∨ x = y := by
  intro t x y f
  induction t generalizing y with
  | leaf =>
      simp [insert, contains]
      exact eq_comm
  | node l v r ihl ihr =>
      by_cases h : f y ≤ f v
      · simp [insert, contains, h, ihl]
        grind
      · simp [insert, contains, h, ihl]
        grind

lemma contains_merge_iff {α : Type u} :
    ∀ (t₁ t₂ : BinaryTree α) (x : α) (f : α → ENat),
      contains (merge t₁ t₂ f) x ↔ contains t₁ x ∨ contains t₂ x := by
  intro t₁ t₂ x f
  fun_induction merge t₁ t₂ f <;> simp [merge, contains, *] <;> grind

lemma contains_remove_subset {α : Type u} [DecidableEq α] :
    ∀ (t : BinaryTree α) (x y : α) (f : α → ENat),
      contains (remove t y f) x → contains t x := by
  intro t x y f
  induction t generalizing y f with
  | leaf => simp [remove, contains]
  | node l v r ihl ihr =>
      by_cases h : y = v
      · subst h
        simp [remove, contains, contains_merge_iff]
        intro hcase
        exact Or.inr hcase
      · simp [remove, contains, h]
        intro hcase
        rcases hcase with hroot | hl | hr
        · exact Or.inl hroot
        · exact Or.inr (Or.inl (ihl y f hl))
        · exact Or.inr (Or.inr (ihr y f hr))

lemma contains_remove_of_ne {α : Type u} [DecidableEq α] :
    ∀ (t : BinaryTree α) (x y : α) (f : α → ENat),
      contains t x → x ≠ y → contains (remove t y f) x := by
  intro t x y f
  induction t generalizing y f with
  | leaf => simp [contains]
  | node l v r ihl ihr =>
      intro hmem hne
      by_cases h : y = v
      · subst h
        simp [remove, contains_merge_iff]
        rcases hmem with hvx | hl | hr
        · exact False.elim (hne hvx.symm)
        · exact Or.inl hl
        · exact Or.inr hr
      · simp [remove, h, contains]
        rcases hmem with hvx | hl | hr
        · exact Or.inl hvx
        · exact Or.inr (Or.inl (ihl y f hl hne))
        · exact Or.inr (Or.inr (ihr y f hr hne))

lemma contains_decrease_priority_iff {α : Type u} [DecidableEq α] :
    ∀ (t : BinaryTree α) (x y : α) (f : α → ENat),
      contains (decrease_priority t y f) x ↔ contains t x := by
  intro t x y f
  by_cases hy : containsb t y = true
  · have hymem : contains t y := (containsb_eq_true_iff_contains t y).mp hy
    simp [decrease_priority, hy, contains_insert_iff]
    constructor
    · intro h
      rcases h with hrem | hxy
      · exact contains_remove_subset t x y f hrem
      · simpa [hxy] using hymem
    · intro hx
      by_cases hxy : x = y
      · exact Or.inr hxy
      · exact Or.inl (contains_remove_of_ne t x y f hx hxy)
  · simp [decrease_priority, hy]

lemma contains_heapify_iff {α : Type u} :
    ∀ (t : BinaryTree α) (x : α) (f : α → ENat),
      contains (heapify t f) x ↔ contains t x := by
  intro t x f
  fun_induction heapify t f <;> simp [heapify, contains, *] <;> grind

lemma get_last_fst_isSome {α : Type u} :
    ∀ t : BinaryTree α, t ≠ leaf → (get_last t).1.isSome := by
  intro t ht
  induction t with
  | leaf => contradiction
  | node l v r ihl ihr =>
      cases l with
      | leaf =>
          cases r with
          | leaf => simp [get_last]
          | node rl rv rr =>
              have hne : node rl rv rr ≠ (leaf : BinaryTree α) := by intro h; cases h
              simpa [get_last] using ihr hne
      | node ll lv lr =>
          have hne : node ll lv lr ≠ (leaf : BinaryTree α) := by intro h; cases h
          simpa [get_last] using ihl hne

lemma get_last_value_contains {α : Type u} :
    ∀ (t : BinaryTree α) (x : α), (get_last t).1 = some x → contains t x := by
  intro t x h
  fun_induction get_last t <;> simp [get_last, contains] at h ⊢ <;> grind

lemma get_last_tree_subset {α : Type u} :
    ∀ (t : BinaryTree α) (x : α), contains (get_last t).2 x → contains t x := by
  intro t x h
  fun_induction get_last t <;> simp [get_last, contains] at h ⊢ <;> grind

lemma get_last_value_or_tree {α : Type u} :
    ∀ (t : BinaryTree α) (x : α),
      contains t x → (get_last t).1 = some x ∨ contains (get_last t).2 x := by
  intro t x h
  fun_induction get_last t <;> simp [get_last, contains] at h ⊢ <;> grind

lemma get_last_node_leaf_fst {α : Type u} :
    ∀ (l r : BinaryTree α) (v : α),
      (get_last (node l v r)).2 = leaf → (get_last (node l v r)).1 = some v := by
  intro l r v h
  cases l <;> cases r <;> simp [get_last] at h ⊢

lemma get_last_node_tree_root {α : Type u} :
    ∀ (l r tl tr : BinaryTree α) (v tv : α),
      (get_last (node l v r)).2 = node tl tv tr → tv = v := by
  intro l r tl tr v tv h
  cases l <;> cases r <;> simp [get_last] at h ⊢ <;> grind

lemma extract_min_fst_node {α : Type u} :
    ∀ (l r : BinaryTree α) (v : α) (f : α → ENat),
      (extract_min (node l v r) f).1 = some v := by
  intro l r v f
  cases l with
  | leaf =>
      cases r with
      | leaf => simp [extract_min, get_last]
      | node rl rv rr =>
          unfold extract_min
          simp only [get_last]
          change (match (get_last (node rl rv rr)).1 with
            | none => (none, leaf)
            | some v' => (some v, (node leaf v' (get_last (node rl rv rr)).2).heapify f)).1 =
              some v
          have hs := get_last_fst_isSome (node rl rv rr) (by intro h; cases h)
          cases hlast : get_last (node rl rv rr) with
          | mk o t =>
              cases o with
              | none => simp [hlast] at hs
              | some a => simp
  | node ll lv lr =>
      unfold extract_min
      simp only [get_last]
      change (match (get_last (node ll lv lr)).1 with
        | none => (none, leaf)
        | some v' => (some v, (node (get_last (node ll lv lr)).2 v' r).heapify f)).1 =
          some v
      have hs := get_last_fst_isSome (node ll lv lr) (by intro h; cases h)
      cases hlast : get_last (node ll lv lr) with
      | mk o t =>
          cases o with
          | none => simp [hlast] at hs
          | some a => simp

lemma contains_extract_min_subset {α : Type u} :
    ∀ (t : BinaryTree α) (x : α) (f : α → ENat),
      contains (extract_min t f).2 x → contains t x := by
  intro t x f hmem
  unfold extract_min at hmem
  cases hlast : get_last t with
  | mk o rest =>
      simp [hlast] at hmem
      cases o with
      | none => simp [contains] at hmem
      | some last =>
          cases hrest : rest with
          | leaf => simp [hrest, contains] at hmem
          | node l v r =>
              have hpre : contains (node l last r) x := by
                exact (contains_heapify_iff (node l last r) x f).mp (by simpa [hrest] using hmem)
              rcases hpre with hlastx | hl | hr
              · exact get_last_value_contains t x (by simpa [hlastx] using congrArg Prod.fst hlast)
              · exact get_last_tree_subset t x (by
                  rw [hlast, hrest]
                  simp [contains]
                  exact Or.inr (Or.inl hl))
              · exact get_last_tree_subset t x (by
                  rw [hlast, hrest]
                  simp [contains]
                  exact Or.inr (Or.inr hr))

lemma contains_extract_min_of_ne_root {α : Type u} :
    ∀ (l r : BinaryTree α) (root x : α) (f : α → ENat),
      contains (node l root r) x → x ≠ root → contains (extract_min (node l root r) f).2 x := by
  intro l r root x f hmem hxne
  unfold extract_min
  cases hlast : get_last (node l root r) with
  | mk o t =>
      have hor := get_last_value_or_tree (node l root r) x hmem
      simp [hlast] at hor
      cases o with
      | none =>
          have hs := get_last_fst_isSome (node l root r) (by intro h; cases h)
          simp [hlast] at hs
      | some last =>
          cases ht : t with
          | leaf =>
              have hfst := get_last_node_leaf_fst l r root
              have hlast_root : last = root := by
                have := hfst (by simpa [hlast, ht])
                simpa [hlast] using this
              rcases hor with hlastx | htree
              · have : x = root := by
                  have hxlast : last = x := by simpa [hlast] using hlastx
                  exact hxlast ▸ hlast_root
                exact False.elim (hxne this)
              · rw [ht] at htree
                cases htree
          | node tl tv tr =>
              have htv : tv = root := by
                exact get_last_node_tree_root l r tl tr root tv (by simpa [hlast, ht])
              simp [ht, contains_heapify_iff, contains]
              rcases hor with hlastx | htree
              · have hxlast : last = x := by simpa [hlast] using hlastx
                exact Or.inl hxlast
              · rw [ht] at htree
                rcases htree with htvx | htl | htr
                · have : x = root := by simpa [htv] using htvx.symm
                  exact False.elim (hxne this)
                · exact Or.inr (Or.inl htl)
                · exact Or.inr (Or.inr htr)

def StrongHeap : BinaryTree α → (α → ENat) → Prop
  | leaf, _ => True
  | node l v r, f =>
      (∀ x, contains l x → f v ≤ f x) ∧
      (∀ x, contains r x → f v ≤ f x) ∧
      StrongHeap l f ∧ StrongHeap r f

def ChildrenStrongHeap : BinaryTree α → (α → ENat) → Prop
  | leaf, _ => True
  | node l _ r, f => StrongHeap l f ∧ StrongHeap r f

lemma strongHeap_root_le {α : Type u} {l r : BinaryTree α} {v x : α} {f : α → ENat} :
    StrongHeap (node l v r) f → contains (node l v r) x → f v ≤ f x := by
  intro hheap hmem
  rcases hheap with ⟨hl, hr, hhl, hhr⟩
  rcases hmem with hvx | hx | hx
  · simp [hvx]
  · exact hl x hx
  · exact hr x hx

lemma strongHeap_insert {α : Type u} [DecidableEq α] :
    ∀ (t : BinaryTree α) (y : α) (f : α → ENat),
      StrongHeap t f → StrongHeap (insert t y f) f := by
  intro t y f hheap
  induction t generalizing y with
  | leaf =>
      simp [insert, StrongHeap]
      intro x hx
      cases hx
  | node l v r ihl ihr =>
      rcases hheap with ⟨hl, hr, hhl, hhr⟩
      by_cases h : f y ≤ f v
      · simp [insert, h, StrongHeap]
        constructor
        · intro x hx
          have hx' := (contains_insert_iff l x v f).mp hx
          rcases hx' with hxl | hxv
          · exact le_trans h (hl x hxl)
          · simpa [hxv] using h
        · constructor
          · intro x hx
            exact le_trans h (hr x hx)
          · constructor
            · exact ihl v hhl
            · exact hhr
      · simp [insert, h, StrongHeap]
        constructor
        · intro x hx
          have hx' := (contains_insert_iff l x y f).mp hx
          rcases hx' with hxl | hxy
          · exact hl x hxl
          · have hy_ge : f v ≤ f y := by exact le_of_not_ge h
            simpa [hxy] using hy_ge
        · constructor
          · exact hr
          · constructor
            · exact ihl y hhl
            · exact hhr

lemma strongHeap_merge {α : Type u} :
    ∀ (t₁ t₂ : BinaryTree α) (f : α → ENat),
      StrongHeap t₁ f → StrongHeap t₂ f → StrongHeap (merge t₁ t₂ f) f := by
  intro t₁ t₂ f h₁ h₂
  fun_induction merge t₁ t₂ f with
  | case1 t => simpa [merge] using h₂
  | case2 t => simpa [merge] using h₁
  | case3 l1 v1 r1 l2 v2 r2 hle ih =>
      rcases h₁ with ⟨hl1, hr1, hhl1, hhr1⟩
      have h₂root : ∀ x, contains (node l2 v2 r2) x → f v2 ≤ f x := by
        intro x hx
        exact strongHeap_root_le h₂ hx
      simp [merge, hle, StrongHeap]
      constructor
      · intro x hx
        have hx' := (contains_merge_iff l1 (node l2 v2 r2) x f).mp hx
        rcases hx' with hxl1 | hx2
        · exact hl1 x hxl1
        · exact le_trans hle (h₂root x hx2)
      · constructor
        · exact hr1
        · constructor
          · exact ih hhl1 h₂
          · exact hhr1
  | case4 l1 v1 r1 l2 v2 r2 hnot ih =>
      rcases h₂ with ⟨hl2, hr2, hhl2, hhr2⟩
      have hle : f v2 ≤ f v1 := le_of_not_ge hnot
      have h₁root : ∀ x, contains (node l1 v1 r1) x → f v1 ≤ f x := by
        intro x hx
        exact strongHeap_root_le h₁ hx
      simp [merge, hnot, StrongHeap]
      constructor
      · intro x hx
        have hx' := (contains_merge_iff (node l1 v1 r1) l2 x f).mp hx
        rcases hx' with hx1 | hxl2
        · exact le_trans hle (h₁root x hx1)
        · exact hl2 x hxl2
      · constructor
        · exact hr2
        · constructor
          · exact ih h₁ hhl2
          · exact hhr2

lemma strongHeap_heapify {α : Type u} :
    ∀ (t : BinaryTree α) (f : α → ENat),
      ChildrenStrongHeap t f → StrongHeap (heapify t f) f := by
  intro t f hch
  fun_induction heapify t f with
  | case1 => simp [StrongHeap]
  | case2 v =>
      simp [heapify, StrongHeap]
      intro x hx
      cases hx
  | case3 v rl rv rr h ih =>
      rcases hch with ⟨_, hright⟩
      rcases hright with ⟨hrl, hrr, hhrl, hhrr⟩
      simp [heapify, h, StrongHeap]
      constructor
      · intro x hx; cases hx
      · constructor
        · intro x hx
          have hxold := (contains_heapify_iff (node rl v rr) x f).mp hx
          rcases hxold with hvx | hxl | hxr
          · exact le_of_lt (by simpa [hvx] using h)
          · exact hrl x hxl
          · exact hrr x hxr
        · exact ih ⟨hhrl, hhrr⟩
  | case4 v rl rv rr h =>
      rcases hch with ⟨_, hright⟩
      rcases hright with ⟨hrl, hrr, hhrl, hhrr⟩
      have hvle : f v ≤ f rv := le_of_not_gt h
      simp [heapify, h, StrongHeap]
      constructor
      · intro x hx; cases hx
      · constructor
        · intro x hx
          rcases hx with hvx | hrest
          · simpa [hvx] using hvle
          · rcases hrest with hxl | hxr
            · exact le_trans hvle (hrl x hxl)
            · exact le_trans hvle (hrr x hxr)
        · exact ⟨hrl, hrr, hhrl, hhrr⟩
  | case5 v ll lv lr h ih =>
      rcases hch with ⟨hleft, _⟩
      rcases hleft with ⟨hll, hlr, hhll, hhlr⟩
      simp [heapify, h, StrongHeap]
      constructor
      · intro x hx
        have hxold := (contains_heapify_iff (node ll v lr) x f).mp hx
        rcases hxold with hvx | hxl | hxr
        · exact le_of_lt (by simpa [hvx] using h)
        · exact hll x hxl
        · exact hlr x hxr
      · constructor
        · intro x hx; cases hx
        · exact ih ⟨hhll, hhlr⟩
  | case6 v ll lv lr h =>
      rcases hch with ⟨hleft, _⟩
      rcases hleft with ⟨hll, hlr, hhll, hhlr⟩
      have hvle : f v ≤ f lv := le_of_not_gt h
      simp [heapify, h, StrongHeap]
      constructor
      · intro x hx
        rcases hx with hvx | hrest
        · simpa [hvx] using hvle
        · rcases hrest with hxl | hxr
          · exact le_trans hvle (hll x hxl)
          · exact le_trans hvle (hlr x hxr)
      · constructor
        · intro x hx; cases hx
        · exact ⟨hll, hlr, hhll, hhlr⟩
  | case7 v ll lv lr rl rv rr hlerv hvle =>
      rcases hch with ⟨hl, hr⟩
      simp [heapify, hlerv, hvle, StrongHeap]
      constructor
      · intro x hx
        exact le_trans hvle (strongHeap_root_le hl hx)
      · constructor
        · intro x hx
          exact le_trans (le_trans hvle hlerv) (strongHeap_root_le hr hx)
        · exact ⟨hl, hr⟩
  | case8 v ll lv lr rl rv rr hlerv hlt ih =>
      rcases hch with ⟨hl, hr⟩
      rcases hl with ⟨hll, hlr, hhll, hhlr⟩
      simp [heapify, hlerv, hlt, StrongHeap]
      constructor
      · intro x hx
        have hxold := (contains_heapify_iff (node ll v lr) x f).mp hx
        rcases hxold with hvx | hxl | hxr
        · exact le_of_lt (by simpa [hvx] using hlt)
        · exact hll x hxl
        · exact hlr x hxr
      · constructor
        · intro x hx
          exact le_trans hlerv (strongHeap_root_le hr hx)
        · constructor
          · exact ih ⟨hhll, hhlr⟩
          · exact hr
  | case9 v ll lv lr rl rv rr hnot hvle =>
      rcases hch with ⟨hl, hr⟩
      have hrvlelv : f rv ≤ f lv := le_of_lt (lt_of_not_ge hnot)
      simp [heapify, hnot, hvle, StrongHeap]
      constructor
      · intro x hx
        exact le_trans (le_trans hvle hrvlelv) (strongHeap_root_le hl hx)
      · constructor
        · intro x hx
          exact le_trans hvle (strongHeap_root_le hr hx)
        · exact ⟨hl, hr⟩
  | case10 v ll lv lr rl rv rr hnot hrvvlt ih =>
      rcases hch with ⟨hl, hr⟩
      rcases hr with ⟨hrl, hrr, hhrl, hhrr⟩
      have hrvlelv : f rv ≤ f lv := le_of_lt (lt_of_not_ge hnot)
      simp [heapify, hnot, hrvvlt, StrongHeap]
      constructor
      · intro x hx
        exact le_trans hrvlelv (strongHeap_root_le hl hx)
      · constructor
        · intro x hx
          have hxold := (contains_heapify_iff (node rl v rr) x f).mp hx
          rcases hxold with hvx | hxl | hxr
          · exact le_of_lt (by simpa [hvx] using hrvvlt)
          · exact hrl x hxl
          · exact hrr x hxr
        · constructor
          · exact hl
          · exact ih ⟨hhrl, hhrr⟩

lemma strongHeap_get_last_tree {α : Type u} :
    ∀ (t : BinaryTree α) (f : α → ENat),
      StrongHeap t f → StrongHeap (get_last t).2 f := by
  intro t f hheap
  fun_induction get_last t <;> simp [get_last, StrongHeap] at * <;>
    grind [get_last_tree_subset]

lemma strongHeap_extract_min {α : Type u} :
    ∀ (t : BinaryTree α) (f : α → ENat),
      StrongHeap t f → StrongHeap (extract_min t f).2 f := by
  intro t f hheap
  cases t with
  | leaf => simp [extract_min, get_last, StrongHeap]
  | node l v r =>
      unfold extract_min
      cases hlast : get_last (node l v r) with
      | mk o rest =>
          cases o with
          | none => simp [StrongHeap]
          | some last =>
              cases hrest : rest with
              | leaf => simp [StrongHeap]
              | node tl tv tr =>
                  have hrestheap : StrongHeap (node tl tv tr) f := by
                    have := strongHeap_get_last_tree (node l v r) f hheap
                    simpa [hlast, hrest] using this
                  rcases hrestheap with ⟨hl, hr, hhl, hhr⟩
                  simp [hrest]
                  exact strongHeap_heapify (node tl last tr) f ⟨hhl, hhr⟩

lemma strongHeap_congr {α : Type u} :
    ∀ (t : BinaryTree α) (f g : α → ENat),
      (∀ x, contains t x → f x = g x) → StrongHeap t f → StrongHeap t g := by
  intro t f g hagree hheap
  induction t with
  | leaf => simp [StrongHeap]
  | node l v r ihl ihr =>
      rcases hheap with ⟨hl, hr, hhl, hhr⟩
      simp [StrongHeap]
      constructor
      · intro x hx
        have hv : f v = g v := hagree v (Or.inl rfl)
        have hxg : f x = g x := hagree x (Or.inr (Or.inl hx))
        simpa [← hv, ← hxg] using hl x hx
      · constructor
        · intro x hx
          have hv : f v = g v := hagree v (Or.inl rfl)
          have hxg : f x = g x := hagree x (Or.inr (Or.inr hx))
          simpa [← hv, ← hxg] using hr x hx
        · constructor
          · exact ihl (fun x hx => hagree x (Or.inr (Or.inl hx))) hhl
          · exact ihr (fun x hx => hagree x (Or.inr (Or.inr hx))) hhr

lemma strongHeap_remove {α : Type u} [DecidableEq α] :
    ∀ (t : BinaryTree α) (y : α) (f : α → ENat),
      StrongHeap t f → StrongHeap (remove t y f) f := by
  intro t y f hheap
  induction t generalizing y f with
  | leaf => simp [remove, StrongHeap]
  | node l v r ihl ihr =>
      rcases hheap with ⟨hl, hr, hhl, hhr⟩
      by_cases hy : y = v
      · subst hy
        simp [remove]
        exact strongHeap_merge l r f hhl hhr
      · simp [remove, hy, StrongHeap]
        constructor
        · intro x hx
          exact hl x (contains_remove_subset l x y f hx)
        · constructor
          · intro x hx
            exact hr x (contains_remove_subset r x y f hx)
          · constructor
            · exact ihl y f hhl
            · exact ihr y f hhr

def NoDupTree : BinaryTree α → Prop
  | leaf => True
  | node l v r =>
      NoDupTree l ∧ NoDupTree r ∧ ¬ contains l v ∧ ¬ contains r v ∧
        ∀ x, contains l x → contains r x → False

lemma noDup_insert {α : Type u} [DecidableEq α] :
    ∀ (t : BinaryTree α) (y : α) (f : α → ENat),
      NoDupTree t → ¬ contains t y → NoDupTree (insert t y f) := by
  intro t y f hnd hnot
  induction t generalizing y with
  | leaf => simp [insert, NoDupTree, contains]
  | node l v r ihl ihr =>
      rcases hnd with ⟨hndl, hndr, hnlv, hnrv, hdisj⟩
      have hnyv : y ≠ v := by intro h; exact hnot (Or.inl h.symm)
      have hnly : ¬ contains l y := by intro h; exact hnot (Or.inr (Or.inl h))
      have hnry : ¬ contains r y := by intro h; exact hnot (Or.inr (Or.inr h))
      by_cases hle : f y ≤ f v
      · simp [insert, hle, NoDupTree]
        constructor
        · exact ihl v hndl hnlv
        · constructor
          · exact hndr
          · constructor
            · intro hyin
              have hyold := (contains_insert_iff l y v f).mp hyin
              rcases hyold with hly | hyv
              · exact hnly hly
              · exact hnyv hyv
            · constructor
              · exact hnry
              · intro x hx hrx
                have hxold := (contains_insert_iff l x v f).mp hx
                rcases hxold with hxl | hxv
                · exact hdisj x hxl hrx
                · exact hnrv (by simpa [hxv] using hrx)
      · simp [insert, hle, NoDupTree]
        constructor
        · exact ihl y hndl hnly
        · constructor
          · exact hndr
          · constructor
            · intro hvin
              have hvold := (contains_insert_iff l v y f).mp hvin
              rcases hvold with hlv | hvy
              · exact hnlv hlv
              · exact hnyv hvy.symm
            · constructor
              · exact hnrv
              · intro x hx hrx
                have hxold := (contains_insert_iff l x y f).mp hx
                rcases hxold with hxl | hxy
                · exact hdisj x hxl hrx
                · exact hnry (by simpa [hxy] using hrx)

lemma noDup_merge {α : Type u} :
    ∀ (t₁ t₂ : BinaryTree α) (f : α → ENat),
      NoDupTree t₁ → NoDupTree t₂ →
      (∀ x, contains t₁ x → contains t₂ x → False) →
      NoDupTree (merge t₁ t₂ f) := by
  intro t₁ t₂ f hnd₁ hnd₂ hdisj12
  fun_induction merge t₁ t₂ f with
  | case1 t => simpa [merge, NoDupTree] using hnd₂
  | case2 t => simpa [merge, NoDupTree] using hnd₁
  | case3 l1 v1 r1 l2 v2 r2 hle ih =>
      rcases hnd₁ with ⟨hndl1, hndr1, hnl1v1, hnr1v1, hdisj1⟩
      have hnd_left : NoDupTree (merge l1 (node l2 v2 r2) f) := by
        apply ih hndl1 hnd₂
        intro x hx1 hx2
        exact hdisj12 x (Or.inr (Or.inl hx1)) hx2
      simp [merge, hle, NoDupTree]
      constructor
      · exact hnd_left
      · constructor
        · exact hndr1
        · constructor
          · intro hv1left
            have hv1old := (contains_merge_iff l1 (node l2 v2 r2) v1 f).mp hv1left
            rcases hv1old with hlv | h2v
            · exact hnl1v1 hlv
            · exact hdisj12 v1 (Or.inl rfl) h2v
          · constructor
            · exact hnr1v1
            · intro x hxleft hxr1
              have hxold := (contains_merge_iff l1 (node l2 v2 r2) x f).mp hxleft
              rcases hxold with hxl1 | hx2
              · exact hdisj1 x hxl1 hxr1
              · exact hdisj12 x (Or.inr (Or.inr hxr1)) hx2
  | case4 l1 v1 r1 l2 v2 r2 hnot ih =>
      rcases hnd₂ with ⟨hndl2, hndr2, hnl2v2, hnr2v2, hdisj2⟩
      have hnd_left : NoDupTree (merge (node l1 v1 r1) l2 f) := by
        apply ih hnd₁ hndl2
        intro x hx1 hx2
        exact hdisj12 x hx1 (Or.inr (Or.inl hx2))
      simp [merge, hnot, NoDupTree]
      constructor
      · exact hnd_left
      · constructor
        · exact hndr2
        · constructor
          · intro hv2left
            have hv2old := (contains_merge_iff (node l1 v1 r1) l2 v2 f).mp hv2left
            rcases hv2old with h1v | hl2v
            · exact hdisj12 v2 h1v (Or.inl rfl)
            · exact hnl2v2 hl2v
          · constructor
            · exact hnr2v2
            · intro x hxleft hxr2
              have hxold := (contains_merge_iff (node l1 v1 r1) l2 x f).mp hxleft
              rcases hxold with hx1 | hxl2
              · exact hdisj12 x hx1 (Or.inr (Or.inr hxr2))
              · exact hdisj2 x hxl2 hxr2

lemma noDup_remove {α : Type u} [DecidableEq α] :
    ∀ (t : BinaryTree α) (y : α) (f : α → ENat),
      NoDupTree t → NoDupTree (remove t y f) := by
  intro t y f hnd
  induction t generalizing y f with
  | leaf => simp [remove, NoDupTree]
  | node l v r ihl ihr =>
      rcases hnd with ⟨hndl, hndr, hnlv, hnrv, hdisj⟩
      by_cases hy : y = v
      · subst hy
        simp [remove]
        exact noDup_merge l r f hndl hndr hdisj
      · simp [remove, hy, NoDupTree]
        constructor
        · exact ihl y f hndl
        · constructor
          · exact ihr y f hndr
          · constructor
            · intro hvleft
              exact hnlv (contains_remove_subset l v y f hvleft)
            · constructor
              · intro hvright
                exact hnrv (contains_remove_subset r v y f hvright)
              · intro x hxleft hxright
                exact hdisj x (contains_remove_subset l x y f hxleft)
                  (contains_remove_subset r x y f hxright)

lemma remove_not_contains_of_noDup {α : Type u} [DecidableEq α] :
    ∀ (t : BinaryTree α) (y : α) (f : α → ENat),
      NoDupTree t → ¬ contains (remove t y f) y := by
  intro t y f hnd
  induction t generalizing y f with
  | leaf => simp [remove, contains]
  | node l v r ihl ihr =>
      rcases hnd with ⟨hndl, hndr, hnlv, hnrv, hdisj⟩
      by_cases hy : y = v
      · subst hy
        simp [remove, contains_merge_iff]
        exact ⟨hnlv, hnrv⟩
      · simp [remove, hy, contains]
        constructor
        · exact fun hvy => hy hvy.symm
        · constructor
          · exact ihl y f hndl
          · exact ihr y f hndr

lemma noDup_heapify {α : Type u} :
    ∀ (t : BinaryTree α) (f : α → ENat),
      NoDupTree t → NoDupTree (heapify t f) := by
  intro t f hnd
  fun_induction heapify t f <;> simp [heapify, NoDupTree, contains] at *
  all_goals grind [contains_heapify_iff, contains]

lemma noDup_get_last_tree {α : Type u} :
    ∀ (t : BinaryTree α), NoDupTree t → NoDupTree (get_last t).2 := by
  intro t hnd
  fun_induction get_last t <;> simp [get_last, NoDupTree] at * <;>
    grind [get_last_tree_subset]

lemma get_last_value_not_in_tree {α : Type u} :
    ∀ (t : BinaryTree α) (x : α),
      NoDupTree t → (get_last t).1 = some x → ¬ contains (get_last t).2 x := by
  intro t x hnd hval hmem
  fun_induction get_last t <;> simp [get_last, NoDupTree, contains] at * <;>
    grind [get_last_value_contains, get_last_tree_subset]

lemma noDup_extract_min {α : Type u} :
    ∀ (t : BinaryTree α) (f : α → ENat),
      NoDupTree t → NoDupTree (extract_min t f).2 := by
  intro t f hnd
  unfold extract_min
  cases hlast : get_last t with
  | mk o rest =>
      cases o with
      | none => simp [NoDupTree]
      | some last =>
          cases hrest : rest with
          | leaf => simp [NoDupTree]
          | node l v r =>
              have hrestnd : NoDupTree (node l v r) := by
                have := noDup_get_last_tree t hnd
                simpa [hlast, hrest] using this
              have hlast_not : ¬ contains (node l v r) last := by
                have := get_last_value_not_in_tree t last hnd
                  (by simpa [hlast] using congrArg Prod.fst hlast)
                simpa [hlast, hrest] using this
              rcases hrestnd with ⟨hndl, hndr, hnlv, hnrv, hdisj⟩
              simp [hrest]
              apply noDup_heapify
              simp [NoDupTree]
              constructor
              · exact hndl
              · constructor
                · exact hndr
                · constructor
                  · intro hl
                    exact hlast_not (Or.inr (Or.inl hl))
                  · constructor
                    · intro hr
                      exact hlast_not (Or.inr (Or.inr hr))
                    · exact hdisj

lemma strongHeap_remove_changed {α : Type u} [DecidableEq α] :
    ∀ (t : BinaryTree α) (y : α) (old new : α → ENat),
      NoDupTree t → StrongHeap t old →
      (∀ x, x ≠ y → new x = old x) →
      StrongHeap (remove t y new) new := by
  intro t y old new hnd hheap hagree
  induction t generalizing y old new with
  | leaf => simp [remove, StrongHeap]
  | node l v r ihl ihr =>
      rcases hnd with ⟨hndl, hndr, hnlv, hnrv, hdisj⟩
      rcases hheap with ⟨hl, hr, hhl, hhr⟩
      by_cases hy : y = v
      · subst hy
        simp [remove]
        have hlnew : StrongHeap l new := by
          apply strongHeap_congr l old new
          · intro x hx
            exact (hagree x (by intro hxv; exact hnlv (by simpa [hxv] using hx))).symm
          · exact hhl
        have hrnew : StrongHeap r new := by
          apply strongHeap_congr r old new
          · intro x hx
            exact (hagree x (by intro hxv; exact hnrv (by simpa [hxv] using hx))).symm
          · exact hhr
        exact strongHeap_merge l r new hlnew hrnew
      · have hvagree : new v = old v := hagree v (by intro h; exact hy h.symm)
        simp [remove, hy, StrongHeap]
        constructor
        · intro x hx
          have hxoldmem := contains_remove_subset l x y new hx
          have hxney : x ≠ y := by
            intro hxy
            have hbad := remove_not_contains_of_noDup l y new hndl
            exact hbad (by simpa [hxy] using hx)
          have hxagree : new x = old x := hagree x hxney
          simpa [hvagree, hxagree] using hl x hxoldmem
        · constructor
          · intro x hx
            have hxoldmem := contains_remove_subset r x y new hx
            have hxney : x ≠ y := by
              intro hxy
              have hbad := remove_not_contains_of_noDup r y new hndr
              exact hbad (by simpa [hxy] using hx)
            have hxagree : new x = old x := hagree x hxney
            simpa [hvagree, hxagree] using hr x hxoldmem
          · constructor
            · exact ihl y old new hndl hhl hagree
            · exact ihr y old new hndr hhr hagree

lemma strongHeap_decrease_priority_changed {α : Type u} [DecidableEq α] :
    ∀ (t : BinaryTree α) (y : α) (old new : α → ENat),
      NoDupTree t → StrongHeap t old →
      (∀ x, x ≠ y → new x = old x) →
      StrongHeap (decrease_priority t y new) new := by
  intro t y old new hnd hheap hagree
  by_cases hy : containsb t y = true
  · have hrem := strongHeap_remove_changed t y old new hnd hheap hagree
    simp [decrease_priority, hy]
    exact strongHeap_insert (remove t y new) y new hrem
  · have hnot : ¬ contains t y := by
      intro hmem
      exact hy ((containsb_eq_true_iff_contains t y).mpr hmem)
    simp [decrease_priority, hy]
    apply strongHeap_congr t old new
    · intro x hx
      exact (hagree x (by intro hxy; exact hnot (by simpa [hxy] using hx))).symm
    · exact hheap

lemma noDup_decrease_priority {α : Type u} [DecidableEq α] :
    ∀ (t : BinaryTree α) (y : α) (f : α → ENat),
      NoDupTree t → NoDupTree (decrease_priority t y f) := by
  intro t y f hnd
  by_cases hy : containsb t y = true
  · simp [decrease_priority, hy]
    apply noDup_insert
    · exact noDup_remove t y f hnd
    · exact remove_not_contains_of_noDup t y f hnd
  · simp [decrease_priority, hy]
    exact hnd

end BinaryTree

namespace BinaryHeap

def Mem {α : Type u} [DecidableEq α] (q : BinaryHeap α) (x : α) : Prop :=
  BinaryTree.contains q.tree x

def Strong {α : Type u} [DecidableEq α] (q : BinaryHeap α) (f : α → ENat) : Prop :=
  BinaryTree.StrongHeap q.tree f

def NoDup {α : Type u} [DecidableEq α] (q : BinaryHeap α) : Prop :=
  BinaryTree.NoDupTree q.tree

lemma not_mem_of_isEmpty {α : Type u} [DecidableEq α] (q : BinaryHeap α) (x : α) :
    q.isEmpty = true → ¬ Mem q x := by
  rcases q with ⟨t⟩
  cases t <;> simp [BinaryHeap.isEmpty, Mem, BinaryTree.contains]

lemma mem_add_iff {α : Type u} [DecidableEq α] (q : BinaryHeap α) (x y : α)
    (f : α → ENat) :
    Mem (q.add y f) x ↔ Mem q x ∨ x = y := by
  rcases q with ⟨t⟩
  simpa [Mem, BinaryHeap.add] using BinaryTree.contains_insert_iff t x y f

lemma mem_decrease_priority_iff {α : Type u} [DecidableEq α] (q : BinaryHeap α)
    (x y : α) (f : α → ENat) :
    Mem (q.decrease_priority y f) x ↔ Mem q x := by
  rcases q with ⟨t⟩
  simpa [Mem, BinaryHeap.decrease_priority] using
    BinaryTree.contains_decrease_priority_iff t x y f

lemma mem_extract_min_subset {α : Type u} [DecidableEq α] [Nonempty α]
    (q : BinaryHeap α) (f : α → ENat) (hne : ¬q.isEmpty = true) (x : α) :
    Mem (q.extract_min f hne).2 x → Mem q x := by
  rcases q with ⟨t⟩
  simpa [Mem, BinaryHeap.extract_min] using BinaryTree.contains_extract_min_subset t x f

lemma mem_extract_min_of_ne_fst {α : Type u} [DecidableEq α] [Nonempty α]
    (q : BinaryHeap α) (f : α → ENat) (hne : ¬q.isEmpty = true) (x : α) :
    Mem q x → x ≠ (q.extract_min f hne).1 → Mem (q.extract_min f hne).2 x := by
  rcases q with ⟨t⟩
  cases t with
  | leaf =>
      simp [Mem, BinaryTree.contains]
  | node l root r =>
      intro hx hxne
      have hfst :
          (BinaryHeap.extract_min ({ tree := node l root r } : BinaryHeap α) f hne).1 = root :=
        by simp [BinaryHeap.extract_min, BinaryTree.extract_min_fst_node]
      have hxne_root : x ≠ root := by
        intro hxr
        exact hxne (by simpa [hfst, hxr])
      simpa [Mem, BinaryHeap.extract_min] using
        BinaryTree.contains_extract_min_of_ne_root l r root x f hx hxne_root

lemma mem_extract_min_cases {α : Type u} [DecidableEq α] [Nonempty α]
    (q : BinaryHeap α) (f : α → ENat) (hne : ¬q.isEmpty = true) (x : α) :
    Mem q x → x = (q.extract_min f hne).1 ∨ Mem (q.extract_min f hne).2 x := by
  intro hx
  by_cases hxf : x = (q.extract_min f hne).1
  · exact Or.inl hxf
  · exact Or.inr (mem_extract_min_of_ne_fst q f hne x hx hxf)

lemma strong_add {α : Type u} [DecidableEq α] (q : BinaryHeap α) (x : α)
    (f : α → ENat) :
    Strong q f → Strong (q.add x f) f := by
  rcases q with ⟨t⟩
  exact BinaryTree.strongHeap_insert t x f

lemma noDup_add {α : Type u} [DecidableEq α] (q : BinaryHeap α) (x : α)
    (f : α → ENat) :
    NoDup q → ¬ Mem q x → NoDup (q.add x f) := by
  rcases q with ⟨t⟩
  exact BinaryTree.noDup_insert t x f

lemma strong_extract_min {α : Type u} [DecidableEq α] [Nonempty α]
    (q : BinaryHeap α) (f : α → ENat) (hne : ¬q.isEmpty = true) :
    Strong q f → Strong (q.extract_min f hne).2 f := by
  rcases q with ⟨t⟩
  simpa [Strong, BinaryHeap.extract_min] using BinaryTree.strongHeap_extract_min t f

lemma noDup_extract_min {α : Type u} [DecidableEq α] [Nonempty α]
    (q : BinaryHeap α) (f : α → ENat) (hne : ¬q.isEmpty = true) :
    NoDup q → NoDup (q.extract_min f hne).2 := by
  rcases q with ⟨t⟩
  simpa [NoDup, BinaryHeap.extract_min] using BinaryTree.noDup_extract_min t f

lemma strong_decrease_priority_changed {α : Type u} [DecidableEq α]
    (q : BinaryHeap α) (y : α) (old new : α → ENat) :
    NoDup q → Strong q old → (∀ x, x ≠ y → new x = old x) →
    Strong (q.decrease_priority y new) new := by
  rcases q with ⟨t⟩
  exact BinaryTree.strongHeap_decrease_priority_changed t y old new

lemma noDup_decrease_priority {α : Type u} [DecidableEq α]
    (q : BinaryHeap α) (y : α) (f : α → ENat) :
    NoDup q → NoDup (q.decrease_priority y f) := by
  rcases q with ⟨t⟩
  exact BinaryTree.noDup_decrease_priority t y f

lemma extract_min_fst_node_heap {α : Type u} [DecidableEq α] [Nonempty α]
    (l r : BinaryTree α) (u : α) (f : α → ENat)
    (hne : ¬(BinaryHeap.isEmpty ({ tree := node l u r } : BinaryHeap α)) = true) :
    (BinaryHeap.extract_min ({ tree := node l u r } : BinaryHeap α) f hne).1 = u := by
  simp [BinaryHeap.extract_min, BinaryTree.extract_min_fst_node]

end BinaryHeap
