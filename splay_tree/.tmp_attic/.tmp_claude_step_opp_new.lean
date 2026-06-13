import Challenges.Splay_Tree.ArsenalTmp

set_option maxHeartbeats 2000000

namespace Splay

/-! ## §A  Membership / ForallTree helpers -/

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

end Splay

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

end Splay

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

end Splay

namespace Splay

/-! ## §E  Counting helpers for the W6'-weakened within-run bound -/

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

end Splay

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

end Splay

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

end Splay

#print axioms Splay.splay_root_of_mem
#print axioms Splay.divergeSuffix_splay_found
#print axioms Splay.divergeSuffix_splay_found_mirror
#print axioms Splay.touchedCount_within_run_splay_le_W6
#print axioms Splay.touchedCount_boundary_splay_le_two
#print axioms Splay.oppC2_step
#print axioms Splay.oppC3_step
#print axioms Splay.oppC3_step_two
#print axioms Splay.oppC3_count
