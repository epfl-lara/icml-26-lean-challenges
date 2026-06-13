import Challenges.Splay_Tree.Def_Ackermann

/-!
M1 staging for a finite-sequence Davenport--Schinzel formalization.

This file is intentionally self-contained and touches no project files.  It
sets up the sequence predicates used by the order-3 target and proves two
small base-case bounds.
-/

namespace CodexDS

open Classical

def HasABA (u : List ℕ) : Prop :=
  ∃ a b : ℕ, a ≠ b ∧ List.Sublist [a, b, a] u

def HasABAB (u : List ℕ) : Prop :=
  ∃ a b : ℕ, a ≠ b ∧ List.Sublist [a, b, a, b] u

def HasABABA (u : List ℕ) : Prop :=
  ∃ a b : ℕ, a ≠ b ∧ List.Sublist [a, b, a, b, a] u

def ABAFree (u : List ℕ) : Prop := ¬ HasABA u

def ABABFree (u : List ℕ) : Prop := ¬ HasABAB u

def ABABAFree (u : List ℕ) : Prop := ¬ HasABABA u

def Sparse (u : List ℕ) : Prop := u.Chain' (fun a b : ℕ => a ≠ b)

/-- Maximal constant blocks, represented as nonempty runs except for the empty input. -/
def prependBlock (x : ℕ) : List (List ℕ) → List (List ℕ)
  | [] => [[x]]
  | [] :: bs => [x] :: bs
  | (y :: b) :: bs =>
      if x = y then (x :: y :: b) :: bs else [x] :: (y :: b) :: bs

def blocks : List ℕ → List (List ℕ)
  | [] => []
  | x :: xs => prependBlock x (blocks xs)

def flattenBlocks : List (List ℕ) → List ℕ
  | [] => []
  | b :: bs => b ++ flattenBlocks bs

@[simp] theorem flattenBlocks_append (bs cs : List (List ℕ)) :
    flattenBlocks (bs ++ cs) = flattenBlocks bs ++ flattenBlocks cs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp [flattenBlocks, ih, List.append_assoc]

def Blocked (m : ℕ) (u : List ℕ) : Prop :=
  ∃ bs : List (List ℕ),
    bs.length ≤ m ∧
    (∀ b ∈ bs, b.Nodup) ∧
    flattenBlocks bs = u

def singletonBlocks : List ℕ → List (List ℕ)
  | [] => []
  | x :: xs => [x] :: singletonBlocks xs

@[simp] theorem flattenBlocks_singletonBlocks (u : List ℕ) :
    flattenBlocks (singletonBlocks u) = u := by
  induction u with
  | nil => rfl
  | cons x xs ih =>
      simp [singletonBlocks, flattenBlocks, ih]

@[simp] theorem singletonBlocks_length (u : List ℕ) :
    (singletonBlocks u).length = u.length := by
  induction u with
  | nil => rfl
  | cons x xs ih =>
      simp [singletonBlocks, ih]

theorem singletonBlocks_nodup_blocks (u : List ℕ) :
    ∀ b ∈ singletonBlocks u, b.Nodup := by
  intro b hb
  induction u with
  | nil => simp [singletonBlocks] at hb
  | cons x xs ih =>
      simp [singletonBlocks] at hb
      rcases hb with rfl | hb
      · simp
      · exact ih hb

theorem blocked_of_singletons (u : List ℕ) :
    Blocked u.length u := by
  refine ⟨singletonBlocks u, ?_, ?_, ?_⟩
  · simp
  · exact singletonBlocks_nodup_blocks u
  · simp

theorem sparse_blocked_by_length (u : List ℕ) (_hs : Sparse u) :
    Blocked u.length u :=
  blocked_of_singletons u

theorem Blocked.mono {m m' : ℕ} {u : List ℕ}
    (hmm' : m ≤ m') (h : Blocked m u) : Blocked m' u := by
  rcases h with ⟨bs, hlen, hnodup, hflat⟩
  exact ⟨bs, le_trans hlen hmm', hnodup, hflat⟩

def DSBound (m n L : ℕ) : Prop :=
  ∀ u : List ℕ,
    ABABAFree u →
    Sparse u →
    Blocked m u →
    u.toFinset.card ≤ n →
    u.length ≤ L

theorem DSBound.mono {m n L m' n' L' : ℕ}
    (h : DSBound m n L) (hm : m' ≤ m) (hn : n' ≤ n) (hL : L ≤ L') :
    DSBound m' n' L' := by
  intro u hfree hs hblocked hcard
  exact le_trans (h u hfree hs (hblocked.mono hm) (le_trans hcard hn)) hL

def flattenBlockGroups : List (List (List ℕ)) → List (List ℕ)
  | [] => []
  | g :: gs => g ++ flattenBlockGroups gs

@[simp] theorem flattenBlocks_flattenBlockGroups_cons
    (g : List (List ℕ)) (gs : List (List (List ℕ))) :
    flattenBlocks (flattenBlockGroups (g :: gs)) =
      flattenBlocks g ++ flattenBlocks (flattenBlockGroups gs) := by
  simp [flattenBlockGroups]

def occursInGroup (a : ℕ) (g : List (List ℕ)) : Prop :=
  a ∈ flattenBlocks g

def IsGlobalInGroups (a : ℕ) (groups : List (List (List ℕ))) : Prop :=
  ∃ g₁ ∈ groups, ∃ g₂ ∈ groups,
    g₁ ≠ g₂ ∧ occursInGroup a g₁ ∧ occursInGroup a g₂

noncomputable def groupGlobalSymbols (groups : List (List (List ℕ))) (g : List (List ℕ)) : List ℕ :=
  (flattenBlocks g).dedup.filter (fun a => IsGlobalInGroups a groups)

noncomputable def globalContraction (groups : List (List (List ℕ))) : List ℕ :=
  flattenBlocks (groups.map (groupGlobalSymbols groups))

theorem groupGlobalSymbols_nodup (groups : List (List (List ℕ))) (g : List (List ℕ)) :
    (groupGlobalSymbols groups g).Nodup := by
  unfold groupGlobalSymbols
  exact (List.nodup_dedup (flattenBlocks g)).filter _

theorem groupGlobalSymbols_sublist
    (groups : List (List (List ℕ))) (g : List (List ℕ)) :
    List.Sublist (groupGlobalSymbols groups g) (flattenBlocks g) := by
  unfold groupGlobalSymbols
  exact List.filter_sublist.trans (List.dedup_sublist (flattenBlocks g))

theorem globalContraction_blocked (groups : List (List (List ℕ))) :
    Blocked groups.length (globalContraction groups) := by
  refine ⟨groups.map (groupGlobalSymbols groups), ?_, ?_, ?_⟩
  · simp [globalContraction]
  · intro b hb
    rcases List.mem_map.mp hb with ⟨g, hg, rfl⟩
    exact groupGlobalSymbols_nodup groups g
  · rfl

theorem globalContraction_sublist_groups_aux
    (all groups : List (List (List ℕ))) :
    List.Sublist
      (flattenBlocks (groups.map (groupGlobalSymbols all)))
      (flattenBlocks (flattenBlockGroups groups)) := by
  induction groups with
  | nil =>
      exact List.Sublist.slnil
  | cons g gs ih =>
      rw [List.map_cons, flattenBlocks, flattenBlockGroups, flattenBlocks_append]
      exact List.Sublist.append (groupGlobalSymbols_sublist all g) ih

theorem globalContraction_sublist_groups (groups : List (List (List ℕ))) :
    List.Sublist (globalContraction groups)
      (flattenBlocks (flattenBlockGroups groups)) := by
  simpa [globalContraction] using globalContraction_sublist_groups_aux groups groups

theorem globalContraction_ababaFree {groups : List (List (List ℕ))}
    (hfree : ABABAFree (flattenBlocks (flattenBlockGroups groups))) :
    ABABAFree (globalContraction groups) := by
  intro hbad
  rcases hbad with ⟨a, b, hne, hsub⟩
  exact hfree ⟨a, b, hne, hsub.trans (globalContraction_sublist_groups groups)⟩

theorem toFinset_card_le_of_sublist {v u : List ℕ}
    (hsub : List.Sublist v u) :
    v.toFinset.card ≤ u.toFinset.card := by
  apply Finset.card_le_card
  intro x hx
  rw [List.mem_toFinset] at hx ⊢
  exact hsub.subset hx

theorem globalContraction_card_le
    (groups : List (List (List ℕ))) :
    (globalContraction groups).toFinset.card ≤
      (flattenBlocks (flattenBlockGroups groups)).toFinset.card :=
  toFinset_card_le_of_sublist (globalContraction_sublist_groups groups)

/-! ## M6 grouping projections -/

def chunkBlocksFuel : ℕ → ℕ → List (List ℕ) → List (List (List ℕ))
  | 0, _b, _bs => []
  | fuel + 1, b, bs =>
      match bs with
      | [] => []
      | _ =>
          if b = 0 then
            [bs]
          else
            bs.take b :: chunkBlocksFuel fuel b (bs.drop b)

def chunkBlocks (b : ℕ) (bs : List (List ℕ)) : List (List (List ℕ)) :=
  chunkBlocksFuel bs.length b bs

@[simp] theorem chunkBlocks_nil (b : ℕ) :
    chunkBlocks b [] = [] := by
  rfl

theorem flattenBlockGroups_chunkBlocksFuel
    (b fuel : ℕ) (hb : 0 < b) :
    ∀ bs : List (List ℕ), bs.length ≤ fuel →
      flattenBlockGroups (chunkBlocksFuel fuel b bs) = bs := by
  induction fuel with
  | zero =>
      intro bs hlen
      have hzero : bs.length = 0 := Nat.eq_zero_of_le_zero hlen
      have hnil : bs = [] := List.eq_nil_of_length_eq_zero hzero
      subst bs
      rfl
  | succ fuel ih =>
      intro bs hlen
      cases bs with
      | nil =>
          simp [chunkBlocksFuel, flattenBlockGroups]
      | cons block rest =>
          have hdrop_len : ((block :: rest).drop b).length ≤ fuel := by
            rw [List.length_drop]
            have hrest : rest.length ≤ fuel := by
              exact Nat.succ_le_succ_iff.mp (by simpa using hlen)
            omega
          simp [chunkBlocksFuel, hb.ne', flattenBlockGroups,
            ih ((block :: rest).drop b) hdrop_len,
            List.take_append_drop]

theorem flattenBlockGroups_chunkBlocks {b : ℕ} (hb : 0 < b)
    (bs : List (List ℕ)) :
    flattenBlockGroups (chunkBlocks b bs) = bs := by
  exact flattenBlockGroups_chunkBlocksFuel b bs.length hb bs le_rfl

noncomputable def groupLocalSubsequence
    (groups : List (List (List ℕ))) (g : List (List ℕ)) : List ℕ :=
  (flattenBlocks g).filter (fun a => ¬ IsGlobalInGroups a groups)

noncomputable def groupLocalSymbols
    (groups : List (List (List ℕ))) (g : List (List ℕ)) : List ℕ :=
  (groupLocalSubsequence groups g).dedup

noncomputable def groupLocalBlocks
    (groups : List (List (List ℕ))) (g : List (List ℕ)) : List (List ℕ) :=
  g.map (fun block => block.filter (fun a => ¬ IsGlobalInGroups a groups))

theorem groupLocalSubsequence_sublist
    (groups : List (List (List ℕ))) (g : List (List ℕ)) :
    List.Sublist (groupLocalSubsequence groups g) (flattenBlocks g) := by
  unfold groupLocalSubsequence
  exact List.filter_sublist

theorem flattenBlocks_groupLocalBlocks
    (groups : List (List (List ℕ))) (g : List (List ℕ)) :
    flattenBlocks (groupLocalBlocks groups g) =
      groupLocalSubsequence groups g := by
  induction g with
  | nil =>
      rfl
  | cons block rest ih =>
      change block.filter (fun a => ¬ IsGlobalInGroups a groups) ++
          flattenBlocks (groupLocalBlocks groups rest) =
        (block ++ flattenBlocks rest).filter
          (fun a => ¬ IsGlobalInGroups a groups)
      rw [ih, List.filter_append]
      simp [groupLocalSubsequence]

theorem groupLocalBlocks_nodup
    (groups : List (List (List ℕ))) {g : List (List ℕ)}
    (hnodup : ∀ block ∈ g, block.Nodup) :
    ∀ block ∈ groupLocalBlocks groups g, block.Nodup := by
  intro block hb
  rcases List.mem_map.mp hb with ⟨orig, horig, rfl⟩
  exact (hnodup orig horig).filter _

theorem groupLocalSubsequence_blocked
    (groups : List (List (List ℕ))) {g : List (List ℕ)} {b : ℕ}
    (hglen : g.length ≤ b) (hnodup : ∀ block ∈ g, block.Nodup) :
    Blocked b (groupLocalSubsequence groups g) := by
  refine ⟨groupLocalBlocks groups g, ?_, ?_, ?_⟩
  · simpa [groupLocalBlocks] using hglen
  · exact groupLocalBlocks_nodup groups hnodup
  · exact flattenBlocks_groupLocalBlocks groups g

theorem flattenBlocks_group_sublist_flattenBlockGroups_of_mem
    {g : List (List ℕ)} {groups : List (List (List ℕ))}
    (hg : g ∈ groups) :
    List.Sublist (flattenBlocks g)
      (flattenBlocks (flattenBlockGroups groups)) := by
  induction groups with
  | nil =>
      simp at hg
  | cons head tail ih =>
      simp at hg
      rw [flattenBlockGroups, flattenBlocks_append]
      rcases hg with rfl | hg
      · exact List.sublist_append_left (flattenBlocks g)
          (flattenBlocks (flattenBlockGroups tail))
      · exact (ih hg).trans
          (List.sublist_append_right (flattenBlocks head)
            (flattenBlocks (flattenBlockGroups tail)))

theorem groupLocalSubsequence_ababaFree
    {groups : List (List (List ℕ))} {g : List (List ℕ)}
    (hg : g ∈ groups)
    (hfree : ABABAFree (flattenBlocks (flattenBlockGroups groups))) :
    ABABAFree (groupLocalSubsequence groups g) := by
  intro hbad
  rcases hbad with ⟨a, b, hne, hsub⟩
  exact hfree ⟨a, b, hne,
    hsub.trans ((groupLocalSubsequence_sublist groups g).trans
      (flattenBlocks_group_sublist_flattenBlockGroups_of_mem hg))⟩

def occursOnBothSides (a : ℕ) (pre post : List ℕ) : Prop :=
  a ∈ pre ∧ a ∈ post

noncomputable def middleRaw
    (pre : List ℕ) (group : List (List ℕ)) (post : List ℕ) : List ℕ :=
  (flattenBlocks group).filter (fun a => occursOnBothSides a pre post)

noncomputable def middleSymbols
    (pre : List ℕ) (group : List (List ℕ)) (post : List ℕ) : List ℕ :=
  (middleRaw pre group post).dedup

theorem middleRaw_sublist
    (pre : List ℕ) (group : List (List ℕ)) (post : List ℕ) :
    List.Sublist (middleRaw pre group post) (flattenBlocks group) := by
  unfold middleRaw
  exact List.filter_sublist

/--
The remaining local Hart--Sharir counting lemma: within one consecutive group,
symbols that occur on both sides contribute at most one representative plus a
linear boundary term in the number of blocks of the group.
-/
def MiddlesKeyHypothesis : Prop :=
  ∀ (pre : List ℕ) (group : List (List ℕ)) (post : List ℕ),
    ABABAFree (pre ++ flattenBlocks group ++ post) →
    (∀ block ∈ group, block.Nodup) →
    (middleRaw pre group post).length ≤
      (middleSymbols pre group post).length + group.length

noncomputable def boundaryRaw
    (groups : List (List (List ℕ))) (pre : List ℕ)
    (group : List (List ℕ)) (post : List ℕ) : List ℕ :=
  (flattenBlocks group).filter
    (fun a => IsGlobalInGroups a groups ∧ ¬ occursOnBothSides a pre post)

noncomputable def localLengthTotal
    (groups : List (List (List ℕ))) : List (List (List ℕ)) → ℕ
  | [] => 0
  | g :: gs => (groupLocalSubsequence groups g).length + localLengthTotal groups gs

noncomputable def middleLengthTotalFrom
    (pre : List ℕ) : List (List (List ℕ)) → ℕ
  | [] => 0
  | g :: gs =>
      (middleRaw pre g (flattenBlocks (flattenBlockGroups gs))).length +
        middleLengthTotalFrom (pre ++ flattenBlocks g) gs

noncomputable def middleSymbolsLengthTotalFrom
    (pre : List ℕ) : List (List (List ℕ)) → ℕ
  | [] => 0
  | g :: gs =>
      (middleSymbols pre g (flattenBlocks (flattenBlockGroups gs))).length +
        middleSymbolsLengthTotalFrom (pre ++ flattenBlocks g) gs

noncomputable def boundaryLengthTotalFrom
    (groups : List (List (List ℕ))) (pre : List ℕ) :
    List (List (List ℕ)) → ℕ
  | [] => 0
  | g :: gs =>
      (boundaryRaw groups pre g (flattenBlocks (flattenBlockGroups gs))).length +
        boundaryLengthTotalFrom groups (pre ++ flattenBlocks g) gs

theorem length_le_filter_trichotomy
    (l : List ℕ) (P Q : ℕ → Bool) :
    l.length ≤
      (l.filter (fun a => ! P a)).length +
        (l.filter Q).length +
          (l.filter (fun a => P a && ! Q a)).length := by
  induction l with
  | nil =>
      simp
  | cons x xs ih =>
      cases hp : P x <;> cases hq : Q x <;> simp [hp, hq]
      all_goals omega

theorem group_trichotomy_length_le
    (groups : List (List (List ℕ))) (pre : List ℕ)
    (group : List (List ℕ)) (post : List ℕ) :
    (flattenBlocks group).length ≤
      (groupLocalSubsequence groups group).length +
        (middleRaw pre group post).length +
          (boundaryRaw groups pre group post).length := by
  simpa [groupLocalSubsequence, middleRaw, boundaryRaw] using
    (length_le_filter_trichotomy
      (l := flattenBlocks group)
      (P := fun a => decide (IsGlobalInGroups a groups))
      (Q := fun a => decide (occursOnBothSides a pre post)))

theorem oneStep_trichotomy_aux
    (groups allGroups : List (List (List ℕ))) (pre : List ℕ) :
    (flattenBlocks (flattenBlockGroups groups)).length ≤
      localLengthTotal allGroups groups +
        middleLengthTotalFrom pre groups +
          boundaryLengthTotalFrom allGroups pre groups := by
  induction groups generalizing pre with
  | nil =>
      simp [flattenBlockGroups, flattenBlocks, localLengthTotal, middleLengthTotalFrom,
        boundaryLengthTotalFrom]
  | cons g gs ih =>
      have hhead :=
        group_trichotomy_length_le allGroups pre g
          (flattenBlocks (flattenBlockGroups gs))
      have htail := ih (pre ++ flattenBlocks g)
      simp [flattenBlockGroups, flattenBlocks_append, localLengthTotal,
        middleLengthTotalFrom, boundaryLengthTotalFrom]
      omega

theorem middleLengthTotalFrom_le_of_middles_key
    (hmid : MiddlesKeyHypothesis) :
    ∀ (pre : List ℕ) (groups : List (List (List ℕ))),
      ABABAFree (pre ++ flattenBlocks (flattenBlockGroups groups)) →
      (∀ block ∈ flattenBlockGroups groups, block.Nodup) →
      middleLengthTotalFrom pre groups ≤
        middleSymbolsLengthTotalFrom pre groups +
          (flattenBlockGroups groups).length
  | pre, [], _hfree, _hnodup => by
      simp [flattenBlockGroups, middleLengthTotalFrom, middleSymbolsLengthTotalFrom]
  | pre, g :: gs, hfree, hnodup => by
      have hhead_free :
          ABABAFree (pre ++ flattenBlocks g ++
            flattenBlocks (flattenBlockGroups gs)) := by
        simpa [flattenBlockGroups, flattenBlocks_append, List.append_assoc] using hfree
      have hhead_nodup : ∀ block ∈ g, block.Nodup := by
        intro block hb
        exact hnodup block (by simp [flattenBlockGroups, hb])
      have hhead :=
        hmid pre g (flattenBlocks (flattenBlockGroups gs)) hhead_free hhead_nodup
      have htail_free :
          ABABAFree ((pre ++ flattenBlocks g) ++
            flattenBlocks (flattenBlockGroups gs)) := by
        simpa [List.append_assoc] using hhead_free
      have htail_nodup : ∀ block ∈ flattenBlockGroups gs, block.Nodup := by
        intro block hb
        exact hnodup block (by simp [flattenBlockGroups, hb])
      have htail :=
        middleLengthTotalFrom_le_of_middles_key hmid
          (pre ++ flattenBlocks g) gs htail_free htail_nodup
      simp [flattenBlockGroups, flattenBlocks_append, middleLengthTotalFrom,
        middleSymbolsLengthTotalFrom]
      omega

/--
M6a one-step counting lemma.  It partitions each occurrence into a local
occurrence, a middle occurrence, or a global boundary occurrence, then consumes
`MiddlesKeyHypothesis` group-by-group to cap middle multiplicity.
-/
theorem oneStep_counting_of_middles_key
    (hmid : MiddlesKeyHypothesis) (groups : List (List (List ℕ)))
    (hfree : ABABAFree (flattenBlocks (flattenBlockGroups groups)))
    (hnodup : ∀ block ∈ flattenBlockGroups groups, block.Nodup) :
    (flattenBlocks (flattenBlockGroups groups)).length ≤
      localLengthTotal groups groups +
        middleSymbolsLengthTotalFrom [] groups +
          (flattenBlockGroups groups).length +
            boundaryLengthTotalFrom groups [] groups := by
  have htri := oneStep_trichotomy_aux groups groups []
  have hmid_bound :=
    middleLengthTotalFrom_le_of_middles_key hmid []
      groups (by simpa using hfree) hnodup
  omega

theorem nil_sublist (u : List ℕ) : List.Sublist ([] : List ℕ) u := by
  induction u with
  | nil => exact List.Sublist.slnil
  | cons x xs ih => exact ih.cons x

@[simp] theorem prependBlock_join (x : ℕ) (bs : List (List ℕ)) :
    flattenBlocks (prependBlock x bs) = x :: flattenBlocks bs := by
  cases bs with
  | nil => rfl
  | cons b bs =>
      cases b with
      | nil => rfl
      | cons y ys =>
          unfold prependBlock
          by_cases h : x = y
          · subst x
            simp [prependBlock, flattenBlocks]
          · simp [prependBlock, flattenBlocks, h]

@[simp] theorem blocks_join (u : List ℕ) : flattenBlocks (blocks u) = u := by
  induction u with
  | nil => rfl
  | cons x xs ih =>
      simp [blocks, ih]

def adjacentPairs : List ℕ → List (ℕ × ℕ)
  | [] => []
  | [_] => []
  | x :: y :: xs => (x, y) :: adjacentPairs (y :: xs)

theorem adjacentPairs_length_add_one (u : List ℕ) :
    (adjacentPairs u).length + 1 ≥ u.length := by
  induction u with
  | nil => simp [adjacentPairs]
  | cons x xs ih =>
      cases xs with
      | nil => simp [adjacentPairs]
      | cons y ys =>
          simp [adjacentPairs] at ih ⊢
          omega

theorem mem_adjacentPairs_support {u : List ℕ} {p : ℕ × ℕ}
    (hp : p ∈ adjacentPairs u) : p.1 ∈ u ∧ p.2 ∈ u := by
  induction u with
  | nil => simp [adjacentPairs] at hp
  | cons x xs ih =>
      cases xs with
      | nil => simp [adjacentPairs] at hp
      | cons y ys =>
          simp [adjacentPairs] at hp
          rcases hp with hp | hp
          · cases hp
            simp
          · have h := ih hp
            simp [h.1, h.2]

theorem pair_sublist_of_mem_adjacentPairs {u : List ℕ} {a b : ℕ}
    (h : (a, b) ∈ adjacentPairs u) : List.Sublist [a, b] u := by
  induction u with
  | nil => simp [adjacentPairs] at h
  | cons x xs ih =>
      cases xs with
      | nil => simp [adjacentPairs] at h
      | cons y ys =>
          simp [adjacentPairs] at h
          rcases h with hxy | htail
          · rcases hxy with ⟨rfl, rfl⟩
            exact List.Sublist.cons₂ a (List.Sublist.cons₂ b (nil_sublist ys))
          · exact (ih htail).cons x

theorem pair_sublist_tail_of_mem_adjacentPairs_cons {x y : ℕ} {xs : List ℕ}
    (hxy : x ≠ y) (h : (x, y) ∈ adjacentPairs (y :: xs)) :
    List.Sublist [x, y] xs := by
  cases xs with
  | nil => simp [adjacentPairs] at h
  | cons z zs =>
      simp [adjacentPairs] at h
      rcases h with hhead | htail
      · rcases hhead with ⟨hyx, _hyz⟩
        exact False.elim (hxy hyx)
      · exact pair_sublist_of_mem_adjacentPairs htail

theorem aba_sublist_of_mem_tail {x y : ℕ} {ys : List ℕ}
    (hxy : x ≠ y) (hmem : x ∈ ys) :
    List.Sublist [x, y, x] (x :: y :: ys) := by
  have hx : List.Sublist [x] ys := (List.singleton_sublist).2 hmem
  exact List.Sublist.cons₂ x (List.Sublist.cons₂ y hx)

theorem abab_sublist_of_repeated_adjacent_pair {x y : ℕ} {xs : List ℕ}
    (hxy : x ≠ y) (h : (x, y) ∈ adjacentPairs (y :: xs)) :
    List.Sublist [x, y, x, y] (x :: y :: xs) := by
  have htail : List.Sublist [x, y] xs :=
    pair_sublist_tail_of_mem_adjacentPairs_cons hxy h
  exact List.Sublist.cons₂ x (List.Sublist.cons₂ y htail)

def beforeFirst (a : ℕ) : List ℕ → List ℕ
  | [] => []
  | x :: xs => if x = a then [] else x :: beforeFirst a xs

def afterFirst (a : ℕ) : List ℕ → List ℕ
  | [] => []
  | x :: xs => if x = a then xs else afterFirst a xs

theorem splitAtFirst_eq {a : ℕ} :
    ∀ {xs : List ℕ}, a ∈ xs →
      xs = beforeFirst a xs ++ a :: afterFirst a xs
  | [], h => by simp at h
  | x :: xs, h => by
      by_cases hxa : x = a
      · subst x
        simp [beforeFirst, afterFirst]
      · have hmem : a ∈ xs := by
          exact Or.resolve_left (List.mem_cons.mp h) (fun hax => hxa (Eq.symm hax))
        have ih := splitAtFirst_eq (a := a) hmem
        simpa [beforeFirst, afterFirst, hxa] using congrArg (fun t => x :: t) ih

theorem not_mem_beforeFirst :
    ∀ (a : ℕ) (xs : List ℕ), a ∉ beforeFirst a xs
  | a, [] => by simp [beforeFirst]
  | a, x :: xs => by
      by_cases hxa : x = a
      · subst x
        simp [beforeFirst]
      · have hax : a ≠ x := fun h => hxa h.symm
        simp [beforeFirst, hxa, hax, not_mem_beforeFirst a xs]

theorem mem_beforeFirst_ne {a y : ℕ} {xs : List ℕ}
    (hy : y ∈ beforeFirst a xs) : y ≠ a := by
  intro h
  subst y
  exact not_mem_beforeFirst a xs hy

theorem yxy_sublist_append_of_mem {x y : ℕ} :
    ∀ {A B : List ℕ}, y ∈ A → y ∈ B →
      List.Sublist [y, x, y] (A ++ x :: B)
  | [], B, hyA, _ => by simp at hyA
  | z :: A, B, hyA, hyB => by
      rcases List.mem_cons.mp hyA with rfl | hyA'
      · have hxy : List.Sublist [x, y] (x :: B) :=
          List.Sublist.cons₂ x ((List.singleton_sublist).2 hyB)
        have hxy' : List.Sublist [x, y] (A ++ x :: B) :=
          hxy.trans (List.sublist_append_right A (x :: B))
        exact List.Sublist.cons₂ y hxy'
      · exact (yxy_sublist_append_of_mem (x := x) (y := y) hyA' hyB).cons z

theorem abab_sublist_of_mem_split {x y : ℕ} {A B : List ℕ}
    (hyA : y ∈ A) (hyB : y ∈ B) :
    List.Sublist [x, y, x, y] (x :: (A ++ x :: B)) := by
  exact List.Sublist.cons₂ x (yxy_sublist_append_of_mem (x := x) hyA hyB)

theorem ababFree_of_sublist {v u : List ℕ}
    (hsub : List.Sublist v u) (hfree : ABABFree u) : ABABFree v := by
  intro hbad
  rcases hbad with ⟨a, b, hne, hv⟩
  exact hfree ⟨a, b, hne, hv.trans hsub⟩

theorem ababaFree_of_sublist {v u : List ℕ}
    (hsub : List.Sublist v u) (hfree : ABABAFree u) : ABABAFree v := by
  intro hbad
  rcases hbad with ⟨a, b, hne, hv⟩
  exact hfree ⟨a, b, hne, hv.trans hsub⟩

theorem sparse_tail {x : ℕ} {xs : List ℕ} (h : Sparse (x :: xs)) :
    Sparse xs := by
  simpa [Sparse] using List.Chain'.tail h

theorem abaFree_tail {x : ℕ} {xs : List ℕ} (h : ABAFree (x :: xs)) :
    ABAFree xs := by
  intro hbad
  rcases hbad with ⟨a, b, hne, hsub⟩
  exact h ⟨a, b, hne, hsub.cons x⟩

theorem ababFree_tail {x : ℕ} {xs : List ℕ} (h : ABABFree (x :: xs)) :
    ABABFree xs := by
  intro hbad
  rcases hbad with ⟨a, b, hne, hsub⟩
  exact h ⟨a, b, hne, hsub.cons x⟩

theorem head_ne_of_sparse_cons_cons {x y : ℕ} {xs : List ℕ}
    (h : Sparse (x :: y :: xs)) : x ≠ y := by
  cases h with
  | cons_cons hxy _ => exact hxy

theorem abaFree_sparse_nodup :
    ∀ u : List ℕ, Sparse u → ABAFree u → u.Nodup
  | [], _, _ => by simp
  | [x], _, _ => by simp
  | x :: y :: ys, hs, hfree => by
      have hxy : x ≠ y := head_ne_of_sparse_cons_cons hs
      have htail_sparse : Sparse (y :: ys) := sparse_tail hs
      have htail_free : ABAFree (y :: ys) := abaFree_tail hfree
      have htail_nodup := abaFree_sparse_nodup (y :: ys) htail_sparse htail_free
      rw [List.nodup_cons]
      refine ⟨?_, htail_nodup⟩
      intro hxmem
      rcases List.mem_cons.mp hxmem with hxy_eq | hxys
      · exact hxy hxy_eq
      · exact hfree ⟨x, y, hxy, aba_sublist_of_mem_tail hxy hxys⟩

theorem length_eq_card_toFinset_of_nodup {u : List ℕ} (h : u.Nodup) :
    u.length = u.toFinset.card := by
  rw [List.card_toFinset, h.dedup]

/-! ## M6: recurrence-shaped bound function and soundness shell -/

def ceilDiv (b m : ℕ) : ℕ :=
  (m + b - 1) / b

theorem ceilDiv_lt_self {b m : ℕ} (hb : 2 ≤ b) (hm : b < m) :
    ceilDiv b m < m := by
  unfold ceilDiv
  rw [Nat.div_lt_iff_lt_mul (by omega)]
  have hsum : m + b ≤ 2 * m := by omega
  have hprod : 2 * m ≤ m * b := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right m hb
  omega

def middleCap : ℕ := 1

def Acoef (b : ℕ) : ℕ → ℕ
  | m =>
      if h : b < 2 ∨ m ≤ b then
        m
      else
        b + 2 + middleCap * Acoef b (ceilDiv b m)
termination_by m => m
decreasing_by
  simp_wf
  have hb : 2 ≤ b := by omega
  have hm : b < m := by omega
  exact ceilDiv_lt_self hb hm

def Bcoef (b : ℕ) : ℕ → ℕ
  | m =>
      if h : b < 2 ∨ m ≤ b then
        m
      else
        ceilDiv b m * b + m + 2 * ceilDiv b m +
          middleCap * Bcoef b (ceilDiv b m)
termination_by m => m
decreasing_by
  simp_wf
  have hb : 2 ≤ b := by omega
  have hm : b < m := by omega
  exact ceilDiv_lt_self hb hm

@[simp] theorem Acoef_le {b m : ℕ} (h : b < 2 ∨ m ≤ b) :
    Acoef b m = m := by
  rw [Acoef]
  simp [h]

theorem Acoef_gt {b m : ℕ} (hb : 2 ≤ b) (hm : b < m) :
    Acoef b m = b + 2 + middleCap * Acoef b (ceilDiv b m) := by
  rw [Acoef]
  simp [show ¬ (b < 2 ∨ m ≤ b) by omega]

@[simp] theorem Bcoef_le {b m : ℕ} (h : b < 2 ∨ m ≤ b) :
    Bcoef b m = m := by
  rw [Bcoef]
  simp [h]

theorem Bcoef_gt {b m : ℕ} (hb : 2 ≤ b) (hm : b < m) :
    Bcoef b m =
      ceilDiv b m * b + m + 2 * ceilDiv b m +
        middleCap * Bcoef b (ceilDiv b m) := by
  rw [Bcoef]
  simp [show ¬ (b < 2 ∨ m ≤ b) by omega]

def affinePsi (b m n : ℕ) : ℕ :=
  Acoef b m * n + Bcoef b m

def Blocking_affine_chunk_assembly : Prop :=
  ∀ (hmk : MiddlesKeyHypothesis) (b m n : ℕ) (_hb : 2 ≤ b) (_hmgt : b < m)
    (bs : List (List ℕ)) (u : List ℕ),
    bs.length ≤ m →
    (∀ block ∈ bs, block.Nodup) →
    flattenBlocks bs = u →
    ABABAFree u →
    u.toFinset.card ≤ n →
    let groups := chunkBlocks b bs
    localLengthTotal groups groups +
      middleSymbolsLengthTotalFrom [] groups +
        (flattenBlockGroups groups).length +
          boundaryLengthTotalFrom groups [] groups ≤ affinePsi b m n

def psiAux : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _b, m, n => m * n
  | fuel + 1, b, m, n =>
      if m ≤ b ∨ b < 2 then
        m * n
      else
        m * n + 8 * (m + n) + 2 * psiAux fuel b (ceilDiv b m) n

def psi (b m n : ℕ) : ℕ :=
  psiAux m b m n

theorem psiAux_ge_blockProduct :
    ∀ fuel b m n : ℕ, m * n ≤ psiAux fuel b m n
  | 0, _b, m, n => by simp [psiAux]
  | fuel + 1, b, m, n => by
      unfold psiAux
      by_cases h : m ≤ b ∨ b < 2
      · simp [h]
      · simp [h]
        omega

theorem psi_ge_blockProduct (b m n : ℕ) :
    m * n ≤ psi b m n := by
  exact psiAux_ge_blockProduct m b m n

theorem mem_flattenBlocks_of_mem {x : ℕ} {b : List ℕ} {bs : List (List ℕ)}
    (hb : b ∈ bs) (hx : x ∈ b) :
    x ∈ flattenBlocks bs := by
  induction bs with
  | nil => simp at hb
  | cons c cs ih =>
      simp [flattenBlocks] at hb ⊢
      rcases hb with rfl | hb
      · exact Or.inl hx
      · exact Or.inr (ih hb)

theorem flattenBlocks_length_le_of_forall_block_length
    (bs : List (List ℕ)) (n : ℕ)
    (h : ∀ b ∈ bs, b.length ≤ n) :
    (flattenBlocks bs).length ≤ bs.length * n := by
  induction bs with
  | nil =>
      simp [flattenBlocks]
  | cons b bs ih =>
      have hb : b.length ≤ n := h b (by simp)
      have htail : ∀ c ∈ bs, c.length ≤ n := by
        intro c hc
        exact h c (by simp [hc])
      have ih' := ih htail
      simp [flattenBlocks]
      calc
        b.length + (flattenBlocks bs).length ≤ n + bs.length * n :=
          Nat.add_le_add hb ih'
        _ = (bs.length + 1) * n := by ring

theorem block_length_le_alphabet_of_mem {u : List ℕ} {bs : List (List ℕ)}
    (hflat : flattenBlocks bs = u) {b : List ℕ} (hb : b ∈ bs)
    (hnodup : b.Nodup) (hcard : u.toFinset.card ≤ n) :
    b.length ≤ n := by
  have hlen : b.length = b.toFinset.card := length_eq_card_toFinset_of_nodup hnodup
  have hsubset : b.toFinset ⊆ u.toFinset := by
    intro x hx
    rw [List.mem_toFinset] at hx ⊢
    rw [← hflat]
    exact mem_flattenBlocks_of_mem hb hx
  exact le_trans (by rw [hlen]; exact Finset.card_le_card hsubset) hcard

theorem length_le_blocks_mul_symbols {m n : ℕ} {u : List ℕ}
    (hblocked : Blocked m u) (hcard : u.toFinset.card ≤ n) :
    u.length ≤ m * n := by
  rcases hblocked with ⟨bs, hbs_len, hnodup, hflat⟩
  have hper : ∀ b ∈ bs, b.length ≤ n := by
    intro b hb
    exact block_length_le_alphabet_of_mem hflat hb (hnodup b hb) hcard
  have hflat_len := flattenBlocks_length_le_of_forall_block_length bs n hper
  have hmul : bs.length * n ≤ m * n := Nat.mul_le_mul_right n hbs_len
  rw [← hflat]
  exact le_trans hflat_len hmul

theorem affine_sound (hmk : MiddlesKeyHypothesis)
    (hblock : Blocking_affine_chunk_assembly) (b : ℕ) (hb : 2 ≤ b) :
    ∀ m, ∀ n u, ABABAFree u → Sparse u → Blocked m u →
      u.toFinset.card ≤ n → u.length ≤ affinePsi b m n := by
  intro m n u hfree _hs hblocked hcard
  by_cases hle : m ≤ b
  · have hlen : u.length ≤ m * n :=
      length_le_blocks_mul_symbols hblocked hcard
    exact le_trans hlen (by
      simp [affinePsi, Acoef_le (Or.inr hle), Bcoef_le (Or.inr hle)])
  · rcases hblocked with ⟨bs, hbs_len, hnodup, hflat⟩
    let groups := chunkBlocks b bs
    have hgroups_flat : flattenBlockGroups groups = bs := by
      exact flattenBlockGroups_chunkBlocks (b := b) (by omega) bs
    have hcount :
        u.length ≤
          localLengthTotal groups groups +
            middleSymbolsLengthTotalFrom [] groups +
              (flattenBlockGroups groups).length +
                boundaryLengthTotalFrom groups [] groups := by
      have hfree_blocks : ABABAFree (flattenBlocks (flattenBlockGroups groups)) := by
        simpa [groups, hgroups_flat, hflat] using hfree
      have hnodup_blocks :
          ∀ block ∈ flattenBlockGroups groups, block.Nodup := by
        intro block hbmem
        exact hnodup block (by simpa [groups, hgroups_flat] using hbmem)
      simpa [groups, hgroups_flat, hflat] using
        oneStep_counting_of_middles_key hmk groups hfree_blocks hnodup_blocks
    exact le_trans hcount
      (hblock hmk b m n hb (by omega) bs u hbs_len hnodup hflat hfree hcard)

/-- Elementary blocked incidence soundness for the current conservative `psi`. -/
theorem psi_sound_incidence (b m n : ℕ) (_hb : 1 ≤ b) :
    DSBound m n (psi b m n) := by
  intro u _hfree _hs hblocked hcard
  exact le_trans (length_le_blocks_mul_symbols hblocked hcard)
    (psi_ge_blockProduct b m n)

/--
M6 public soundness surface.  Once the local `MiddlesKeyHypothesis` is proved,
this theorem is the place where the incidence shell is replaced by the real
Hart--Sharir block recurrence.
-/
theorem psi_sound_of_middles_key (_hmid : MiddlesKeyHypothesis)
    (b m n : ℕ) (hb : 2 ≤ b) :
    DSBound m n (psi b m n) := by
  intro u hfree _hs hblocked hcard
  rcases hblocked with ⟨bs, hbs_len, hnodup, hflat⟩
  let groups := chunkBlocks b bs
  have hgroups_flat : flattenBlockGroups groups = bs := by
    exact flattenBlockGroups_chunkBlocks (b := b) (by omega) bs
  have _hcount :
      u.length ≤
        localLengthTotal groups groups +
          middleSymbolsLengthTotalFrom [] groups +
            (flattenBlockGroups groups).length +
              boundaryLengthTotalFrom groups [] groups := by
    have hfree_blocks : ABABAFree (flattenBlocks (flattenBlockGroups groups)) := by
      simpa [groups, hgroups_flat, hflat] using hfree
    have hnodup_blocks :
        ∀ block ∈ flattenBlockGroups groups, block.Nodup := by
      intro block hb
      exact hnodup block (by simpa [groups, hgroups_flat] using hb)
    simpa [groups, hgroups_flat, hflat] using
      oneStep_counting_of_middles_key _hmid groups hfree_blocks hnodup_blocks
  exact le_trans
    (length_le_blocks_mul_symbols ⟨bs, hbs_len, hnodup, hflat⟩ hcard)
    (psi_ge_blockProduct b m n)

theorem abaFree_sparse_length_le_card (u : List ℕ)
    (hs : Sparse u) (hfree : ABAFree u) :
    u.length ≤ u.toFinset.card := by
  rw [length_eq_card_toFinset_of_nodup (abaFree_sparse_nodup u hs hfree)]

theorem abaFree_sparse_length_le_m (m : ℕ) (u : List ℕ)
    (hcard : u.toFinset.card ≤ m) (hs : Sparse u) (hfree : ABAFree u) :
    u.length ≤ m := by
  exact le_trans (abaFree_sparse_length_le_card u hs hfree) hcard

theorem adjacentPairs_nodup_of_ababFree :
    ∀ u : List ℕ, Sparse u → ABABFree u → (adjacentPairs u).Nodup
  | [], _, _ => by simp [adjacentPairs]
  | [x], _, _ => by simp [adjacentPairs]
  | x :: y :: ys, hs, hfree => by
      have hxy : x ≠ y := head_ne_of_sparse_cons_cons hs
      have htail_sparse : Sparse (y :: ys) := sparse_tail hs
      have htail_free : ABABFree (y :: ys) := ababFree_tail hfree
      have htail_nodup :=
        adjacentPairs_nodup_of_ababFree (y :: ys) htail_sparse htail_free
      simp only [adjacentPairs, List.nodup_cons]
      refine ⟨?_, htail_nodup⟩
      intro hmem
      exact hfree ⟨x, y, hxy, abab_sublist_of_repeated_adjacent_pair hxy hmem⟩

theorem adjacentPairs_length_le_card_sq (u : List ℕ)
    (hnodup : (adjacentPairs u).Nodup) :
    (adjacentPairs u).length ≤ u.toFinset.card * u.toFinset.card := by
  classical
  let ps := adjacentPairs u
  have hlen : ps.length = ps.toFinset.card := by
    rw [List.card_toFinset, hnodup.dedup]
  have hsubset : ps.toFinset ⊆ u.toFinset.product u.toFinset := by
    intro p hp
    rw [List.mem_toFinset] at hp
    have hsupp := mem_adjacentPairs_support hp
    simp [List.mem_toFinset, hsupp.1, hsupp.2]
  have hcard := Finset.card_le_card hsubset
  have hprod : (u.toFinset.product u.toFinset).card
      = u.toFinset.card * u.toFinset.card := by
    simp
  calc
    (adjacentPairs u).length = ps.toFinset.card := hlen
    _ ≤ (u.toFinset.product u.toFinset).card := hcard
    _ = u.toFinset.card * u.toFinset.card := hprod

/-- Sharp order-2 warm-up in a subtraction-free form.  A nonempty sparse
`abab`-free sequence has length at most `2n - 1`. -/
theorem ababFree_sparse_length_add_one_le_two_card :
    ∀ u : List ℕ, u ≠ [] → Sparse u → ABABFree u →
      u.length + 1 ≤ 2 * u.toFinset.card
  | [], hne, _, _ => by contradiction
  | x :: xs, _hne, hs, hfree => by
      by_cases hx : x ∈ xs
      · let A := beforeFirst x xs
        let B := afterFirst x xs
        let rest : List ℕ := x :: B
        have hsplit : xs = A ++ rest := by
          simpa [A, B, rest] using splitAtFirst_eq (a := x) hx
        have hlen_split : xs.length = A.length + rest.length := by
          calc
            xs.length = (A ++ rest).length := congrArg List.length hsplit
            _ = A.length + rest.length := by simp
        have hlen_cons_split : (x :: xs).length = A.length + rest.length + 1 := by
          simp [hlen_split]
        have hA_ne : A ≠ [] := by
          intro hA
          have hxs : xs = rest := by
            simpa [hA] using hsplit
          have hsxx : Sparse (x :: rest) := by
            simpa [hxs] using hs
          exact (head_ne_of_sparse_cons_cons hsxx) rfl
        have hA_len : A.length < (x :: xs).length := by
          rw [hlen_cons_split]
          omega
        have hrest_len : rest.length < (x :: xs).length := by
          rw [hlen_cons_split]
          omega
        have hA_len_le : A.length ≤ xs.length := by
          omega
        have hB_len : B.length < xs.length := by
          have hrest_len_eq : rest.length = B.length + 1 := by
            simp [rest]
          omega
        have hchain_split : Sparse (A ++ rest) := by
          simpa [hsplit] using sparse_tail hs
        have hA_sparse : Sparse A := by
          simpa [Sparse] using
            (List.IsChain.left_of_append
              (R := fun a b : ℕ => a ≠ b)
              (l₁ := A) (l₂ := rest) (by simpa [Sparse] using hchain_split))
        have hrest_sparse : Sparse rest := by
          simpa [Sparse] using
            (List.IsChain.right_of_append
              (R := fun a b : ℕ => a ≠ b)
              (l₁ := A) (l₂ := rest) (by simpa [Sparse] using hchain_split))
        have hA_sub : List.Sublist A (x :: xs) := by
          have hAxs : List.Sublist A xs := by
            simpa [hsplit] using List.sublist_append_left A rest
          exact hAxs.cons x
        have hrest_sub : List.Sublist rest (x :: xs) := by
          have hrestxs : List.Sublist rest xs := by
            simpa [hsplit] using List.sublist_append_right A rest
          exact hrestxs.cons x
        have hA_free : ABABFree A := ababFree_of_sublist hA_sub hfree
        have hrest_free : ABABFree rest := ababFree_of_sublist hrest_sub hfree
        have hno_cross : ∀ ⦃y : ℕ⦄, y ∈ A → y ∉ B := by
          intro y hyA hyB
          have hyne : x ≠ y := by
            exact (mem_beforeFirst_ne (a := x) (xs := xs) (y := y) (by simpa [A] using hyA)).symm
          have hsub : List.Sublist [x, y, x, y] (x :: xs) := by
            have hseq : x :: xs = x :: (A ++ x :: B) := by
              simpa [A, B, rest] using congrArg (fun t => x :: t) hsplit
            rw [hseq]
            exact abab_sublist_of_mem_split (x := x) (y := y) (A := A) (B := B) hyA hyB
          exact hfree ⟨x, y, hyne, hsub⟩
        have hdisj : Disjoint A.toFinset rest.toFinset := by
          rw [Finset.disjoint_left]
          intro y hyA hyrest
          rw [List.mem_toFinset] at hyA hyrest
          rcases List.mem_cons.mp hyrest with hyx | hyB
          · exact (mem_beforeFirst_ne (a := x) (xs := xs) (y := y) (by simpa [A] using hyA)) hyx
          · exact hno_cross hyA (by simpa [B] using hyB)
        have hsubset : A.toFinset ∪ rest.toFinset ⊆ (x :: xs).toFinset := by
          intro y hy
          rw [Finset.mem_union] at hy
          rw [List.mem_toFinset]
          rcases hy with hyA | hyrest
          · rw [List.mem_toFinset] at hyA
            simp [hsplit, hyA]
          · rw [List.mem_toFinset] at hyrest
            simp [hsplit, hyrest]
        have hcardle :
            A.toFinset.card + rest.toFinset.card ≤ (x :: xs).toFinset.card := by
          calc
            A.toFinset.card + rest.toFinset.card =
                (A.toFinset ∪ rest.toFinset).card := by
                  exact (Finset.card_union_of_disjoint hdisj).symm
            _ ≤ (x :: xs).toFinset.card := Finset.card_le_card hsubset
        have ihA :=
          ababFree_sparse_length_add_one_le_two_card A hA_ne hA_sparse hA_free
        have ihRest :=
          ababFree_sparse_length_add_one_le_two_card rest (by simp [rest]) hrest_sparse hrest_free
        have hlen_goal :
            (x :: xs).length + 1 = (A.length + 1) + (rest.length + 1) := by
          simp
          omega
        nlinarith [ihA, ihRest, hcardle]
      · by_cases hxs : xs = []
        · subst xs
          simp
        · have htail :=
            ababFree_sparse_length_add_one_le_two_card xs hxs (sparse_tail hs) (ababFree_tail hfree)
          have hcard : (x :: xs).toFinset.card = xs.toFinset.card + 1 := by
            simp [hx, Nat.add_comm]
          rw [hcard]
          change xs.length + 2 ≤ 2 * (xs.toFinset.card + 1)
          omega
termination_by u => u.length
decreasing_by
  all_goals simp_wf
  · simpa [A] using hA_len_le
  · simpa [B] using hB_len

/-- Linear order-2 warm-up. -/
theorem ababFree_sparse_length_le_linear (m : ℕ) (u : List ℕ)
    (hcard : u.toFinset.card ≤ m) (hs : Sparse u) (hfree : ABABFree u) :
    u.length ≤ 2 * m := by
  by_cases hu : u = []
  · subst u
    simp
  · have hsharp := ababFree_sparse_length_add_one_le_two_card u hu hs hfree
    nlinarith

/-- A simple order-2 warm-up: no repeated ordered adjacent pair.  This gives a
quadratic alphabet-size bound.  The sharper classical `2m-1` estimate is not
used by the later conditional DS3 shell. -/
theorem ababFree_sparse_length_le_quadratic (m : ℕ) (u : List ℕ)
    (hcard : u.toFinset.card ≤ m) (hs : Sparse u) (hfree : ABABFree u) :
    u.length ≤ m * m + 1 := by
  have hpairs_nodup := adjacentPairs_nodup_of_ababFree u hs hfree
  have hpairs := adjacentPairs_length_le_card_sq u hpairs_nodup
  have hlen := adjacentPairs_length_add_one u
  have hsq : u.toFinset.card * u.toFinset.card ≤ m * m :=
    Nat.mul_le_mul hcard hcard
  omega

#print axioms abaFree_sparse_length_le_m
#print axioms ababFree_sparse_length_le_linear
#print axioms ababFree_sparse_length_le_quadratic
#print axioms sparse_blocked_by_length
#print axioms DSBound.mono
#print axioms globalContraction_blocked
#print axioms globalContraction_ababaFree
#print axioms groupLocalSubsequence_blocked
#print axioms globalContraction_card_le
#print axioms flattenBlockGroups_chunkBlocks
#print axioms oneStep_counting_of_middles_key
#print axioms ceilDiv_lt_self
#print axioms Acoef_gt
#print axioms Bcoef_gt
#print axioms affine_sound
#print axioms length_le_blocks_mul_symbols
#print axioms psi_sound_incidence
#print axioms psi_sound_of_middles_key

end CodexDS
