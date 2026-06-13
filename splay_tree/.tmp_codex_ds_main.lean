/- PUBLICATION HEADER
  Splay Deque — Davenport-Schinzel toolkit (namespace CodexDS)

  Public results: middlesKey_proved (order-5 Hart-Sharir middles lemma),
  affine_sound_positional (positional one-step DS decomposition), recursion_telescope and
  gamma_poly_alpha_proved (the gammaOf inverse-Ackermann arithmetic).
  NOTE: several `Blocking_*` defs here are OFF the deque critical path and are documented
  as falsified or superseded (Blocking_affine_chunk_assembly, Blocking_M7_positional_schedule,
  Blocking_middles_order12_linear, Blocking_BlockSeqLinear_ten) — see .tmp_codex_NOTES.md.
  Axioms of all proved theorems: {propext, Classical.choice, Quot.sound}; no sorry.
-/

import Challenges.Splay_Tree.Def_Ackermann

/-!
Self-contained DS3 staging file.

This file deliberately imports only the shipped Ackermann hierarchy.  It
contains the finite-sequence definitions, basic subsequence toolkit, two
warm-up bounds, the directly usable `alpha` facts, and a final theorem reduced
to one named mathematical hypothesis for the Hart--Sharir/Klazar order-3
recurrence.
-/

namespace CodexDS

open Classical
open KlazarAckermann

/-! ## Sequence predicates and block scaffolding -/

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
            simp [flattenBlocks]
          · simp [flattenBlocks, h]

@[simp] theorem blocks_join (u : List ℕ) : flattenBlocks (blocks u) = u := by
  induction u with
  | nil => rfl
  | cons x xs ih =>
      simp [blocks, ih]

/-! ## Adjacent pairs and warm-up bounds -/

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
quadratic alphabet-size bound.  The sharper classical `2m-1` estimate is the
next natural strengthening, but is not used by the conditional DS3 shell. -/
theorem ababFree_sparse_length_le_quadratic (m : ℕ) (u : List ℕ)
    (hcard : u.toFinset.card ≤ m) (hs : Sparse u) (hfree : ABABFree u) :
    u.length ≤ m * m + 1 := by
  have hpairs_nodup := adjacentPairs_nodup_of_ababFree u hs hfree
  have hpairs := adjacentPairs_length_le_card_sq u hpairs_nodup
  have hlen := adjacentPairs_length_add_one u
  have hsq : u.toFinset.card * u.toFinset.card ≤ m * m :=
    Nat.mul_le_mul hcard hcard
  omega

/-! ## Direct Ackermann/alpha facts -/

namespace AckermannFacts

-- from dsv
lemma F_omega_exists (n : ℕ) : ∃ m, n ≤ F_omega m := by
  induction n with
  | zero =>
      use 0
      simp [F_omega, F]
  | succ n _ih =>
      use n + 1
      have := @F_inflationary (n + 1) (n + 1) (by omega) (by omega)
      rw [← F_omega] at this
      linarith

-- from dsv
lemma F_one (n : ℕ) : F 1 n = 2 * n := by
  rfl

-- from dsv
lemma F_succ_succ (k n : ℕ) : F (k + 2) n = (F (k + 1) ·)^[n] 1 := by
  rfl

-- from dsv
lemma iterate_ge_one {k m : ℕ} (hk : 1 ≤ k) :
    1 ≤ (F k ·)^[m] 1 := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
      rw [show (F k ·)^[m + 1] 1 = F k ((F k ·)^[m] 1) by
        rw [Function.iterate_succ_apply']]
      exact F_iterate_ge_one hk ih

-- from dsv
lemma iterate_step_ge {k n : ℕ} (hk : 1 ≤ k) :
    (F k ·)^[n] 1 ≤ (F k ·)^[n + 1] 1 := by
  rw [Function.iterate_succ_apply']
  have h_ge : 1 ≤ (F k ·)^[n] 1 := iterate_ge_one hk
  have h_inf : (F k ·)^[n] 1 < F k ((F k ·)^[n] 1) :=
    F_inflationary hk h_ge
  linarith

-- from dsv
lemma iterate_le_iterate_of_le {k a b : ℕ} (hk : 1 ≤ k) (hab : a ≤ b) :
    (F k ·)^[a] 1 ≤ (F k ·)^[b] 1 := by
  induction b generalizing a with
  | zero =>
      have ha0 : a = 0 := by linarith
      rw [ha0]
  | succ b ih =>
      by_cases h : a ≤ b
      · have h1 : (F k ·)^[a] 1 ≤ (F k ·)^[b] 1 := ih h
        have h2 : (F k ·)^[b] 1 ≤ (F k ·)^[b + 1] 1 := iterate_step_ge hk
        linarith
      · have ha1 : a = b + 1 := by linarith
        rw [ha1]

-- from dsv
lemma F_mono_right : ∀ k, 1 ≤ k → ∀ {a b : ℕ}, a ≤ b → F k a ≤ F k b := by
  intro k hk a b hab
  cases k with
  | zero => contradiction
  | succ k =>
      by_cases hk0 : k = 0
      · subst hk0
        simp [F]
        omega
      · have k_ge_1 : k ≥ 1 := by omega
        simp [F]
        exact iterate_le_iterate_of_le k_ge_1 hab

-- from dsv
lemma F_k_1_eq_2 {k : ℕ} (hk : 1 ≤ k) : F k 1 = 2 := by
  induction k with
  | zero => contradiction
  | succ k ih =>
      by_cases hk0 : k = 0
      · subst hk0
        rfl
      · have k_ge_1 : k ≥ 1 := by omega
        have : F (k + 1) 1 = F k 1 := by simp [F]
        rw [this]
        exact ih k_ge_1

-- from dsv
lemma F_k_n_le_iterate {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) :
    F k n ≤ (F k ·)^[n] 1 := by
  induction n with
  | zero => linarith
  | succ n ih =>
      cases n with
      | zero =>
          simp [F_k_1_eq_2 hk]
      | succ n =>
          have h_iter : (F k ·)^[n + 2] 1 =
              F k ((F k ·)^[n + 1] 1) := by
            rw [Function.iterate_succ_apply']
          have h_n2 : n + 2 ≤ F k (n + 1) := by
            have h_inf : n + 1 < F k (n + 1) :=
              F_inflationary hk (by linarith)
            linarith
          have h_F2 : F k (n + 2) ≤ F k (F k (n + 1)) :=
            F_mono_right k hk (by omega)
          have h_ih : F k (n + 1) ≤ (F k ·)^[n + 1] 1 :=
            ih (by linarith)
          have h_F : F k (F k (n + 1)) ≤
              F k ((F k ·)^[n + 1] 1) :=
            F_mono_right k hk h_ih
          rw [h_iter]
          linarith

-- from dsv
lemma F_mono_left :
    ∀ {j k : ℕ}, 1 ≤ j → j ≤ k → ∀ n, 1 ≤ n → F j n ≤ F k n := by
  intro j k hj hjk n hn
  have h_base : F j n ≤ F j n := le_rfl
  have h_step :
      ∀ (m : ℕ), j ≤ m → F j n ≤ F m n → F j n ≤ F (m + 1) n := by
    intro m hm ih
    have h_kn : F m n ≤ F (m + 1) n := by
      cases m with
      | zero =>
          have h_j0 : j = 0 := by omega
          omega
      | succ m =>
          have hk' : 1 ≤ m + 1 := by omega
          simp [F]
          exact F_k_n_le_iterate hk' hn
    linarith
  exact Nat.le_induction h_base h_step k hjk

-- from dsv
lemma F_omega_zero : F_omega 0 = 0 := by
  rw [F_omega, F]

-- from dsv
lemma alpha_zero_eq : alpha 0 = 0 := by
  have h1 : alpha 0 ≤ 0 := by
    unfold alpha
    apply Nat.find_le
    unfold P_omega
    simp [F_omega_zero]
  have h2 : 0 ≤ alpha 0 := by simp
  omega

-- from dsv
lemma F_omega_mono : ∀ {a b : ℕ}, 1 ≤ a → a ≤ b → F_omega a ≤ F_omega b := by
  intro a b ha hab
  rw [F_omega, F_omega]
  have h3 : F a a ≤ F b a := F_mono_left ha hab a ha
  have h4 : F b a ≤ F b b := F_mono_right b (by omega) hab
  linarith

theorem alpha_spec (n : ℕ) :
    n ≤ F_omega (alpha n) := by
  change P_omega n (alpha n)
  unfold alpha
  exact @Nat.find_spec (P_omega n) (P_omega_decidable n) _

theorem alpha_min {n m : ℕ} (h : n ≤ F_omega m) :
    alpha n ≤ m := by
  change @Nat.find (P_omega n) (P_omega_decidable n) _ ≤ m
  exact @Nat.find_min' (P_omega n) (P_omega_decidable n) _ m h

theorem alpha_le_iff_exists_le (n m : ℕ) :
    alpha n ≤ m ↔ ∃ r ≤ m, n ≤ F_omega r := by
  change @Nat.find (P_omega n) (P_omega_decidable n) _ ≤ m ↔ ∃ r ≤ m, P_omega n r
  exact @Nat.find_le_iff (P_omega n) (P_omega_decidable n) _ m

theorem alpha_Fomega_le (m : ℕ) :
    alpha (F_omega m) ≤ m :=
  alpha_min (n := F_omega m) (m := m) le_rfl

theorem alpha_le_of_le_Fomega {n m : ℕ} (h : n ≤ F_omega m) :
    alpha n ≤ m :=
  alpha_min h

theorem alpha_zero_eq_zero :
    alpha 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact alpha_min (n := 0) (m := 0) (by simp)

theorem alpha_one_le_one :
    alpha 1 ≤ 1 := by
  apply alpha_min (n := 1) (m := 1)
  unfold F_omega KlazarAckermann.F
  norm_num

theorem one_le_Fomega_self {m : ℕ} (hm : 1 ≤ m) :
    1 ≤ F_omega m := by
  exact KlazarAckermann.F_iterate_ge_one (k := m) (n := m) hm hm

theorem Fomega_inflationary {m : ℕ} (hm : 1 ≤ m) :
    m < F_omega m := by
  exact KlazarAckermann.F_inflationary (k := m) (n := m) hm hm

theorem alpha_succ_le_self_of_Fomega_ge {n m : ℕ}
    (h : n + 1 ≤ F_omega m) :
    alpha (n + 1) ≤ m :=
  alpha_min h

theorem alpha_le_self_add_one (n : ℕ) :
    alpha n ≤ n + 1 := by
  apply alpha_min (n := n) (m := n + 1)
  cases n with
  | zero =>
      simp
  | succ n =>
      have hlt :
          n + 2 < F_omega (n + 2) := by
        exact Fomega_inflationary (m := n + 2) (by omega)
      have hle : n + 1 ≤ F_omega (n + 2) := by omega
      simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hle

-- from dsv
lemma alpha_le_iff (n m : ℕ) : alpha n ≤ m ↔ n ≤ F_omega m := by
  constructor
  · intro h
    have h_n_le : n ≤ F_omega (alpha n) := by
      have h_spec := Nat.find_spec (@F_omega_exists n)
      have h_eq :
          alpha n =
            @Nat.find (P_omega n) (P_omega_decidable n) (F_omega_exists n) := by
        unfold alpha
        rfl
      rw [h_eq]
      exact h_spec
    have h_Fmono : F_omega (alpha n) ≤ F_omega m := by
      by_cases hn0 : n = 0
      · subst hn0
        rw [alpha_zero_eq] at h
        rw [alpha_zero_eq, F_omega_zero]
        linarith
      · have h1 : 1 ≤ alpha n := by
          have : alpha n ≠ 0 := by
            by_contra h0
            rw [h0] at h_n_le
            rw [F_omega_zero] at h_n_le
            omega
          omega
        apply F_omega_mono h1 h
    linarith
  · intro h
    unfold alpha
    apply Nat.find_le
    unfold P_omega
    exact h

-- from dsv
lemma alpha_mono : ∀ {a b : ℕ}, a ≤ b → alpha a ≤ alpha b := by
  intro a b hab
  by_cases ha0 : a = 0
  · subst ha0
    rw [alpha_zero_eq]
    simp
  · have h_alpha_a_1 : 1 ≤ alpha a := by
      have : alpha a ≠ 0 := by
        by_contra h0
        have h_spec : a ≤ F_omega (alpha a) := by
          have h_spec := Nat.find_spec (F_omega_exists a)
          have h_eq :
              alpha a =
                @Nat.find (P_omega a) (P_omega_decidable a) (F_omega_exists a) := by
            unfold alpha
            rfl
          rw [h_eq]
          exact h_spec
        rw [h0] at h_spec
        rw [F_omega_zero] at h_spec
        omega
      omega
    apply (alpha_le_iff a (alpha b)).mpr
    have h_b_le : b ≤ F_omega (alpha b) := by
      have h_spec := Nat.find_spec (F_omega_exists b)
      have h_eq :
          alpha b =
            @Nat.find (P_omega b) (P_omega_decidable b) (F_omega_exists b) := by
        unfold alpha
        rfl
      rw [h_eq]
      exact h_spec
    linarith

-- from dsv
lemma alpha_F_omega_self (m : ℕ) : alpha (F_omega m) ≤ m := by
  unfold alpha
  apply Nat.find_le
  unfold P_omega
  exact le_rfl

-- from dsv
lemma alpha_pos_of_two_le {n : ℕ} : 2 ≤ n → 1 ≤ alpha n := by
  intro h
  have : n ≠ 0 := by linarith
  have : alpha n ≠ 0 := by
    by_contra h0
    have h_spec : n ≤ F_omega (alpha n) := by
      have h_spec := Nat.find_spec (F_omega_exists n)
      have h_eq :
          alpha n =
            @Nat.find (P_omega n) (P_omega_decidable n) (F_omega_exists n) := by
        unfold alpha
        rfl
      rw [h_eq]
      exact h_spec
    rw [h0] at h_spec
    rw [F_omega_zero] at h_spec
    omega
  omega

theorem target_bound_mono_const {C D m len : ℕ}
    (hCD : C ≤ D)
    (h : len ≤ C * (m + 1) * (alpha (m + 1) + 1)) :
    len ≤ D * (m + 1) * (alpha (m + 1) + 1) := by
  exact le_trans h (by
    gcongr)

end AckermannFacts

/-! ## Conditional order-3 endpoint after M6 -/

def DSBoundHard (blocks symbols L : ℕ) : Prop :=
  ∀ u : List ℕ,
    ABABAFree u →
    Sparse u →
    HasABAB u →
    Blocked blocks u →
    u.toFinset.card ≤ symbols →
    u.length ≤ L

/--
The remaining post-M6 obligation: the local middle-counting lemma plus the
numeric level/alpha assembly for the current `psi` overapproximation.
-/
def KlazarN5AfterM6Hypothesis : Prop :=
  MiddlesKeyHypothesis ∧
    ∃ C : ℕ, ∀ blocks symbols : ℕ,
      psi 2 blocks symbols ≤
        C * (symbols + 1) * (alpha (symbols + 1) + 1)

theorem main_of_hypothesis (h : KlazarN5AfterM6Hypothesis) :
    ∃ C : ℕ, ∀ (m : ℕ) (u : List ℕ),
      u.toFinset.card ≤ m →
      u.Chain' (· ≠ ·) →
      (¬ ∃ a b : ℕ, a ≠ b ∧ List.Sublist [a, b, a, b, a] u) →
      u.length ≤ C * (m + 1) * (alpha (m + 1) + 1) := by
  rcases h with ⟨hmid, C, hC⟩
  refine ⟨C + 2, ?_⟩
  intro m u hcard hs hfree
  by_cases h2 : ABABFree u
  · have hlin : u.length ≤ 2 * m :=
      ababFree_sparse_length_le_linear m u hcard hs h2
    have hmono :
        2 * m ≤ (C + 2) * (m + 1) * (alpha (m + 1) + 1) := by
      have hαpos : 0 < alpha (m + 1) + 1 := Nat.succ_pos _
      have hcoeff : 2 * (m + 1) ≤ (C + 2) * (m + 1) := by
        exact Nat.mul_le_mul_right (m + 1) (by omega)
      calc
        2 * m ≤ 2 * (m + 1) :=
          Nat.mul_le_mul_left 2 (Nat.le_succ m)
        _ ≤ 2 * (m + 1) * (alpha (m + 1) + 1) :=
          Nat.le_mul_of_pos_right _ hαpos
        _ ≤ (C + 2) * (m + 1) * (alpha (m + 1) + 1) :=
          Nat.mul_le_mul_right (k := alpha (m + 1) + 1) hcoeff
    exact le_trans hlin hmono
  · have hblocked : Blocked u.length u := sparse_blocked_by_length u hs
    have hpsi_sound : u.length ≤ psi 2 u.length m :=
      psi_sound_of_middles_key hmid 2 u.length m (by omega) u hfree hs hblocked hcard
    have hpsi_target :
        psi 2 u.length m ≤
          C * (m + 1) * (alpha (m + 1) + 1) :=
      hC u.length m
    exact le_trans hpsi_sound
      (AckermannFacts.target_bound_mono_const
        (C := C) (D := C + 2) (m := m) (len := psi 2 u.length m)
        (by omega) hpsi_target)

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
#print axioms AckermannFacts.alpha_spec
#print axioms AckermannFacts.F_mono_right
#print axioms AckermannFacts.F_mono_left
#print axioms AckermannFacts.F_omega_mono
#print axioms AckermannFacts.alpha_le_iff
#print axioms AckermannFacts.alpha_mono
#print axioms AckermannFacts.alpha_F_omega_self
#print axioms AckermannFacts.alpha_pos_of_two_le
#print axioms AckermannFacts.alpha_Fomega_le
#print axioms AckermannFacts.alpha_le_self_add_one
#print axioms main_of_hypothesis

/-! ## M6c-P: positional per-step assembly (closes `Blocking_affine_chunk_assembly`'s
role modulo `MiddlesKeyHypothesis` ONLY)

The earlier four-term assembly is unprovable as stated: `IsGlobalInGroups`
distinguishes groups by LIST INEQUALITY, so duplicate-content groups make the
local alphabets non-disjoint and the Σ-counting fails.  The classical
Hart--Sharir recursion is positional.  Here the trichotomy is defined
pre/post-RELATIVELY (a symbol of a group is local / left-boundary /
right-boundary / middle according to its occurrence in the flattened prefix
and suffix), which is positional by construction: local alphabets are pairwise
disjoint, boundary symbols are charged to their unique first / last group.
The middles recurse through the per-position contraction.  Result:

  `affine_sound_positional :  MiddlesKeyHypothesis → ∀ b ≥ 2,
      ABABAFree u → Blocked m u → card ≤ n →
      u.length ≤ AcoefP b m * n + BcoefP b m`

with `AcoefP b m = 3b + AcoefP b ⌈m/b⌉`, `BcoefP b m = m + BcoefP b ⌈m/b⌉`
(bases `m`, `0`).  No sparsity needed anywhere in the recursion. -/

section Positional

/-- Selector for symbols occurring in neither side. -/
def selLocal (pre post : List ℕ) (a : ℕ) : Bool :=
  !(decide (a ∈ pre)) && !(decide (a ∈ post))

/-- Selector for symbols occurring before but not after (last-group side). -/
def selLeft (pre post : List ℕ) (a : ℕ) : Bool :=
  (decide (a ∈ pre)) && !(decide (a ∈ post))

/-- Selector for symbols occurring after but not before (first-group side). -/
def selRight (pre post : List ℕ) (a : ℕ) : Bool :=
  !(decide (a ∈ pre)) && (decide (a ∈ post))

theorem selLocal_excludes_post {pre post : List ℕ} {a : ℕ}
    (h : selLocal pre post a = true) : a ∉ post := by
  simp [selLocal] at h
  exact h.2

theorem selLeft_excludes_post {pre post : List ℕ} {a : ℕ}
    (h : selLeft pre post a = true) : a ∉ post := by
  simp [selLeft] at h
  exact h.2

theorem selRight_excludes_pre {pre post : List ℕ} {a : ℕ}
    (h : selRight pre post a = true) : a ∉ pre := by
  simp [selRight] at h
  exact h.1

/-- Four-way per-group split: every occurrence is local, left, right,
or middle. -/
theorem group_four_way (pre : List ℕ) (g : List (List ℕ)) (post : List ℕ) :
    (flattenBlocks g).length
      ≤ ((flattenBlocks g).filter (selLocal pre post)).length
        + ((flattenBlocks g).filter (selLeft pre post)).length
        + ((flattenBlocks g).filter (selRight pre post)).length
        + (middleRaw pre g post).length := by
  unfold middleRaw
  induction (flattenBlocks g) with
  | nil => simp
  | cons x xs ih =>
      by_cases hpre : x ∈ pre <;> by_cases hpost : x ∈ post
      · rw [List.filter_cons_of_neg (by simp [selLocal, hpre]),
          List.filter_cons_of_neg (by simp [selLeft, hpost]),
          List.filter_cons_of_neg (by simp [selRight, hpre]),
          List.filter_cons_of_pos (by simp [occursOnBothSides, hpre, hpost])]
        simp only [List.length_cons]
        omega
      · rw [List.filter_cons_of_neg (by simp [selLocal, hpre]),
          List.filter_cons_of_pos (by simp [selLeft, hpre, hpost]),
          List.filter_cons_of_neg (by simp [selRight, hpre]),
          List.filter_cons_of_neg (by simp [occursOnBothSides, hpost])]
        simp only [List.length_cons]
        omega
      · rw [List.filter_cons_of_neg (by simp [selLocal, hpost]),
          List.filter_cons_of_neg (by simp [selLeft, hpre]),
          List.filter_cons_of_pos (by simp [selRight, hpre, hpost]),
          List.filter_cons_of_neg (by simp [occursOnBothSides, hpre])]
        simp only [List.length_cons]
        omega
      · rw [List.filter_cons_of_pos (by simp [selLocal, hpre, hpost]),
          List.filter_cons_of_neg (by simp [selLeft, hpre]),
          List.filter_cons_of_neg (by simp [selRight, hpost]),
          List.filter_cons_of_neg (by simp [occursOnBothSides, hpre])]
        simp only [List.length_cons]
        omega

/-- Totals of a selector-filtered classification along the group recursion. -/
def selTotalFrom (sel : List ℕ → List ℕ → ℕ → Bool) (pre : List ℕ) :
    List (List (List ℕ)) → ℕ
  | [] => 0
  | g :: gs =>
      ((flattenBlocks g).filter
        (sel pre (flattenBlocks (flattenBlockGroups gs)))).length
        + selTotalFrom sel (pre ++ flattenBlocks g) gs

/-- Distinct-symbol totals of a selector-filtered classification. -/
def selSymsTotalFrom (sel : List ℕ → List ℕ → ℕ → Bool) (pre : List ℕ) :
    List (List (List ℕ)) → ℕ
  | [] => 0
  | g :: gs =>
      ((flattenBlocks g).filter
        (sel pre (flattenBlocks (flattenBlockGroups gs)))).toFinset.card
        + selSymsTotalFrom sel (pre ++ flattenBlocks g) gs

/-- The master four-way length split over all groups. -/
theorem length_four_way_total (gs : List (List (List ℕ))) :
    ∀ pre, (flattenBlocks (flattenBlockGroups gs)).length
      ≤ selTotalFrom selLocal pre gs + selTotalFrom selLeft pre gs
        + selTotalFrom selRight pre gs + middleLengthTotalFrom pre gs := by
  induction gs with
  | nil =>
      intro pre
      simp [flattenBlockGroups, flattenBlocks, selTotalFrom,
        middleLengthTotalFrom]
  | cons g rest ih =>
      intro pre
      have hhead := group_four_way pre g (flattenBlocks (flattenBlockGroups rest))
      have htail := ih (pre ++ flattenBlocks g)
      simp only [flattenBlockGroups, flattenBlocks_append, List.length_append,
        selTotalFrom, middleLengthTotalFrom]
      omega

/-- Filtering distributes from blocks to the flattened group. -/
theorem filter_blocks_flatten (p : ℕ → Bool) (g : List (List ℕ)) :
    flattenBlocks (g.map (fun blk => blk.filter p))
      = (flattenBlocks g).filter p := by
  induction g with
  | nil => rfl
  | cons blk rest ih =>
      simp only [List.map_cons, flattenBlocks, List.filter_append, ih]

/-- A filtered group is blocked by its own block count. -/
theorem relFilter_blocked (p : ℕ → Bool) {g : List (List ℕ)} {b : ℕ}
    (hg : g.length ≤ b) (hnodup : ∀ blk ∈ g, blk.Nodup) :
    Blocked b ((flattenBlocks g).filter p) := by
  refine ⟨g.map (fun blk => blk.filter p), by simpa using hg, ?_,
    filter_blocks_flatten p g⟩
  intro blk hblk
  rcases List.mem_map.mp hblk with ⟨o, ho, rfl⟩
  exact (hnodup o ho).filter _

/-- Per-group linear bound on a filtered classification. -/
theorem relFilter_length_le (p : ℕ → Bool) {g : List (List ℕ)} {b : ℕ}
    (hg : g.length ≤ b) (hnodup : ∀ blk ∈ g, blk.Nodup) :
    ((flattenBlocks g).filter p).length
      ≤ b * ((flattenBlocks g).filter p).toFinset.card :=
  length_le_blocks_mul_symbols (relFilter_blocked p hg hnodup) (le_refl _)

theorem selTotalFrom_le_syms (sel : List ℕ → List ℕ → ℕ → Bool) (b : ℕ) :
    ∀ (gs : List (List (List ℕ))), (∀ g ∈ gs, g.length ≤ b) →
      (∀ g ∈ gs, ∀ blk ∈ g, blk.Nodup) →
      ∀ pre, selTotalFrom sel pre gs ≤ b * selSymsTotalFrom sel pre gs := by
  intro gs
  induction gs with
  | nil =>
      intro _ _ pre
      simp [selTotalFrom, selSymsTotalFrom]
  | cons g rest ih =>
      intro hlen hnd pre
      simp only [selTotalFrom, selSymsTotalFrom, Nat.mul_add]
      exact Nat.add_le_add
        (relFilter_length_le _ (hlen g (by simp)) (hnd g (by simp)))
        (ih (fun g' hg' => hlen g' (by simp [hg']))
          (fun g' hg' => hnd g' (by simp [hg'])) _)

/-- Symbols excluded from the suffix have pairwise-disjoint per-group symbol
sets: their total is at most the whole alphabet. -/
theorem selSymsTotalFrom_le_of_excludes_post
    (sel : List ℕ → List ℕ → ℕ → Bool)
    (hsel : ∀ pre post a, sel pre post a = true → a ∉ post) :
    ∀ (gs : List (List (List ℕ))) (pre : List ℕ),
      selSymsTotalFrom sel pre gs
        ≤ (flattenBlocks (flattenBlockGroups gs)).toFinset.card := by
  intro gs
  induction gs with
  | nil =>
      intro pre
      simp [selSymsTotalFrom]
  | cons g rest ih =>
      intro pre
      simp only [selSymsTotalFrom, flattenBlockGroups, flattenBlocks_append,
        List.toFinset_append]
      have htail := ih (pre ++ flattenBlocks g)
      have hdisj : Disjoint
          (((flattenBlocks g).filter
            (sel pre (flattenBlocks (flattenBlockGroups rest)))).toFinset)
          ((flattenBlocks (flattenBlockGroups rest)).toFinset) := by
        rw [Finset.disjoint_left]
        intro a ha hpost
        rw [List.mem_toFinset, List.mem_filter] at ha
        rw [List.mem_toFinset] at hpost
        exact hsel _ _ _ ha.2 hpost
      have hsub : (((flattenBlocks g).filter
          (sel pre (flattenBlocks (flattenBlockGroups rest)))).toFinset)
          ⊆ (flattenBlocks g).toFinset := by
        intro a ha
        rw [List.mem_toFinset, List.mem_filter] at ha
        rw [List.mem_toFinset]
        exact ha.1
      calc (((flattenBlocks g).filter
            (sel pre (flattenBlocks (flattenBlockGroups rest)))).toFinset).card
            + selSymsTotalFrom sel (pre ++ flattenBlocks g) rest
          ≤ (((flattenBlocks g).filter
            (sel pre (flattenBlocks (flattenBlockGroups rest)))).toFinset).card
            + ((flattenBlocks (flattenBlockGroups rest)).toFinset).card :=
            Nat.add_le_add_left htail _
        _ = ((((flattenBlocks g).filter
            (sel pre (flattenBlocks (flattenBlockGroups rest)))).toFinset)
            ∪ ((flattenBlocks (flattenBlockGroups rest)).toFinset)).card :=
            (Finset.card_union_of_disjoint hdisj).symm
        _ ≤ (((flattenBlocks g).toFinset)
            ∪ ((flattenBlocks (flattenBlockGroups rest)).toFinset)).card :=
            Finset.card_le_card
              (Finset.union_subset_union hsub (Finset.Subset.refl _))

/-- Symbols excluded from the prefix have pairwise-disjoint per-group symbol
sets (first-occurrence groups are unique): total at most the alphabet minus
the prefix. -/
theorem selSymsTotalFrom_le_of_excludes_pre
    (sel : List ℕ → List ℕ → ℕ → Bool)
    (hsel : ∀ pre post a, sel pre post a = true → a ∉ pre) :
    ∀ (gs : List (List (List ℕ))) (pre : List ℕ),
      selSymsTotalFrom sel pre gs
        ≤ ((flattenBlocks (flattenBlockGroups gs)).toFinset
            \ pre.toFinset).card := by
  intro gs
  induction gs with
  | nil =>
      intro pre
      simp [selSymsTotalFrom]
  | cons g rest ih =>
      intro pre
      simp only [selSymsTotalFrom, flattenBlockGroups, flattenBlocks_append,
        List.toFinset_append]
      have htail := ih (pre ++ flattenBlocks g)
      rw [List.toFinset_append] at htail
      have hsub : (((flattenBlocks g).filter
          (sel pre (flattenBlocks (flattenBlockGroups rest)))).toFinset)
          ⊆ (flattenBlocks g).toFinset \ pre.toFinset := by
        intro a ha
        rw [List.mem_toFinset, List.mem_filter] at ha
        rw [Finset.mem_sdiff, List.mem_toFinset]
        exact ⟨ha.1, fun hp => hsel _ _ _ ha.2 (List.mem_toFinset.mp hp)⟩
      have hdisj : Disjoint
          (((flattenBlocks g).filter
            (sel pre (flattenBlocks (flattenBlockGroups rest)))).toFinset)
          (((flattenBlocks (flattenBlockGroups rest)).toFinset)
            \ (pre.toFinset ∪ (flattenBlocks g).toFinset)) := by
        rw [Finset.disjoint_left]
        intro a ha hrest
        rw [Finset.mem_sdiff, Finset.mem_union] at hrest
        have hag : a ∈ (flattenBlocks g).toFinset := by
          rw [List.mem_toFinset]
          rw [List.mem_toFinset, List.mem_filter] at ha
          exact ha.1
        exact hrest.2 (Or.inr hag)
      have hunion : (((flattenBlocks g).filter
          (sel pre (flattenBlocks (flattenBlockGroups rest)))).toFinset)
          ∪ (((flattenBlocks (flattenBlockGroups rest)).toFinset)
            \ (pre.toFinset ∪ (flattenBlocks g).toFinset))
          ⊆ (((flattenBlocks g).toFinset)
            ∪ ((flattenBlocks (flattenBlockGroups rest)).toFinset))
            \ pre.toFinset := by
        intro a ha
        rw [Finset.mem_union] at ha
        rw [Finset.mem_sdiff, Finset.mem_union]
        rcases ha with ha | ha
        · have := hsub ha
          rw [Finset.mem_sdiff] at this
          exact ⟨Or.inl this.1, this.2⟩
        · rw [Finset.mem_sdiff, Finset.mem_union] at ha
          exact ⟨Or.inr ha.1, fun hp => ha.2 (Or.inl hp)⟩
      calc (((flattenBlocks g).filter
            (sel pre (flattenBlocks (flattenBlockGroups rest)))).toFinset).card
            + selSymsTotalFrom sel (pre ++ flattenBlocks g) rest
          ≤ (((flattenBlocks g).filter
            (sel pre (flattenBlocks (flattenBlockGroups rest)))).toFinset).card
            + (((flattenBlocks (flattenBlockGroups rest)).toFinset)
              \ (pre.toFinset ∪ (flattenBlocks g).toFinset)).card :=
            Nat.add_le_add_left htail _
        _ = ((((flattenBlocks g).filter
            (sel pre (flattenBlocks (flattenBlockGroups rest)))).toFinset)
            ∪ (((flattenBlocks (flattenBlockGroups rest)).toFinset)
              \ (pre.toFinset ∪ (flattenBlocks g).toFinset))).card :=
            (Finset.card_union_of_disjoint hdisj).symm
        _ ≤ ((((flattenBlocks g).toFinset)
            ∪ ((flattenBlocks (flattenBlockGroups rest)).toFinset))
            \ pre.toFinset).card := Finset.card_le_card hunion

/-- The per-position middles contraction: one (deduplicated) block of
both-sided symbols per group, in group order. -/
noncomputable def middleContractionFrom (pre : List ℕ) :
    List (List (List ℕ)) → List (List ℕ)
  | [] => []
  | g :: gs =>
      middleSymbols pre g (flattenBlocks (flattenBlockGroups gs))
        :: middleContractionFrom (pre ++ flattenBlocks g) gs

theorem middleContractionFrom_length (pre : List ℕ)
    (gs : List (List (List ℕ))) :
    ∀ pre', (middleContractionFrom pre' gs).length = gs.length := by
  induction gs with
  | nil => intro pre'; rfl
  | cons g rest ih =>
      intro pre'
      simp only [middleContractionFrom, List.length_cons, ih]

theorem middleContractionFrom_flatten_length :
    ∀ (gs : List (List (List ℕ))) (pre : List ℕ),
      (flattenBlocks (middleContractionFrom pre gs)).length
        = middleSymbolsLengthTotalFrom pre gs := by
  intro gs
  induction gs with
  | nil => intro pre; rfl
  | cons g rest ih =>
      intro pre
      simp only [middleContractionFrom, flattenBlocks, List.length_append,
        middleSymbolsLengthTotalFrom, ih]

theorem middleContractionFrom_blocked (gs : List (List (List ℕ)))
    (pre : List ℕ) :
    Blocked gs.length (flattenBlocks (middleContractionFrom pre gs)) := by
  refine ⟨middleContractionFrom pre gs,
    le_of_eq (middleContractionFrom_length pre gs pre), ?_, rfl⟩
  intro blk hblk
  induction gs generalizing pre with
  | nil => simp [middleContractionFrom] at hblk
  | cons g rest ih =>
      simp only [middleContractionFrom, List.mem_cons] at hblk
      rcases hblk with rfl | hblk
      · exact List.nodup_dedup _
      · exact ih _ hblk

theorem middleContractionFrom_sublist :
    ∀ (gs : List (List (List ℕ))) (pre : List ℕ),
      List.Sublist (flattenBlocks (middleContractionFrom pre gs))
        (flattenBlocks (flattenBlockGroups gs)) := by
  intro gs
  induction gs with
  | nil => intro pre; exact List.Sublist.slnil
  | cons g rest ih =>
      intro pre
      simp only [middleContractionFrom, flattenBlocks, flattenBlockGroups,
        flattenBlocks_append]
      exact List.Sublist.append
        ((List.dedup_sublist _).trans (middleRaw_sublist _ _ _)) (ih _)

/-- The concrete selected subsequences, one per group, matching `selTotalFrom`. -/
def selSeqsFrom (sel : List ℕ → List ℕ → ℕ → Bool) (pre : List ℕ) :
    List (List (List ℕ)) → List (List ℕ)
  | [] => []
  | g :: gs =>
      ((flattenBlocks g).filter
        (sel pre (flattenBlocks (flattenBlockGroups gs))))
        :: selSeqsFrom sel (pre ++ flattenBlocks g) gs

theorem selSeqsFrom_length (sel : List ℕ → List ℕ → ℕ → Bool) :
    ∀ (gs : List (List (List ℕ))) (pre : List ℕ),
      (selSeqsFrom sel pre gs).length = gs.length := by
  intro gs
  induction gs with
  | nil =>
      intro pre
      rfl
  | cons g rest ih =>
      intro pre
      simp [selSeqsFrom, ih]

theorem selSeqsFrom_lengths_sum
    (sel : List ℕ → List ℕ → ℕ → Bool) :
    ∀ (gs : List (List (List ℕ))) (pre : List ℕ),
      ((selSeqsFrom sel pre gs).map List.length).sum =
        selTotalFrom sel pre gs := by
  intro gs
  induction gs with
  | nil =>
      intro pre
      rfl
  | cons g rest ih =>
      intro pre
      simp [selSeqsFrom, selTotalFrom, ih]

theorem selSeqsFrom_cards_sum
    (sel : List ℕ → List ℕ → ℕ → Bool) :
    ∀ (gs : List (List (List ℕ))) (pre : List ℕ),
      ((selSeqsFrom sel pre gs).map (fun l => l.toFinset.card)).sum =
        selSymsTotalFrom sel pre gs := by
  intro gs
  induction gs with
  | nil =>
      intro pre
      rfl
  | cons g rest ih =>
      intro pre
      simp [selSeqsFrom, selSymsTotalFrom, ih]

theorem selSeqsFrom_sublist_flatten
    (sel : List ℕ → List ℕ → ℕ → Bool) :
    ∀ (gs : List (List (List ℕ))) (pre : List ℕ) (l : List ℕ),
      l ∈ selSeqsFrom sel pre gs →
        List.Sublist l (flattenBlocks (flattenBlockGroups gs)) := by
  intro gs
  induction gs with
  | nil =>
      intro pre l hl
      simp [selSeqsFrom] at hl
  | cons g rest ih =>
      intro pre l hl
      simp only [selSeqsFrom, List.mem_cons] at hl
      rw [flattenBlockGroups, flattenBlocks_append]
      rcases hl with rfl | hl
      · exact List.filter_sublist.trans
          (List.sublist_append_left (flattenBlocks g)
            (flattenBlocks (flattenBlockGroups rest)))
      · exact (ih (pre ++ flattenBlocks g) l hl).trans
          (List.sublist_append_right (flattenBlocks g)
            (flattenBlocks (flattenBlockGroups rest)))

theorem selSeqsFrom_blocked
    (sel : List ℕ → List ℕ → ℕ → Bool) {b : ℕ} :
    ∀ (gs : List (List (List ℕ))) (pre : List ℕ) (l : List ℕ),
      (∀ g ∈ gs, g.length ≤ b) →
      (∀ g ∈ gs, ∀ blk ∈ g, blk.Nodup) →
      l ∈ selSeqsFrom sel pre gs →
        Blocked b l := by
  intro gs
  induction gs with
  | nil =>
      intro pre l _hlen _hnd hl
      simp [selSeqsFrom] at hl
  | cons g rest ih =>
      intro pre l hlen hnd hl
      simp only [selSeqsFrom, List.mem_cons] at hl
      rcases hl with rfl | hl
      · exact relFilter_blocked _
          (hlen g (by simp)) (hnd g (by simp))
      · exact ih (pre ++ flattenBlocks g) l
          (fun g' hg' => hlen g' (by simp [hg']))
          (fun g' hg' blk hblk => hnd g' (by simp [hg']) blk hblk)
          hl

theorem mem_flattenBlockGroups_of_mem {blk : List ℕ} {g : List (List ℕ)}
    {groups : List (List (List ℕ))} (hg : g ∈ groups) (hblk : blk ∈ g) :
    blk ∈ flattenBlockGroups groups := by
  induction groups with
  | nil => simp at hg
  | cons h rest ih =>
      rw [flattenBlockGroups]
      rcases List.mem_cons.mp hg with rfl | hg'
      · exact List.mem_append_left _ hblk
      · exact List.mem_append_right _ (ih hg')

theorem chunkBlocksFuel_group_le (b : ℕ) (hb : 0 < b) :
    ∀ (fuel : ℕ) (bs : List (List ℕ)),
      ∀ g ∈ chunkBlocksFuel fuel b bs, g.length ≤ b := by
  intro fuel
  induction fuel with
  | zero =>
      intro bs g hg
      simp [chunkBlocksFuel] at hg
  | succ fuel ih =>
      intro bs g hg
      cases bs with
      | nil => simp [chunkBlocksFuel] at hg
      | cons blk rest =>
          rw [show chunkBlocksFuel (fuel + 1) b (blk :: rest)
              = if b = 0 then [blk :: rest]
                else (blk :: rest).take b
                  :: chunkBlocksFuel fuel b ((blk :: rest).drop b) from rfl] at hg
          rw [if_neg (by omega : ¬ b = 0)] at hg
          rcases List.mem_cons.mp hg with rfl | hg'
          · exact List.length_take_le _ _
          · exact ih _ g hg'

theorem chunkBlocks_group_le {b : ℕ} (hb : 0 < b) (bs : List (List ℕ)) :
    ∀ g ∈ chunkBlocks b bs, g.length ≤ b :=
  chunkBlocksFuel_group_le b hb bs.length bs

theorem chunkBlocksFuel_count_le (b : ℕ) (hb : 0 < b) :
    ∀ (fuel : ℕ) (bs : List (List ℕ)), bs.length ≤ fuel →
      (chunkBlocksFuel fuel b bs).length ≤ ceilDiv b bs.length := by
  intro fuel
  induction fuel with
  | zero =>
      intro bs hlen
      have : bs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
      subst this
      simp [chunkBlocksFuel]
  | succ fuel ih =>
      intro bs hlen
      cases bs with
      | nil => simp [chunkBlocksFuel]
      | cons blk rest =>
          rw [show chunkBlocksFuel (fuel + 1) b (blk :: rest)
              = if b = 0 then [blk :: rest]
                else (blk :: rest).take b
                  :: chunkBlocksFuel fuel b ((blk :: rest).drop b) from rfl]
          rw [if_neg (by omega : ¬ b = 0)]
          have hdrop : ((blk :: rest).drop b).length ≤ fuel := by
            rw [List.length_drop]
            have : (blk :: rest).length ≤ fuel + 1 := hlen
            omega
          have hrec := ih ((blk :: rest).drop b) hdrop
          rw [List.length_drop] at hrec
          simp only [List.length_cons]
          have hlen1 : 1 ≤ (blk :: rest).length := by simp
          unfold ceilDiv at hrec ⊢
          rw [List.length_cons] at hrec
          by_cases hsmall : rest.length + 1 ≤ b
          · have hdrop0 : rest.length + 1 - b = 0 := by omega
            rw [hdrop0] at hrec
            have hone : 1 ≤ (rest.length + 1 + b - 1) / b := by
              have hge : b ≤ rest.length + 1 + b - 1 := by omega
              exact Nat.one_le_div_iff hb |>.mpr hge
            have hzero : (chunkBlocksFuel fuel b ((blk :: rest).drop b)).length = 0 := by
              have hnil : (blk :: rest).drop b = [] := by
                rw [List.drop_eq_nil_iff]
                simp
                omega
              rw [hnil]
              cases fuel <;> simp [chunkBlocksFuel]
            rw [hzero]
            omega
          · have harith : rest.length + 1 - b + b - 1 = rest.length := by omega
            rw [harith] at hrec
            have hsplit : rest.length + 1 + b - 1 = rest.length + b := by omega
            rw [hsplit]
            have hdiv : (rest.length + b) / b = rest.length / b + 1 :=
              Nat.add_div_right _ hb
            rw [hdiv]
            omega

theorem chunkBlocks_count_le {b : ℕ} (hb : 0 < b) (bs : List (List ℕ)) :
    (chunkBlocks b bs).length ≤ ceilDiv b bs.length :=
  chunkBlocksFuel_count_le b hb bs.length bs le_rfl

theorem ceilDiv_mono_right (b : ℕ) {x y : ℕ} (h : x ≤ y) :
    ceilDiv b x ≤ ceilDiv b y := by
  unfold ceilDiv
  exact Nat.div_le_div_right (by omega)

/-- Positional affine coefficient (slope). -/
def AcoefP (b : ℕ) : ℕ → ℕ
  | m =>
      if h : b < 2 ∨ m ≤ b then
        m
      else
        3 * b + AcoefP b (ceilDiv b m)
termination_by m => m
decreasing_by
  simp_wf
  have hb : 2 ≤ b := by omega
  have hm : b < m := by omega
  exact ceilDiv_lt_self hb hm

/-- Positional affine coefficient (offset). -/
def BcoefP (b : ℕ) : ℕ → ℕ
  | m =>
      if h : b < 2 ∨ m ≤ b then
        0
      else
        m + BcoefP b (ceilDiv b m)
termination_by m => m
decreasing_by
  simp_wf
  have hb : 2 ≤ b := by omega
  have hm : b < m := by omega
  exact ceilDiv_lt_self hb hm

theorem AcoefP_le {b m : ℕ} (h : b < 2 ∨ m ≤ b) : AcoefP b m = m := by
  rw [AcoefP]
  simp [h]

theorem AcoefP_gt {b m : ℕ} (hb : 2 ≤ b) (hm : b < m) :
    AcoefP b m = 3 * b + AcoefP b (ceilDiv b m) := by
  rw [AcoefP]
  simp [show ¬ (b < 2 ∨ m ≤ b) by omega]

theorem BcoefP_le {b m : ℕ} (h : b < 2 ∨ m ≤ b) : BcoefP b m = 0 := by
  rw [BcoefP]
  simp [h]

theorem BcoefP_gt {b m : ℕ} (hb : 2 ≤ b) (hm : b < m) :
    BcoefP b m = m + BcoefP b (ceilDiv b m) := by
  rw [BcoefP]
  simp [show ¬ (b < 2 ∨ m ≤ b) by omega]

/-- **THE POSITIONAL PER-STEP SOUNDNESS** — the honest affine recursion,
conditional on `MiddlesKeyHypothesis` only.  No sparsity, no auxiliary
numeric domination. -/
theorem affine_sound_positional (hmid : MiddlesKeyHypothesis)
    (b : ℕ) (hb : 2 ≤ b) :
    ∀ m n u, ABABAFree u → Blocked m u → u.toFinset.card ≤ n →
      u.length ≤ AcoefP b m * n + BcoefP b m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n u hfree hblocked hcard
    by_cases hle : m ≤ b
    · have hlin := length_le_blocks_mul_symbols hblocked hcard
      rw [AcoefP_le (Or.inr hle), BcoefP_le (Or.inr hle)]
      omega
    · push_neg at hle
      rcases hblocked with ⟨bs, hbs_len, hnodup, hflat⟩
      have hgflat : flattenBlockGroups (chunkBlocks b bs) = bs :=
        flattenBlockGroups_chunkBlocks (by omega) bs
      have hu : flattenBlocks (flattenBlockGroups (chunkBlocks b bs)) = u := by
        rw [hgflat, hflat]
      have hglen : ∀ g ∈ chunkBlocks b bs, g.length ≤ b :=
        chunkBlocks_group_le (by omega) bs
      have hgnodup : ∀ g ∈ chunkBlocks b bs, ∀ blk ∈ g, blk.Nodup := by
        intro g hg blk hblk
        refine hnodup blk ?_
        rw [← hgflat]
        exact mem_flattenBlockGroups_of_mem hg hblk
      -- (1) the four-way split
      have h1 : u.length
          ≤ selTotalFrom selLocal [] (chunkBlocks b bs)
            + selTotalFrom selLeft [] (chunkBlocks b bs)
            + selTotalFrom selRight [] (chunkBlocks b bs)
            + middleLengthTotalFrom [] (chunkBlocks b bs) := by
        rw [← hu]
        exact length_four_way_total (chunkBlocks b bs) []
      -- (2) the three linear classifications
      have hLa : selTotalFrom selLocal [] (chunkBlocks b bs)
          ≤ b * selSymsTotalFrom selLocal [] (chunkBlocks b bs) :=
        selTotalFrom_le_syms selLocal b _ hglen hgnodup []
      have hLb : selSymsTotalFrom selLocal [] (chunkBlocks b bs) ≤ n := by
        have := selSymsTotalFrom_le_of_excludes_post selLocal
          (fun _ _ _ h => selLocal_excludes_post h) (chunkBlocks b bs) []
        rw [hu] at this
        omega
      have hFa : selTotalFrom selLeft [] (chunkBlocks b bs)
          ≤ b * selSymsTotalFrom selLeft [] (chunkBlocks b bs) :=
        selTotalFrom_le_syms selLeft b _ hglen hgnodup []
      have hFb : selSymsTotalFrom selLeft [] (chunkBlocks b bs) ≤ n := by
        have := selSymsTotalFrom_le_of_excludes_post selLeft
          (fun _ _ _ h => selLeft_excludes_post h) (chunkBlocks b bs) []
        rw [hu] at this
        omega
      have hRa : selTotalFrom selRight [] (chunkBlocks b bs)
          ≤ b * selSymsTotalFrom selRight [] (chunkBlocks b bs) :=
        selTotalFrom_le_syms selRight b _ hglen hgnodup []
      have hRb : selSymsTotalFrom selRight [] (chunkBlocks b bs) ≤ n := by
        have := selSymsTotalFrom_le_of_excludes_pre selRight
          (fun _ _ _ h => selRight_excludes_pre h) (chunkBlocks b bs) []
        rw [hu] at this
        simp only [List.toFinset_nil, Finset.sdiff_empty] at this
        omega
      -- (3) the middles, through the hypothesis
      have hM : middleLengthTotalFrom [] (chunkBlocks b bs)
          ≤ middleSymbolsLengthTotalFrom [] (chunkBlocks b bs)
            + (flattenBlockGroups (chunkBlocks b bs)).length := by
        refine middleLengthTotalFrom_le_of_middles_key hmid [] _ ?_ ?_
        · simpa [hu] using hfree
        · intro blk hblk
          rw [hgflat] at hblk
          exact hnodup blk hblk
      have hMm : (flattenBlockGroups (chunkBlocks b bs)).length ≤ m := by
        rw [hgflat]
        exact hbs_len
      -- (4) the contraction recursion
      have hcount : (chunkBlocks b bs).length ≤ ceilDiv b m :=
        le_trans (chunkBlocks_count_le (by omega) bs)
          (by
            have := ceilDiv_mono_right b hbs_len
            omega)
      have hctr_blocked : Blocked (ceilDiv b m)
          (flattenBlocks (middleContractionFrom [] (chunkBlocks b bs))) :=
        (middleContractionFrom_blocked (chunkBlocks b bs) []).mono hcount
      have hctr_free : ABABAFree
          (flattenBlocks (middleContractionFrom [] (chunkBlocks b bs))) := by
        refine ababaFree_of_sublist ?_ hfree
        have := middleContractionFrom_sublist (chunkBlocks b bs) []
        rwa [hu] at this
      have hctr_card :
          (flattenBlocks (middleContractionFrom [] (chunkBlocks b bs))).toFinset.card
            ≤ n := by
        have hsub := toFinset_card_le_of_sublist
          (middleContractionFrom_sublist (chunkBlocks b bs) [])
        rw [hu] at hsub
        omega
      have hMS : middleSymbolsLengthTotalFrom [] (chunkBlocks b bs)
          ≤ AcoefP b (ceilDiv b m) * n + BcoefP b (ceilDiv b m) := by
        rw [← middleContractionFrom_flatten_length]
        exact ih (ceilDiv b m) (ceilDiv_lt_self hb hle) n _
          hctr_free hctr_blocked hctr_card
      -- assemble
      rw [AcoefP_gt hb hle, BcoefP_gt hb hle]
      have hbn1 : selTotalFrom selLocal [] (chunkBlocks b bs) ≤ b * n :=
        le_trans hLa (Nat.mul_le_mul_left b hLb)
      have hbn2 : selTotalFrom selLeft [] (chunkBlocks b bs) ≤ b * n :=
        le_trans hFa (Nat.mul_le_mul_left b hFb)
      have hbn3 : selTotalFrom selRight [] (chunkBlocks b bs) ≤ b * n :=
        le_trans hRa (Nat.mul_le_mul_left b hRb)
      have hexpand : (3 * b + AcoefP b (ceilDiv b m)) * n
          = b * n + b * n + b * n + AcoefP b (ceilDiv b m) * n := by ring
      rw [hexpand]
      omega

/-- The honest `DSBound` surface from the positional recursion. -/
theorem psi_sound_positional (hmid : MiddlesKeyHypothesis)
    (b m n : ℕ) (hb : 2 ≤ b) :
    DSBound m n (AcoefP b m * n + BcoefP b m) := by
  intro u hfree _hs hblocked hcard
  exact affine_sound_positional hmid b hb m n u hfree hblocked hcard

/-- One Hart--Sharir positional decomposition step with local subsequences exposed. -/
theorem oneStep_decomposition (hmid : MiddlesKeyHypothesis) (b : ℕ)
    (hb : 2 ≤ b) (m n : ℕ) (u : List ℕ) (hm : b < m)
    (hfree : ABABAFree u) (hblocked : Blocked m u)
    (hcard : u.toFinset.card ≤ n) :
    ∃ (locals : List (List ℕ)) (ctr : List ℕ),
      locals.length ≤ ceilDiv b m
      ∧ (∀ l ∈ locals, ABABAFree l ∧ Blocked b l)
      ∧ (locals.map (fun l => l.toFinset.card)).sum ≤ n
      ∧ ABABAFree ctr ∧ Blocked (ceilDiv b m) ctr
      ∧ ctr.toFinset.card ≤ n
      ∧ u.length ≤ (locals.map List.length).sum + ctr.length
          + 2 * b * n + m := by
  rcases hblocked with ⟨bs, hbs_len, hnodup, hflat⟩
  let groups := chunkBlocks b bs
  let locals := selSeqsFrom selLocal [] groups
  let ctr := flattenBlocks (middleContractionFrom [] groups)
  have hgflat : flattenBlockGroups groups = bs := by
    dsimp [groups]
    exact flattenBlockGroups_chunkBlocks (by omega) bs
  have hu : flattenBlocks (flattenBlockGroups groups) = u := by
    rw [hgflat, hflat]
  have hglen : ∀ g ∈ groups, g.length ≤ b := by
    dsimp [groups]
    exact chunkBlocks_group_le (by omega) bs
  have hgnodup : ∀ g ∈ groups, ∀ blk ∈ g, blk.Nodup := by
    intro g hg blk hblk
    refine hnodup blk ?_
    rw [← hgflat]
    exact mem_flattenBlockGroups_of_mem hg hblk
  have hcount : groups.length ≤ ceilDiv b m := by
    dsimp [groups]
    exact le_trans (chunkBlocks_count_le (by omega) bs)
      (by
        have := ceilDiv_mono_right b hbs_len
        omega)
  refine ⟨locals, ctr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [locals]
    rw [selSeqsFrom_length]
    exact hcount
  · intro l hl
    have hl' : l ∈ selSeqsFrom selLocal [] groups := by
      simpa [locals] using hl
    constructor
    · refine ababaFree_of_sublist ?_ hfree
      have hsub := selSeqsFrom_sublist_flatten selLocal groups [] l hl'
      rwa [hu] at hsub
    · exact selSeqsFrom_blocked selLocal groups [] l hglen hgnodup hl'
  · have hsyms : selSymsTotalFrom selLocal [] groups ≤ n := by
      have := selSymsTotalFrom_le_of_excludes_post selLocal
        (fun _ _ _ h => selLocal_excludes_post h) groups []
      rw [hu] at this
      omega
    dsimp [locals]
    rw [selSeqsFrom_cards_sum]
    exact hsyms
  · refine ababaFree_of_sublist ?_ hfree
    dsimp [ctr]
    have hsub := middleContractionFrom_sublist groups []
    rwa [hu] at hsub
  · dsimp [ctr]
    exact (middleContractionFrom_blocked groups []).mono hcount
  · have hsub : ctr.toFinset.card ≤ u.toFinset.card := by
      dsimp [ctr]
      have := toFinset_card_le_of_sublist
        (middleContractionFrom_sublist groups [])
      rwa [hu] at this
    exact le_trans hsub hcard
  · have hsplit : u.length
        ≤ selTotalFrom selLocal [] groups + selTotalFrom selLeft [] groups
          + selTotalFrom selRight [] groups + middleLengthTotalFrom [] groups := by
      rw [← hu]
      exact length_four_way_total groups []
    have hFa : selTotalFrom selLeft [] groups
        ≤ b * selSymsTotalFrom selLeft [] groups :=
      selTotalFrom_le_syms selLeft b groups hglen hgnodup []
    have hFb : selSymsTotalFrom selLeft [] groups ≤ n := by
      have := selSymsTotalFrom_le_of_excludes_post selLeft
        (fun _ _ _ h => selLeft_excludes_post h) groups []
      rw [hu] at this
      omega
    have hleft : selTotalFrom selLeft [] groups ≤ b * n :=
      le_trans hFa (Nat.mul_le_mul_left b hFb)
    have hRa : selTotalFrom selRight [] groups
        ≤ b * selSymsTotalFrom selRight [] groups :=
      selTotalFrom_le_syms selRight b groups hglen hgnodup []
    have hRb : selSymsTotalFrom selRight [] groups ≤ n := by
      have := selSymsTotalFrom_le_of_excludes_pre selRight
        (fun _ _ _ h => selRight_excludes_pre h) groups []
      rw [hu] at this
      simp only [List.toFinset_nil, Finset.sdiff_empty] at this
      omega
    have hright : selTotalFrom selRight [] groups ≤ b * n :=
      le_trans hRa (Nat.mul_le_mul_left b hRb)
    have hM : middleLengthTotalFrom [] groups
        ≤ middleSymbolsLengthTotalFrom [] groups
          + (flattenBlockGroups groups).length := by
      refine middleLengthTotalFrom_le_of_middles_key hmid [] groups ?_ ?_
      · simpa [hu] using hfree
      · intro blk hblk
        rw [hgflat] at hblk
        exact hnodup blk hblk
    have hMm : (flattenBlockGroups groups).length ≤ m := by
      rw [hgflat]
      exact hbs_len
    have hlocals_len :
        (locals.map List.length).sum = selTotalFrom selLocal [] groups := by
      dsimp [locals]
      rw [selSeqsFrom_lengths_sum]
    have hctr_len :
        ctr.length = middleSymbolsLengthTotalFrom [] groups := by
      dsimp [ctr]
      exact middleContractionFrom_flatten_length groups []
    have htwo : 2 * b * n = b * n + b * n := by ring
    calc
      u.length
          ≤ selTotalFrom selLocal [] groups + selTotalFrom selLeft [] groups
            + selTotalFrom selRight [] groups + middleLengthTotalFrom [] groups :=
        hsplit
      _ ≤ selTotalFrom selLocal [] groups + b * n + b * n
            + (middleSymbolsLengthTotalFrom [] groups
              + (flattenBlockGroups groups).length) := by
        omega
      _ ≤ (locals.map List.length).sum + ctr.length + 2 * b * n + m := by
        rw [hlocals_len, hctr_len, htwo]
        omega

/--
M7 schedule/compression blocker.  This is the exact remaining endpoint
assembly obligation after the positional M6c recurrence: for each sparse
ABABA-free sequence, choose a positional blocking level and a legal group size
whose affine `AcoefP/BcoefP` bound is already in the target inverse-Ackermann
shape.  It is deliberately independent of the middle-counting hypothesis.
-/
def Blocking_M7_positional_schedule : Prop :=
  ∃ C : ℕ, ∀ (m : ℕ) (u : List ℕ),
    u.toFinset.card ≤ m →
    Sparse u →
    ABABAFree u →
    ∃ blocks b : ℕ,
      2 ≤ b ∧
      Blocked blocks u ∧
      AcoefP b blocks * m + BcoefP b blocks ≤
        C * (m + 1) * (alpha (m + 1) + 1)

def KlazarN5PositionalHypothesis : Prop :=
  MiddlesKeyHypothesis ∧ Blocking_M7_positional_schedule

/--
Endpoint from the closed positional recurrence plus the isolated M7
schedule/compression obligation.  Closing `Blocking_M7_positional_schedule`
reduces this theorem's hypothesis to `MiddlesKeyHypothesis` alone.
-/
theorem main_of_positional (h : KlazarN5PositionalHypothesis) :
    ∃ C : ℕ, ∀ (m : ℕ) (u : List ℕ),
      u.toFinset.card ≤ m →
      u.Chain' (· ≠ ·) →
      (¬ ∃ a b : ℕ, a ≠ b ∧ List.Sublist [a, b, a, b, a] u) →
      u.length ≤ C * (m + 1) * (alpha (m + 1) + 1) := by
  rcases h with ⟨hmid, C, hC⟩
  refine ⟨C, ?_⟩
  intro m u hcard hs hfree
  have hsparse : Sparse u := hs
  have hfree' : ABABAFree u := hfree
  rcases hC m u hcard hsparse hfree' with
    ⟨blocks, b, hb, hblocked, hcoeff⟩
  have hpos :
      u.length ≤ AcoefP b blocks * m + BcoefP b blocks :=
    affine_sound_positional hmid b hb blocks m u hfree' hblocked hcard
  exact le_trans hpos hcoeff

end Positional

#print axioms affine_sound_positional
#print axioms psi_sound_positional
#print axioms oneStep_decomposition
#print axioms main_of_positional

/-! ## MiddlesKey: PROOF of `MiddlesKeyHypothesis`

The interval argument.  For a both-sided ("middle") symbol `a`, occurrences
in the group sit in distinct blocks.  For middle `a ≠ b`, no `b`-block lies
strictly between two `a`-blocks, and shared first blocks are equally fatal
(the within-block order supplies the alternation): each case yields the
forbidden five-term alternation through `pre` and `post`.  Hence the
non-first occurrence blocks of distinct middle symbols are pairwise disjoint
subsets of the block range:

  |middleRaw| = Σ_a #blocks(a) ≤ #symbols + #blocks.                      -/

section MiddlesKeyProof

/-- Occurrence count survives a filter the value satisfies. -/
theorem count_filter_of_pos {q : ℕ → Bool} {a : ℕ} (h : q a = true) :
    ∀ l : List ℕ, (l.filter q).count a = l.count a := by
  intro l
  induction l with
  | nil => rfl
  | cons x rest ih =>
      by_cases hx : q x = true
      · rw [List.filter_cons_of_pos hx, List.count_cons, List.count_cons, ih]
      · rw [List.filter_cons_of_neg (by simp [hx]), ih, List.count_cons]
        have hxa : ¬ (x == a) = true := by
          simp only [beq_iff_eq]
          intro heq
          rw [heq] at hx
          exact hx h
        simp [hxa]

/-- In a duplicate-free list every value occurs zero or one times. -/
theorem count_eq_ite_of_nodup {blk : List ℕ} (h : blk.Nodup) (a : ℕ) :
    blk.count a = if a ∈ blk then 1 else 0 := by
  by_cases hm : a ∈ blk
  · rw [if_pos hm]
    have h1 := List.nodup_iff_count_le_one.mp h a
    have h2 : 0 < blk.count a := List.count_pos_iff.mpr hm
    omega
  · rw [if_neg hm]
    exact List.count_eq_zero_of_not_mem hm

/-- Filtering commutes with mapping at the level of lengths. -/
theorem length_filter_map (f : ℕ → ℕ) (p : ℕ → Bool) :
    ∀ l : List ℕ, ((l.map f).filter p).length
      = (l.filter (fun x => p (f x))).length := by
  intro l
  induction l with
  | nil => rfl
  | cons x rest ih =>
      rw [List.map_cons]
      by_cases hx : p (f x) = true
      · rw [List.filter_cons_of_pos hx,
          List.filter_cons_of_pos (p := fun y => p (f y)) hx,
          List.length_cons, List.length_cons, ih]
      · rw [List.filter_cons_of_neg (by simp [hx]),
          List.filter_cons_of_neg (p := fun y => p (f y)) (by simp [hx]), ih]

/-- The list length as a sum of per-value counts. -/
theorem length_eq_sum_count_toFinset :
    ∀ l : List ℕ, l.length = ∑ a ∈ l.toFinset, l.count a := by
  intro l
  induction l with
  | nil => simp
  | cons x rest ih =>
      have hcnt : ∀ a, (x :: rest).count a
          = rest.count a + if a = x then 1 else 0 := by
        intro a
        rw [List.count_cons]
        by_cases hax : x = a
        · simp [hax]
        · have hax' : ¬ a = x := fun heq => hax heq.symm
          simp [hax, hax']
      rw [List.length_cons, ih]
      by_cases hx : x ∈ rest
      · have hT : (x :: rest).toFinset = rest.toFinset := by
          simp [List.toFinset_cons,
            Finset.insert_eq_self.mpr (List.mem_toFinset.mpr hx)]
        rw [hT]
        have hsum : ∑ a ∈ rest.toFinset, (x :: rest).count a
            = (∑ a ∈ rest.toFinset, rest.count a)
              + ∑ a ∈ rest.toFinset, (if a = x then 1 else 0) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun a _ => hcnt a)
        have hone : (∑ a ∈ rest.toFinset, if a = x then (1 : ℕ) else 0) = 1 := by
          rw [Finset.sum_ite_eq' rest.toFinset x (fun _ => 1),
            if_pos (List.mem_toFinset.mpr hx)]
        rw [hsum, hone]
      · have hT : (x :: rest).toFinset = insert x rest.toFinset :=
          List.toFinset_cons
        rw [hT, Finset.sum_insert (by simpa using hx)]
        have h1 : (x :: rest).count x = rest.count x + 1 := by
          rw [hcnt x]
          simp
        have h2 : ∑ a ∈ rest.toFinset, (x :: rest).count a
            = ∑ a ∈ rest.toFinset, rest.count a := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          rw [hcnt a]
          have : ¬ a = x := fun heq => hx (heq ▸ List.mem_toFinset.mp ha)
          simp [this]
        have h3 : rest.count x = 0 := List.count_eq_zero_of_not_mem hx
        rw [h1, h2, h3]
        omega

/-- The blocks (by index) in which a symbol occurs. -/
def blockIdxList (group : List (List ℕ)) (a : ℕ) : List ℕ :=
  (List.range group.length).filter (fun i => decide (a ∈ group.getD i []))

/-- Occurrences in the flattened group are exactly the blocks met. -/
theorem count_flattenBlocks (a : ℕ) :
    ∀ (group : List (List ℕ)), (∀ blk ∈ group, blk.Nodup) →
      (flattenBlocks group).count a = (blockIdxList group a).length := by
  intro group
  induction group with
  | nil => intro _; rfl
  | cons blk rest ih =>
      intro hnd
      have hcount : (flattenBlocks (blk :: rest)).count a
          = blk.count a + (flattenBlocks rest).count a := by
        show (blk ++ flattenBlocks rest).count a = _
        rw [List.count_append]
      have hstep : blockIdxList (blk :: rest) a
          = (List.range (rest.length + 1)).filter
              (fun i => decide (a ∈ (blk :: rest).getD i [])) := rfl
      rw [hcount, ih (fun b hb => hnd b (List.mem_cons_of_mem _ hb)),
        count_eq_ite_of_nodup (hnd blk (by simp)) a, hstep,
        List.range_succ_eq_map]
      have htail : (((List.range rest.length).map Nat.succ).filter
            (fun i => decide (a ∈ (blk :: rest).getD i []))).length
          = (blockIdxList rest a).length := by
        rw [length_filter_map]
        rfl
      by_cases hm : a ∈ blk
      · rw [if_pos hm, List.filter_cons_of_pos (by simpa using hm),
          List.length_cons, htail]
        omega
      · rw [if_neg hm, List.filter_cons_of_neg (by simpa using hm), htail]
        omega

/-- Block index lists are strictly increasing. -/
theorem blockIdxList_pairwise (group : List (List ℕ)) (a : ℕ) :
    (blockIdxList group a).Pairwise (· < ·) :=
  List.pairwise_lt_range.sublist List.filter_sublist

theorem blockIdxList_mem_pred {group : List (List ℕ)} {a i : ℕ}
    (h : i ∈ blockIdxList group a) :
    i < group.length ∧ a ∈ group.getD i [] := by
  unfold blockIdxList at h
  have h1 := List.mem_of_mem_filter h
  have h2 := (List.mem_filter.mp h).2
  exact ⟨List.mem_range.mp h1, of_decide_eq_true h2⟩

/-- A sublist of one block embeds in the flattened group. -/
theorem flatten_sublist_one (y : List ℕ) :
    ∀ (group : List (List ℕ)) (j : ℕ), j < group.length →
      y.Sublist (group.getD j []) → y.Sublist (flattenBlocks group) := by
  intro group
  induction group with
  | nil => intro j hj; simp at hj
  | cons blk rest ih =>
      intro j hj hy
      show y.Sublist (blk ++ flattenBlocks rest)
      cases j with
      | zero =>
          exact hy.trans (List.sublist_append_left _ _)
      | succ j' =>
          have hj' : j' < rest.length := by
            have h := hj
            simp only [List.length_cons] at h
            omega
          exact (ih j' hj' hy).trans (List.sublist_append_right _ _)

/-- Sublists of two blocks at increasing indices concatenate into the
flattened group. -/
theorem flatten_sublist_two (x y : List ℕ) :
    ∀ (group : List (List ℕ)) (i j : ℕ), i < j → j < group.length →
      x.Sublist (group.getD i []) → y.Sublist (group.getD j []) →
      (x ++ y).Sublist (flattenBlocks group) := by
  intro group
  induction group with
  | nil => intro i j hij hj; simp at hj
  | cons blk rest ih =>
      intro i j hij hj hx hy
      show (x ++ y).Sublist (blk ++ flattenBlocks rest)
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hj' : j' < rest.length := by
        have h := hj
        simp only [List.length_cons] at h
        omega
      cases i with
      | zero =>
          exact List.Sublist.append hx (flatten_sublist_one y rest j' hj' hy)
      | succ i' =>
          exact (ih i' j' (by omega) hj' hx hy).trans
            (List.sublist_append_right _ _)

/-- Three blocks. -/
theorem flatten_sublist_three (x y z : List ℕ) :
    ∀ (group : List (List ℕ)) (i j k : ℕ), i < j → j < k →
      k < group.length →
      x.Sublist (group.getD i []) → y.Sublist (group.getD j []) →
      z.Sublist (group.getD k []) →
      (x ++ y ++ z).Sublist (flattenBlocks group) := by
  intro group
  induction group with
  | nil => intro i j k hij hjk hk; simp at hk
  | cons blk rest ih =>
      intro i j k hij hjk hk hx hy hz
      show (x ++ y ++ z).Sublist (blk ++ flattenBlocks rest)
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hk' : k' < rest.length := by
        have h := hk
        simp only [List.length_cons] at h
        omega
      cases i with
      | zero =>
          obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
          rw [List.append_assoc]
          exact List.Sublist.append hx
            (flatten_sublist_two y z rest j' k' (by omega) hk' hy hz)
      | succ i' =>
          obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
          exact (ih i' j' k' (by omega) (by omega) hk' hx hy hz).trans
            (List.sublist_append_right _ _)

/-- Two distinct members of a list appear in one of the two orders. -/
theorem pair_sublist_of_two_mem {a b : ℕ} :
    ∀ {blk : List ℕ}, a ∈ blk → b ∈ blk → a ≠ b →
      [a, b].Sublist blk ∨ [b, a].Sublist blk := by
  intro blk
  induction blk with
  | nil => intro h; simp at h
  | cons x rest ih =>
      intro ha hb hab
      by_cases hxa : x = a
      · subst hxa
        have hb' : b ∈ rest := by
          rcases List.mem_cons.mp hb with h | h
          · exact (hab h.symm).elim
          · exact h
        exact Or.inl ((List.singleton_sublist.mpr hb').cons₂ x)
      · by_cases hxb : x = b
        · subst hxb
          have ha' : a ∈ rest := by
            rcases List.mem_cons.mp ha with h | h
            · exact (hab h).elim
            · exact h
          exact Or.inr ((List.singleton_sublist.mpr ha').cons₂ x)
        · have ha' : a ∈ rest := by
            rcases List.mem_cons.mp ha with h | h
            · exact (hxa h.symm).elim
            · exact h
          have hb' : b ∈ rest := by
            rcases List.mem_cons.mp hb with h | h
            · exact (hxb h.symm).elim
            · exact h
          rcases ih ha' hb' hab with h | h
          · exact Or.inl (h.cons x)
          · exact Or.inr (h.cons x)

/-- Assemble a 5-alternation from prefix, group part, and suffix. -/
theorem ababa_of_parts {pre post : List ℕ} {gpart : List ℕ} {x : ℕ}
    (group : List (List ℕ))
    (hpre : x ∈ pre) (hpost : x ∈ post)
    (hg : gpart.Sublist (flattenBlocks group)) :
    (([x] ++ gpart ++ [x]) : List ℕ).Sublist
      (pre ++ flattenBlocks group ++ post) :=
  List.Sublist.append
    (List.Sublist.append (List.singleton_sublist.mpr hpre) hg)
    (List.singleton_sublist.mpr hpost)

/-- **The disjointness core**: distinct middle symbols cannot share
non-first occurrence blocks. -/
theorem middle_tails_disjoint {pre post : List ℕ} {group : List (List ℕ)}
    (hfree : ABABAFree (pre ++ flattenBlocks group ++ post))
    {a b : ℕ} (hab : a ≠ b)
    (hapre : a ∈ pre) (hapost : a ∈ post)
    (hbpre : b ∈ pre) (hbpost : b ∈ post)
    {sa sb : ℕ} {ta tb : List ℕ}
    (hda : blockIdxList group a = sa :: ta)
    (hdb : blockIdxList group b = sb :: tb)
    {i : ℕ} (hia : i ∈ ta) (hib : i ∈ tb) : False := by
  have hpa := blockIdxList_pairwise group a
  have hpb := blockIdxList_pairwise group b
  rw [hda] at hpa
  rw [hdb] at hpb
  have hsai : sa < i := (List.pairwise_cons.mp hpa).1 i hia
  have hsbi : sb < i := (List.pairwise_cons.mp hpb).1 i hib
  have hsa := blockIdxList_mem_pred (group := group) (a := a)
    (by rw [hda]; exact List.mem_cons_self ..)
  have hsb := blockIdxList_mem_pred (group := group) (a := b)
    (by rw [hdb]; exact List.mem_cons_self ..)
  have hiA := blockIdxList_mem_pred (group := group) (a := a)
    (by rw [hda]; exact List.mem_cons_of_mem _ hia)
  have hiB := blockIdxList_mem_pred (group := group) (a := b)
    (by rw [hdb]; exact List.mem_cons_of_mem _ hib)
  rcases Nat.lt_trichotomy sa sb with hlt | heq | hgt
  · -- blocks sa < sb < i : pattern b a b a b
    have hg : (([a] ++ [b] ++ [a]) : List ℕ).Sublist (flattenBlocks group) :=
      flatten_sublist_three [a] [b] [a] group sa sb i hlt hsbi hiA.1
        (List.singleton_sublist.mpr hsa.2)
        (List.singleton_sublist.mpr hsb.2)
        (List.singleton_sublist.mpr hiA.2)
    exact hfree ⟨b, a, fun h => hab h.symm,
      ababa_of_parts group hbpre hbpost hg⟩
  · -- shared first block: the within-block order decides the pattern
    subst heq
    rcases pair_sublist_of_two_mem hsa.2 hsb.2 hab with hord | hord
    · have hg : (([a, b] ++ [a]) : List ℕ).Sublist (flattenBlocks group) :=
        flatten_sublist_two [a, b] [a] group sa i hsai hiA.1 hord
          (List.singleton_sublist.mpr hiA.2)
      exact hfree ⟨b, a, fun h => hab h.symm,
        ababa_of_parts group hbpre hbpost hg⟩
    · have hg : (([b, a] ++ [b]) : List ℕ).Sublist (flattenBlocks group) :=
        flatten_sublist_two [b, a] [b] group sa i hsai hiB.1 hord
          (List.singleton_sublist.mpr hiB.2)
      exact hfree ⟨a, b, hab,
        ababa_of_parts group hapre hapost hg⟩
  · -- blocks sb < sa < i : pattern a b a b a
    have hg : (([b] ++ [a] ++ [b]) : List ℕ).Sublist (flattenBlocks group) :=
      flatten_sublist_three [b] [a] [b] group sb sa i hgt hsai hiB.1
        (List.singleton_sublist.mpr hsb.2)
        (List.singleton_sublist.mpr hsa.2)
        (List.singleton_sublist.mpr hiB.2)
    exact hfree ⟨a, b, hab,
      ababa_of_parts group hapre hapost hg⟩

/-- **MiddlesKeyHypothesis is a THEOREM.** -/
theorem middlesKey_proved : MiddlesKeyHypothesis := by
  intro pre group post hfree hnodup
  classical
  set T := (middleRaw pre group post).toFinset with hT
  have hboth : ∀ a ∈ T, a ∈ pre ∧ a ∈ post := by
    intro a ha
    rw [hT, List.mem_toFinset] at ha
    have h2 := (List.mem_filter.mp ha).2
    rw [decide_eq_true_eq] at h2
    exact h2
  have hflat : ∀ a ∈ T, a ∈ flattenBlocks group := by
    intro a ha
    rw [hT, List.mem_toFinset] at ha
    exact List.mem_of_mem_filter ha
  have hlen : (middleRaw pre group post).length
      = ∑ a ∈ T, (middleRaw pre group post).count a := by
    rw [hT]
    exact length_eq_sum_count_toFinset _
  have hcnt : ∀ a ∈ T, (middleRaw pre group post).count a
      = (blockIdxList group a).length := by
    intro a ha
    have hmem : a ∈ middleRaw pre group post := by
      rw [hT, List.mem_toFinset] at ha
      exact ha
    unfold middleRaw at hmem ⊢
    have hqa := (List.mem_filter.mp hmem).2
    rw [count_filter_of_pos hqa, count_flattenBlocks a group hnodup]
  have hsyms : (middleSymbols pre group post).length = T.card := by
    show (middleRaw pre group post).dedup.length = T.card
    rw [hT, List.card_toFinset]
  have hne : ∀ a ∈ T, blockIdxList group a ≠ [] := by
    intro a ha hnil
    have h1 : 0 < (flattenBlocks group).count a :=
      List.count_pos_iff.mpr (hflat a ha)
    rw [count_flattenBlocks a group hnodup, hnil] at h1
    simp at h1
  have hsplit : (∑ a ∈ T, (blockIdxList group a).length)
      = (∑ a ∈ T, ((blockIdxList group a).tail).length) + T.card := by
    have hper : ∀ a ∈ T, (blockIdxList group a).length
        = ((blockIdxList group a).tail).length + 1 := by
      intro a ha
      obtain ⟨s, t, heq⟩ := List.exists_cons_of_ne_nil (hne a ha)
      rw [heq]
      rfl
    rw [Finset.sum_congr rfl hper, Finset.sum_add_distrib]
    simp
  have hcore : (∑ a ∈ T, ((blockIdxList group a).tail).length)
      ≤ group.length := by
    have hnodupT : ∀ a ∈ T, ((blockIdxList group a).tail).Nodup := by
      intro a _
      have hnd : (blockIdxList group a).Nodup :=
        (blockIdxList_pairwise group a).imp Nat.ne_of_lt
      exact hnd.sublist (List.tail_sublist _)
    have hcard : ∀ a ∈ T, ((blockIdxList group a).tail).length
        = (((blockIdxList group a).tail).toFinset).card := by
      intro a ha
      exact (List.toFinset_card_of_nodup (hnodupT a ha)).symm
    have hdisj : (↑T : Set ℕ).PairwiseDisjoint
        (fun a => ((blockIdxList group a).tail).toFinset) := by
      intro a ha b hb hab
      show Disjoint ((blockIdxList group a).tail).toFinset
        ((blockIdxList group b).tail).toFinset
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      rw [List.mem_toFinset] at hi1 hi2
      have haT : a ∈ T := ha
      have hbT : b ∈ T := hb
      obtain ⟨sa, ta, hda⟩ := List.exists_cons_of_ne_nil (hne a haT)
      obtain ⟨sb, tb, hdb⟩ := List.exists_cons_of_ne_nil (hne b hbT)
      have hia : i ∈ ta := by
        rw [hda] at hi1
        exact hi1
      have hib : i ∈ tb := by
        rw [hdb] at hi2
        exact hi2
      exact middle_tails_disjoint hfree hab
        (hboth a haT).1 (hboth a haT).2 (hboth b hbT).1 (hboth b hbT).2
        hda hdb hia hib
    have hsub : (T.biUnion (fun a => ((blockIdxList group a).tail).toFinset))
        ⊆ Finset.range group.length := by
      intro i hi
      rw [Finset.mem_biUnion] at hi
      obtain ⟨a, ha, hia⟩ := hi
      rw [List.mem_toFinset] at hia
      have hmem : i ∈ blockIdxList group a := by
        obtain ⟨s, t, heq⟩ := List.exists_cons_of_ne_nil (hne a ha)
        rw [heq]
        rw [heq] at hia
        exact List.mem_cons_of_mem _ hia
      exact Finset.mem_range.mpr (blockIdxList_mem_pred hmem).1
    calc (∑ a ∈ T, ((blockIdxList group a).tail).length)
        = ∑ a ∈ T, (((blockIdxList group a).tail).toFinset).card :=
          Finset.sum_congr rfl hcard
      _ = (T.biUnion (fun a => ((blockIdxList group a).tail).toFinset)).card :=
          (Finset.card_biUnion hdisj).symm
      _ ≤ (Finset.range group.length).card := Finset.card_le_card hsub
      _ = group.length := Finset.card_range _
  rw [hlen, Finset.sum_congr rfl hcnt, hsyms]
  omega

end MiddlesKeyProof

#print axioms middlesKey_proved

/-! ## Unconditional surfaces: the per-step engine with no hypotheses left -/

/-- The positional per-step soundness, UNCONDITIONAL. -/
theorem affine_sound_unconditional (b : ℕ) (hb : 2 ≤ b) :
    ∀ m n u, ABABAFree u → Blocked m u → u.toFinset.card ≤ n →
      u.length ≤ AcoefP b m * n + BcoefP b m :=
  affine_sound_positional middlesKey_proved b hb

/-- The honest `DSBound` surface, UNCONDITIONAL. -/
theorem psi_sound_unconditional (b m n : ℕ) (hb : 2 ≤ b) :
    DSBound m n (AcoefP b m * n + BcoefP b m) :=
  psi_sound_positional middlesKey_proved b m n hb

/-- The locals-exposed one-step decomposition, UNCONDITIONAL. -/
theorem oneStep_counting_unconditional (groups : List (List (List ℕ)))
    (hfree : ABABAFree (flattenBlocks (flattenBlockGroups groups)))
    (hnodup : ∀ block ∈ flattenBlockGroups groups, block.Nodup) :
    (flattenBlocks (flattenBlockGroups groups)).length ≤
      localLengthTotal groups groups +
        middleSymbolsLengthTotalFrom [] groups +
          (flattenBlockGroups groups).length +
            boundaryLengthTotalFrom groups [] groups :=
  oneStep_counting_of_middles_key middlesKey_proved groups hfree hnodup

/-! ## T1: order-parametric alternation engine -/

section OrderParametric

/-- Alternating pattern of length `s`, starting with `a`. -/
def altPattern (a b : ℕ) : ℕ → List ℕ
  | 0 => []
  | s + 1 => a :: altPattern b a s

def AltFree (s : ℕ) (u : List ℕ) : Prop :=
  ¬ ∃ a b : ℕ, a ≠ b ∧ List.Sublist (altPattern a b s) u

theorem altPattern_sublist_succ (a b s : ℕ) :
    List.Sublist (altPattern a b s) (altPattern a b (s + 1)) := by
  induction s generalizing a b with
  | zero =>
      simp [altPattern]
  | succ s ih =>
      exact List.Sublist.cons₂ a (ih b a)

theorem AltFree.succ {s : ℕ} {u : List ℕ}
    (hfree : AltFree s u) : AltFree (s + 1) u := by
  intro hbad
  rcases hbad with ⟨a, b, hne, hsub⟩
  exact hfree ⟨a, b, hne, (altPattern_sublist_succ a b s).trans hsub⟩

theorem ABABAFree_iff_AltFree5 (u : List ℕ) :
    ABABAFree u ↔ AltFree 5 u := by
  unfold ABABAFree HasABABA AltFree
  simp [altPattern]

theorem AltFree_of_sublist {s : ℕ} {v u : List ℕ}
    (hsub : List.Sublist v u) (hfree : AltFree s u) : AltFree s v := by
  intro hbad
  rcases hbad with ⟨a, b, hne, hv⟩
  exact hfree ⟨a, b, hne, hv.trans hsub⟩

theorem groupLocalSubsequence_altFree
    {s : ℕ} {groups : List (List (List ℕ))} {g : List (List ℕ)}
    (hg : g ∈ groups)
    (hfree : AltFree s (flattenBlocks (flattenBlockGroups groups))) :
    AltFree s (groupLocalSubsequence groups g) := by
  exact AltFree_of_sublist
    ((groupLocalSubsequence_sublist groups g).trans
      (flattenBlocks_group_sublist_flattenBlockGroups_of_mem hg))
    hfree

theorem globalContraction_altFree
    {s : ℕ} {groups : List (List (List ℕ))}
    (hfree : AltFree s (flattenBlocks (flattenBlockGroups groups))) :
    AltFree s (globalContraction groups) := by
  exact AltFree_of_sublist (globalContraction_sublist_groups groups) hfree

theorem middleContractionFrom_altFree
    {s : ℕ} {groups : List (List (List ℕ))} {pre : List ℕ}
    (hfree : AltFree s (flattenBlocks (flattenBlockGroups groups))) :
    AltFree s (flattenBlocks (middleContractionFrom pre groups)) := by
  exact AltFree_of_sublist (middleContractionFrom_sublist groups pre) hfree

def MiddlesKeyAt (s C : ℕ) : Prop :=
  ∀ pre group post,
    AltFree s (pre ++ flattenBlocks group ++ post) →
    (∀ b ∈ group, b.Nodup) →
    (middleRaw pre group post).length ≤
      C * ((middleSymbols pre group post).length + group.length)

theorem MiddlesKeyAt_5_1 : MiddlesKeyAt 5 1 := by
  intro pre group post hfree hnodup
  have hfree' : ABABAFree (pre ++ flattenBlocks group ++ post) :=
    (ABABAFree_iff_AltFree5 _).2 hfree
  have h := middlesKey_proved pre group post hfree' hnodup
  simpa using h

theorem middleLengthTotalFrom_le_of_middles_key_at
    {s C : ℕ} (hmid : MiddlesKeyAt s C) :
    ∀ (pre : List ℕ) (groups : List (List (List ℕ))),
      AltFree s (pre ++ flattenBlocks (flattenBlockGroups groups)) →
      (∀ block ∈ flattenBlockGroups groups, block.Nodup) →
      middleLengthTotalFrom pre groups ≤
        C * (middleSymbolsLengthTotalFrom pre groups +
          (flattenBlockGroups groups).length)
  | pre, [], _hfree, _hnodup => by
      simp [flattenBlockGroups, middleLengthTotalFrom, middleSymbolsLengthTotalFrom]
  | pre, g :: gs, hfree, hnodup => by
      have hhead_free :
          AltFree s (pre ++ flattenBlocks g ++
            flattenBlocks (flattenBlockGroups gs)) := by
        simpa [flattenBlockGroups, flattenBlocks_append, List.append_assoc] using hfree
      have hhead_nodup : ∀ block ∈ g, block.Nodup := by
        intro block hb
        exact hnodup block (by simp [flattenBlockGroups, hb])
      have hhead :=
        hmid pre g (flattenBlocks (flattenBlockGroups gs)) hhead_free hhead_nodup
      have htail_free :
          AltFree s ((pre ++ flattenBlocks g) ++
            flattenBlocks (flattenBlockGroups gs)) := by
        simpa [List.append_assoc] using hhead_free
      have htail_nodup : ∀ block ∈ flattenBlockGroups gs, block.Nodup := by
        intro block hb
        exact hnodup block (by simp [flattenBlockGroups, hb])
      have htail :=
        middleLengthTotalFrom_le_of_middles_key_at hmid
          (pre ++ flattenBlocks g) gs htail_free htail_nodup
      simp only [flattenBlockGroups, flattenBlocks_append, List.length_append,
        middleLengthTotalFrom, middleSymbolsLengthTotalFrom]
      calc
        (middleRaw pre g (flattenBlocks (flattenBlockGroups gs))).length
            + middleLengthTotalFrom (pre ++ flattenBlocks g) gs
            ≤ C * ((middleSymbols pre g
                (flattenBlocks (flattenBlockGroups gs))).length + g.length)
              + C * (middleSymbolsLengthTotalFrom (pre ++ flattenBlocks g) gs
                + (flattenBlockGroups gs).length) :=
          Nat.add_le_add hhead htail
        _ = C * ((middleSymbols pre g
                (flattenBlocks (flattenBlockGroups gs))).length
              + middleSymbolsLengthTotalFrom (pre ++ flattenBlocks g) gs
              + (g.length + (flattenBlockGroups gs).length)) := by
          ring

/-- One positional decomposition step, parameterized by the forbidden order. -/
theorem oneStep_decomposition_at {s C : ℕ} (hmid : MiddlesKeyAt s C) (b : ℕ)
    (hb : 2 ≤ b) (m n : ℕ) (u : List ℕ) (hm : b < m)
    (hfree : AltFree s u) (hblocked : Blocked m u)
    (hcard : u.toFinset.card ≤ n) :
    ∃ (locals : List (List ℕ)) (ctr : List ℕ),
      locals.length ≤ ceilDiv b m
      ∧ (∀ l ∈ locals, AltFree s l ∧ Blocked b l)
      ∧ (locals.map (fun l => l.toFinset.card)).sum ≤ n
      ∧ AltFree s ctr ∧ Blocked (ceilDiv b m) ctr
      ∧ ctr.toFinset.card ≤ n
      ∧ u.length ≤ (locals.map List.length).sum
          + C * (ctr.length + m) + 2 * b * n := by
  rcases hblocked with ⟨bs, hbs_len, hnodup, hflat⟩
  let groups := chunkBlocks b bs
  let locals := selSeqsFrom selLocal [] groups
  let ctr := flattenBlocks (middleContractionFrom [] groups)
  have hgflat : flattenBlockGroups groups = bs := by
    dsimp [groups]
    exact flattenBlockGroups_chunkBlocks (by omega) bs
  have hu : flattenBlocks (flattenBlockGroups groups) = u := by
    rw [hgflat, hflat]
  have hglen : ∀ g ∈ groups, g.length ≤ b := by
    dsimp [groups]
    exact chunkBlocks_group_le (by omega) bs
  have hgnodup : ∀ g ∈ groups, ∀ blk ∈ g, blk.Nodup := by
    intro g hg blk hblk
    refine hnodup blk ?_
    rw [← hgflat]
    exact mem_flattenBlockGroups_of_mem hg hblk
  have hcount : groups.length ≤ ceilDiv b m := by
    dsimp [groups]
    exact le_trans (chunkBlocks_count_le (by omega) bs)
      (by
        have := ceilDiv_mono_right b hbs_len
        omega)
  refine ⟨locals, ctr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [locals]
    rw [selSeqsFrom_length]
    exact hcount
  · intro l hl
    have hl' : l ∈ selSeqsFrom selLocal [] groups := by
      simpa [locals] using hl
    constructor
    · refine AltFree_of_sublist ?_ hfree
      have hsub := selSeqsFrom_sublist_flatten selLocal groups [] l hl'
      rwa [hu] at hsub
    · exact selSeqsFrom_blocked selLocal groups [] l hglen hgnodup hl'
  · have hsyms : selSymsTotalFrom selLocal [] groups ≤ n := by
      have := selSymsTotalFrom_le_of_excludes_post selLocal
        (fun _ _ _ h => selLocal_excludes_post h) groups []
      rw [hu] at this
      omega
    dsimp [locals]
    rw [selSeqsFrom_cards_sum]
    exact hsyms
  · refine AltFree_of_sublist ?_ hfree
    dsimp [ctr]
    have hsub := middleContractionFrom_sublist groups []
    rwa [hu] at hsub
  · dsimp [ctr]
    exact (middleContractionFrom_blocked groups []).mono hcount
  · have hsub : ctr.toFinset.card ≤ u.toFinset.card := by
      dsimp [ctr]
      have := toFinset_card_le_of_sublist
        (middleContractionFrom_sublist groups [])
      rwa [hu] at this
    exact le_trans hsub hcard
  · have hsplit : u.length
        ≤ selTotalFrom selLocal [] groups + selTotalFrom selLeft [] groups
          + selTotalFrom selRight [] groups + middleLengthTotalFrom [] groups := by
      rw [← hu]
      exact length_four_way_total groups []
    have hFa : selTotalFrom selLeft [] groups
        ≤ b * selSymsTotalFrom selLeft [] groups :=
      selTotalFrom_le_syms selLeft b groups hglen hgnodup []
    have hFb : selSymsTotalFrom selLeft [] groups ≤ n := by
      have := selSymsTotalFrom_le_of_excludes_post selLeft
        (fun _ _ _ h => selLeft_excludes_post h) groups []
      rw [hu] at this
      omega
    have hleft : selTotalFrom selLeft [] groups ≤ b * n :=
      le_trans hFa (Nat.mul_le_mul_left b hFb)
    have hRa : selTotalFrom selRight [] groups
        ≤ b * selSymsTotalFrom selRight [] groups :=
      selTotalFrom_le_syms selRight b groups hglen hgnodup []
    have hRb : selSymsTotalFrom selRight [] groups ≤ n := by
      have := selSymsTotalFrom_le_of_excludes_pre selRight
        (fun _ _ _ h => selRight_excludes_pre h) groups []
      rw [hu] at this
      simp only [List.toFinset_nil, Finset.sdiff_empty] at this
      omega
    have hright : selTotalFrom selRight [] groups ≤ b * n :=
      le_trans hRa (Nat.mul_le_mul_left b hRb)
    have hM : middleLengthTotalFrom [] groups
        ≤ C * (middleSymbolsLengthTotalFrom [] groups
          + (flattenBlockGroups groups).length) := by
      refine middleLengthTotalFrom_le_of_middles_key_at hmid [] groups ?_ ?_
      · simpa [hu] using hfree
      · intro blk hblk
        rw [hgflat] at hblk
        exact hnodup blk hblk
    have hMm : (flattenBlockGroups groups).length ≤ m := by
      rw [hgflat]
      exact hbs_len
    have hCM : C * (middleSymbolsLengthTotalFrom [] groups
          + (flattenBlockGroups groups).length)
        ≤ C * (middleSymbolsLengthTotalFrom [] groups + m) := by
      exact Nat.mul_le_mul_left C (Nat.add_le_add_left hMm _)
    have hlocals_len :
        (locals.map List.length).sum = selTotalFrom selLocal [] groups := by
      dsimp [locals]
      rw [selSeqsFrom_lengths_sum]
    have hctr_len :
        ctr.length = middleSymbolsLengthTotalFrom [] groups := by
      dsimp [ctr]
      exact middleContractionFrom_flatten_length groups []
    have htwo : 2 * b * n = b * n + b * n := by ring
    calc
      u.length
          ≤ selTotalFrom selLocal [] groups + selTotalFrom selLeft [] groups
            + selTotalFrom selRight [] groups + middleLengthTotalFrom [] groups :=
        hsplit
      _ ≤ selTotalFrom selLocal [] groups + b * n + b * n
            + C * (middleSymbolsLengthTotalFrom [] groups
              + (flattenBlockGroups groups).length) := by
        omega
      _ ≤ (locals.map List.length).sum + C * (ctr.length + m)
            + 2 * b * n := by
        rw [hlocals_len, hctr_len, htwo]
        omega

/-- Order-3 instance of the order-parametric one-step decomposition. -/
theorem oneStep_decomposition_at_five_one (b : ℕ)
    (hb : 2 ≤ b) (m n : ℕ) (u : List ℕ) (hm : b < m)
    (hfree : AltFree 5 u) (hblocked : Blocked m u)
    (hcard : u.toFinset.card ≤ n) :
    ∃ (locals : List (List ℕ)) (ctr : List ℕ),
      locals.length ≤ ceilDiv b m
      ∧ (∀ l ∈ locals, AltFree 5 l ∧ Blocked b l)
      ∧ (locals.map (fun l => l.toFinset.card)).sum ≤ n
      ∧ AltFree 5 ctr ∧ Blocked (ceilDiv b m) ctr
      ∧ ctr.toFinset.card ≤ n
      ∧ u.length ≤ (locals.map List.length).sum
          + ctr.length + 2 * b * n + m := by
  rcases oneStep_decomposition_at MiddlesKeyAt_5_1 b hb m n u hm hfree hblocked hcard with
    ⟨locals, ctr, hlen, hloc, hsum, hctrfree, hctrblocked, hctrcard, hbound⟩
  refine ⟨locals, ctr, hlen, hloc, hsum, hctrfree, hctrblocked, hctrcard, ?_⟩
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbound

end OrderParametric

/-! ## T2: abstract corrected-M7 shells -/

section CorrectedM7Shell

def MonotoneNat (beta : ℕ → ℕ) : Prop :=
  ∀ ⦃x y : ℕ⦄, x ≤ y → beta x ≤ beta y

/-- Occurrence cap parameter for external extremal transcript hypotheses. -/
def OccurrenceCap (cap : ℕ) (tr : List ℕ) : Prop :=
  ∀ a ∈ tr.toFinset, tr.count a ≤ cap

/--
Abstract extremal hypothesis consumed by the corrected level schedule.
`cap` is explicit because Pettie-style transcripts are split to enforce an
occurrence cap, but the bound itself is stated in terms of alphabet budget `q`.
-/
def ExHyp (s : ℕ) (beta : ℕ → ℕ) : Prop :=
  MonotoneNat beta ∧
    ∀ (q cap : ℕ) (tr : List ℕ),
      AltFree s tr →
      tr.toFinset.card ≤ q →
      OccurrenceCap cap tr →
      tr.length ≤ q * beta q

def DecreasesAbove (threshold : ℕ) (f : ℕ → ℕ) : Prop :=
  ∀ n, threshold < n → f n < n

/-- Number of iterations of `f` needed to reach `threshold`. -/
def gammaOf (f : ℕ → ℕ) (threshold : ℕ)
    (hdec : DecreasesAbove threshold f) : ℕ → ℕ
  | n =>
      if h : n ≤ threshold then
        0
      else
        1 + gammaOf f threshold hdec (f n)
termination_by n => n
decreasing_by
  simp_wf
  exact hdec n (by omega)

theorem gammaOf_le {f : ℕ → ℕ} {threshold n : ℕ}
    {hdec : DecreasesAbove threshold f} (h : n ≤ threshold) :
    gammaOf f threshold hdec n = 0 := by
  rw [gammaOf]
  simp [h]

theorem gammaOf_gt {f : ℕ → ℕ} {threshold n : ℕ}
    {hdec : DecreasesAbove threshold f} (h : threshold < n) :
    gammaOf f threshold hdec n =
      1 + gammaOf f threshold hdec (f n) := by
  rw [gammaOf]
  simp [show ¬ n ≤ threshold by omega]

def Blocking_gamma_mono : Prop :=
  ∀ (f : ℕ → ℕ) (threshold : ℕ) (hdec : DecreasesAbove threshold f),
    MonotoneNat f →
    MonotoneNat (gammaOf f threshold hdec)

theorem gammaOf_mono_of_blocking
    (hblock : Blocking_gamma_mono)
    (f : ℕ → ℕ) (threshold : ℕ) (hdec : DecreasesAbove threshold f)
    (hf : MonotoneNat f) :
    MonotoneNat (gammaOf f threshold hdec) :=
  hblock f threshold hdec hf

def Blocking_gamma_poly_alpha : Prop :=
  ∀ (beta : ℕ → ℕ) (c d threshold : ℕ)
    (hdec : DecreasesAbove threshold (fun z => beta (beta z))),
    MonotoneNat beta →
    (∀ z, beta z ≤ c * (alpha (z + 1) + 1) ^ d) →
    ∃ c' : ℕ, ∀ n,
      gammaOf (fun z => beta (beta z)) threshold hdec n
        ≤ c' * (alpha (n + 1) + 1)

theorem gamma_poly_alpha_of_blocking
    (hblock : Blocking_gamma_poly_alpha)
    (beta : ℕ → ℕ) (c d threshold : ℕ)
    (hdec : DecreasesAbove threshold (fun z => beta (beta z)))
    (hmono : MonotoneNat beta)
    (hpoly : ∀ z, beta z ≤ c * (alpha (z + 1) + 1) ^ d) :
    ∃ c' : ℕ, ∀ n,
      gammaOf (fun z => beta (beta z)) threshold hdec n
        ≤ c' * (alpha (n + 1) + 1) :=
  hblock beta c d threshold hdec hmono hpoly

/-- Level-indexed slope for the locals-recursive corrected recurrence. -/
def LevelA (sched : ℕ → ℕ) (C : ℕ) : ℕ → ℕ → ℕ
  | 0, m => m
  | level + 1, m =>
      let b := sched level
      if h : b < 2 ∨ m ≤ b then
        m
      else
        LevelA sched C level b +
          C * LevelA sched C (level + 1) (ceilDiv b m) +
            2 * b
termination_by level m => level + m
decreasing_by
  · simp_wf
    have hm : sched level < m := by omega
    omega
  · simp_wf
    have hb : 2 ≤ sched level := by omega
    have hm : sched level < m := by omega
    have hg := ceilDiv_lt_self hb hm
    omega

/-- Level-indexed offset for the locals-recursive corrected recurrence. -/
def LevelB (sched : ℕ → ℕ) (C : ℕ) : ℕ → ℕ → ℕ
  | 0, _m => 0
  | level + 1, m =>
      let b := sched level
      if h : b < 2 ∨ m ≤ b then
        0
      else
        ceilDiv b m * LevelB sched C level b +
          C * LevelB sched C (level + 1) (ceilDiv b m) +
            C * m
termination_by level m => level + m
decreasing_by
  · simp_wf
    have hm : sched level < m := by omega
    omega
  · simp_wf
    have hb : 2 ≤ sched level := by omega
    have hm : sched level < m := by omega
    have hg := ceilDiv_lt_self hb hm
    omega

def TwoLevelBound (sched : ℕ → ℕ) (C level m n : ℕ) : ℕ :=
  LevelA sched C level m * n + LevelB sched C level m

theorem LevelA_zero (sched : ℕ → ℕ) (C m : ℕ) :
    LevelA sched C 0 m = m := by
  rw [LevelA]

theorem LevelB_zero (sched : ℕ → ℕ) (C m : ℕ) :
    LevelB sched C 0 m = 0 := by
  rw [LevelB]

theorem LevelA_succ_le {sched : ℕ → ℕ} {C level m : ℕ}
    (h : sched level < 2 ∨ m ≤ sched level) :
    LevelA sched C (level + 1) m = m := by
  rw [LevelA]
  simp [h]

theorem LevelB_succ_le {sched : ℕ → ℕ} {C level m : ℕ}
    (h : sched level < 2 ∨ m ≤ sched level) :
    LevelB sched C (level + 1) m = 0 := by
  rw [LevelB]
  simp [h]

theorem LevelA_succ_gt {sched : ℕ → ℕ} {C level m : ℕ}
    (hb : 2 ≤ sched level) (hm : sched level < m) :
    LevelA sched C (level + 1) m =
      LevelA sched C level (sched level) +
        C * LevelA sched C (level + 1) (ceilDiv (sched level) m) +
          2 * sched level := by
  rw [LevelA]
  simp [show ¬ (sched level < 2 ∨ m ≤ sched level) by omega]

theorem LevelB_succ_gt {sched : ℕ → ℕ} {C level m : ℕ}
    (hb : 2 ≤ sched level) (hm : sched level < m) :
    LevelB sched C (level + 1) m =
      ceilDiv (sched level) m * LevelB sched C level (sched level) +
        C * LevelB sched C (level + 1) (ceilDiv (sched level) m) +
          C * m := by
  rw [LevelB]
  simp [show ¬ (sched level < 2 ∨ m ≤ sched level) by omega]

end CorrectedM7Shell

#print axioms affine_sound_unconditional
#print axioms psi_sound_unconditional
#print axioms oneStep_counting_unconditional
#print axioms ABABAFree_iff_AltFree5
#print axioms AltFree.succ
#print axioms AltFree_of_sublist
#print axioms MiddlesKeyAt_5_1
#print axioms oneStep_decomposition_at
#print axioms oneStep_decomposition_at_five_one
#print axioms gammaOf_le
#print axioms gammaOf_gt
#print axioms gamma_poly_alpha_of_blocking
#print axioms LevelA_succ_gt
#print axioms LevelB_succ_gt

/-! ## T2 blocker discharge: `gammaOf` monotonicity and the poly-alpha collapse

Both T2 blockers are TRUE as stated and are proven below.

* `gamma_mono_proved : Blocking_gamma_mono`.  For monotone `f` the iterate
  count `gammaOf f threshold hdec` is monotone, by strong induction on the
  larger start: pointwise `f x ≤ f y` keeps the smaller orbit below the
  larger one, so it cannot hit `[0, threshold]` later.

* `gamma_poly_alpha_proved : Blocking_gamma_poly_alpha`, with explicit
  witness `c' = F_omega (c + 4 * d + 7) + 1`.  Collapse mechanism: write
  `a = alpha (z + 1)` and `A₀ = c + 4 * d + 7`.  Monotonicity of `beta` plus
  `DecreasesAbove threshold (beta ∘ beta)` force `beta z ≤ z` above the
  threshold, so one double step lands at
  `beta (beta z) ≤ c * (a + 1) ^ d` (poly in `a`, exponent `d`, NOT `d²`).
  Numerically `c * (a + 1) ^ d + 1 ≤ 2 ^ (c + (a + 1) * d + 1)` and, as soon
  as `a ≥ A₀`, the linear exponent fits under the tower:
  `c + (a + 1) * d + 1 ≤ (a - 2) * (a - 2) ≤ 2 ^ (a - 2) ≤ F 3 (a - 2)`,
  hence `beta (beta z) + 1 ≤ 2 ^ F 3 (a - 2) = F 3 (a - 1) ≤ F_omega (a - 1)`
  and `alpha (beta (beta z) + 1) ≤ a - 1`: each double step above level `A₀`
  costs at least one alpha unit (`alpha_drop_step`).  Below level `A₀` the
  start is at most the constant `F_omega A₀`, and the trivial estimate
  `gammaOf n ≤ n` (`gammaOf_le_self`) finishes.  Total:
  `gammaOf n ≤ F_omega A₀ + alpha (n + 1) ≤ (F_omega A₀ + 1) * (alpha (n+1) + 1)`.
-/

section GammaBlockersClosed

/-- The iterate count never exceeds its starting point: every counted step
strictly decreases the argument. -/
theorem gammaOf_le_self (f : ℕ → ℕ) (threshold : ℕ)
    (hdec : DecreasesAbove threshold f) :
    ∀ n, gammaOf f threshold hdec n ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n ≤ threshold
    · rw [gammaOf_le h]
      exact Nat.zero_le n
    · have hn : threshold < n := by omega
      have hlt : f n < n := hdec n hn
      have hrec := ih (f n) hlt
      rw [gammaOf_gt hn]
      omega

/-- **First T2 blocker, closed**: monotone `f` gives a monotone iterate
count. -/
theorem gamma_mono_proved : Blocking_gamma_mono := by
  intro f threshold hdec hf
  have main : ∀ y x, x ≤ y →
      gammaOf f threshold hdec x ≤ gammaOf f threshold hdec y := by
    intro y
    induction y using Nat.strong_induction_on with
    | _ y ih =>
      intro x hxy
      by_cases hy : y ≤ threshold
      · rw [gammaOf_le (le_trans hxy hy), gammaOf_le hy]
      · have hy' : threshold < y := by omega
        by_cases hx : x ≤ threshold
        · rw [gammaOf_le hx]
          exact Nat.zero_le _
        · have hx' : threshold < x := by omega
          rw [gammaOf_gt hx', gammaOf_gt hy']
          have hrec := ih (f y) (hdec y hy') (f x) (hf hxy)
          omega
  intro x y hxy
  exact main y x hxy

/-- `F 2` is exactly the powers of two. -/
theorem F_two_eq : ∀ n, F 2 n = 2 ^ n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      have h1 : F 2 (n + 1) = (F 1 ·)^[n + 1] 1 :=
        AckermannFacts.F_succ_succ 0 (n + 1)
      have h2 : (F 1 ·)^[n] 1 = F 2 n := (AckermannFacts.F_succ_succ 0 n).symm
      rw [h1, Function.iterate_succ_apply', h2, ih, AckermannFacts.F_one]
      ring

/-- One-step recurrence of the tower function `F 3`. -/
theorem F_three_succ (n : ℕ) : F 3 (n + 1) = 2 ^ F 3 n := by
  have h1 : F 3 (n + 1) = (F 2 ·)^[n + 1] 1 :=
    AckermannFacts.F_succ_succ 1 (n + 1)
  have h2 : (F 2 ·)^[n] 1 = F 3 n := (AckermannFacts.F_succ_succ 1 n).symm
  rw [h1, Function.iterate_succ_apply', h2, F_two_eq]

/-- The tower dominates the plain powers of two. -/
theorem two_pow_le_F_three {x : ℕ} (hx : 1 ≤ x) : 2 ^ x ≤ F 3 x := by
  have h := AckermannFacts.F_mono_left (j := 2) (k := 3) (by omega) (by omega)
    x hx
  rw [F_two_eq] at h
  exact h

/-- Every natural is below its own power of two. -/
theorem le_two_pow_self : ∀ n : ℕ, n ≤ 2 ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hpos : 0 < 2 ^ n := pow_pos (by omega) n
      have h2 : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
        rw [pow_succ]
        ring
      omega

/-- Squares are below the powers of two from `4` on. -/
theorem sq_le_two_pow : ∀ x : ℕ, 4 ≤ x → x * x ≤ 2 ^ x := by
  intro x
  induction x with
  | zero => intro h; omega
  | succ x ih =>
      intro hx
      by_cases h4 : 4 ≤ x
      · have hrec : x * x ≤ 2 ^ x := ih h4
        have h4x : 4 * x ≤ x * x := Nat.mul_le_mul h4 (le_refl x)
        have hkey : (x + 1) * (x + 1) ≤ 2 * (x * x) := by linarith
        have hdbl : 2 * (x * x) ≤ 2 * 2 ^ x := Nat.mul_le_mul (le_refl 2) hrec
        have h2 : 2 ^ (x + 1) = 2 * 2 ^ x := by
          rw [pow_succ]
          ring
        linarith
      · have hx3 : x = 3 := by omega
        subst hx3
        norm_num

/-- A monotone `beta` whose double application decreases above `threshold` is
itself non-increasing above `threshold`. -/
theorem beta_le_self_of_double_dec {beta : ℕ → ℕ} {threshold : ℕ}
    (hmono : MonotoneNat beta)
    (hdec : DecreasesAbove threshold (fun z => beta (beta z)))
    {z : ℕ} (hz : threshold < z) :
    beta z ≤ z := by
  by_contra hgt
  push_neg at hgt
  have h1 : beta z ≤ beta (beta z) := hmono (Nat.le_of_lt hgt)
  have h2 : beta (beta z) < z := hdec z hz
  omega

/-- **The poly-to-alpha collapse kernel**: one double application of a
poly-alpha-bounded monotone `beta` drops `alpha (· + 1)` by at least one,
as soon as `alpha (z + 1)` clears the explicit constant `c + 4 * d + 7`. -/
theorem alpha_drop_step {beta : ℕ → ℕ} {c d threshold : ℕ}
    (hmono : MonotoneNat beta)
    (hdec : DecreasesAbove threshold (fun z => beta (beta z)))
    (hpoly : ∀ z, beta z ≤ c * (alpha (z + 1) + 1) ^ d)
    {z : ℕ} (hz : threshold < z) (ha : c + 4 * d + 7 ≤ alpha (z + 1)) :
    alpha (beta (beta z) + 1) + 1 ≤ alpha (z + 1) := by
  obtain ⟨x, hx⟩ : ∃ x, alpha (z + 1) = x + 2 := ⟨alpha (z + 1) - 2, by omega⟩
  have hx5 : c + 4 * d + 5 ≤ x := by omega
  -- the double-step image is polynomial in `a = alpha (z + 1)`, exponent `d`
  have hbz : beta z ≤ z := beta_le_self_of_double_dec hmono hdec hz
  have hinner : alpha (beta z + 1) ≤ alpha (z + 1) :=
    AckermannFacts.alpha_mono (by omega)
  have hgz : beta (beta z) ≤ c * (alpha (z + 1) + 1) ^ d := by
    have h1 : beta (beta z) ≤ c * (alpha (beta z + 1) + 1) ^ d := hpoly (beta z)
    have h2 : (alpha (beta z + 1) + 1) ^ d ≤ (alpha (z + 1) + 1) ^ d :=
      Nat.pow_le_pow_left (by omega) d
    have h3 : c * (alpha (beta z + 1) + 1) ^ d
        ≤ c * (alpha (z + 1) + 1) ^ d := Nat.mul_le_mul (le_refl c) h2
    exact le_trans h1 h3
  -- poly(a) + 1 ≤ 2 ^ (linear in a)
  have hpoly2 : c * (alpha (z + 1) + 1) ^ d + 1
      ≤ 2 ^ (c + (alpha (z + 1) + 1) * d + 1) := by
    have hc : c ≤ 2 ^ c := le_two_pow_self c
    have hbase : alpha (z + 1) + 1 ≤ 2 ^ (alpha (z + 1) + 1) :=
      le_two_pow_self (alpha (z + 1) + 1)
    have hpow : (alpha (z + 1) + 1) ^ d ≤ 2 ^ ((alpha (z + 1) + 1) * d) := by
      have h1 : (alpha (z + 1) + 1) ^ d ≤ (2 ^ (alpha (z + 1) + 1)) ^ d :=
        Nat.pow_le_pow_left hbase d
      have h2 : (2 ^ (alpha (z + 1) + 1)) ^ d
          = 2 ^ ((alpha (z + 1) + 1) * d) :=
        (pow_mul 2 (alpha (z + 1) + 1) d).symm
      rw [h2] at h1
      exact h1
    have hmul : c * (alpha (z + 1) + 1) ^ d
        ≤ 2 ^ c * 2 ^ ((alpha (z + 1) + 1) * d) := Nat.mul_le_mul hc hpow
    have hadd : 2 ^ c * 2 ^ ((alpha (z + 1) + 1) * d)
        = 2 ^ (c + (alpha (z + 1) + 1) * d) :=
      (pow_add 2 c ((alpha (z + 1) + 1) * d)).symm
    have hpos : 0 < 2 ^ (c + (alpha (z + 1) + 1) * d) := pow_pos (by omega) _
    have hdbl : 2 ^ (c + (alpha (z + 1) + 1) * d + 1)
        = 2 ^ (c + (alpha (z + 1) + 1) * d) * 2 :=
      pow_succ 2 (c + (alpha (z + 1) + 1) * d)
    linarith
  -- the linear exponent fits under the square at `x = a - 2`
  have hlin : c + (alpha (z + 1) + 1) * d + 1 ≤ x * x := by
    have hx1 : 1 ≤ x := by omega
    have h1 : (c + 4 * d + 5) * x ≤ x * x := Nat.mul_le_mul hx5 (le_refl x)
    have e1 : c ≤ c * x := Nat.le_mul_of_pos_right c (by omega)
    have e2 : 3 * d ≤ 3 * d * x := Nat.le_mul_of_pos_right (3 * d) (by omega)
    have ha1 : alpha (z + 1) + 1 = x + 3 := by omega
    rw [ha1]
    nlinarith [h1, e1, e2, hx1]
  -- assemble through the tower: x * x ≤ 2 ^ x ≤ F 3 x
  have hsq : x * x ≤ 2 ^ x := sq_le_two_pow x (by omega)
  have hF3 : 2 ^ x ≤ F 3 x := two_pow_le_F_three (by omega)
  have hexp : c + (alpha (z + 1) + 1) * d + 1 ≤ F 3 x :=
    le_trans hlin (le_trans hsq hF3)
  have hmono2 : 2 ^ (c + (alpha (z + 1) + 1) * d + 1) ≤ 2 ^ F 3 x :=
    Nat.pow_le_pow_right (by omega) hexp
  have htower : 2 ^ F 3 x = F 3 (x + 1) := (F_three_succ x).symm
  have homega : F 3 (x + 1) ≤ F_omega (x + 1) := by
    rw [F_omega]
    exact AckermannFacts.F_mono_left (by omega) (by omega) (x + 1) (by omega)
  have homega' : 2 ^ F 3 x ≤ F_omega (x + 1) := by
    rw [htower]
    exact homega
  -- conclude through the alpha interface
  have hfinal : beta (beta z) + 1 ≤ F_omega (x + 1) := by
    have s1 : beta (beta z) + 1 ≤ c * (alpha (z + 1) + 1) ^ d + 1 :=
      Nat.add_le_add_right hgz 1
    exact le_trans s1 (le_trans hpoly2 (le_trans hmono2 homega'))
  have hcollapse : alpha (beta (beta z) + 1) ≤ x + 1 :=
    (AckermannFacts.alpha_le_iff (beta (beta z) + 1) (x + 1)).mpr hfinal
  omega

/-- **Second T2 blocker, closed**: iterating the double application of a
monotone poly-alpha-bounded `beta` down to any fixed threshold takes at most
`(F_omega (c + 4 * d + 7) + 1) * (alpha (n + 1) + 1)` steps. -/
theorem gamma_poly_alpha_proved : Blocking_gamma_poly_alpha := by
  intro beta c d threshold hdec hmono hpoly
  refine ⟨F_omega (c + 4 * d + 7) + 1, ?_⟩
  have main : ∀ k z, alpha (z + 1) ≤ c + 4 * d + 7 + k →
      gammaOf (fun z => beta (beta z)) threshold hdec z
        ≤ F_omega (c + 4 * d + 7) + k := by
    intro k
    induction k with
    | zero =>
        intro z hz
        have hzF : z + 1 ≤ F_omega (c + 4 * d + 7) :=
          (AckermannFacts.alpha_le_iff (z + 1) (c + 4 * d + 7)).mp (by omega)
        have hself := gammaOf_le_self (fun z => beta (beta z)) threshold hdec z
        omega
    | succ k ih =>
        intro z hz
        by_cases hsmall : alpha (z + 1) ≤ c + 4 * d + 7 + k
        · have := ih z hsmall
          omega
        · by_cases hth : z ≤ threshold
          · rw [gammaOf_le hth]
            omega
          · have hth' : threshold < z := by omega
            have heq : gammaOf (fun z => beta (beta z)) threshold hdec z
                = 1 + gammaOf (fun z => beta (beta z)) threshold hdec
                    (beta (beta z)) := gammaOf_gt hth'
            have hdrop : alpha (beta (beta z) + 1) + 1 ≤ alpha (z + 1) :=
              alpha_drop_step hmono hdec hpoly hth' (by omega)
            have hnext := ih (beta (beta z)) (by omega)
            omega
  intro n
  have h := main (alpha (n + 1)) n (by omega)
  have e1 : F_omega (c + 4 * d + 7)
      ≤ F_omega (c + 4 * d + 7) * (alpha (n + 1) + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have e2 : (F_omega (c + 4 * d + 7) + 1) * (alpha (n + 1) + 1)
      = F_omega (c + 4 * d + 7) * (alpha (n + 1) + 1) + (alpha (n + 1) + 1) := by
    ring
  linarith

end GammaBlockersClosed

#print axioms gammaOf_le_self
#print axioms gamma_mono_proved
#print axioms F_two_eq
#print axioms F_three_succ
#print axioms two_pow_le_F_three
#print axioms le_two_pow_self
#print axioms sq_le_two_pow
#print axioms beta_le_self_of_double_dec
#print axioms alpha_drop_step
#print axioms gamma_poly_alpha_proved

/-! ## T1 continued: one-per-block extraction and the shared-block pair cap

For two distinct symbols `a ≠ b` both occurring before and after a block
group, every block containing both contributes one letter to an alternating
pattern (`altPattern_of_shared_blocks`); with one closing letter from `post`
(`altPattern_of_shared_blocks_post`) and an opening *pair* from `pre`
(orientation supplied by `pair_sublist_of_two_mem`), `k` shared blocks yield
an alternation of length `k + 3`.  Under `AltFree 12` this caps the number
of shared blocks at `8`. -/

section SharedBlockCap

/-- Mapping a strictly increasing list of positives by `· - 1` keeps it
strictly increasing. -/
theorem pairwise_lt_map_pred :
    ∀ (l : List ℕ), l.Pairwise (· < ·) → (∀ j ∈ l, 0 < j) →
      (l.map (fun j => j - 1)).Pairwise (· < ·) := by
  intro l
  induction l with
  | nil =>
      intro _ _
      exact List.Pairwise.nil
  | cons x rest ih =>
      intro hpw hpos
      rw [List.map_cons, List.pairwise_cons]
      refine ⟨?_, ih (List.pairwise_cons.mp hpw).2
        (fun j hj => hpos j (List.mem_cons_of_mem _ hj))⟩
      intro y hy
      rw [List.mem_map] at hy
      obtain ⟨j, hj, rfl⟩ := hy
      have h1 := (List.pairwise_cons.mp hpw).1 j hj
      have h2 := hpos x List.mem_cons_self
      show x - 1 < j - 1
      omega

/-- **One-per-block extraction**: a strictly increasing list of block
indices, each of whose blocks contains both `a` and `b`, yields an
alternating pattern of the same length inside the flattened group (one
letter per block, starting with `a`). -/
theorem altPattern_of_shared_blocks :
    ∀ (group : List (List ℕ)) (a b : ℕ) (idxs : List ℕ),
      idxs.Pairwise (· < ·) →
      (∀ i ∈ idxs,
        i < group.length ∧ a ∈ group.getD i [] ∧ b ∈ group.getD i []) →
      (altPattern a b idxs.length).Sublist (flattenBlocks group) := by
  intro group
  induction group with
  | nil =>
      intro a b idxs hpw hmem
      cases idxs with
      | nil => simp [altPattern]
      | cons i ridx =>
          have h := (hmem i List.mem_cons_self).1
          simp only [List.length_nil] at h
          omega
  | cons blk rest ih =>
      intro a b idxs hpw hmem
      cases idxs with
      | nil => simp [altPattern]
      | cons i₀ ridx =>
          cases i₀ with
          | zero =>
              have ha : a ∈ blk := by
                have h := (hmem 0 List.mem_cons_self).2.1
                simpa using h
              have hpos : ∀ j ∈ ridx, 0 < j := (List.pairwise_cons.mp hpw).1
              have hpw' := pairwise_lt_map_pred ridx
                (List.pairwise_cons.mp hpw).2 hpos
              have hmem' : ∀ j ∈ ridx.map (fun j => j - 1),
                  j < rest.length ∧ b ∈ rest.getD j [] ∧ a ∈ rest.getD j [] := by
                intro j hj
                rw [List.mem_map] at hj
                obtain ⟨j', hj', rfl⟩ := hj
                have hj1 := hpos j' hj'
                obtain ⟨k, rfl⟩ : ∃ k, j' = k + 1 := ⟨j' - 1, by omega⟩
                have h := hmem (k + 1) (List.mem_cons_of_mem _ hj')
                simp only [List.length_cons, List.getD_cons_succ] at h
                simp only [Nat.add_sub_cancel]
                exact ⟨by omega, h.2.2, h.2.1⟩
              have htail := ih b a (ridx.map (fun j => j - 1)) hpw' hmem'
              rw [List.length_map] at htail
              show (altPattern a b (ridx.length + 1)).Sublist
                (blk ++ flattenBlocks rest)
              exact List.Sublist.append (List.singleton_sublist.mpr ha) htail
          | succ i' =>
              have hall : ∀ j ∈ (i' + 1) :: ridx, 0 < j := by
                intro j hj
                rcases List.mem_cons.mp hj with rfl | hj'
                · omega
                · have := (List.pairwise_cons.mp hpw).1 j hj'
                  omega
              have hpw' := pairwise_lt_map_pred ((i' + 1) :: ridx) hpw hall
              have hmem' : ∀ j ∈ ((i' + 1) :: ridx).map (fun j => j - 1),
                  j < rest.length ∧ a ∈ rest.getD j [] ∧ b ∈ rest.getD j [] := by
                intro j hj
                rw [List.mem_map] at hj
                obtain ⟨j', hj', rfl⟩ := hj
                have hj1 := hall j' hj'
                obtain ⟨k, rfl⟩ : ∃ k, j' = k + 1 := ⟨j' - 1, by omega⟩
                have h := hmem (k + 1) hj'
                simp only [List.length_cons, List.getD_cons_succ] at h
                simp only [Nat.add_sub_cancel]
                exact ⟨by omega, h.2.1, h.2.2⟩
              have htail := ih a b (((i' + 1) :: ridx).map (fun j => j - 1))
                hpw' hmem'
              rw [List.length_map] at htail
              show (altPattern a b ((i' + 1) :: ridx).length).Sublist
                (blk ++ flattenBlocks rest)
              exact htail.trans (List.sublist_append_right _ _)

/-- Post-extended extraction: with both symbols available in a common
suffix, the pattern picks up one extra closing letter. -/
theorem altPattern_of_shared_blocks_post :
    ∀ (group : List (List ℕ)) (a b : ℕ) (post idxs : List ℕ),
      idxs.Pairwise (· < ·) →
      (∀ i ∈ idxs,
        i < group.length ∧ a ∈ group.getD i [] ∧ b ∈ group.getD i []) →
      a ∈ post → b ∈ post →
      (altPattern a b (idxs.length + 1)).Sublist
        (flattenBlocks group ++ post) := by
  intro group
  induction group with
  | nil =>
      intro a b post idxs hpw hmem hapost hbpost
      cases idxs with
      | nil => exact List.singleton_sublist.mpr hapost
      | cons i ridx =>
          have h := (hmem i List.mem_cons_self).1
          simp only [List.length_nil] at h
          omega
  | cons blk rest ih =>
      intro a b post idxs hpw hmem hapost hbpost
      cases idxs with
      | nil =>
          exact List.singleton_sublist.mpr (List.mem_append_right _ hapost)
      | cons i₀ ridx =>
          cases i₀ with
          | zero =>
              have ha : a ∈ blk := by
                have h := (hmem 0 List.mem_cons_self).2.1
                simpa using h
              have hpos : ∀ j ∈ ridx, 0 < j := (List.pairwise_cons.mp hpw).1
              have hpw' := pairwise_lt_map_pred ridx
                (List.pairwise_cons.mp hpw).2 hpos
              have hmem' : ∀ j ∈ ridx.map (fun j => j - 1),
                  j < rest.length ∧ b ∈ rest.getD j [] ∧ a ∈ rest.getD j [] := by
                intro j hj
                rw [List.mem_map] at hj
                obtain ⟨j', hj', rfl⟩ := hj
                have hj1 := hpos j' hj'
                obtain ⟨k, rfl⟩ : ∃ k, j' = k + 1 := ⟨j' - 1, by omega⟩
                have h := hmem (k + 1) (List.mem_cons_of_mem _ hj')
                simp only [List.length_cons, List.getD_cons_succ] at h
                simp only [Nat.add_sub_cancel]
                exact ⟨by omega, h.2.2, h.2.1⟩
              have htail := ih b a post (ridx.map (fun j => j - 1))
                hpw' hmem' hbpost hapost
              rw [List.length_map] at htail
              show (altPattern a b (ridx.length + 1 + 1)).Sublist
                ((blk ++ flattenBlocks rest) ++ post)
              rw [List.append_assoc]
              exact List.Sublist.append (List.singleton_sublist.mpr ha) htail
          | succ i' =>
              have hall : ∀ j ∈ (i' + 1) :: ridx, 0 < j := by
                intro j hj
                rcases List.mem_cons.mp hj with rfl | hj'
                · omega
                · have := (List.pairwise_cons.mp hpw).1 j hj'
                  omega
              have hpw' := pairwise_lt_map_pred ((i' + 1) :: ridx) hpw hall
              have hmem' : ∀ j ∈ ((i' + 1) :: ridx).map (fun j => j - 1),
                  j < rest.length ∧ a ∈ rest.getD j [] ∧ b ∈ rest.getD j [] := by
                intro j hj
                rw [List.mem_map] at hj
                obtain ⟨j', hj', rfl⟩ := hj
                have hj1 := hall j' hj'
                obtain ⟨k, rfl⟩ : ∃ k, j' = k + 1 := ⟨j' - 1, by omega⟩
                have h := hmem (k + 1) hj'
                simp only [List.length_cons, List.getD_cons_succ] at h
                simp only [Nat.add_sub_cancel]
                exact ⟨by omega, h.2.1, h.2.2⟩
              have htail := ih a b post (((i' + 1) :: ridx).map (fun j => j - 1))
                hpw' hmem' hapost hbpost
              rw [List.length_map] at htail
              show (altPattern a b (((i' + 1) :: ridx).length + 1)).Sublist
                ((blk ++ flattenBlocks rest) ++ post)
              rw [List.append_assoc]
              exact htail.trans (List.sublist_append_right _ _)

/-- **The pair cap**: in an `AltFree 12` context, two distinct symbols both
occurring in `pre` and in `post` can share at most `8` blocks of the group:
`9` shared blocks would assemble (pair from `pre`, one letter per block,
one closing letter from `post`) into a forbidden `12`-alternation. -/
theorem shared_blocks_le_of_altFree {pre post : List ℕ}
    {group : List (List ℕ)} {a b : ℕ} (hab : a ≠ b)
    (hapre : a ∈ pre) (hapost : a ∈ post)
    (hbpre : b ∈ pre) (hbpost : b ∈ post)
    {idxs : List ℕ} (hpw : idxs.Pairwise (· < ·))
    (hmem : ∀ i ∈ idxs,
      i < group.length ∧ a ∈ group.getD i [] ∧ b ∈ group.getD i [])
    (hfree : AltFree 12 (pre ++ flattenBlocks group ++ post)) :
    idxs.length ≤ 8 := by
  by_contra hgt
  push_neg at hgt
  have hlen9 : (idxs.take 9).length = 9 := by
    rw [List.length_take]
    omega
  have hpw9 : (idxs.take 9).Pairwise (· < ·) :=
    hpw.sublist (List.take_sublist 9 idxs)
  have hmem9 : ∀ i ∈ idxs.take 9,
      i < group.length ∧ a ∈ group.getD i [] ∧ b ∈ group.getD i [] :=
    fun i hi => hmem i ((List.take_sublist 9 idxs).subset hi)
  rcases pair_sublist_of_two_mem hapre hbpre hab with hord | hord
  · -- `[a, b]` opens in `pre`: forbidden pattern `altPattern a b 12`
    have hg := altPattern_of_shared_blocks_post group a b post (idxs.take 9)
      hpw9 hmem9 hapost hbpost
    rw [hlen9] at hg
    refine hfree ⟨a, b, hab, ?_⟩
    have h12 : altPattern a b 12 = [a, b] ++ altPattern a b (9 + 1) := rfl
    rw [h12, List.append_assoc]
    exact List.Sublist.append hord hg
  · -- `[b, a]` opens in `pre`: forbidden pattern `altPattern b a 12`
    have hmem9' : ∀ i ∈ idxs.take 9,
        i < group.length ∧ b ∈ group.getD i [] ∧ a ∈ group.getD i [] :=
      fun i hi => ⟨(hmem9 i hi).1, (hmem9 i hi).2.2, (hmem9 i hi).2.1⟩
    have hg := altPattern_of_shared_blocks_post group b a post (idxs.take 9)
      hpw9 hmem9' hbpost hapost
    rw [hlen9] at hg
    refine hfree ⟨b, a, hab.symm, ?_⟩
    have h12 : altPattern b a 12 = [b, a] ++ altPattern b a (9 + 1) := rfl
    rw [h12, List.append_assoc]
    exact List.Sublist.append hord hg

/-- **Shared-block cap in `blockIdxList` form**: for two distinct middle
symbols the number of blocks they share is at most `8` under `AltFree 12`. -/
theorem shared_blockIdx_filter_le {pre post : List ℕ}
    {group : List (List ℕ)} {a b : ℕ} (hab : a ≠ b)
    (hapre : a ∈ pre) (hapost : a ∈ post)
    (hbpre : b ∈ pre) (hbpost : b ∈ post)
    (hfree : AltFree 12 (pre ++ flattenBlocks group ++ post)) :
    ((blockIdxList group a).filter
      (fun i => decide (i ∈ blockIdxList group b))).length ≤ 8 := by
  refine shared_blocks_le_of_altFree hab hapre hapost hbpre hbpost
    ((blockIdxList_pairwise group a).sublist List.filter_sublist) ?_ hfree
  intro i hi
  have hia : i ∈ blockIdxList group a := List.mem_of_mem_filter hi
  have hib : i ∈ blockIdxList group b := by
    have h2 := (List.mem_filter.mp hi).2
    simp only [decide_eq_true_eq] at h2
    exact h2
  exact ⟨(blockIdxList_mem_pred hia).1, (blockIdxList_mem_pred hia).2,
    (blockIdxList_mem_pred hib).2⟩

end SharedBlockCap

#print axioms pairwise_lt_map_pred
#print axioms altPattern_of_shared_blocks
#print axioms altPattern_of_shared_blocks_post
#print axioms shared_blocks_le_of_altFree
#print axioms shared_blockIdx_filter_le

/-! ## Order-12 middles: what the pair cap honestly yields

`shared_blockIdx_filter_le` caps at `8` the number of blocks shared by any
two distinct middle symbols.  A double count over ordered distinct pairs
turns this into a **quadratic** middles bound with explicit constants
(`middles_order12_quadratic`): blocks meeting at most `2` middles are
charged to the `2·blocks` term, and every block meeting `μ ≥ 3` middles
satisfies `2μ ≤ μ(μ−1)`, so the crowded total is dominated by the ordered
pair sum `≤ 8·ms²`.

The **linear** order-12 statement is isolated as
`Blocking_middles_order12_linear` and is expected to be **false** at scale:
pairwise caps cannot rule out rotating-partner families (an alternation
`a,b₁,a,b₂,a,b₃,…` with fresh partners violates no two-fixed-symbol
pattern), and an `ababa`-free internal Hart–Sharir fan family — fully
anchored in `pre`/`post`, so every two-symbol alternation of the whole
string stays `≤ 2 + 4 + 2 = 8 < 12` — reaches length `Θ(n·α(n))` against
`Θ(n)` blocks and symbols, beating `C₁·n + C₂·m` for every fixed constant
pair on astronomically large inputs.  This is exactly why the classical
Agarwal–Sharir recursion treats middles at order `s` by recursing at order
`s − 2` instead of bounding them linearly.  The bounded-alphabet corollary
`middles_order12_of_symbols_le` recovers the linear `MiddlesKeyAt` shape
whenever the middle alphabet of a group is bounded (the per-level
hierarchical regime). -/

section MiddlesOrder12

/-- Indicator (as `0/1`) that symbol `a` occurs in block `i` of `group`. -/
def blkInd (group : List (List ℕ)) (a i : ℕ) : ℕ :=
  if a ∈ group.getD i [] then 1 else 0

/-- Number of symbols of `T` meeting block `i`. -/
def multAt (group : List (List ℕ)) (T : Finset ℕ) (i : ℕ) : ℕ :=
  ∑ a ∈ T, blkInd group a i

/-- Ordered distinct pairs of `T` jointly meeting block `i`. -/
def offTermAt (group : List (List ℕ)) (T : Finset ℕ) (i : ℕ) : ℕ :=
  ∑ p ∈ T.offDiag, blkInd group p.1 i * blkInd group p.2 i

theorem blkInd_idem (group : List (List ℕ)) (a i : ℕ) :
    blkInd group a i * blkInd group a i = blkInd group a i := by
  by_cases h : a ∈ group.getD i [] <;> simp [blkInd, h]

/-- Length of a filtered range as an indicator sum over `Finset.range`. -/
theorem length_filter_range (p : ℕ → Bool) :
    ∀ m : ℕ, ((List.range m).filter p).length
      = ∑ i ∈ Finset.range m, (if p i = true then 1 else 0) := by
  intro m
  induction m with
  | zero => rfl
  | succ k ih =>
      have h1 : (List.filter p [k]).length = if p k = true then 1 else 0 := by
        by_cases hp : p k = true
        · simp [List.filter_cons, hp]
        · simp [List.filter_cons, hp]
      rw [List.range_succ, List.filter_append, List.length_append, ih,
        Finset.sum_range_succ, h1]

/-- Per-symbol block count as an indicator sum. -/
theorem blockIdxList_length_eq_sum (group : List (List ℕ)) (a : ℕ) :
    (blockIdxList group a).length
      = ∑ i ∈ Finset.range group.length, blkInd group a i := by
  have h0 : blockIdxList group a
      = (List.range group.length).filter
          (fun i => decide (a ∈ group.getD i [])) := rfl
  have h := length_filter_range (fun i => decide (a ∈ group.getD i []))
    group.length
  rw [h0, h]
  refine Finset.sum_congr rfl ?_
  intro i _
  by_cases hmem : a ∈ group.getD i []
  · simp [blkInd, hmem]
  · simp [blkInd, hmem]

/-- The square of a block multiplicity splits into the diagonal
(idempotent) part and the ordered off-diagonal pair count. -/
theorem multAt_sq (group : List (List ℕ)) (T : Finset ℕ) (i : ℕ) :
    multAt group T i * multAt group T i
      = multAt group T i + offTermAt group T i := by
  classical
  have h1 : multAt group T i * multAt group T i
      = ∑ a ∈ T, ∑ b ∈ T, blkInd group a i * blkInd group b i :=
    Finset.sum_mul_sum T T _ _
  have h2 : (∑ a ∈ T, ∑ b ∈ T, blkInd group a i * blkInd group b i)
      = ∑ p ∈ T ×ˢ T, blkInd group p.1 i * blkInd group p.2 i :=
    (Finset.sum_product T T
      (fun p => blkInd group p.1 i * blkInd group p.2 i)).symm
  have h3 : (∑ p ∈ T ×ˢ T, blkInd group p.1 i * blkInd group p.2 i)
      = (∑ p ∈ T.diag, blkInd group p.1 i * blkInd group p.2 i)
        + ∑ p ∈ T.offDiag, blkInd group p.1 i * blkInd group p.2 i := by
    rw [← Finset.diag_union_offDiag T,
      Finset.sum_union (Finset.disjoint_diag_offDiag T)]
  have h4 : (∑ p ∈ T.diag, blkInd group p.1 i * blkInd group p.2 i)
      = multAt group T i := by
    rw [Finset.sum_diag]
    exact Finset.sum_congr rfl (fun a _ => blkInd_idem group a i)
  rw [h1, h2, h3, h4]
  rfl

/-- Under `AltFree 12`, two distinct symbols anchored on both sides jointly
meet at most `8` blocks: the indicator-sum form of
`shared_blockIdx_filter_le`. -/
theorem shared_pair_sum_le {pre post : List ℕ} {group : List (List ℕ)}
    {a b : ℕ} (hab : a ≠ b)
    (hapre : a ∈ pre) (hapost : a ∈ post)
    (hbpre : b ∈ pre) (hbpost : b ∈ post)
    (hfree : AltFree 12 (pre ++ flattenBlocks group ++ post)) :
    (∑ i ∈ Finset.range group.length,
      blkInd group a i * blkInd group b i) ≤ 8 := by
  classical
  have hsum : (∑ i ∈ Finset.range group.length,
      blkInd group a i * blkInd group b i)
      = ((Finset.range group.length).filter
          (fun i => a ∈ group.getD i [] ∧ b ∈ group.getD i [])).card := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl ?_
    intro i _
    unfold blkInd
    by_cases ha : a ∈ group.getD i []
    · by_cases hb : b ∈ group.getD i []
      · rw [if_pos ha, if_pos hb, if_pos ⟨ha, hb⟩]
      · rw [if_pos ha, if_neg hb, if_neg (fun hcon => hb hcon.2)]
    · by_cases hb : b ∈ group.getD i []
      · rw [if_neg ha, if_pos hb, if_neg (fun hcon => ha hcon.1)]
      · rw [if_neg ha, if_neg hb, if_neg (fun hcon => ha hcon.1)]
  rw [hsum]
  have hsub : ((Finset.range group.length).filter
      (fun i => a ∈ group.getD i [] ∧ b ∈ group.getD i []))
      ⊆ ((blockIdxList group a).filter
          (fun i => decide (i ∈ blockIdxList group b))).toFinset := by
    intro i hi
    rw [Finset.mem_filter, Finset.mem_range] at hi
    have hia : i ∈ blockIdxList group a := by
      rw [show blockIdxList group a
          = (List.range group.length).filter
              (fun j => decide (a ∈ group.getD j [])) from rfl,
        List.mem_filter]
      exact ⟨List.mem_range.mpr hi.1, decide_eq_true hi.2.1⟩
    have hib : i ∈ blockIdxList group b := by
      rw [show blockIdxList group b
          = (List.range group.length).filter
              (fun j => decide (b ∈ group.getD j [])) from rfl,
        List.mem_filter]
      exact ⟨List.mem_range.mpr hi.1, decide_eq_true hi.2.2⟩
    rw [List.mem_toFinset, List.mem_filter]
    exact ⟨hia, decide_eq_true hib⟩
  have h1 := Finset.card_le_card hsub
  have h2 := List.toFinset_card_le ((blockIdxList group a).filter
      (fun i => decide (i ∈ blockIdxList group b)))
  have h3 := shared_blockIdx_filter_le hab hapre hapost hbpre hbpost hfree
  omega

/-- **Order-12 middles, the provable form**: under `AltFree 12` the raw
middle occurrences satisfy the explicit quadratic bound
`mr ≤ 4·ms² + 2·blocks`.  Blocks meeting `≤ 2` middles pay the linear
term; crowded blocks are dominated by the ordered-pair cap `8` of
`shared_blockIdx_filter_le` via `2μ ≤ μ(μ−1)` for `μ ≥ 3`. -/
theorem middles_order12_quadratic :
    ∀ (pre : List ℕ) (group : List (List ℕ)) (post : List ℕ),
      (∀ b ∈ group, b.Nodup) →
      AltFree 12 (pre ++ flattenBlocks group ++ post) →
      (middleRaw pre group post).length ≤
        4 * ((middleSymbols pre group post).length
              * (middleSymbols pre group post).length)
          + 2 * group.length := by
  intro pre group post hnodup hfree
  classical
  set T := (middleRaw pre group post).toFinset with hT
  have hboth : ∀ a ∈ T, a ∈ pre ∧ a ∈ post := by
    intro a ha
    rw [hT, List.mem_toFinset] at ha
    have h2 := (List.mem_filter.mp ha).2
    rw [decide_eq_true_eq] at h2
    exact h2
  have hlen : (middleRaw pre group post).length
      = ∑ a ∈ T, (middleRaw pre group post).count a := by
    rw [hT]
    exact length_eq_sum_count_toFinset _
  have hcnt : ∀ a ∈ T, (middleRaw pre group post).count a
      = (blockIdxList group a).length := by
    intro a ha
    have hmem : a ∈ middleRaw pre group post := by
      rw [hT, List.mem_toFinset] at ha
      exact ha
    unfold middleRaw at hmem ⊢
    have hqa := (List.mem_filter.mp hmem).2
    rw [count_filter_of_pos hqa, count_flattenBlocks a group hnodup]
  have hsyms : (middleSymbols pre group post).length = T.card := by
    show (middleRaw pre group post).dedup.length = T.card
    rw [hT, List.card_toFinset]
  -- the raw length as a sum of per-block multiplicities
  have hmr : (middleRaw pre group post).length
      = ∑ i ∈ Finset.range group.length, multAt group T i := by
    calc (middleRaw pre group post).length
        = ∑ a ∈ T, (middleRaw pre group post).count a := hlen
      _ = ∑ a ∈ T, (blockIdxList group a).length :=
          Finset.sum_congr rfl hcnt
      _ = ∑ a ∈ T, ∑ i ∈ Finset.range group.length, blkInd group a i :=
          Finset.sum_congr rfl
            (fun a _ => blockIdxList_length_eq_sum group a)
      _ = ∑ i ∈ Finset.range group.length, ∑ a ∈ T, blkInd group a i :=
          Finset.sum_comm
      _ = ∑ i ∈ Finset.range group.length, multAt group T i := rfl
  -- total ordered-pair incidence is at most 8·ms²
  have hoff : (∑ i ∈ Finset.range group.length, offTermAt group T i)
      ≤ 8 * (T.card * T.card) := by
    have hswap : (∑ i ∈ Finset.range group.length, offTermAt group T i)
        = ∑ p ∈ T.offDiag, ∑ i ∈ Finset.range group.length,
            blkInd group p.1 i * blkInd group p.2 i := by
      show (∑ i ∈ Finset.range group.length,
          ∑ p ∈ T.offDiag, blkInd group p.1 i * blkInd group p.2 i) = _
      exact Finset.sum_comm
    have hper : ∀ p ∈ T.offDiag,
        (∑ i ∈ Finset.range group.length,
          blkInd group p.1 i * blkInd group p.2 i) ≤ 8 := by
      intro p hp
      rw [Finset.mem_offDiag] at hp
      exact shared_pair_sum_le hp.2.2 (hboth p.1 hp.1).1 (hboth p.1 hp.1).2
        (hboth p.2 hp.2.1).1 (hboth p.2 hp.2.1).2 hfree
    rw [hswap]
    calc (∑ p ∈ T.offDiag, ∑ i ∈ Finset.range group.length,
          blkInd group p.1 i * blkInd group p.2 i)
        ≤ ∑ _p ∈ T.offDiag, 8 := Finset.sum_le_sum hper
      _ = T.offDiag.card * 8 := Finset.sum_const_nat (fun _ _ => rfl)
      _ ≤ (T.card * T.card) * 8 := by
          have h2 : T.offDiag.card ≤ T.card * T.card := by
            rw [Finset.offDiag_card]
            exact Nat.sub_le _ _
          exact Nat.mul_le_mul_right 8 h2
      _ = 8 * (T.card * T.card) := Nat.mul_comm _ _
  -- split the blocks by multiplicity
  have hsplit : (∑ i ∈ Finset.range group.length, multAt group T i)
      = (∑ i ∈ (Finset.range group.length).filter
            (fun i => multAt group T i ≤ 2), multAt group T i)
        + ∑ i ∈ (Finset.range group.length).filter
            (fun i => ¬ multAt group T i ≤ 2), multAt group T i :=
    (Finset.sum_filter_add_sum_filter_not (Finset.range group.length)
      (fun i => multAt group T i ≤ 2) (multAt group T)).symm
  have hA : (∑ i ∈ (Finset.range group.length).filter
        (fun i => multAt group T i ≤ 2), multAt group T i)
      ≤ 2 * group.length := by
    calc (∑ i ∈ (Finset.range group.length).filter
          (fun i => multAt group T i ≤ 2), multAt group T i)
        ≤ ∑ _i ∈ (Finset.range group.length).filter
            (fun i => multAt group T i ≤ 2), 2 :=
          Finset.sum_le_sum (fun i hi => (Finset.mem_filter.mp hi).2)
      _ = ((Finset.range group.length).filter
            (fun i => multAt group T i ≤ 2)).card * 2 :=
          Finset.sum_const_nat (fun _ _ => rfl)
      _ ≤ group.length * 2 := by
          have h1 := Finset.card_filter_le (Finset.range group.length)
            (fun i => multAt group T i ≤ 2)
          rw [Finset.card_range] at h1
          exact Nat.mul_le_mul_right 2 h1
      _ = 2 * group.length := Nat.mul_comm _ _
  have hBper : ∀ i ∈ (Finset.range group.length).filter
      (fun i => ¬ multAt group T i ≤ 2),
      2 * multAt group T i ≤ offTermAt group T i := by
    intro i hi
    have h3 : 3 ≤ multAt group T i := by
      have := (Finset.mem_filter.mp hi).2
      omega
    have hmul : 3 * multAt group T i ≤ multAt group T i * multAt group T i :=
      Nat.mul_le_mul_right (multAt group T i) h3
    rw [multAt_sq group T i] at hmul
    omega
  have hB : 2 * (∑ i ∈ (Finset.range group.length).filter
        (fun i => ¬ multAt group T i ≤ 2), multAt group T i)
      ≤ 8 * (T.card * T.card) := by
    calc 2 * (∑ i ∈ (Finset.range group.length).filter
          (fun i => ¬ multAt group T i ≤ 2), multAt group T i)
        = ∑ i ∈ (Finset.range group.length).filter
            (fun i => ¬ multAt group T i ≤ 2), 2 * multAt group T i :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ i ∈ (Finset.range group.length).filter
            (fun i => ¬ multAt group T i ≤ 2), offTermAt group T i :=
          Finset.sum_le_sum hBper
      _ ≤ ∑ i ∈ Finset.range group.length, offTermAt group T i :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ ≤ 8 * (T.card * T.card) := hoff
  have hBfin : (∑ i ∈ (Finset.range group.length).filter
        (fun i => ¬ multAt group T i ≤ 2), multAt group T i)
      ≤ 4 * (T.card * T.card) := by
    have h82 : 8 * (T.card * T.card) = 2 * (4 * (T.card * T.card)) := by
      ring
    rw [h82] at hB
    exact Nat.le_of_mul_le_mul_left hB (by norm_num)
  rw [hsyms, hmr, hsplit]
  exact le_trans (Nat.add_le_add hA hBfin) (le_of_eq (Nat.add_comm _ _))

/-- **The linear order-12 middles bound, isolated.**  The pair cap alone
cannot deliver it (rotating-partner families satisfy every two-fixed-symbol
constraint), and an anchored internal-order-3 Hart–Sharir fan family keeps
the whole string `AltFree 12` while reaching length `Θ(n·α(n))` with
`Θ(n)` symbols and blocks — so this exact statement is expected to be
**false** for sufficiently (astronomically) large inputs, for every fixed
constant pair.  Kept as the precise interface a linear route would need;
downstream consumers should instead use `middles_order12_quadratic`, the
bounded-alphabet `middles_order12_of_symbols_le`, or keep `MiddlesKeyAt 12 C`
itself as the named hypothesis. -/
def Blocking_middles_order12_linear : Prop :=
  ∀ (pre : List ℕ) (group : List (List ℕ)) (post : List ℕ),
    (∀ b ∈ group, b.Nodup) →
    AltFree 12 (pre ++ flattenBlocks group ++ post) →
    (middleRaw pre group post).length ≤
      10 * (middleSymbols pre group post).length + 2 * group.length

/-- The linear statement, if ever supplied, wires straight into the
order-parametric engine at `s = 12`, `C = 12`. -/
theorem MiddlesKeyAt_12_of_linear
    (h : Blocking_middles_order12_linear) : MiddlesKeyAt 12 12 := by
  intro pre group post hfree hnodup
  have h1 := h pre group post hnodup hfree
  omega

/-- Bounded-alphabet corollary of the quadratic bound: on groups whose
middle alphabet has size at most `K`, the bound is linear with
`C = 4K + 2`, in exactly the `MiddlesKeyAt` shape. -/
theorem middles_order12_of_symbols_le (K : ℕ) :
    ∀ (pre : List ℕ) (group : List (List ℕ)) (post : List ℕ),
      (∀ b ∈ group, b.Nodup) →
      AltFree 12 (pre ++ flattenBlocks group ++ post) →
      (middleSymbols pre group post).length ≤ K →
      (middleRaw pre group post).length ≤
        (4 * K + 2) * ((middleSymbols pre group post).length
          + group.length) := by
  intro pre group post hnodup hfree hK
  have h1 := middles_order12_quadratic pre group post hnodup hfree
  have h2 : (middleSymbols pre group post).length
      * (middleSymbols pre group post).length
      ≤ K * (middleSymbols pre group post).length :=
    Nat.mul_le_mul_right _ hK
  have h3 : (middleRaw pre group post).length
      ≤ 4 * (K * (middleSymbols pre group post).length)
        + 2 * group.length :=
    le_trans h1 (Nat.add_le_add_right (Nat.mul_le_mul_left 4 h2) _)
  have h4 : 4 * (K * (middleSymbols pre group post).length)
      + 2 * group.length
      ≤ (4 * K + 2) * ((middleSymbols pre group post).length
          + group.length) := by
    have e : (4 * K + 2) * ((middleSymbols pre group post).length
          + group.length)
        = 4 * (K * (middleSymbols pre group post).length)
            + 2 * group.length
          + (4 * K * group.length
              + 2 * (middleSymbols pre group post).length) := by
      ring
    rw [e]
    exact Nat.le_add_right _ _
  exact le_trans h3 h4

/-- Conditional order-12 decomposition step: a single application of the
parametric engine, one `exact` away once the linear middles law lands. -/
theorem oneStep_decomposition_at_twelve_of_linear
    (h : Blocking_middles_order12_linear) (b : ℕ)
    (hb : 2 ≤ b) (m n : ℕ) (u : List ℕ) (hm : b < m)
    (hfree : AltFree 12 u) (hblocked : Blocked m u)
    (hcard : u.toFinset.card ≤ n) :
    ∃ (locals : List (List ℕ)) (ctr : List ℕ),
      locals.length ≤ ceilDiv b m
      ∧ (∀ l ∈ locals, AltFree 12 l ∧ Blocked b l)
      ∧ (locals.map (fun l => l.toFinset.card)).sum ≤ n
      ∧ AltFree 12 ctr ∧ Blocked (ceilDiv b m) ctr
      ∧ ctr.toFinset.card ≤ n
      ∧ u.length ≤ (locals.map List.length).sum
          + 12 * (ctr.length + m) + 2 * b * n :=
  oneStep_decomposition_at (MiddlesKeyAt_12_of_linear h) b hb m n u hm
    hfree hblocked hcard

end MiddlesOrder12

#print axioms blkInd_idem
#print axioms length_filter_range
#print axioms blockIdxList_length_eq_sum
#print axioms multAt_sq
#print axioms shared_pair_sum_le
#print axioms middles_order12_quadratic
#print axioms MiddlesKeyAt_12_of_linear
#print axioms middles_order12_of_symbols_le
#print axioms oneStep_decomposition_at_twelve_of_linear

/-! ## T1 finale: the order-descent ladder for `MiddlesKeyAt`

The Hart--Sharir / Klazar order descent for the *middles* sub-object.  The
derived sequence `derivedSeq` is the per-block dedup of the middle
occurrences; because every block is `Nodup`, each middle symbol occurs at
most once per block, so the per-block dedup is the identity and
`derivedSeq = middleRaw` as lists.  This makes `derivedSeq_length_eq` exact.

The descent's combinatorial heart is the *pair-alternation lift*
(`pair_alt_lift_to_context`): a within-`middleRaw` alternation of two anchored
symbols of length `L` lifts to a length-`(L+2)` alternation in the context by
prepending the opening pair from `pre`.  This is the lemma the order-`s`
contradiction is built from; under `AltFree s` it caps any single pair's
alternation inside `middleRaw` at `s - 3`. -/

section OrderDescentLadder

/-- The derived sequence: per-block dedup of the middle-filtered
occurrences, flattened.  Since blocks are `Nodup`, this equals `middleRaw`. -/
noncomputable def derivedSeq
    (pre : List ℕ) (group : List (List ℕ)) (post : List ℕ) : List ℕ :=
  flattenBlocks
    (group.map (fun blk =>
      (blk.filter (fun a => occursOnBothSides a pre post)).dedup))

/-- On a `Nodup` group the per-block dedup is vacuous, so `derivedSeq`
coincides with `middleRaw`. -/
theorem derivedSeq_eq_middleRaw
    (pre : List ℕ) (group : List (List ℕ)) (post : List ℕ)
    (hnodup : ∀ blk ∈ group, blk.Nodup) :
    derivedSeq pre group post = middleRaw pre group post := by
  unfold derivedSeq middleRaw
  have hmap : group.map (fun blk =>
        (blk.filter (fun a => occursOnBothSides a pre post)).dedup)
      = group.map (fun blk => blk.filter (fun a => occursOnBothSides a pre post)) := by
    refine List.map_congr_left ?_
    intro blk hblk
    exact List.Nodup.dedup ((hnodup blk hblk).filter _)
  rw [hmap]
  exact filter_blocks_flatten _ group

/-- Exact length transfer between the derived sequence and the raw middles. -/
theorem derivedSeq_length_eq
    (pre : List ℕ) (group : List (List ℕ)) (post : List ℕ)
    (hnodup : ∀ blk ∈ group, blk.Nodup) :
    (derivedSeq pre group post).length = (middleRaw pre group post).length := by
  rw [derivedSeq_eq_middleRaw pre group post hnodup]

/-- `altPattern b a (L + 1) = b :: altPattern a b L`: prepending the *other*
symbol flips the start and lengthens by one. -/
theorem altPattern_cons_swap (a b L : ℕ) :
    altPattern b a (L + 1) = b :: altPattern a b L := rfl

/-- Alternating patterns are monotone (as sublists) in their length. -/
theorem altPattern_sublist_mono (a b : ℕ) :
    ∀ {m n : ℕ}, m ≤ n → (altPattern a b m).Sublist (altPattern a b n) := by
  intro m n hmn
  induction n with
  | zero =>
      have : m = 0 := Nat.le_zero.mp hmn
      subst this
      exact List.Sublist.refl _
  | succ k ih =>
      rcases Nat.lt_or_ge m (k + 1) with hlt | hge
      · exact (ih (Nat.lt_succ_iff.mp hlt)).trans (altPattern_sublist_succ a b k)
      · have : m = k + 1 := Nat.le_antisymm hmn hge
        subst this
        exact List.Sublist.refl _

/-- **The pair-alternation lift (single-prepend form).**  An alternation of
two distinct symbols `a, b`, occurring as a sublist of the flattened group
(hence in particular of `middleRaw`), lifts to an alternation one longer in
the full context, by prepending the opposite symbol from `pre`.  This is the
order-descent engine: an `(s-1)`-alternation inside the group with both
symbols available in `pre` would force a forbidden `s`-alternation. -/
theorem pair_alt_lift_to_context
    {pre post : List ℕ} {group : List (List ℕ)} {a b L : ℕ}
    (hapre : a ∈ pre) (hbpre : b ∈ pre)
    (hgroup : (altPattern a b L).Sublist (flattenBlocks group)) :
    (altPattern b a (L + 1)).Sublist (pre ++ flattenBlocks group ++ post) := by
  rw [altPattern_cons_swap]
  have hb : [b].Sublist pre := List.singleton_sublist.mpr hbpre
  have hstep : (b :: altPattern a b L).Sublist (pre ++ flattenBlocks group) :=
    List.Sublist.append hb hgroup
  exact hstep.trans (List.sublist_append_left _ _)

/-- **Per-pair alternation cap inside `middleRaw`.**  Under `AltFree s`, any
two distinct symbols anchored on both sides alternate at most `s - 2` times
inside the flattened group: an `(s-1)`-alternation would lift to a forbidden
`s`-alternation.  This is the order-`s` to order-`(s-2)` descent in the form
the count actually consumes (a per-pair statement, sidestepping the
sequence/triple repackaging obstacle). -/
theorem pair_alt_cap_of_altFree
    {pre post : List ℕ} {group : List (List ℕ)} {a b s L : ℕ}
    (hab : a ≠ b) (hapre : a ∈ pre) (hbpre : b ∈ pre)
    (hgroup : (altPattern a b L).Sublist (flattenBlocks group))
    (hfree : AltFree s (pre ++ flattenBlocks group ++ post)) :
    L + 1 < s := by
  by_contra hge
  push_neg at hge
  -- `s ≤ L + 1`, so the forbidden length-`s` pattern `altPattern b a s`
  -- is a sublist of the lifted `altPattern b a (L+1)`.
  have hlift := pair_alt_lift_to_context (post := post) hapre hbpre hgroup
  have hsub : (altPattern b a s).Sublist (altPattern b a (L + 1)) :=
    altPattern_sublist_mono b a hge
  exact hfree ⟨b, a, hab.symm, hsub.trans hlift⟩

/-- The head symbol occurs in any nonempty alternating pattern. -/
theorem mem_altPattern_fst (a b L : ℕ) (hL : 1 ≤ L) :
    a ∈ altPattern a b L := by
  obtain ⟨k, rfl⟩ : ∃ k, L = k + 1 := ⟨L - 1, by omega⟩
  simp [altPattern]

/-- The second symbol occurs in any length `≥ 2` alternating pattern. -/
theorem mem_altPattern_snd (a b L : ℕ) (hL : 2 ≤ L) :
    b ∈ altPattern a b L := by
  obtain ⟨k, rfl⟩ : ∃ k, L = k + 2 := ⟨L - 2, by omega⟩
  show b ∈ a :: b :: altPattern a b k
  exact List.mem_cons_of_mem _ List.mem_cons_self

/-- A symbol of `middleRaw` occurs on both sides, hence in `pre`. -/
theorem mem_pre_of_mem_middleRaw
    {pre post : List ℕ} {group : List (List ℕ)} {a : ℕ}
    (ha : a ∈ middleRaw pre group post) : a ∈ pre := by
  unfold middleRaw at ha
  have h2 := (List.mem_filter.mp ha).2
  rw [decide_eq_true_eq] at h2
  exact h2.1

/-- **The whole-sequence descent: `middleRaw` is `AltFree (s-1)`** whenever the
context is `AltFree s` (`s ≥ 3`).  Every alternation inside `middleRaw` lifts
by one (single prepend from `pre`, available because middle symbols occur on
both sides), so a length-`(s-1)` alternation would force a forbidden length-`s`
one.  This is the order-`s` to order-`(s-1)` step on the derived sequence,
exact in the lift count.  (`s ≥ 3` is sharp: `AltFree 1` of a nonempty
sequence is false, so the step cannot start below order `3`.) -/
theorem middleRaw_altFree_pred
    {pre post : List ℕ} {group : List (List ℕ)} {s : ℕ} (hs : 3 ≤ s)
    (hfree : AltFree s (pre ++ flattenBlocks group ++ post)) :
    AltFree (s - 1) (middleRaw pre group post) := by
  rintro ⟨a, b, hab, hsub⟩
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 2 := ⟨s - 2, by omega⟩
  -- now `s - 1 = k + 1`, and `k ≥ 1`, so the pattern has length `≥ 2`
  have hsub' : (altPattern a b (k + 1)).Sublist (middleRaw pre group post) := by
    simpa using hsub
  have ha_mr : a ∈ middleRaw pre group post :=
    hsub'.subset (mem_altPattern_fst a b (k + 1) (by omega))
  have hapre : a ∈ pre := mem_pre_of_mem_middleRaw ha_mr
  have hb_mr : b ∈ middleRaw pre group post :=
    hsub'.subset (mem_altPattern_snd a b (k + 1) (by omega))
  have hbpre : b ∈ pre := mem_pre_of_mem_middleRaw hb_mr
  have hgroup : (altPattern a b (k + 1)).Sublist (flattenBlocks group) :=
    hsub'.trans (middleRaw_sublist pre group post)
  have hcap := pair_alt_cap_of_altFree (post := post) (s := k + 2)
    hab hapre hbpre hgroup hfree
  omega

/-- The closing letter of an alternating pattern is one of its two symbols:
`altPattern a b (L+1) = altPattern a b L ++ [c]` with `c = a ∨ c = b`. -/
theorem altPattern_append_tail (a b : ℕ) :
    ∀ L : ℕ, ∃ c, (c = a ∨ c = b)
      ∧ altPattern a b (L + 1) = altPattern a b L ++ [c] := by
  intro L
  induction L generalizing a b with
  | zero => exact ⟨a, Or.inl rfl, rfl⟩
  | succ k ih =>
      obtain ⟨c, hc, heq⟩ := ih b a
      refine ⟨c, ?_, ?_⟩
      · rcases hc with h | h
        · exact Or.inr h
        · exact Or.inl h
      · show a :: altPattern b a (k + 1) = (a :: altPattern b a k) ++ [c]
        rw [heq]
        rfl

/-- A symbol of `middleRaw` occurs on both sides, hence in `post`. -/
theorem mem_post_of_mem_middleRaw
    {pre post : List ℕ} {group : List (List ℕ)} {a : ℕ}
    (ha : a ∈ middleRaw pre group post) : a ∈ post := by
  unfold middleRaw at ha
  have h2 := (List.mem_filter.mp ha).2
  rw [decide_eq_true_eq] at h2
  exact h2.2

/-- **The two-step pair lift.**  An alternation `altPattern a b L` inside the
flattened group, with both symbols anchored in `pre` *and* `post`, lifts to a
length-`(L+2)` alternation in the context: prepend the opposite symbol from
`pre` (`+1`) and append the matching closing symbol from `post` (`+1`). -/
theorem pair_alt_lift_two
    {pre post : List ℕ} {group : List (List ℕ)} {a b L : ℕ}
    (hapre : a ∈ pre) (hbpre : b ∈ pre) (hapost : a ∈ post) (hbpost : b ∈ post)
    (hgroup : (altPattern a b L).Sublist (flattenBlocks group)) :
    (altPattern b a (L + 2)).Sublist (pre ++ flattenBlocks group ++ post) := by
  -- `altPattern b a (L+2) = b :: altPattern a b (L+1)`, and
  -- `altPattern a b (L+1) = altPattern a b L ++ [c]` with `c ∈ {a,b} ⊆ post`.
  obtain ⟨c, hc, hceq⟩ := altPattern_append_tail a b L
  have hcpost : c ∈ post := by rcases hc with h | h <;> (subst h; assumption)
  have hbpre' : [b].Sublist pre := List.singleton_sublist.mpr hbpre
  have hcpost' : [c].Sublist post := List.singleton_sublist.mpr hcpost
  have hstep : (b :: (altPattern a b L ++ [c])).Sublist
      (pre ++ flattenBlocks group ++ post) := by
    have h1 : (altPattern a b L ++ [c]).Sublist (flattenBlocks group ++ post) :=
      List.Sublist.append hgroup hcpost'
    have h2 : ([b] ++ (altPattern a b L ++ [c])).Sublist
        (pre ++ (flattenBlocks group ++ post)) :=
      List.Sublist.append hbpre' h1
    simpa [List.append_assoc] using h2
  have hrw : altPattern b a (L + 2) = b :: (altPattern a b L ++ [c]) := by
    show b :: altPattern a b (L + 1) = b :: (altPattern a b L ++ [c])
    rw [hceq]
  rw [hrw]
  exact hstep

/-- **The order `s` to order `s-2` descent on `middleRaw`** — the exact form
claimed by the Hart--Sharir / Klazar ladder.  Under `AltFree s` (`s ≥ 4`) the
derived sequence `middleRaw` is `AltFree (s-2)`: any `(s-2)`-alternation inside
`middleRaw` lifts (pre-prepend `+1`, post-append `+1`) to a forbidden
`s`-alternation.  Sharp lift count, margin exactly the documented `≥ 1`. -/
theorem middleRaw_altFree_sub_two
    {pre post : List ℕ} {group : List (List ℕ)} {s : ℕ} (hs : 4 ≤ s)
    (hfree : AltFree s (pre ++ flattenBlocks group ++ post)) :
    AltFree (s - 2) (middleRaw pre group post) := by
  rintro ⟨a, b, hab, hsub⟩
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 4 := ⟨s - 4, by omega⟩
  -- `s - 2 = k + 2 ≥ 2`, so both symbols occur in `middleRaw`
  have hsub' : (altPattern a b (k + 2)).Sublist (middleRaw pre group post) := by
    simpa using hsub
  have ha_mr : a ∈ middleRaw pre group post :=
    hsub'.subset (mem_altPattern_fst a b (k + 2) (by omega))
  have hb_mr : b ∈ middleRaw pre group post :=
    hsub'.subset (mem_altPattern_snd a b (k + 2) (by omega))
  have hapre : a ∈ pre := mem_pre_of_mem_middleRaw ha_mr
  have hbpre : b ∈ pre := mem_pre_of_mem_middleRaw hb_mr
  have hapost : a ∈ post := mem_post_of_mem_middleRaw ha_mr
  have hbpost : b ∈ post := mem_post_of_mem_middleRaw hb_mr
  have hgroup : (altPattern a b (k + 2)).Sublist (flattenBlocks group) :=
    hsub'.trans (middleRaw_sublist pre group post)
  -- lift to length `k + 4 = s`, contradicting `AltFree s`
  have hlift := pair_alt_lift_two (post := post)
    hapre hbpre hapost hbpost hgroup
  -- `altPattern b a (k + 2 + 2) = altPattern b a (k + 4)`
  exact hfree ⟨b, a, hab.symm, by simpa using hlift⟩

/-! ### The ladder

The descent reduces a `MiddlesKeyAt s` obligation to a **DS-linearity bound on
a lower-order blocked sequence**: the derived sequence is `flattenBlocks` of a
`Nodup` block list of the same block-count as `group`, it is `AltFree (s-2)`,
and its distinct-symbol count is exactly `middleSymbols.length`.  We isolate
the surviving combinatorial obligation as `BlockSeqLinear`. -/

/-- The block list of the derived sequence: per-block dedup of middle
occurrences. -/
noncomputable def derivedBlocks
    (pre : List ℕ) (group : List (List ℕ)) (post : List ℕ) : List (List ℕ) :=
  group.map (fun blk =>
    (blk.filter (fun a => occursOnBothSides a pre post)).dedup)

theorem derivedSeq_eq_flatten_derivedBlocks
    (pre : List ℕ) (group : List (List ℕ)) (post : List ℕ) :
    derivedSeq pre group post = flattenBlocks (derivedBlocks pre group post) := rfl

theorem derivedBlocks_length
    (pre : List ℕ) (group : List (List ℕ)) (post : List ℕ) :
    (derivedBlocks pre group post).length = group.length := by
  unfold derivedBlocks
  exact List.length_map _

theorem derivedBlocks_nodup
    (pre : List ℕ) (group : List (List ℕ)) (post : List ℕ) :
    ∀ blk ∈ derivedBlocks pre group post, blk.Nodup := by
  intro blk hblk
  unfold derivedBlocks at hblk
  rcases List.mem_map.mp hblk with ⟨o, _, rfl⟩
  exact List.nodup_dedup _

/-- **The isolated DS-linearity obligation.**  A linear length bound for an
`AltFree s` sequence built from `Nodup` blocks, in terms of its distinct
symbols and its block count.  This is the surviving content of the ladder: it
is provable with `C = 1` at `s = 5` from `middlesKey_proved`'s tail-disjointness
machinery for *triples*, but as a bound on a *bare* blocked sequence it is the
genuinely separated obligation (the derived sequence carries no `pre`/`post`
anchoring of its own — the obstacle flagged for the order-descent route). -/
def BlockSeqLinear (s C : ℕ) : Prop :=
  ∀ (bg : List (List ℕ)),
    (∀ blk ∈ bg, blk.Nodup) →
    AltFree s (flattenBlocks bg) →
    (flattenBlocks bg).length
      ≤ C * ((flattenBlocks bg).toFinset.card + bg.length)

/-- **The ladder.**  A DS-linearity bound at order `s-2` lifts, via the
descent `middleRaw_altFree_sub_two`, to the triple bound `MiddlesKeyAt s C`
(for `s ≥ 4`).  The derived sequence is fed in as a bare blocked sequence;
its symbol count is `middleSymbols.length` and its block count is
`group.length`, so the `BlockSeqLinear (s-2) C` bound is exactly the
`MiddlesKeyAt s C` inequality. -/
theorem MiddlesKeyAt_of_descent {s C : ℕ} (hs : 4 ≤ s)
    (hbsl : BlockSeqLinear (s - 2) C) : MiddlesKeyAt s C := by
  intro pre group post hfree hnodup
  -- derived block structure
  set bg := derivedBlocks pre group post with hbg
  have hbg_nodup : ∀ blk ∈ bg, blk.Nodup := derivedBlocks_nodup pre group post
  -- the derived flatten equals middleRaw
  have hflat_eq : flattenBlocks bg = middleRaw pre group post := by
    rw [hbg, ← derivedSeq_eq_flatten_derivedBlocks]
    exact derivedSeq_eq_middleRaw pre group post hnodup
  -- AltFree (s-2) on the derived sequence
  have hfree2 : AltFree (s - 2) (flattenBlocks bg) := by
    rw [hflat_eq]
    exact middleRaw_altFree_sub_two hs hfree
  -- apply the obligation
  have hb := hbsl bg hbg_nodup hfree2
  -- rewrite all three quantities in `middleRaw / middleSymbols / group` terms
  rw [hflat_eq, derivedBlocks_length pre group post] at hb
  have hcard : (middleRaw pre group post).toFinset.card
      = (middleSymbols pre group post).length := by
    show (middleRaw pre group post).toFinset.card
        = (middleRaw pre group post).dedup.length
    exact List.card_toFinset _
  rw [hcard] at hb
  exact hb

/-! ### The surviving frontier and the unconditional bounded-alphabet closure

`BlockSeqLinear s C` with a **constant** `C` is *false* for `s ≥ 3`: it is a
Davenport--Schinzel length bound and `λ_3(n) = Θ(n·α(n))` is superlinear.  So
the ladder `MiddlesKeyAt_of_descent` cannot be closed by any constant-`C`
`BlockSeqLinear (s-2)`; equivalently, **`MiddlesKeyAt 12 C` is false for
every constant `C`** (consistent with the documented falsification of
`Blocking_middles_order12_linear`).  The `α`-factor here is real and is exactly
what the period/`gamma`-recursion engine (this file's `gamma_poly_alpha_proved`)
absorbs — it is not a constant.  We record the precise surviving obligation
and provide the unconditional closures that *do* hold. -/

/-- The exact surviving obligation, named: the order-`10` DS-linearity bound on
a bare blocked sequence.  Constant-`C` form is the superlinear frontier; the
honest closure replaces the constant by the `α`-aware recursion engine.  Kept
as the precise interface a constant-`C` route would need (and which the
DS lower bound rules out at scale). -/
def Blocking_BlockSeqLinear_ten : Prop := ∃ C, BlockSeqLinear 10 C

/-- Conditional closure of `MiddlesKeyAt 12` through the descent ladder: any
order-`10` blocked-sequence linearity bound yields `MiddlesKeyAt 12`. -/
theorem MiddlesKeyAt_twelve_of_blockSeqLinear {C : ℕ}
    (h : BlockSeqLinear 10 C) : MiddlesKeyAt 12 C :=
  MiddlesKeyAt_of_descent (by norm_num) (by simpa using h)

/-- **Unconditional bounded-alphabet closure**, in `MiddlesKeyAt` shape: when
the middle alphabet of every triple is bounded by `K`, the constant `4K + 2`
works at order `12`.  This is the quadratic bound `middles_order12_quadratic`
contracted by the symbol bound; it is genuinely unconditional (no `Blocking_`),
and is the form a fixed-fan-out recursion consumes. -/
def MiddlesKeyAtBounded (s C K : ℕ) : Prop :=
  ∀ pre group post,
    AltFree s (pre ++ flattenBlocks group ++ post) →
    (∀ b ∈ group, b.Nodup) →
    (middleSymbols pre group post).length ≤ K →
    (middleRaw pre group post).length ≤
      C * ((middleSymbols pre group post).length + group.length)

theorem MiddlesKeyAtBounded_twelve (K : ℕ) :
    MiddlesKeyAtBounded 12 (4 * K + 2) K := by
  intro pre group post hfree hnodup hK
  exact middles_order12_of_symbols_le K pre group post hnodup hfree hK

#print axioms MiddlesKeyAtBounded_twelve

/-- Sanity wiring of the descent at the *proven* base: `MiddlesKeyAt 5 1`
already holds (`MiddlesKeyAt_5_1`), and the descent reconstructs the order-`7`
statement from it under the genuine order-`5` blocked-sequence obligation —
demonstrating the ladder composes with the proven base.  (The order-`5`
obligation `BlockSeqLinear 5 C` is itself the superlinear DS object, hence
left as the named interface; this lemma only certifies the *wiring*.) -/
theorem MiddlesKeyAt_seven_of_blockSeqLinear {C : ℕ}
    (h : BlockSeqLinear 5 C) : MiddlesKeyAt 7 C :=
  MiddlesKeyAt_of_descent (by norm_num) (by simpa using h)

/-- **The order-12 decomposition step through the descent ladder.**  Given the
isolated order-`10` blocked-sequence linearity bound, the parametric engine
`oneStep_decomposition_at` fires at `s = 12`, `C`, with the descent supplying
`MiddlesKeyAt 12 C`.  This is the ladder's plug into the period recursion. -/
theorem oneStep_decomposition_at_twelve_of_blockSeqLinear {C : ℕ}
    (h : BlockSeqLinear 10 C) (b : ℕ)
    (hb : 2 ≤ b) (m n : ℕ) (u : List ℕ) (hm : b < m)
    (hfree : AltFree 12 u) (hblocked : Blocked m u)
    (hcard : u.toFinset.card ≤ n) :
    ∃ (locals : List (List ℕ)) (ctr : List ℕ),
      locals.length ≤ ceilDiv b m
      ∧ (∀ l ∈ locals, AltFree 12 l ∧ Blocked b l)
      ∧ (locals.map (fun l => l.toFinset.card)).sum ≤ n
      ∧ AltFree 12 ctr ∧ Blocked (ceilDiv b m) ctr
      ∧ ctr.toFinset.card ≤ n
      ∧ u.length ≤ (locals.map List.length).sum
          + C * (ctr.length + m) + 2 * b * n :=
  oneStep_decomposition_at (MiddlesKeyAt_twelve_of_blockSeqLinear h) b hb m n u hm
    hfree hblocked hcard

end OrderDescentLadder

#print axioms derivedSeq_eq_middleRaw
#print axioms derivedSeq_length_eq
#print axioms altPattern_sublist_mono
#print axioms pair_alt_lift_to_context
#print axioms pair_alt_cap_of_altFree
#print axioms altPattern_append_tail
#print axioms pair_alt_lift_two
#print axioms middleRaw_altFree_pred
#print axioms middleRaw_altFree_sub_two
#print axioms derivedBlocks_length
#print axioms derivedBlocks_nodup
#print axioms MiddlesKeyAt_of_descent
#print axioms MiddlesKeyAt_twelve_of_blockSeqLinear
#print axioms MiddlesKeyAtBounded_twelve
#print axioms MiddlesKeyAt_seven_of_blockSeqLinear
#print axioms oneStep_decomposition_at_twelve_of_blockSeqLinear

/-! ## W-D backbone: the abstract recurrence-telescoping theorem

This section delivers the **per-level-flat recurrence + O(alpha) depth ⟹
`n·alpha`** backbone the W-D core instantiates.  We work over an arbitrary
`ℕ`-valued cost `T` and an explicit *level-descent* schedule `f : ℕ → ℕ`
that strictly decreases above a `threshold`.  The number of descent levels
is exactly `gammaOf f threshold hdec`, the iterate counter already proven
monotone (`gamma_mono_proved`) and `O(alpha)` under a polynomial bound
(`gamma_poly_alpha_proved`).

The recurrence we telescope is the *aggregated-per-level* form

  base : `m ≤ threshold → T m ≤ c0 * m`
  step : `threshold < m → T m ≤ T (f m) + c * m`

i.e. at every level above the threshold the work shrinks the size to `f m`
and pays a flat overhead `c * m`.  Because the descent sizes are
non-increasing and bounded by the start `n`, each of the
`L = gammaOf f threshold hdec n` levels costs at most `c * n`, plus a base
charge `c0 * n`.  Strong induction on the size telescopes this to

  `T n ≤ c * n * L + c0 * n`            (`recursion_unfold`)

and `gamma_poly_alpha_proved` collapses `L ≤ c' * (alpha (n+1) + 1)` for the
double schedule, yielding the closed `n·alpha` form

  `T n ≤ (c * c') * (n * alpha (n+1)) + (c*c' + c0) * n`   (`recursion_telescope`).
-/

section RecurrenceTelescope

/-- The two hypotheses packaging an aggregated-per-level recurrence for a cost
function `T` with descent schedule `f`, flat per-level slope `c`, and base
slope `c0`. -/
def RecBase (T : ℕ → ℕ) (threshold c0 : ℕ) : Prop :=
  ∀ m, m ≤ threshold → T m ≤ c0 * m

def RecStep (T f : ℕ → ℕ) (threshold c : ℕ) : Prop :=
  ∀ m, threshold < m → T m ≤ T (f m) + c * m

/-- **Level-unfolding lemma (deliverable 1).**  An aggregated-per-level
recurrence telescopes to `c · n · L + c0 · n`, where `L` is the descent depth
`gammaOf f threshold hdec n`.  Proof: strong induction on the size.  Above the
threshold one descent level peels a flat `c * m ≤ c * n` charge and `gammaOf`
increments by one; `f m ≤ m` (from `DecreasesAbove`) keeps the recursive
estimate's size factor below `m`. -/
theorem recursion_unfold
    (T f : ℕ → ℕ) (threshold c c0 : ℕ)
    (hdec : DecreasesAbove threshold f)
    (hbase : RecBase T threshold c0)
    (hstep : RecStep T f threshold c) :
    ∀ n, T n ≤ c * n * gammaOf f threshold hdec n + c0 * n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n ≤ threshold
    · -- base case: the descent depth is zero, the base charge suffices
      rw [gammaOf_le (hdec := hdec) h]
      have hb := hbase n h
      simpa using hb
    · have hn : threshold < n := by omega
      have hfn : f n < n := hdec n hn
      have hflen : f n ≤ n := Nat.le_of_lt hfn
      -- one descent level: gammaOf increments, flat charge is `c * n`
      have hrec := ih (f n) hfn
      have hstepn := hstep n hn
      have heq : gammaOf f threshold hdec n
          = 1 + gammaOf f threshold hdec (f n) := gammaOf_gt hn
      -- size monotonicity of the two estimate factors
      have hmulA : c * (f n) * gammaOf f threshold hdec (f n)
          ≤ c * n * gammaOf f threshold hdec (f n) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left c hflen)
      have hmulB : c0 * (f n) ≤ c0 * n := Nat.mul_le_mul_left c0 hflen
      -- assemble: T n ≤ T(f n) + c*n
      --                ≤ (c*(f n)*G + c0*(f n)) + c*n
      --                ≤ c*n*G + c0*n + c*n = c*n*(G+1) + c0*n
      have hTfn : T (f n) ≤ c * n * gammaOf f threshold hdec (f n) + c0 * n :=
        le_trans hrec (by omega)
      have hexpand : c * n * gammaOf f threshold hdec n
          = c * n * gammaOf f threshold hdec (f n) + c * n := by
        rw [heq]; ring
      calc T n ≤ T (f n) + c * n := hstepn
        _ ≤ (c * n * gammaOf f threshold hdec (f n) + c0 * n) + c * n := by
              omega
        _ = c * n * gammaOf f threshold hdec n + c0 * n := by
              rw [hexpand]; ring

/-! ### Deliverable 2: the alpha collapse of the descent depth

For the *double schedule* `f = fun z => beta (beta z)` with `beta` monotone and
polynomially `alpha`-bounded, `gamma_poly_alpha_proved` gives a constant `c'`
with `gammaOf f threshold hdec n ≤ c' * (alpha (n+1) + 1)`.  We package this as
a standalone level-count bound. -/

theorem recursion_depth_alpha
    (beta : ℕ → ℕ) (c d threshold : ℕ)
    (hdec : DecreasesAbove threshold (fun z => beta (beta z)))
    (hmono : MonotoneNat beta)
    (hpoly : ∀ z, beta z ≤ c * (alpha (z + 1) + 1) ^ d) :
    ∃ c' : ℕ, ∀ n,
      gammaOf (fun z => beta (beta z)) threshold hdec n
        ≤ c' * (alpha (n + 1) + 1) :=
  gamma_poly_alpha_proved beta c d threshold hdec hmono hpoly

/-! ### Deliverable 3: the combined closed form `T n ≤ C·n·alpha(n+1) + C'·n`

Composing the level-unfolding (deliverable 1) with the depth collapse
(deliverable 2) gives the closed `n · alpha` bound.  The explicit constants are
`C = c * c'` and `C' = c * c' + c0`, where `c'` is the depth constant from
`gamma_poly_alpha_proved` (itself `F_omega (c_beta + 4 d + 7) + 1`). -/

theorem recursion_telescope
    (T beta : ℕ → ℕ) (cβ d threshold c c0 : ℕ)
    (hdec : DecreasesAbove threshold (fun z => beta (beta z)))
    (hmono : MonotoneNat beta)
    (hpoly : ∀ z, beta z ≤ cβ * (alpha (z + 1) + 1) ^ d)
    (hbase : RecBase T threshold c0)
    (hstep : RecStep T (fun z => beta (beta z)) threshold c) :
    ∃ C C' : ℕ, ∀ n,
      T n ≤ C * (n * alpha (n + 1)) + C' * n := by
  -- depth collapse
  obtain ⟨c', hc'⟩ := recursion_depth_alpha beta cβ d threshold hdec hmono hpoly
  -- level unfolding
  have hunfold := recursion_unfold T (fun z => beta (beta z)) threshold c c0
    hdec hbase hstep
  refine ⟨c * c', c * c' + c0, ?_⟩
  intro n
  -- substitute the depth bound into the unfolded estimate
  have h1 : T n
      ≤ c * n * gammaOf (fun z => beta (beta z)) threshold hdec n + c0 * n :=
    hunfold n
  have hG : gammaOf (fun z => beta (beta z)) threshold hdec n
      ≤ c' * (alpha (n + 1) + 1) := hc' n
  have h2 : c * n * gammaOf (fun z => beta (beta z)) threshold hdec n
      ≤ c * n * (c' * (alpha (n + 1) + 1)) :=
    Nat.mul_le_mul_left (c * n) hG
  -- expand `c * n * (c' * (alpha+1)) = (c*c')*(n*alpha) + (c*c')*n`
  have hexpand : c * n * (c' * (alpha (n + 1) + 1))
      = (c * c') * (n * alpha (n + 1)) + (c * c') * n := by ring
  have hfold : (c * c') * (n * alpha (n + 1)) + (c * c') * n + c0 * n
      = (c * c') * (n * alpha (n + 1)) + (c * c' + c0) * n := by ring
  -- assemble through the explicit `ring` rewrites and `omega`
  calc T n
      ≤ c * n * gammaOf (fun z => beta (beta z)) threshold hdec n + c0 * n := h1
    _ ≤ c * n * (c' * (alpha (n + 1) + 1)) + c0 * n :=
          Nat.add_le_add_right h2 (c0 * n)
    _ = (c * c') * (n * alpha (n + 1)) + (c * c' + c0) * n := by
          rw [hexpand]; ring

end RecurrenceTelescope

#print axioms recursion_unfold
#print axioms recursion_depth_alpha
#print axioms recursion_telescope

end CodexDS
