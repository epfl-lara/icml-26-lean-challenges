import Challenges.Splay_Tree.Def_Containment
import Challenges.Splay_Tree.Def_Ackermann
import Challenges.Splay_Tree.Def_Splay
set_option maxHeartbeats 2000000
namespace Splay
local notation "bN" => BinaryTree.node
local notation "bE" => BinaryTree.empty
def touchedCount (T : List Nat) (c : List Nat) : Nat := (c.filter (fun x => x ∈ T)).length
def searchPath (q : Nat) : BinaryTree → List Nat
  | .empty => []
  | .node l k r =>
      if q = k then [k]
      else if q < k then k :: searchPath q l
      else k :: searchPath q r
def kD (y : Nat) (t : BinaryTree) : Nat := (searchPath y t).length
@[simp] theorem kE (y : Nat) : kD y .empty = 0 := rfl
theorem fI {p : Nat → Prop} {l r : BinaryTree} {k : Nat} :
    ForallTree p (.node l k r) ↔ ForallTree p l ∧ p k ∧ ForallTree p r := by
  constructor
  · intro h
    cases h
    exact ⟨by assumption, by assumption, by assumption⟩
  · rintro ⟨hl, hk, hr⟩
    exact ForallTree.node l k r hl hk hr
theorem bI {l r : BinaryTree} {k : Nat} :
    IsBST (.node l k r) ↔
      ForallTree (fun x => x < k) l ∧ ForallTree (fun x => k < x) r ∧ IsBST l ∧ IsBST r := by
  constructor
  · intro h
    cases h
    exact ⟨by assumption, by assumption, by assumption, by assumption⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact IsBST.node k l r h1 h2 h3 h4
theorem sS {q k : Nat} (h : q = k) (l r : BinaryTree) :
    searchPath q (.node l k r) = [k] := by
  simp only [searchPath, if_pos h]
theorem sL {q k : Nat} (h : q < k) (l r : BinaryTree) :
    searchPath q (.node l k r) = k :: searchPath q l := by
  simp only [searchPath, if_neg (Nat.ne_of_lt h), if_pos h]
theorem sG {q k : Nat} (h : k < q) (l r : BinaryTree) :
    searchPath q (.node l k r) = k :: searchPath q r := by
  have h1 : q ≠ k := by omega
  have h2 : ¬ q < k := by omega
  simp only [searchPath, if_neg h1, if_neg h2]
theorem kS {y k : Nat} (h : y = k) (l r : BinaryTree) :
    kD y (.node l k r) = 1 := by
  simp [kD, sS h]
theorem kL {y k : Nat} (h : y < k) (l r : BinaryTree) :
    kD y (.node l k r) = kD y l + 1 := by
  simp [kD, sL h]
theorem kG {y k : Nat} (h : k < y) (l r : BinaryTree) :
    kD y (.node l k r) = kD y r + 1 := by
  simp [kD, sG h]
theorem mSF {p : Nat → Prop} {q y : Nat} :
    ∀ {t : BinaryTree}, ForallTree p t → y ∈ searchPath q t → p y := by
  intro t
  induction t with
  | empty => intro _ hy; simp [searchPath] at hy
  | node l k r ihl ihr =>
    intro h hy
    rcases fI.mp h with ⟨hl, hk, hr⟩
    by_cases hqk : q = k
    · rw [sS hqk] at hy
      simp only [List.mem_singleton] at hy
      exact hy ▸ hk
    · by_cases hqlt : q < k
      · rw [sL hqlt] at hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hk
        · exact ihl hl hy
      · have hklt : k < q := by omega
        rw [sG hklt] at hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hk
        · exact ihr hr hy
theorem sNE (l r : BinaryTree) (k q : Nat) :
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
theorem zzS (ll lr r A B : BinaryTree) (lk k q s : Nat)
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
theorem zaS (ll lr r A B : BinaryTree) (lk k q s : Nat)
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
theorem azS (l rl rr A B : BinaryTree) (rk k q s : Nat)
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
theorem aiS (l rl rr A B : BinaryTree) (rk k q s : Nat)
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
theorem sFA (p : Nat → Prop) :
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
      have hnn : (bN l k r).num_nodes = 1 + l.num_nodes + r.num_nodes := rfl
      omega
  | succ n ih =>
    intro t ht q hp
    cases t with
    | empty => exact hp
    | node l k r =>
      rcases fI.mp hp with ⟨hpl, hpk, hpr⟩
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
            rcases fI.mp hpl with ⟨hpll, hplk, hplr⟩
            by_cases hqlk : q < lk
            · cases ll with
              | empty =>
                rw [splay.eq_def]
                simp only [if_neg hqk, if_pos hqlt, if_pos hqlk]
                show ForallTree p (.node .empty lk (.node lr k r))
                exact .node _ _ _ .left hplk (.node _ _ _ hplr hpk hpr)
              | node a x b =>
                have hsz : (bN a x b).num_nodes ≤ n := by
                  have hnn : (bN (bN (bN a x b) lk lr)
                      k r).num_nodes
                      = 1 + (1 + (bN a x b).num_nodes + lr.num_nodes)
                        + r.num_nodes := rfl
                  omega
                have hrec := ih _ hsz q hpll
                cases hs : splay (bN a x b) q with
                | empty => exact absurd hs (sNE _ _ _ _)
                | node A s B =>
                  rw [zzS (bN a x b) lr r A B lk k q s hqk hqlt
                    hqlk (fun h => nomatch h) hs]
                  rw [hs] at hrec
                  rcases fI.mp hrec with ⟨hA, hsP, hB⟩
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
                  have hsz : (bN a x b).num_nodes ≤ n := by
                    have hnn : (bN (bN ll lk (bN a x b))
                        k r).num_nodes
                        = 1 + (1 + ll.num_nodes + (bN a x b).num_nodes)
                          + r.num_nodes := rfl
                    omega
                  have hrec := ih _ hsz q hplr
                  cases hs : splay (bN a x b) q with
                  | empty => exact absurd hs (sNE _ _ _ _)
                  | node A s B =>
                    rw [zaS ll (bN a x b) r A B lk k q s hqk hqlt
                      hlkq (fun h => nomatch h) hs]
                    rw [hs] at hrec
                    rcases fI.mp hrec with ⟨hA, hsP, hB⟩
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
            rcases fI.mp hpr with ⟨hprl, hprk, hprr⟩
            by_cases hqrk : q < rk
            · cases rl with
              | empty =>
                rw [splay.eq_def]
                simp only [if_neg hqk, if_neg hqlt, if_pos hqrk]
                show ForallTree p (.node (.node l k .empty) rk rr)
                exact .node _ _ _ (.node _ _ _ hpl hpk .left) hprk hprr
              | node a x b =>
                have hsz : (bN a x b).num_nodes ≤ n := by
                  have hnn : (bN l k
                      (bN (bN a x b) rk rr)).num_nodes
                      = 1 + l.num_nodes
                        + (1 + (bN a x b).num_nodes + rr.num_nodes) := rfl
                  omega
                have hrec := ih _ hsz q hprl
                cases hs : splay (bN a x b) q with
                | empty => exact absurd hs (sNE _ _ _ _)
                | node A s B =>
                  rw [aiS l (bN a x b) rr A B rk k q s hqk hklt
                    hqrk (fun h => nomatch h) hs]
                  rw [hs] at hrec
                  rcases fI.mp hrec with ⟨hA, hsP, hB⟩
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
                  have hsz : (bN a x b).num_nodes ≤ n := by
                    have hnn : (bN l k
                        (bN rl rk (bN a x b))).num_nodes
                        = 1 + l.num_nodes
                          + (1 + rl.num_nodes + (bN a x b).num_nodes) := rfl
                    omega
                  have hrec := ih _ hsz q hprr
                  cases hs : splay (bN a x b) q with
                  | empty => exact absurd hs (sNE _ _ _ _)
                  | node A s B =>
                    rw [azS l rl (bN a x b) A B rk k q s hqk hklt
                      hrkq (fun h => nomatch h) hs]
                    rw [hs] at hrec
                    rcases fI.mp hrec with ⟨hA, hsP, hB⟩
                    exact .node _ _ _
                      (.node _ _ _ (.node _ _ _ hpl hpk hprl) hprk hA) hsP hB
              · rw [splay.eq_def]
                simp only [if_neg hqk, if_neg hqlt, if_neg hqrk, if_neg hrkq]
                show ForallTree p (.node (.node l k rl) rk rr)
                exact .node _ _ _ (.node _ _ _ hpl hpk hprl) hprk hprr
theorem sF0 (p : Nat → Prop) (t : BinaryTree) (q : Nat)
    (h : ForallTree p t) : ForallTree p (splay t q) :=
  sFA p t.num_nodes t (Nat.le_refl _) q h
@[simp] theorem sE0 (q : Nat) : searchPath q .empty = [] := rfl
theorem rM (y s : Nat) (A B : BinaryTree) :
    s ∈ searchPath y (.node A s B) := by
  by_cases h1 : y = s
  · rw [sS h1]; simp
  · by_cases h2 : y < s
    · rw [sL h2]; simp
    · rw [sG (by omega)]; simp
def divergeSuffix (y q : Nat) : BinaryTree → List Nat
  | .empty => []
  | .node l k r =>
      if y = k then []
      else if q = k then (if y < k then searchPath y l else searchPath y r)
      else if y < k ∧ q < k then divergeSuffix y q l
      else if k < y ∧ k < q then divergeSuffix y q r
      else (if y < k then searchPath y l else searchPath y r)
@[simp] theorem dsE0 (y q : Nat) : divergeSuffix y q .empty = [] := rfl
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
theorem dsQ (q : Nat) : ∀ t : BinaryTree, divergeSuffix q q t = [] := by
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
theorem mDF {p : Nat → Prop} {q y : Nat} :
    ∀ (t : BinaryTree), ForallTree p t → ∀ z ∈ divergeSuffix y q t, p z := by
  intro t
  induction t with
  | empty => intro _ z hz; simp at hz
  | node l k r ihl ihr =>
    intro h z hz
    rcases fI.mp h with ⟨hl, hk, hr⟩
    by_cases h1 : y = k
    · rw [ds_self h1] at hz; simp at hz
    · by_cases h2 : q = k
      · by_cases h3 : y < k
        · rw [ds_qroot_lt h2 h3] at hz
          exact mSF hl hz
        · rw [ds_qroot_gt h2 (by omega)] at hz
          exact mSF hr hz
      · by_cases h3 : y < k
        · by_cases h4 : q < k
          · rw [ds_both_lt h3 h4] at hz
            exact ihl hl z hz
          · rw [ds_div_lt h3 (by omega)] at hz
            exact mSF hl hz
        · have h3' : k < y := by omega
          by_cases h4 : k < q
          · rw [ds_both_gt h3' h4] at hz
            exact ihr hr z hz
          · rw [ds_div_gt h3' (by omega)] at hz
            exact mSF hr hz
theorem dsD {q y : Nat} :
    ∀ (t : BinaryTree), IsBST t → ∀ z ∈ divergeSuffix y q t, z ∉ searchPath q t := by
  intro t
  induction t with
  | empty => intro _ z hz; simp at hz
  | node l k r ihl ihr =>
    intro hbst z hz
    rcases bI.mp hbst with ⟨hfl, hfr, hbl, hbr⟩
    by_cases h1 : y = k
    · rw [ds_self h1] at hz; simp at hz
    · by_cases h2 : q = k
      · rw [sS h2]
        by_cases h3 : y < k
        · rw [ds_qroot_lt h2 h3] at hz
          have hzk : z < k := mSF (p := fun w => w < k) hfl hz
          simp only [List.mem_singleton]
          omega
        · rw [ds_qroot_gt h2 (by omega)] at hz
          have hzk : k < z := mSF hfr hz
          simp only [List.mem_singleton]
          omega
      · by_cases h3 : y < k
        · by_cases h4 : q < k
          · rw [ds_both_lt h3 h4] at hz
            rw [sL h4]
            have hzk : z < k := mDF l hfl z hz
            intro hmem
            rcases List.mem_cons.mp hmem with heq | hmem'
            · omega
            · exact ihl hbl z hz hmem'
          · have h4' : k < q := by omega
            rw [ds_div_lt h3 h4'] at hz
            rw [sG h4']
            have hzk : z < k := mSF (p := fun w => w < k) hfl hz
            intro hmem
            rcases List.mem_cons.mp hmem with heq | hmem'
            · omega
            · have : k < z := mSF hfr hmem'
              omega
        · have h3' : k < y := by omega
          by_cases h4 : k < q
          · rw [ds_both_gt h3' h4] at hz
            rw [sG h4]
            have hzk : k < z := mDF r hfr z hz
            intro hmem
            rcases List.mem_cons.mp hmem with heq | hmem'
            · omega
            · exact ihr hbr z hz hmem'
          · have h4' : q < k := by omega
            rw [ds_div_gt h3' h4'] at hz
            rw [sL h4']
            have hzk : k < z := mSF hfr hz
            intro hmem
            rcases List.mem_cons.mp hmem with heq | hmem'
            · omega
            · have : z < k := mSF (p := fun w => w < k) hfl hmem'
              omega
theorem shd (q y : Nat) (t : BinaryTree) :
    ∃ sh, searchPath y t = sh ++ divergeSuffix y q t ∧ ∀ z ∈ sh, z ∈ searchPath q t := by
  induction t with
  | empty => exact ⟨[], rfl, by simp⟩
  | node l k r ihl ihr =>
    have hk : k ∈ searchPath q (bN l k r) := rM q k l r
    by_cases hyk : y = k
    · refine ⟨[k], ?_, ?_⟩
      · simp only [sS hyk, ds_self hyk, List.append_nil]
      · intro z hz
        simp only [List.mem_singleton] at hz
        subst hz; exact hk
    · by_cases hqk : q = k
      · by_cases hylt : y < k
        · refine ⟨[k], ?_, ?_⟩
          · simp only [sL hylt, ds_qroot_lt hqk hylt,
              List.cons_append, List.nil_append]
          · intro z hz
            simp only [List.mem_singleton] at hz
            subst hz; exact hk
        · have hkly : k < y := by omega
          refine ⟨[k], ?_, ?_⟩
          · simp only [sG hkly, ds_qroot_gt hqk hkly,
              List.cons_append, List.nil_append]
          · intro z hz
            simp only [List.mem_singleton] at hz
            subst hz; exact hk
      · by_cases hylt : y < k
        · by_cases hqlt : q < k
          · obtain ⟨sh, hsh, hm⟩ := ihl
            refine ⟨k :: sh, ?_, ?_⟩
            · simp only [sL hylt, ds_both_lt hylt hqlt, hsh,
                List.cons_append]
            · intro z hz
              rcases List.mem_cons.mp hz with rfl | hz
              · exact hk
              · rw [sL hqlt]
                exact List.mem_cons_of_mem _ (hm z hz)
          · have hklq : k < q := by omega
            refine ⟨[k], ?_, ?_⟩
            · simp only [sL hylt, ds_div_lt hylt hklq,
                List.cons_append, List.nil_append]
            · intro z hz
              simp only [List.mem_singleton] at hz
              subst hz; exact hk
        · have hkly : k < y := by omega
          by_cases hklq : k < q
          · obtain ⟨sh, hsh, hm⟩ := ihr
            refine ⟨k :: sh, ?_, ?_⟩
            · simp only [sG hkly, ds_both_gt hkly hklq, hsh,
                List.cons_append]
            · intro z hz
              rcases List.mem_cons.mp hz with rfl | hz
              · exact hk
              · rw [sG hklq]
                exact List.mem_cons_of_mem _ (hm z hz)
          · have hqlt : q < k := by omega
            refine ⟨[k], ?_, ?_⟩
            · simp only [sG hkly, ds_div_gt hkly hqlt,
                List.cons_append, List.nil_append]
            · intro z hz
              simp only [List.mem_singleton] at hz
              subst hz; exact hk
theorem spdA :
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
      have hnn : (bN l k r).num_nodes = 1 + l.num_nodes + r.num_nodes := rfl
      omega
  | succ n ih =>
    intro t ht q y hbst
    cases t with
    | empty => exact ⟨[], rfl, by simp⟩
    | node l k r =>
      rcases bI.mp hbst with ⟨hbL, hbR, hbstl, hbstr⟩
      by_cases hqk : q = k
      · -- (1) FOUND AT ROOT: splay is the identity
        rw [splay.eq_def]
        simp only [if_pos hqk]
        have hqpath : searchPath q (bN l k r) = [k] :=
          sS hqk l r
        by_cases hyk : y = k
        · refine ⟨[k], ?_, ?_⟩
          · simp only [sS hyk, ds_self hyk, List.append_nil]
          · intro z hz
            simp only [List.mem_singleton] at hz
            subst hz; rw [hqpath]; simp
        · by_cases hylt : y < k
          · refine ⟨[k], ?_, ?_⟩
            · simp only [sL hylt, ds_qroot_lt hqk hylt,
                List.cons_append, List.nil_append]
            · intro z hz
              simp only [List.mem_singleton] at hz
              subst hz; rw [hqpath]; simp
          · have hkly : k < y := by omega
            refine ⟨[k], ?_, ?_⟩
            · simp only [sG hkly, ds_qroot_gt hqk hkly,
                List.cons_append, List.nil_append]
            · intro z hz
              simp only [List.mem_singleton] at hz
              subst hz; rw [hqpath]; simp
      · by_cases hqlt : q < k
        · cases l with
          | empty =>
            rw [splay.eq_def]
            simp only [if_neg hqk, if_pos hqlt]
            show ∃ p', searchPath y (bN .empty k r)
                = p' ++ divergeSuffix y q (bN .empty k r)
              ∧ ∀ z ∈ p', z ∈ searchPath q (bN .empty k r)
            have hqpath : searchPath q (bN .empty k r) = [k] := by
              rw [sL hqlt, sE0]
            by_cases hyk : y = k
            · refine ⟨[k], ?_, ?_⟩
              · simp only [sS hyk, ds_self hyk, List.append_nil]
              · intro z hz
                simp only [List.mem_singleton] at hz
                subst hz; rw [hqpath]; simp
            · by_cases hylt : y < k
              · refine ⟨[k], ?_, ?_⟩
                · simp only [sL hylt, sE0,
                    ds_both_lt hylt hqlt, dsE0,
                    List.cons_append, List.nil_append, List.append_nil]
                · intro z hz
                  simp only [List.mem_singleton] at hz
                  subst hz; rw [hqpath]; simp
              · have hkly : k < y := by omega
                refine ⟨[k], ?_, ?_⟩
                · simp only [sG hkly, ds_div_gt hkly hqlt,
                    List.cons_append, List.nil_append]
                · intro z hz
                  simp only [List.mem_singleton] at hz
                  subst hz; rw [hqpath]; simp
          | node ll lk lr =>
            rcases fI.mp hbL with ⟨hbL_ll, hlk_k, hbL_lr⟩
            rcases bI.mp hbstl with ⟨hbLL, hbLR, hbstll, hbstlr⟩
            by_cases hqlk : q < lk
            · cases ll with
              | empty =>
                rw [splay.eq_def]
                simp only [if_neg hqk, if_pos hqlt, if_pos hqlk]
                show ∃ p', searchPath y (bN .empty lk (bN lr k r))
                    = p' ++ divergeSuffix y q
                        (bN (bN .empty lk lr) k r)
                  ∧ ∀ z ∈ p',
                      z ∈ searchPath q (bN (bN .empty lk lr) k r)
                have hqpath : searchPath q
                    (bN (bN .empty lk lr) k r) = [k, lk] := by
                  rw [sL hqlt, sL hqlk, sE0]
                by_cases hyk : y = k
                · have hlky : lk < y := by omega
                  refine ⟨[lk, k], ?_, ?_⟩
                  · simp only [sG hlky, sS hyk,
                      ds_self hyk, List.cons_append, List.nil_append, List.append_nil]
                  · intro z hz; rw [hqpath]
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                    tauto
                · by_cases hylt : y < k
                  · by_cases hylk : y = lk
                    · refine ⟨[lk], ?_, ?_⟩
                      · simp only [sS hylk, ds_both_lt hylt hqlt,
                          ds_self hylk, List.cons_append, List.nil_append, List.append_nil]
                      · intro z hz; rw [hqpath]
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                        tauto
                    · by_cases hyllk : y < lk
                      · refine ⟨[lk], ?_, ?_⟩
                        · simp only [sL hyllk, sE0,
                            ds_both_lt hylt hqlt, ds_both_lt hyllk hqlk, dsE0,
                            List.cons_append, List.nil_append, List.append_nil]
                        · intro z hz; rw [hqpath]
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                          tauto
                      · have hlky : lk < y := by omega
                        refine ⟨[lk, k], ?_, ?_⟩
                        · simp only [sG hlky, sL hylt,
                            ds_both_lt hylt hqlt, ds_div_gt hlky hqlk,
                            List.cons_append, List.nil_append]
                        · intro z hz; rw [hqpath]
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                          tauto
                  · have hkly : k < y := by omega
                    have hlky : lk < y := by omega
                    refine ⟨[lk, k], ?_, ?_⟩
                    · simp only [sG hlky, sG hkly,
                        ds_div_gt hkly hqlt, List.cons_append, List.nil_append]
                    · intro z hz; rw [hqpath]
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                      tauto
              | node a x b =>
                have hsz : (bN a x b).num_nodes ≤ n := by
                  have hnn : (bN (bN (bN a x b) lk lr)
                      k r).num_nodes
                      = 1 + (1 + (bN a x b).num_nodes + lr.num_nodes)
                        + r.num_nodes := rfl
                  omega
                cases hs : splay (bN a x b) q with
                | empty => exact absurd hs (sNE _ _ _ _)
                | node A s B =>
                  rw [zzS (bN a x b) lr r A B lk k q s hqk hqlt
                    hqlk (fun h => nomatch h) hs]
                  have hsA := sF0 _ (bN a x b) q hbLL
                  rw [hs] at hsA
                  have hslk : s < lk := (fI.mp hsA).2.1
                  obtain ⟨pq, hpq, hmq⟩ := ih (bN a x b) hsz q q hbstll
                  rw [hs, dsQ, List.append_nil] at hpq
                  have hsq : s ∈ searchPath q (bN a x b) := by
                    apply hmq
                    rw [← hpq]
                    exact rM q s A B
                  have hqpath : searchPath q (bN
                      (bN (bN a x b) lk lr) k r)
                      = k :: lk :: searchPath q (bN a x b) := by
                    rw [sL hqlt, sL hqlk]
                  by_cases hyk : y = k
                  · have hsy : s < y := by omega
                    have hlky : lk < y := by omega
                    refine ⟨[s, lk, k], ?_, ?_⟩
                    · simp only [sG hsy, sG hlky,
                        sS hyk, ds_self hyk,
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
                        · simp only [sG hsy, sS hylk,
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
                          obtain ⟨p'', hp'', hm''⟩ := ih (bN a x b) hsz q y hbstll
                          rw [hs] at hp''
                          have hds : divergeSuffix y q (bN
                              (bN (bN a x b) lk lr) k r)
                              = divergeSuffix y q (bN a x b) := by
                            rw [ds_both_lt hylt hqlt, ds_both_lt hyllk hqlk]
                          rw [hds]
                          rcases Nat.lt_trichotomy y s with hys | hys | hys
                          · rw [sL hys] at hp''
                            refine ⟨p'', ?_, ?_⟩
                            · rw [sL hys]
                              exact hp''
                            · intro z hz
                              rw [hqpath]
                              have hzin := hm'' z hz
                              simp [hzin]
                          · rw [sS hys] at hp''
                            refine ⟨p'', ?_, ?_⟩
                            · rw [sS hys]
                              exact hp''
                            · intro z hz
                              rw [hqpath]
                              have hzin := hm'' z hz
                              simp [hzin]
                          · rw [sG hys] at hp''
                            cases p'' with
                            | nil =>
                              exfalso
                              rw [List.nil_append] at hp''
                              have hsmem : s ∈ divergeSuffix y q (bN a x b) := by
                                rw [← hp'']
                                simp
                              exact dsD (bN a x b)
                                hbstll s hsmem hsq
                            | cons c p''' =>
                              rw [List.cons_append] at hp''
                              injection hp'' with hc htail
                              subst hc
                              refine ⟨s :: lk :: p''', ?_, ?_⟩
                              · simp only [sG hys, sL hyllk,
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
                          · simp only [sG hsy, sG hlky,
                              sL hylt, ds_both_lt hylt hqlt,
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
                      · simp only [sG hsy, sG hlky,
                          sG hkly, ds_div_gt hkly hqlt,
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
                  rw [splay.eq_def]
                  simp only [if_neg hqk, if_pos hqlt, if_neg hqlk, if_pos hlkq]
                  show ∃ p', searchPath y (bN ll lk (bN .empty k r))
                      = p' ++ divergeSuffix y q
                          (bN (bN ll lk .empty) k r)
                    ∧ ∀ z ∈ p',
                        z ∈ searchPath q (bN (bN ll lk .empty) k r)
                  have hqpath : searchPath q
                      (bN (bN ll lk .empty) k r) = [k, lk] := by
                    rw [sL hqlt, sG hlkq, sE0]
                  by_cases hyk : y = k
                  · have hlky : lk < y := by omega
                    refine ⟨[lk, k], ?_, ?_⟩
                    · simp only [sG hlky, sS hyk,
                        ds_self hyk, List.cons_append, List.nil_append, List.append_nil]
                    · intro z hz; rw [hqpath]
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                      tauto
                  · by_cases hylt : y < k
                    · by_cases hylk : y = lk
                      · refine ⟨[lk], ?_, ?_⟩
                        · simp only [sS hylk, ds_both_lt hylt hqlt,
                            ds_self hylk, List.cons_append, List.nil_append, List.append_nil]
                        · intro z hz; rw [hqpath]
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                          tauto
                      · by_cases hyllk : y < lk
                        · refine ⟨[lk], ?_, ?_⟩
                          · simp only [sL hyllk, ds_both_lt hylt hqlt,
                              ds_div_lt hyllk hlkq,
                              List.cons_append, List.nil_append]
                          · intro z hz; rw [hqpath]
                            simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                            tauto
                        · have hlky : lk < y := by omega
                          refine ⟨[lk, k], ?_, ?_⟩
                          · simp only [sG hlky, sL hylt,
                              sE0, ds_both_lt hylt hqlt,
                              ds_both_gt hlky hlkq, dsE0,
                              List.cons_append, List.nil_append, List.append_nil]
                          · intro z hz; rw [hqpath]
                            simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                            tauto
                    · have hkly : k < y := by omega
                      have hlky : lk < y := by omega
                      refine ⟨[lk, k], ?_, ?_⟩
                      · simp only [sG hlky, sG hkly,
                          ds_div_gt hkly hqlt, List.cons_append, List.nil_append]
                      · intro z hz; rw [hqpath]
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                        tauto
                | node a x b =>
                  have hsz : (bN a x b).num_nodes ≤ n := by
                    have hnn : (bN (bN ll lk
                        (bN a x b)) k r).num_nodes
                        = 1 + (1 + ll.num_nodes + (bN a x b).num_nodes)
                          + r.num_nodes := rfl
                    omega
                  cases hs : splay (bN a x b) q with
                  | empty => exact absurd hs (sNE _ _ _ _)
                  | node A s B =>
                    rw [zaS ll (bN a x b) r A B lk k q s hqk hqlt
                      hlkq (fun h => nomatch h) hs]
                    have hsF1 := sF0 _ (bN a x b) q hbLR
                    have hsF2 := sF0 _ (bN a x b) q hbL_lr
                    rw [hs] at hsF1 hsF2
                    have hlks : lk < s := (fI.mp hsF1).2.1
                    have hsk : s < k := (fI.mp hsF2).2.1
                    obtain ⟨pq, hpq, hmq⟩ := ih (bN a x b) hsz q q hbstlr
                    rw [hs, dsQ, List.append_nil] at hpq
                    have hsq : s ∈ searchPath q (bN a x b) := by
                      apply hmq
                      rw [← hpq]
                      exact rM q s A B
                    have hqpath : searchPath q (bN
                        (bN ll lk (bN a x b)) k r)
                        = k :: lk :: searchPath q (bN a x b) := by
                      rw [sL hqlt, sG hlkq]
                    by_cases hyk : y = k
                    · have hsy : s < y := by omega
                      refine ⟨[s, k], ?_, ?_⟩
                      · simp only [sG hsy, sS hyk,
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
                          · simp only [sL hys, sS hylk,
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
                            · simp only [sL hys, sL hyllk,
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
                              ih (bN a x b) hsz q y hbstlr
                            rw [hs] at hp''
                            have hds : divergeSuffix y q (bN
                                (bN ll lk (bN a x b)) k r)
                                = divergeSuffix y q (bN a x b) := by
                              rw [ds_both_lt hylt hqlt, ds_both_gt hlky hlkq]
                            rw [hds]
                            rcases Nat.lt_trichotomy y s with hys | hys | hys
                            · rw [sL hys] at hp''
                              cases p'' with
                              | nil =>
                                exfalso
                                rw [List.nil_append] at hp''
                                have hsmem : s ∈ divergeSuffix y q (bN a x b) := by
                                  rw [← hp'']
                                  simp
                                exact dsD (bN a x b)
                                  hbstlr s hsmem hsq
                              | cons c p''' =>
                                rw [List.cons_append] at hp''
                                injection hp'' with hc htail
                                subst hc
                                refine ⟨s :: lk :: p''', ?_, ?_⟩
                                · simp only [sL hys, sG hlky,
                                    htail, List.cons_append]
                                · intro z hz
                                  rw [hqpath]
                                  simp only [List.mem_cons] at hz
                                  rcases hz with rfl | rfl | hz
                                  · simp [hsq]
                                  · simp
                                  · have hzin := hm'' z (by simp [hz])
                                    simp [hzin]
                            · rw [sS hys] at hp''
                              refine ⟨p'', ?_, ?_⟩
                              · rw [sS hys]
                                exact hp''
                              · intro z hz
                                rw [hqpath]
                                have hzin := hm'' z hz
                                simp [hzin]
                            · rw [sG hys] at hp''
                              cases p'' with
                              | nil =>
                                exfalso
                                rw [List.nil_append] at hp''
                                have hsmem : s ∈ divergeSuffix y q (bN a x b) := by
                                  rw [← hp'']
                                  simp
                                exact dsD (bN a x b)
                                  hbstlr s hsmem hsq
                              | cons c p''' =>
                                rw [List.cons_append] at hp''
                                injection hp'' with hc htail
                                subst hc
                                refine ⟨s :: k :: p''', ?_, ?_⟩
                                · simp only [sG hys, sL hylt,
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
                        · simp only [sG hsy, sG hkly,
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
                show ∃ p', searchPath y (bN ll lk (bN lr k r))
                    = p' ++ divergeSuffix y q
                        (bN (bN ll lk lr) k r)
                  ∧ ∀ z ∈ p',
                      z ∈ searchPath q (bN (bN ll lk lr) k r)
                have hqpath : searchPath q
                    (bN (bN ll lk lr) k r) = [k, lk] := by
                  rw [sL hqlt, sS hqeq]
                by_cases hyk : y = k
                · have hlky : lk < y := by omega
                  refine ⟨[lk, k], ?_, ?_⟩
                  · simp only [sG hlky, sS hyk,
                      ds_self hyk, List.cons_append, List.nil_append, List.append_nil]
                  · intro z hz; rw [hqpath]
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                    tauto
                · by_cases hylt : y < k
                  · by_cases hylk : y = lk
                    · refine ⟨[lk], ?_, ?_⟩
                      · simp only [sS hylk, ds_both_lt hylt hqlt,
                          ds_self hylk, List.cons_append, List.nil_append, List.append_nil]
                      · intro z hz; rw [hqpath]
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                        tauto
                    · by_cases hyllk : y < lk
                      · refine ⟨[lk], ?_, ?_⟩
                        · simp only [sL hyllk, ds_both_lt hylt hqlt,
                            ds_qroot_lt hqeq hyllk,
                            List.cons_append, List.nil_append]
                        · intro z hz; rw [hqpath]
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                          tauto
                      · have hlky : lk < y := by omega
                        refine ⟨[lk, k], ?_, ?_⟩
                        · simp only [sG hlky, sL hylt,
                            ds_both_lt hylt hqlt, ds_qroot_gt hqeq hlky,
                            List.cons_append, List.nil_append]
                        · intro z hz; rw [hqpath]
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                          tauto
                  · have hkly : k < y := by omega
                    have hlky : lk < y := by omega
                    refine ⟨[lk, k], ?_, ?_⟩
                    · simp only [sG hlky, sG hkly,
                        ds_div_gt hkly hqlt, List.cons_append, List.nil_append]
                    · intro z hz; rw [hqpath]
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                      tauto
        · -- k < q
          have hklt : k < q := by omega
          cases r with
          | empty =>
            rw [splay.eq_def]
            simp only [if_neg hqk, if_neg hqlt]
            show ∃ p', searchPath y (bN l k .empty)
                = p' ++ divergeSuffix y q (bN l k .empty)
              ∧ ∀ z ∈ p', z ∈ searchPath q (bN l k .empty)
            have hqpath : searchPath q (bN l k .empty) = [k] := by
              rw [sG hklt, sE0]
            by_cases hyk : y = k
            · refine ⟨[k], ?_, ?_⟩
              · simp only [sS hyk, ds_self hyk, List.append_nil]
              · intro z hz
                simp only [List.mem_singleton] at hz
                subst hz; rw [hqpath]; simp
            · by_cases hylt : y < k
              · refine ⟨[k], ?_, ?_⟩
                · simp only [sL hylt, ds_div_lt hylt hklt,
                    List.cons_append, List.nil_append]
                · intro z hz
                  simp only [List.mem_singleton] at hz
                  subst hz; rw [hqpath]; simp
              · have hkly : k < y := by omega
                refine ⟨[k], ?_, ?_⟩
                · simp only [sG hkly, sE0,
                    ds_both_gt hkly hklt, dsE0,
                    List.cons_append, List.nil_append, List.append_nil]
                · intro z hz
                  simp only [List.mem_singleton] at hz
                  subst hz; rw [hqpath]; simp
          | node rl rk rr =>
            rcases fI.mp hbR with ⟨hbR_rl, hk_rk, hbR_rr⟩
            rcases bI.mp hbstr with ⟨hbRL, hbRR, hbstrl, hbstrr⟩
            by_cases hqrk : q < rk
            · cases rl with
              | empty =>
                rw [splay.eq_def]
                simp only [if_neg hqk, if_neg hqlt, if_pos hqrk]
                show ∃ p', searchPath y (bN (bN l k .empty) rk rr)
                    = p' ++ divergeSuffix y q
                        (bN l k (bN .empty rk rr))
                  ∧ ∀ z ∈ p',
                      z ∈ searchPath q (bN l k (bN .empty rk rr))
                have hqpath : searchPath q
                    (bN l k (bN .empty rk rr)) = [k, rk] := by
                  rw [sG hklt, sL hqrk, sE0]
                by_cases hyk : y = k
                · have hyrk : y < rk := by omega
                  refine ⟨[rk, k], ?_, ?_⟩
                  · simp only [sL hyrk, sS hyk,
                      ds_self hyk, List.cons_append, List.nil_append, List.append_nil]
                  · intro z hz; rw [hqpath]
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                    tauto
                · by_cases hylt : y < k
                  · have hyrk : y < rk := by omega
                    refine ⟨[rk, k], ?_, ?_⟩
                    · simp only [sL hyrk, sL hylt,
                        ds_div_lt hylt hklt, List.cons_append, List.nil_append]
                    · intro z hz; rw [hqpath]
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                      tauto
                  · have hkly : k < y := by omega
                    by_cases hyrk : y = rk
                    · refine ⟨[rk], ?_, ?_⟩
                      · simp only [sS hyrk, ds_both_gt hkly hklt,
                          ds_self hyrk, List.cons_append, List.nil_append, List.append_nil]
                      · intro z hz; rw [hqpath]
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                        tauto
                    · by_cases hyrklt : y < rk
                      · refine ⟨[rk, k], ?_, ?_⟩
                        · simp only [sL hyrklt, sG hkly,
                            sE0, ds_both_gt hkly hklt,
                            ds_both_lt hyrklt hqrk, dsE0,
                            List.cons_append, List.nil_append, List.append_nil]
                        · intro z hz; rw [hqpath]
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                          tauto
                      · have hrky : rk < y := by omega
                        refine ⟨[rk], ?_, ?_⟩
                        · simp only [sG hrky, ds_both_gt hkly hklt,
                            ds_div_gt hrky hqrk, List.cons_append, List.nil_append]
                        · intro z hz; rw [hqpath]
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                          tauto
              | node a x b =>
                have hsz : (bN a x b).num_nodes ≤ n := by
                  have hnn : (bN l k (bN (bN a x b)
                      rk rr)).num_nodes
                      = 1 + l.num_nodes
                        + (1 + (bN a x b).num_nodes + rr.num_nodes) := rfl
                  omega
                cases hs : splay (bN a x b) q with
                | empty => exact absurd hs (sNE _ _ _ _)
                | node A s B =>
                  rw [aiS l (bN a x b) rr A B rk k q s hqk hklt
                    hqrk (fun h => nomatch h) hs]
                  have hsF1 := sF0 _ (bN a x b) q hbRL
                  have hsF2 := sF0 _ (bN a x b) q hbR_rl
                  rw [hs] at hsF1 hsF2
                  have hsrk : s < rk := (fI.mp hsF1).2.1
                  have hks : k < s := (fI.mp hsF2).2.1
                  obtain ⟨pq, hpq, hmq⟩ := ih (bN a x b) hsz q q hbstrl
                  rw [hs, dsQ, List.append_nil] at hpq
                  have hsq : s ∈ searchPath q (bN a x b) := by
                    apply hmq
                    rw [← hpq]
                    exact rM q s A B
                  have hqpath : searchPath q (bN l k
                      (bN (bN a x b) rk rr))
                      = k :: rk :: searchPath q (bN a x b) := by
                    rw [sG hklt, sL hqrk]
                  by_cases hyk : y = k
                  · have hys : y < s := by omega
                    refine ⟨[s, k], ?_, ?_⟩
                    · simp only [sL hys, sS hyk,
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
                      · simp only [sL hys, sL hylt,
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
                        · simp only [sG hsy, sS hyrk,
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
                            ih (bN a x b) hsz q y hbstrl
                          rw [hs] at hp''
                          have hds : divergeSuffix y q (bN l k
                              (bN (bN a x b) rk rr))
                              = divergeSuffix y q (bN a x b) := by
                            rw [ds_both_gt hkly hklt, ds_both_lt hyrklt hqrk]
                          rw [hds]
                          rcases Nat.lt_trichotomy y s with hys | hys | hys
                          · rw [sL hys] at hp''
                            cases p'' with
                            | nil =>
                              exfalso
                              rw [List.nil_append] at hp''
                              have hsmem : s ∈ divergeSuffix y q (bN a x b) := by
                                rw [← hp'']
                                simp
                              exact dsD (bN a x b)
                                hbstrl s hsmem hsq
                            | cons c p''' =>
                              rw [List.cons_append] at hp''
                              injection hp'' with hc htail
                              subst hc
                              refine ⟨s :: k :: p''', ?_, ?_⟩
                              · simp only [sL hys, sG hkly,
                                  htail, List.cons_append]
                              · intro z hz
                                rw [hqpath]
                                simp only [List.mem_cons] at hz
                                rcases hz with rfl | rfl | hz
                                · simp [hsq]
                                · simp
                                · have hzin := hm'' z (by simp [hz])
                                  simp [hzin]
                          · rw [sS hys] at hp''
                            refine ⟨p'', ?_, ?_⟩
                            · rw [sS hys]
                              exact hp''
                            · intro z hz
                              rw [hqpath]
                              have hzin := hm'' z hz
                              simp [hzin]
                          · rw [sG hys] at hp''
                            cases p'' with
                            | nil =>
                              exfalso
                              rw [List.nil_append] at hp''
                              have hsmem : s ∈ divergeSuffix y q (bN a x b) := by
                                rw [← hp'']
                                simp
                              exact dsD (bN a x b)
                                hbstrl s hsmem hsq
                            | cons c p''' =>
                              rw [List.cons_append] at hp''
                              injection hp'' with hc htail
                              subst hc
                              refine ⟨s :: rk :: p''', ?_, ?_⟩
                              · simp only [sG hys, sL hyrklt,
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
                          · simp only [sG hsy, sG hrky,
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
                  rw [splay.eq_def]
                  simp only [if_neg hqk, if_neg hqlt, if_neg hqrk, if_pos hrkq]
                  show ∃ p', searchPath y (bN (bN l k rl) rk .empty)
                      = p' ++ divergeSuffix y q
                          (bN l k (bN rl rk .empty))
                    ∧ ∀ z ∈ p',
                        z ∈ searchPath q (bN l k (bN rl rk .empty))
                  have hqpath : searchPath q
                      (bN l k (bN rl rk .empty)) = [k, rk] := by
                    rw [sG hklt, sG hrkq, sE0]
                  by_cases hyk : y = k
                  · have hyrk : y < rk := by omega
                    refine ⟨[rk, k], ?_, ?_⟩
                    · simp only [sL hyrk, sS hyk,
                        ds_self hyk, List.cons_append, List.nil_append, List.append_nil]
                    · intro z hz; rw [hqpath]
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                      tauto
                  · by_cases hylt : y < k
                    · have hyrk : y < rk := by omega
                      refine ⟨[rk, k], ?_, ?_⟩
                      · simp only [sL hyrk, sL hylt,
                          ds_div_lt hylt hklt, List.cons_append, List.nil_append]
                      · intro z hz; rw [hqpath]
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                        tauto
                    · have hkly : k < y := by omega
                      by_cases hyrk : y = rk
                      · refine ⟨[rk], ?_, ?_⟩
                        · simp only [sS hyrk, ds_both_gt hkly hklt,
                            ds_self hyrk, List.cons_append, List.nil_append, List.append_nil]
                        · intro z hz; rw [hqpath]
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                          tauto
                      · by_cases hyrklt : y < rk
                        · refine ⟨[rk, k], ?_, ?_⟩
                          · simp only [sL hyrklt, sG hkly,
                              ds_both_gt hkly hklt, ds_div_lt hyrklt hrkq,
                              List.cons_append, List.nil_append]
                          · intro z hz; rw [hqpath]
                            simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                            tauto
                        · have hrky : rk < y := by omega
                          refine ⟨[rk], ?_, ?_⟩
                          · simp only [sG hrky, sE0,
                              ds_both_gt hkly hklt, ds_both_gt hrky hrkq, dsE0,
                              List.cons_append, List.nil_append, List.append_nil]
                          · intro z hz; rw [hqpath]
                            simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                            tauto
                | node a x b =>
                  have hsz : (bN a x b).num_nodes ≤ n := by
                    have hnn : (bN l k (bN rl rk
                        (bN a x b))).num_nodes
                        = 1 + l.num_nodes
                          + (1 + rl.num_nodes + (bN a x b).num_nodes) := rfl
                    omega
                  cases hs : splay (bN a x b) q with
                  | empty => exact absurd hs (sNE _ _ _ _)
                  | node A s B =>
                    rw [azS l rl (bN a x b) A B rk k q s hqk hklt
                      hrkq (fun h => nomatch h) hs]
                    have hsF1 := sF0 _ (bN a x b) q hbRR
                    rw [hs] at hsF1
                    have hrks : rk < s := (fI.mp hsF1).2.1
                    obtain ⟨pq, hpq, hmq⟩ := ih (bN a x b) hsz q q hbstrr
                    rw [hs, dsQ, List.append_nil] at hpq
                    have hsq : s ∈ searchPath q (bN a x b) := by
                      apply hmq
                      rw [← hpq]
                      exact rM q s A B
                    have hqpath : searchPath q (bN l k
                        (bN rl rk (bN a x b)))
                        = k :: rk :: searchPath q (bN a x b) := by
                      rw [sG hklt, sG hrkq]
                    by_cases hyk : y = k
                    · have hys : y < s := by omega
                      have hyrk : y < rk := by omega
                      refine ⟨[s, rk, k], ?_, ?_⟩
                      · simp only [sL hys, sL hyrk,
                          sS hyk, ds_self hyk,
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
                        · simp only [sL hys, sL hyrk,
                            sL hylt, ds_div_lt hylt hklt,
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
                          · simp only [sL hys, sS hyrk,
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
                            · simp only [sL hys, sL hyrklt,
                                sG hkly, ds_both_gt hkly hklt,
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
                              ih (bN a x b) hsz q y hbstrr
                            rw [hs] at hp''
                            have hds : divergeSuffix y q (bN l k
                                (bN rl rk (bN a x b)))
                                = divergeSuffix y q (bN a x b) := by
                              rw [ds_both_gt hkly hklt, ds_both_gt hrky hrkq]
                            rw [hds]
                            rcases Nat.lt_trichotomy y s with hys | hys | hys
                            · rw [sL hys] at hp''
                              cases p'' with
                              | nil =>
                                exfalso
                                rw [List.nil_append] at hp''
                                have hsmem : s ∈ divergeSuffix y q (bN a x b) := by
                                  rw [← hp'']
                                  simp
                                exact dsD (bN a x b)
                                  hbstrr s hsmem hsq
                              | cons c p''' =>
                                rw [List.cons_append] at hp''
                                injection hp'' with hc htail
                                subst hc
                                refine ⟨s :: rk :: p''', ?_, ?_⟩
                                · simp only [sL hys, sG hrky,
                                    htail, List.cons_append]
                                · intro z hz
                                  rw [hqpath]
                                  simp only [List.mem_cons] at hz
                                  rcases hz with rfl | rfl | hz
                                  · simp [hsq]
                                  · simp
                                  · have hzin := hm'' z (by simp [hz])
                                    simp [hzin]
                            · rw [sS hys] at hp''
                              refine ⟨p'', ?_, ?_⟩
                              · rw [sS hys]
                                exact hp''
                              · intro z hz
                                rw [hqpath]
                                have hzin := hm'' z hz
                                simp [hzin]
                            · rw [sG hys] at hp''
                              refine ⟨p'', ?_, ?_⟩
                              · rw [sG hys]
                                exact hp''
                              · intro z hz
                                rw [hqpath]
                                have hzin := hm'' z hz
                                simp [hzin]
              · -- (13) found at the right child: q = rk, single ZAG
                have hqeq : q = rk := by omega
                rw [splay.eq_def]
                simp only [if_neg hqk, if_neg hqlt, if_neg hqrk, if_neg hrkq]
                show ∃ p', searchPath y (bN (bN l k rl) rk rr)
                    = p' ++ divergeSuffix y q
                        (bN l k (bN rl rk rr))
                  ∧ ∀ z ∈ p',
                      z ∈ searchPath q (bN l k (bN rl rk rr))
                have hqpath : searchPath q
                    (bN l k (bN rl rk rr)) = [k, rk] := by
                  rw [sG hklt, sS hqeq]
                by_cases hyk : y = k
                · have hyrk : y < rk := by omega
                  refine ⟨[rk, k], ?_, ?_⟩
                  · simp only [sL hyrk, sS hyk,
                      ds_self hyk, List.cons_append, List.nil_append, List.append_nil]
                  · intro z hz; rw [hqpath]
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                    tauto
                · by_cases hylt : y < k
                  · have hyrk : y < rk := by omega
                    refine ⟨[rk, k], ?_, ?_⟩
                    · simp only [sL hyrk, sL hylt,
                        ds_div_lt hylt hklt, List.cons_append, List.nil_append]
                    · intro z hz; rw [hqpath]
                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                      tauto
                  · have hkly : k < y := by omega
                    by_cases hyrk : y = rk
                    · refine ⟨[rk], ?_, ?_⟩
                      · simp only [sS hyrk, ds_both_gt hkly hklt,
                          ds_self hyrk, List.cons_append, List.nil_append, List.append_nil]
                      · intro z hz; rw [hqpath]
                        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                        tauto
                    · by_cases hyrklt : y < rk
                      · refine ⟨[rk, k], ?_, ?_⟩
                        · simp only [sL hyrklt, sG hkly,
                            ds_both_gt hkly hklt, ds_qroot_lt hqeq hyrklt,
                            List.cons_append, List.nil_append]
                        · intro z hz; rw [hqpath]
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                          tauto
                      · have hrky : rk < y := by omega
                        refine ⟨[rk], ?_, ?_⟩
                        · simp only [sG hrky, ds_both_gt hkly hklt,
                            ds_qroot_gt hqeq hrky, List.cons_append, List.nil_append]
                        · intro z hz; rw [hqpath]
                          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
                          tauto
theorem spd (q y : Nat) (t : BinaryTree) (hbst : IsBST t) :
    ∃ p', searchPath y (splay t q) = p' ++ divergeSuffix y q t
      ∧ ∀ z ∈ p', z ∈ searchPath q t :=
  spdA t.num_nodes t (Nat.le_refl _) q y hbst
def rootKey : BinaryTree → Nat
  | .empty => 0
  | .node _ k _ => k
theorem tcA (T a b : List Nat) :
    touchedCount T (a ++ b) = touchedCount T a + touchedCount T b := by
  simp [touchedCount, List.filter_append]
theorem tcC {T T' c : List Nat}
    (h : ∀ z ∈ c, (z ∈ T') ↔ (z ∈ T)) : touchedCount T' c = touchedCount T c := by
  simp only [touchedCount]
  congr 1
  exact List.filter_congr (fun x hx => decide_eq_decide.mpr (h x hx))
theorem sp_len (y : Nat) (t : BinaryTree) : (searchPath y t).length = kD y t := rfl
theorem kshA :
    ∀ (n : Nat) (t : BinaryTree), t.num_nodes ≤ n → ∀ (q y : Nat),
      IsBST t →
      2 * kD y (splay t q) ≤ kD y t + (divergeSuffix y q t).length + 5 := by
  intro n
  induction n with
  | zero =>
    intro t ht q y _
    cases t with
    | empty =>
      have h0 : splay bE q = bE := rfl
      rw [h0]
      simp only [kE, dsE0, List.length_nil]
      omega
    | node l k r =>
      exfalso
      have hnn : (bN l k r).num_nodes = 1 + l.num_nodes + r.num_nodes := rfl
      omega
  | succ n ih =>
    intro t ht q y hbst
    cases t with
    | empty =>
      have h0 : splay bE q = bE := rfl
      rw [h0]
      simp only [kE, dsE0, List.length_nil]
      omega
    | node l k r =>
      rcases bI.mp hbst with ⟨hfl, hfr, hbl, hbr⟩
      by_cases hqk : q = k
      · -- (1) q found at the root: splay returns t
        rw [splay.eq_def]
        simp only [if_pos hqk]
        by_cases hyk : y = k
        · rw [ds_self hyk]
          have h1 : kD y (bN l k r) = 1 := kS hyk _ _
          simp only [List.length_nil]
          omega
        · by_cases hylt : y < k
          · rw [ds_qroot_lt hqk hylt, sp_len]
            have h1 : kD y (bN l k r) = kD y l + 1 :=
              kL hylt _ _
            omega
          · have hkly : k < y := by omega
            rw [ds_qroot_gt hqk hkly, sp_len]
            have h1 : kD y (bN l k r) = kD y r + 1 :=
              kG hkly _ _
            omega
      · by_cases hqlt : q < k
        · cases l with
          | empty =>
            rw [splay.eq_def]
            simp only [if_neg hqk, if_pos hqlt]
            by_cases hyk : y = k
            · rw [ds_self hyk]
              have h1 : kD y (bN bE k r) = 1 :=
                kS hyk _ _
              simp only [List.length_nil]
              omega
            · by_cases hylt : y < k
              · rw [ds_both_lt hylt hqlt, dsE0]
                have h1 : kD y (bN bE k r)
                    = kD y bE + 1 := kL hylt _ _
                have h2 : kD y bE = 0 := rfl
                simp only [List.length_nil]
                omega
              · have hkly : k < y := by omega
                rw [ds_div_gt hkly hqlt, sp_len]
                have h1 : kD y (bN bE k r)
                    = kD y r + 1 := kG hkly _ _
                omega
          | node ll lk lr =>
            rcases fI.mp hfl with ⟨hfll, hlkk, hflr⟩
            rcases bI.mp hbl with ⟨hll_lt, hlr_gt, hbll, hblr⟩
            by_cases hqlk : q < lk
            · cases ll with
              | empty =>
                rw [splay.eq_def]
                simp only [if_neg hqk, if_pos hqlt, if_pos hqlk]
                show 2 * kD y (bN bE lk (bN lr k r))
                    ≤ kD y (bN (bN bE lk lr) k r)
                      + (divergeSuffix y q
                          (bN (bN bE lk lr) k r)).length
                      + 5
                by_cases hyk : y = k
                · rw [ds_self hyk]
                  have h1 : kD y
                      (bN bE lk (bN lr k r))
                      = kD y (bN lr k r) + 1 :=
                    kG (by omega) _ _
                  have h2 : kD y (bN lr k r) = 1 := kS hyk _ _
                  have h3 : kD y
                      (bN (bN bE lk lr) k r) = 1 :=
                    kS hyk _ _
                  simp only [List.length_nil]
                  omega
                · by_cases hylt : y < k
                  · by_cases hylk : y = lk
                    · rw [ds_both_lt hylt hqlt, ds_self hylk]
                      have h1 : kD y
                          (bN bE lk (bN lr k r)) = 1 :=
                        kS hylk _ _
                      simp only [List.length_nil]
                      omega
                    · by_cases hylk2 : y < lk
                      · rw [ds_both_lt hylt hqlt, ds_both_lt hylk2 hqlk, dsE0]
                        have h1 : kD y
                            (bN bE lk (bN lr k r))
                            = kD y bE + 1 := kL hylk2 _ _
                        have h2 : kD y bE = 0 := rfl
                        simp only [List.length_nil]
                        omega
                      · have hlky : lk < y := by omega
                        rw [ds_both_lt hylt hqlt, ds_div_gt hlky hqlk, sp_len]
                        have h1 : kD y
                            (bN bE lk (bN lr k r))
                            = kD y (bN lr k r) + 1 :=
                          kG hlky _ _
                        have h2 : kD y (bN lr k r) = kD y lr + 1 :=
                          kL hylt _ _
                        have h3 : kD y
                            (bN (bN bE lk lr) k r)
                            = kD y (bN bE lk lr) + 1 :=
                          kL hylt _ _
                        have h4 : kD y (bN bE lk lr)
                            = kD y lr + 1 := kG hlky _ _
                        omega
                  · have hkly : k < y := by omega
                    rw [ds_div_gt hkly hqlt, sp_len]
                    have h1 : kD y
                        (bN bE lk (bN lr k r))
                        = kD y (bN lr k r) + 1 :=
                      kG (by omega) _ _
                    have h2 : kD y (bN lr k r) = kD y r + 1 :=
                      kG hkly _ _
                    have h3 : kD y
                        (bN (bN bE lk lr) k r)
                        = kD y r + 1 := kG hkly _ _
                    omega
              | node a x b =>
                have hsz : (bN a x b).num_nodes ≤ n := by
                  have hnn : (bN
                      (bN (bN a x b) lk lr) k r).num_nodes
                      = 1 + (1 + (bN a x b).num_nodes + lr.num_nodes)
                        + r.num_nodes := rfl
                  omega
                cases hs : splay (bN a x b) q with
                | empty => exact absurd hs (sNE _ _ _ _)
                | node A s B =>
                  have hsA : ForallTree (fun z => z < lk) (splay (bN a x b) q) :=
                    sF0 _ _ _ hll_lt
                  rw [hs] at hsA
                  rcases fI.mp hsA with ⟨hAlt, hslk, hBlt⟩
                  rw [zzS (bN a x b) lr r A B lk k q s hqk hqlt
                    hqlk (fun h => nomatch h) hs]
                  by_cases hyk : y = k
                  · -- y = k : depth 1 → 3 (tight, 2*3 = 1 + 0 + 5)
                    rw [ds_self hyk]
                    have h1 : kD y
                        (bN A s (bN B lk (bN lr k r)))
                        = kD y (bN B lk (bN lr k r)) + 1 :=
                      kG (by omega) _ _
                    have h2 : kD y (bN B lk (bN lr k r))
                        = kD y (bN lr k r) + 1 :=
                      kG (by omega) _ _
                    have h3 : kD y (bN lr k r) = 1 :=
                      kS hyk _ _
                    have h4 : kD y (bN
                        (bN (bN a x b) lk lr) k r) = 1 :=
                      kS hyk _ _
                    simp only [List.length_nil]
                    omega
                  · by_cases hylt : y < k
                    · by_cases hylk : y = lk
                      · rw [ds_both_lt hylt hqlt, ds_self hylk]
                        have h1 : kD y
                            (bN A s (bN B lk (bN lr k r)))
                            = kD y (bN B lk (bN lr k r)) + 1 :=
                          kG (by omega) _ _
                        have h2 : kD y (bN B lk (bN lr k r)) = 1 :=
                          kS hylk _ _
                        simp only [List.length_nil]
                        omega
                      · by_cases hylk2 : y < lk
                        · -- y in the recursion zone: IH on the grandchild
                          rw [ds_both_lt hylt hqlt, ds_both_lt hylk2 hqlk]
                          have hIH := ih _ hsz q y hbll
                          rw [hs] at hIH
                          have h3 : kD y (bN
                              (bN (bN a x b) lk lr) k r)
                              = kD y (bN (bN a x b) lk lr) + 1 :=
                            kL hylt _ _
                          have h4 : kD y (bN (bN a x b) lk lr)
                              = kD y (bN a x b) + 1 :=
                            kL hylk2 _ _
                          rcases Nat.lt_trichotomy y s with hys | hys | hys
                          · have h1 : kD y (bN A s
                                (bN B lk (bN lr k r)))
                                = kD y A + 1 := kL hys _ _
                            have h2 : kD y (bN A s B) = kD y A + 1 :=
                              kL hys _ _
                            omega
                          · have h1 : kD y (bN A s
                                (bN B lk (bN lr k r)))
                                = 1 := kS hys _ _
                            omega
                          · have h1 : kD y (bN A s
                                (bN B lk (bN lr k r)))
                                = kD y (bN B lk (bN lr k r)) + 1 :=
                              kG hys _ _
                            have h2 : kD y (bN B lk (bN lr k r))
                                = kD y B + 1 := kL hylk2 _ _
                            have h5 : kD y (bN A s B) = kD y B + 1 :=
                              kG hys _ _
                            omega
                        · -- lk < y < k : y lands in the cargo subtree lr
                          have hlky : lk < y := by omega
                          rw [ds_both_lt hylt hqlt, ds_div_gt hlky hqlk, sp_len]
                          have h1 : kD y (bN A s
                              (bN B lk (bN lr k r)))
                              = kD y (bN B lk (bN lr k r)) + 1 :=
                            kG (by omega) _ _
                          have h2 : kD y (bN B lk (bN lr k r))
                              = kD y (bN lr k r) + 1 :=
                            kG hlky _ _
                          have h3 : kD y (bN lr k r)
                              = kD y lr + 1 := kL hylt _ _
                          have h4 : kD y (bN
                              (bN (bN a x b) lk lr) k r)
                              = kD y (bN (bN a x b) lk lr) + 1 :=
                            kL hylt _ _
                          have h5 : kD y (bN (bN a x b) lk lr)
                              = kD y lr + 1 := kG hlky _ _
                          omega
                    · -- k < y : y lands in the cargo subtree r (tight: 2d+6 ≤ 2d+6)
                      have hkly : k < y := by omega
                      rw [ds_div_gt hkly hqlt, sp_len]
                      have h1 : kD y (bN A s
                          (bN B lk (bN lr k r)))
                          = kD y (bN B lk (bN lr k r)) + 1 :=
                        kG (by omega) _ _
                      have h2 : kD y (bN B lk (bN lr k r))
                          = kD y (bN lr k r) + 1 :=
                        kG (by omega) _ _
                      have h3 : kD y (bN lr k r)
                          = kD y r + 1 := kG hkly _ _
                      have h4 : kD y (bN
                          (bN (bN a x b) lk lr) k r)
                          = kD y r + 1 := kG hkly _ _
                      omega
            · by_cases hlkq : lk < q
              · cases lr with
                | empty =>
                  rw [splay.eq_def]
                  simp only [if_neg hqk, if_pos hqlt, if_neg hqlk, if_pos hlkq]
                  show 2 * kD y (bN ll lk (bN bE k r))
                      ≤ kD y (bN (bN ll lk bE) k r)
                        + (divergeSuffix y q
                            (bN (bN ll lk bE) k r)).length
                        + 5
                  by_cases hyk : y = k
                  · rw [ds_self hyk]
                    have h1 : kD y
                        (bN ll lk (bN bE k r))
                        = kD y (bN bE k r) + 1 :=
                      kG (by omega) _ _
                    have h2 : kD y (bN bE k r) = 1 :=
                      kS hyk _ _
                    have h3 : kD y
                        (bN (bN ll lk bE) k r) = 1 :=
                      kS hyk _ _
                    simp only [List.length_nil]
                    omega
                  · by_cases hylt : y < k
                    · by_cases hylk : y = lk
                      · rw [ds_both_lt hylt hqlt, ds_self hylk]
                        have h1 : kD y
                            (bN ll lk (bN bE k r)) = 1 :=
                          kS hylk _ _
                        simp only [List.length_nil]
                        omega
                      · by_cases hylk2 : y < lk
                        · rw [ds_both_lt hylt hqlt, ds_div_lt hylk2 hlkq, sp_len]
                          have h1 : kD y
                              (bN ll lk (bN bE k r))
                              = kD y ll + 1 := kL hylk2 _ _
                          have h2 : kD y
                              (bN (bN ll lk bE) k r)
                              = kD y (bN ll lk bE) + 1 :=
                            kL hylt _ _
                          have h3 : kD y (bN ll lk bE)
                              = kD y ll + 1 := kL hylk2 _ _
                          omega
                        · have hlky : lk < y := by omega
                          rw [ds_both_lt hylt hqlt, ds_both_gt hlky hlkq, dsE0]
                          have h1 : kD y
                              (bN ll lk (bN bE k r))
                              = kD y (bN bE k r) + 1 :=
                            kG hlky _ _
                          have h2 : kD y (bN bE k r)
                              = kD y bE + 1 := kL hylt _ _
                          have h3 : kD y bE = 0 := rfl
                          simp only [List.length_nil]
                          omega
                    · have hkly : k < y := by omega
                      rw [ds_div_gt hkly hqlt, sp_len]
                      have h1 : kD y
                          (bN ll lk (bN bE k r))
                          = kD y (bN bE k r) + 1 :=
                        kG (by omega) _ _
                      have h2 : kD y (bN bE k r)
                          = kD y r + 1 := kG hkly _ _
                      have h3 : kD y
                          (bN (bN ll lk bE) k r)
                          = kD y r + 1 := kG hkly _ _
                      omega
                | node a x b =>
                  have hsz : (bN a x b).num_nodes ≤ n := by
                    have hnn : (bN
                        (bN ll lk (bN a x b)) k r).num_nodes
                        = 1 + (1 + ll.num_nodes + (bN a x b).num_nodes)
                          + r.num_nodes := rfl
                    omega
                  cases hs : splay (bN a x b) q with
                  | empty => exact absurd hs (sNE _ _ _ _)
                  | node A s B =>
                    have hsA : ForallTree (fun z => lk < z) (splay (bN a x b) q) :=
                      sF0 _ _ _ hlr_gt
                    rw [hs] at hsA
                    rcases fI.mp hsA with ⟨hAgt, hlks, hBgt⟩
                    have hsK : ForallTree (fun z => z < k) (splay (bN a x b) q) :=
                      sF0 _ _ _ hflr
                    rw [hs] at hsK
                    rcases fI.mp hsK with ⟨hAk, hsk, hBk⟩
                    rw [zaS ll (bN a x b) r A B lk k q s hqk hqlt
                      hlkq (fun h => nomatch h) hs]
                    by_cases hyk : y = k
                    · rw [ds_self hyk]
                      have h1 : kD y
                          (bN (bN ll lk A) s (bN B k r))
                          = kD y (bN B k r) + 1 :=
                        kG (by omega) _ _
                      have h2 : kD y (bN B k r) = 1 :=
                        kS hyk _ _
                      have h3 : kD y (bN
                          (bN ll lk (bN a x b)) k r) = 1 :=
                        kS hyk _ _
                      simp only [List.length_nil]
                      omega
                    · by_cases hylt : y < k
                      · by_cases hylk : y = lk
                        · rw [ds_both_lt hylt hqlt, ds_self hylk]
                          have h1 : kD y
                              (bN (bN ll lk A) s (bN B k r))
                              = kD y (bN ll lk A) + 1 :=
                            kL (by omega) _ _
                          have h2 : kD y (bN ll lk A) = 1 :=
                            kS hylk _ _
                          simp only [List.length_nil]
                          omega
                        · by_cases hylk2 : y < lk
                          · -- y < lk : y lands in the cargo subtree ll
                            rw [ds_both_lt hylt hqlt, ds_div_lt hylk2 hlkq, sp_len]
                            have h1 : kD y (bN
                                (bN ll lk A) s (bN B k r))
                                = kD y (bN ll lk A) + 1 :=
                              kL (by omega) _ _
                            have h2 : kD y (bN ll lk A)
                                = kD y ll + 1 := kL hylk2 _ _
                            have h3 : kD y (bN
                                (bN ll lk (bN a x b)) k r)
                                = kD y (bN ll lk (bN a x b)) + 1 :=
                              kL hylt _ _
                            have h4 : kD y (bN ll lk (bN a x b))
                                = kD y ll + 1 := kL hylk2 _ _
                            omega
                          · -- lk < y < k : y in the recursion zone
                            have hlky : lk < y := by omega
                            rw [ds_both_lt hylt hqlt, ds_both_gt hlky hlkq]
                            have hIH := ih _ hsz q y hblr
                            rw [hs] at hIH
                            have h3 : kD y (bN
                                (bN ll lk (bN a x b)) k r)
                                = kD y (bN ll lk (bN a x b)) + 1 :=
                              kL hylt _ _
                            have h4 : kD y (bN ll lk (bN a x b))
                                = kD y (bN a x b) + 1 :=
                              kG hlky _ _
                            rcases Nat.lt_trichotomy y s with hys | hys | hys
                            · have h1 : kD y (bN
                                  (bN ll lk A) s (bN B k r))
                                  = kD y (bN ll lk A) + 1 :=
                                kL hys _ _
                              have h2 : kD y (bN ll lk A)
                                  = kD y A + 1 := kG hlky _ _
                              have h5 : kD y (bN A s B) = kD y A + 1 :=
                                kL hys _ _
                              omega
                            · have h1 : kD y (bN
                                  (bN ll lk A) s (bN B k r))
                                  = 1 := kS hys _ _
                              omega
                            · have h1 : kD y (bN
                                  (bN ll lk A) s (bN B k r))
                                  = kD y (bN B k r) + 1 :=
                                kG hys _ _
                              have h2 : kD y (bN B k r)
                                  = kD y B + 1 := kL hylt _ _
                              have h5 : kD y (bN A s B) = kD y B + 1 :=
                                kG hys _ _
                              omega
                      · -- k < y : y lands in the cargo subtree r
                        have hkly : k < y := by omega
                        rw [ds_div_gt hkly hqlt, sp_len]
                        have h1 : kD y (bN
                            (bN ll lk A) s (bN B k r))
                            = kD y (bN B k r) + 1 :=
                          kG (by omega) _ _
                        have h2 : kD y (bN B k r)
                            = kD y r + 1 := kG hkly _ _
                        have h3 : kD y (bN
                            (bN ll lk (bN a x b)) k r)
                            = kD y r + 1 := kG hkly _ _
                        omega
              · -- (7) q found at the left child (q = lk): single ZIG
                have hqlk_eq : q = lk := by omega
                rw [splay.eq_def]
                simp only [if_neg hqk, if_pos hqlt, if_neg hqlk, if_neg hlkq]
                show 2 * kD y (bN ll lk (bN lr k r))
                    ≤ kD y (bN (bN ll lk lr) k r)
                      + (divergeSuffix y q
                          (bN (bN ll lk lr) k r)).length + 5
                by_cases hyk : y = k
                · rw [ds_self hyk]
                  have h1 : kD y (bN ll lk (bN lr k r))
                      = kD y (bN lr k r) + 1 :=
                    kG (by omega) _ _
                  have h2 : kD y (bN lr k r) = 1 := kS hyk _ _
                  have h3 : kD y (bN (bN ll lk lr) k r) = 1 :=
                    kS hyk _ _
                  simp only [List.length_nil]
                  omega
                · by_cases hylt : y < k
                  · by_cases hylk : y = lk
                    · rw [ds_both_lt hylt hqlt, ds_self hylk]
                      have h1 : kD y (bN ll lk (bN lr k r)) = 1 :=
                        kS hylk _ _
                      simp only [List.length_nil]
                      omega
                    · by_cases hylk2 : y < lk
                      · rw [ds_both_lt hylt hqlt, ds_qroot_lt hqlk_eq hylk2, sp_len]
                        have h1 : kD y (bN ll lk (bN lr k r))
                            = kD y ll + 1 := kL hylk2 _ _
                        have h2 : kD y (bN (bN ll lk lr) k r)
                            = kD y (bN ll lk lr) + 1 :=
                          kL hylt _ _
                        have h3 : kD y (bN ll lk lr)
                            = kD y ll + 1 := kL hylk2 _ _
                        omega
                      · have hlky : lk < y := by omega
                        rw [ds_both_lt hylt hqlt, ds_qroot_gt hqlk_eq hlky, sp_len]
                        have h1 : kD y (bN ll lk (bN lr k r))
                            = kD y (bN lr k r) + 1 :=
                          kG hlky _ _
                        have h2 : kD y (bN lr k r)
                            = kD y lr + 1 := kL hylt _ _
                        have h3 : kD y (bN (bN ll lk lr) k r)
                            = kD y (bN ll lk lr) + 1 :=
                          kL hylt _ _
                        have h4 : kD y (bN ll lk lr)
                            = kD y lr + 1 := kG hlky _ _
                        omega
                  · have hkly : k < y := by omega
                    rw [ds_div_gt hkly hqlt, sp_len]
                    have h1 : kD y (bN ll lk (bN lr k r))
                        = kD y (bN lr k r) + 1 :=
                      kG (by omega) _ _
                    have h2 : kD y (bN lr k r)
                        = kD y r + 1 := kG hkly _ _
                    have h3 : kD y (bN (bN ll lk lr) k r)
                        = kD y r + 1 := kG hkly _ _
                    omega
        · -- k < q : symmetric (zag) side
          have hklt : k < q := by omega
          cases r with
          | empty =>
            rw [splay.eq_def]
            simp only [if_neg hqk, if_neg hqlt]
            by_cases hyk : y = k
            · rw [ds_self hyk]
              have h1 : kD y (bN l k bE) = 1 :=
                kS hyk _ _
              simp only [List.length_nil]
              omega
            · by_cases hylt : y < k
              · rw [ds_div_lt hylt hklt, sp_len]
                have h1 : kD y (bN l k bE)
                    = kD y l + 1 := kL hylt _ _
                omega
              · have hkly : k < y := by omega
                rw [ds_both_gt hkly hklt, dsE0]
                have h1 : kD y (bN l k bE)
                    = kD y bE + 1 := kG hkly _ _
                have h2 : kD y bE = 0 := rfl
                simp only [List.length_nil]
                omega
          | node rl rk rr =>
            rcases fI.mp hfr with ⟨hfrl, hkrk, hfrr⟩
            rcases bI.mp hbr with ⟨hrl_lt, hrr_gt, hbrl, hbrr⟩
            by_cases hqrk : q < rk
            · cases rl with
              | empty =>
                rw [splay.eq_def]
                simp only [if_neg hqk, if_neg hqlt, if_pos hqrk]
                show 2 * kD y (bN (bN l k bE) rk rr)
                    ≤ kD y (bN l k (bN bE rk rr))
                      + (divergeSuffix y q
                          (bN l k (bN bE rk rr))).length
                      + 5
                by_cases hyk : y = k
                · rw [ds_self hyk]
                  have h1 : kD y
                      (bN (bN l k bE) rk rr)
                      = kD y (bN l k bE) + 1 :=
                    kL (by omega) _ _
                  have h2 : kD y (bN l k bE) = 1 :=
                    kS hyk _ _
                  have h3 : kD y
                      (bN l k (bN bE rk rr)) = 1 :=
                    kS hyk _ _
                  simp only [List.length_nil]
                  omega
                · by_cases hylt : y < k
                  · rw [ds_div_lt hylt hklt, sp_len]
                    have h1 : kD y
                        (bN (bN l k bE) rk rr)
                        = kD y (bN l k bE) + 1 :=
                      kL (by omega) _ _
                    have h2 : kD y (bN l k bE)
                        = kD y l + 1 := kL hylt _ _
                    have h3 : kD y
                        (bN l k (bN bE rk rr))
                        = kD y l + 1 := kL hylt _ _
                    omega
                  · have hkly : k < y := by omega
                    by_cases hyrk : y = rk
                    · rw [ds_both_gt hkly hklt, ds_self hyrk]
                      have h1 : kD y
                          (bN (bN l k bE) rk rr) = 1 :=
                        kS hyrk _ _
                      simp only [List.length_nil]
                      omega
                    · by_cases hyrk2 : y < rk
                      · rw [ds_both_gt hkly hklt, ds_both_lt hyrk2 hqrk, dsE0]
                        have h1 : kD y
                            (bN (bN l k bE) rk rr)
                            = kD y (bN l k bE) + 1 :=
                          kL hyrk2 _ _
                        have h2 : kD y (bN l k bE)
                            = kD y bE + 1 := kG hkly _ _
                        have h3 : kD y bE = 0 := rfl
                        simp only [List.length_nil]
                        omega
                      · have hrky : rk < y := by omega
                        rw [ds_both_gt hkly hklt, ds_div_gt hrky hqrk, sp_len]
                        have h1 : kD y
                            (bN (bN l k bE) rk rr)
                            = kD y rr + 1 := kG hrky _ _
                        have h2 : kD y
                            (bN l k (bN bE rk rr))
                            = kD y (bN bE rk rr) + 1 :=
                          kG hkly _ _
                        have h3 : kD y (bN bE rk rr)
                            = kD y rr + 1 := kG hrky _ _
                        omega
              | node a x b =>
                have hsz : (bN a x b).num_nodes ≤ n := by
                  have hnn : (bN l k
                      (bN (bN a x b) rk rr)).num_nodes
                      = 1 + l.num_nodes
                        + (1 + (bN a x b).num_nodes + rr.num_nodes) := rfl
                  omega
                cases hs : splay (bN a x b) q with
                | empty => exact absurd hs (sNE _ _ _ _)
                | node A s B =>
                  have hsA : ForallTree (fun z => k < z) (splay (bN a x b) q) :=
                    sF0 _ _ _ hfrl
                  rw [hs] at hsA
                  rcases fI.mp hsA with ⟨hAgt, hks, hBgt⟩
                  have hsK : ForallTree (fun z => z < rk) (splay (bN a x b) q) :=
                    sF0 _ _ _ hrl_lt
                  rw [hs] at hsK
                  rcases fI.mp hsK with ⟨hArk, hsrk, hBrk⟩
                  rw [aiS l (bN a x b) rr A B rk k q s hqk hklt
                    hqrk (fun h => nomatch h) hs]
                  by_cases hyk : y = k
                  · rw [ds_self hyk]
                    have h1 : kD y
                        (bN (bN l k A) s (bN B rk rr))
                        = kD y (bN l k A) + 1 :=
                      kL (by omega) _ _
                    have h2 : kD y (bN l k A) = 1 :=
                      kS hyk _ _
                    have h3 : kD y (bN l k
                        (bN (bN a x b) rk rr)) = 1 :=
                      kS hyk _ _
                    simp only [List.length_nil]
                    omega
                  · by_cases hylt : y < k
                    · -- y < k : y lands in the cargo subtree l
                      rw [ds_div_lt hylt hklt, sp_len]
                      have h1 : kD y
                          (bN (bN l k A) s (bN B rk rr))
                          = kD y (bN l k A) + 1 :=
                        kL (by omega) _ _
                      have h2 : kD y (bN l k A)
                          = kD y l + 1 := kL hylt _ _
                      have h3 : kD y (bN l k
                          (bN (bN a x b) rk rr))
                          = kD y l + 1 := kL hylt _ _
                      omega
                    · have hkly : k < y := by omega
                      by_cases hyrk : y = rk
                      · rw [ds_both_gt hkly hklt, ds_self hyrk]
                        have h1 : kD y
                            (bN (bN l k A) s (bN B rk rr))
                            = kD y (bN B rk rr) + 1 :=
                          kG (by omega) _ _
                        have h2 : kD y (bN B rk rr) = 1 :=
                          kS hyrk _ _
                        simp only [List.length_nil]
                        omega
                      · by_cases hyrk2 : y < rk
                        · -- k < y < rk : y in the recursion zone
                          rw [ds_both_gt hkly hklt, ds_both_lt hyrk2 hqrk]
                          have hIH := ih _ hsz q y hbrl
                          rw [hs] at hIH
                          have h3 : kD y (bN l k
                              (bN (bN a x b) rk rr))
                              = kD y (bN (bN a x b) rk rr) + 1 :=
                            kG hkly _ _
                          have h4 : kD y (bN (bN a x b) rk rr)
                              = kD y (bN a x b) + 1 :=
                            kL hyrk2 _ _
                          rcases Nat.lt_trichotomy y s with hys | hys | hys
                          · have h1 : kD y (bN
                                (bN l k A) s (bN B rk rr))
                                = kD y (bN l k A) + 1 :=
                              kL hys _ _
                            have h2 : kD y (bN l k A)
                                = kD y A + 1 := kG hkly _ _
                            have h5 : kD y (bN A s B) = kD y A + 1 :=
                              kL hys _ _
                            omega
                          · have h1 : kD y (bN
                                (bN l k A) s (bN B rk rr))
                                = 1 := kS hys _ _
                            omega
                          · have h1 : kD y (bN
                                (bN l k A) s (bN B rk rr))
                                = kD y (bN B rk rr) + 1 :=
                              kG hys _ _
                            have h2 : kD y (bN B rk rr)
                                = kD y B + 1 := kL hyrk2 _ _
                            have h5 : kD y (bN A s B) = kD y B + 1 :=
                              kG hys _ _
                            omega
                        · -- rk < y : y lands in the cargo subtree rr
                          have hrky : rk < y := by omega
                          rw [ds_both_gt hkly hklt, ds_div_gt hrky hqrk, sp_len]
                          have h1 : kD y (bN
                              (bN l k A) s (bN B rk rr))
                              = kD y (bN B rk rr) + 1 :=
                            kG (by omega) _ _
                          have h2 : kD y (bN B rk rr)
                              = kD y rr + 1 := kG hrky _ _
                          have h3 : kD y (bN l k
                              (bN (bN a x b) rk rr))
                              = kD y (bN (bN a x b) rk rr) + 1 :=
                            kG hkly _ _
                          have h4 : kD y (bN (bN a x b) rk rr)
                              = kD y rr + 1 := kG hrky _ _
                          omega
            · by_cases hrkq : rk < q
              · cases rr with
                | empty =>
                  rw [splay.eq_def]
                  simp only [if_neg hqk, if_neg hqlt, if_neg hqrk, if_pos hrkq]
                  show 2 * kD y
                      (bN (bN l k rl) rk bE)
                      ≤ kD y (bN l k (bN rl rk bE))
                        + (divergeSuffix y q
                            (bN l k (bN rl rk bE))).length
                        + 5
                  by_cases hyk : y = k
                  · rw [ds_self hyk]
                    have h1 : kD y
                        (bN (bN l k rl) rk bE)
                        = kD y (bN l k rl) + 1 :=
                      kL (by omega) _ _
                    have h2 : kD y (bN l k rl) = 1 :=
                      kS hyk _ _
                    have h3 : kD y
                        (bN l k (bN rl rk bE)) = 1 :=
                      kS hyk _ _
                    simp only [List.length_nil]
                    omega
                  · by_cases hylt : y < k
                    · rw [ds_div_lt hylt hklt, sp_len]
                      have h1 : kD y
                          (bN (bN l k rl) rk bE)
                          = kD y (bN l k rl) + 1 :=
                        kL (by omega) _ _
                      have h2 : kD y (bN l k rl)
                          = kD y l + 1 := kL hylt _ _
                      have h3 : kD y
                          (bN l k (bN rl rk bE))
                          = kD y l + 1 := kL hylt _ _
                      omega
                    · have hkly : k < y := by omega
                      by_cases hyrk : y = rk
                      · rw [ds_both_gt hkly hklt, ds_self hyrk]
                        have h1 : kD y
                            (bN (bN l k rl) rk bE) = 1 :=
                          kS hyrk _ _
                        simp only [List.length_nil]
                        omega
                      · by_cases hyrk2 : y < rk
                        · rw [ds_both_gt hkly hklt, ds_div_lt hyrk2 hrkq, sp_len]
                          have h1 : kD y
                              (bN (bN l k rl) rk bE)
                              = kD y (bN l k rl) + 1 :=
                            kL hyrk2 _ _
                          have h2 : kD y (bN l k rl)
                              = kD y rl + 1 := kG hkly _ _
                          have h3 : kD y
                              (bN l k (bN rl rk bE))
                              = kD y (bN rl rk bE) + 1 :=
                            kG hkly _ _
                          have h4 : kD y (bN rl rk bE)
                              = kD y rl + 1 := kL hyrk2 _ _
                          omega
                        · have hrky : rk < y := by omega
                          rw [ds_both_gt hkly hklt, ds_both_gt hrky hrkq, dsE0]
                          have h1 : kD y
                              (bN (bN l k rl) rk bE)
                              = kD y bE + 1 := kG hrky _ _
                          have h2 : kD y bE = 0 := rfl
                          simp only [List.length_nil]
                          omega
                | node a x b =>
                  have hsz : (bN a x b).num_nodes ≤ n := by
                    have hnn : (bN l k
                        (bN rl rk (bN a x b))).num_nodes
                        = 1 + l.num_nodes
                          + (1 + rl.num_nodes + (bN a x b).num_nodes) := rfl
                    omega
                  cases hs : splay (bN a x b) q with
                  | empty => exact absurd hs (sNE _ _ _ _)
                  | node A s B =>
                    have hsA : ForallTree (fun z => rk < z) (splay (bN a x b) q) :=
                      sF0 _ _ _ hrr_gt
                    rw [hs] at hsA
                    rcases fI.mp hsA with ⟨hAgt, hrks, hBgt⟩
                    rw [azS l rl (bN a x b) A B rk k q s hqk hklt
                      hrkq (fun h => nomatch h) hs]
                    by_cases hyk : y = k
                    · -- y = k : depth 1 → 3 (tight, 2*3 = 1 + 0 + 5)
                      rw [ds_self hyk]
                      have h1 : kD y (bN
                          (bN (bN l k rl) rk A) s B)
                          = kD y (bN (bN l k rl) rk A) + 1 :=
                        kL (by omega) _ _
                      have h2 : kD y (bN (bN l k rl) rk A)
                          = kD y (bN l k rl) + 1 :=
                        kL (by omega) _ _
                      have h3 : kD y (bN l k rl) = 1 :=
                        kS hyk _ _
                      have h4 : kD y (bN l k
                          (bN rl rk (bN a x b))) = 1 :=
                        kS hyk _ _
                      simp only [List.length_nil]
                      omega
                    · by_cases hylt : y < k
                      · -- y < k : y lands in the cargo subtree l (tight: 2d+6 ≤ 2d+6)
                        rw [ds_div_lt hylt hklt, sp_len]
                        have h1 : kD y (bN
                            (bN (bN l k rl) rk A) s B)
                            = kD y (bN (bN l k rl) rk A) + 1 :=
                          kL (by omega) _ _
                        have h2 : kD y (bN (bN l k rl) rk A)
                            = kD y (bN l k rl) + 1 :=
                          kL (by omega) _ _
                        have h3 : kD y (bN l k rl)
                            = kD y l + 1 := kL hylt _ _
                        have h4 : kD y (bN l k
                            (bN rl rk (bN a x b)))
                            = kD y l + 1 := kL hylt _ _
                        omega
                      · have hkly : k < y := by omega
                        by_cases hyrk : y = rk
                        · rw [ds_both_gt hkly hklt, ds_self hyrk]
                          have h1 : kD y (bN
                              (bN (bN l k rl) rk A) s B)
                              = kD y (bN (bN l k rl) rk A) + 1 :=
                            kL (by omega) _ _
                          have h2 : kD y (bN (bN l k rl) rk A)
                              = 1 := kS hyrk _ _
                          simp only [List.length_nil]
                          omega
                        · by_cases hyrk2 : y < rk
                          · -- k < y < rk : y lands in the cargo subtree rl
                            rw [ds_both_gt hkly hklt, ds_div_lt hyrk2 hrkq, sp_len]
                            have h1 : kD y (bN
                                (bN (bN l k rl) rk A) s B)
                                = kD y
                                    (bN (bN l k rl) rk A) + 1 :=
                              kL (by omega) _ _
                            have h2 : kD y (bN (bN l k rl) rk A)
                                = kD y (bN l k rl) + 1 :=
                              kL hyrk2 _ _
                            have h3 : kD y (bN l k rl)
                                = kD y rl + 1 := kG hkly _ _
                            have h4 : kD y (bN l k
                                (bN rl rk (bN a x b)))
                                = kD y (bN rl rk (bN a x b)) + 1 :=
                              kG hkly _ _
                            have h5 : kD y (bN rl rk (bN a x b))
                                = kD y rl + 1 := kL hyrk2 _ _
                            omega
                          · -- rk < y : y in the recursion zone
                            have hrky : rk < y := by omega
                            rw [ds_both_gt hkly hklt, ds_both_gt hrky hrkq]
                            have hIH := ih _ hsz q y hbrr
                            rw [hs] at hIH
                            have h3 : kD y (bN l k
                                (bN rl rk (bN a x b)))
                                = kD y
                                    (bN rl rk (bN a x b)) + 1 :=
                              kG hkly _ _
                            have h4 : kD y (bN rl rk (bN a x b))
                                = kD y (bN a x b) + 1 :=
                              kG hrky _ _
                            rcases Nat.lt_trichotomy y s with hys | hys | hys
                            · have h1 : kD y (bN
                                  (bN (bN l k rl) rk A) s B)
                                  = kD y
                                      (bN (bN l k rl) rk A) + 1 :=
                                kL hys _ _
                              have h2 : kD y (bN (bN l k rl) rk A)
                                  = kD y A + 1 := kG hrky _ _
                              have h5 : kD y (bN A s B) = kD y A + 1 :=
                                kL hys _ _
                              omega
                            · have h1 : kD y (bN
                                  (bN (bN l k rl) rk A) s B)
                                  = 1 := kS hys _ _
                              omega
                            · have h1 : kD y (bN
                                  (bN (bN l k rl) rk A) s B)
                                  = kD y B + 1 := kG hys _ _
                              have h5 : kD y (bN A s B) = kD y B + 1 :=
                                kG hys _ _
                              omega
              · -- (13) q found at the right child (q = rk): single ZAG
                have hqrk_eq : q = rk := by omega
                rw [splay.eq_def]
                simp only [if_neg hqk, if_neg hqlt, if_neg hqrk, if_neg hrkq]
                show 2 * kD y (bN (bN l k rl) rk rr)
                    ≤ kD y (bN l k (bN rl rk rr))
                      + (divergeSuffix y q
                          (bN l k (bN rl rk rr))).length + 5
                by_cases hyk : y = k
                · rw [ds_self hyk]
                  have h1 : kD y (bN (bN l k rl) rk rr)
                      = kD y (bN l k rl) + 1 :=
                    kL (by omega) _ _
                  have h2 : kD y (bN l k rl) = 1 :=
                    kS hyk _ _
                  have h3 : kD y (bN l k (bN rl rk rr)) = 1 :=
                    kS hyk _ _
                  simp only [List.length_nil]
                  omega
                · by_cases hylt : y < k
                  · rw [ds_div_lt hylt hklt, sp_len]
                    have h1 : kD y (bN (bN l k rl) rk rr)
                        = kD y (bN l k rl) + 1 :=
                      kL (by omega) _ _
                    have h2 : kD y (bN l k rl)
                        = kD y l + 1 := kL hylt _ _
                    have h3 : kD y (bN l k (bN rl rk rr))
                        = kD y l + 1 := kL hylt _ _
                    omega
                  · have hkly : k < y := by omega
                    by_cases hyrk : y = rk
                    · rw [ds_both_gt hkly hklt, ds_self hyrk]
                      have h1 : kD y (bN (bN l k rl) rk rr) = 1 :=
                        kS hyrk _ _
                      simp only [List.length_nil]
                      omega
                    · by_cases hyrk2 : y < rk
                      · rw [ds_both_gt hkly hklt, ds_qroot_lt hqrk_eq hyrk2, sp_len]
                        have h1 : kD y (bN (bN l k rl) rk rr)
                            = kD y (bN l k rl) + 1 :=
                          kL hyrk2 _ _
                        have h2 : kD y (bN l k rl)
                            = kD y rl + 1 := kG hkly _ _
                        have h3 : kD y (bN l k (bN rl rk rr))
                            = kD y (bN rl rk rr) + 1 :=
                          kG hkly _ _
                        have h4 : kD y (bN rl rk rr)
                            = kD y rl + 1 := kL hyrk2 _ _
                        omega
                      · have hrky : rk < y := by omega
                        rw [ds_both_gt hkly hklt, ds_qroot_gt hqrk_eq hrky, sp_len]
                        have h1 : kD y (bN (bN l k rl) rk rr)
                            = kD y rr + 1 := kG hrky _ _
                        have h2 : kD y (bN l k (bN rl rk rr))
                            = kD y (bN rl rk rr) + 1 :=
                          kG hkly _ _
                        have h3 : kD y (bN rl rk rr)
                            = kD y rr + 1 := kG hrky _ _
                        omega
theorem ksh (q y : Nat) (t : BinaryTree) (hbst : IsBST t) :
    2 * kD y (splay t q) ≤ kD y t + (divergeSuffix y q t).length + 5 :=
  kshA t.num_nodes t (Nat.le_refl _) q y hbst
theorem tcL {T c : List Nat} (h : ∀ z ∈ c, z ∈ T) :
    touchedCount T c = c.length := by
  simp only [touchedCount]
  congr 1
  exact List.filter_eq_self.mpr (fun a ha => decide_eq_true (h a ha))
theorem sH (v k : Nat) (l r : BinaryTree) :
    ∃ rest, searchPath v (.node l k r) = k :: rest := by
  by_cases h1 : v = k
  · exact ⟨[], sS h1 l r⟩
  · by_cases h2 : v < k
    · exact ⟨searchPath v l, sL h2 l r⟩
    · exact ⟨searchPath v r, sG (by omega) l r⟩
theorem touchedCount_shared_decomp (t : BinaryTree) (q v : Nat) (T : List Nat)
    (hbst : IsBST t)
    (hsh : ∀ z ∈ searchPath q t, z ∈ searchPath v t → z ∈ T) :
    ∃ p' sh : List Nat,
      searchPath v t = sh ++ divergeSuffix v q t
      ∧ touchedCount (T ++ searchPath q t) (searchPath v (splay t q)) + sh.length
          = touchedCount T (searchPath v t) + p'.length
      ∧ 2 * p'.length ≤ sh.length + 5 := by
  obtain ⟨p', hnew, hp'⟩ := spd q v t hbst
  obtain ⟨sh, hold, hshq⟩ := shd q v t
  refine ⟨p', sh, hold, ?_, ?_⟩
  · -- counting: T' fully covers p', T fully covers sh (hypothesis W6),
    have e1 : touchedCount (T ++ searchPath q t) (searchPath v (splay t q))
        = p'.length + touchedCount T (divergeSuffix v q t) := by
      rw [hnew, tcA]
      congr 1
      · exact tcL (fun z hz => List.mem_append_right T (hp' z hz))
      · exact tcC (fun z hz => by
          constructor
          · intro hzT'
            rcases List.mem_append.mp hzT' with h | h
            · exact h
            · exact absurd h (dsD t hbst z hz)
          · exact fun h => List.mem_append_left _ h)
    have e2 : touchedCount T (searchPath v t)
        = sh.length + touchedCount T (divergeSuffix v q t) := by
      rw [hold, tcA]
      congr 1
      exact tcL (fun z hz =>
        hsh z (hshq z hz) (by rw [hold]; exact List.mem_append_left _ hz))
    omega
  · -- halving: 2·|p' ++ ds| ≤ |sh ++ ds| + |ds| + 5
    have h5 := ksh q v t hbst
    rw [← sp_len, ← sp_len, hnew, hold] at h5
    simp only [List.length_append] at h5
    omega
theorem touchedCount_sharedTouched_splay_le (t : BinaryTree) (q v : Nat) (T : List Nat)
    (hbst : IsBST t) (hne : t ≠ .empty)
    (hsh : ∀ z ∈ searchPath q t, z ∈ searchPath v t → z ∈ T) :
    touchedCount (T ++ searchPath q t) (searchPath v (splay t q))
      ≤ touchedCount T (searchPath v t) + 2 := by
  obtain ⟨p', sh, hold, hcount, hhalf⟩ := touchedCount_shared_decomp t q v T hbst hsh
  cases t with
  | empty => exact absurd rfl hne
  | node l k r =>
    have hkq : k ∈ searchPath q (.node l k r) := rM q k l r
    have hkv : k ∈ searchPath v (.node l k r) := rM v k l r
    have h1 : 1 ≤ sh.length := by
      rw [hold] at hkv
      rcases List.mem_append.mp hkv with h | h
      · exact List.length_pos_of_mem h
      · exact absurd hkq (dsD _ hbst k h)
    omega
theorem tcId (l r : BinaryTree) (k q v : Nat) (T : List Nat)
    (hkT : k ∈ T)
    (hid : splay (.node l k r) q = .node l k r)
    (hpq : searchPath q (.node l k r) = [k]) :
    touchedCount (T ++ searchPath q (.node l k r)) (searchPath v (splay (.node l k r) q))
      = touchedCount T (searchPath v (.node l k r)) := by
  rw [hid, hpq]
  exact tcC (fun z hz => by
    constructor
    · intro h
      rcases List.mem_append.mp h with h | h
      · exact h
      · simp only [List.mem_singleton] at h
        exact h ▸ hkT
    · exact fun h => List.mem_append_left _ h)
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
    have hkT : k ∈ T := hsh k (rM q k l r) (rM v k l r)
    by_cases hqk : q = k
    · -- q found at the root: splay is the identity, q's path is [k]
      rw [tcId l r k q v T hkT
        (by rw [splay.eq_def]; simp only [if_pos hqk])
        (sS hqk l r)]
      omega
    · rcases hside with ⟨hq, hv⟩ | ⟨hv, hq⟩
      · -- k < q ≤ v
        have hklt : k < q := by omega
        cases r with
        | empty =>
          rw [tcId l .empty k q v T hkT
            (by rw [splay.eq_def]; simp only [if_neg hqk, if_neg (by omega : ¬ q < k)])
            (by rw [sG hklt]; rfl)]
          omega
        | node rl rk rr =>
          obtain ⟨p', sh, hold, hcount, hhalf⟩ :=
            touchedCount_shared_decomp (.node l k (.node rl rk rr)) q v T hbst hsh
          have hkv : k < v := by omega
          obtain ⟨rest, hrest⟩ := sH v rk rl rr
          have hvpath : searchPath v (.node l k (.node rl rk rr)) = k :: rk :: rest := by
            rw [sG hkv, hrest]
          have hkq : k ∈ searchPath q (.node l k (.node rl rk rr)) :=
            rM q k _ _
          have hrkq : rk ∈ searchPath q (.node l k (.node rl rk rr)) := by
            rw [sG hklt]
            exact List.mem_cons_of_mem _ (rM q rk rl rr)
          rw [hvpath] at hold
          have h2 : 2 ≤ sh.length := by
            rcases sh with _ | ⟨z0, _ | ⟨z1, sh'⟩⟩
            · exfalso
              simp only [List.nil_append] at hold
              exact dsD (q := q) (y := v) _ hbst k
                (by rw [← hold]; exact List.mem_cons_self) hkq
            · exfalso
              simp only [List.cons_append, List.nil_append] at hold
              injection hold with h1 htl
              exact dsD (q := q) (y := v) _ hbst rk
                (by rw [← htl]; exact List.mem_cons_self) hrkq
            · simp only [List.length_cons]
              omega
          omega
      · -- mirror: v ≤ q < k
        have hklt : q < k := by omega
        cases l with
        | empty =>
          rw [tcId .empty r k q v T hkT
            (by rw [splay.eq_def]; simp only [if_neg hqk, if_pos hklt])
            (by rw [sL hklt]; rfl)]
          omega
        | node ll lk lr =>
          obtain ⟨p', sh, hold, hcount, hhalf⟩ :=
            touchedCount_shared_decomp (.node (.node ll lk lr) k r) q v T hbst hsh
          have hvk : v < k := by omega
          obtain ⟨rest, hrest⟩ := sH v lk ll lr
          have hvpath : searchPath v (.node (.node ll lk lr) k r) = k :: lk :: rest := by
            rw [sL hvk, hrest]
          have hkq : k ∈ searchPath q (.node (.node ll lk lr) k r) :=
            rM q k _ _
          have hlkq : lk ∈ searchPath q (.node (.node ll lk lr) k r) := by
            rw [sL hklt]
            exact List.mem_cons_of_mem _ (rM q lk ll lr)
          rw [hvpath] at hold
          have h2 : 2 ≤ sh.length := by
            rcases sh with _ | ⟨z0, _ | ⟨z1, sh'⟩⟩
            · exfalso
              simp only [List.nil_append] at hold
              exact dsD (q := q) (y := v) _ hbst k
                (by rw [← hold]; exact List.mem_cons_self) hkq
            · exfalso
              simp only [List.cons_append, List.nil_append] at hold
              injection hold with h1 htl
              exact dsD (q := q) (y := v) _ hbst lk
                (by rw [← htl]; exact List.mem_cons_self) hlkq
            · simp only [List.length_cons]
              omega
          omega
theorem touchedCount_within_run_splay_le (t : BinaryTree) (q v : Nat) (T : List Nat)
    (hbst : IsBST t) (hne : t ≠ .empty)
    (hside : (rootKey t ≤ q ∧ q ≤ v) ∨ (v ≤ q ∧ q ≤ rootKey t))
    (hsh : ∀ z ∈ searchPath q t, z ∈ searchPath v t → z ∈ T) :
    touchedCount (T ++ searchPath q t) (searchPath v (splay t q))
      ≤ touchedCount T (searchPath v t) + 2 := by
  have := touchedCount_within_run_splay_le_one t q v T hbst hne hside hsh
  omega
theorem sAL {l r : BinaryTree} {k q : Nat}
    (hL : ForallTree (fun x => x < k) l) (hq : q ≤ k) :
    ∀ w ∈ searchPath q (.node l k r), w ≤ k := by
  intro w hw
  rcases Nat.eq_or_lt_of_le hq with heq | hlt
  · rw [sS heq] at hw
    simp only [List.mem_singleton] at hw
    omega
  · rw [sL hlt] at hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact Nat.le_refl _
    · exact Nat.le_of_lt (mSF (p := fun x => x < k) hL hw)
theorem sAG {l r : BinaryTree} {k q : Nat}
    (hR : ForallTree (fun x => k < x) r) (hq : k ≤ q) :
    ∀ w ∈ searchPath q (.node l k r), k ≤ w := by
  intro w hw
  rcases Nat.eq_or_lt_of_le hq with heq | hlt
  · rw [sS heq.symm] at hw
    simp only [List.mem_singleton] at hw
    omega
  · rw [sG hlt] at hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact Nat.le_refl _
    · exact Nat.le_of_lt (mSF hR hw)
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
    rcases bI.mp hbst with ⟨hL, hR, _, _⟩
    rcases hside with ⟨hq, hv⟩ | ⟨hv, hq⟩
    · have h1 : z ≤ k := sAL hL hq z hzq
      have h2 : k ≤ z := sAG hR hv z hzv
      have : z = k := by omega
      rwa [this]
    · have h1 : k ≤ z := sAG hR hq z hzq
      have h2 : z ≤ k := sAL hL hv z hzv
      have : z = k := by omega
      rwa [this]
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
