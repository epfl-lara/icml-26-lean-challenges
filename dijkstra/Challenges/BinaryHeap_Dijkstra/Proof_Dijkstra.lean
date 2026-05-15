import Challenges.BinaryHeap_Dijkstra.Proof_BinaryHeap

open BinaryTree BinaryHeap Finset SimpleGraph

set_option autoImplicit true
set_option linter.unusedSimpArgs false
set_option linter.unusedDecidableInType false
set_option linter.unnecessarySimpa false
set_option linter.style.longLine false

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace SimpleGraph

lemma walk_boundary {V : Type u} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (P : V → Prop) [DecidablePred P]
    (ha : ¬ P a) (hb : P b) :
    ∃ x y, ∃ q : G.Walk a x, ¬ P x ∧ P y ∧ G.Adj x y ∧ q.length + 1 ≤ p.length := by
  induction p with
  | nil => exact False.elim (ha hb)
  | cons h p ih =>
      case _ u v w =>
      by_cases hp : P v
      · refine ⟨_, _, Walk.nil, ha, hp, h, ?_⟩
        simp [Walk.length_cons]
      · rcases ih hp hb with ⟨x, y, q, hx, hy, hxy, hlen⟩
        refine ⟨x, y, Walk.cons h q, hx, hy, hxy, ?_⟩
        simp [Walk.length_cons]
        omega

end SimpleGraph

lemma delta_adj_le [Nonempty V] (g : fin_simple_graph V) (s u v : V)
    (hconn : SimpleGraph.Connected g.toSimpleGraph) (hadj : g.Adj u v) :
    delta g s v ≤ delta g s u + 1 := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist s u
  have hle := SimpleGraph.dist_le (p.concat hadj)
  rw [SimpleGraph.Walk.length_concat, hp] at hle
  simpa [delta] using hle

lemma relax_neighbors_mem_iff (g : fin_simple_graph V) (u x : V) (dist : V → ENat)
    (q : BinaryHeap V) :
    BinaryHeap.Mem (relax_neighbors g u dist q).2 x ↔ BinaryHeap.Mem q x := by
  unfold relax_neighbors
  generalize hs : (g.neighborFinset u).val.toList = xs
  clear hs
  induction xs generalizing dist q with
  | nil => simp
  | cons v xs ih =>
      by_cases hlt : dist u + 1 < dist v
      · let dist' : V → ENat := fun x => if x = v then dist u + 1 else dist x
        have hih := ih dist' (q.decrease_priority v dist')
        simpa [List.foldl, hlt, dist'] using
          (hih.trans (BinaryHeap.mem_decrease_priority_iff q x v dist'))
      · have hih := ih dist q
        simpa [List.foldl, hlt] using hih

lemma relax_neighbors_good (g : fin_simple_graph V) (u : V) (dist : V → ENat)
    (q : BinaryHeap V) :
    BinaryHeap.NoDup q → BinaryHeap.Strong q dist →
    BinaryHeap.NoDup (relax_neighbors g u dist q).2 ∧
      BinaryHeap.Strong (relax_neighbors g u dist q).2 (relax_neighbors g u dist q).1 := by
  unfold relax_neighbors
  generalize hs : (g.neighborFinset u).val.toList = xs
  clear hs
  induction xs generalizing dist q with
  | nil =>
      intro hnd hstrong
      simp [hnd, hstrong]
  | cons v xs ih =>
      intro hnd hstrong
      by_cases hlt : dist u + 1 < dist v
      · let dist' : V → ENat := fun x => if x = v then dist u + 1 else dist x
        have hagree : ∀ x, x ≠ v → dist' x = dist x := by intro x hx; simp [dist', hx]
        have hstrong' : BinaryHeap.Strong (q.decrease_priority v dist') dist' :=
          BinaryHeap.strong_decrease_priority_changed q v dist dist' hnd hstrong hagree
        have hnd' : BinaryHeap.NoDup (q.decrease_priority v dist') :=
          BinaryHeap.noDup_decrease_priority q v dist' hnd
        have hih := ih dist' (q.decrease_priority v dist') hnd' hstrong'
        simpa [List.foldl, hlt, dist'] using hih
      · have hih := ih dist q hnd hstrong
        simpa [List.foldl, hlt] using hih

lemma relax_list_dist_le (xs : List V) (u x : V) (dist : V → ENat)
    (q : BinaryHeap V) :
    (List.foldl
      (fun (acc : (V → ENat) × BinaryHeap V) (v : V) =>
        let (dist, queue) := acc
        let alt := dist u + 1
        if alt < dist v then
          let dist' : V → ENat := fun x => if x = v then alt else dist x
          let queue' := queue.decrease_priority v dist'
          (dist', queue')
        else
          (dist, queue))
      (dist, q) xs).1 x ≤ dist x := by
  induction xs generalizing dist q with
  | nil => simp
  | cons v xs ih =>
      by_cases hlt : dist u + 1 < dist v
      · let dist' : V → ENat := fun x => if x = v then dist u + 1 else dist x
        have hstep : dist' x ≤ dist x := by
          by_cases hx : x = v
          · subst x
            simp [dist']
            exact le_of_lt hlt
          · simp [dist', hx]
        have hih := ih dist' (q.decrease_priority v dist')
        exact le_trans (by simpa [List.foldl, hlt, dist'] using hih) hstep
      · have hih := ih dist q
        simpa [List.foldl, hlt] using hih

lemma relax_neighbors_dist_le (g : fin_simple_graph V) (u x : V) (dist : V → ENat)
    (q : BinaryHeap V) :
    (relax_neighbors g u dist q).1 x ≤ dist x := by
  unfold relax_neighbors
  exact relax_list_dist_le (g.neighborFinset u).val.toList u x dist q

lemma relax_neighbors_source_zero (g : fin_simple_graph V) (u s : V) (dist : V → ENat)
    (q : BinaryHeap V) :
    dist s = 0 → (relax_neighbors g u dist q).1 s = 0 := by
  intro hs0
  unfold relax_neighbors
  generalize hslist : (g.neighborFinset u).val.toList = xs
  clear hslist
  induction xs generalizing dist q with
  | nil => simpa using hs0
  | cons v xs ih =>
      by_cases hlt : dist u + 1 < dist v
      · by_cases hsv : s = v
        · subst hsv
          have : ¬ dist u + 1 < 0 := not_lt_of_ge bot_le
          exact False.elim (this (by simpa [hs0] using hlt))
        · let dist' : V → ENat := fun x => if x = v then dist u + 1 else dist x
          have hs0' : dist' s = 0 := by simp [dist', hsv, hs0]
          simpa [List.foldl, hlt, dist'] using ih dist' (q.decrease_priority v dist') hs0'
      · simpa [List.foldl, hlt] using ih dist q hs0

lemma relax_neighbors_lower [Nonempty V] (g : fin_simple_graph V) (u s : V)
    (dist : V → ENat) (q : BinaryHeap V)
    (hconn : SimpleGraph.Connected g.toSimpleGraph)
    (hu : dist u = (delta g s u : ENat))
    (hlower : ∀ x, (delta g s x : ENat) ≤ dist x) :
    ∀ x, (delta g s x : ENat) ≤ (relax_neighbors g u dist q).1 x := by
  unfold relax_neighbors
  generalize hslist : (g.neighborFinset u).val.toList = xs
  have hadjall : ∀ v, v ∈ xs → g.Adj u v := by
    intro v hv
    rw [← hslist] at hv
    simpa using hv
  clear hslist
  induction xs generalizing dist q with
  | nil => simpa using hlower
  | cons v xs ih =>
      have hadjv : g.Adj u v := hadjall v (by simp)
      have huv : u ≠ v := hadjv.ne
      have hadjtail : ∀ w, w ∈ xs → g.Adj u w := by
        intro w hw
        exact hadjall w (by simp [hw])
      by_cases hlt : dist u + 1 < dist v
      · let dist' : V → ENat := fun x => if x = v then dist u + 1 else dist x
        have hlower' : ∀ x, (delta g s x : ENat) ≤ dist' x := by
          intro x
          by_cases hx : x = v
          · have hnat := delta_adj_le g s u v hconn hadjv
            subst x
            have hcast : (delta g s v : ENat) ≤ (delta g s u : ENat) + 1 := by
              exact_mod_cast hnat
            simpa [dist', hu] using hcast
          · simp [dist', hx, hlower x]
        have hu' : dist' u = (delta g s u : ENat) := by
          simp [dist', huv, hu]
        have hih := ih dist' (q.decrease_priority v dist') hu' hlower' hadjtail
        simpa [List.foldl, hlt, dist'] using hih
      · have hih := ih dist q hu hlower hadjtail
        simpa [List.foldl, hlt] using hih

lemma relax_neighbors_neighbor_bound (g : fin_simple_graph V) (u y : V)
    (dist : V → ENat) (q : BinaryHeap V) (hadjuy : g.Adj u y) :
    (relax_neighbors g u dist q).1 y ≤ dist u + 1 := by
  unfold relax_neighbors
  generalize hslist : (g.neighborFinset u).val.toList = xs
  have hadjall : ∀ v, v ∈ xs → g.Adj u v := by
    intro v hv
    rw [← hslist] at hv
    simpa using hv
  have hy_mem : y ∈ xs := by
    rw [← hslist]
    simpa using hadjuy
  clear hslist
  induction xs generalizing dist q with
  | nil => simp at hy_mem
  | cons v xs ih =>
      have hadjv : g.Adj u v := hadjall v (by simp)
      have huv : u ≠ v := hadjv.ne
      have hadjtail : ∀ w, w ∈ xs → g.Adj u w := by
        intro w hw
        exact hadjall w (by simp [hw])
      by_cases hlt : dist u + 1 < dist v
      · let dist' : V → ENat := fun x => if x = v then dist u + 1 else dist x
        have hdu : dist' u = dist u := by simp [dist', huv]
        by_cases hyv : y = v
        · subst y
          have htail := relax_list_dist_le xs u v dist' (q.decrease_priority v dist')
          have hstep : dist' v ≤ dist u + 1 := by simp [dist']
          exact le_trans (by simpa [relax_neighbors, List.foldl, hlt, dist'] using htail) hstep
        · have hymem_tail : y ∈ xs := by
            simp at hy_mem
            exact hy_mem.resolve_left (fun h => hyv h)
          have hih := ih dist' (q.decrease_priority v dist') hadjtail hymem_tail
          simpa [List.foldl, hlt, dist', hdu] using hih
      · by_cases hyv : y = v
        · subst y
          have htail := relax_list_dist_le xs u v dist q
          have hstep : dist v ≤ dist u + 1 := le_of_not_gt hlt
          exact le_trans (by simpa [relax_neighbors, List.foldl, hlt] using htail) hstep
        · have hymem_tail : y ∈ xs := by
            simp at hy_mem
            exact hy_mem.resolve_left (fun h => hyv h)
          have hih := ih dist q hadjtail hymem_tail
          simpa [List.foldl, hlt] using hih

lemma relax_neighbors_eq_of_not_improve (g : fin_simple_graph V) (u x : V)
    (dist : V → ENat) (q : BinaryHeap V)
    (hnot : g.Adj u x → ¬ dist u + 1 < dist x) :
    (relax_neighbors g u dist q).1 x = dist x := by
  unfold relax_neighbors
  generalize hslist : (g.neighborFinset u).val.toList = xs
  have hadjall : ∀ v, v ∈ xs → g.Adj u v := by
    intro v hv
    rw [← hslist] at hv
    simpa using hv
  clear hslist
  induction xs generalizing dist q with
  | nil => simp
  | cons v xs ih =>
      have hadjv : g.Adj u v := hadjall v (by simp)
      have huv : u ≠ v := hadjv.ne
      have hadjtail : ∀ w, w ∈ xs → g.Adj u w := by
        intro w hw
        exact hadjall w (by simp [hw])
      by_cases hlt : dist u + 1 < dist v
      · have hvx : v ≠ x := by
          intro hvx
          exact hnot (by simpa [hvx] using hadjv) (by simpa [hvx] using hlt)
        let dist' : V → ENat := fun z => if z = v then dist u + 1 else dist z
        have hdu : dist' u = dist u := by simp [dist', huv]
        have hxv : x ≠ v := by intro hxv; exact hvx hxv.symm
        have hdx : dist' x = dist x := by simp [dist', hxv]
        have hnot' : g.Adj u x → ¬ dist' u + 1 < dist' x := by
          intro hux
          simpa [hdu, hdx] using hnot hux
        have hih := ih dist' (q.decrease_priority v dist') hnot' hadjtail
        simpa [List.foldl, hlt, dist', hdx] using hih
      · have hih := ih dist q hnot hadjtail
        simpa [List.foldl, hlt] using hih

lemma relax_neighbors_settled_eq [Nonempty V] (g : fin_simple_graph V) (s u x : V)
    (dist : V → ENat) (q : BinaryHeap V)
    (hconn : SimpleGraph.Connected g.toSimpleGraph)
    (hu : dist u = (delta g s u : ENat))
    (hx : dist x = (delta g s x : ENat)) :
    (relax_neighbors g u dist q).1 x = dist x := by
  apply relax_neighbors_eq_of_not_improve
  intro hux hlt
  have hnat := delta_adj_le g s u x hconn hux
  have hδ : (delta g s x : ENat) ≤ (delta g s u : ENat) + 1 := by
    exact_mod_cast hnat
  have hle : dist x ≤ dist u + 1 := by
    simpa [hu, hx] using hδ
  exact (not_lt_of_ge hle) hlt

def DijkstraInv [Nonempty V] (g : fin_simple_graph V) (s : V)
    (dist : V → ENat) (q : BinaryHeap V) : Prop :=
  BinaryHeap.NoDup q ∧ BinaryHeap.Strong q dist ∧ dist s = 0 ∧
  (∀ x, (delta g s x : ENat) ≤ dist x) ∧
  (∀ x, ¬ BinaryHeap.Mem q x → dist x = (delta g s x : ENat)) ∧
  (∀ x y, ¬ BinaryHeap.Mem q x → BinaryHeap.Mem q y → g.Adj x y →
    dist y ≤ (delta g s x : ENat) + 1)

lemma extracted_correct [Nonempty V] (g : fin_simple_graph V) (s : V)
    (hconn : SimpleGraph.Connected g.toSimpleGraph) (dist : V → ENat)
    (q : BinaryHeap V) (hne : ¬q.isEmpty = true)
    (hinv : DijkstraInv g s dist q) :
    dist (q.extract_min dist hne).1 = (delta g s (q.extract_min dist hne).1 : ENat) := by
  rcases q with ⟨t⟩
  cases t with
  | leaf => simp [BinaryHeap.isEmpty] at hne
  | node l u r =>
      classical
      have hu_extract :
          (BinaryHeap.extract_min ({ tree := node l u r } : BinaryHeap V) dist hne).1 = u :=
        BinaryHeap.extract_min_fst_node_heap l r u dist hne
      rw [hu_extract]
      rcases hinv with ⟨hnd, hstrong, hs0, hlower, hsettled, hfrontier⟩
      by_cases hus : u = s
      · have hdu0 : dist u = 0 := by simpa [hus] using hs0
        have hδu : delta g s u = 0 := by
          simp [delta, hus, SimpleGraph.dist_self]
        simpa [hδu] using hdu0
      · have hu_mem : BinaryHeap.Mem ({ tree := node l u r } : BinaryHeap V) u := by
          simp [BinaryHeap.Mem, BinaryTree.contains]
        have hs_not_mem : ¬ BinaryHeap.Mem ({ tree := node l u r } : BinaryHeap V) s := by
          intro hs_mem
          have hmin : dist u ≤ dist s := BinaryTree.strongHeap_root_le hstrong hs_mem
          have hdu0 : dist u = 0 := le_antisymm (by simpa [hs0] using hmin) bot_le
          have hδu0_enat : (delta g s u : ENat) = 0 :=
            le_antisymm (by simpa [hdu0] using hlower u) bot_le
          have hδu0 : delta g s u = 0 := by exact_mod_cast hδu0_enat
          have hzeroiff := (hconn.dist_eq_zero_iff (u := s) (v := u))
          have hs_eq_u : s = u := by
            exact hzeroiff.mp (by simpa [delta] using hδu0)
          exact hus hs_eq_u.symm
        obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist s u
        rcases SimpleGraph.walk_boundary p
            (fun x => BinaryHeap.Mem ({ tree := node l u r } : BinaryHeap V) x)
            hs_not_mem hu_mem with
          ⟨x, y, qwalk, hx_not, hy_mem, hxy, hlen⟩
        have hfront := hfrontier x y hx_not hy_mem hxy
        have hminy : dist u ≤ dist y := BinaryTree.strongHeap_root_le hstrong hy_mem
        have hdistx_nat : delta g s x ≤ qwalk.length := by
          simpa [delta] using SimpleGraph.dist_le qwalk
        have hboundary_nat : delta g s x + 1 ≤ delta g s u := by
          have hpδ : p.length = delta g s u := by
            simpa [delta] using hp
          rw [← hpδ]
          omega
        have hboundary_enat : (delta g s x : ENat) + 1 ≤ (delta g s u : ENat) := by
          exact_mod_cast hboundary_nat
        have hdu_le_delta : dist u ≤ (delta g s u : ENat) :=
          le_trans hminy (le_trans hfront hboundary_enat)
        exact le_antisymm hdu_le_delta (hlower u)

lemma dijkstra_step_inv [Nonempty V] (g : fin_simple_graph V) (s : V)
    (hconn : SimpleGraph.Connected g.toSimpleGraph) (dist : V → ENat)
    (q : BinaryHeap V) (hne : ¬q.isEmpty = true)
    (hinv : DijkstraInv g s dist q) :
    DijkstraInv g s
      (relax_neighbors g (q.extract_min dist hne).1 dist (q.extract_min dist hne).2).1
      (relax_neighbors g (q.extract_min dist hne).1 dist (q.extract_min dist hne).2).2 := by
  let u := (q.extract_min dist hne).1
  let q' := (q.extract_min dist hne).2
  let relaxed := relax_neighbors g u dist q'
  rcases hinv with ⟨hnd, hstrong, hs0, hlower, hsettled, hfrontier⟩
  have hu : dist u = (delta g s u : ENat) := by
    simpa [u] using extracted_correct g s hconn dist q hne
      ⟨hnd, hstrong, hs0, hlower, hsettled, hfrontier⟩
  have hnd_extract : BinaryHeap.NoDup q' :=
    BinaryHeap.noDup_extract_min q dist hne hnd
  have hstrong_extract : BinaryHeap.Strong q' dist :=
    BinaryHeap.strong_extract_min q dist hne hstrong
  have hgood := relax_neighbors_good g u dist q' hnd_extract hstrong_extract
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [relaxed, u, q'] using hgood.1
  · simpa [relaxed, u, q'] using hgood.2
  · simpa [relaxed, u, q'] using
      relax_neighbors_source_zero g u s dist q' hs0
  · intro x
    simpa [relaxed, u, q'] using
      relax_neighbors_lower g u s dist q' hconn hu hlower x
  · intro x hx_not_new
    have hx_not_q' : ¬ BinaryHeap.Mem q' x := by
      intro hxq'
      exact hx_not_new ((relax_neighbors_mem_iff g u x dist q').2 hxq')
    by_cases hxq : BinaryHeap.Mem q x
    · rcases BinaryHeap.mem_extract_min_cases q dist hne x hxq with hxu | hxq'
      · subst hxu
        have hpres := relax_neighbors_settled_eq g s u u dist q' hconn hu hu
        calc
          relaxed.1 u = dist u := by simpa [relaxed, u, q'] using hpres
          _ = (delta g s u : ENat) := hu
      · exact False.elim (hx_not_q' hxq')
    · have hxexact := hsettled x hxq
      have hpres := relax_neighbors_settled_eq g s u x dist q' hconn hu hxexact
      calc
        relaxed.1 x = dist x := by simpa [relaxed, u, q'] using hpres
        _ = (delta g s x : ENat) := hxexact
  · intro x y hx_not_new hy_new hxy
    have hx_not_q' : ¬ BinaryHeap.Mem q' x := by
      intro hxq'
      exact hx_not_new ((relax_neighbors_mem_iff g u x dist q').2 hxq')
    have hy_q' : BinaryHeap.Mem q' y := by
      exact (relax_neighbors_mem_iff g u y dist q').1 hy_new
    have hy_q : BinaryHeap.Mem q y :=
      BinaryHeap.mem_extract_min_subset q dist hne y hy_q'
    by_cases hxq : BinaryHeap.Mem q x
    · rcases BinaryHeap.mem_extract_min_cases q dist hne x hxq with hxu | hxq'
      · subst hxu
        have hbound := relax_neighbors_neighbor_bound g u y dist q' hxy
        simpa [relaxed, u, q', hu] using hbound
      · exact False.elim (hx_not_q' hxq')
    · exact le_trans (by
        simpa [relaxed, u, q'] using relax_neighbors_dist_le g u y dist q')
        (hfrontier x y hxq hy_q hxy)

lemma dijkstra_rec_correct_of_inv [Nonempty V] (g : fin_simple_graph V) (s target : V)
    (hconn : SimpleGraph.Connected g.toSimpleGraph) (dist : V → ENat)
    (q : BinaryHeap V) :
    DijkstraInv g s dist q →
      ∀ v : V, dijkstra_rec g s target dist q v = (delta g s v : ENat) := by
  refine dijkstra_rec.induct (g := g)
    (motive := fun dist q =>
      DijkstraInv g s dist q →
        ∀ v : V, dijkstra_rec g s target dist q v = (delta g s v : ENat))
    ?base ?step dist q
  · intro dist q hq hinv v
    rw [dijkstra_rec.eq_def]
    simp [hq]
    rcases hinv with ⟨_, _, _, _, hsettled, _⟩
    exact hsettled v (BinaryHeap.not_mem_of_isEmpty q v hq)
  · intro dist q hq hne
    dsimp
    intro ih hinv v
    rw [dijkstra_rec.eq_def]
    simp [hq]
    exact ih (dijkstra_step_inv g s hconn dist q hne hinv) v

lemma fold_add_mem_iff (xs : List V) (dist : V → ENat) (q : BinaryHeap V)
    (x : V) :
    BinaryHeap.Mem (xs.foldl (fun acc v => acc.add v dist) q) x ↔
      BinaryHeap.Mem q x ∨ x ∈ xs := by
  induction xs generalizing q with
  | nil => simp
  | cons v xs ih =>
      rw [List.foldl_cons]
      simp [ih, BinaryHeap.mem_add_iff, List.mem_cons]
      aesop

lemma fold_add_strong (xs : List V) (dist : V → ENat) (q : BinaryHeap V) :
    BinaryHeap.Strong q dist →
      BinaryHeap.Strong (xs.foldl (fun acc v => acc.add v dist) q) dist := by
  induction xs generalizing q with
  | nil => simpa
  | cons v xs ih =>
      intro hstrong
      rw [List.foldl_cons]
      exact ih (q.add v dist) (BinaryHeap.strong_add q v dist hstrong)

lemma fold_add_noDup (xs : List V) (dist : V → ENat) (q : BinaryHeap V) :
    xs.Nodup → (∀ x, x ∈ xs → ¬ BinaryHeap.Mem q x) → BinaryHeap.NoDup q →
      BinaryHeap.NoDup (xs.foldl (fun acc v => acc.add v dist) q) := by
  induction xs generalizing q with
  | nil =>
      intro _ _ hnd
      simpa
  | cons v xs ih =>
      intro hnodup hfresh hnd
      rcases List.nodup_cons.mp hnodup with ⟨hv_not_xs, hxs_nodup⟩
      have hv_fresh : ¬ BinaryHeap.Mem q v := hfresh v (by simp)
      have hnd_add : BinaryHeap.NoDup (q.add v dist) :=
        BinaryHeap.noDup_add q v dist hnd hv_fresh
      have hfresh_tail : ∀ x, x ∈ xs → ¬ BinaryHeap.Mem (q.add v dist) x := by
        intro x hx hmem
        have hmem' := (BinaryHeap.mem_add_iff q x v dist).mp hmem
        rcases hmem' with hxq | hxv
        · exact hfresh x (by simp [hx]) hxq
        · exact hv_not_xs (by simpa [hxv] using hx)
      rw [List.foldl_cons]
      exact ih (q.add v dist) hxs_nodup hfresh_tail hnd_add

lemma initial_dijkstra_inv [Nonempty V] (g : fin_simple_graph V) (s : V) :
    let dist : V → ENat := fun v => if v = s then 0 else ⊤
    let q := Finset.univ.val.toList.foldl (fun acc v => acc.add v dist) BinaryHeap.empty
    DijkstraInv g s dist q := by
  intro dist q
  have hmem_all : ∀ x : V, BinaryHeap.Mem q x := by
    intro x
    have hxlist : x ∈ (Finset.univ : Finset V).val.toList := by
      simpa using (Finset.mem_univ x)
    have hx := (fold_add_mem_iff (Finset.univ : Finset V).val.toList dist
      BinaryHeap.empty x).2 (Or.inr hxlist)
    simpa [q] using hx
  have hstrong_empty : BinaryHeap.Strong (BinaryHeap.empty : BinaryHeap V) dist := by
    simp [BinaryHeap.Strong, BinaryHeap.empty, BinaryTree.StrongHeap]
  have hstrong : BinaryHeap.Strong q dist := by
    simpa [q] using
      fold_add_strong (Finset.univ : Finset V).val.toList dist
        (BinaryHeap.empty : BinaryHeap V) hstrong_empty
  have hnodup_list : ((Finset.univ : Finset V).val.toList).Nodup := by
    simpa using Finset.nodup_toList (Finset.univ : Finset V)
  have hfresh_empty :
      ∀ x, x ∈ (Finset.univ : Finset V).val.toList →
        ¬ BinaryHeap.Mem (BinaryHeap.empty : BinaryHeap V) x := by
    intro x _ hx
    simpa [BinaryHeap.Mem, BinaryHeap.empty, BinaryTree.contains] using hx
  have hnd_empty : BinaryHeap.NoDup (BinaryHeap.empty : BinaryHeap V) := by
    simp [BinaryHeap.NoDup, BinaryHeap.empty, BinaryTree.NoDupTree]
  have hnd : BinaryHeap.NoDup q := by
    simpa [q] using
      fold_add_noDup (Finset.univ : Finset V).val.toList dist
        (BinaryHeap.empty : BinaryHeap V) hnodup_list hfresh_empty hnd_empty
  refine ⟨hnd, hstrong, ?_, ?_, ?_, ?_⟩
  · simp [dist]
  · intro x
    by_cases hxs : x = s
    · subst hxs
      simp [dist, delta, SimpleGraph.dist_self]
    · simp [dist, hxs]
  · intro x hx_not
    exact False.elim (hx_not (hmem_all x))
  · intro x y hx_not _ _
    exact False.elim (hx_not (hmem_all x))

theorem dijkstra_correctness_aux [Nonempty V] (g : fin_simple_graph V) (s target : V)
    (hconn : SimpleGraph.Connected g.toSimpleGraph) :
    ∀ v : V, (dijkstra g s target) v = (delta g s v : ENat) := by
  let dist : V → ENat := fun v => if v = s then 0 else ⊤
  let q := Finset.univ.val.toList.foldl (fun acc v => acc.add v dist) BinaryHeap.empty
  have hinv : DijkstraInv g s dist q := by
    simpa [dist, q] using initial_dijkstra_inv g s
  intro v
  simpa [dijkstra, dist, q] using
    dijkstra_rec_correct_of_inv g s target hconn dist q hinv v
