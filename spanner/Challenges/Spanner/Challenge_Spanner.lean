import Challenges.Spanner.Def_Spanner

namespace Spanner

/-- (100 pts) Spanner existence. Prove that every connected simple graph
on `n` vertices admits a `(2t - 1)`-spanner with at most `2 * n * n^(1/t)`
edges. This is the classical Althofer, Das, Dobkin, Joseph existence
bound. -/
lemma spanner_exists {n} (G : SimpleGraph (Fin n))
    (hG : G.Connected) (t : ℕ) [NeZero t] :
    ∃ H : SimpleGraph (Fin n), H.IsSpannerOf G (2 * t - 1)
    ∧ H.numEdges ≤ 2 * n * (NNReal.rpow ↑n (1 / (↑t))) := by
  classical
  have hnpos : 0 < n := by
    haveI : Nonempty (Fin n) := hG.nonempty
    simpa using (Fintype.card_pos : 0 < Fintype.card (Fin n))
  have hDenseSubgraph : ∀ (G0 : SimpleGraph (Fin n)) (d : ℕ),
      Nat.card G0.support * d < G0.numEdges →
      ∃ K : SimpleGraph (Fin n), K ≤ G0 ∧
        Nat.card K.support * d < K.numEdges ∧
        ∀ v, v ∈ K.support → d < Nat.card (K.neighborSet v) := by
    intro G0 d hdense
    let P : Set (SimpleGraph (Fin n)) :=
      {K | K ≤ G0 ∧ Nat.card K.support * d < K.numEdges}
    have hfin : P.Finite := Set.finite_univ.subset (by intro K hK; simp)
    have hnon : P.Nonempty := ⟨G0, ⟨le_rfl, hdense⟩⟩
    obtain ⟨K, hKP, hmin⟩ :=
      Set.exists_min_image P (fun K : SimpleGraph (Fin n) => Nat.card K.support) hfin hnon
    letI : DecidableRel K.Adj := fun a b => Classical.propDecidable (K.Adj a b)
    refine ⟨K, hKP.1, hKP.2, ?_⟩
    intro v hv
    by_contra hdeg_not
    have hdeg_le : Nat.card (K.neighborSet v) ≤ d := Nat.le_of_not_gt hdeg_not
    have hdeg_le' : K.degree v ≤ d := by
      simpa [Nat.card_eq_fintype_card, SimpleGraph.degree, SimpleGraph.neighborFinset_def,
        Set.toFinset_card] using hdeg_le
    let K' : SimpleGraph (Fin n) := K.deleteIncidenceSet v
    have hK'leG : K' ≤ G0 := (SimpleGraph.deleteIncidenceSet_le K v).trans hKP.1
    have hsupp_le : Nat.card K'.support ≤ Nat.card K.support - 1 := by
      simpa [K', Nat.card_eq_fintype_card] using
        SimpleGraph.card_support_deleteIncidenceSet K hv
    have hedge_eq : K'.numEdges = K.numEdges - K.degree v := by
      dsimp [K']
      unfold SimpleGraph.numEdges SimpleGraph.edgeFinset
      simp [SimpleGraph.edgeSet_deleteIncidenceSet, Set.toFinset_diff, Finset.card_sdiff]
      have hcard : ((K.incidenceSet v).toFinset ∩ K.edgeSet.toFinset).card = K.degree v := by
        have hsub : (K.incidenceSet v).toFinset ⊆ K.edgeSet.toFinset := by
          rw [Set.toFinset_subset_toFinset]
          exact SimpleGraph.incidenceSet_subset K v
        rw [Finset.inter_eq_left.mpr hsub]
        rw [← SimpleGraph.card_incidenceSet_eq_degree]
        exact Set.toFinset_card _
      rw [hcard]
    have hK'dense : Nat.card K'.support * d < K'.numEdges := by
      rw [hedge_eq]
      have hle_mul : Nat.card K'.support * d ≤ (Nat.card K.support - 1) * d :=
        Nat.mul_le_mul_right _ hsupp_le
      apply lt_of_le_of_lt hle_mul
      apply lt_tsub_of_add_lt_right
      have hpos : 0 < Nat.card K.support := by
        haveI : Nonempty K.support := ⟨⟨v, hv⟩⟩
        exact Nat.card_pos
      have hsd : (Nat.card K.support - 1) * d + d = Nat.card K.support * d := by
        have hs : Nat.card K.support - 1 + 1 = Nat.card K.support :=
          Nat.sub_one_add_one (Nat.ne_of_gt hpos)
        calc
          (Nat.card K.support - 1) * d + d = ((Nat.card K.support - 1) + 1) * d := by
            rw [add_mul, one_mul]
          _ = Nat.card K.support * d := by rw [hs]
      calc
        (Nat.card K.support - 1) * d + K.degree v ≤
            (Nat.card K.support - 1) * d + d := Nat.add_le_add_left hdeg_le' _
        _ = Nat.card K.support * d := hsd
        _ < K.numEdges := hKP.2
    have hK'P : K' ∈ P := ⟨hK'leG, hK'dense⟩
    have hmin_le := hmin K' hK'P
    have hstrict_supp : Nat.card K'.support < Nat.card K.support := by
      have hpos : 0 < Nat.card K.support := by
        haveI : Nonempty K.support := ⟨⟨v, hv⟩⟩
        exact Nat.card_pos
      exact lt_of_le_of_lt hsupp_le (Nat.sub_one_lt (Nat.ne_of_gt hpos))
    exact (Nat.not_lt_of_ge hmin_le) hstrict_supp
  have hMoore : ∀ (K : SimpleGraph (Fin n)) (d : ℕ), 0 < d →
      (∀ u (c : K.Walk u u), c.IsCycle → ¬ c.length ≤ 2 * t) →
      (∀ v, v ∈ K.support → d < Nat.card (K.neighborSet v)) →
      ∀ r : Fin n, r ∈ K.support → d ^ t < n := by
    intro K d hdpos hNo hmin r hr
    let L : ℕ → Set (Fin n) := fun i =>
      {v | ∃ p : K.Walk r v, p.IsPath ∧ p.length = i}
    have hunique : ∀ {u v : Fin n} (p q : K.Walk u v), p.IsPath → q.IsPath →
        p.length + q.length ≤ 2 * t → p = q := by
      intro u v p
      induction p with
      | nil =>
          intro q hp hq hlen
          have hqnil : q = SimpleGraph.Walk.nil :=
            (SimpleGraph.Walk.isPath_iff_eq_nil q).mp hq
          exact hqnil.symm
      | @cons u x v h p ih =>
          intro q hp hq hlen
          cases q with
          | nil =>
              have hpnil : (SimpleGraph.Walk.cons h p).IsPath →
                  (SimpleGraph.Walk.cons h p) = SimpleGraph.Walk.nil := by
                intro hp'
                exact (SimpleGraph.Walk.isPath_iff_eq_nil (SimpleGraph.Walk.cons h p)).mp hp'
              cases hpnil hp
          | @cons _ y _ hq0 qtail =>
              have hp_parts := (SimpleGraph.Walk.cons_isPath_iff h p).mp hp
              have hp_tail : p.IsPath := hp_parts.1
              have hp_no_edge : s(u, x) ∉ p.edges := by
                intro he
                exact hp_parts.2 (SimpleGraph.Walk.fst_mem_support_of_mem_edges p he)
              have hq_parts := (SimpleGraph.Walk.cons_isPath_iff hq0 qtail).mp hq
              have hq_tail : qtail.IsPath := hq_parts.1
              by_cases hmem : s(u, x) ∈ (SimpleGraph.Walk.cons hq0 qtail).edges
              · have hxy : x = y := by
                  have hxeq := hq.eq_snd_of_mem_edges hmem
                  simpa [SimpleGraph.Walk.snd_cons] using hxeq
                subst y
                have htail_len : p.length + qtail.length ≤ 2 * t := by
                  rw [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_cons] at hlen
                  omega
                have htail_eq : p = qtail := ih qtail hp_tail hq_tail htail_len
                subst htail_eq
                rfl
              · let rest : K.Walk x u := p.append (SimpleGraph.Walk.cons hq0 qtail).reverse
                have hnot_rest : s(u, x) ∉ rest.edges := by
                  intro he
                  dsimp [rest] at he
                  rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_reverse,
                    List.mem_append, List.mem_reverse] at he
                  rcases he with he | he
                  · exact hp_no_edge he
                  · exact hmem he
                let c : K.Walk u u := SimpleGraph.Walk.cons h rest
                have hc : c.cycleBypass.IsCycle := by
                  dsimp [c, SimpleGraph.Walk.cycleBypass]
                  rw [SimpleGraph.Walk.cons_isCycle_iff]
                  constructor
                  · exact SimpleGraph.Walk.bypass_isPath rest
                  · intro he
                    exact hnot_rest (SimpleGraph.Walk.edges_bypass_subset rest he)
                have hclen : c.cycleBypass.length ≤ 2 * t := by
                  dsimp [c, SimpleGraph.Walk.cycleBypass]
                  have hb := SimpleGraph.Walk.length_bypass_le rest
                  have hrestlen : rest.length = p.length + (qtail.length + 1) := by
                    dsimp [rest]
                    rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
                      SimpleGraph.Walk.length_cons]
                  rw [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_cons] at hlen
                  omega
                exact False.elim (hNo u c.cycleBypass hc hclen)
    have hendpoint : ∀ {rvw : Fin n} {p : K.Walk r rvw}, p.IsPath →
        p.length + 1 ≤ 2 * t → ∀ {w}, K.Adj rvw w →
        w ∈ p.support → w = p.penultimate := by
      intro rvw p hp hlen w hadj hw
      by_cases hmem : s(rvw, w) ∈ p.edges
      · exact hp.eq_penultimate_of_mem_edges hmem
      · let q : K.Walk w rvw := p.dropUntil w hw
        have hqpath : q.IsPath := hp.dropUntil hw
        have hqno : s(rvw, w) ∉ q.edges := by
          intro he
          exact hmem (SimpleGraph.Walk.edges_dropUntil_subset p hw he)
        let c : K.Walk rvw rvw := SimpleGraph.Walk.cons hadj q
        have hc : c.IsCycle := by
          dsimp [c]
          rw [SimpleGraph.Walk.cons_isCycle_iff]
          exact ⟨hqpath, hqno⟩
        have hclen : c.length ≤ 2 * t := by
          dsimp [c]
          have hqle : q.length ≤ p.length := by
            dsimp [q]
            exact SimpleGraph.Walk.length_dropUntil_le p hw
          omega
        exact False.elim (hNo rvw c hc hclen)
    have hL1 : L 1 = K.neighborSet r := by
      ext v
      constructor
      · intro hv
        rcases hv with ⟨p, hp, hlen⟩
        exact SimpleGraph.Walk.adj_of_length_eq_one hlen
      · intro hv
        exact ⟨hv.toWalk, SimpleGraph.Walk.IsPath.of_adj hv, by simp⟩
    have hL1card : d < Nat.card (L 1) := by
      rw [hL1]
      exact hmin r hr
    have hstep : ∀ i, 0 < i → i < t → Nat.card (L i) * d ≤ Nat.card (L (i + 1)) := by
      intro i hi0 hit
      let choosePath : (v : L i) → K.Walk r v.1 := fun v => Classical.choose v.2
      have choosePath_spec : ∀ v : L i,
          (choosePath v).IsPath ∧ (choosePath v).length = i := fun v => Classical.choose_spec v.2
      let parent : (v : L i) → Fin n := fun v => (choosePath v).penultimate
      let Child : (v : L i) → Type := fun v => {w : Fin n // K.Adj v.1 w ∧ w ≠ parent v}
      haveI : ∀ v : L i, Fintype (Child v) := by
        intro v
        dsimp [Child]
        infer_instance
      have hchild : ∀ v : L i, d ≤ Nat.card (Child v) := by
        intro v
        have hv_support : v.1 ∈ K.support := by
          rcases v.2 with ⟨p, hp, hlen⟩
          have hnotnil : ¬ p.Nil := by
            rw [SimpleGraph.Walk.not_nil_iff_lt_length]
            omega
          exact (SimpleGraph.mem_support K).mpr ⟨p.penultimate, (p.adj_penultimate hnotnil).symm⟩
        have hdeg : d < Nat.card (K.neighborSet v.1) := hmin v.1 hv_support
        let Childv := Child v
        change d ≤ Nat.card Childv
        let g : K.neighborSet v.1 → Option Childv := fun w =>
          if h : w.1 = parent v then none else some ⟨w.1, ⟨w.2, h⟩⟩
        have hg_inj : Function.Injective g := by
          intro a b hab
          dsimp [g] at hab
          by_cases ha : a.1 = parent v
          · by_cases hb : b.1 = parent v
            · apply Subtype.ext
              exact ha.trans hb.symm
            · simp [ha, hb] at hab
          · by_cases hb : b.1 = parent v
            · simp [ha, hb] at hab
            · simp [ha, hb] at hab
              have hval : a.1 = b.1 := congrArg (fun x : Childv => x.1) hab
              exact Subtype.ext hval
        have hle : Nat.card (K.neighborSet v.1) ≤ Nat.card (Option Childv) :=
          Nat.card_le_card_of_injective g hg_inj
        have hopt : Nat.card (Option Childv) = Nat.card Childv + 1 := by simp
        omega
      let domain := Σ v : L i, Child v
      have hdom_lower : Nat.card (L i) * d ≤ Nat.card domain := by
        dsimp [domain]
        rw [Nat.card_sigma]
        rw [← Nat.card_coe_set_eq (L i)]
        rw [Nat.card_eq_fintype_card]
        calc
          Fintype.card (L i) * d = ∑ _v : L i, d := by
            simp [Finset.sum_const, mul_comm]
          _ ≤ ∑ v : L i, Nat.card (Child v) := by
            exact Finset.sum_le_sum (fun v hv => hchild v)
      let f : domain → L (i + 1) := fun x =>
        let p := choosePath x.1
        let hp := choosePath_spec x.1
        ⟨x.2.1, ⟨p.concat x.2.2.1, by
          refine SimpleGraph.Walk.IsPath.concat hp.1 ?_ x.2.2.1
          intro hw
          have hwparent : x.2.1 = p.penultimate := by
            exact hendpoint hp.1 (by omega) x.2.2.1 hw
          exact x.2.2.2 (by simpa [parent] using hwparent), by
          rw [SimpleGraph.Walk.length_concat, hp.2]⟩⟩
      have hinj : Function.Injective f := by
        intro a b hab
        rcases a with ⟨av, aw⟩
        rcases b with ⟨bv, bw⟩
        cases aw with
        | mk awv awprop =>
        cases bw with
        | mk bwv bwprop =>
        have hw : awv = bwv := congrArg Subtype.val hab
        subst bwv
        have hpa := choosePath_spec av
        have hpb := choosePath_spec bv
        let qa : K.Walk r awv := (choosePath av).concat awprop.1
        let qb : K.Walk r awv := (choosePath bv).concat bwprop.1
        have hqa_path : qa.IsPath := by
          dsimp [qa]
          refine SimpleGraph.Walk.IsPath.concat hpa.1 ?_ awprop.1
          intro hwmem
          have hwparent : awv = (choosePath av).penultimate :=
            hendpoint hpa.1 (by omega) awprop.1 hwmem
          exact awprop.2 (by simpa [parent] using hwparent)
        have hqb_path : qb.IsPath := by
          dsimp [qb]
          refine SimpleGraph.Walk.IsPath.concat hpb.1 ?_ bwprop.1
          intro hwmem
          have hwparent : awv = (choosePath bv).penultimate :=
            hendpoint hpb.1 (by omega) bwprop.1 hwmem
          exact bwprop.2 (by simpa [parent] using hwparent)
        have hqeq : qa = qb := by
          apply hunique qa qb hqa_path hqb_path
          have hqa_len : qa.length = i + 1 := by
            dsimp [qa]
            rw [SimpleGraph.Walk.length_concat, hpa.2]
          have hqb_len : qb.length = i + 1 := by
            dsimp [qb]
            rw [SimpleGraph.Walk.length_concat, hpb.2]
          omega
        dsimp [qa, qb] at hqeq
        obtain ⟨hv, hpwalk⟩ := SimpleGraph.Walk.concat_inj hqeq
        cases av with
        | mk avv avmem =>
        cases bv with
        | mk bvv bvmem =>
        simp only at hv
        subst bvv
        simp
      have hle := Nat.card_le_card_of_injective f hinj
      exact hdom_lower.trans hle
    have htpos : 0 < t := NeZero.pos t
    have hpow_lt_level : ∀ k, 0 < k → k ≤ t → d ^ k < Nat.card (L k) := by
      intro k
      induction k with
      | zero =>
          intro hk _
          cases hk
      | succ k ih =>
          intro hk hkle
          cases k with
          | zero =>
              simpa using hL1card
          | succ m =>
              have ih' : d ^ (m + 1) < Nat.card (L (m + 1)) :=
                ih (Nat.succ_pos m) (by omega)
              have hrec := hstep (m + 1) (Nat.succ_pos m) (by omega)
              have hmul : d ^ (m + 1) * d < Nat.card (L (m + 1)) * d :=
                Nat.mul_lt_mul_of_pos_right ih' hdpos
              have hpow : d ^ (m + 2) = d ^ (m + 1) * d := by rw [pow_succ]
              rw [hpow]
              exact hmul.trans_le hrec
    have hlevel_le_n : Nat.card (L t) ≤ n := by
      rw [Nat.card_coe_set_eq]
      simpa using (Set.ncard_le_card (L t))
    exact (hpow_lt_level t htpos le_rfl).trans_le hlevel_le_n
  have hNoShortEdgeBound : ∀ H : SimpleGraph (Fin n),
      (∀ u (c : H.Walk u u), c.IsCycle → ¬ c.length ≤ 2 * t) →
      (H.numEdges : NNReal) ≤ 2 * (n : NNReal) *
        NNReal.rpow (n : NNReal) (1 / (t : ℝ)) := by
    intro H hHNo
    let rNN : NNReal := NNReal.rpow (n : NNReal) (1 / (t : ℝ))
    let d : ℕ := Nat.ceil rNN
    have hr1 : (1 : NNReal) ≤ rNN := by
      have hn1 : (1 : NNReal) ≤ (n : NNReal) := by exact_mod_cast hnpos
      have hz : 0 ≤ (1 / (t : ℝ)) := by positivity
      dsimp [rNN]
      simpa using NNReal.rpow_le_rpow hn1 hz
    have hdpos : 0 < d := by
      have hd1 : (1 : NNReal) ≤ (d : NNReal) := by
        exact hr1.trans (by dsimp [d]; exact Nat.le_ceil rNN)
      have hd1nat : 1 ≤ d := by exact_mod_cast hd1
      exact Nat.succ_le_iff.mp hd1nat
    have hrootNat : n ≤ d ^ t := by
      have hrootNN : (n : NNReal) ≤ (d : NNReal) ^ t := by
        have hr_le : rNN ≤ (d : NNReal) := by
          dsimp [d]
          exact Nat.le_ceil rNN
        have hp : rNN ^ t ≤ (d : NNReal) ^ t := pow_le_pow_left' hr_le t
        have htne : t ≠ 0 := NeZero.ne t
        have hrpow : rNN ^ t = (n : NNReal) := by
          dsimp [rNN]
          rw [show (1 / (t : ℝ)) = ((t : ℝ)⁻¹) by ring]
          exact NNReal.rpow_inv_natCast_pow (n : NNReal) htne
        exact hrpow ▸ hp
      exact_mod_cast hrootNN
    by_contra hnot
    have hlt : 2 * (n : NNReal) * rNN < (H.numEdges : NNReal) := lt_of_not_ge hnot
    have hdceil : (d : NNReal) ≤ 2 * rNN := by
      have hceil : (Nat.ceil rNN : NNReal) < rNN + 1 := Nat.ceil_lt_add_one (zero_le rNN)
      have hceil_le : (Nat.ceil rNN : NNReal) ≤ rNN + 1 := le_of_lt hceil
      dsimp [d]
      calc
        (Nat.ceil rNN : NNReal) ≤ rNN + 1 := hceil_le
        _ ≤ rNN + rNN := by simpa [add_comm] using add_le_add_left hr1 rNN
        _ = 2 * rNN := by ring
    have hsupp_le_nat : Nat.card H.support ≤ n := by
      rw [Nat.card_coe_set_eq]
      simpa using (Set.ncard_le_card H.support)
    have hsupp_le : (Nat.card H.support : NNReal) ≤ (n : NNReal) := by
      exact_mod_cast hsupp_le_nat
    have hdenseNN : ((Nat.card H.support * d : ℕ) : NNReal) < (H.numEdges : NNReal) := by
      calc
        ((Nat.card H.support * d : ℕ) : NNReal) =
            (Nat.card H.support : NNReal) * (d : NNReal) := by norm_num
        _ ≤ (n : NNReal) * (d : NNReal) := by gcongr
        _ ≤ (n : NNReal) * (2 * rNN) := by gcongr
        _ = 2 * (n : NNReal) * rNN := by ring
        _ < (H.numEdges : NNReal) := hlt
    have hdense : Nat.card H.support * d < H.numEdges := by
      exact_mod_cast hdenseNN
    obtain ⟨K, hKH, hKdense, hKmin⟩ := hDenseSubgraph H d hdense
    have hKNo : ∀ u (c : K.Walk u u), c.IsCycle → ¬ c.length ≤ 2 * t := by
      intro u c hc hlen
      exact hHNo u (c.mapLe hKH) (hc.mapLe hKH) (by simpa using hlen)
    have hsupp_nonempty : K.support.Nonempty := by
      by_contra hempty
      have hsupp_empty : K.support = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
      have hKbot : K = ⊥ := (SimpleGraph.support_eq_bot_iff K).mp hsupp_empty
      have hedges0 : K.numEdges = 0 := by
        simp [SimpleGraph.numEdges, hKbot]
      omega
    rcases hsupp_nonempty with ⟨root, hroot⟩
    have hltMoore : d ^ t < n := hMoore K d hdpos hKNo hKmin root hroot
    exact (Nat.not_lt_of_ge hrootNat) hltMoore
  obtain ⟨H, hHG, hHNo, hmax⟩ : ∃ H : SimpleGraph (Fin n), H ≤ G ∧
      (∀ u (c : H.Walk u u), c.IsCycle → ¬ c.length ≤ 2 * t) ∧
      ∀ K : SimpleGraph (Fin n), K ≤ G →
        (∀ u (c : K.Walk u u), c.IsCycle → ¬ c.length ≤ 2 * t) →
        K.numEdges ≤ H.numEdges := by
    let P : Set (SimpleGraph (Fin n)) :=
      {H | H ≤ G ∧ ∀ u (c : H.Walk u u), c.IsCycle → ¬ c.length ≤ 2 * t}
    have hfin : P.Finite := Set.finite_univ.subset (by intro H hH; simp)
    have hbotNoShort : ∀ u (c : (⊥ : SimpleGraph (Fin n)).Walk u u),
        c.IsCycle → ¬ c.length ≤ 2 * t := by
      intro u c hc
      cases c with
      | nil => simp at hc
      | cons h p => simp at h
    have hnon : P.Nonempty := by
      refine ⟨⊥, ?_⟩
      exact ⟨bot_le, hbotNoShort⟩
    obtain ⟨H, hHP, hmax⟩ :=
      Set.exists_max_image P (fun H : SimpleGraph (Fin n) => H.numEdges) hfin hnon
    refine ⟨H, hHP.1, hHP.2, ?_⟩
    intro K hKG hK
    exact hmax K ⟨hKG, hK⟩
  have hAddShort : ∀ {u v : Fin n}, G.Adj u v → ¬ H.Adj u v →
      ∃ x : Fin n,
        ∃ c : (H ⊔ SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 (Fin n)))).Walk x x,
          c.IsCycle ∧ c.length ≤ 2 * t := by
    intro u v hGuv hnot
    let E : SimpleGraph (Fin n) := SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 (Fin n)))
    let K : SimpleGraph (Fin n) := H ⊔ E
    have hne : u ≠ v := hGuv.ne
    have hE_le : E ≤ G := by
      dsimp [E]
      rw [SimpleGraph.fromEdgeSet_le]
      intro e he
      rcases he with ⟨he_mem, he_nd⟩
      rw [Set.mem_singleton_iff] at he_mem
      subst e
      exact (SimpleGraph.mem_edgeSet G).2 hGuv
    have hKG : K ≤ G := by
      dsimp [K]
      exact sup_le hHG hE_le
    have hstrict : H.numEdges < K.numEdges := by
      have hadjSup : (H ⊔ E).Adj u v := by
        dsimp [E]
        rw [SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj]
        exact Or.inr ⟨by simp, hne⟩
      have hneGraph : H ≠ H ⊔ E := by
        intro heq
        exact hnot (heq ▸ hadjSup)
      have hlt : H < H ⊔ E := lt_of_le_of_ne le_sup_left hneGraph
      have hcard : H.edgeFinset.card < (H ⊔ E).edgeFinset.card :=
        Finset.card_lt_card (SimpleGraph.edgeFinset_strict_mono hlt)
      simpa [SimpleGraph.numEdges, K] using hcard
    by_contra hnone
    have hKNo : ∀ x (c : K.Walk x x), c.IsCycle → ¬ c.length ≤ 2 * t := by
      intro x c hc hle
      exact hnone ⟨x, by simpa [K] using c, by simpa [K] using hc, hle⟩
    have hle := hmax K hKG hKNo
    exact (Nat.not_lt_of_ge hle) hstrict
  have hCycleToPath : ∀ {u v x : Fin n}
      (c : (H ⊔ SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 (Fin n)))).Walk x x),
      c.IsCycle → c.length ≤ 2 * t → ∃ p : H.Walk v u, p.length ≤ 2 * t - 1 := by
    intro u v x c hc hlen
    let E : SimpleGraph (Fin n) := SimpleGraph.fromEdgeSet ({s(u, v)} : Set (Sym2 (Fin n)))
    let K : SimpleGraph (Fin n) := H ⊔ E
    let cK : K.Walk x x := by simpa [K, E] using c
    have hcK : cK.IsCycle := by
      dsimp [cK]
      simpa [K, E] using hc
    have hlenK : cK.length ≤ 2 * t := by
      dsimp [cK]
      simpa [K, E] using hlen
    have hnew : s(u, v) ∈ cK.edges := by
      by_contra hnotEdge
      have h_edges_H : ∀ e ∈ cK.edges, e ∈ H.edgeSet := by
        intro e he
        have heK : e ∈ K.edgeSet := cK.edges_subset_edgeSet he
        dsimp [K, E] at heK
        rw [SimpleGraph.edgeSet_sup] at heK
        rcases heK with heH | heE
        · exact heH
        · rw [SimpleGraph.edgeSet_fromEdgeSet] at heE
          rcases heE with ⟨he_mem, he_notdiag⟩
          rw [Set.mem_singleton_iff] at he_mem
          exact False.elim (hnotEdge (he_mem ▸ he))
      let cH : H.Walk x x := cK.transfer H h_edges_H
      have hcH : cH.IsCycle := hcK.transfer h_edges_H
      have hlen_eq : cH.length = cK.length := by
        dsimp [cH]
        rw [SimpleGraph.Walk.length_transfer]
      have hlenH : cH.length ≤ 2 * t := by
        simpa [hlen_eq] using hlenK
      exact hHNo x cH hcH hlenH
    have hu : u ∈ cK.support := SimpleGraph.Walk.fst_mem_support_of_mem_edges cK hnew
    let r : K.Walk u u := cK.rotate hu
    have hrCycle : r.IsCycle := by
      dsimp [r]
      exact hcK.rotate hu
    have hrLen : r.length = cK.length := by
      dsimp [r]
      unfold SimpleGraph.Walk.rotate
      rw [SimpleGraph.Walk.length_append, Nat.add_comm, ← SimpleGraph.Walk.length_append,
        SimpleGraph.Walk.take_spec]
    have hrMem : s(u, v) ∈ r.edges := by
      dsimp [r]
      exact (SimpleGraph.Walk.rotate_edges cK hu).mem_iff.mpr hnew
    have h_extract : ∃ p : K.Walk v u,
        p.IsPath ∧ p.length + 1 = r.length ∧ s(u, v) ∉ p.edges := by
      have hnil : ¬ r.Nil := hrCycle.not_nil
      have htailPath : r.tail.IsPath := hrCycle.isPath_tail
      have htailLen : r.tail.length + 1 = r.length := SimpleGraph.Walk.length_tail_add_one hnil
      have htailNoFirst : s(u, r.snd) ∉ r.tail.edges := by
        have hc' : (SimpleGraph.Walk.cons (r.adj_snd hnil) r.tail).IsCycle := by
          simpa [SimpleGraph.Walk.cons_tail_eq r hnil] using hrCycle
        exact ((SimpleGraph.Walk.cons_isCycle_iff r.tail (r.adj_snd hnil)).mp hc').2
      rw [← SimpleGraph.Walk.cons_tail_eq r hnil,
        SimpleGraph.Walk.edges_cons, List.mem_cons] at hrMem
      rcases hrMem with hhead | htail
      · have hv : v = r.snd := by
          rw [show s(u, v) = Sym2.mk (u, v) by rfl,
            show s(u, r.snd) = Sym2.mk (u, r.snd) by rfl] at hhead
          rcases Sym2.mk_eq_mk_iff.mp hhead with h | h
          · exact congrArg Prod.snd h
          · have hu_snd : u = r.snd := congrArg Prod.fst h
            exact False.elim ((r.adj_snd hnil).ne hu_snd)
        let p : K.Walk v u := r.tail.copy hv.symm rfl
        have hpPath : p.IsPath := by
          dsimp [p]
          simpa [SimpleGraph.Walk.isPath_copy] using htailPath
        have hpLen : p.length + 1 = r.length := by
          dsimp [p]
          rw [SimpleGraph.Walk.length_copy]
          exact htailLen
        have hpNo : s(u, v) ∉ p.edges := by
          dsimp [p]
          rw [SimpleGraph.Walk.edges_copy]
          simpa [hv] using htailNoFirst
        exact ⟨p, hpPath, hpLen, hpNo⟩
      · have hvpen_tail : v = r.tail.penultimate := by
          exact htailPath.eq_penultimate_of_mem_edges htail
        have htail_not_nil : ¬ r.tail.Nil := by
          rw [SimpleGraph.Walk.not_nil_iff_lt_length]
          have h3 := hrCycle.three_le_length
          omega
        have hvpen : v = r.penultimate := by
          rw [hvpen_tail]
          have hpen :=
            SimpleGraph.Walk.penultimate_cons_of_not_nil (r.adj_snd hnil) r.tail htail_not_nil
          simpa [SimpleGraph.Walk.cons_tail_eq r hnil] using hpen.symm
        let q0 : K.Walk r.reverse.snd u := r.reverse.tail
        let q : K.Walk v u := q0.copy (by rw [SimpleGraph.Walk.snd_reverse, ← hvpen]) rfl
        have hqPath : q.IsPath := by
          dsimp [q, q0]
          simpa [SimpleGraph.Walk.isPath_copy] using (hrCycle.reverse.isPath_tail)
        have hqLen : q.length + 1 = r.length := by
          dsimp [q, q0]
          rw [SimpleGraph.Walk.length_copy]
          rw [SimpleGraph.Walk.length_tail_add_one]
          · simp [SimpleGraph.Walk.length_reverse]
          · exact hrCycle.reverse.not_nil
        have hqNo : s(u, v) ∉ q.edges := by
          dsimp [q, q0]
          rw [SimpleGraph.Walk.edges_copy]
          have hrevNoFirst : s(u, r.reverse.snd) ∉ r.reverse.tail.edges := by
            have hrevnil : ¬ r.reverse.Nil := hrCycle.reverse.not_nil
            have hc' : (SimpleGraph.Walk.cons
                (r.reverse.adj_snd hrevnil) r.reverse.tail).IsCycle := by
              simpa [SimpleGraph.Walk.cons_tail_eq r.reverse hrevnil] using hrCycle.reverse
            exact ((SimpleGraph.Walk.cons_isCycle_iff r.reverse.tail
              (r.reverse.adj_snd hrevnil)).mp hc').2
          simpa [hvpen, SimpleGraph.Walk.snd_reverse] using hrevNoFirst
        exact ⟨q, hqPath, hqLen, hqNo⟩
    rcases h_extract with ⟨pK, hpKPath, hpKLen, hpKNo⟩
    have h_edges_H : ∀ e ∈ pK.edges, e ∈ H.edgeSet := by
      intro e he
      have heK : e ∈ K.edgeSet := pK.edges_subset_edgeSet he
      dsimp [K, E] at heK
      rw [SimpleGraph.edgeSet_sup] at heK
      rcases heK with heH | heE
      · exact heH
      · rw [SimpleGraph.edgeSet_fromEdgeSet] at heE
        rcases heE with ⟨he_mem, he_notdiag⟩
        rw [Set.mem_singleton_iff] at he_mem
        exact False.elim (hpKNo (he_mem ▸ he))
    let pH : H.Walk v u := pK.transfer H h_edges_H
    refine ⟨pH, ?_⟩
    have hlenPK : pK.length + 1 ≤ 2 * t := by
      rw [hpKLen, hrLen]
      exact hlenK
    dsimp [pH]
    rw [SimpleGraph.Walk.length_transfer]
    omega
  have hMissingPath : ∀ {u v : Fin n}, G.Adj u v → ¬ H.Adj u v →
      ∃ p : H.Walk v u, p.length ≤ 2 * t - 1 := by
    intro u v hGuv hnot
    obtain ⟨x, c, hc, hlen⟩ := hAddShort hGuv hnot
    exact hCycleToPath c hc hlen
  have hedge : ∀ ⦃a b : Fin n⦄, G.Adj a b → H.edist a b ≤ 2 * t - 1 := by
    intro a b hGab
    by_cases hHab : H.Adj a b
    · have h1 : H.edist a b ≤ (1 : ℕ∞) := by
        simpa using (SimpleGraph.edist_le hHab.toWalk)
      have hfac : (1 : ℕ∞) ≤ (2 * t - 1 : ℕ∞) := by
        have htpos : 0 < t := NeZero.pos t
        exact_mod_cast (by omega : 1 ≤ 2 * t - 1)
      exact h1.trans hfac
    · obtain ⟨p, hp⟩ := hMissingPath hGab hHab
      have hed : H.edist a b ≤ (p.length : ℕ∞) := by
        simpa [SimpleGraph.Walk.length_reverse] using (SimpleGraph.edist_le p.reverse)
      exact hed.trans (by exact_mod_cast hp)
  have hSpanner : H.IsSpannerOf G (2 * t - 1) := by
    have hwalk : ∀ ⦃u v : Fin n⦄ (p : G.Walk u v),
        H.edist u v ≤ (2 * t - 1) * (p.length : ℕ∞) := by
      intro u v p
      induction p with
      | nil => simp
      | cons h p ih =>
          calc
            H.edist _ _ ≤ H.edist _ _ + H.edist _ _ := SimpleGraph.edist_triangle
            _ ≤ (2 * t - 1) + (2 * t - 1) * (p.length : ℕ∞) :=
              add_le_add (hedge h) ih
            _ = (2 * t - 1) * ((p.length + 1 : ℕ) : ℕ∞) := by
              rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, add_comm]
            _ = (2 * t - 1) * ((SimpleGraph.Walk.cons h p).length : ℕ∞) := by
              rw [SimpleGraph.Walk.length_cons]
    constructor
    · exact hHG
    · intro u v
      obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_edist u v
      simpa [hp] using hwalk p
  refine ⟨H, hSpanner, ?_⟩
  exact hNoShortEdgeBound H hHNo

end Spanner
