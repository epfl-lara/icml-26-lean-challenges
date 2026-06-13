import Challenges.ZBBase

set_option maxHeartbeats 4000000

namespace Splay
namespace Splay
namespace Splay
namespace Splay
namespace Splay
namespace Splay

/-!
#######################################################################
# PHASE D — the zb-REFORM: pair clauses replaced by the PZB form,
# C3/C4 kernels DISCHARGED, the open core reduced to ONE counting kernel
#######################################################################

The validated zb-reform (`/tmp/zb_final.py`: 0/84 adversarial runs incl.
collapse/x20like families; worst consumption-zb = 4): with

  `zlbOn T L b := #{z ∈ L : z ∈ T ∧ b z ≤ 1}`

(the ghost-definable zb-count, in the `b ≤ 1` weighting that also covers
partially-drained heads), the PZB pair clause

  (PZB)  `2·tc(L) ≤ Σb(L on T) + 2·zlbOn(L) + 8`

is a POINTWISE TAUTOLOGY: every touched key contributes at least `2` to
`b + 2·[b ≤ 1]` (`b = 0 ↦ 2`, `b = 1 ↦ 3`, `b ≥ 2 ↦ b`).  Hence:

* `AtomicC3Kernel`/`AtomicC4Kernel` RESTATED in PZB form are DISCHARGED
  OUTRIGHT (`AtomicC3KernelPZB_proved`, `AtomicC4KernelPZB_proved`) — the
  step-neutrality bookkeeping of the reform (b=0 heads: LHS +2 = RHS +2·zb;
  b=1 heads: RHS +3; repay 0→2: Σb +2, zb −2; drains/prunes invisible to
  dive-disjoint live suffixes) is subsumed by the tautology, and the
  pair-clause slots of the strong invariant become content-free;
* the invariant SHRINKS to `INVZA := C1 ∧ C2S` (κ = 9, C2S +20);
* the C2S reproduction (the W-cap route of Phase C) re-derives with the
  PZB consumption: tautology + the ONE remaining counting bound

  `AtomicZBKernel`:  at the consumption pair `(i, j)` (`j` the first
  own-side access of either side after `i+1`), the dive suffix
  `divergeSuffix (X j) (X i) (tree i)` carries at most NINE touched
  low-budget (`b ≤ 1`) keys.

  The funnel only needs `zlb ≤ 9` (`2 + 2·9 = 20` = the C2S constant);
  the validated checker (`/tmp/zb_pin.py`, the `b ≤ 1` extension of
  `/tmp/zb_final.py`) pins the worst case over all adversarial families
  at FOUR — over ALL tracked pairs and steps, not only consumption sites —
  and `zlb ≤ 4` is itself empirically step-inductive (0 violations).
  The suffix is dive-disjoint (`divergeSuffix_disjoint*`), so the count
  transfers VERBATIM across the step (`zlbOn_transfer_step`).

The capstones close from this SINGLE kernel
(`deque_challenge_CLOSED_of_zb_kernel`,
`deque_conjecture_CLOSED_of_zb_kernel`); the two pair-clause kernels of
Phase B are no longer needed anywhere in the reformed funnel.
-/

/-! ## D.1 The zb-count and its toolkit -/

/-- The zb-count of the validated reform, in the `b ≤ 1` weighting:
the number of TOUCHED keys of `L` whose budget is at most `1`. -/
def zlbOn (T L : List ℕ) (b : KeyBudgets) : ℕ :=
  (L.filter (fun z => decide (z ∈ T) && decide (b z ≤ 1))).length

@[simp] theorem zlbOn_nil (T : List ℕ) (b : KeyBudgets) : zlbOn T [] b = 0 := rfl

theorem zlbOn_cons (T : List ℕ) (z : ℕ) (L : List ℕ) (b : KeyBudgets) :
    zlbOn T (z :: L) b
      = (if z ∈ T ∧ b z ≤ 1 then 1 else 0) + zlbOn T L b := by
  unfold zlbOn
  simp only [List.filter_cons]
  by_cases h1 : z ∈ T
  · by_cases h2 : b z ≤ 1
    · rw [if_pos (show (decide (z ∈ T) && decide (b z ≤ 1)) = true by
        simp [h1, h2]), if_pos (show z ∈ T ∧ b z ≤ 1 from ⟨h1, h2⟩),
        List.length_cons]
      omega
    · rw [if_neg (show ¬ (decide (z ∈ T) && decide (b z ≤ 1)) = true by
        simp [h1, h2]), if_neg (fun hc : z ∈ T ∧ b z ≤ 1 => h2 hc.2)]
      omega
  · rw [if_neg (show ¬ (decide (z ∈ T) && decide (b z ≤ 1)) = true by
      simp [h1]), if_neg (fun hc : z ∈ T ∧ b z ≤ 1 => h1 hc.1)]
    omega

/-- `bSumOn` unfolded over a cons (companion to `zlbOn_cons`). -/
theorem bSumOn_cons_pzb (T : List ℕ) (z : ℕ) (L : List ℕ) (b : KeyBudgets) :
    bSumOn T (z :: L) b = (if z ∈ T then b z else 0) + bSumOn T L b := by
  unfold bSumOn
  simp only [List.filter_cons]
  by_cases h : z ∈ T
  · rw [if_pos (show decide (z ∈ T) = true by simp [h]), bSum_cons, if_pos h]
  · rw [if_neg (show ¬ decide (z ∈ T) = true by simp [h]), if_neg h]
    omega

/-- Congruence: the zb-count only depends on the touched-membership and the
budget value at the members of `L`. -/
theorem zlbOn_congr {T T' : List ℕ} {L : List ℕ} {b b' : KeyBudgets}
    (h : ∀ z ∈ L, ((z ∈ T) ↔ (z ∈ T')) ∧ b z = b' z) :
    zlbOn T L b = zlbOn T' L b' := by
  unfold zlbOn
  congr 1
  refine List.filter_congr ?_
  intro z hz
  obtain ⟨h1, h2⟩ := h z hz
  rw [h2, decide_eq_decide.mpr h1]

/-- Dropping a prefix only lowers the zb-count (sublist monotonicity; the
`drop e` quantification of the pair clauses is FREE for the zb-bound). -/
theorem zlbOn_drop_le (T : List ℕ) (L : List ℕ) (b : KeyBudgets) (e : ℕ) :
    zlbOn T (L.drop e) b ≤ zlbOn T L b := by
  induction L generalizing e with
  | nil => exact Nat.le_of_eq (by rw [List.drop_nil])
  | cons z L ih =>
      cases e with
      | zero => exact Nat.le_refl _
      | succ e =>
          rw [List.drop_succ_cons, zlbOn_cons]
          exact Nat.le_trans (ih e) (Nat.le_add_left _ _)

/-! ## D.2 THE PZB TAUTOLOGY -/

/-- **THE PZB TAUTOLOGY.**  Twice the touched count of ANY key list is covered
by its touched budget sum plus twice its zb-count: pointwise, a touched key
contributes `2` to the LHS and `b + 2·[b ≤ 1] ≥ 2` to the RHS
(`b = 0 ↦ 0 + 2`, `b = 1 ↦ 1 + 2`, `b ≥ 2 ↦ b`).  This is the
step-neutrality of the validated zb-reform in closed form: every case of the
reform's bookkeeping (b=0 and b=1 head-gains, repays, disjoint drains,
live prunes) is subsumed, with NO reachability content. -/
theorem pzb_tautology (T L : List ℕ) (b : KeyBudgets) :
    2 * touchedCount T L ≤ bSumOn T L b + 2 * zlbOn T L b := by
  induction L with
  | nil =>
      rw [touchedCount_nil]
      omega
  | cons z L ih =>
      rw [touchedCount_cons T z L, bSumOn_cons_pzb T z L b, zlbOn_cons T z L b]
      by_cases h1 : z ∈ T
      · have ht : tc1 T z = 1 := by
          unfold tc1
          rw [if_pos h1]
        by_cases h2 : b z ≤ 1
        · rw [ht, if_pos h1, if_pos (show z ∈ T ∧ b z ≤ 1 from ⟨h1, h2⟩)]
          omega
        · rw [ht, if_pos h1, if_neg (fun hc : z ∈ T ∧ b z ≤ 1 => h2 hc.2)]
          omega
      · have ht : tc1 T z = 0 := by
          unfold tc1
          rw [if_neg h1]
        rw [ht, if_neg h1, if_neg (fun hc : z ∈ T ∧ b z ≤ 1 => h1 hc.1)]
        omega

/-- The PZB clause in the exact shipped shape (`+ 8` slack of the validated
checker), for ANY touched set, key list and budget state. -/
theorem pzb_clause_universal (T L : List ℕ) (b : KeyBudgets) :
    2 * touchedCount T L ≤ bSumOn T L b + 2 * zlbOn T L b + 8 :=
  Nat.le_trans (pzb_tautology T L b) (by omega)

/-! ## D.3 The PZB-restated pair kernels, DISCHARGED -/

/-- **KERNEL (C3) RESTATED IN PZB FORM** — the consecutive same-side pair
clause reproduction of `AtomicC3Kernel`, with the pair budget `+14` replaced
by the validated zb-form `+ 2·zb + 8`. -/
def AtomicC3KernelPZB : Prop :=
  ∀ (n : ℕ) (X : Fin n → ℕ) (init : BinaryTree),
    init.num_nodes = n → IsBST init → (∀ i : Fin n, X i ∈ init.toKeyList) →
    (X avoids ![2, 1, 3]) → (X avoids ![2, 3, 1]) →
    ∀ i, i < n →
    ∀ (b' : Bool) (j k : ℕ), ConsecOwnAfter X (i+1) b' j k → ∀ (e : ℕ),
    2 * touchedCount (touchedList init X (i+1))
        ((divergeSuffix (accessN X k) (accessN X j)
          (processTree init X (i+1))).drop e)
      ≤ bSumOn (touchedList init X (i+1))
          ((divergeSuffix (accessN X k) (accessN X j)
            (processTree init X (i+1))).drop e)
          (batomicAt 9 init X (i+1))
        + 2 * zlbOn (touchedList init X (i+1))
            ((divergeSuffix (accessN X k) (accessN X j)
              (processTree init X (i+1))).drop e)
            (batomicAt 9 init X (i+1)) + 8

/-- **KERNEL (C4) RESTATED IN PZB FORM** — the first-opposite cross pair
clause reproduction of `AtomicC4Kernel` in the zb-form. -/
def AtomicC4KernelPZB : Prop :=
  ∀ (n : ℕ) (X : Fin n → ℕ) (init : BinaryTree),
    init.num_nodes = n → IsBST init → (∀ i : Fin n, X i ∈ init.toKeyList) →
    (X avoids ![2, 1, 3]) → (X avoids ![2, 3, 1]) →
    ∀ i, i < n →
    ∀ (j k : ℕ), FirstOppAfter X (i+1) j k → ∀ (e : ℕ),
    2 * touchedCount (touchedList init X (i+1))
        ((divergeSuffix (accessN X k) (accessN X j)
          (processTree init X (i+1))).drop e)
      ≤ bSumOn (touchedList init X (i+1))
          ((divergeSuffix (accessN X k) (accessN X j)
            (processTree init X (i+1))).drop e)
          (batomicAt 9 init X (i+1))
        + 2 * zlbOn (touchedList init X (i+1))
            ((divergeSuffix (accessN X k) (accessN X j)
              (processTree init X (i+1))).drop e)
            (batomicAt 9 init X (i+1)) + 8

/-- **`AtomicC3Kernel` IN PZB FORM, DISCHARGED**: the same-side pair clause
reproduction is an instance of the tautology — no reachability content, no
invariant hypothesis needed. -/
theorem AtomicC3KernelPZB_proved : AtomicC3KernelPZB :=
  fun _ X init _ _ _ _ _ i _ _ j k _ e =>
    pzb_clause_universal (touchedList init X (i+1))
      ((divergeSuffix (accessN X k) (accessN X j)
        (processTree init X (i+1))).drop e)
      (batomicAt 9 init X (i+1))

/-- **`AtomicC4Kernel` IN PZB FORM, DISCHARGED**. -/
theorem AtomicC4KernelPZB_proved : AtomicC4KernelPZB :=
  fun _ X init _ _ _ _ _ i _ j k _ e =>
    pzb_clause_universal (touchedList init X (i+1))
      ((divergeSuffix (accessN X k) (accessN X j)
        (processTree init X (i+1))).drop e)
      (batomicAt 9 init X (i+1))

/-! ## D.4 The reformed invariant `INVZA` (κ = 9): C1 ∧ C2S only -/

/-- The REFORMED atomic strong invariant: conservation plus the per-side
first-access cover.  The pair-clause slots of `INVSA` are GONE — their
entire content is the tautology `pzb_tautology` plus the consumption
zb-bound, which lives in the named kernel below. -/
def INVZA {n : ℕ} (kap : ℕ) (init : BinaryTree) (X : Fin n → ℕ) (i : ℕ) : Prop :=
  (bSum (keySupp init) (batomicAt kap init X i)
      ≤ ledgerP kap (costN init X) (freshN init X) i)
  ∧ (∀ (b : Bool) (j : ℕ), FirstOwnAfter X i b j →
      2 * tcOf init X (accessN X j) i
        ≤ bSumOn (touchedList init X i)
            (searchPath (accessN X j) (processTree init X i))
            (batomicAt kap init X i) + 20)

/-- The reformed invariant holds at step `0`. -/
theorem INVZA_zero {n : ℕ} (kap : ℕ) (init : BinaryTree) (X : Fin n → ℕ) :
    INVZA kap init X 0 := by
  refine ⟨?_, ?_⟩
  · rw [batomicAt_zero, bSum_zero]
    exact Nat.zero_le _
  · intro b j _
    have h0 : tcOf init X (accessN X j) 0 = 0 := by
      show touchedCount (touchedList init X 0) _ = 0
      rw [touchedList_zero, touchedCount_nil_T]
    rw [h0]
    omega

/-- The old strong invariant implies the reformed one (audit bridge). -/
theorem INVZA_of_INVSA {n : ℕ} {kap : ℕ} {init : BinaryTree} {X : Fin n → ℕ}
    {i : ℕ} (h : INVSA kap init X i) : INVZA kap init X i :=
  ⟨h.1, h.2.1⟩

/-- **C1 reproduction across one step** (kernel-free, reformed invariant):
verbatim the Phase-B route — the cover comes from the C2S clause alone. -/
theorem INVZA_C1_step {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (hsize : init.num_nodes = n) (hbst : IsBST init) (i : ℕ) (hi : i < n)
    (hINV : INVZA 9 init X i) :
    bSum (keySupp init) (batomicAt 9 init X (i+1))
      ≤ ledgerP 9 (costN init X) (freshN init X) (i+1) := by
  obtain ⟨hC1, hC2S⟩ := hINV
  refine batomicAt_C1_succ_of_cover 9 init X hbst i hC1 ?_
  have hcov := coverA_of_C2SA init X hsize hbst i hi hC2S
  omega

/-! ## D.5 The zb-transfer and the named kernel -/

/-- **zb-transfer**: a live, dive-disjoint key list keeps its zb-count
VERBATIM across the atomic step — the drain only touches path keys, the
repay only touches witnessed path keys (`wKeys ⊆ P`), the prune spares live
keys, and the touched set grows only by path keys. -/
theorem zlbOn_transfer_step {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (i : ℕ) (L : List ℕ)
    (hdisj : ∀ z ∈ L, z ∉ pathN init X i)
    (hlive : ∀ z ∈ L, liveKey (!(sideF X i)) (accessN X i) z = true) :
    zlbOn (touchedList init X (i+1)) L (batomicAt 9 init X (i+1))
      = zlbOn (touchedList init X i) L (batomicAt 9 init X i) := by
  refine zlbOn_congr ?_
  intro z hz
  constructor
  · rw [touchedList_succ, List.mem_append]
    exact ⟨fun h => h.resolve_right (hdisj z hz), Or.inl⟩
  · rw [batomicAt_succ]
    have hzS : z ∉ survN init X i := by
      intro hmem
      have hmem' : z ∈ wKeys (processTree init X i) (pathN init X i)
          (accessN X i) (!(sideF X i)) := hmem
      exact hdisj z hz (wKeys_subset_path z hmem')
    exact atomicStep_get_off_path 9 (pathN init X i) (survN init X i)
      (costN init X i) (freshN init X i) (accessN X i) (!(sideF X i))
      (batomicAt 9 init X i) (hdisj z hz) hzS (hlive z hz)

/-- **KERNEL (ZB)** — THE one remaining named hypothesis of the reformed
programme: at the consumption pair `(i, j)` (`j` the first own-side access of
either side from `i+1`), the dive suffix carries at most NINE touched
low-budget (`b ≤ 1`) keys.

The funnel needs exactly `zlb ≤ 9` (`2 + 2·9 = 20` = the C2S constant at
κ = 9); the validated checker (`/tmp/zb_pin.py`, the `b ≤ 1` extension of
`/tmp/zb_final.py`) pins the worst case over all adversarial families
(alt/runs/rand/collapse/x20like × spine/rand/V/W inits) at FOUR — over ALL
tracked pairs and steps, not only consumption sites — and `zlb ≤ 4` is
itself empirically step-inductive (0 violations at Z = 4).  The open content
is the gain/clear cycle: tracked suffixes are never drained (dive
disjointness, proven), low heads arrive at most one per same-side step
(`divergeSuffix_splay_found`/`_mirror`, proven) and are cleared as
`wKeys`-repaid `p'`-interiors at the next same-side dive
(`searchPath_splay_decomp_interior_witness` + `batomicAt_succ_ge_two`,
proven); opposite-side dives can lower suffix budgets only on the shared
prefix of the cross pair, which the next consumption re-prices. -/
def AtomicZBKernel : Prop :=
  ∀ (n : ℕ) (X : Fin n → ℕ) (init : BinaryTree),
    init.num_nodes = n → IsBST init → (∀ i : Fin n, X i ∈ init.toKeyList) →
    (X avoids ![2, 1, 3]) → (X avoids ![2, 3, 1]) →
    ∀ i, i < n → INVZA 9 init X i →
    ∀ (b' : Bool) (j : ℕ), FirstOwnAfter X (i+1) b' j →
    zlbOn (touchedList init X i)
      (divergeSuffix (accessN X j) (accessN X i) (processTree init X i))
      (batomicAt 9 init X i) ≤ 9

/-! ## D.6 The C2S reproduction from {W-cap, tautology, ZB kernel} -/

/-- **C2S reproduction across one step, REFORMED**: the W-cap route of
Phase C with the pair-clause consumption replaced by the PZB tautology plus
the zb-kernel — the suffix part now costs `bSumOn + 2·9 = bSumOn + 18`,
and the assembly lands exactly on the `+20` C2S constant. -/
theorem INVZA_C2S_step {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (hsize : init.num_nodes = n) (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (h213 : X avoids ![2, 1, 3]) (h231 : X avoids ![2, 3, 1])
    (i : ℕ) (hi : i < n) (hINV : INVZA 9 init X i)
    (hzb : ∀ (b' : Bool) (j : ℕ), FirstOwnAfter X (i+1) b' j →
      zlbOn (touchedList init X i)
        (divergeSuffix (accessN X j) (accessN X i) (processTree init X i))
        (batomicAt 9 init X i) ≤ 9) :
    ∀ (b' : Bool) (j : ℕ), FirstOwnAfter X (i+1) b' j →
    2 * tcOf init X (accessN X j) (i+1)
      ≤ bSumOn (touchedList init X (i+1))
          (searchPath (accessN X j) (processTree init X (i+1)))
          (batomicAt 9 init X (i+1)) + 20 := by
  intro b' j hfo
  obtain ⟨hij, hjn, hsj, hbetween⟩ := hfo
  obtain ⟨hC1, hC2S⟩ := hINV
  have hbstt : IsBST (processTree init X i) := processTree_isBST init X hbst i
  have hcover : drawA 9 (costN init X i) (freshN init X i)
      ≤ bSum (pathN init X i) (batomicAt 9 init X i) :=
    coverA_of_C2SA init X hsize hbst i hi hC2S
  have hpay := batomicAt_succ_ge_two init X hsize hbst wCap_proved hmem i hi hcover
  have hpath : pathN init X i
      = searchPath (accessN X i) (processTree init X i) :=
    pathN_lt init X hi
  have ht2 : processTree init X (i+1)
      = splay (processTree init X i) (accessN X i) := by
    rw [processTree_succ_dite, dif_pos hi, accessN_lt X hi]
  have hxmem : accessN X i ∈ (processTree init X i).toKeyList := by
    rw [processTree_toKeyList, accessN_lt X hi]
    exact hmem ⟨i, hi⟩
  have hiltj : i < j := lt_of_lt_of_le (Nat.lt_succ_self i) hij
  obtain ⟨p', hdec, hsub, hwit⟩ := searchPath_splay_decomp_interior_witness
    (accessN X i) (accessN X j) (processTree init X i) hbstt
  -- the geometry pack, by the chirality of the access at i
  have hgeo :
      (∀ z ∈ divergeSuffix (accessN X j) (accessN X i) (processTree init X i),
          z ∉ pathN init X i)
      ∧ (∀ z ∈ divergeSuffix (accessN X j) (accessN X i) (processTree init X i),
          liveKey (!(sideF X i)) (accessN X i) z = true)
      ∧ (∀ w ∈ searchPath (accessN X j)
            (splay (processTree init X i) (accessN X i)),
          liveKey (!(sideF X i)) (accessN X i) w = true) := by
    cases hsf : sideF X i with
    | false =>
        have hxv : accessN X i ≤ accessN X j :=
          accessN_le_of_sideF_false X h213 h231 hi hjn hiltj hsf
        refine ⟨?_, ?_, ?_⟩
        · intro z hz
          rw [hpath]
          exact divergeSuffix_disjoint_dive (processTree init X i) hbstt
            (accessN X i) (accessN X i) (accessN X j) le_rfl hxv z hz
        · intro z hz
          have hxz := mem_divergeSuffix_gt hxv (processTree init X i) hbstt z hz
          simp only [Bool.not_false, liveKey, if_true]
          simpa using le_of_lt hxz
        · intro w hw
          have hxw := mem_searchPath_splay_ge (accessN X i) (accessN X j)
            (processTree init X i) hbstt hxmem hxv w hw
          simp only [Bool.not_false, liveKey, if_true]
          simpa using hxw
    | true =>
        have hvx : accessN X j ≤ accessN X i :=
          accessN_ge_of_sideF_true X hi hjn hiltj hsf
        refine ⟨?_, ?_, ?_⟩
        · intro z hz
          rw [hpath]
          exact divergeSuffix_disjoint_dive_mirror (processTree init X i) hbstt
            (accessN X i) (accessN X i) (accessN X j) le_rfl hvx z hz
        · intro z hz
          have hzx := mem_divergeSuffix_lt hvx (processTree init X i) hbstt z hz
          simp only [Bool.not_true, liveKey, if_false]
          simpa using le_of_lt hzx
        · intro w hw
          have hwx := mem_searchPath_splay_le (accessN X i) (accessN X j)
            (processTree init X i) hbstt hxmem hvx w hw
          simp only [Bool.not_true, liveKey, if_false]
          simpa using hwx
  obtain ⟨hdisj, hlivesuf, hlivepath⟩ := hgeo
  -- THE PZB CONSUMPTION: tautology at (i+1) + zb-kernel at i + zb-transfer
  have htaut := pzb_tautology (touchedList init X (i+1))
    (divergeSuffix (accessN X j) (accessN X i) (processTree init X i))
    (batomicAt 9 init X (i+1))
  have hzb_i : zlbOn (touchedList init X i)
      (divergeSuffix (accessN X j) (accessN X i) (processTree init X i))
      (batomicAt 9 init X i) ≤ 9 :=
    hzb b' j ⟨hij, hjn, hsj, hbetween⟩
  have htrans : zlbOn (touchedList init X (i+1))
      (divergeSuffix (accessN X j) (accessN X i) (processTree init X i))
      (batomicAt 9 init X (i+1))
      = zlbOn (touchedList init X i)
          (divergeSuffix (accessN X j) (accessN X i) (processTree init X i))
          (batomicAt 9 init X i) :=
    zlbOn_transfer_step init X i _ hdisj hlivesuf
  have hsufstep : 2 * touchedCount (touchedList init X (i+1))
        (divergeSuffix (accessN X j) (accessN X i) (processTree init X i))
      ≤ bSumOn (touchedList init X (i+1))
          (divergeSuffix (accessN X j) (accessN X i) (processTree init X i))
          (batomicAt 9 init X (i+1)) + 18 := by
    omega
  -- the interiors are repaid witnessed survivors
  have hint : ∀ w ∈ p'.dropLast, w ∈ survN init X i := by
    intro w hw
    have hwp' : w ∈ p' := List.dropLast_subset p' hw
    obtain ⟨w', hw'P, hne, hwmem⟩ := hwit w hw
    have hwP : w ∈ searchPath (accessN X i) (processTree init X i) :=
      hsub w hwp'
    have hwlive : liveKey (!(sideF X i)) (accessN X i) w = true := by
      apply hlivepath
      rw [hdec]
      exact List.mem_append_left _ hwp'
    show w ∈ wKeys (processTree init X i) (pathN init X i) (accessN X i)
      (!(sideF X i))
    rw [hpath]
    exact mem_wKeys.mpr ⟨hwP, hwlive, w', hw'P, hne, hwmem⟩
  -- assemble
  show 2 * touchedCount (touchedList init X (i+1))
      (searchPath (accessN X j) (processTree init X (i+1)))
    ≤ bSumOn (touchedList init X (i+1))
        (searchPath (accessN X j) (processTree init X (i+1)))
        (batomicAt 9 init X (i+1)) + 20
  rw [ht2, hdec, touchedCount_append_c, bSumOn_append]
  have hsubT : ∀ z ∈ p', z ∈ touchedList init X (i+1) := by
    intro z hz
    rw [touchedList_succ]
    refine List.mem_append_right _ ?_
    rw [hpath]
    exact hsub z hz
  have htc1 : touchedCount (touchedList init X (i+1)) p' = p'.length :=
    touchedCount_eq_length_of_subset hsubT
  have hbeq : bSumOn (touchedList init X (i+1)) p' (batomicAt 9 init X (i+1))
      = bSum p' (batomicAt 9 init X (i+1)) :=
    bSumOn_eq_bSum_of_subset _ hsubT
  have hp2 : 2 * p'.length ≤ bSum p' (batomicAt 9 init X (i+1)) + 2 := by
    by_cases hpe : p' = []
    · rw [hpe]
      simp
    · have hsplit : p'.dropLast ++ [p'.getLast hpe] = p' :=
        List.dropLast_append_getLast hpe
      have hge : ∀ w ∈ p'.dropLast, 2 ≤ batomicAt 9 init X (i+1) w :=
        fun w hw => hpay w (hint w hw)
      have hsum := bSum_ge_two_mul_length hge
      have hlen2 : p'.dropLast.length = p'.length - 1 := List.length_dropLast
      have hone : 1 ≤ p'.length := by
        cases p' with
        | nil => exact absurd rfl hpe
        | cons a l => simp
      have hsum2 : bSum p' (batomicAt 9 init X (i+1))
          = bSum p'.dropLast (batomicAt 9 init X (i+1))
            + bSum [p'.getLast hpe] (batomicAt 9 init X (i+1)) := by
        rw [← bSum_append_c, hsplit]
      omega
  omega

/-! ## D.7 The assembled step, induction, master and capstones -/

/-- **THE REFORMED ATOMIC STEP** (`hstepZ`): the two-clause invariant
reproduces across every access — C1 via the cover, C2S via
{W-cap (proven), PZB tautology (proven), zb-kernel}. -/
theorem hstepZ {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (hsize : init.num_nodes = n) (hbst : IsBST init)
    (hmem : ∀ i : Fin n, X i ∈ init.toKeyList)
    (h213 : X avoids ![2, 1, 3]) (h231 : X avoids ![2, 3, 1])
    (hkZB : ∀ i, i < n → INVZA 9 init X i →
      ∀ (b' : Bool) (j : ℕ), FirstOwnAfter X (i+1) b' j →
      zlbOn (touchedList init X i)
        (divergeSuffix (accessN X j) (accessN X i) (processTree init X i))
        (batomicAt 9 init X i) ≤ 9) :
    ∀ i, i < n → INVZA 9 init X i → INVZA 9 init X (i+1) := by
  intro i hi hINV
  exact ⟨INVZA_C1_step init X hsize hbst i hi hINV,
    INVZA_C2S_step init X hsize hbst hmem h213 h231 i hi hINV (hkZB i hi hINV)⟩

/-- The reformed invariant propagates from the base case through the step. -/
theorem INVZA_all_of_step {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (hstep : ∀ i, i < n → INVZA 9 init X i → INVZA 9 init X (i+1)) :
    ∀ i, i ≤ n → INVZA 9 init X i := by
  intro i
  induction i with
  | zero =>
      intro _
      exact INVZA_zero 9 init X
  | succ i ih =>
      intro hin
      exact hstep i hin (ih (Nat.le_of_succ_le hin))

/-- **MASTER discharge (κ = 9, reformed)**: the two-clause invariant implies
the per-access MASTER inequality of the pooled ledger capstone. -/
theorem masterAtomic_of_INVZA {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ)
    (hsize : init.num_nodes = n) (hbst : IsBST init)
    (i : ℕ) (hi : i < n) (hINV : INVZA 9 init X i) :
    2 * costN init X i
      ≤ ledgerP 9 (costN init X) (freshN init X) i
        + 2 * 9 * (1 + freshN init X i) := by
  obtain ⟨hC1, hC2S⟩ := hINV
  have h2 := hC2S (sideF X i) i (firstOwnAfter_self X i hi)
  have hsplit := costN_split init X hsize hbst i hi
  have htc : tcOf init X (accessN X i) i
      = touchedCount (touchedList init X i)
          (searchPath (accessN X i) (processTree init X i)) := rfl
  have hsub : bSumOn (touchedList init X i)
      (searchPath (accessN X i) (processTree init X i)) (batomicAt 9 init X i)
      ≤ bSum (keySupp init) (batomicAt 9 init X i) := by
    unfold bSumOn
    refine bSum_le_of_subset _ _ _ ?_ ?_
    · exact (searchPath_nodup _ _ (processTree_isBST init X hbst i)).filter _
    · intro z hz
      have hz1 : z ∈ searchPath (accessN X i) (processTree init X i) :=
        List.mem_of_mem_filter hz
      have hz2 := searchPath_subset_toKeyList _ _ z hz1
      rw [processTree_toKeyList] at hz2
      exact mem_keySupp.mpr hz2
  exact master_of_C1A_C2A_strict20
    (ledgerP 9 (costN init X) (freshN init X) i)
    (touchedCount (touchedList init X i)
      (searchPath (accessN X i) (processTree init X i)))
    (freshN init X i)
    (bSumOn (touchedList init X i)
      (searchPath (accessN X i) (processTree init X i)) (batomicAt 9 init X i))
    (costN init X i)
    (Nat.le_trans hsub hC1) (by omega) (by omega)

/-- **THE COMPLETE REFORMED CONDITIONAL (κ = 9).**  Given the SINGLE zb
counting kernel, the MASTER per-access inequality holds in the exact
`∀ i : Fin n` hypothesis shape of the pooled capstone. -/
theorem hmasterAtomic_of_zb_kernel (hkZB : AtomicZBKernel) :
    ∀ (n : ℕ) (X : Fin n → ℕ) (init : BinaryTree),
      init.num_nodes = n → IsBST init → (∀ i : Fin n, X i ∈ init.toKeyList) →
      (X avoids ![2, 1, 3]) → (X avoids ![2, 3, 1]) →
      ∀ i : Fin n, 2 * costN init X i ≤
        ledgerP 9 (costN init X) (freshN init X) i
          + 2 * 9 * (1 + freshN init X i) := by
  intro n X init hsize hbst hmem h213 h231 i
  have hstep := hstepZ init X hsize hbst hmem h213 h231
    (hkZB n X init hsize hbst hmem h213 h231)
  have hINV : INVZA 9 init X (i : ℕ) :=
    INVZA_all_of_step init X hstep (i : ℕ) (Nat.le_of_lt i.isLt)
  exact masterAtomic_of_INVZA init X hsize hbst (i : ℕ) i.isLt hINV

/-- **DEQUE CHALLENGE from the ONE zb kernel** (`c = 38`): the exact statement
of `Challenge_Splay_Deque.lean`'s `theorem deque`. -/
theorem deque_challenge_CLOSED_of_zb_kernel (hkZB : AtomicZBKernel) :
    ∃ c, ∀ n, ∀ X : Fin n → ℕ,
    (X avoids ![2, 1, 3]) → (X avoids ![2, 3, 1]) →
    ∀ (init : BinaryTree), (h_size : init.num_nodes = n) → IsBST init →
    (∀ i : Fin n, (X i) ∈ init.toKeyList) →
    splay.sequence_cost init X ≤ c * n * (KlazarAckermann.alpha n) :=
  deque_challenge_of_ledger_masterP 9 (hmasterAtomic_of_zb_kernel hkZB)

/-- **DEQUE CONJECTURE from the ONE zb kernel**: the exact statement of
`Challenge_Splay_DequeConjecture.lean`'s `theorem deque_conjecture`. -/
theorem deque_conjecture_CLOSED_of_zb_kernel (hkZB : AtomicZBKernel) :
    ∃ c, ∀ n, ∀ X : Fin n → ℕ,
    (X avoids ![2, 1, 3]) → (X avoids ![2, 3, 1]) →
    ∀ (init : BinaryTree), (h_size : init.num_nodes = n) → IsBST init →
    (∀ i : Fin n, (X i) ∈ init.toKeyList) →
    splay.sequence_cost init X ≤ c * n :=
  deque_conjecture_challenge_of_ledger_masterP 9 (hmasterAtomic_of_zb_kernel hkZB)
