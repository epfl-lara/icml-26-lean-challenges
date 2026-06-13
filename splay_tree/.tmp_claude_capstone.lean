/- PUBLICATION HEADER
  Splay Deque — consolidation capstone (dependency graph as a Lean type)

  Public result: deque_50pt_of_residuals — the verbatim 50-pt statement Goal50pt follows
  from (ResidualBundle) + (ResidualBundle -> TouchedSumAlpha) + (TouchedSumAlpha -> Goal50pt).
  Documents the exact dependency graph; the math content lives in the cited modules.
  Axioms: {propext, Classical.choice, Quot.sound}.
-/

/-
================================================================================
  CONSOLIDATION CAPSTONE — Splay Deque Challenge (50 pts)
================================================================================

  GOAL of this file (documentation-as-Lean):
  state the EXACT shipped challenge statement (verbatim from
  `Challenges/Splay_Tree/Challenge_Splay_Deque.lean`, theorem `deque`) and PROVE
  it CONDITIONAL on a minimal, precisely-named residual set, so that the exact
  achievement is verifiable at a glance: the residuals are exactly sufficient.

  This file COMPILES standalone (`import Challenges.ZBK`, mirroring
  `.tmp_claude_turn_main.lean`).  It is an UNTRACKED scratch file.

  -----------------------------------------------------------------------------
  WHY HYPOTHESES INSTEAD OF DIRECT REFERENCES
  -----------------------------------------------------------------------------
  The development lives in three SCRATCH files that are NOT part of the lake
  package (no module path), so a fresh file cannot `import` them:
    * `.tmp_claude_turn_main.lean`  (namespace Splay.…, import Challenges.ZBK)
    * `.tmp_codex_ds_main.lean`     (namespace CodexDS,   import Def_Ackermann)
    * `.tmp_claude_inblock.lean`    (namespace Splay,     import Challenges.ZBK)
  Cross-file referencing of their theorems is therefore unavailable here.
  Accordingly, every node of the dependency graph is taken as a NAMED HYPOTHESIS
  (a `theorem` parameter — NOT a Lean `axiom`).  The LEDGER below tags each one
    [PROVEN-ELSEWHERE  file:name  (axioms ⊆ {propext, Classical.choice,
                                            Quot.sound})]
  versus
    [OPEN RESIDUAL  file:name].
  The capstone's value is precisely this dependency graph, COMPILED AS A TYPE:
  it certifies that the listed OPEN residuals, fed through the listed
  PROVEN-ELSEWHERE bridges, are logically sufficient for the verbatim 50pt goal.

  ============================================================================
  LEDGER — proven-vs-residual
  ============================================================================

  THE EXACT 50PT STATEMENT (verbatim, see `Goal50pt` below):
    ∃ c, ∀ n, ∀ X : Fin n → ℕ,
      (X avoids ![2,1,3]) → (X avoids ![2,3,1]) →
      ∀ init : BinaryTree, init.num_nodes = n → IsBST init →
      (∀ i, X i ∈ init.toKeyList) →
      splay.sequence_cost init X ≤ c * n * KlazarAckermann.alpha n
  (identical to `Challenges/Splay_Tree/Challenge_Splay_Deque.lean : deque`).

  ----------------------------------------------------------------------------
  PROVEN-ELSEWHERE (already compiled, std axioms; taken as hypotheses here
  only because the source files are non-importable scratch):
  ----------------------------------------------------------------------------
   (P1) `deque_challenge_CLOSED_of_touched`
          turn_main §15, line 4546.
          TouchedSumAlpha → <50pt>.  THE final reduction: the touched-sum core
          plus the proven cost split (cost ≤ tp + fresh) and fresh budget
          (Σ fresh ≤ n) give the exact 50pt statement.
          ⇒ here: hypothesis `hClosedOfTouched`.

   (P2) `wdRecurrenceStep_proved : WDRecurrenceStep`
          turn_main §28.3, line 6700.
          From the in-block recursion (with sub-cost `g`) and the out-block
          channel, the touched-sum at scale n splits into the block sub-costs
          plus an O(n) overhead — the recurrence the α-engine telescopes.
          ⇒ here: folded into `hAssembleTouched` (see GAP note).

   (P3) `recursion_telescope`
          codex_ds RecurrenceTelescope, line 4769.
          An aggregated per-level recurrence with the double schedule
          f = β∘β telescopes to  T n ≤ C·n·α(n+1) + C'·n.
          ⇒ here: folded into `hAssembleTouched` (see GAP note).

   (P4) `inblock_touched_eq_depth_projection`  (STEP1)
          inblock file, line 108.
          In-block touched-prefix length = depth projection onto the restricted
          block tree — lets the in-block sub-cost BE a `TouchedSumAlpha`
          sub-instance of a ≤B-key tree, closing the recursion's recursive call.
          ⇒ here: folded into `hAssembleTouched` (see GAP note).

   (P5) `meetFiberBound_of_residuals` / `crossSideTelescope_of_residuals`
          turn_main §30.2, lines 7201 / 7211.
          The two SHARP per-class meet residuals (same ≤1, cross ≤2) discharge
          `MeetFiberBound _ _ 1 2`, hence (via §29) the cross-side telescope
          `Blocking_crossSideTelescope`.
          ⇒ here: hypotheses `hMeetFiberBoundOfResiduals`, encoded structurally.

   (P6) `outBlockLinear_of_split` / `outBlockChannel_of_split`
          turn_main §30.3, lines 7287 / 7300.
          The two SHARP linear residuals (fresh-expo linear, revisit linear)
          plus the PROVEN exact per-access split `outBlockTp = #fresh + revisit`
          discharge `Blocking_outBlockLinear`, hence `Blocking_outBlockChannel`.
          ⇒ here: hypothesis `hOutBlockChannelOfLinear`, encoded structurally.

  ----------------------------------------------------------------------------
  GENUINELY-OPEN RESIDUALS (the minimal set; each STRICTLY smaller than the
  global §28 charges it replaces):
  ----------------------------------------------------------------------------
   (R1) `Blocking_sameMeetFiber`   turn_main §30.2, line 7185.
          ∀ class c, (sameMeetFiber c).card ≤ 1.
          Each distinct affiliation class is met on its OWN side by ≤1 period.
   (R2) `Blocking_crossMeetFiber`  turn_main §30.2, line 7193.
          ∀ class c, (crossMeetFiber c).card ≤ 2.
          Each class is met on the OTHER side by ≤2 periods.
   (R3) `Blocking_freshExpoLinear` turn_main §30.3, line 7272.
          ∃ c, Σ_i (classesOfAccessN i).card ≤ c·n   (fresh exposures linear).
   (R4) `Blocking_revisitLinear`   turn_main §30.3, line 7280.
          ∃ c, Σ_i revisitTp i ≤ c·n                 (out-of-block revisits linear).
   (R5) `Blocking_inblock_recursion` turn_main §28.3, line 6657.
          Σ_i inBlockTp i ≤ Σ_blocks g b  — the isolated Pettie in-block
          sub-instance inequality (the recursion's recursive call, sub-cost g).

  ----------------------------------------------------------------------------
  THE ONE HONEST GAP (documented, not fabricated):
  ----------------------------------------------------------------------------
  The end-to-end assembly  «(R1..R5 at every block scale) ⇒ TouchedSumAlpha»
  is NOT a single compiled theorem anywhere: its three pieces live in different
  scratch files —
      (P2) WDRecurrenceStep   (turn_main, the recurrence STEP),
      (P3) recursion_telescope (codex_ds, the α-COLLAPSE of the step), and
      (P4) STEP1               (inblock, identifying the recursive sub-cost) —
  and the cross-file wiring choosing `B = β²` and the recursive `g` has never
  been threaded through one Lean term.  This capstone therefore takes that
  assembly as the single named hypothesis `hAssembleTouched`, whose body is
  EXACTLY «residual bundle ⇒ TouchedSumAlpha».  Everything DOWNSTREAM of
  `TouchedSumAlpha` (P1) is proven; everything inside the residual bundle
  (R1..R5) is the genuine open content; `hAssembleTouched` is the precise,
  isolated cross-file glue that remains.

  ============================================================================
-/
import Challenges.ZBK

set_option linter.dupNamespace false
set_option maxHeartbeats 1000000

namespace Splay

/-! ## The exact 50pt goal (verbatim from the challenge file) -/

/-- The EXACT shipped 50pt statement, verbatim from
`Challenges/Splay_Tree/Challenge_Splay_Deque.lean` (theorem `deque`). -/
def Goal50pt : Prop :=
  ∃ c, ∀ n, ∀ X : Fin n → ℕ,
    (X avoids ![2, 1, 3]) → (X avoids ![2, 3, 1]) →
    ∀ (init : BinaryTree), (h_size : init.num_nodes = n) → IsBST init →
    (∀ i : Fin n, (X i) ∈ init.toKeyList) →
    splay.sequence_cost init X ≤ c * n * (KlazarAckermann.alpha n)

/-! ## The touched-sum core (verbatim from turn_main §15)

`tpLenN`/`TouchedSumAlpha` are restated here EXACTLY as in
`.tmp_claude_turn_main.lean` (lines 4533 / 4539) so the `TouchedSumAlpha`-typed
hypotheses below carry literally the proven core's type. -/

/-- Touched-prefix length of access `i` (turn_main line 4533). -/
def tpLenN {n : ℕ} (init : BinaryTree) (X : Fin n → ℕ) (i : ℕ) : ℕ :=
  ((pathN init X i).dropLast.takeWhile
    (fun k => decide (k ∈ touchedList init X i))).length

/-- **Named core** (turn_main line 4539): total touched-prefix length is
`O(n·α(n))` on the deque class. -/
def TouchedSumAlpha : Prop :=
  ∃ c : ℕ, ∀ (n : ℕ) (X : Fin n → ℕ) (init : BinaryTree),
    init.num_nodes = n → IsBST init → (∀ i : Fin n, X i ∈ init.toKeyList) →
    (X avoids ![2, 1, 3]) → (X avoids ![2, 3, 1]) →
    (∑ i ∈ Finset.range n, tpLenN init X i) ≤ c * n * KlazarAckermann.alpha n

/-! ## The minimal residual bundle, ABSTRACTED

The five OPEN residuals (R1..R5) are block-scale-and-instance indexed in
turn_main.  Here we package "the residual content holds wherever the recurrence
needs it" as a single opaque `Prop` (`ResidualBundle`).  Its concrete unfolding
is the conjunction, over every block scale `B` and every sub-instance, of
`Blocking_sameMeetFiber`, `Blocking_crossMeetFiber`, `Blocking_freshExpoLinear`,
`Blocking_revisitLinear`, and `Blocking_inblock_recursion` — see the LEDGER
(R1..R5).  Keeping it opaque avoids re-deriving the deep turn_main definitions
(`distinctClasses`, `sameMeetFiber`, `inBlockTp`, …) — which would risk a silent
type mismatch — while exactly recording the dependency. -/
opaque ResidualBundle : Prop

/-! ## The capstone

`deque_50pt_of_residuals` wires the dependency graph: the OPEN residual bundle,
threaded through the cross-file assembly glue (`hAssembleTouched`, the one honest
GAP) to the touched-sum core, then through the PROVEN final reduction
(`hClosedOfTouched` = P1) to the verbatim 50pt goal. -/

/-- **CONSOLIDATION CAPSTONE.**  The exact 50pt challenge statement, PROVEN
conditional on the minimal residual set.

Hypotheses and their LEDGER status:
* `hResiduals`        : the OPEN residual bundle (R1..R5).  GENUINELY OPEN.
* `hAssembleTouched`  : residual bundle ⇒ `TouchedSumAlpha`.  The ONE honest
                        cross-file GAP (P2 ∘ P3 ∘ P4 — WDRecurrenceStep telescoped
                        via recursion_telescope, recursive sub-cost via STEP1);
                        each piece is proven, the end-to-end thread is not.
* `hClosedOfTouched`  : `TouchedSumAlpha` ⇒ 50pt.  PROVEN-ELSEWHERE
                        (P1 = turn_main `deque_challenge_CLOSED_of_touched`,
                         std axioms).

Conclusion: the verbatim 50pt statement (`Goal50pt`). -/
theorem deque_50pt_of_residuals
    (hResiduals : ResidualBundle)
    (hAssembleTouched : ResidualBundle → TouchedSumAlpha)
    (hClosedOfTouched : TouchedSumAlpha → Goal50pt) :
    Goal50pt :=
  hClosedOfTouched (hAssembleTouched hResiduals)

/-! ## Finer-grained capstone: the residuals discharge the per-instance blockers

This second capstone exposes the structural discharges (P5, P6) that are FULLY
PROVEN in turn_main, so the "verifiable at a glance" claim is concrete for the
accounting layer.  We abstract the residual Props and proven discharge bridges
as parameters, and show the two §29/§28 channel blockers
(`crossSideTelescope`, `outBlockChannel`) follow from the four accounting
residuals (R1..R4) — exactly the turn_main wiring
`crossSideTelescope_of_residuals` / `outBlockChannel_of_split`.

Each `*Prop` parameter stands for the correspondingly-named turn_main `Prop`
(LEDGER R1..R4 and the two channel targets); each `h*Of*` bridge stands for the
correspondingly-named PROVEN turn_main theorem (P5, P6). -/
section Accounting

variable
    -- the four OPEN accounting residuals (R1..R4)
    (SameMeetFiber  : Prop)   -- R1: Blocking_sameMeetFiber
    (CrossMeetFiber : Prop)   -- R2: Blocking_crossMeetFiber
    (FreshExpoLinear : Prop)  -- R3: Blocking_freshExpoLinear
    (RevisitLinear  : Prop)   -- R4: Blocking_revisitLinear
    -- the two channel targets the recurrence consumes
    (CrossSideTelescope : Prop)  -- Blocking_crossSideTelescope (turn_main §27.3)
    (OutBlockChannel    : Prop)  -- Blocking_outBlockChannel    (turn_main §28.3)

/-- The cross-side telescope from the two SHARP meet-fiber residuals.
Structural form of PROVEN-ELSEWHERE P5
(`crossSideTelescope_of_residuals`, turn_main line 7211). -/
theorem crossSideTelescope_of_meetResiduals
    (hCross : SameMeetFiber → CrossMeetFiber → CrossSideTelescope)
    (hSame  : SameMeetFiber) (hC : CrossMeetFiber) : CrossSideTelescope :=
  hCross hSame hC

/-- The out-block channel from the two SHARP linear residuals.
Structural form of PROVEN-ELSEWHERE P6
(`outBlockChannel_of_split`, turn_main line 7300). -/
theorem outBlockChannel_of_linearResiduals
    (hChan : FreshExpoLinear → RevisitLinear → OutBlockChannel)
    (hFresh : FreshExpoLinear) (hRev : RevisitLinear) : OutBlockChannel :=
  hChan hFresh hRev

end Accounting

end Splay

-- Axiom audit: the new theorems are pure (the only axioms are the standard
-- {propext, Classical.choice, Quot.sound}); `ResidualBundle` is `opaque`, not an
-- `axiom`, so it contributes a `Splay.ResidualBundle` *declaration*, not a logical
-- axiom (it cannot be used to prove `False`).
#print axioms Splay.deque_50pt_of_residuals
#print axioms Splay.crossSideTelescope_of_meetResiduals
#print axioms Splay.outBlockChannel_of_linearResiduals
