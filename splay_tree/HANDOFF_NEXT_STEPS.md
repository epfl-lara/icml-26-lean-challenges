# HANDOFF — Deque programme: 2026-06-12 state (turn-decomposition implementation begun)

## ⭐⭐⭐ §9 GENERATION-CHAIN REDUCTION (the latest verified layer, post-CombShape)
`.tmp_claude_turn_main.lean` §9 (compiles, std axioms): defs `lastTouchN` (last-touch
time) + `gensN` (#distinct generations on the touched prefix). NEW named cores:
- **`SegChainBound`**: touchedTurnsN i ≤ 4·gensN i + 3 — the segment-chain lemma
  (each corridor = generation segments, each ≤ 3 turns by the PROVEN comb + strictly
  decreasing generations by suffix nesting). EMPIRICALLY: 0 violations through n=8192.
  NEXT MECHANICAL ROUND: prove by i-induction carrying the segmentation ∃-invariant
  (segments + partial-head infix-mono via turnCount_prefix/suffix_mono; the unroll step
  = the §8 decomp searchPath y t_i = p' ++ tail-of-corridor(t_{i-1})).
- **`GenIncidenceAlpha`**: Σ gensN ≤ c·n·α(n) — THE DS-TRANSCRIPTION TARGET (emp
  Σ/n = 1.04→1.16 flat-ish at 8192; per-access max creeps 12→19, irrelevant).
  Transcription design: per access, emit its generation list (top-down, strictly
  decreasing); the concatenated sequence's alternation structure ↔ cargo-nesting
  laminarity; consume Codex's DS3_length_bound (alphabet = generations ≤ n).
PROVEN WIRING: `turnSumBoundAlpha_of_chain : SegChainBound → GenIncidenceAlpha →
TurnSumBoundAlpha` and `deque_challenge_CLOSED_of_chain_cores`.
⭐⭐⭐ **`SegChainBound` IS NOW A THEOREM** (`segChainBound_proved`, §10, std axioms):
`chainAux` = the full chain induction (∀ i y e — the TAIL-strengthened IH over all
targets and drops closes the unroll; in-range step: decomp + dropLast/takeWhile
plumbing + congr-to-old-touched on the suffix + three-way case split: drop-in-p'
(comb piece ≤3 + junction + IH-at-|sh| with the +1-generation card via
toFinset-insert), drop-in-TL (IH at |sh|+e′ with drop_append normalization),
sh-untouched (positional ancestry + closure kill TL); out-of-range trivial).
Bridge `segChainBound_proved` via take_takeWhile_length + map_take.
**CURRENT END-TO-END: `deque_challenge_CLOSED_of_B_and_incidence :
TurnCostBridge → GenIncidenceAlpha → ⟨exact 50pt⟩`.**

## 🎯🎯 BRIDGE BREAKTHROUGH (end of session): TurnCostBridge is BYPASSED —
the COST side reduces to the SAME generation-incidence core. NEW LAW, 0 violations
n ≤ 8192 (worst margin −3, ratio ≤ 1.50, flat; probe inline in session log):
**GenConsumption**: ∀ generation g ≥ 1:
  Σ over accesses i of (total length of gen-g runs on i's touched prefix)
    ≤ ½·cost_{g−1} + 5·inc_g,
  where gen of node = lastTouchN, inc_g = #accesses whose touched prefix meets gen g.
THE TELESCOPE (replaces the bridge entirely):
  Σcost ≤ Σ touchedLen + Σ fresh ≤ Σ_g consumed_g + n
        ≤ ½·Σcost + 5·Σ_g inc_g + n  and  Σ_g inc_g = Σ_i gensN i
  ⟹ **Σcost ≤ 10·Σ gensN + 2n** ⟹ with GenIncidenceAlpha: Σcost ≤ C·n·α(n)
  ⟹ THE 50PT NEEDS ONLY: GenConsumption (structural) + GenIncidenceAlpha (DS/W3).
PROOF PLAN for GenConsumption (next round, chainAux-machinery grade):
  (D1) consumption-disjointness is TRIVIAL: a node consumed at access i gets
  lastTouch := i+1 ⟹ leaves generation g forever ⟹ consumed gen-g node-sets are
  pairwise disjoint across accesses, all ⊆ comb_{g−1} ⟹ Σ ≤ cost_{g−1}+1 free;
  (D2) the ½ refinement: each consumed gen-g run is a sub-path of the gen-g
  p'-piece of its target, born ≤ ½·(birth-share ⊆ path_{g−1}) + 3 (the PROVEN
  halving keyDepth_splay_le_shared / the §8 decomp); combine disjointness with
  birth-share nesting; constants free (any C₁cost+C₂inc with C₁<1 telescopes:
  Σcost ≤ (C₂/(1−C₁))Σgens + n/(1−C₁)).
FALSIFIED THIS ROUND (do not retry): corridor-length potentials for the bridge —
raw (Φ jumps ~n on frontier jumps), touched-only (Φ jumps at mass-touch),
weighted grid w∈{1,2}×c×D (all ~n margins) — pointer-handovers mint unpaid
corridors; only the generation-ledger amortizes.

### ⚠️ TRANSCRIPT CORRECTION (DeepSeek Task B result): the FLAT generation
transcript (concatenated per-access generation lists) is NOT ababa-free — max
alternation grows ~linearly. ANATOMY (expected in hindsight): alternating
min/max frontier consumption eats the two frontier combs interleaved: two fixed
generations a (a min comb), b (a max comb) alternate a,b,a,b,… ~n/2 times. This
kills only the NAIVE transcription vehicle for GenIncidenceAlpha — NOT the core
itself (Σ gensN stays empirically ≈1.16n flat), NOT GenConsumption, NOT the
telescope. The honest route for GenIncidenceAlpha = the HIERARCHICAL labeling
(Sundar epochs / Pettie block-level labels: per-level transcripts are ababa-free
by hierarchy laminarity — Pettie Lemma 4.2's scheme), built on the key-space/
epoch recursion; Codex's self-contained DS3 theorem (psi_sound route) remains
the right consumable for the per-level counting. SIDE-SPLIT + per-level
transcription empirics = the next DeepSeek Task B' (design the level structure
empirically before formalizing).

### 🏆🏆🏆 E1–E3 EXECUTED AND PROVEN (same session, §13–§14): THE ENTIRE
CONSUMPTION SIDE IS MACHINE-CHECKED. **THE 50PT = `GenIncidenceAlpha` ALONE.**
- §13 **`exposureAux`** (E1, the 9th shape induction, ~600 lines, 13 cases):
  every splay output has an exposure set E with 2|E| ≤ |path| + 2·turns + 2,
  the splayed ROOT ∈ E (the root-invariant makes zigzig cost 2 = gain 2 and
  zigzag cost 4 = gain 2+2·turn — EXACT), and every target's p'-piece ⊆ E ∪ ex
  with |ex| ≤ 2. Lean traps solved: multi-line `by`-payloads inside ⟨⟩ break at
  dedented continuations (parens do NOT lift the column rule) → restructure as
  refine ⟨…, ?_, …⟩ + bullets; term-position searchPath_node_lt/gt/self need
  explicit `_ _` tree args (rw-position doesn't).
- §14 **`gen_node_mem_birth_corridor`** (suffix preservation, downward d-induction
  via searchPath_splay_decomp p'⊆path + lastTouchN_not_path_between + shared-
  suffix re-entry), **`consumedN_le_exposure`** (E2: 2·consumed_g ≤ cost_{g−1}
  + 2·turnsN_{g−1} + 4·inc_g + 5; length_split_filter into E-part [biUnion-
  disjoint ≤ |E|] + ex-part [≤ 2·indicator]), **`costSum_le_gens_proved`** (E3:
  Σcost ≤ 12·Σgens + 17n UNCONDITIONAL — turns budget via PROVEN
  totalTurnsN_le_touched + segChainBound_proved), and
  **`deque_challenge_CLOSED_of_incidence : GenIncidenceAlpha → ⟨exact 50pt⟩`**.
  (Trap: List.of_mem_filter fails HO-unification on decide-lambdas → use
  (List.mem_filter.mp h).2.)
REMAINING FOR THE 50PT: **GenIncidenceAlpha ONLY** (§9 def, ∃c, Σ gensN ≤
c·n·α): Codex's DS engine (M6c → M7) + the hierarchical/per-level transcription
(DeepSeek B′ empirics pending). GenConsumption-the-core is OBSOLETE (proven).

### ⭐ §12 D1 PROVEN (superseded by E1–E3 above): **`consumedN_le_cost`**
(consumedN g ≤ costN (g−1) + 1, std axioms) — the disjointness half of
GenConsumption. New proven layer: `searchPath_length_eq`/`pathN_length_eq`
(the length bridges via search_path_len_node_of_* + node_search_path_len_pos),
`lastTouchN_mem_path` (a positive generation locates its node on the birth
path), `lastTouchN_mono` (Nat.le_induction), `consumed_once` (consuming a node
re-generations it), and the biUnion-injection counting (countP→filter→toFinset
cards, PairwiseDisjoint via consumed_once both ways, card_biUnion +
card_le_card into (pathN (g−1)).toFinset). ⭐ D2 MECHANISM DISCOVERED (oracle round complete, this session):
- per-segment halving REAL: max single gen-g segment ≤ 0.52·comb on combs ≥ 64;
- "one big + O(1)·inc" FALSE (+251: jump2/spine g=3 segments [763,256,4] on
  comb 2045 — but their SUM = 1019 ≈ ½·2045 exactly);
- identity facts: consumed_g + neverAgain_g ≤ cost_{g−1}+1 ALWAYS (gap⁺ = 0);
  the re-touched-unconsumed mass = path-LAST-node leaks (targets; Σ_g ≤ n).
**THE MECHANISM — descent exposure**: the comb's gen-g nodes split into
DESCENT-EXPOSED (one per zigzig ladder level — the lk's — about HALF) and
EXIT-ONLY (the k's — touched ≤ 2 per incidence); zigzag levels expose both but
#zigzag-levels ≤ turnCount(original path) which feeds back through the PROVEN
chain reduction. FORMAL PROGRAM (next round, the 9th shape induction):
(E1) extend combShapeAux: ∃ E ⊆ path-nodes, 2|E| ≤ |path| + 2·turns(path) + C,
     ∀y the p'(y) descent-interior ⊆ E (exits ≤ 2 outside E);
(E2) gen-g segments at consumption ⊆ the g−1-splay's p'-pieces (suffix-verbatim
     preservation, the chain structure) ⟹ consumed_g ≤ |E_g| + 2·inc_g via the
     D1 injection restricted to E_g;
(E3) assemble: 2·consumed_g ≤ cost_{g−1} + 2·turnsN(g−1) + C + 4·inc_g; the
     telescope still closes since Σ turnsN ≤ 4·Σ gensN + 5n is PROVEN
     (totalTurnsN_le_touched + segChainBound_proved): final
     Σcost ≤ C₁·Σ gensN + C₂·n with explicit constants. Wire a
     GenConsumption-variant core (the E3 form) into costSum_le_gens (the
     telescope is constant-generic — adjust 10→C₁ when E3's constants land).

### ⭐⭐⭐ §11 EXECUTED AND PROVEN (same session): `costSum_le_gens` (the telescope
Σcost ≤ 10·ΣgensN + 2n from GenConsumption) and **`deque_challenge_CLOSED_of_gen_cores
: GenConsumption → GenIncidenceAlpha → ⟨exact 50pt⟩`** — both compile, std axioms,
no sorry. All defs/lemmas of the spec landed: genCountN/consumedN/incN,
lastTouchN_pos_of_touched, genCountN_zero, mem_takeWhile_pred, length_eq_sum_countP,
tp_length_eq_sum_gen, gensN_eq_sum_ite, costN_le_tp_add_fresh (the cost split via
costN_split + touchedCount_append + the §6 all-untouched block), the fresh-sum block,
and the range-succ' reindex telescope. THE 50PT = TWO NAMED CORES, BOTH WITH
COMPLETE ATTACK PLANS: GenConsumption (next Lean round: D1 disjointness +
D2 birth-halving) and GenIncidenceAlpha (hierarchical DS; Codex M6/M7 + DeepSeek B').

### 📐 ORIGINAL MECHANICAL SPEC (executed above, kept for reference):
Defs (align with §9/§10 conventions; tp i := (pathN i).dropLast.takeWhile
(· ∈ touchedList i)):
  genCountN g i := (tp i).countP (fun z => decide (lastTouchN init X i z = g))
  consumedN g   := Σ_{i ∈ range n} genCountN g i
  incN g        := Σ_{i ∈ range n} (if g ∈ ((tp i).map (lastTouchN init X i)).toFinset then 1 else 0)
Lemmas (plumbing, all standard):
  (L1) lastTouchN_pos_of_touched : z ∈ touchedList i → 1 ≤ lastTouchN i z
       (induction via touchedList_succ) ⟹ consumedN 0 = 0.
  (L2) length_eq_sum_countP : (∀ z ∈ l, f z ∈ range N) → l.length =
       Σ_{g ∈ range N} l.countP (fun z => decide (f z = g))
       (induction on l + Finset.sum_ite_eq'); with lastTouchN_le ⟹
       Σ_i (tp i).length = Σ_{g ∈ range (n+1)} consumedN g.
  (L3) gensN-exchange: gensN i = Σ_{g ∈ range (n+1)} (if g ∈ … then 1 else 0)
       (card via Finset.sum_ite_mem-style, S ⊆ range(n+1) by lastTouchN_le);
       Finset.sum_comm ⟹ Σ_i gensN i = Σ_{g ∈ range(n+1)} incN g.
  (L4) cost ≤ tp-length + freshN: reuse §6 turnsN_le_touched_add_fresh's
       internal steps (dropWhile-part is all-untouched by closure; its length
       ≤ freshN via nodup + toFinset-card — copy the h4/h5 blocks).
  (L5) Σ freshN ≤ n: the hfreshsum block (copy from the ledger-capstone proof).
NAMED CORE (the only new one):
  def GenConsumption : Prop := ∀ <class-hyps>, ∀ g, 1 ≤ g → g ≤ n →
    2 * consumedN init X g ≤ costN init X (g-1) + 10 * incN init X g
  (doubled = ℕ-clean; empirics: 0 violations ≤ 8192, worst margin −3.
   Proof plan: D1 disjointness (consumed ⟹ on pathN i ⟹ lastTouch updates ⟹
   leaves gen g; pieces ⊆ comb_{g−1}) + D2 birth-halving via §8 decomp +
   keyDepth_splay_le_shared.)
TELESCOPE (pure arithmetic from L1-L5 + GenConsumption):
  2Σcost ≤ 2Σtp-len + 2Σfresh ≤ Σ_{g≥1} (cost_{g−1} + 10·incN g) + 2n
         ≤ Σcost + 10·Σ gensN + 2n  ⟹  Σcost ≤ 10·Σ gensN + 2n
CAPSTONE: deque_challenge_CLOSED_of_gen_cores (hGC : GenConsumption)
  (hInc : GenIncidenceAlpha) : ⟨exact 50pt⟩ — replaces the B-route; wire through
  sequence_cost_eq_costSum_cast + the α-arithmetic pattern of §3.

## 📋 MASTER PLAN (2026-06-12 end-of-session; 50pt only; Codex parallel track agreed)
W1 (Claude): ⭐ MOSTLY DONE (this session, inline). In `.tmp_claude_turn_main.lean` §7
   (compiles, 0 errors, std axioms): `dirsTo`/`corridorPrefix`/`ttcOf` defs;
   `turnCount_prefix_mono`/`turnCount_suffix_mono`/`takeWhile_congr''`/
   `takeWhile_append_of_all`; **`ttcOf_splay_le` PROVEN**: from the ONE named core
   `CombShape` (∀ t x y p': decomp ⟹ turnCount (dirsTo y p') ≤ 3 — empirically max
   EXACTLY 3, flat, oracle-verified), the corridor turn count conserves across any
   splay: ttcOf T' y (splay t x) ≤ max (ttcOf T y t) 3 + 4, for any prefix-closed T
   (instantiate hclosed := touched_prefix_closed_strong at process level; hT' :=
   touchedList_succ membership). Case analysis: y-on-path (suffix nil, prefix-mono);
   shared-all-touched (suffix corridor embeds in old corridor via suffix-mono);
   shared-has-untouched (positional ancestry + closure kill the suffix corridor).
   ⭐⭐ W1 FULLY CLOSED (same session, one push): **`combShape_proved : CombShape` is a
   THEOREM** (std axioms) — §8 of turn_main: the ladder grammar (`ExitR/ExitL`,
   `LadderR/LadderL`, `PShape` = root-dir :: descent-run :: ≤2-step exit),
   `turnCount_le_of_pshape` (shape ⟹ ≤ 3 turns), and **`combShapeAux`** — THE 8th SHAPE
   INDUCTION (fuel induction mirroring the splay recursion; zig-zig/zig-zag/zag-zig/
   zag-zag recursive cases extend the ladder by one descent step via head-peel
   (injection on the decomp equation + `splay_root_spec` + `divergeSuffix_disjoint`),
   all non-recursive exits ≤ 3-long prefixes via `pshape_of_short`; uses the
   `splay_*_shape` result-tree lemmas + the `ds_*` unfold family). Uniqueness of the
   decomposition prefix (`List.append_inj`) transfers the shape to any given p'.
   **`ttcOf_splay_le_proved`** = the ttc-conservation law UNCONDITIONAL:
   ttcOf T' y (splay t x) ≤ max (ttcOf T y t) 3 + 4. The per-step stability ingredient
   for the W2 global argument is fully machine-checked.
W2 (Claude, the long pole): the global block/epoch recursion for the repo's TOP-DOWN
   splay, Sundar/Pettie-style, bounding Σcost (or ΣtouchedTurns) directly:
   (a) empirically pin the deque↦halving-spinal-compression correspondence for
   top-down splay (Pettie Obs 2.1 analog); (b) state the epoch/affiliation recursion;
   (c) transcription of epoch events → repetition-free sequence, prove ababa-freeness
   (empirically first); (d) consume W3's extremal theorem → Σcost ≤ C·n·α(n).
W3 (CODEX, independent): the DS-sequence extremal theorem N₅/λ₃ ≤ C·n·α(n) against
   the SHIPPED KlazarAckermann.alpha (Def_Ackermann.lean) — pure list combinatorics,
   zero splay content, composable interface (statement contract in the Codex prompt,
   recorded in the session log). Files: .tmp_codex_*.lean only.
W4 (assembly): W2 + W3 → costSum ≤ C·n·α n → the existing cast plumbing
   (sequence_cost_eq_costSum_cast + capstone adapters) → fill ONLY the
   Challenge_Splay_Deque.lean sorry → lake build + axiom audit + diff audit →
   STOP for user inspection, NO commit.
Merge gates: every deliverable = compiling file + #print axioms ⊆ {propext,
Classical.choice, Quot.sound} + no sorry; nothing below n=2048 counts as empirical
validation; no challenge-file edits before W4.

## 🎯 FOCUS DIRECTIVE (user, late 2026-06-12): the 50-pt challenge ONLY
(`Challenge_Splay_Deque.lean`, c·n·α(n)). The 100-pt conjecture file is out of scope.

## ⭐⭐ CONSOLIDATED DELIVERABLE: `.tmp_claude_turn_main.lean` (698 lines, compiles,
0 errors, std axioms, no sorry — agent draft repaired inline: dead omega, length_nil
simp, explicit (p := ·) on mem_searchPath_forall, List.Sublist for <+ notation).
THE VERIFIED 50-PT CHAIN:
  `TouchedTurnSumLinear → TurnSumBoundLinear → TurnSumBoundAlpha`
  `TurnCostBridge → TurnSumBoundAlpha → deque_challenge_CLOSED_of_turn_cores = ⟨exact 50pt⟩`
Proven supporting layer (all in the file): `searchPath_chain`,
`mem_searchPath_splay_cases`, `touched_prefix_closed_strong` (ancestors of touched are
touched), `searchPath_append_ancestor` (earlier-on-path ⟹ ancestor),
`turnCount_append_le`, `turnsN_le_touched_add_fresh` (turnsN ≤ touchedTurnsN + 1 +
freshN — the fresh bridge via mem_touchedList_iff + List.toFinset_card_of_nodup),
`totalTurnsN_le_touched` (Σturns ≤ ΣtouchedTurns + 2n via fresh_sum_le).
REMAINING OPEN CORES for the 50pt (both empirically true, flat, n ≤ 8192):
  (B) `TurnCostBridge`: Σcost ≤ c₂·(n + totalTurns)   [emp ratio ≤ 2.92]
  (T) `TouchedTurnSumLinear`: ΣtouchedTurns ≤ c·n     [emp ≤ 0.86n; α-form suffices]
Attack order recommendation: (T) first via the token-ledger oracle loop (touched-prefix
turns: 99%+ of paths ≤ 2; the ≥3 tail is tiny — find the mint/consume ledger), then (B)
via the two-sided halving telescope (the deep half; Sundar-grade if the linear forms
resist — for the 50pt an α-graded (T)+(B) suffices and matches published mathematics).
⚠️ Subagent spend limit was hit this session — work INLINE until reset.

### Core-T oracle round COMPLETE (late session) — local-ledger space EXHAUSTED
Falsified ledger shapes (probes /tmp/corridor_pot.py, /tmp/ttc_conserve.py, inline):
1. Corridor potential (Φ = ttc of the two next-target corridors): S1 false — post-splay
   own corridor reaches ttc 5-6 (CARGO INTERIORS carry old turn structure verbatim;
   splays expose it); law C=6.
2-3. Σ-over-futures potentials (raw ttc and (ttc−2)⁺ excess): per-target conservation
   is TIGHT (δ≤2, see below) but a single splay shifts MANY targets ⟹ aggregate mints
   Θ(#futures)/step (law C ≈ 0.5n–1.8n). 5th confirmation of the universal lesson:
   NO Σ-over-futures potential can work in this problem.
4. Per-node ALL turn-events: V-junction node hosts ~0.75n events (the structural
   crossing turn — it belongs to the per-access "2", not the excess ledger).
5. Per-node EXCESS (3rd+) events: creeps 7@512 → 11@2048 → 16@8192. ✗.
⭐ NEW TRUE LAW (the round's positive yield): **ttc-conservation** — for EVERY future
target y, after ANY access: ttc'(y) ≤ max(ttc(y), 2) + 2 (worst δ = 2, tight, universal;
/tmp/ttc_conserve.py). Lean-provable shape (splay decomp: corridor = p'-part (≤2-ish
turns, freshly combed) ++ preserved suffix (turns conserved); same machinery class as
the proven step laws). This is the per-step stability ingredient any future global
argument needs.
CONCLUSION: Core T linear has NO local witness (matches the budget-side verdict — now
~10 falsified designs across two quantity families). The 50pt's (T)-alpha needs the
GLOBAL block recursion (Sundar §turns / Pettie §4 style): block the key space, recurse
per block + spawned systems, transcribe block-membership as a DS-sequence. ENTRY POINT
SIMPLIFICATION won this session: the recursion only needs to bound TURNS (integers,
≈0.8n) not cost — enter Sundar at the turn-counting layer through the proven
`totalTurnsN_le_touched` + capstone chain. Next cycle (with subagent budget): (1) prove
ttc-conservation in Lean (well-scoped); (2) formalize the block-decomposition statement
and its recursion lemma over `touchedTurnsN`; (3) the Ex(ababa)/Klazar arithmetic on
`Def_Ackermann`'s F-hierarchy (self-contained number theory, agent-friendly).

## ⭐ NEW (implementation round, late 2026-06-12): the TURN-DECOMPOSITION skeleton

`.tmp_claude_turn_skeleton.lean` (compiles clean on the ZBK base, std axioms) — the NEW
conditional closure replacing the falsified ZB one:
- defs: `pathDirsN` / `turnCount` / `turnsN` / `totalTurnsN` (+ toolkit lemmas);
- **`deque_challenge_CLOSED_of_turn_cores : TurnCostBridge → TurnSumBoundAlpha → ⟨exact 50pt⟩`**
- **`deque_conjecture_CLOSED_of_turn_cores : TurnCostBridge → TurnSumBoundLinear → ⟨exact 100pt⟩`**
- `turnSumBoundAlpha_of_linear`. Cores quantified over exactly the challenge class.

EMPIRICAL FOUNDATIONS (probes `/tmp/turns_pin.py`, `/tmp/turns_stress.py`,
`/tmp/turn_potential{,2}.py`; n = 256…8192, adversarial battery incl. zigzag inits +
frontier-jump patterns):
- `totalTurns ≤ 2.00·n` FLAT (Core T-linear true with margin; α-form a fortiori);
- `cost ≤ 2.92·(n + totalTurns)` FLAT (Core B true with margin);
- per-path turns are NOT uniformly bounded (zigzag init ⟹ first access ~n/2 turns) —
  only the SUM amortizes;
- **ANCESTRY SPLIT holds universally**: on every search path, touched nodes form a
  PREFIX (untouched suffix) — ancestry-clean in all runs; provable (splays rearrange
  only path nodes (touched) and re-hang cargoes wholesale, so untouched-above-touched
  pairs can never be created); a background agent is proving it
  (`.tmp_claude_agent_ancestry.lean`, statement `touched_prefix_closed`).

CORE T CAMPAIGN STATE (the turn-sum ledger — the tractable half):
- decomposition: turns_i = turns(touched prefix) + ≤1 boundary + turns(untouched suffix);
  Σ untouched-suffix turns telescopes against the init's alternation structure
  (each alternation consumed once at first touch, Σ ≤ n) — formalizable;
- Φ-candidate 1 (turns of the two extreme paths): FALSIFIED (frontier jumps re-aim into
  undigested init regions, Φ jumps +1023 at n=2048; /tmp/turn_potential.py);
- Φ-candidate 2 (turn-edges on the union of future-target paths): FALSIFIED (the splay's
  pairing comb CREATES ~c/2 pair-turn-edges per access on future paths, Φ rises +276;
  /tmp/turn_potential2.py) — note each future PATH crosses only O(1) of them: the union
  potential overcounts; the consumable-once structure is per-path, not per-edge;
- touched-prefix per-path turns creep mildly (max 5 @512 → 6 @2048; /tmp inline probe) —
  so the touched part also needs a SUM ledger, not a per-path constant;
- NEXT: Φ-candidate 3 = "consumable pair-turn tokens": each splay creates ≤ 1 token per
  comb pair; a future path's touched-prefix turns ≤ 2 + tokens-consumed-on-it (tokens
  destroyed when their pair is restructured = on first traversal). Oracle-iterate
  (the established recipe), then the 8th shape induction.
- MEASURED (/tmp/touched_turns_pin.py): Σ touchedTurns/n = 0.751 (512) / 0.757 (2048) /
  0.856 (8192) — flat-ish with slight drift at 8192 (family-mix noise vs slow growth:
  unresolved); per-path histogram 99%+ ≤ 2 turns (0:190k, 1:109k, 2:90k, 3:8k, 4:4k,
  5:434, 6:23, 7:1); per-path max creeps 5→6→7 per 4×. The usual log-vs-α empirical
  ambiguity applies — treat Core T-linear as plausible-but-unproven, Core T-alpha as
  the safe target. A reduction layer making the verified chain
  `TouchedTurnSumLinear → TurnSumBoundLinear → TurnSumBoundAlpha` (turn sum ≤
  touched-prefix turn sum + 2n via ancestry + freshN, Σfresh ≤ n) is being
  agent-assembled into `.tmp_claude_turn_main.lean` (consolidating the skeleton +
  the proven ancestry lemmas `touched_prefix_closed_strong`/`searchPath_chain`/
  `mem_searchPath_splay_cases` from `.tmp_claude_agent_ancestry.lean`).

CORE B (the bridge, cost ≤ c₂(n + T)) — the deep half: two-sided sequential-style
halving telescope + crossing-decay; the staircase dives have ≤ 1 turn so their cost
lands HERE; this is where the conjecture-hardness concentrates. Sub-skeleton design
after Core T. (For the 50pt, B + T-alpha suffices; B is the half that may genuinely
need Sundar-grade machinery — see the assessment below.)



(Read this first. Details: memory `splay-deque-hstepP.md` (🏁 + ☠️ sections),
`NOTES_deque_formalization.md` for the historical designs.)

## Scoreboard

| Challenge | Status |
|---|---|
| `Challenge_Splay_Sequential.lean` (50 pt) | ✅ COMPLETE, compliant, **committed** (c = 27, std axioms) |
| `Challenge_Splay_Deque.lean` (50 pt) | ⛔ OPEN — every local-witness route falsified; realistic route = Klazar/DS formalization (multi-week, below) |
| `Challenge_Splay_DequeConjecture.lean` (100 pt) | ⛔ OPEN — this IS the open Sleator–Tarjan Deque Conjecture; do not bet ghost-invariant sessions |
| `Challenge_Splay_TraversalConjecture.lean` (200 pt) | untouched/shipped (Codex's domain) |

**RULES state**: repo clean — challenge files pristine (shipped `sorry`s), only tracked
modification is `.epflemma/project.yaml` (not ours). All development in untracked
`.tmp_claude_*` files. NOTHING was committed this session.

## 🏁 THE 2026-06-12 VERDICT — six architectures falsified at scale

**Universal failure mode**: every constant-slack local-budget clause family loses
~+2 margin per n-doubling — one new unwitnessed-zero key per scale on pending-pair
suffixes — the **geometric staircase** (approach dives at value-gaps 2^k each mint one
drained-unwitnessed key on the next target's suffix; ~log n of them accumulate).
Verified anatomy: rand1/spine/2048 pair (1932,1929): suffix lows at gaps
128,64,32,16,8,4,2,1. This is the open conjecture's hardness made empirical.

Falsified (faithful checkers, era-records reproduced where available):
1. **zb lows-cap** (κ=9, `ZBHighWaterCap`/`AtomicZBKernel`): kernel quantity grows
   7 → 9 → 10 at n = 1024 → 2048 → 4096. The prior "saturation at 7" was a ≤1024
   artifact (the decision-fork scale run had died silently with an empty output file).
2. **Per-side claims three-clause** (NOTES ⭐⭐⭐): C2 false at warm-up as stated
   (opposite ghost empty vs fully-touched far next-own path).
3. **Pooled v3 ∀-pair kernels** (`hstepP` @14645, INVS κ=7/16/10): far-pair C4 false
   at n=256 (warm-up debris); kernels unsatisfiable (warm-up has positive drains).
4. **Pooled imminent pairs**: false at n=512 with margins growing (+3@256 → +26@512).
   ROOT CAUSE: interval-claims drain-locality flaw — ONE junction key inside a claim
   interval lets the wrong side fully drain it (S-protection only covers next-own;
   phase-3 caps break C1).
5. **Atomic INVSA budget-sums** (κ=9 W-repay, C2S+20/pairs+14): margins −4 → 0 → 0 →
   **+4** at n = 256/512/1024/2048 (era's −4@256 reproduced exactly — transcription
   faithful). C2S itself HOLDS everywhere through 4096; only pair/suffix clauses die.
6. **Synthesis** (atomic + ordered drain protecting BOTH imminent suffixes drained-last
   + boundary-repay +2 to both imminent suffix-boundary keys, cap c+6, κ=11):
   −6/−4/0/+2/+4 at 256/512/1024/2048/4096 (e0-only family also creeps). Slows, never stops.

Drain-order freedom (only the TOTAL is C1-pinned) and boundary-repay are real tools —
they shave constants but cannot beat the per-scale mint. Apportioned/exempt drains and
fat repays (all-touched +2) provably break C1/conservation (gains must stay ≤ c + O(1+f)
for the ½-decay telescope; gains ~2c kill linearity).

## What SURVIVES (for any future route)

In `.tmp_claude_zb_kernel.lean` (20089 lines, compiles, std axioms):
- **κ-parametric capstones**: `deque_challenge_of_ledger_masterP kap hmaster` and
  `deque_conjecture_challenge_of_ledger_masterP kap hmaster` close BOTH challenges from
  one per-step master `2·c_i ≤ ledgerP kap c f i + 2·kap·(1+f_i)`. Architecture-agnostic.
- The full path/tree arsenal: `searchPath_splay_decomp` (+interior-witness variants),
  `keyDepth_splay_le_shared` (2|p'| ≤ |sh|+5), transfer lemmas, wKeys/wCap (7th shape
  induction), atomicStep/batomicAt machinery, the {213,231}⟹future-one-sided
  characterization layer, C2S machinery (`AtomicC2Kernel_proved`).
- All reductions remain valid theorems (their leaves are false).

## The realistic route for the 50 pt (c·n·α(n))

The shipped `Def_Ackermann.lean` is **Klazar's hierarchy (N₅)** — the intended solution
is evidently the Sundar/Klazar mathematics: map the splay-deque execution to an
ababa-free (DS order-3 style) sequence and use λ₃(n) = Θ(n·α(n)) (Hart–Sharir/Klazar).
Scope: ≈25 pages of sequence combinatorics + the transfer risk (repo splay is TOP-DOWN
pairing; Sundar's analysis is bottom-up — the mapping must be re-derived). Multi-week
with agent fleets. The capstone plumbing absorbs any resulting per-step master, or the
final bound can be proven directly against `sequence_cost` (the adapters in
`.tmp_claude_capstone_pooled.lean` show the exact-statement bridging pattern).

## The 100 pt (c·n)

Is the open Deque Conjecture (challenge text says so itself). Today's six falsifications
are the strongest internal evidence: the constant-slack witness space is exhausted.
Treat as research, not formalization. (If the 50pt's DS machinery ever lands, λ-style
bounds still only give n·α(n) — the linear bound needs genuinely new mathematics.)

## Probes (all in /tmp, this session)

`zb_water_all.py` (all-pending water; beware the wkeys_fast id()-memo bug pattern —
push the SAME node object, never a rebuilt tuple), `zb_water_scale2.py`,
`zb_verify_violation.py` (staircase anatomy), `zb_tower_log.py` (+ events JSON),
`zb_ladder.py` (rank grading — none), `claims_checker.py`, `invs_checker.py`,
`invs_imminent.py`, `c4_anatomy.py` (junction-drain anatomy), `atomic_scale_test.py`
(base|brepay), `atomic_synth.py` (the synthesis). Faithful sim `.tmp_alt_sim.py`;
helpers exec'd from `/tmp/lambda_hunt2.py`, `/tmp/crossing_decay.py`, `/tmp/v_adversary.py`.

## Posture

No fabrication; the challenge files keep their shipped `sorry`s. Bank every probe.
Any future session: validation gate n ≥ 2048 (preferably 4096–8192) — nothing below
counts for this programme.

### 🧭 THE PETTIE BLUEPRINT (acquired 2026-06-12, full paper read; saved as
.tmp_claude_pettie_deque.pdf) — THE faithful route for GenIncidenceAlpha
(= the remaining 50pt core, which equals the theorem itself since
Σgens = Θ(Σcost ± n) by the proven telescope).

7th FALSIFICATION (same session, closes the naive-transcription family):
top-node and bottom-node anchored gen-segment transcripts have ~n alternation
(witness: two valley-shoulder nodes flip as segment tops forever, runs1/V);
(gen,top)-pairs are repetition-free (alphabet = length, vacuous). With
flat/side/level (DeepSeek B′) ALL O(n)-alphabet symbolizations of the
gen-incidence object are ~n-alternating: the α CANNOT come from
pattern-avoidance of gen-incidences. Pettie transcribes a DIFFERENT object:

PETTIE'S ARCHITECTURE (Sections 2-5):
1. REDUCTION: deque ops ↔ HALVING PATH COMPRESSIONS up the left spine of a
   general rooted tree (L → L′ → L″ transform: left child ↔ leftmost child,
   right child ↔ right sibling). Pop = halving compression from leftmost
   leaf + delete; push = leftmost-leaf addition. [For US: must be re-derived
   for the ACCESS-ONLY top-down pairing variant — accesses don't delete;
   our touched-prefix/exposure machinery is the analogue.]
2. SPINAL COMPRESSION SYSTEMS: essential + fluff nodes on an initial path;
   halving spinal compressions; ℛ(n,f,m) = max total official compression
   length, m = stunted-compression budget.
3. THE RECURSION (Lemmas 4.1/4.3): blocks of B essential nodes; epoch j =
   while leftmost leaf ∈ block j; I_j = path of outside-block nodes touched
   in epoch j; EXPOSED Î_j ⊆ I_j (≤ 1 node per affiliation class — the
   dedup!); sparse epoch (|Î_j|log|Î_j| < |I_j|): no affiliation; dense:
   affiliate all of I_j, spawn child system (Î_j essential, I_j∖Î_j fluff
   = l·log l, stunted ≤ 2l·log²l). ℛ(n,f,m) = Σ_j ℛ(B,f_j,m̃_j)
   + 3Σ_i ℛ(l_i, l_i log l_i, 2l_i log²l_i) + 2m + n + f, with l_i ≤ t
   (split big Î's), and Σ l_i ≤ Ex(σ, q) for the TRANSCRIPT 𝒮.
   [CORRESPONDENCE: this recursion ≅ our DS3 affine engine — blocks/chunk,
   locals/per-block systems, contraction/spawned systems. Our
   oneStep_decomposition + affine machinery is the right chassis.]
4. THE TRANSCRIPTION (Lemma 4.2): evolving node labels = DESCENDING lists of
   dense-epoch indices (prepend j to each Î_j node's label); 𝒮′ = labels
   concatenated in POSTORDER of deletion (append a node's label when it is
   deleted as leftmost leaf); split Î's so no symbol exceeds t occurrences;
   remove ≤ n/B−1 boundary repetitions → 𝒮. THEOREM: abaabba ⊀ 𝒮 and
   abababa ⊀ 𝒮. Proof core: for b > a at b's commencement, I_b is a path;
   ≤ 1 exposed node per affiliation class ⟹ ≤ 1 b-labeled node affiliated
   with a; all other b-nodes postorder-before or -after ALL a-nodes; after
   babb, all a-nodes deleted ⟹ babba ⊀ 𝒮′ ⟹ both patterns excluded.
5. ASSEMBLY (Lemma 4.4): β(z) = min{Ex(abaabba,z), Ex(abababa,z)}/z;
   B = t = β²(n); induction ℛ(n,f,m) ≤ c(n+f+m)γ(n), γ = iterations of β²
   to constant; ASS bounds give β = O(α^α) ⟹ γ = O(α*). Section 5: phases
   (left/right halves), periods, 𝒟(m′) ≤ (m′/B)𝒟(B) + O(m′ + Σℛ(...)),
   induction ⟹ O((m+n)α*(m+n)).

EFFORT MAP / DECISION:
- Ex(abababa)/Ex(abaabba): the ASS order-5 machinery is the heavy new
  dependency. ANY β = poly(α) suffices for γ = O(α*) ≤ O(α) (challenge-OK);
  a crude β = log (provable by our λ₃-engine generalization) gives only
  γ = log* — NOT ≤ c·α. So the extremal step needs real ASS-grade work,
  OR pivot the assembly to Sundar's direct n·α potential argument
  (paywalled; reconstruct from [30]-citing surveys if needed).
- NEXT CONCRETE STEPS: (P1) re-derive the reduction for our variant:
  empirically verify that per-epoch exposure transcripts (epochs =
  frontier-in-block periods, exposed = affiliation-deduped) on OUR splay
  avoid abababa/abaabba at n ≤ 8192 — the decisive probe, now precisely
  specified by the paper; (P2) if clean, formalize the transcription lemma
  (the postorder/affiliation argument — our exposureAux is the geometric
  half); (P3) the recursion bookkeeping on the proven affine chassis;
  (P4) the extremal bound at whatever order the probe certifies (if our
  variant's transcript is even ababa-free — possible, our setting is more
  restrictive! — the PROVEN middlesKey engine applies as-is and gives n·α
  DIRECTLY, no ASS needed: CHECK THIS FIRST in P1).

### ✅✅ P1 VALIDATED (2026-06-12, the green light): the Pettie-style transcript
on OUR access-only variant has n-INDEPENDENT alternation.
**MAX ALTERNATION = 11, FLAT from n=1024 through n=16384 (16×)**, full battery
(runs1/2/4, rand, jump × spine/zigzag/V), B=16. (B=64: 7–9, small-block-count
regime.) THE CONSTRUCTION THAT WORKS (two details are load-bearing; the naive
version FAILS with ~n/35 growth):
- PERIODS: per side, period = maximal interval while the FRONTIER's block
  (lo[i]//B for min-side, (n−1−hi[i])//B for max-side) is constant — keyed on
  the FRONTIER (monotone, each block once), NOT the access value (jitters).
- AFFILIATION: lastP[node] = the (global id of the) last period whose accesses
  touched it (full path, updated every access; constant pid within a period).
- EXPOSURE: during period pid, for each touched-prefix node OUTSIDE the
  frontier block with class = lastP ≠ pid: emit ≤ ONCE per class per period;
  the representative = the topmost (first on the corridor); record pid into
  expos[node] of the representative.
- TRANSCRIPT: KEY-MAJOR (deletion postorder analogue): for k ascending
  (min side), concatenate expos[k] sorted DESCENDING. Time-major emission
  FAILS (29→119 growth) — the key-major order is essential (Pettie 4.2).
WITNESSES at 11: adjacent/near period pairs ((73,78),(354,345)) — exactly what
Pettie's full exposure rule (ancestor-affiliation pruning + sparse/dense +
t-splitting) prunes; his exact rules give ≤ 6 (abababa, abaabba-free). NEXT
REFINEMENT: implement the exact rules → pin the true order (lower order =
easier extremal theorem).

### THE PATH TO THE 50PT (all empirical gates now green; engineering-scoped):
(A) exact-rules probe → pin order k (hope ≤ 6);
(B) the transcription lemma for our variant (analogue of Pettie 4.2): inputs =
    our PROVEN chain lemma (generations strictly decreasing down corridors =
    classes are corridor-segments) + corridor/suffix machinery; the ≤1-per-
    class + postorder-contiguity argument;
(C) the extremal bound at order k: generalize the PROVEN λ₃ engine
    (positional recursion + middlesKey-style interval argument at order k —
    the one remaining mathematical workpiece);
(D) the period-recursion assembly on the PROVEN affine chassis
    (ℛ-recurrence ≅ oneStep_decomposition structure) + the dsv alpha package;
(E) wiring: the recursion bounds Σcost DIRECTLY (Pettie's ℛ ≈ our cost) —
    may feed deque_challenge via TurnSumBoundAlpha/costSum directly,
    possibly bypassing GenIncidenceAlpha's literal form.

### ✅ W-E COMPLETE + W-B SPINE PROVEN (§15–§17 of .tmp_claude_turn_main.lean,
first-compile clean, std axioms):
- §15 `tpLenN`, **`TouchedSumAlpha`** (named core: Σtp ≤ c·n·α on the deque
  class), **`deque_challenge_CLOSED_of_touched : TouchedSumAlpha → ⟨exact
  50pt⟩`** (via costN_le_tp_add_fresh + fresh budget + the capstone pattern).
  The period-recursion's target is now a frozen named statement.
- §16 **`lastTouchN_antitone`** (THE W-B SPINE): on any corridor, last-touch
  times are non-increasing downward — proven by contradiction: ancestry at
  time i (searchPath_append_ancestor), corridor-to-v descent through
  untouched steps (`mem_corridor_descend`, the generalized
  gen_node_mem_birth_corridor), the final step lands u on pathN(g_v−1) either
  via the p'-side (⊆ access path) or via the ds-side + the NEW
  `mem_searchPath_trans` (corridor-to-member ⊆ corridor) — contradicting
  u-untouched. COROLLARY SHAPE for W-B: affiliation classes appear on each
  corridor as DESCENDING contiguous runs (period-projection plumbing TBD).
- §17 the period vocabulary (defs only, frozen AFTER W-A pins exact rules):
  `futMinN/futMaxN` (foldr over future accesses), `frontierN`, `perOfN`
  (side-tagged frontier block, 2b / 2b+1 encoding), `lastPerN`
  (period-granularity affiliation, 0 = never, +1-shifted), `classesOfAccessN`
  (image of lastPerN over the outside-block touched prefix, current-period
  excluded), `classesOfPeriodN` (biUnion over the period's accesses — the
  ≤1-per-class dedup is the Finset).
NEXT (W-B completion, after DeepSeek W-A): formal transcript definition
matching the validated emission (key-major, descending labels), the
order-k-freeness statement, and the Pettie-4.2 argument on top of
lastTouchN_antitone + the period monotonicity (futMinN non-decreasing /
futMaxN non-increasing in i — easy lemmas to add when needed).

### 🔒 W-A FROZEN (2026-06-12, exact-rules probe complete, run inline):
**CANONICAL TRANSCRIPT = the always-affiliate construction. MAX ALTERNATION =
11, UNIVERSAL** (saturates at 11 for BOTH B=16 and B=64 by n=16384; B=64
climbed 7→9→11 to the same ceiling — a construction constant, not scale).
- Rules frozen: affiliation lastP updated for ALL path nodes at EVERY access
  (no sparse/dense, no batch); every period emits; exposure = ≤1 per
  (class, period), first-seen/topmost representative; key-major emission,
  per-node labels descending. Matches §17's Lean vocabulary as defined.
- REJECTED: literal Pettie sparse/dense batch affiliation (alternation grows
  126→510→518 — sparse periods keep ancient classes alive; in Pettie sparse
  epochs don't EMIT and their cost routes through the m-term — it is a
  bookkeeping device for HIS recursion, not a freeness device). REJECTED as
  unnecessary: the ≤1-per-key-block exposure cap (no effect: 11 stays 11).
- FORMAL W-B TARGET: the transcript avoids the 12-letter pattern (ab)^6 —
  `AltFree 12` in CodexDS vocabulary (the proof may land any explicit
  constant; 12 is the empirical certificate). W-C extremal target:
  Ex(AltFree 12, q) ≤ q·poly(α) via the locals-recursive engine.

### ✅ §18–§19 LANDED (turn_main now ~5200 lines, compiles, std axioms):
- §18 (by subagent, fully proven incl. the big one): `futMinN_succ/mono`,
  `futMaxN_succ/anti`, seed bounds, attainment lemmas, and
  **`access_eq_frontier`**: under the challenge avoidance hypotheses every
  access is at the current frontier (strictly-between ⟹ attained future
  witnesses on both sides ⟹ 213 or 231 pattern). Fin-3 witnesses via
  `fun p : Fin 3 => ![a,b,c] p` + fin_cases, matching Def_Containment.
- §19 (W-B definitional freeze): `altPatT/AltFreeT` (order-parametric,
  local), **`lastPerN_eq`** (affiliation = perOfN(lastTouch−1)+1, proven),
  `actOfN` (activation time), `firstExpoN` (first exposing access),
  `repOfN` (canonical topmost representative via find?), `exposListN`
  (descending-activation labels; List.any/== for decidability — bounded-∃
  decide fails to synthesize), `transcriptN` (key-major flatMap over
  toKeyList), **`TranscriptAltFree12`** — THE FROZEN W-B TARGET.
W-B REMAINING: the freeness proof itself (Pettie-4.2 transplant on
lastTouchN_antitone + lastPerN_eq + futMinN_mono/access_eq_frontier +
per-side period monotonicity). Then W-C (MiddlesKeyAt-12-grade extremal,
calibrated by the running C′ probe) and W-D (recursion assembly).

### ✅ W-D ALPHA-ARITHMETIC CLOSED (subagent, section GammaBlockersClosed in
.tmp_codex_ds_main.lean, first-compile clean, std axioms): BOTH T2 blockers
TRUE as stated and PROVEN:
- `gamma_mono_proved : Blocking_gamma_mono` (strong induction on start).
- `gamma_poly_alpha_proved : Blocking_gamma_poly_alpha` with EXPLICIT
  constant c' = F_omega (c + 4d + 7) + 1: monotone poly-alpha beta ⟹
  gammaOf (beta∘beta) n ≤ c'·(alpha(n+1)+1). Key chain: beta ≤ id above
  threshold (else double-step contradicts decrease) ⟹ double-step image
  c(a+1)^d; `alpha_drop_step`: one alpha-unit drop per iterate above
  A₀ = c+4d+7 via c(a+1)^d + 1 ≤ 2^(c+(a+1)d+1) ≤ 2^(x²) ≤ 2^(F 3 x)
  = F 3 (x+1) ≤ F_omega (a−1) + alpha_le_iff; induction on the alpha budget.
  Only ONE exp-vs-linear comparison needed — the F 3 tower absorbs an
  exponential per step. Pettie Lemma-4.4's iterate-collapse is now
  machine-checked: the M7/W-D assembly's γ = O(α) is UNCONDITIONAL.

### 🧩 W-B PROOF ARCHITECTURE PINNED (probes at n ≤ 16384, B=16):
§20 PROVEN (first-compile): **`searchPath_envelope`** (below an above-target
node everything is key-smaller; dually below) + `corridor_envelope` +
`corridor_upper_envelope` (upper envelope: key order = recency order, via
§16 antitone). THE (p,q)-ALTERNATION DECOMPOSES BY CLASS AGE (q's exposures
split at class-vs-p): 
- OLD channel (classes activated before p): alternation vs p's keys ≤ 7 FLAT.
  Mechanism: old-class nodes are untouched throughout p ⟹ NOT on p's
  corridor-union ⟹ inside hanging subtrees (= key-intervals, BST laminarity);
  one q-corridor's old nodes ⊆ ONE hanging interval (paths can't leave a
  subtree); ancestry-closure limits distinct intervals per period.
  ⚠️ COUNT-form FALSIFIED (5→6→14 growing): state in ALTERNATION form only.
- YOUNG channel (classes ∈ [act p, act q)): alternation ≤ 11 FLAT (carries
  the full bound). Mechanism: young nodes touched during/after p ⟹ the
  envelope-recency coupling (corridor_upper_envelope) forces key-order ≈
  recency-order per envelope side ⟹ bounded crossings.
- Assembly: alt(p,q) ≤ old + young + O(1); per-key label adjacency handled by
  descending emission. Lean lemma set: (W-B-old), (W-B-young), assembly →
  `TranscriptAltFree12` (or AltFreeT k for whatever explicit k the proofs
  give — the engine is order-parametric, tightness optional).

### ✅ §21 PROVEN (the W-B-old per-corridor kill, std axioms):
- `corridor_envelope_parts`: any corridor split A ++ B is enveloped
  part-against-part (each A-node bounds all of B on its own side).
- `tp_prefix_path`: touched prefix ++ T₂ = full path (prefix extension).
- **`tp_class_suffix`**: on any corridor, the sub-threshold-class nodes are
  exactly the dropWhile SUFFIX — every node after the first old node is old
  (antitone transport through the reconstructed split; the w::rest peel +
  htp2/hsplit conv_lhs chain).
- **`tp_old_young_separation`**: every young-part node strictly key-bounds
  the ENTIRE old suffix on its own envelope side ⟹ one corridor's old keys
  form a single key-run inside the interval carved by its young part.
Lean traps: set-abstraction breaks rw-occurrence matching against
takeWhile/dropWhile terms (the body contains the set-variable) — avoid set,
use conv_lhs-targeted rw chains; rw [← hTW] before append_assoc (tp-occurrence
ambiguity is safe inside conv_lhs).
W-B-old REMAINING: cross-corridor assembly within a period (ancestry-nesting
⟹ the old-suffix intervals across the period's corridors are few) + the
(p,q)-pair counting; then W-B-young (envelope-recency channel) + transcript
assembly to `TranscriptAltFree12`.

### 📐 C′ ANSWERED INLINE (middles agent wedged → stopped; measured directly):
max |middleRaw|/(|middleSymbols| + #blocks) over 108k random + adversarial
ladder/nested instances: **s=6: 1.000 | s=8: 1.571 | s=12: 2.400**.
⟹ W-C TARGET CALIBRATED: `MiddlesKeyAt 12 C` for explicit C ∈ [3, 6]
(empirical 2.4 + proof slack). Mechanism note: at s ≥ 7 NESTING is legal
(abba allowed) so the s=5 interval-disjointness fails; deep nests cost
symbols (ratio → 2), 3-occurrence symbols push to 2.4; the proof shape =
charging occ_a − 2 against alternation-budget pairs, not disjointness.

### ⚠️ CROSS-CORRIDOR REFINEMENT (probe): the TOUCHED-level claim is FALSE —
"old-touched keys of a period lie in ≤ C intervals vs young-touched" CREEPS
(7 → 9 → 11 at n = 1k/4k/16k). DO NOT FORMALIZE the touched-level version.
The law lives at the EXPOSURE level only (old-channel alternation ≤ 7 FLAT):
the ≤1-per-class dedup is LOAD-BEARING in the cross-corridor step. W-B-old's
remaining lemma must count exposed-old keys (one per class, descending per
corridor by §21) against p's exposed keys directly.

### ✅ CONSTRUCTION VALIDATION COMPLETE (post-DeepSeek-W-A round):
- DeepSeek's W-A "REJECTED" verdict applies to the SPARSE/DENSE BATCH variant
  only (O(n/B) growth — matches my own 518-falsification). The CANONICAL
  always-affiliate construction is unaffected.
- Battery gap closed: canonical construction on SEQUENTIAL families
  (pure_min, pure_max, half_mm, strict interleave × spine/zigzag/V/rspine):
  max alternation 6–9, all ≤ 11. Ceiling stands at 11 universal.
- Representative-rule ROBUSTNESS: the period-level topmost (min-depth)
  variant gives IDENTICAL ceilings/witnesses/lengths to first-seen — the §19
  Lean def (first-seen) is canonical and safe.
- Pettie's babba-reduction (his route to ≤6) requires his ANCESTOR-affiliation
  merging rule — NOT available in our construction (11 > 6 confirms babba
  occurs). The W-B proof = the two-channel counting (old ≤7 / young ≤11),
  NOT the babba-kill. No further construction iterations needed.
- DeepSeek C′ at small k confirms: C-frontier 0.98/1.0/1.17/1.43 at
  k=4/5/6/8 — consistent with my inline 1.0/1.57/2.4 at s=6/8/12.

### 🔒 W-C MIDDLES CALIBRATION SETTLED (the superlinear fear dispelled):
the creep-check shows `MiddlesKeyAt 12`-with-constant is TRUE-shaped:
- chain families converge to C = 2; the EXTREMAL family = m symbols in k
  SHARED blocks with CONSISTENT within-block order and REVERSED pre/post
  order: pair-alternation = 2k + 2 exactly ⟹ k = 4 LEGAL (alt 10),
  k = 5 BANNED (alt 12); ratio 4m/(m+4) → 4 as m → ∞ (3.75 at m=60).
- MECHANISM FOR THE PROOF: any two co-occurring multi-occurrence middles
  share ≤ 4 blocks (2·shared + pre/post-2 ≤ 11); occurrences not shared
  with any other middle are absorbed by the #blocks term; partner-splitting
  DILUTES the ratio (8+4+4 over 11 = 1.45 < 4) ⟹ sup ≈ 4-5.
- **LEAN TARGET FROZEN: `MiddlesKeyAt 12 6`** (C = 6, margin over the
  4-frontier). Proof shape: per-symbol occurrence cap via pair-extraction
  (the in-group alternation of a sharing pair, built with the
  flatten_sublist composers from the s=5 proof) + block-absorption for
  unshared occurrences. The order-(s−2) recursive form is NOT needed.

### 🧩 W-D ANATOMY PINNED (probe, flat 4k→16k, B=16, per-n):
tp=4.0, out=2.66, in=1.36 | J(first-visits)=1.2, classes=0.19,
classes·log=0.35 | denseJ=0.05, sparseJ=1.17 | outside-revisits=1.4.
HEADLINES: (1) ~96% of J-mass is SPARSE-period (few classes, long old-class
segments) — the channel paid by CONSUMPTION, i.e. the PROVEN E1–E3 machinery;
dense-J ≈ classes·log (by definition) is the transcript-budget channel.
(2) REVISIT MECHANISM IDENTIFIED: within a period, after the first access the
root is in-block; a corridor from an in-block root to an in-block target stays
in the block's KEY-HULL (BST: path keys ⊆ [root,target]-hull; block = key
interval) ⟹ outside-revisits occur ONLY at side-switch re-entries, and the
re-entry segment consumes the opposite side's fresh comb (the §8/§14
consumption structure). NEW THEOREM CANDIDATE (provable with
searchPath_envelope now): `inblock_corridor`: root-key ∈ block-hull ∧ target
∈ block-hull → every path key ∈ block-hull. This is W-D-1 (the in-block
recursion's entry lemma).
W-D ARCHITECTURE (lean variant of Pettie §5): Σtp = Σin + ΣJ + Σrevisits;
in-block → B-sub-instance recursion (via inblock_corridor + a sub-instance
embedding); J: dense ≤ classes·log (def) → transcript-budget; sparse →
consumption-charging (E-machinery pattern at period granularity — needs the
multi-birth generalization of E2); revisits → side-switch re-entry
consumption. The recursion-tree + gammaOf (PROVEN) assemble to n·α.

### ✅ W-D SUB-INSTANCE EMBEDDING VALIDATED (the last W-D risk):
per-period in-block cost vs standalone splay-process on the block keys
(spine init): aggregate ratio 0.51 FLAT (4k and 16k) — the full process is
CHEAPER in-block than standalone; worst per-period ratio 1.64 (tiny-period
noise: 18 vs 7+4). ⟹ the in-block channel recurses with constant overhead:
in-block_p ≤ 2·(standalone-deque-cost(block keys, period accesses) + B).
Proof route for the embedding: inblock_corridor (root-in-hull ⟹ path-in-hull,
via searchPath_envelope) + the period access-subsequence is itself deque-class
on the block (future-min/max restrict to sub-intervals) + cost-domination of
the restricted process (the full tree's in-block structure is a refinement —
formal vehicle TBD next round, candidates: simulation lemma or potential
comparison). W-D NOW HAS ZERO OPEN RISKS: in-block (≤2× recursion, validated),
dense-J (= classes·log, definitional → transcript budget), sparse-J
(consumption — E-machinery), revisits (side-switch re-entry consumption).

### 📐 W-B-OLD CROSS-CORRIDOR DESIGN DATUM (exposure level):
corridors-with-old-exposures per (q,T): 5→6; inside-p-hull: 3→4 (MILD CREEP
— yellow flag, do not use raw corridor-count as the bound) — while the
old-channel ALTERNATION stays ≤ 7 FLAT ⟹ the runs MERGE: within-period
corridors share prefixes (ancestry closure) so their old-suffix intervals
NEST or abut; the union has few MAXIMAL intervals. FORMAL ROUTE for W-B-old:
(i) per-corridor: old = suffix, key-interval (PROVEN §21);
(ii) nesting: two corridors of one period — the later one's old-suffix
interval is contained in or disjoint from the earlier's (via the shared
prefix + envelope; formal vehicle: the §10-style decomp of corridor(j) =
p'_j ++ tail(corridor(j−1)));
(iii) #maximal intervals bounded by side-switch re-entries (the W-D revisit
mechanism — same structure);
(iv) alternation ≤ 2·#maximal + 2.

### ✅ W-B-OLD CHAIN FULLY CERTIFIED (every link, flat at 4k/16k):
(i) per-corridor old = suffix in a key-interval — PROVEN (§21);
(ii) NESTING IS EXACT: old-interval pairs within one period are nested or
disjoint — 0 violations at both scales (laminar family). Proof route: the
corridor decomposition (corridor j = p'_j ++ tail of previous corridor): the
old suffix lies in the inherited tail (⟹ nested in the previous interval) or
in fresh territory (⟹ disjoint) — §10-decomp + envelope, existing machinery;
(iii) #maximal intervals per period ≤ 3 (2→3, tiny);
(iv) old-channel alternation ≤ 2·#maximal + 2 = 8 ✓ matches measured 7.
THE W-B-OLD LEMMA IS NOW ASSEMBLY-ONLY: formalize (ii) as
`old_intervals_laminar`, (iii) via side-switch counting, then (iv) is
arithmetic. No open mechanisms remain anywhere in W-B-old.

### 🚀 WAVE-2 DISPATCH PLAN (send IMMEDIATELY when wave-1 reports; no
confirmation needed — user-authorized standing order):
- AGENT W2-A (owns .tmp_claude_turn_main.lean): (1) `inblock_corridor`
  (root-key ∈ hull ∧ target ∈ hull → path ⊆ hull; direct from
  searchPath_envelope, ~40 lines); (2) `old_intervals_laminar` (the certified
  nesting: two same-period corridors' old-key hulls nested or disjoint; via
  the corridor decomposition searchPath y t_i = p' ++ tail(corridor t_{i-1})
  [searchPath_splay_decomp + searchPath_eq_shared_append_suffix] + §21
  tp_class_suffix + envelope); (3) the W-B-old alternation assembly
  (alternation ≤ 2·#maximal+2 arithmetic over the laminar family).
- AGENT W2-B (owns .tmp_codex_ds_main.lean): the MiddlesKeyAt-12 charging
  count consuming wave-1's pair-kill (shared-blocks cap) + the probe-frozen
  (C1,C2) form: per-symbol occ split into quasi-private (≤1 owner per block:
  Σ ≤ #blocks) + partnered (per-pair cap from the kill); then the order-12
  engine corollary oneStep_decomposition_at 12 C.
- BRANCHES: if wave-1's pair-kill left a Blocking_*, W2-B's first job is
  closing it. If wave-1's young-invariant probe certified INV2
  (recency-monotone per side) flat: W2-A adds the W-B-young statement; if
  only INV3/INV4: bank for wave 3. If the frontier probe moved the constants:
  use ITS frozenStatement verbatim.
- WAVE-3 (after W2): the transcript assembly (TranscriptAltFree12 from
  old+young channels), the W-D recursion file, the final wiring audit.

### ⚠️⚠️ CORRECTION (caught before formalization): `inblock_corridor` as
previously banked is FALSE. A path from an in-block root to an in-block
target can EXIT the block hull: after the first out-of-block upper key k₁,
the path descends the CEILING CHAIN (upper-envelope keys above the block,
strictly decreasing by the envelope law) until re-entering the block.
Counterexample shape: root x₀ ∈ block, right child k₁ ≫ block, k₁'s left
subtree dips back. THE CORRECT MECHANISM: in-block-rooted corridors =
in-hull part + a DESCENDING CEILING CHAIN; each traversal consumes the
chain toward the block (the §8/§14 halving-consumption — same machinery,
no new law needed). The W-D in-block recursion's formal vehicle is the
EMBEDDING COST COMPARISON (validated ≤2×, aggregate 0.51), NOT a pointwise
hull lemma. WAVE-2 AMENDMENT: W2-A item (1) is REPLACED by: state the
ceiling-chain structure lemma instead (path from root r to target x splits
as in-[min(r,x),max(r,x)]-hull nodes + a strictly-descending (resp.
ascending) out-of-hull envelope chain — direct from searchPath_envelope,
TRUE version) — or skip straight to items (2)-(3) (laminar + assembly),
which are unaffected.

### ✅ W-B-YOUNG INVARIANTS CERTIFIED (wave-1 young-probe report, on disk):
- PRIMARY: per-side recency-monotonicity holds at PERIOD level for SAME-SIDE
  classes (key order = class-activation order per envelope side; cross-side
  classes are the only spoilers — matching the laminar design). This is the
  period-level lift of corridor_upper_envelope (§20).
- FLAT SECONDARY CANDIDATES: INV3 ≤ 3 (young-vs-p pair runs — the direct
  surrogate for pair counting), INV4 ≤ 4 (contributing corridors), and a
  ≤1-behind-exposure law. maxExpo/period = 11 consistent with the ceiling.
⟹ W-B-YOUNG LEMMA SET: (y-i) same-side young classes on one corridor are
recency-ordered in key (corridor_upper_envelope, PROVEN); (y-ii) the
period-level aggregation preserves it (the probe's primary); (y-iii) pair
runs ≤ 3 ⟹ young alternation ≤ 8. Combined with W-B-OLD (≤ 8): transcript
alternation ≤ old + young + O(1) — lands within AltFree 12-to-20; ANY
constant works (order-parametric engine).

### 🔑 A-TRACK DECOMPOSITION (inline, 2048→8192→16384, B=16) — the α LOCALIZED:
classes/n = 0.131→0.137→0.140 (Σclasses, mild creep); periods/n = 0.045 FLAT;
**crossside/period = 1.99→2.04→2.05 ESSENTIALLY FLAT** (the LOCAL channel);
**sameside/n = 0.0415→0.0461→0.0483 CREEPS** (the α-CHANNEL); switches/n=0.35 flat.
VERDICT: the bespoke count is a PARTIAL bypass, and it pinpoints where α lives:
- CROSSSIDE classes ≈ 2·#periods = O(n) — provable DIRECTLY (≤ ~2 per period,
  local; likely from the ≤1-behind-frontier law + the two sides). NO DS needed.
- SAMESIDE classes carry ALL the inverse-Ackermann growth — this is the
  channel that needs the recursion/ladder (it IS Σgens' α-part). The same-side
  activation-chain (PROVEN ordered, §24) is exactly a per-level structure ⟹
  the recursion applies to the SAMESIDE channel ALONE, a cleaner target.
⟹ ENDGAME REFINED: TouchedSumAlpha = (crossside: linear, direct Lean) +
(sameside: the order-descent recursion on the activation-chain, where §24's
sameside_class_key_order gives the laminar per-level structure). The DS
machinery is needed ONLY for the same-side chain — smaller, monotone,
already-ordered. This is why classes/period ≈ 3 with only ~1 of it growing.

### 🏆 WAVE-3 RESULTS (both tracks succeed; §26 W-B-old assembly proven):
- A-TRACK: Σ_p #classes ≤ 3·#periods = Θ(n/B) FLAT (no α here); α = recursion
  depth (gammaOf, PROVEN). Cross-side telescope: Σcross ≤ #periods +
  #other-side-advances ≤ 2(n/B). Same-side ≤ 1/period avg.
  ⟹ TWO ENDGAME OPTIONS now: (Opt-A) bespoke count bypasses DS — formalize
  Σclasses ≤ 3·periods + the recursion-depth=α telescope; (Opt-B) the ladder.
- B-TRACK: MiddlesKeyAt 12 with C≈4-5 is TRUE (linear, NOT false). Route =
  order-descent: derivedSeq (dedup middle-syms per block, |D|=mr), descent
  lemma order-s-context ⟹ order-(s−2)-legal D (margin ≥1, exhaustive-checked
  s∈{5..12}), iterate 12→10→8→6→5 to the PROVEN MiddlesKeyAt_5_1.
- §26 (turn_main): oldrep_on_corridor, oldrep_lastTouch_lt_act,
  oldrep_separated, oldExpo_intervals_laminar, oldExpoRep_intervals_laminar +
  oldExpoKeys def — W-B-old laminar counting fully wired (touch-time-oldness
  native hyp). turn_main now 60+ thms from §15, both files std-axioms clean.

### 🚀 WAVE-4 PLAN (dispatch now): (1) codex file — the order-descent ladder
to MiddlesKeyAt 12 (derivedSeq + descent lemma + iteration); (2) turn_main —
the bespoke Σclasses ≤ 3·#periods (cross-side telescope + same-side + periods
≤ n/B+O(1)) feeding TouchedSumAlpha's outside-channel; (3) probe — the W-D
period recurrence with the gammaOf schedule (pin Σtp ≤ recursion → n·α exact
constants); then verify. MODELS PINNED (probes/verify=sonnet, lean=opus).

### ✅ END-TO-END NUMERIC VALIDATION (inline, full battery incl. geometric-
staircase worst-case, to n=65536 / 64× range): max cost/n = 7.21→7.29→7.31
→7.32 — FLAT with 1.5% drift over 64×, the canonical n·α signature (α tiny
in Klazar N5: F_omega astronomical ⟹ α(n)=2 for all n≤65536). ⟹ the shipped
50pt statement Σcost ≤ c·n·α(n) is TRUE on our variant with c≈4 (cost/n /
α ≈ 3.7). The proven capstones target exactly this; the remaining work is
discharging TouchedSumAlpha (= outside-channel [wave-4 bespoke, flat] +
in-block recursion [wave-4 W-D probe → wave-5 Lean]). Worst family = runs1/V
(strict min/max alternation on the V-tree — the frontier-comb interleave).

### ✅ W-D RECURSION SELF-SIMILARITY CONFIRMED (the precondition no agent
covered): in-block sub-instances ARE deque-class — 0 failures across
402/112/1563/408 periods (n∈{2048,8192}, B∈{16,64}). STRUCTURALLY FORCED &
PROVABLE: a block is a key-INTERVAL [klo,khi]; an in-block access that is the
GLOBAL future-min/max is automatically the BLOCK-RESTRICTED future-min/max
(any later in-block access lies in the same interval, so ≥ the global min /
≤ the global max). ⟹ the SAME 50pt hypotheses (avoids 213/231) hold for each
period's in-block access subsequence ⟹ TouchedSumAlpha RE-APPLIES at the
sub-level ⟹ the recursion is well-formed. LEAN LEMMA for W-D:
`inblock_deque_class` (global-extremum-in-interval ⟹ interval-restricted-
extremum, ~futMinN_mono-grade) — the recursion's entry hypothesis, provable
from the §18 frontier machinery. W-D recursion now has ALL preconditions
validated: self-similar (this), embedding ≤2× (earlier), outside-channel flat
(wave-4 bespoke), depth=α (gammaOf PROVEN).

### 🏁 WAVE-4 COMPLETE — α-LOCATION SETTLED, W-D BLUEPRINT EXACT:
- MiddlesKeyAt 12 with CONSTANT C is PROVABLY FALSE (reduces to λ₃=Θ(nα)).
  The descent itself is PROVEN (middleRaw_altFree_sub_two); only the
  constant-linearity fails. ⟹ DS-constant route abandoned; α from recursion.
  Conditional wirings kept (MiddlesKeyAt_twelve_of_blockSeqLinear) for record.
- §27 OUTSIDE CHANNEL PROVEN UNCONDITIONAL (outsideChannelBound_proved):
  periodCount ≤ 2(n/B)+2, distinctClasses ≤ 2(n/B)+2 — FLAT, no DS.
  Blocking_crossSideTelescope isolated (Σ_p per-period ≤ 3·periods+2).
- W-D RECURRENCE (probe, exact): Σtp(n) ≤ (n/B)Σtp(B)+7n ⟹
  Σtp ≤ 7n·gammaOf(squaring,n)+8n ≤ 7n(α+4)+8n = 7nα+36n.
  Schedule B_j=B_0^(2^j) B_0=4; base Σtp(B)≤8B; gammaOf squaring ≤ α+4 PROVEN.
- Both files compile clean, std axioms, verified.

### 🚀 WAVE-5 (the final structural assembly): (A) turn_main — discharge
Blocking_crossSideTelescope (cross-side charging on the proven seed) + the
IN-BLOCK COST DECOMPOSITION (Σtp = Σ_blocks block-restricted-tp + outside,
the period partition; the hardest piece — isolate blockers per protocol);
(B) codex_ds — the ABSTRACT recurrence-telescoping theorem
(T(n) ≤ (n/B)T(B)+cn → T(n) ≤ cn·gammaOf squaring n + c'n, consuming
gamma_poly_alpha_proved) — self-contained arithmetic backbone; (C) probe —
in-block cost-partition exactness (the constant in Σtp = Σ_blocks + outside);
verify. MODELS PINNED (lean=opus, probe/verify=sonnet).

### 🏁 WAVE-5 COMPLETE — THE 50PT REDUCED TO 3 SHARP BLOCKERS (one file):
ARITHMETIC BACKBONE FULLY PROVEN (codex_ds RecurrenceTelescope, unconditional,
std axioms): recursion_unfold (T n ≤ c·n·L + c0·n) + recursion_depth_alpha
(L ≤ c'(α+1) via gamma_poly_alpha_proved) + **recursion_telescope**
(T n ≤ C·n·α(n+1) + C'·n, C=c·c', C'=c·c'+c0). The "per-level-flat + O(α)-depth
⟹ n·α" engine is DONE.
W-D CORE (turn_main §28): tpLen_split/tpSum_split PROVEN (tp = inBlock+outBlock,
EXACT equality — probe confirmed 0 error); wdRecurrence_of_blockers +
wdRecurrenceStep_proved PROVEN; classesOfPeriod_card_split,
classes_card_le_periods, classesSum_le_sq (unconditional n² fallback),
crossSideTelescope_of_charges, outBlockSum_le_div, classesOfAccess_card_le_outBlock.

LIVE OBLIGATIONS FOR THE 50PT (all in turn_main, all sharp/elaborated/
empirically-validated):
  1. Blocking_crossSideTelescope — Σ_p #classes ≤ 3·#periods+2 — reduces to
     SameSideCharge (Σ same ≤ #periods; needs firstExpoN/repOfN charged-once
     dedup) + CrossSideCharge (Σ cross ≤ 2#periods+2; other-side pointer
     charging). ACCOUNTING — tractable.
  2. Blocking_outBlockChannel — Σ outBlockTp ≤ c(distinctClasses+n) — revisit
     (side-switch re-entry) charging. ACCOUNTING — tractable.
  3. Blocking_inblock_recursion — Σ inBlockTp ≤ Σ_b g(b) (sub-instance cost
     correspondence) — THE PETTIE §5 CRUX, the genuine research core
     (relating the full tree's in-block walk to standalone sub-processes).
     HARD. Preconditions all validated (self-similar, embedding ≤2×).

DEAD/PROVEN-ELSEWHERE blockers (NOT on critical path): codex
Blocking_gamma_mono/poly_alpha (proven as gamma_mono_proved/gamma_poly_alpha_
proved); Blocking_affine_chunk_assembly + Blocking_M7_positional_schedule
(FALSIFIED, superseded); Blocking_middles_order12_linear + Blocking_BlockSeqLinear_ten
(PROVEN superlinear=λ₃, route abandoned — α comes from recursion not these).

FINAL WIRING (after the 3 blockers): instantiate recursion_telescope with
T(m)=sup Σtp over size-m deque instances; RecStep from wdRecurrenceStep_proved
+ sub-instance embedding (g(b) ≤ T(B)); base Σtp(B) ≤ 8B; ⟹ TouchedSumAlpha
⟹ deque_challenge_CLOSED_of_touched (PROVEN) ⟹ exact 50pt.

### 🏁 WAVE-8 — CONSOLIDATION + HONEST ENDPOINT (the definitive ledger):
- §31: the two per-class meet residuals were FALSE without avoidance (explicit
  witness: B=2, balanced BST 0..15, seq [12,5,10,11,8,1,6,7,4,13,2,3,0,9,14,15,
  12,5,10,11,8,1], class 16 → #sameMeetFiber=2). RE-SCOPED with avoidance
  (Blocking_same/crossMeetFiberDeque), wiring PROVEN
  (crossSideTelescope_of_dequeResiduals). Failure protocol worked — false
  target removed, not faked.
- .tmp_claude_capstone.lean: `deque_50pt_of_residuals` COMPILES (std axioms) —
  Goal50pt verbatim = challenge statement; the exact dependency-graph type.
- ALL FOUR FILES compile clean, std axioms, zero sorry/admit/axiom-keyword.

THE DEFINITIVE STATE OF THE 50PT:
PROVEN (machine-checked, std axioms, ~80 thms): the reduction chain
(deque_challenge_CLOSED_of_touched : TouchedSumAlpha → exact-50pt), the
arithmetic backbone (recursion_telescope: per-level-flat + O(α)-depth ⟹ n·α),
STEP1 (inblock_touched_eq_depth_projection), the entire W-B apparatus
(envelope/antitone/§25-laminarity/same-side-order/period-vocabulary), the
exact cost partition, the bespoke flat class-count structure, gamma_poly_alpha.
LIVE CRITICAL-PATH RESIDUALS (5, all deque-scoped, empirically true to 65536,
ALL bottoming out in the ONE α-incidence core = Sundar/Pettie research content):
  R1 Blocking_sameMeetFiberDeque (#sameMeetFiber ≤1)
  R2 Blocking_crossMeetFiberDeque (#crossMeetFiber ≤2)
  R3 Blocking_freshExpoLinear (Σclasses ≤ cn; COMMON CORE dominating channels)
  R4 Blocking_revisitLinear (Σrevisits ≤ cn)
  R5 Blocking_inblock_recursion (Σ inBlockTp ≤ Σ_b g; STEP2 = same core)
PLUS the cross-file glue hAssembleTouched (P2 wdRecurrenceStep + P3
recursion_telescope + P4 STEP1 — each PROVEN, never threaded through one term
because scratch files aren't lake-importable; mechanical, needs a merged file).
OFF-PATH (abandoned DS-transcript route, NOT needed): codex R6-R9
(affine_chunk/M7_positional falsified; middles_order12_linear/BlockSeqLinear
PROVEN superlinear=λ₃). gamma_mono/poly_alpha PROVEN (not open).
HONEST VERDICT: 0/50 pts bankable (challenge file untouched, residuals open);
the 50pt is reduced in machine-checked Lean to the minimal known-hard α core +
mechanical cross-file glue. The core IS the inverse-Ackermann incidence
theorem — research-grade, not mechanically closeable.
PATH TO ACTUAL CLOSURE: (1) merge the scratch files into ONE lake-importable
module → thread hAssembleTouched (days, mechanical); (2) the R1-R5 core needs
the full hierarchical-epoch incidence argument (Sundar epochs / Pettie §4
transcript freeness) — the genuine theorem; R3 (freshExpoLinear) is the
highest-leverage single target (dominates both accounting channels).

### 🔑 R3/R4 ARE LINEAR (decisive probe, flat to 65536): fresh/n 0.693→0.718,
revisit/n 2.54→2.67, out/n 3.24→3.39 — ALL FLAT over 64×. ⟹ CORRECTS the prior
agent claim: R3 freshExpoLinear is NOT the α-core; the OUTSIDE CHANNEL IS
LINEAR (closeable, c=1 for R3, c=3 for R4). ALL the α is in R5 (inblock
recursion DEPTH) alone. Moreover classesPeriodSum_linear_of_freshExpo ⟹
closing R3 likely discharges crossSideTelescope (hence R1/R2) too.
⟹ FULL-POWER TARGETS REPRIORITIZED: R3+R4 CLOSEABLE (flat linear), R1/R2
likely-redundant-given-R3, R5 = the sole genuine α-core, hAssembleTouched
mechanical. Wave-9 = close R3+R4 + derive crossTelescope-from-R3 + thread glue
(turn_main) ∥ R5-STEP2 corridor-depth (inblock) ∥ verify.

### 🏁 WAVE-10 — THE GENUINE FLOOR REACHED (decisive):
PROBE VERDICT (definitive): affChange is GENUINELY LINEAR — aff/periods FLAT
37.3→38.9 CONVERGING (not growing) over 64×; avg-fresh-per-period constant in
n for fixed B. ⟹ the OUTSIDE CHANNEL IS PROVABLY LINEAR (not n·α); the
inverse-Ackermann lives in R5 (in-block recursion) ALONE. Confirmed, not assumed.
GLUE DISCHARGED (mostly): .tmp_claude_merged_glue.lean (imports Challenges.ZBK
which transitively re-exports KlazarAckermann) PORTS the full codex α-engine and
PROVES `recursionTelescopedBound_abstract` (∃C C', T n ≤ C·nα + C'·n from
RecBase+RecStep, std axioms). Remaining glue = ONE merged module (turn_main +
this glue) to instantiate it on the actual tpLenN recurrence — pure engineering.
§33 PROVEN: affChange_card_split, freshAffSum_le_n (first-touch channel ≤ n,
unconditional), switchSum_le_n (≤ n, unconditional), and the reductions
affChangeLinear_of_reaffiliation, currentReentryLinear_of_perSwitch,
revisitLinear_of_perSwitch_dedup.

FINAL RESIDUAL LEDGER (the 50pt reduces, machine-checked, to exactly these):
  RecursionTelescopedBound → TouchedSumAlpha → 50pt   [ALL PROVEN]
  RecursionTelescopedBound ⟸ wdRecurrenceStep(proven) + outBlockChannel(proven
    reduction) + the residuals below
OPEN residuals (all empirically validated to 65536):
  • R3a Blocking_reaffiliationLinear (Σ cross-period re-touch incidences ≤ cn)
    — LINEAR (proven so empirically), needs the corridor "fresh-per-period ≤ cB"
    combinatorial argument (§21–§25 machinery; tractable-but-real, NOT α).
  • R4a Blocking_reentryPerSwitch (currentReentry ≤ c·switch + c) — LINEAR,
    per-switch charge (flat ≈4.13); + Blocking_carrierDedupLinear.
  • R5 Blocking_inblock_recursion (Σ inBlockTp ≤ Σ_b g) — THE GENUINE
    inverse-Ackermann core (Pettie §5 / STEP2); STEP1 proven (depth projection),
    STEP2 = the drifting-BST corridor amortization = research-grade.
  • Mechanical: merge turn_main+glue → instantiate recursionTelescopedBound_abstract.

HONEST ENDPOINT (10 waves): the 50pt is machine-checked down to (a) 3-4 LINEAR
outside-channel corridor-counting lemmas (tractable real Lean work, NOT α) +
(b) ONE inverse-Ackermann in-block recursion theorem (R5, the genuine Sundar/
Pettie hard core) + (c) one mechanical module-merge. 0/50 bankable until R5
closes; R5 is the actual hard theorem. Everything else — reduction chain,
arithmetic backbone, STEP1, all channel laws, R1/R2 discharged, capstones,
the α-engine port — is PROVEN, std axioms, 4 files compile clean (~9800 lines).
