# Deque challenge (50pt) + Deque Conjecture (100pt) — formalization architecture

Target: `Challenges/Splay_Tree/Challenge_Splay_Deque.lean` — for X avoiding {213, 231}:
`splay.sequence_cost init X ≤ c · n · α(n)`. Since `one_le_alpha_of_pos` (α ≥ 1), a flat
`c·n` bound suffices — which also closes `Challenge_Splay_DequeConjecture.lean` (same class, c·n).

## The run-decay architecture (validated 2026-06-10)

Empirical status: VALIDATED — residual ≤ +1.0 across families alt/runs4/runs16/rand2/rand3/rand4,
inits spine/random-BST, n = 512..8192 (`/tmp/run_decay3.py`).

**Master recurrence** (per maximal same-side run j):

```
cost(run_j) ≤ ½·cost(prev same-side run) + 6·(len_j + fresh_j) + 2·(maxdepth_live drop) + 1
```

- side of access i: min-side if X i ≤ all future accesses, else max-side
  (the {213,231} characterization — PROVEN in Lean: `deque_future_one_sided`).
- fresh = path nodes never previously on any access path.
- maxdepth_live = max keyDepth over keys in the live interval [lo, hi]
  (lo/hi = running min/max constraints from the one-sided structure; monotone).

**Summation → linear.** Each run is the "prev same-side" of ≤ 1 later run, so
Σ cost ≤ ½ Σ cost + 6(Σlen + Σfresh) + 2·Σ MDdrop + #runs + firsts, giving
Σ cost ≤ 2·[6(n + n) + 2(MD₀ + ΣMDrise) + n + firsts] with
- Σ fresh ≤ n,
- Σ MDdrop ≤ MD₀ + Σ MDrise ≤ n + 2n (deepening lemma: MD rises ≤ 2 per access),
- firsts: first run of each side is all-fresh ⇒ covered by the fresh budget.
Net ≈ 38–42n. Total links ≤ 3.4n observed; the constant is loose but linear.

It is FINE to weaken the formal statement with an extra `+ 2·(opposite gap length)` term
(Σ 2g ≤ 2n keeps linearity) if the induction needs it.

## Lean proof obligations

| # | Obligation | Status |
|---|---|---|
| L1 | **Deepening**: `keyDepth y (splay t q) ≤ keyDepth y t + 2` (∀ y; empir. worst exactly 2) | agents running |
| L2 | **Halving**: `y ∈ searchPath q t → 2·keyDepth y (splay t q) ≤ keyDepth y t + c` (c ≈ 6) | agents running |
| L3 | **Run-decay glue** (research core): derive the master recurrence from L1+L2 | paper sketch below |
| L4 | Epoch summation arithmetic | easy, standard |
| L5 | Characterization: avoiding {213,231} ⇒ future-one-sided, restriction lemmas | ✅ DONE, compiled |
| L6 | cost = search-path-length − 1 bridges (`splay_cost_add_one_eq_search_path_len_of_mem`) | exists from sequential work |

Dev file: `.tmp_claude_deque.lean` (588 lines, compiles, std axioms, 3 Def-imports only):
counting primitives, rel5 both chiralities, 4 interior shape lemmas, hSq2 + 6 exchange
equations (Ω-route fallback assets), characterization layer.

## L3 paper sketch (the glue)

After splaying a min-side x with path P = [p₀..p_d = x], result = node A x B:
- path nodes y ∈ P: new depth ≤ pos(y)/2 + 2 (L2);
- off-path z in a cargo at path position p: depth-within-cargo unchanged, cargo root lands
  at ≈ p/2 + 2, and never deeper than before +2 (L1).

Within a min-run, for consecutive accesses x < x': the path to x' from root x =
stack-prefix through B (halved remnants of P ∩ (x,∞): ≤ ½·prev cost + 2) + a virgin-interior
dive within one cargo block. Virgin interiors are paid by:
- fresh budget (never-touched nodes), or
- the MD-drop credit (touched-but-never-restructured chains, e.g. post-warm-up spine debris).

Between runs: g opposite accesses deepen any of our side's keys by ≤ 2g total (L1);
formally allowed as a `+2g` term.

**⚠️ COUNTEREXAMPLE FOUND (V/W trees, /tmp/v_adversary.py)** to the GLOBAL-MD forms (both
granularities): V-tree (deep left arm at key 0, deep right arm at key n−1) + rand-jump
sequences breaks them with Θ(n) residuals. Anatomy: (i) cost-0 same-side repeats (target at
root) RESET the ½·prev budget while a deep remnant persists; (ii) the global MD witness sits
on the OTHER arm, so the dive's halving earns no credit. FIX (validated? see /tmp/split_stock.py):
**per-side stocks split at the static meeting point m\* := max(min-side access values)** —
min-side accesses ⊆ [0,m*], max-side ⊆ (m*, n]; R_min := max keyDepth over live keys ≤ m*,
R_max mirror. m* is computable from X (the proof has X globally — no online-ness needed).
A dive then always drops its OWN side's stock, immune to repeats and to the other arm.
Master becomes: COST(J) ≤ ½COST(prevSame J) + κ(LEN+FRESH) + κd·(R_side drop over J) + C·LEN.
Summation unchanged (two stocks, each: Σ drops ≤ R₀ + 2n via deepening).

**Open formal risk** in L3 (historical): the MD-drop credit assumes the virgin dive is (close to) the
live max-depth witness; if a deeper untouched live region exists elsewhere the credit is 0
and the dive must be charged to ½prev-same. Confirmed real by the V/W counterexample above;
alternatives tested:
- per-ACCESS recurrence (`/tmp/per_access.py`): cost_i ≤ ½prev-same-access + 6(1+fresh) + 2·MDdrop —
  if it holds, the Lean induction is a simple per-step process induction with two scalars of state;
- ~~fresh2/freshK budget~~ TESTED AND FAILED (`/tmp/run_decay4.py`): K=2 fails on rand3/rand4-spine
  (grows ~n/4); K=3 still fails rand3-spine (29→221 growing). Touch-count budgets cannot capture
  warm-up — spine debris is touched 3+ times while remaining virgin-deep. Do not retry;
  the MD-drop credit is the only validated warm-up payer.

## ⭐ FINAL DESIGN — the per-side remnant LEDGER (2026-06-10, /tmp/ledger_test.py: ZERO violations everywhere)

All earlier master-recurrence forms (½prevSame ± global-MD ± m*-split stocks) are SUPERSEDED.
Counterexample chain that forced this: V-tree broke global-MD (witness on other arm);
W-tree broke the m*-split (cost-0 same-side repeats reset prevSame while a halved arm
remnant persists + two deep arms on ONE side).

**THE LEDGER.** Per side s ∈ {min,max}, a scalar M_s ≥ 0, M_s(0) = 0. At each access
(side s, cost c, fresh f):

```
MASTER:  c ≤ M_s + κ·(1 + f)              (κ = 6 validated, zero violations all n/fams/inits)
update:  M_s ← M_s − max(0, c − κ(1+f)) + ½c ;  M_{other} ← M_{other} + 2
```

Validated: alt/runs4/runs16/rand2/rand3/rand4 × spine/rand/V/W × n ∈ {512, 2048, 8192},
both the draw-only and everything-banks variants: zero violations. Total links ≤ 3.44n.

**Summation (trivial):** Σdraw ≤ Σgains = ½Σc + 2n (M ≥ 0, M₀ = 0), so
Σc ≤ ½Σc + 2n + κ(n + Σf) ≤ ½Σc + 2n + 2κn ⟹ **Σc ≤ (4 + 4κ)n = 28n** (κ=6).

**Lean shape.** M is an explicit fold over the access history (simple def — no tree
inspection!). The single remaining research obligation (L3') is the MASTER inequality,
proven by a process induction carrying the **dive-tree invariant with SEGMENT claims**
(critical refinement, 2026-06-10): the ghost structure is a TREE of path SEGMENTS (not
absolute-depth chunks). Each segment = a contiguous piece of a past dive path with a
remnant claim r; the depth of any touched live key ≤ Σ claims along its root-to-key
segment chain + κ·(its untouched suffix). Invariant: Σ all claims ≤ M_s.
- A dive consumes the claims along its target's chain (draw), halves them (L2), and its
  repaid ½c covers the new halved chain — segment-wise.
- An opposite access perturbs exactly ONE segment (the shared head where its path crosses
  our territory): subtrees re-hang at ≤ +2 (L1/cargo argument), so M_other += 2 per access
  is EXACTLY the right total — this is why the flat +2 works despite many chunks (absolute-
  depth chunks would each need +2; segment claims share the head, only the head claim grows).
- Untouched tails hanging off past paths are fresh (κf pays their first dive).
- The claim family is carried as an existential ghost (∃ segTree, cover + Σ ≤ M).
Halving of the dived path = L2 (may need a segment-wise variant: depth-position within the
path halves — derivable from the same fuel induction); +2 re-hang = L1's proof technique
(cargo offsets), possibly needing a "subtree relocation depth" corollary of L1.

## L3 proof plan — the three-payer path decomposition (HISTORICAL paper sketch — the
ledger above replaces the run-level recurrence; the payer analysis below still describes
the same structural mechanisms and feeds the dive-tree invariant)

For a min-side access x from state t (mirror for max): every node on the search path to x is
paid by one of THREE payers; the master inequality is the sum of the three budgets.

1. **Fresh** (never touched): paid κ per node by the fresh budget. Covers first-dives into
   untouched structure (incl. interleaved virgin cargo interiors).
2. **Halved remnant** (on the previous min dive's path): by L2 (halving), such nodes sit at
   ≤ ½·(their old path position) + 2, plus ≤ 2 per opposite access since (L1 deepening,
   formally a +2g term). Total ≤ ½·prevMinCost + 2g + O(1). Covers re-dives.
3. **Witness drop** (the R_min stock): R_min := max keyDepth over LIVE keys ≤ m*. If the
   dive's depth exceeds payers 1+2, the dive IS (close to) the R_min witness, and L2 makes
   R_min drop by ≈ half the dive: paid κd·(R_min drop).

Why the suspect cases compose (witness-flip arithmetic): two deep min-side arms a (deeper)
and b: diving b with witness on a — either b > rem(a) (witness has flipped to b after a's
dive halved it: R-drop pays), or b ≤ rem(a) ≈ ½·prevMinCost (the ½prev term pays). Deep
off-path siblings below the dived path: untouched ⇒ fresh pays their later dive. Touched-
but-virgin deep parts: a key can only be touched by a path through it; any min-path through
arm-b's top leaves its deep part fresh; the touched part was halved (payer 2 next time).
The live-restriction kills dead-arm witnesses for free (keys < lo die, R_min drops freely).

Head segments (min-path nodes with keys > m*, interleaved): max-territory ancestors.
Suspected bound: ≤ ½prevMaxCost-ish or ≤ 2g — handled in the harness by the κ·LEN slack;
formal treatment TBD (may need a small cross-term; any +δ·COST(prevOtherSide) with δ < ½
keeps the geometric sum convergent: Σc ≤ (½+δ)Σc + B still gives Σc ≤ B/(½−δ)).

The Lean statement of the master should be the RUN-LEVEL m*-split form; the induction
invariant carries: (i) the previous min-run's path-key set with their halved depths,
(ii) R_min/R_max values, (iii) the touched set. This is sequential-formalization-grade work
(multi-week) but fully specified — no remaining design unknowns IF /tmp/split_stock.py
validates (task 1).

## ⭐⭐ L3' INVARIANT FULLY VALIDATED (2026-06-10, /tmp/ghost_checker7.py + /tmp/ghost_strict.py:
ZERO violations, 180/180 combos = n∈{128,512,1024} × 10 families (incl. runs16, repeats) × 6 inits (incl. V/W/zz/comb))

**THE INVARIANT (final form, Lean-transcribable):** per side s: claims = list of (key-interval I,
budget r ∈ ℕ doubled), pool p ∈ ℕ, plus the frozen ledger D.
- (C1) Σ_all r + p ≤ D_s — conserved EXACTLY by construction.
- (C2-strict) for the NEXT own-side access v: 2·tc(P_v) ≤ Σ_{claims met by P_v} r + p + 10 + 10·fresh(P_v)
  (met = claim intervals containing a touched node of P_v; NO per-claim overhead needed!).

**MASTER DERIVATION (exact, κ=6):** 2c = 2tc + 2f − 2 ≤ [Σr_met + p + 10 + 10f] + 2f − 2
≤ D + 8 + 12f ≤ D + 12(1+f) = D + 2κ(1+f) ✓.

**MAINTENANCE (the witness construction):**
- own dive (path P, cost c, fresh f): consume EXACTLY draw = (2c − 2κ(1+f))⁺, greedily from
  claims met by P then from pool (KEY LESSON: consumption ≡ ledger draw, NOT per-usage —
  cheap dives (draw 0) must consume NOTHING; this was the runs16 fix); add debris claim
  (I = span of P's live-side keys, r = c); prune all claims to the live interval (free).
- opposite access: p += 4.

**⭐(C2) FINAL FORM + REPRODUCTION CORES PINNED (2026-06-10 late session):**
- (C2-FINAL): **2·tc(P_next-own) ≤ Σr_met + pool + 14** — NO fresh term (/tmp/ghost_coef0.py:
  zero violations 180/180). Fresh-coefficient 0 is reproduction-optimal: fresh→touched
  conversions cost nothing on the RHS. Keystone: 2c = 2tc+2f−2 ≤ D+12+2f ≤ D+12(1+f) ✓ κ=6.
- (R2-core pinned, /tmp/r2_pin2.py): next OPPOSITE-side target v, mixed touched-sets
  (T before, T' = T ∪ q-path): tc(P_v-new, T') ≤ tc(P_v-old, T) + 2 for steps i ≥ 1
  (step 0 worst = 3, absorbed by the base case: 2·3 = 6 ≤ pool 4 + 14 ✓). Per-step
  reproduction arithmetic: 2Δtc ≤ 4 = pool gain. EXACT.
- (R1-core pinned, /tmp/prefix_measure.py + r2_pin.py): same-side: 2|p'| ≤ |sh| + 5 (flat),
  equivalently 2·keyDepth y (splay t q) ≤ keyDepth y t + |divergeSuffix y q t| + 5
  (generalizes keyDepth_splay_halving; suffix=[] case = the proven L2); also mixed-T form
  2Δtc ≤ c + 3.
- Agents launched on both cores (background): r2_core (hypothesis-pinning mandate: root ∈ T /
  path-closed T (H4) / one-sided orderings), r1_core (keyDepth_splay_le_shared).
- ⚠️REMAINING ASSEMBLY RISK (for the clause-chain, NOT the truth — checker validates the
  composite): (a) met-sum can DROP at opposite steps (claims losing met-status when the
  prefix changes) — resolution: the suffix-met claims are preserved (disjointness) and the
  prefix's needs shrink correspondingly; formalize (C2) reproduction by REGION-SPLIT
  (suffix-cover preserved exactly + prefix-cover ≤ 2Δtc ≤ pool-gain), NOT by met-sum
  monotonicity. (b) greedy-drain can drain claims that the same-side next-v'-suffix needed
  (intervals overlap even though paths are disjoint) — resolution candidates: the debris
  interval ⊇ v'-suffix values (suffix lies inside the q-span) so the debris claim r = c
  re-covers; may need drain-order refinement (drain the debris-span-internal claims first)
  or a (C2)-strengthening carrying per-region budgets; iterate against the checker
  (/tmp/ghost_coef0.py) BEFORE writing the Lean induction.

**(R2) SUBTLETY (pin before proving — historical, superseded by the region-split plan above):** after an opposite access, P_v's decomposition =
new-prefix (⊆ opposite q-path, all touched-after, length ≤ ½·shared + 2 by halving) ++
preserved suffix (∩ q-path = ∅, so its fresh nodes stay fresh ✓). The fresh→touched
conversions are confined to the prefix; the checker validates the composed accounting
(our-side claims + pool absorb the prefix-tc), but the exact per-case mechanism for
big-shared prefixes (which our-side claims cover the shared region) is to be discovered
during the (R2) proof — the validated checker guarantees a proof exists with these
constants; the case decomposition may need the claim-interval geometry (shared prefix
spans value-intervals of our previously-claimed debris).

**Lean reproduction obligations (task #4 — now exactly determined):**
- (R1) own-dive reproduction of (C2): suffix-preservation decomposition of the new next path
  (p'-part covered by the debris claim via L2-halving; suffix-part by surviving claims —
  greedy-drain overlap subtleties may need drain-ordering refinement, system-level validated).
- (R2) opposite-access reproduction: touched-deepening (+2) vs pool += 4 ✓.
- (R3) (C1) conservation: pure arithmetic.
- Plus: characterization wiring for sides, ascending-future-min facts, prune-≤-live lemmas.
Design lessons (do not re-litigate): full-claim consumption ✗ (cost-0 repeats wipe);
all-future (C2) ✗ (over-demands Θ(n) — only NEXT access, reproduction = induction);
+2·#met overhead ✗ ILLEGITIMATE (#met grows ~n; the strict form holds anyway);
per-usage consumption ✗ (over-drains during cheap runs).

## L3' GHOST-CHECKER history (earlier iterations — superseded by the validated form above)

The interval-claims ghost is now concrete and almost fully validated:
- State per side: claims = [(key-interval I, budget r)] (overlaps allowed) + pool p; ledger D.
- Checked invariants: (C1) Σr + p ≤ D; (C2) for the NEXT own-side access v:
  2·tc(path v) ≤ Σ_{met claims} r + 2·#met + p + 6; (C3) #met ≤ 2 observed.
- Maintenance: own dive = PARTIAL consumption (r −= 2·#(P∩I∩touched) per met claim; claims
  never zeroed by cheap dives) + debris claim (dive's live-span, r = c) + prune-to-live;
  opposite access: p += 4.
- THREE design lessons learned (each fixed a violation class): (i) full-claim consumption
  fails (cost-0 repeats wipe budgets) → partial; (ii) (C2) must quantify over the NEXT
  access only — far-future paths' tc is paid by accruals between now and their turn
  (all-future quantification over-demands by Θ(n)); reproduction across steps is the
  induction; (iii) cross-side coverage is the POOL's job (the +4s = L1' divergence pairs).
- STATUS: 58/64 family×init×size combos PASS exactly (incl. V, W, spines, all rand seeds,
  alt, runs4, n ∈ {128,512}).残 6 violations: ALL in runs16 (long same-side runs), small
  but drifting (C1: 3→7, C2: 6→10 at n 128→512). Diagnosed fixes to try next:
  (F1) draws must deduct pool after claims (C1 bookkeeping mismatch);
  (F2) within-run L2-halving constant (+5/step) accumulates over long runs — route 4 of the
  per-access 2κ constant into the debris claim (r = c + 4) or equivalent constant shuffle;
  possibly requires the consumption rule per-claim cap. Anatomy printer needed for the
  runs16 claim-evolution before finalizing.
- The Lean decomposition of (C2)-reproduction: per-claim soundness (∀-future, per-claim:
  2#(P∩I∩T) ≤ r + 2, maintained by L2-halving at own dives / unchanged suffixes) +
  pool-covers-unclaimed (∀-future: 2·#unclaimed-touched ≤ p + C, maintained by L1'-touched
  +2-pair per opposite access ✓ matching p += 4) + (C1). The checker's constant routing
  must stabilize first; the TARGET (master inequality, ledger def) is FROZEN — only the
  ghost witness bookkeeping is being polished.

## L3' GHOST-CHECKER SPEC (original spec — superseded by results above)

Findings narrowing the invariant (2026-06-10, /tmp/u_invariant.py):
- D ≥ 2·U_union FAILS by Θ(n) (future dives pay from FUTURE accruals; pooling over-demands now).
- Pooled claims (one Σ for all paths) FAIL maintenance in the W case (arm-a's draw must not
  deplete arm-b's cover) ⇒ claims must be REGION-PARTITIONED.
- Per-claim cover condition with +2 overhead per claim-met needs **#claims met by one path
  bounded** — likely true via the old turns-bounded measurement (/tmp/deque_turns.py: path
  turn-count ≤ 2 structured / ≤ 6 random, flat in n).

THE CHECKER (build in Python first; if it validates, its construction IS the Lean witness):
ghost state per side s = list of claims (I, r): I a key-interval ⊆ live, pairwise disjoint;
r ∈ ℕ (doubled budget). Invariants checked at every step:
  (C1) Σ r ≤ D_s (the explicit ledger).
  (C2) for EVERY future own-side access value v (from the fixed X): path P = searchPath(v, t):
       for each claim (I, r): 2·#(P ∩ I ∩ touched) ≤ r + 2; and the UNCOVERED touched nodes
       of P (∉ any claim interval) number ≤ C₂ (should be ≤ 2·(opposite accesses whose +4s
       are still unconsumed?) — design: uncovered ≤ accounted by a per-side "+2-pool").
  (C3) #claims met by P ≤ C₃ (the overhead bound; from turns-boundedness).
Maintenance rules (the construction, to mirror in Lean):
  - own dive at v: consume claims met by P (draw their r); after the splay, create ONE new
    claim for the dive's debris: I = the dive's span-interval, r = c (the doubled repay);
    split/shrink surviving claims' intervals as the splay relocates regions (use suffix-
    preservation: off-path regions keep their intervals; live-shrink deletes claims below
    new lo for free).
  - opposite access: +4 to ... ONE claim (the crossing-region claim) or a global pool;
    test both.
Acid tests: W-tree both-arm dives; spine warm-up; the cost-0-repeat resets; alt at n=8192.
If (C3) fails unbounded: refine claim granularity (merge adjacent same-dive claims) or
charge claim-overhead to the fresh/2κ constants per segment-entry.

## ⭐⭐⭐ L3' COMPLETE INVARIANT — THREE CLAUSES, ALL VALIDATED (2026-06-10 final, /tmp/c3_chain.py: ZERO violations)

**(C1)** Σr + pool ≤ D (exact conservation, consumption ≡ draw).
**(C2-next)** next own-side v: 2·tc(P_v) ≤ Σr_met + pool + 14 (max margin −11 observed).
**(C3-chain)** ∀ consecutive future same-side pairs (v_k, v_{k+1}): 2·tc(divergeSuffix of
v_{k+1} vs v_k's CURRENT path) ≤ Σr_met-by-suffix + pool + 8.
Quantification lessons (validated negatively): all-future (C2) ✗ (33/180, far-future shared
mass paid later); suffix-vs-NEXT ✗ (10/180, spines — far suffixes hold intermediate mass);
suffix-vs-PREDECESSOR ✓ (the marginal-mass decomposition; nested suffixes are what nobody
else pays).

✅DRAIN-ORDER RESOLVED (/tmp/drain_variants.py): the ghost's own-step drain order is
**A-claims (q-met, NOT next-own-suffix-met) → pool → B-claims (suffix-met) LAST** —
zero violations on ALL clauses (C1/C2/C3) across all combos. The 'cap' variant (cap B-drain
at c) BREAKS C1 (under-drain accumulates — D-gap shrinks; do not retry). CONSEQUENCES:
(1) ghostStepOwn in the invariant shell must be REDEFINED with the ordered drain (the
B-classification needs the next-own target — X-global, fine); the C1-own conservation
lemmas re-prove with the same totals (order-agnostic). (2) hstepOpp is UNAFFECTED
(opposite steps don't touch own-drain internals; INV@i is opaque to it). (3) the
hstepOwn (C3 k=1)-reproduction gains the order-structure: drained-B > 0 only when
draw > ΣA + pool, and draw ≤ 2tc_q − 12 ≤ ΣA + ΣB + pool + 2 (q's own (C2)@i), giving
drained-B ≤ ΣB + 2-ish; the residual full-drain case co-occurs with tiny suffixes
(adjacency) — the last arithmetic detail to settle inside the hstepOwn proof (named
hypothesis fallback allowed, then checker-iterate).

⚠️STEP-OWN MET-SURVIVAL — historical analysis (resolved by the reorder above) (pinned 2026-06-10 night,
/tmp/drain_overlap.py + /tmp/drain_net.py): the dive's greedy drain CAN take more from
next-own-suffix-met claims than the debris re-covers (drained-suf − c up to ~n/4, 28/36
rows positive). The composite (C3)@i+1 still validates because the bad steps co-occur
with v₁ ADJACENT to q (suffix nearly empty: e.g. alt/spine step 4: q=2, v₁=3, dsuf=118,
c=65, but tc(suffix)≈1 — the (C3 k=1) clause was hugely slack exactly when drained).
The validated rearrangement: drained-suf ≤ (sufMet-before − 2tc(suf)) + c + pool + 8 —
i.e. "the drain never exceeds the clause slack + c" ≡ (SUF-COVER)@after — TRUE at all
reached states but not yet derivable from {C1,C2,C3}@i alone. RESOLUTION CANDIDATES for
the Lean induction (checker-oracle them in order): (a) drain-CAP refinement of the ghost
construction: cap the per-dive drain from suffix-met claims at c + slack (modifying
consumeGreedy's order/cap — the ledger only needs Σdrain = draw; re-validate (C1));
(b) a 4th clause carrying the drain-aware bound for the next TWO dives; (c) X-global
clause referencing planned future drains. The checker-oracle pattern (8+ successes this
session) applies; the per-step arithmetic is all integer with headroom.

INDUCTION STRUCTURE:
- master@i ⟸ (C2-next)@i + (C1)@i + master_of_C1_C2 ✓ all proven/wired.
- STEP-OWN (dive q = v₀): (C2)@i+1 for v₁ ⟸ (C3-chain k=1)@i [suffix-vs-q!] +
  keyDepth_splay_le_shared [2|p'| ≤ c+6 ✓ PROVEN] + debris-met [r=c, easy].
  (C3-chain)@i+1 for (v_k, v_{k+1}), k ≥ 1: mutual-divergence preservation — if the pair's
  mutual divergence node is OFF q's path (in a cargo): suffix verbatim-preserved ✓; if ON:
  bounded perturbation via the cores (+2-ish, pool absorbs). NEW STRUCTURAL LEMMA NEEDED:
  divergeSuffix-vs-moving-base preservation: divergeSuffix v (searchPath-base v') under
  splay q — same machinery as searchPath_splay_decomp (the agent toolkit handles it).
- STEP-OPP: cores (touchedCount_mixed_splay_le root-between + within-run variant) give +2
  per clause; pool += 4 ✓.

## L3' ASSEMBLY — the reproduction clause-chain (earlier draft, superseded by the
three-clause form above)

PROVEN CORES (all merged, dev 6262 lines): keyDepth_splay_le_shared (2·kd' ≤ kd + |ds| + 5,
tight), touchedCount_mixed_splay_le (+2, root-between, arbitrary T), _step0 (+3),
searchPath_splay_decomp, divergeSuffix_disjoint. In flight: within-run variant
(root ≤ q ≤ v; workflow wf_9191db6d-914).

STEP-OWN derivation of (C2)@i+1 for next-own v' (validated link by link):
  (i)  2|p'| ≤ c + 6                       [keyDepth_splay_le_shared ✓ PROVEN: 2|p'| ≤ |sh|+5 ≤ c+6]
  (ii) debris claim (r = c) met via p'     [p'-keys ∈ [q, maxPq] ∧ touched-after; easy interval lemma;
                                            note v'-path-after keys all ≥ q by BST/root]
  (iii) (SUF-COVER): 2tc(suffix v') ≤ sufMet-after + pool-after + 8 — ✅VALIDATED zero
        violations (/tmp/repro_chain.py) — but it references the AFTER-state: as an
        induction link it needs either (a) all-future (C2) quantification (being re-tested
        on the FINAL ghost: /tmp/ghost_allfuture.py — the old failure predates the
        draw-exact-consumption fix, fat claims may now cover all-future), or (b) carrying
        (SUF-COVER) as an explicit invariant clause with its own reproduction.
  Then: 2tc_{i+1}(v') ≤ (c+6) + (sufMet + pool + 8) = c + sufMet + pool + 14 ≤ met_{i+1} + pool + 14 ✓
        (met_{i+1} ≥ c (debris) + sufMet (suffix ⊆ new path)).

STEP-OPP derivation for next-own v (side ≠ s_i): 2tc-new ≤ 2tc-old + 4 (cores: root-between
@run-boundaries + within-run variant), pool += 4, suffix-met preserved (claims of side b
untouched at opposite steps except prune-to-live; future paths avoid dead keys).

DRAIN-OVERLAP (the one open formal detail): greedy drain may consume claims that are both
q-met and v'-suffix-met. Resolutions (choose during the Lean proof; checker-equivalent):
the drain is bounded by q's own (C2) (draw ≤ met_i(q) + pool + 2), and the construction's
drain ORDER is ours to define — candidates: innermost-first (claims inside the debris span
first; their coverage is replaced by the debris claim) or oldest-first (current list order).
Test refined orders in /tmp/repro_chain.py-style probes before committing.

PROCESS SHELL (the final wiring, mechanical once the above closes): define
ghostAt : ℕ → Bool → GhostState as the fold of ghostStepOwn/ghostStepOpp over the process
(processTree, touchedUpTo, sideF, costN, freshN — all in the capstone file); prove
INV(i) := (C1: claimsTotal + pool ≤ ledger i side) ∧ (C2 per the chosen quantification)
by induction; instantiate hmaster via master_of_C1_C2 + searchPath_length_split +
metSum_le_total; feed hmaster to deque_challenge_of_ledger_master and
deque_conjecture_challenge_of_ledger_master (capstone2) → fill BOTH challenge sorries
(ℕ→ℝ existential cast adapter only).

## Assembly skeleton (L4) — exact Lean plan

Process defs: `t₀ = init`, `tᵢ₊₁ = splay tᵢ (X i)`; `costᵢ = splay.cost tᵢ (X i)`;
`Pathᵢ` = search-path keys; `touchedᵢ = ⋃_{j<i} Pathⱼ`; `freshᵢ = |Pathᵢ \ touchedᵢ|`;
`side i` from `deque_future_one_sided` (tie → min, via if/Classical);
`lo_i` = max of past min-side accesses (hi mirror); future accesses ∈ [lo_i, hi_i] by one-sidedness;
`MDᵢ` = max keyDepth over live keys (∈ [lo_i,hi_i]) in tᵢ (0 if none);
runs = maximal constant-side blocks; `prevSame J` = latest earlier run of J's side.

**H_MASTER (run-level, the L3 target; prevSame-cost = 0 when none):**
```
COST(J) ≤ ½·COST(prevSame J) + κ·(LEN J + FRESH J) + κd·(MD_start(J) − MD_end(J))⁺ + C·LEN J
```

Assembly chain (all mechanical):
1. Σ_J COST(prevSame J) ≤ Σ_J COST(J)  (injectivity: each run is prevSame of ≤ 1 run).
2. Σ FRESH ≤ n (touched-set telescope; sequential μ-pattern).
3. Σ_J (MD_start − MD_end)⁺ ≤ MD₀ + Σ rises ≤ MD₀ + 2n, using per-access MD-rise ≤ 2
   (from L1 deepening + live-interval monotone shrink), MD₀ ≤ n (`search_path_len_le_num_nodes` ✓ ported).
4. ⇒ Σ cost ≤ 2(2κ + 3κd + C)·n; with (κ,κd,C) = (6,2,1): 38n.
5. Bridge: `sequence_cost = Σ costᵢ` (foldl ↔ sum, sequential's `sequence_cost_eq_seqCost` pattern),
   `splay_cost_eq_search_path_len_sub_one` ✓ ported, α ≥ 1 (`one_le_alpha_of_pos`)
   ⇒ `sequence_cost init X ≤ c·n·α n` with c = 38-ish (loose is fine).

The constants in H_MASTER are whatever the L3 induction yields; assembly only needs them fixed.

## Failed routes (do not retry)

- Monolithic Ω = Σ live non-root [hL² + hR² + 4(φ₂L+φ₂R)] per-step telescope: minimal stock
  Λ* is Θ(n)-sized and is NOT any simple state function (8·width / 8·touched-live / 2·Ω dominate
  the envelope pointwise but all fail per-step); raising the φ₂ coefficient makes it worse
  (A=4 optimal); residual creep ≈ 8·log₂ n from turn-bump assembly jumps (+177 on an 8-link
  step). Cumulative telescope holds (rate ≈ 15) but is not directly inductible.
- Per-side decay of turn-bumps, per-node O(1) ledgers, same-side bump recurrences: all fail
  (bumps spike after long same-side runs; nodes re-counted ~n/10 times).
- Per-level local payment at zigzig levels (mirror-bump): fails; compensation is cross-level.

## Empirical harnesses (all faithful to repo splay via .tmp_alt_sim.py)

- `/tmp/run_decay3.py` — THE validated master recurrence (run-level, MD credit).
- `/tmp/run_decay4.py` — fresh2 (first-K-touches) budget variant.
- `/tmp/per_access.py` — per-access granularity variant.
- `/tmp/crossing_decay.py` — crossing-cost recurrence (½-decay + 4(gap+1) + 4fresh + 3, resid 0–3).
- `/tmp/boundary_deepen.py` — deepening ≤ 2 measurement (deepWorst = 2 universally).
- `/tmp/violation_anatomy.py` — run anatomy printer (rand2/rand4-spine virgin dives).
- `/tmp/lambda_*.py`, `/tmp/jump_anatomy.py` — the Λ-hunt forensics (Ω route).
- `/tmp/deque_telescope2.py` — cumulative Ω telescope (fallback route).
