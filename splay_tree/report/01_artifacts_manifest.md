# Artifact Manifest — splay_tree development files

This maps every working file to its role. Tracked files under `Challenges/`
are the shipped problem statements/definitions and the (filled) Sequential
proof — **never modify these except the intended final fill**. Everything
prefixed `.tmp_` is untracked scratch/development.

## Tracked (shipped) — do not touch except final fill
- `Challenges/Splay_Tree/Def_Splay.lean`, `Def_Containment.lean`,
  `Def_Ackermann.lean` — cost model, pattern avoidance, inverse-Ackermann.
- `Challenges/Splay_Tree/Challenge_Splay_Sequential.lean` — **SOLVED**: contains
  the complete proof of `Splay.sequential` (no `sorry`, standard axioms).
- `Challenge_Splay_Deque.lean`, `Challenge_Splay_DequeConjecture.lean`,
  `Challenge_Splay_TraversalConjecture.lean` — still `sorry` (open / partial).

Each load-bearing deque file below carries a `/- PUBLICATION HEADER … -/` block
documenting its public results, axiom status, and any off-path obligations.
(`Challenge_Splay_Sequential.lean` is deliberately left untouched — it is under
separate optimization.)

## Load-bearing scratch — KEEP (the deque reduction + kernel)
- `.tmp_claude_turn_main.lean` — **the deque deliverable** (§§1–33): the turn/
  generation/exposure machinery, `TouchedSumAlpha`, the cost bridge, the proved
  reduction `deque_challenge_CLOSED_of_touched`, the channel decompositions and
  residuals. ~8,400 lines, compiles, standard axioms.
- `.tmp_claude_inblock.lean` — STEP-1 depth-projection identity
  (`inblock_touched_eq_depth_projection`) + `restrict` and its lemmas.
- `.tmp_claude_merged_glue.lean` — the `gammaOf` inverse-Ackermann arithmetic +
  `recursion_telescope` ported over the ZBK base; `recursionTelescopedBound_abstract`.
- `.tmp_claude_capstone.lean` — `deque_50pt_of_residuals`: the dependency-graph
  capstone (verbatim `Goal50pt`).
- `.tmp_codex_ds_main.lean`, `.tmp_codex_ds_defs.lean`, `.tmp_codex_ds_alpha.lean`
  — the Davenport–Schinzel toolkit (`CodexDS`): `middlesKey_proved`,
  `affine_sound_positional`, the gamma/alpha engine.
- `.tmp_claude_zb_closing.lean`, `.tmp_claude_zb_kernel.lean` — **source of the
  prebuilt `Challenges.ZBK` olean** (search-path calculus, touched-prefix
  closure, comb-shape, generations, cost bridge). The deque file imports the
  olean; keep these as the rebuildable source.
- `.tmp_dsv_alpha.lean` — auxiliary `F`/`alpha` lemmas.
- `.tmp_alt_sim.py` — **the executable reference splay model**; every empirical
  probe imports it. Keep.
- `.tmp_codex_NOTES.md`, `.tmp_dsv_NOTES.md`, `../HANDOFF_NEXT_STEPS.md` —
  development notes / the full campaign ledger and open-lemma statements.

## Traversal-conjecture development — KEEP (un-audited but substantial)
These constitute the (partial) Traversal-conjecture effort — a reduction to
three structural hypotheses. Not audited to the standard of the Sequential/Deque
results; retained pending review.
- `.tmp_traversal_lemmas.lean`, `.tmp_claude_hlower_drop.lean`,
  `.tmp_hkernel_probe.lean`, `.tmp_local_pair_work.lean`,
  `.tmp_claude_arsenal_frozen.lean`.

## Superseded development iterations — ARCHIVED to `.tmp_attic/`
Earlier versions/probes whose results were consolidated into the kept files
above (the ZBK kernel, `turn_main`, or the traversal cluster). Moved, not
deleted, so they remain recoverable.
- Kernel/atomic-step dev (consolidated into ZBK): `hstep_v2`, `hstep_v3`,
  `hstep_final`, `hstep_opp_partial`, `hstep_opp_scratch`, `step_opp`,
  `step_opp_new`, `atomic_step`, `atomic_ghost`, `pos_halving`, `pos_base`,
  `r2_within`, `r2_within_min`.
- Old deque architecture (pre-`turn_main`): `deque`, `closing`,
  `capstone_deque`, `capstone_deque2`, `capstone_pooled`, `shell_pooled`,
  `turn_skeleton`, `zb_phaseD_dev`, `devbase1`, `devbase2`.
- Traversal dev duplicates (superseded by `local_pair_work`/`traversal_lemmas`):
  `local_pair`, `local_pair2`, `probe_local_pair`, `pair_induction`,
  `path_compare`, `path_triangle_probe`, `Q_bound`.
- Tiny one-off probes: `print_theorems`, `probe_card`, `print_containment`,
  `agent_ancestry`, `claude_sequential` (68-line stub, superseded by the filled
  challenge), and various `.tmp_print_*`/`.tmp_inspect_*`/`.tmp_splay_consts`.

To discard the archive entirely: `rm -rf .tmp_attic/`.
