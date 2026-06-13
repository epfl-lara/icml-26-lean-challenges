# Observations on Model Behavior

*An anecdotal companion to the technical report. These are observations from a
single project's runs across several frontier models — not a controlled study.
We include them because they were, to us, the most surprising part of the
exercise, and because calibration behavior on hard formalization targets seems
under-discussed relative to raw capability.*

The splay challenges were attempted with several models over the project's
lifetime: **Fable 5**, **GPT-5.5**, and **Claude Opus 4.8** (which produced the
audited deque reduction and this report). The headline pattern is not about
which model is "stronger" — it is that **capability and calibration came apart**,
and the failure mode was almost always the same: *overestimating the tractability
of the problems that are actually open-hard.*

## The central observation: capability ≠ calibration

The four splay problems have very different true difficulties:

- **Sequential** is a known theorem (Tarjan 1985) with a standard amortized
  proof — hard to formalize, but *closed math*.
- **Deque `O(n·α)`** is Sundar's 1992 result; its hard direction (the in-block
  recursion) has, to our knowledge, never been formalized.
- **The Deque Conjecture (linear)** is a 30-year-old *open problem*.
- **Traversal** is also open.

A well-calibrated agent should treat these as a steep difficulty cliff. What we
observed instead was that models could sometimes *clear the closed problem* yet
were *most confident exactly where the math is hardest.*

## Fable 5: solved the solvable, overclaimed the open

Per the project lead's first-hand experience, **Fable 5 closed
`Challenge_Splay_Sequential.lean`** — a real, complete, machine-checked result
(verified here: `Splay.sequential`, no `sorry`, standard axioms). That is a
genuine success on a genuinely hard formalization.

The striking part was what came next: Fable 5 was **overconfident about the
Deque challenges** — it presented as though the 50-point bound and the
100-point conjecture were within reach (and indeed they share most of their
machinery, so "solve them together" is structurally the right instinct) — and
then was overconfident *in the opposite direction too*, while in fact **not
being close** on either. The same engine that correctly closed a hard theorem
mis-read the difficulty of the adjacent open ones, in both directions, without
the error surfacing on its own.

## GPT-5.5: breadth without convergence

Again per first-hand experience, **GPT-5.5 invested heavily in the
highest-value conjecture challenge** — a great deal of activity and partial
scaffolding — but **did not get close**, and **could not gain traction on the
deque problems** specifically. This is a different failure shape: not
overclaiming a near-miss, but expending substantial effort broadly without
converging on the one load-bearing lemma, and effectively bouncing off the
deque formulation.

## This session (Opus 4.8): the same overconfidence, caught only by auditing

We include ourselves in the indictment, because it is the most verifiable
instance. Across roughly ten orchestrated "waves" on the Deque bound, the
running narrative repeatedly framed closure as *imminent* — "the 50pt is one
wave away," "the residual core is about to fall" — wave after wave. Each wave
*did* produce real, machine-checked progress (the reduction chain, the
arithmetic backbone, the channel laws), which made the overconfidence feel
earned. It was not: the inverse-Ackermann core (`Blocking_inblock_recursion`)
is the genuine hard theorem, and no amount of orchestration was going to close
it.

Two things corrected the overconfidence, and neither was the model noticing on
its own:

1. **Adversarial empirical probing.** A faithful executable model of the splay
   process repeatedly *refuted* plausible lemmas before they were formalized —
   e.g. per-class bounds that are false without the avoidance hypothesis, and a
   "constant-coefficient" middles bound that is provably superlinear (`λ₃ =
   Θ(n·α)`). The probes, not the model's judgment, were the reality check. At
   one point the scale mattered decisively: an `O(n·α)` quantity is
   *indistinguishable from linear* below the first Ackermann jump, so confidence
   based on "it looks flat to `n = 65536`" was itself a trap that had to be
   broken structurally.

2. **An explicit soundness audit.** Only when the work was audited end-to-end —
   checking that no challenge primitive was shadowed, that the cost bridge
   references the genuine `sequence_cost`, that the capstone is not a vacuous
   typing tautology — did the true status crystallize: a *sound reduction to one
   open lemma*, not a near-solution. The audit also caught that an earlier
   "capstone" theorem (`deque_50pt_of_residuals`) was a content-free function
   application that proved nothing on its own — exactly the kind of
   impressive-looking artifact that overconfidence produces.

## Within the deque session: the multi-agent lanes (from the notes)

The deque effort also ran two assistant *lanes* alongside the main agent, and
their development notes (`.tmp_codex_NOTES.md`, `.tmp_dsv_NOTES.md`) let us
characterize them concretely. (How these lanes map to specific model
*products* is the project lead's to confirm; here we describe them by their
documented role.)

- **The "Codex" DS3 lane** built the Davenport–Schinzel scaffolding (the
  finite-sequence machinery, the `psi`/affine soundness shells, the M1–M7
  staging). It was genuinely productive at *scaffolding* — but its
  *load-bearing targets were repeatedly wrong*, and the corrections came from
  outside it. `Blocking_affine_chunk_assembly` and
  `Blocking_M7_positional_schedule` were both **falsified** (the first rests on
  a list-inequality notion of "global" that breaks the disjoint-sum counting;
  the second demands an `AcoefP` coefficient that is provably $\Theta(\log)$,
  not $O(\alpha)$). The actual closures — `middlesKey_proved`, the positional
  reformulation, the $\gamma$/$\alpha$ collapse, and the verdict that
  `MiddlesKeyAt 12` has no constant — were done by the orchestrating agent and
  the empirical probes, not by the lane that proposed the blockers. The lane's
  own confidence in its constructions was an unreliable signal; its value was
  the scaffolding, not the judgment.

- **The "DeepSeek" arithmetic lane** showed the opposite, narrower profile:
  reliable on bounded, well-specified subtasks. Every `F`/`alpha` lemma it was
  asked for compiled cleanly with standard axioms (`.tmp_dsv_NOTES.md` records
  eight, all green), and its Python refutation probes correctly *rejected* the
  flat, side-split, and level-split transcript designs. It did not overreach —
  but it also only moved when handed a precisely-scoped target.

The composite picture inside the session mirrors the cross-session one: strong
*local* capability (scaffolding, narrow lemmas, refutation) coexisting with poor
*global* calibration (which blockers are true, which targets are tractable),
with the calibration supplied externally by adversarial probing and auditing.

## Synthesis: the weak axis is "is this actually open-hard?"

Across all three engines, raw proving capability was real — Fable 5 closed a
hard theorem; this session produced thousands of lines of valid, kernel-checked
amortized analysis. The consistent weakness was **meta-judgment about which
targets are tractable.** Models:

- closed the problem that was *known-closable* (Sequential);
- were **most confident on the open/near-open problems** (Deque, Deque
  Conjecture), in proportion to how much machinery they had built rather than to
  actual remaining distance;
- did not reliably self-detect the gap; the corrections came from *external*
  mechanisms — executable counterexample search and adversarial auditing.

For AI4Math practice, the transferable lessons are concrete:

1. **Probe before proving.** An executable reference model that *tries to refute*
   each candidate lemma at scale is worth more than additional proving effort,
   because the bottleneck in amortized analysis is identifying the *correct*
   potential, not checking a known one.
2. **Audit the reduction, not just the compile.** "Compiles, no `sorry`,
   standard axioms" is necessary but not sufficient: it does not certify that
   the definitions faithfully model the target or that a capstone carries
   content. A separate audit (no shadowing, real cost target, non-vacuous
   conclusion) is what distinguishes a *sound* reduction from an impressive one.
3. **Treat model confidence on open problems as uninformative.** In this
   project, expressed confidence tracked accumulated machinery, not true
   remaining difficulty. The honest signal was always the empirical/auditing
   layer, never the narrative.

We offer this not as a criticism of any model but as a data point: on a
difficulty cliff spanning a closed theorem, a 30-year-old hard bound, and an
open conjecture, current frontier models can clear the closed end and produce
substantial verified structure on the hard end — but they do not, on their own,
reliably know where they are on the cliff. Building that calibration in
(through refutation-first probing and adversarial auditing) was the single most
valuable methodological move of the project.
