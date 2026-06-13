# A Lean 4 Formalization of Splay-Tree Access Bounds

Report and machine-checked artifacts for the splay-tree access problems of the
ICML 2026 AI for Math Challenge 4 (ShadowBench, Track 2) [ai4math2026track2].
Splay trees are the open frontier of the challenge set: the Sequential Access
Theorem is closed, while the Deque bound, the Deque Conjecture, and the Traversal
Conjecture remain open or partial. Markdown sources here; convert to LaTeX
(`references.bib` provided) for submission.

## Contents

- **`00_splay_formalization_report.md`** — the paper: the Sequential Access
  Theorem (solved); an audited *sound reduction* of the Deque `O(n·α(n))` bound
  to a single inverse-Ackermann residual; the Deque-Conjecture obstruction; the
  Traversal partial reduction; methodology; precise open obligations.
- **`03_diagrams.md`** — Figures 1–3 (status, the Deque reduction, the Sequential
  proof), with exact Lean declaration names.
- **`02_model_behavior_observations.md`** — Discussion: an anecdotal cross-model
  account of how capability and calibration came apart on these targets.
- **`01_artifacts_manifest.md`** — appendix: which Lean files are load-bearing.
- **`references.bib`** — competition and classical references (Sleator–Tarjan,
  Tarjan, Sundar, Pettie, Hart–Sharir, Klazar, Agarwal–Sharir–Shor).
- **`../blueprint/`** — a `leanblueprint` scaffold whose dependency graph is the
  proven-spine / open-core picture of Figure 2.

## Verified status of the four splay challenges

Each was checked by compilation plus `#print axioms` on its main theorem.

| Challenge | Theorem | Status | Axioms |
|---|---|---|---|
| Sequential | `Splay.sequential` | **solved** (no `sorry`) | `{propext, Classical.choice, Quot.sound}` |
| Deque (`O(n·α)`) | `Splay.deque` | open — sound reduction to `Blocking_inblock_recursion` | std (for the proved chain) |
| Deque Conjecture (`O(n)`) | `Splay.deque` (linear) | open | — |
| Traversal Conjecture | `traversal_conjecture` | partial (3-hypothesis reduction) | — |

## Abstract (one paragraph)

We formalize, in Lean 4, the cost analysis of the top-down ("pairing") splay
heuristic on the access patterns of the ICML 2026 AI4Math splay challenge. We
give a complete machine-checked proof of the **Sequential Access Theorem**
[Tarjan1985sequential] (`Splay.sequential`, standard axioms only), via a
rotation-link count and a left-spine potential. For the **Deque bound**
[Sundar1992] we contribute an audited *sound reduction*: a verified chain from
the genuine `splay.sequence_cost` to a named core (`TouchedSumAlpha`), and from
there — through a proven telescope backbone and an exact depth-projection
identity — to a single sharply-stated inverse-Ackermann incidence lemma
(`Blocking_inblock_recursion`), which is precisely the in-block recursion at the
heart of Sundar's `O(n·α(n))` theorem. We do not close that lemma; we isolate it
and validate it empirically. For the **Deque Conjecture** [SleatorTarjan1985] we
record a negative result on constant-slack local potentials, and for the
**Traversal Conjecture** a reduction to three structural hypotheses. The
Davenport–Schinzel toolkit underlying the deque analysis (an order-5 Hart–Sharir
middles lemma [HartSharir1986], the inverse-Ackermann arithmetic of
[Klazar1992]) is developed and machine-checked separately.
