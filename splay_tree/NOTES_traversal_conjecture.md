# Splay Traversal Conjecture — attempt status & findings

Consolidated record of the attempt to close the `sorry` in
`Challenges/Splay_Tree/Challenge_Splay_TraversalConjecture.lean` (200 pts).
All Lean claims below are **machine-checked** (`lake env lean` clean, `#print axioms`
= only `propext, Classical.choice, Quot.sound`; the one counterexample uses
`native_decide`). Nothing here is asserted without compiling.

## TL;DR

- The 200-pt **Traversal Conjecture** (splay any 231-avoiding / preorder sequence
  from an *arbitrary* initial BST in `O(n)`) and the 100-pt **Deque Conjecture**
  are **open research problems**, confirmed open as of 2024–2026 by an exhaustive
  literature pass (21 primary sources, adversarially verified). They cannot be
  filled with current mathematics.
- We produced a **verified conditional reduction**: the conjecture follows from three
  crisp leaves `{hstrict, hlower, hkernel}`. `hkernel` is reduced further (Codex) to
  per-pair gap bounds; `hstrict`/`hlower` are the irreducible open core.
- We **rigorously ruled out** the elementary attacks (per-step potentials) with
  experimental evidence (LP over a rich feature space + held-out scaling), and
  confirmed the literature's verdict that a **global charging argument** is required.

## 1. Verified Lean results (in `.tmp_claude_hlower_drop.lean`, compile-clean)

| Theorem | What it proves |
|---|---|
| `traversal_conjecture_of_reset_budget_kernel` | conjecture `⟸ {hstrict, hlower, hkernel}` (the whole problem reduces to these three) |
| `upperResetFirstPairQPotential_gap_drop_of_budget_kernel` | the upper-block amortized step closes with constants `(A,G,H,D)=(3,1,2,3)` from the single budget-drop kernel `g1+1 ≤ 3·Δbb` |
| `pivotResetLowerPathSum_le_boundaryBudget_of_hupper_and_reset_le_plain` | `hlower ⟸ hupper + (reset ≤ plain + C·N)` |
| `claude_hzero_after_lower_counterexample` | refutes "the pair-gap is always 0 after a lower access" — the descent case (left spine `0..10`, seq `![9,2,3,9,7]`) has gap `> 0` (`native_decide`) |

`traversal_conjecture_of_reset_budget_kernel` and `upperResetFirstPairQPotential_gap_drop_of_budget_kernel`
have been integrated into the live scratch file `.tmp_traversal_lemmas.lean` by Codex.

## 2. Reduction architecture (how the problem decomposes)

```
traversal_conjecture
  ⟸ first-max split (231-avoidance) + amortized "reset/budget" potential
  ⟸ { hstrict : splayPathSumWithFinal ≤ Ks·boundaryBudget   (strict prefix block, all < q)
      hlower  : pivotResetLowerPathSum ≤ K·boundaryBudget    (reset baseline, q at root)
      hkernel : actualResetFirstLowerPairGapPotential + 1 ≤ 3·Δbb   (per-step gap kernel) }
```
- `hkernel` (Codex): reduced via `_231_gap_cases` to ascending (`hgap_ge`, gap ≤ 2) and
  descent-under-barrier (`hdesc_gap_barrier`, gap ≤ 2). The barrier follows from
  231-avoidance; under it the gap is empirically ≤ 1. **Near closure.**
- `hstrict`, `hlower`: **the open core** — both are exactly "231-avoiding splay access is
  linear," i.e. the Traversal Conjecture itself (no shortcut; see §3).

## 3. Why the elementary attacks fail (rigorous, evidence-backed)

The open core requires a *global* amortized argument; every *per-step* / closed-form
potential provably fails:

- **Budget non-subadditivity (2× wall):** `boundaryBudget(prefix)+boundaryBudget(suffix) ≤ 2·boundaryBudget(full)` (proved) but **not** `≤ 1·` (counterexample in file). So naive firstMax induction **doubles the constant per level** → diverges.
- **Per-step weighted step** (`Φ = A·boundaryBudget`): required slack `C ≈ q` (linear), worst case = sorted/spine access. Dead for any constant `A`.
- **`maxSequentialPotential`** (`= 5(n−1)+5·max(leftEdges,rightEdges)`, already in file with reductions at lines 31682/31719): per-step `C ≈ n/2`; `+δ·activeBudget` only shifts the intercept. Dead.
- **LP potential discovery** (`.tmp_potential_lp*.py`): solved a min-max LP over a rich Lean-definable feature space (edge counts, two-child, zig-zag nodes, root spines, depth-2 "staircase"). Held-out scaling: depth-1 features → `C~m/2`; depth-2 staircase → `C~m/6`; held-out `C = 11,21,41,82` for `m=64..512` — **still linear in m**. The limit is the *circular* "remaining-cost" potential. **No closed-form per-step potential exists in this space.**
- **Levy–Tarjan's global potential** (`Φ=2·#touched-ancestors-of-sub-roots`, ≤6 amortized) is for **insertion**-splaying; tested on **access**-splaying it gives `C~n` (the first deep access from a bad init is unpaid). It does not transfer.

These are exactly consistent with the problem being open.

## 4. Literature verdict (deep research, 2024–2026, cited)

- **OPEN** for splay: only special cases proven — sequential/sorted access [Tarjan,
  *Combinatorica* 1985]; `T=T'` preorder-insertion-from-empty [Chaudhuri–Höft 1991;
  cleanly re-proved Levy–Tarjan, WADS 2019, arXiv:1907.06309]; `T` α-weight-balanced
  [Levy–Tarjan 2019].
- **Best general progress is for Greedy BST, not splay:** `O(n·2^{α(n)})` on preorders
  [Chalermsook et al., SODA 2023; FOCS 2015 arXiv:1507.06953], linear only with
  preprocessing / permutation-initial-tree [Pareek 2024, arXiv:2407.03666]. *"None
  transfer to splay."* "No online BST is known to satisfy this conjecture."
- **Only proposed attack on the general case:** Pettie (SODA 2008, arXiv:0707.2160)
  conjectures (does **not** prove) that transcribing splay rotations into a generalized
  Davenport–Schinzel sequence of length `O(n)` would resolve deque/split/traversal.
- The clean global technique that *does* exist: **Levy–Tarjan's** `Φ = 2·(#touched
  nodes that are ancestors of sub-roots)` (sub-root = untouched node with a touched
  parent), `Φ_0=Φ_n=0`, amortized ≤ 6/splay; 231-avoidance keeps each sub-root at
  left-depth ≤ 1. Closes the **insertion** preorder case only.

## 5. Achievable vs open (the repo's challenges)

`sequential` → `deque` → `deque_conjecture` → **`traversal_conjecture`**: every challenge
`rcases traversal_conjecture`, so all are currently *conditional* on the open sorry.

| Challenge | pts | Honest status |
|---|---|---|
| `traversal_conjecture` | 200 | **open** problem — unfillable |
| `deque_conjecture` | 100 | **open** problem — unfillable |
| `sequential` | 50 | proven theorem [Tarjan 1985], but needs his intricate *access* charging argument (not freely/cleanly available; Levy–Tarjan's clean potential does not transfer to access). Major formalization. |
| `deque` | 50 | proven theorem [Sundar 1992, `O(nα(n))`], needs Davenport–Schinzel α(n) charging. Major formalization. `Def_Ackermann` (Klazar α) is already present. |

## 6. Recommendation

- Treat the 200/100-pt as the open problems they are.
- Let Codex land `hkernel` (completes the *conditional* scaffold: conjecture ⟸ {hstrict, hlower}).
- The only feasible *unconditional* new theorem is formalizing Levy–Tarjan's insertion
  result as a standalone (real, clean, ~weeks) — but it does not fill a repo sorry.

## 7. Artifacts

- `.tmp_claude_hlower_drop.lean` — verified reductions (this file's §1).
- Faithful Python harnesses (mirror exact Lean `splay`/`search_path_len`/`avoids231`):
  `.tmp_faithful_hlt_search.py`, `.tmp_faithful_lower_weighted_step.py`,
  `.tmp_check_modified_vs_plain.py`, `.tmp_find_budget_drop_lemma.py`,
  `.tmp_maxseqpot_step_search.py`, `.tmp_potential_lp2.py`, `.tmp_levytarjan_potential.py`.
- Deep-research report: see session transcript (task `wklb4wz6w`).
