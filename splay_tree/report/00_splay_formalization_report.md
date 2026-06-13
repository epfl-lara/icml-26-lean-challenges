# Machine-Checked Amortized Analysis of Splay Trees in Lean 4

**A formalization report on the splay-tree access conjectures: the Sequential
Access Theorem (solved), and a sound reduction of the Deque bound to a single
inverse-Ackermann incidence lemma.**

---

## Abstract

We report a Lean 4 formalization effort targeting the four splay-tree access
problems of the ICML 2026 AI for Math Challenge 4 (ShadowBench, Track 2)
[ai4math2026track2] — the open frontier of that challenge set. All four are
phrased as bounds on `splay.sequence_cost`, the total cost of running the
top-down ("pairing") splay heuristic [SleatorTarjan1985] on an access sequence.
Our results:

1. **The Sequential Access Theorem is fully proved** [Tarjan1985sequential]: for the
   sequential pattern `1, 2, …, n` on any `n`-node BST, the total splay cost is
   at most `c·n` for an explicit constant. The challenge theorem
   `Splay.sequential` is closed with no `sorry` and axioms
   `{propext, Classical.choice, Quot.sound}`. The proof is a machine-checked
   amortized argument via a rotation-link count and a left-spine potential.

2. **The Deque bound (`O(n·α(n))`) is reduced, soundly and machine-checked, to
   a single open lemma.** We give a verified chain
   `TouchedSumAlpha → ⟨the verbatim challenge statement⟩` where `TouchedSumAlpha`
   asserts that the total *touched-prefix* length is `O(n·α(n))`. Every step
   from the real `splay.sequence_cost` down to `TouchedSumAlpha` is proven; the
   inverse-Ackermann factor is localized to exactly one combinatorial residual,
   the *in-block recursion* lemma, which is the genuine content of Sundar's
   `O(n·α(n))` deque bound [Sundar1992] (and of Pettie's Davenport–Schinzel
   re-proof [Pettie2008]). We were not able to close that residual; it is
   isolated sharply and validated empirically to `n = 65536`.

3. **The Deque Conjecture (linear bound) and the Traversal Conjecture remain
   open.** For the Deque Conjecture we record a negative result: a large family
   of constant-slack local-potential arguments is provably insufficient (the
   "geometric-staircase" obstruction). For the Traversal Conjecture we have a
   reduction to three structural hypotheses, not yet discharged.

All proofs are checked under Lean's kernel with only the three standard
classical axioms. We also describe the simulator-guided methodology that drove
the development: every architectural decision was first tested against an
executable reference implementation of the splay process before any Lean was
written, which repeatedly caught false lemmas before formalization effort was
spent on them.

---

## 1. Setting and definitions

All four problems concern the same cost model, fixed by the challenge's
`Def_Splay.lean`:

- `splay : BinaryTree → ℕ → BinaryTree` is the **top-down pairing splay**
  (zig / zig-zig / zig-zag two-level rewrites; *not* standard bottom-up
  splaying — the two coincide in asymptotics but differ step-by-step).
- `splay.cost : BinaryTree → ℕ → ℝ` charges `+1` per zig and `+2` per
  two-level step.
- `splay.sequence_cost init X : ℝ` folds `splay.cost` over the access sequence
  `X : Fin n → ℕ`, splaying as it goes:
  ```
  sequence_cost init X = (foldl (fun (t,c) i => (splay t (X i), c + splay.cost t (X i))) (init,0) (finRange n)).2
  ```
- `IsBST`, `BinaryTree.num_nodes`, `BinaryTree.toKeyList` are the obvious
  structural predicates/measures.
- `KlazarAckermann.alpha` is Klazar's inverse-Ackermann function [Klazar1992], defined via
  the `N₅` hierarchy `F 1 n = 2n`, `F (k+1) n = (F k ·)^[n] 1`,
  `F_omega n = F n n`, `alpha = Nat.find …`.
- `X avoids p` is order-pattern avoidance (`Def_Containment.lean`); the deque
  access class is exactly `X avoids ![2,1,3] ∧ X avoids ![2,3,1]` (every access
  is the current minimum or maximum of the remaining suffix — "future
  one-sided").

The four challenge statements (each `theorem … := sorry` in the shipped files):

| Problem | Statement (informal) | Points |
|---|---|---|
| Sequential | sequential access `1..n` costs `≤ c·n` | — |
| Deque | deque-class access costs `≤ c·n·α(n)` | 50 |
| Deque Conjecture | deque-class access costs `≤ c·n` | 100 |
| Traversal Conjecture | preorder-of-`S`-in-`T` access costs `≤ c·n` | — |

### 1.1 Context and related work

These four problems are the "easy access pattern" corollaries of the *dynamic
optimality conjecture* of Sleator and Tarjan [SleatorTarjan1985], which asks
whether splay trees are constant-competitive against any dynamic binary search
tree. Dynamic optimality remains open; the best general results are the
`O(log log n)`-competitive tango trees [Demaine2004tango] and their refinements
[Wang2006], analyzed not against splay but against Wilber's lower bounds
[Wilber1989]. Among the access-pattern corollaries, the *static optimality*,
*working set*, and *dynamic finger* theorems are known — the last by the deep
two-part argument of Cole and collaborators [ColeMishraSchmidtSiegel2000,
Cole2000] — while *sequential access* [Tarjan1985sequential], *deque*, *split*,
and *traversal* form a cluster of conjectures about *linear*-cost patterns.

The Deque Conjecture (linear deque cost) was posed in [SleatorTarjan1985]; the
best known upper bound is Sundar's `O(n·α(n))` [Sundar1992], later re-derived by
Pettie via a Davenport–Schinzel transcription [Pettie2008] and also studied by
Elmasry [Elmasry2004]. The deque/split analyses are tightly connected to the
*postorder path-compression* and union-find lineage — Lucas [Lucas1991,
Lucas1990], Loebl–Nešetřil [LoeblNesetril1997], and Buchsbaum–Sundar–Tarjan
[BuchsbaumSundarTarjan1995] — which is the source of the inverse-Ackermann
factor, itself originating in Tarjan's union-find analysis [TarjanUnionFind1975].
Key-independent and alternative-structure perspectives are due to Iacono
[Iacono2001, Iacono2005].

Our formalization is in Lean 4 [LeanMoura2021] over Mathlib [Mathlib2020]; the
companion blueprint uses [leanblueprint].

---

## 2. The Sequential Access Theorem (solved)

**Theorem (`Splay.sequential`, challenge file, no `sorry`, standard axioms).**
There is a constant `c` such that for every `n`, every `n`-node BST `init`
whose keys include `0,…,n-1`, accessing `one_to_n n = (0,1,…,n-1)` costs
`splay.sequence_cost init (one_to_n n) ≤ c·n`.

The constant obtained is small and explicit (`c = 26` suffices in the final
assembly; see below).

### 2.1 Proof architecture

The formalization follows the classical amortized argument, recast to fit the
top-down pairing variant and made fully constructive.

- **Min-splay reframing.** `sequence_cost_eq_seqCost` rewrites the fold for the
  sequential pattern as a recursive process cost `seqCost init n = Σₖ splay.cost
  (seqTree init k) k`, where `seqTree init k` is the tree after the first `k`
  accesses. Because each access is the current minimum, the accessed element is
  always the leftmost relevant node, and the process tracks a shrinking left
  region against a growing right structure.

- **Links as the amortization unit.** `splayLinks : BinaryTree → ℕ → ℕ` counts
  the rotation links on a splay path. The key inequality
  `two_splayLinks_le_cost : 2·splayLinks t q ≤ splay.cost t q` (proven by
  structural induction over the splay recursion's two-level cases) reduces the
  real cost to twice a link count.

- **A left-spine potential.** `omegaNB (T : List ℕ) (t : BinaryTree) : ℕ` is a
  non-branching potential on the touched keys and the right subtree's left
  spine. The development proves:
  - `omegaNB_base_le : omegaNB … ≤ 9·num_nodes` (initial potential is linear);
  - `omegaNB_step` / `omegaNB_growth` (per-access evolution);
  - `fresh_le_mu` (newly exposed nodes are paid for by potential / first-touch
    budget).

- **Telescoping.** `links_telescope` accumulates the per-step inequalities, and
  `totalLinks_le : Σₖ splayLinks (seqTree init k) k ≤ 13·n` collapses the
  telescope. Combining with `two_splayLinks_le_cost` gives
  `Σ cost ≤ 2·13·n = 26·n`, i.e. `sequential_access_theorem`, whence the
  challenge theorem.

### 2.2 Significance

This is, to our knowledge, a complete machine-checked proof of the Sequential
Access Theorem for the pairing-splay cost model with standard axioms only. It
is self-contained in `Challenge_Splay_Sequential.lean` (≈ 5,500 lines including
all supporting BST/list infrastructure).

---

## 3. The Deque bound: a sound reduction to one open lemma

The 50-point Deque problem asks for `O(n·α(n))`. We did **not** close it, but we
reduced it, with a fully machine-checked and independently audited chain, to a
single combinatorial residual. This section states precisely what is proved and
what remains.

### 3.1 The verified reduction chain

Define `tpLenN init X i`, the **touched-prefix length** of access `i`: the
number of nodes on the search path to `X i` that were already touched by a
previous access, taken as the leading (prefix) run. Define the named core:

> **`TouchedSumAlpha`** : `∃ c, ∀ (deque-class instance), Σᵢ tpLenN init X i ≤ c·n·α(n)`.

**Proved (Lean, standard axioms, audited — see §3.3):**

- `sequence_cost_eq_costSum_cast` : `splay.sequence_cost init X = (Σᵢ costN init X i : ℝ)`,
  where `costN init X i` is the per-access path-length-minus-one. This rests on
  two ZBK-kernel lemmas, both checked sorry-free:
  `splay_cost_eq_search_path_len_sub_one` (`splay.cost t q = search_path_len t q − 1`)
  and `sequence_cost_eq_process_sum` (the fold equals the sum over the process
  trees). **The cost target is the genuine `splay.sequence_cost`, not a proxy.**
- `costN_le_tp_add_fresh` : `costN init X i ≤ tpLenN init X i + freshN init X i`
  (the non-touched-prefix tail of any search path consists entirely of newly
  touched nodes — a consequence of *touched-prefix closure*: ancestors of
  touched nodes are touched).
- `Σᵢ freshN init X i ≤ n` (each node is first-touched at most once).
- Hence `Σ cost ≤ Σ tpLen + n`, and **`deque_challenge_CLOSED_of_touched :
  TouchedSumAlpha → ⟨verbatim 50-pt statement⟩`** is proved.

So the entire problem is reduced to bounding the touched-prefix sum.

### 3.2 Where the inverse-Ackermann lives

We then decompose `tpLenN` per access into an **in-block** part and an
**out-of-block** part relative to a block decomposition of the key space
(block size `B`), following the Pettie/Sundar recursion structure. The key
empirical and structural finding:

- **The out-of-block channel is linear.** Across a 64× scale sweep
  (`n = 1024 … 65536`) the out-of-block work per `n` is flat
  (`≈ 3.4 n`, no inverse-Ackermann growth). We reduce its bound, in Lean, to two
  linear residuals (`reaffiliationLinear`, `reentryPerSwitch` + a dedup term);
  the first-touch and side-switch sub-channels are proved unconditionally
  (`freshAffSum_le_n`, `switchSum_le_n`).
- **All the `α` is in the in-block recursion.** The total cost is `Θ(n·α(n))`
  empirically (cost/`n` = `7.21 → 7.32` over the 64× range — the textbook
  near-flat `n·α` signature), and the in-block part carries it.

We then built the recursion machinery:

- **`recursion_telescope`** (proved, standard axioms): an abstract
  "per-level-flat recurrence + `O(α)`-depth ⟹ `n·α` total" theorem. With a
  squaring block schedule `B_j = B_0^{2^j}` the recursion depth is
  `gammaOf squaring n ≤ α(n) + O(1)` (proved via `gamma_poly_alpha_proved`,
  whose explicit constant is `F_ω(c+4d+7)+1`).
- **`inblock_touched_eq_depth_projection`** (proved): the in-block touched count
  of an access equals the search-path length in the *restricted* tree
  `restrict T lo hi` (the BST induced on the block's key interval). This is an
  exact per-access identity (100% match empirically, no amortization).

### 3.3 The single open residual

> **`Blocking_inblock_recursion`** : `Σᵢ inBlockTp init X i ≤ Σ_b g(b)`, where
> `g(b)` is the touched-cost of block `b`'s sub-instance.

This is the in-block recursion step. `inblock_touched_eq_depth_projection`
("STEP 1") reduces it to bounding the *sum of depths in the evolving restricted
trees* by the per-block sub-cost ("STEP 2"). We established, empirically and by
a failed-potential analysis, that STEP 2 **genuinely is** the Sundar/Pettie
inverse-Ackermann argument: the restricted-tree sequence is a "drifting BST"
(splay does not commute with restriction; 15–43% per-step mismatch), the naive
logarithmic potential fails (gaps grow `~B log B`), and the correct bound
requires the same corridor old/young decomposition that constitutes the hard
direction of the deque bound. We did not close it.

### 3.4 Audit of the reduction

Because the reduction was assembled across several files (some by orchestrated
sub-agents), we audited its soundness directly:

1. **Statement match.** The proved conclusion is byte-identical to the shipped
   `theorem deque`.
2. **No shadowing.** No challenge primitive (`splay`, `splay.cost`,
   `sequence_cost`, `IsBST`, `avoids`, `num_nodes`, `toKeyList`, `alpha`) is
   redefined anywhere outside the shipped `Challenges/` directory.
3. **Real cost bridge.** The two ZBK bridge lemmas type-check against the genuine
   `splay.sequence_cost : ℝ` and print standard axioms.
4. **Clean capstone.** `deque_challenge_CLOSED_of_touched` compiles (0 errors,
   0 `sorryAx` in the whole 8,385-line file) with axioms
   `{propext, Classical.choice, Quot.sound}`.

Conclusion: **the reduction `TouchedSumAlpha → ⟨50-pt challenge⟩` is sound and
complete** — it is a genuine reduction of the actual problem, not an artifact of
definitional drift. (The remaining assembly `TouchedSumAlpha ⟸ residuals` has
its pieces proved and compiling, with one mechanical cross-file glue step, plus
the open `Blocking_inblock_recursion`.)

---

## 4. The Deque Conjecture (linear bound): an obstruction

The 100-point Deque Conjecture (Tarjan, in [SleatorTarjan1985]) asks for a
**linear** bound and is a long-standing open problem; Sundar's `O(n·α(n))`
[Sundar1992] remains the best known upper bound. We did not attempt to resolve
it, but we record a
concrete negative result useful for anyone attempting a potential-function
proof.

**The geometric-staircase obstruction.** We tested six distinct families of
constant-slack local-potential / local-witness arguments (corridor-length
potentials, raw/touched/weighted variants, several ledger schemes). Each is
falsified at scale by a "geometric-staircase" access pattern: roughly `log n`
keys remain undrained on one suffix at gaps `n/2, n/4, …, 1`, producing a margin
that grows by `≈ +2` per doubling of `n`. Nothing observable below `n ≈ 2048`
distinguishes these schemes from a correct one — the obstruction only manifests
asymptotically, which is itself a methodological warning. The detailed
falsification anatomies are recorded in the development notes.

This does not refute the conjecture; it shows the linear bound (if true) cannot
come from any constant-slack *local* potential of the forms we tried, consistent
with the difficulty of the problem.

---

## 5. The Traversal Conjecture (partial)

The Traversal Conjecture (accessing the elements of tree `T` in the preorder of
a second tree `S` costs `O(n)`) is reduced, in scratch developments, to three
structural hypotheses (`hstrict`, `hlower`, `hkernel`) via a potential-method
decomposition; compile-clean theorems close the conjecture *from* those three
hypotheses, and the upper block is done modulo a "budget-drop kernel." The
challenge theorem itself remains `sorry`. We flag this as a partial reduction,
not a result, since it has not been audited to the standard of §2–§3.

---

## 6. Methodology: simulator-guided formalization

A recurring theme — and the single most useful transferable lesson — is that
**every architectural decision was validated against an executable reference
implementation before being formalized.** A faithful Python model of the
pairing-splay process (`.tmp_alt_sim.py`) let us:

- test candidate invariants and potentials at scale (`n` up to 65536) in
  seconds, *before* committing Lean effort;
- distinguish true laws from small-scale coincidences (e.g. an `O(n·α)`
  quantity is indistinguishable from linear below the first Ackermann jump, so
  we discriminated structurally — by ratio against `#periods` vs against the
  total — rather than by magnitude);
- catch false lemmas early. Several plausible statements were *refuted* with
  explicit machine-checked witnesses before formalization (e.g. per-class
  meet-fiber bounds are false without the avoidance hypothesis; the
  "`MiddlesKeyAt 12` with a constant" bound is provably superlinear — it equals
  a third-order Davenport–Schinzel length `λ₃ = Θ(n·α)`).

This "probe first, prove second" loop repeatedly prevented wasted proofs and is,
we think, the right default for formalizing amortized data-structure analyses,
where the hard part is identifying the *correct* potential rather than checking
a known one.

A second component is a reusable **kernel library** (compiled as
`Challenges.ZBK`): the splay search-path calculus, touched-prefix closure,
positional-ancestry lemmas, the comb-shape structural theorem for the post-splay
prefix, the generation/last-touch machinery, and the cost-bridge lemmas. The
deque development is built entirely on this kernel.

---

## 7. Davenport–Schinzel layer (auxiliary, self-contained)

The deque analysis required an order-`s` Davenport–Schinzel (DS) toolkit
[DavenportSchinzel1965], which we developed as a self-contained module
(`CodexDS` namespace). DS sequences and their generalized/path-compression
variants [HartSharir1986, KlazarValtr1994, AdamecKlazarValtr1992] are the
combinatorial substrate of the Pettie transcription [Pettie2008]; the relevant
length bounds are the sharp `Θ(n·α(n))` of Agarwal–Sharir–Shor
[AgarwalSharirShor1989] at order 3 and the general-order bounds of Klazar
[Klazar1992]. Notable machine-checked results in our module:

- **`middlesKey_proved`**: the Hart–Sharir "middles" lemma at order 5 [HartSharir1986] — for an
  `ababa`-free context, the both-sided ("middle") symbols satisfy
  `|middleRaw| ≤ |middleSymbols| + #blocks`. Proved by an interval argument:
  distinct middle symbols cannot share non-first occurrence blocks (either
  ordering yields the forbidden alternation), so excess occurrences inject
  disjointly into the block range.
- **`affine_sound_positional`**: an unconditional positional one-step DS
  decomposition (local + boundary + middle), correcting an earlier
  list-equality-based formulation that fails on duplicate-content groups.
- **the `gammaOf` inverse-Ackermann arithmetic**: monotonicity and the
  poly-`α` collapse `gammaOf (β∘β) ≤ c'(α+1)`, with explicit constants.

We also recorded a clean negative result: the order-12 "middles" bound has **no
constant**, because the order-descent ladder reduces it to `BlockSeqLinear 10`,
a third-order DS length that is `Θ(n·α)`. This is *why* the inverse-Ackermann in
the deque bound must come from the recursion depth, not from a per-level DS
constant — a structural fact that took several iterations to pin down and that
constrains any future closure attempt.

---

## 8. What remains, stated precisely

For anyone continuing this work, the open obligations are sharp and localized:

1. **`Blocking_inblock_recursion`** (the one genuine core for the 50-pt Deque
   bound): `Σᵢ inBlockTp ≤ Σ_b g(b)`. Equivalent, via the proved depth-projection
   identity, to bounding `Σ depth(x_i, restrict T_i bkeys)` by the per-block
   sub-cost. This *is* the Sundar in-block recursion; closing it in Lean would
   be, as far as we know, the first formalization of the hard direction of the
   `O(n·α(n))` deque bound.

2. **The linear out-of-block residuals** (`reaffiliationLinear`,
   `reentryPerSwitch`, `carrierDedupLinear`): empirically linear, tractable
   corridor-counting arguments on already-proved machinery; closing them removes
   everything from the open set except (1).

3. **One mechanical glue step**: merging the kernel and telescope modules into a
   single importable unit so `recursionTelescopedBound_abstract` discharges the
   `RecursionTelescopedBound` hypothesis (the depth bound is already proved; it
   is currently in a sibling, non-importable module).

4. **The Deque Conjecture (linear)** and **the Traversal Conjecture**: open;
   for the former, no constant-slack local potential of the tested forms can
   work (§4).

---

## 9. Honest status summary

| Problem | Status | Axioms | Notes |
|---|---|---|---|
| **Sequential** | **SOLVED** | std | `Splay.sequential`, challenge filled, compiles |
| **Deque (50pt)** | **sound reduction** to 1 open lemma | std (for the proved chain) | `TouchedSumAlpha → challenge` proved & audited; `Blocking_inblock_recursion` open |
| Deque Conjecture (100pt) | open | — | constant-slack local potentials shown insufficient |
| Traversal | partial reduction (3 hypotheses) | — | challenge `sorry`; not audited |

The Sequential result is a genuine, self-contained, machine-checked theorem.
The Deque result is a genuine, audited, *sound reduction* — its value is that it
isolates the entire difficulty of a 30-year-old `O(n·α)` bound into one sharply
stated, empirically validated combinatorial lemma, with a complete verified
edifice (cost bridge, telescope backbone, channel decomposition, DS toolkit,
depth-projection identity) around it. We make no claim to have closed the Deque
bound, the Deque Conjecture, or the Traversal Conjecture.

---

## 10. Observations on model behavior

A companion section, `02_model_behavior_observations.md`, records an anecdotal
but (we think) interesting cross-model observation from this project: across the
frontier models that attempted these problems, **capability and calibration came
apart**. Models could close the *known-closable* problem (Sequential) yet were
most confident exactly on the *open/near-open* ones (the Deque bound and
conjecture), with expressed confidence tracking accumulated machinery rather
than true remaining difficulty — a pattern the present session exhibited too,
and which was corrected only by external mechanisms (refutation-first empirical
probing and an explicit soundness audit), never by the model's own judgment. See
that section for the detailed account and the methodological takeaways.

---

## References

Bibliographic entries are in `references.bib`; cited inline by key.

*Competition.* [ai4math2026track2] ICML 2026 AI for Math Workshop & Challenge 4
— ShadowBench. `https://www.codabench.org/competitions/16161/`

*Splay trees and the access conjectures.*
[SleatorTarjan1985] Sleator, Tarjan. *Self-Adjusting Binary Search Trees.*
J. ACM 32(3), 1985. •
[Tarjan1985sequential] Tarjan. *Sequential Access in Splay Trees Takes Linear
Time.* Combinatorica 5(4), 1985. •
[Sundar1992] Sundar. *On the Deque Conjecture for the Splay Algorithm.*
Combinatorica 12(1), 1992. •
[Pettie2008] Pettie. *Splay Trees, Davenport–Schinzel Sequences, and the Deque
Conjecture.* SODA 2008 (arXiv:0707.2160). •
[Elmasry2004] Elmasry. *On the Sequential Access Theorem and Deque Conjecture
for Splay Trees.* TCS 314, 2004.

*Dynamic optimality and lower bounds.*
[Demaine2004tango] Demaine, Harmon, Iacono, Pătrașcu. *Dynamic Optimality—
Almost.* FOCS 2004. •
[Wang2006] Wang, Derryberry, Sleator. *O(log log n)-Competitive Dynamic BSTs.*
SODA 2006. •
[Wilber1989] Wilber. *Lower Bounds for Accessing Binary Search Trees with
Rotations.* SICOMP 18(1), 1989. •
[Cole2000; ColeMishraSchmidtSiegel2000] Cole et al. *On the Dynamic Finger
Conjecture for Splay Trees, I & II.* SICOMP 30(1), 2000. •
[Iacono2001] Iacono. *Alternatives to Splay Trees with o(log n) Worst-Case
Access Times.* SODA 2001. •
[Iacono2005] Iacono. *Key-Independent Optimality.* Algorithmica 42, 2005.

*Path compression, union-find, and the inverse Ackermann factor.*
[TarjanUnionFind1975] Tarjan. *Efficiency of a Good but Not Linear Set Union
Algorithm.* J. ACM 22(2), 1975. •
[Lucas1990] Lucas. *Postorder Disjoint Set Union is Linear.* SICOMP 19(5),
1990. •
[Lucas1991] Lucas. *On the Competitiveness of Splay Trees.* DIMACS 7, 1991. •
[LoeblNesetril1997] Loebl, Nešetřil. *Linearity of Strong Postorder.*
J. Algorithms 23(2), 1997. •
[BuchsbaumSundarTarjan1995] Buchsbaum, Sundar, Tarjan. *Data-Structural
Bootstrapping, Linear Path Compression, and Catenable Deques.* SICOMP 24, 1995.

*Davenport–Schinzel sequences.*
[DavenportSchinzel1965] Davenport, Schinzel. *A Combinatorial Problem Connected
with Differential Equations.* Amer. J. Math. 87, 1965. •
[HartSharir1986] Hart, Sharir. *Nonlinearity of Davenport–Schinzel Sequences
and of Generalized Path Compression Schemes.* Combinatorica 6(2), 1986. •
[AgarwalSharirShor1989] Agarwal, Sharir, Shor. *Sharp Bounds on General
Davenport–Schinzel Sequences.* JCTA 52, 1989. •
[Klazar1992] Klazar. *A General Upper Bound in Extremal Theory of Sequences.*
Comment. Math. Univ. Carolin. 33(4), 1992. •
[KlazarValtr1994] Klazar, Valtr. *Generalized Davenport–Schinzel Sequences.*
Combinatorica 14(4), 1994. •
[AdamecKlazarValtr1992] Adamec, Klazar, Valtr. *Generalized Davenport–Schinzel
Sequences with Linear Upper Bound.* Discrete Math. 108, 1992.

*Formalization infrastructure.*
[LeanMoura2021] de Moura, Ullrich. *The Lean 4 Theorem Prover and Programming
Language.* CADE 2021. •
[Mathlib2020] The Mathlib Community. *The Lean Mathematical Library.* CPP 2020. •
[leanblueprint] Massot. *The Lean Blueprint Tool.*
`https://github.com/PatrickMassot/leanblueprint`
