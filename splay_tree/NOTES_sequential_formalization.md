# Formalization blueprint — Elmasry's Sequential Access Theorem → `Splay.sequential`

Direct proof of `splay.sequence_cost init (one_to_n n) ≤ c·n` with **no** dependency on
the open traversal/deque conjecture. Source: A. Elmasry, *On the sequential access theorem
and deque conjecture for splay trees*, TCS 314 (2004) 459–466 (PDF in `.tmp_literature/Elmasry.pdf`).
Since the repo's `splay.cost` counts **rotations**, the target reduces exactly to Elmasry's
`≤ 4.5n` and gives `c = 4.5`.

Working file: `.tmp_claude_sequential.lean` (foundation compiles, no `sorry`).
This is a large, multi-session build; the plan below is bottom-up so every step compiles.

## Reduction overview

`sequence_cost init (one_to_n n)` = Σ over `i=0..n-1` of `splay.cost Tᵢ i`, where
`Tᵢ` = tree after accessing `0..i-1`. `splay.cost = #rotations`. Elmasry bounds the total
rotations by `4.5n`, hence `sequence_cost ≤ 4.5n`.

## Component A — reframing (the min-splay / splaying-spine process)

**Claim.** After accessing `0..i-1`, `Tᵢ = node(Lᵢ, i-1, Rᵢ)` (for `i≥1`), the left part
`Lᵢ`/root is never touched again, and accessing `i` splays the leftmost node of `Rᵢ₋₁`.
Track only `Rᵢ` (the *remaining tree*) and the **splaying spine** = its left spine.

Lean targets:
- `def remainingTree : BinaryTree → ℕ → BinaryTree` — `Rᵢ` after `i` min-splays.
- `seqInvariant i Tᵢ` — structural invariant (root = `i-1`; right subtree = `Rᵢ`; keys split).
- `seqInvariant_step` — `seqInvariant i Tᵢ → seqInvariant (i+1) (splay Tᵢ i)`; the access of
  `i` goes right (since `i > i-1 = root`) to the min of `Rᵢ₋₁`, splays it up, and the old
  root + left part fall into the new left subtree.
- `cost_eq_min_splay_cost` — `splay.cost Tᵢ i = 1 + (cost of min-splay within Rᵢ₋₁)` (the `+1`
  for descending past the root), summing the `+1`s to `≤ n`.
- `sequence_cost_eq_spine_rotations` — `sequence_cost init (one_to_n n) = totalRotations(process)`.

*This is the crux foundational layer — pure splay-behaviour reasoning. Hard but `sorry`-free
once the splay case analysis (q>root ⇒ recurse right) is in place.*

## Component B — coloring (auxiliary state)

`inductive Color | yellow | green | black` and a `coloring : ℕ → (Nat → Option Color)`
indexed by time `t` (after splay `t`). Rules (Elmasry):
- uncolored node joining the splaying spine → `yellow`;
- `yellow` linked to another node → `green`; `green` linked to a `yellow` → that yellow → `green`;
- any node on the tree's right spine → `black` (overrides).
Invariants to prove: spine nodes are yellow/green; once green stays green; parent of a colored
node is colored; freshly-yellow nodes are the deepest spine nodes.

## Component C — counting functions

After splay `t`, for a node `x`:
- `g x t` = #colored nodes on `x`'s right spine; `h x t` = #colored on left-child's right spine;
- `v x t = g x t − h x t`; `g x 0 = h x 0 = 0`.
Relations to prove for `w` linked to its left child `z` at step `t+1` (Elmasry (1)–(5)):
`h w t = g z t`; `g w (t+1)=g w t`; `h w (t+1)=h w t − 1`; `g z (t+1)=g w t + 1`;
`h z (t+1) ≤ h z t + 1` (equality except `z=x₂`, where it is `h z t − 1`).

## Component D — Lemma 1 (the invariant)

`vx_nonneg` : `v x t ≥ 0` for any yellow/green `x`; and `vz_mono` : when a green `w` is
linked to `z` at `t+1`, `v z (t+1) ≥ v z t`. Proof: induction on a node's lifetime; base
case at yellowing (`g=1, h=1`, or `h=0` for the deepest); step via (1)–(5) and `vw≥0`.

## Component E — link count = total rotations ≤ 4.5n

Every rotation is a "link". Partition and bound:
- **black** links (right-spine node, ≤ 1 per splay): ≤ `n`;
- **yellow→green** (yellow-to-yellow / yellow-to-green / green-to-yellow, each turns a yellow
  green, monotone): ≤ `n`;
- **green-green A-links** (`v z = 1`): each `z` gains ≤ 1 child before `v z ≥ 2` (by `vz_mono`): ≤ `n`;
- **green-green B-links** (`v z ≥ 2`): credit accounting. Invariant: node `x` holds `h x t² / 2`
  credits. Released credit `d = (h_z²+h_w² − h_z'²−h_w'²)/2 ≥ h_w − h_z − 1 = v_z − 1 ≥ 1`.
  Allocate `1.5` credits per node at yellowing (`1` for the `v_z=0` maintenance + `0.5` for the
  initial `h²/2=1/2`). Total ≤ `1.5n`.

Total ≤ `n + n + n + 1.5n = 4.5n`.

## Component F — assemble

`totalRotations ≤ 4.5n` (E) + `sequence_cost = totalRotations` (A) ⇒
`sequence_cost init (one_to_n n) ≤ 4.5 * n`; then `sequential` with `c = 4.5`, replacing the
repo's proof that routes through `deque_conjecture`/`traversal_conjecture`.

## Status / risk

### Component A — COMPLETE & VERIFIED (`.tmp_claude_hlower_drop.lean`, all `#print axioms` = `[propext, Classical.choice, Quot.sound]`, no `sorryAx`)

The reframing and the **goal reduction** are fully proved. The challenge goal is now
machine-checked equivalent to a single explicit sum bound:

| Lemma | Statement |
|---|---|
| `seqTree` (def) | `seqTree init 0 = init`; `seqTree init (k+1) = splay (seqTree init k) k` (the sequential process) |
| `seqTree_toKeyList` | keys preserved: `(seqTree init k).toKeyList = init.toKeyList` |
| `seqTree_isBST` | BST preserved through the process |
| `seqTree_rootKey` | root-is-last-accessed: `rootKey (seqTree init (k+1)) = some k` (for `k<n`) |
| `tree_eq_node_of_rootKey` | `rootKey t = some m → t = node (leftSubtree t) m (rightSubtree t)` |
| `splay_cost_node_right_indep_left` | for `k<q`: `splay.cost (node L k R) q = splay.cost (node empty k R) q` |
| `seq_access_cost_eq` | **cost isolation**: the `k`-th access cost `= splay.cost (node empty (k-1) Rₖ) k` (depends only on the right subtree `Rₖ`) — Elmasry's "track only the right subtree" |
| `sequence_cost_eq_seqCost` | **bridge**: `sequence_cost init (one_to_n n) = seqCost init n` (foldl-over-`finRange` ⇒ recursive process; via `map_coe_finRange`+`foldl_map`+snoc induction) |
| `seqCost_eq_sum`, `sequence_cost_eq_sum` | **goal reduction**: `sequence_cost init (one_to_n n) = Σ_{k<n} splay.cost (seqTree init k) k` |

**Net effect:** `Splay.sequential` (the `≤ c·n` goal) is now machine-equivalent to
`∑ k ∈ Finset.range n, splay.cost (seqTree init k) k ≤ c·n`. The reframing has no remaining gap.

Plumbing (also done & verified):
| `seqTree_num_nodes` | the process preserves `num_nodes` |
| `rightSubtree_seqTree_succ_mem_iff` | the remaining right subtree `Rₖ₊₁` holds **exactly** the keys `> k` (`x ∈ Rₖ₊₁.toKeyList ↔ k < x ∧ x ∈ init.toKeyList`) |

⚠️ **KEY FINDING (verified by counterexample, `/tmp/verify_recur.lean`): the naive structural
recursion `Rₖ₊₁ = rightSubtree (splay Rₖ k)` is FALSE.** On `R` = left-spine `6(5(4(3)))`,
`m=2`, `k=3`: splaying `3` in `R` alone yields right subtree `5(4,6)` (balanced), but splaying
`3` in `node L 2 R` yields right subtree `6(4(_,5),_)` (left-leaning) — *different trees*.
Reason: splay pairs its zig-zig/zig-zag rotations **bottom-up from the access point**, so
prepending the root `m` flips the pairing parity along the path. **Consequence for B–E:** the
"remaining tree" is characterized by its *key set* (above), NOT by a clean per-step splay shape.
This is precisely *why* Elmasry needs the coloring/charging machinery instead of a structural
induction — the right-subtree shape is not recursively determined.

### Charging reduction — DONE & VERIFIED (M1–M2.5, compile-clean, std axioms)

The goal is now reduced (machine-checked) to a single combinatorial spine-sum:

| Lemma | Statement |
|---|---|
| `sequence_cost_eq_search_path_sum` (M1) | `sequence_cost init (one_to_n n) = (∑_{k<n} search_path_len (seqTree init k) k) − n`. So `≤ c·n` ⟺ `∑ search_path_len ≤ (c+1)·n` (rotations = depth, via `splay_cost_add_one_eq_search_path_len_of_mem`). |
| `search_path_len_seqTree_eq_succ` (M2) | for `k≥1` (root `=k−1`): `search_path_len (seqTree init k) k = 1 + search_path_len (rightSubtree (seqTree init k)) k`. |
| `leftSpine` (def) + `search_path_len_min_eq_leftSpine_length` (M2.5) | for the min `q` of a BST `t`: `search_path_len t q = (leftSpine t).length`. |

**Net:** `Splay.sequential` ⟸ `∑_{k<n} (leftSpine (rightSubtree (seqTree init k))).length ≤ C·n`
— the **total splaying-spine length over the process**. Empirically `≈ 3.3n` (worst case = left
spine); the repo's full sequential cost is `≈ 5.35n` (NOT Elmasry's 4.5 — repo `cost`=depth-sum,
a different metric, so the constant differs but the technique still applies). Any constant closes
the challenge.

**Empirical: NO potential shortcut for the spine-sum (confirmed `/tmp/explore_pot.py`).** Tested
`Φ=∑ₓ h_x²/2` (Elmasry's credit, uncolored), `∑ₓ h_x`, `∑ₓ rspine(x)²/2` as direct tree
potentials on the actual `Rₖ` process — all have per-step slack growing `~n` (fail). Reason: the
structural mismatch `Rₖ₊₁ ≠ rightSubtree(splay Rₖ k)` (rotation-pairing parity) means the credit
must be maintained on the *actual* process with the coloring (black/right-spine exclusion is
load-bearing). So the dynamic coloring is genuinely required; it cannot be replaced by a static
potential on the tree.

### NEW MATH (this session): the halving + entrant decomposition — engine lemmas PROVEN

⚠️ **Discovery: the repo's `splay` is NOT standard splay.** Its recursion fixes zig-zig pairs
**top-down from the root** (standard splay pairs bottom-up from the accessed node). Hence the
repo's sequential cost ≈ 5.35n ≠ Elmasry's 4.5n, and Elmasry's relations (1)–(5) cannot be
transcribed verbatim — the math must be re-derived for this variant. (Also tested: touched-
restricted linear/quadratic cargo potentials still fail, slack ~n/4; the conservation identities
`s_{k+1} = s_k − 1 − pairoffs + e_k`, `E' = C₀ + P` are exact, so no identity-only bound exists.)

For **min-splay** (each sequential step's core), the repo's top-down recursion is CLEAN:
`spine'(t) = lk :: spine'(ll)` (root drops, second node survives, recurse two levels down).
This yields two compile-clean structural lemmas (std axioms, in `.tmp_claude_hlower_drop.lean`):

| Lemma | Statement |
|---|---|
| `minCargo` (def) | right subtree of the minimum node |
| `leftSpine_rightSubtree_splay_min_subset` | **entrant source**: new spine ⊆ old spine ∪ `leftSpine (minCargo t)` (verified empirically 0 violations first, then proven) |
| `leftSpine_rightSubtree_splay_min_length` | **halving**: `2·s' ≤ s + 2·e` with `s' = new spine len, s = old, e = |leftSpine (minCargo t)|` |

**Consequence** (unrolling `s' ≤ s/2 + e`): `∑ₖ sₖ ≤ 2·s₀ + 2·∑ₖ eₖ ≤ 2n + 2E`. The 50-pt goal
is reduced to ONE remaining quantity: **`E = ∑ₖ |leftSpine (minCargo)| ≤ C·n`** (total entries),
plus a wrapper transferring min-splay lemmas to the real per-step shape (`node(L', k-1, Rₖ)`,
one zag at root then min-splay inside — same case analysis, mild).

### MASTER REDUCTION — PROVEN (compile-clean, std axioms)

The full chain is now machine-checked. `sequence_cost_le_four_n_add_two_entries`:

```
sequence_cost init (one_to_n n) ≤ 4n + 2E,   E := ∑_{k∈[1,n)} eSeq init k
                                              eSeq k = |leftSpine (minCargo Rₖ)|
```

via: `real_halving` (per-step `2s' ≤ s + 1 + 2e` for the actual shape `node(L,k-1,R)`, one
zag/zagZig at the root + min-splay inside, reusing the min-splay halving), `sSeq_halving`
(instantiated on the process), `sum_halving_unroll` (arithmetic unrolling), `leftSpine_length_
le_num_nodes`, head-step `cost₀ ≤ n`. **The 50-pt challenge is now exactly ONE lemma away:
`E ≤ C·n`.** Empirically `E/n ≈ 1.45` (slowly converging; conjecture `E ≤ 2n`, then c = 8).

### CREDIT MACHINE — spec fully validated + first Lean pieces landed

**Alignment resolved (zero violations at all n):** touched = ever-on-spine; **black = ever-on-
`rightSpine Rₖ`** (the missing exclusion that caused earlier v<0 flags); `g x` = #touched on
`rightSpine`(subtree x); `h x` = #touched on `rightSpine`(left child x). Verified exactly:
Lemma 1 (`v = g−h ≥ 0`, touched non-black); **A-links ≤ 1 per node**; strengthened monotonicity
`v_z' ≥ v_z + v_w` at green-green links; `h ≤ 1` at first touch; no h-jump > +1 ever.

**Lean landed (compile-clean):** `touchedCount` (+ cons lemmas), `touchedKeys` process set
(+ `spine_subset_touchedKeys`, `touchedKeys_mono`), `rightSpine_node_eq` (relation (1) is
definitional: w's h-chain *is* z's g-chain), **`relation3_zigzig`** (`h_w' = h_w − 1`),
**`relation4_zigzig`** (`g_z' = g_w + 1`).

**SIMPLIFIED ENDGAME (links formulation — E and cargo-conservation BYPASSED):**
per-pair potential arithmetic: `ΔΦ_pair = (h_z+1)²/2 − h_z²/2 + (h_w−1)²/2 − h_w²/2 =
h_z − h_w + 1 = 1 − v_z` (using relation (1)). So:
- `cost = 2·links + n` — immediate from the cost recursion (zig-zig level = 1 link = cost 2).
- `links = Y + A' + B + black-links`; `Y ≤ greenings ≤ n`; `A'`(green-green, v≤1) `≤ n`
  (once-per-node, via v-monotonicity); `black ≤ 1/splay ≤ n`; `B`(v≥2) pays itself: `ΔΦ ≤ −1`
  per B-link, `Φ₀ = 0`, Φ-injections ≤ 1.5/touch + 1/Y-or-A'-link ⇒ `B ≤ 3.5n`.
- Total: `links ≤ 6.5n` ⇒ **`cost ≤ 14n`** (constants loose; any constant closes).

**Remaining formal blocks:** (F1) per-splay aggregated Φ-change (induction over the zig-zig
recursion; per level = relations (3)+(4) already proven + frozen-blocks argument), (F2) Lemma 1
process induction, (F3) A'-once-per-node, (F4) Y ≤ greenings, (F5) black ≤ 1/splay, (F6) cost =
2·links + n + assembly. No conceptual gaps; ~1–2 focused weeks of Lean.

**UPDATE — F6 DONE, all five relations machine-checked (compile-clean, std axioms):**
- `splayLinks` (def, mirrors the cost recursion), `splay_cost_le_two_mul_splayLinks_add_one`
  (per splay, explicit-recursion style — `fun_induction` chokes on opaque match scrutinees),
  **`sequence_cost_le_two_mul_links_add_n`**: `sequence_cost ≤ 2·totalLinks + n`. The challenge
  is now literally `totalLinks ≤ C·n`.
- `hSqPotential` (the doubled credit potential `Σ h²`, ℕ-valued, `Φ₀ = 0`),
  `hsq_pair_change` (the per-link `(h_z+1)² + (h_w−1)²` arithmetic, B-link payment).
- **`relation5_touchedCount_rightSpine_splay_min`** — relation (5) proven: the touched count on
  `rightSpine (rightSubtree (splay t q))` grows ≤ 1 per min-splay (zig-zig: exactly +1 via
  touched survivor; zig: 0; root: −1, the x₂-exception). NON-recursive (three shapes suffice).
  Applied to the subtree `ll` under a survivor `z`, this is exactly `h_z(t+1) ≤ h_z(t) + 1`.
- Relations (1) and (2) are *definitional* in these coordinates: (1) the dropped parent's
  h-chain is literally the survivor's g-chain (same list, `rightSpine_node_eq`); (2) the dropped
  parent keeps its right subtree, so its g-chain `k :: rightSpine r` is unchanged by the link.

Remaining: F1 (the aggregated per-splay Φ identity — next, the big induction; per-level pieces
all proven now), F2 (Lemma 1 process induction), F3–F5 (counters), assembly.

**UPDATE — F1 per-level toolkit COMPLETE (compile-clean, std axioms):**
- `splay_min_zigzig_shape` — the zig-zig splay shape extracted standalone (given branch
  conditions + min-normal-form of the recursive call).
- **`hSqPotential_exchange_zigzig`** — the *exact* ℕ exchange equation at one zig-zig level
  (no `T`-hypotheses, no invariants): only the dropped parent's h-term
  (`tc(lk :: rs lr)² ↦ tc(rs lr)²`) and the survivor's h-term (`tc(rs ll)² ↦ tc(rs M)²`,
  the recursive subproblem) change; all other nodes are frozen blocks.
- `hSqPotential_exchange_root` (Φ unchanged) and `hSqPotential_exchange_zig` (the
  `x₂`-exception swap `tc(q :: rs lr)² ↦ tc(rs lr)²`) — the two boundary cases.
- `touchedCount_nil`.

The remaining F1 step: the **unrolled per-splay Φ-bound** — chain the exchange equations down
the recursion, applying relation (5) (`Z_new ≤ Z_old + 1`) and `touchedCount_cons_of_mem`
(`W_old = W_new + 1`, spine nodes touched) per level; the per-level net is `2(1 − v_z)`, so the
unroll needs the v-classification (cheap `v≤1` vs B `v≥2`) threaded through the induction, with
Lemma 1 (F2, `v ≥ 0`) as the process invariant. Dependency order: F2 before (or jointly with)
the unrolled F1.

**UPDATE — F2 state + engine landed; augmented invariant DISCOVERED & VALIDATED:**
The bare `v ≥ 0` is NOT inductive through *release* events (the touched/untouched boundary on a
released cargo chain: the first untouched member gets touched, bumping the `h` of the touched
node above it). Inductive strengthening (mine): **boundary-readiness** — `v_x ≥ 1` whenever the
head of `x`'s h-chain is untouched. Validated empirically in the exact Lean formulation
(`vInvariantNB`: full-check left subtrees along the right chain, blacks exempt): **0 violations
at all n** (`/tmp/check_augmented.py`). Event-by-event re-establishment verified on paper:
fresh yellowing → `v = 0`/touched-head (deepest: `v = 1`/no head); dropped parent → `v' = v+1 ≥ 1`
(covers exposed head, rel (3)); survivor → `v' ≥ v_z + v_w ≥ 0`, touched head; base survivor →
`v' = v+1 ≥ 1` (covers the absorbed cargo's possibly-untouched head); release consumes the bit.
Lean landed (compile-clean): `boundaryBit`, `vAt`, `vInvariantFull`, `vInvariantNB`,
`vInvariantFull_of_untouched` (untouched blocks vacuous), **`vjump_zigzig`** (the engine:
`v_z' ≥ v_z + v_w` in ℕ form from relation (5) + cons-counting).
Next: the per-splay preservation induction (`vInvariantNB` through one splay + T-growth), then
the process wrap: `∀ k, vInvariantNB (touchedKeys init k) (rightSubtree (seqTree init k))`.

**UPDATE — RELEASE EVENTS PROVEN (6-agent parallel fan-out, all integrated, compile-clean):**
- `touchedKeys` corrected: accumulate from step 1 (step 0's `leftSpine R₀` is not an access
  path; including it falsifies `touchedClosed` — caught by counterexample, both invariants
  re-validated at 0 violations with the corrected def).
- Integrated (std axioms): `forallTree_mem`, `touchedCount_mono_T` / `_frozen` / `_zero`,
  `boundaryBit_frozen`, `rightSpine_subset_toKeyList`, `vInvariantFull_frozen`,
  `touchedClosed` (def) + `_of_untouched` + `_frozen`, **`vInvariantFull_release`** (the heart:
  the cargo-chain release re-establishes the invariant, with the boundary bit paying the
  touched/untouched boundary exactly), **`touchedClosed_release`**, `boundaryBit_le_one`,
  `touchedKeys_succ_diff`.
- Remaining F2 (case design verified on paper, recorded in memory): the main per-splay
  preservation lemma (root case done = release; zig and zigzig cases consume the proven
  pieces + relation (5)), the `touchedClosed` splay-preservation, the NB wrapper, and the
  process induction. Then the F1 unroll and the counters.

### The wall (updated): the entries bound `E ≤ C·n` — superseded by the links formulation above

Counting alone provably cannot bound `E`: the conservation identities are exact
(`C₀ + s₀ = n`, `P = s₀ + E − n`, `E = C₀ + P`; every drop ⇒ exactly one later re-entry, LIFO
cargo release), so all counting relations cancel — the bound is genuinely credit-theoretic.
**Elmasry's relations (1)–(5) DO transfer to the repo variant** (hand-derived from the proven
zig-zig restructuring: cargo′(survivor) = node(old-cargo, dropped-parent, parent-cargo) gives
(1) h_w = g_z, (2) g_w′ = g_w, (3) h_w′ = h_w−1, (4) g_z′ = g_w+1; (5) needs care at the
recursion boundary). Formalization plan: time-indexed touched-set + g/h counts on right spines,
relations as local lemmas (same case-analysis style as the proven halving), Lemma 1 (v ≥ 0),
link classification + h²/2 credit ⇒ `E ≤ Cn`. Mechanical but large (the genuine multi-week
block).

Empirically `E/n → ~2`. First-entries ≤ n trivially; re-entries need the credit/charging idea
(cargo mechanics: pairing prepends partners to cargo spines; consumption releases them). No
static potential works (tested exhaustively, incl. touched-restricted). This is the one
genuinely-open formalization core left; it is where Elmasry-style accounting (adapted to the
top-down variant) must be built.

No shortcut exists: the trivial per-access bound is `≤ n` each ⇒ `Σ ≤ n²` (not linear); every
per-step potential provably fails (documented). A real linear `c` *requires* Elmasry's global
amortized accounting (B coloring + C g/h/v counting + D Lemma 1 + **E** the `h²/2` credit
accounting). E is the single hardest piece and is research-formalization-grade.

### Earlier foundation
- Foundation (`one_to_n` facts, `splay_cost_nonneg`, `sequence_cost_nonneg`): **done, compiles** (`.tmp_claude_sequential.lean`).
- Component A first lemma — **`splay_min_eq_node_empty`** (min-splay normal form `splay t q = node empty q R`), proved reusing the repo's `splay_rootKey_eq_some_of_mem_isBST` + `splay_leftSubtree_empty_of_min_isBST`; compiles, axioms `[propext, Quot.sound]` (in `.tmp_claude_hlower_drop.lean`, the snapshot that carries the foundational splay infra). - Component A, lemma 2 — **`splay_cost_node_right_indep_left`**: for `k < q`, `splay.cost (node L k R) q = splay.cost (node empty k R) q` (the access cost ignores the accumulating left subtree). Compiles, standard axioms.
Remaining A: the sequential structural invariant (`Tₖ = node(L,k-1,Rₖ)`, `Rₖ` a BST on `{k..n-1}`); `rightSubtree`-shed-left (the next right subtree depends only on `Rₖ`); the cost reframing `sequence_cost = Σ rotations` of the min-splay process.
Then the hard cores: **B–D** (coloring state model + `g/h/v` + Lemma 1) and **E** (the `h²/2` credit accounting). E is the single hardest piece.
- A (reframing) and E (accounting) are the two heavy components; B–D are mechanical given a
  faithful time-indexed coloring/state model.
- Honest estimate: multi-week, ~2–5k lines. No conceptual gap (unlike the traversal route's
  open "arbitrary-initial lift"); it is "only" a large formalization of a known, complete proof.
