# Formalization Blueprint: `topology/L2/top_gen_L2_019`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Source Documents and Support Files Read

- `docs/source.tex` via `formalization_document_inspect`; theorem block `line-17`, proof lines 19-50.
- Preflight manifest: `.epflemma/workflow-state/formalization/docs-source/manifest.json`.
- Planner context: `.epflemma/workflow-state/formalization/docs-source/context.md`.
- Companion instructions: `docs/instructions.md`.
- Candidate skeleton inventory: `docs/skeletons/README.md`.
- Candidate skeleton files: `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, `Skeleton3.lean`, `Skeleton4.lean`.
- No project-local PDFs, figures, bibliography files, citations, or cross-references were listed in the manifest.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the source-backed theorem statement `isTotallyDisconnected_cantorSet` with a `by sorry` proof placeholder for the later proof workflow.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so project-level builds cover the generated target module.

## Import Plan

Direct Lean imports for `ShadowBench/Source/Main.lean`:

```lean
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Perfect
```

Import notes:

- `Mathlib.Topology.Instances.CantorSet` provides the Mathlib ternary Cantor set `cantorSet : Set ℝ`, `isClosed_cantorSet`, `isCompact_cantorSet`, and the bridge homeomorphism `cantorSetHomeomorphNatToBool`.
- `Mathlib.Topology.Connected.TotallyDisconnected` provides `IsTotallyDisconnected`, `TotallyDisconnectedSpace`, `Pi.totallyDisconnectedSpace`, and `totallyDisconnectedSpace_subtype_iff`.
- `Mathlib.Topology.Perfect` provides the topological set predicate `Perfect` and its closed-plus-accumulation-point characterization.

## Suggested Search Modules

These are proof-search hints only; they are not part of the direct import plan unless a later proof turn needs them.

- `Mathlib.Topology.MetricSpace.PiNat` (candidate skeleton/import hint for countable products).
- `Mathlib.Topology.Homeomorph.Lemmas` (homeomorphism invariance of total disconnectedness, e.g. `Homeomorph.totallyDisconnectedSpace`).
- `Mathlib.Topology.Separation.Profinite` (possible totally separated/profinite route if needed).
- Existing declarations to search first: `cantorSetHomeomorphNatToBool`, `Pi.totallyDisconnectedSpace`, `totallyDisconnectedSpace_subtype_iff`, `isClosed_cantorSet`, `Perfect`, `perfect_def`, `preperfect_iff_nhds`.

## Search Log

- `lean_search "CantorSet"`: Mathlib uses lowercase `cantorSet : Set ℝ`; also found `isClosed_cantorSet`, `isCompact_cantorSet`, `cantorSetEquivNatToBool`, and `cantorSetHomeomorphNatToBool`.
- `lean_search "IsTotallyDisconnected ..."`: found `IsTotallyDisconnected`, `TotallyDisconnectedSpace`, `Pi.totallyDisconnectedSpace`, `totallyDisconnectedSpace_subtype_iff`, and embedding/homeomorphism transfer lemmas.
- `lean_search "Perfect cantorSet"`: found the topological predicate `Perfect`; no topological `IsPerfect` predicate was found. Skeleton uses `IsPerfect`, which is stale for this Mathlib version.
- Local skeletons all preserve the required theorem name and the conjunction shape, but use stale identifiers (`CantorSet`, `IsPerfect`) and `Skeleton4.lean` has a malformed duplicate `:= by sorry`. The final statement adopts the theorem name and conjunction intent, correcting identifiers to Mathlib names.

## Required Names

- `isTotallyDisconnected_cantorSet`

## Detected Theorem-Like Blocks

1. `line-17` (theorem, lines 17-19) - isTotallyDisconnected_cantorSet

## Source Map

- line-17 -> `isTotallyDisconnected_cantorSet` (`docs/source.tex` lines 17-19; proof lines 19-50)

## Source inventory

- label: line-17
  source_id: line-17
  kind: theorem
  source_title: isTotallyDisconnected_cantorSet
  planned_lean_declaration: isTotallyDisconnected_cantorSet
  source_locator: docs/source.tex lines 17-19, proof lines 19-50
  details: Full statement-fidelity details and prover notes are in the matching source statement inventory entry below.

## Source Statement Inventory

### line-17

- Source inventory entry: `line-17`
- Source title: theorem `isTotallyDisconnected_cantorSet`.
- Planned Lean declarations: `isTotallyDisconnected_cantorSet`
- Adopted statement shape:

```lean
theorem isTotallyDisconnected_cantorSet :
    IsTotallyDisconnected cantorSet ∧ Perfect cantorSet := by
  sorry
```

- Source inventory entry: `line-17`.
- Source locator: `docs/source.tex`, theorem environment lines 17-19; proof lines 19-50.
- Source statement: “Prove that the Cantor set $\mathcal{C}$ is totally disconnected and perfect.”
- Skeleton candidate used: `Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` shaped the required name and top-level conjunction only. The final statement corrects their stale identifiers from `CantorSet`/`IsPerfect` to Mathlib’s `cantorSet`/`Perfect`. `Skeleton4.lean` was rejected as syntactically malformed.
- Dependencies:
  - `cantorSet : Set ℝ` from `Mathlib.Topology.Instances.CantorSet`.
  - `IsTotallyDisconnected` and `TotallyDisconnectedSpace` infrastructure from `Mathlib.Topology.Connected.TotallyDisconnected`.
  - `Perfect` from `Mathlib.Topology.Perfect`.
  - Proof-level bridge declarations expected later: `cantorSetHomeomorphNatToBool`, `Pi.totallyDisconnectedSpace`, `Homeomorph.totallyDisconnectedSpace`, `totallyDisconnectedSpace_subtype_iff`, `isClosed_cantorSet`, and the `Perfect` accumulation-point characterization.
- Formal statement review:
  - The source theorem has no free parameters or hypotheses; the Lean theorem has none.
  - The source object is the Cantor set as a subset/subspace of the real line; the Lean object is Mathlib’s standard ternary Cantor set `cantorSet : Set ℝ`.
  - The source claims exactly two topological properties, “totally disconnected” and “perfect”; the Lean theorem states exactly the conjunction `IsTotallyDisconnected cantorSet ∧ Perfect cantorSet`.
  - The source describes total disconnectedness in component/subspace language. Lean states the set predicate `IsTotallyDisconnected cantorSet`; Mathlib’s `totallyDisconnectedSpace_subtype_iff` is the available bridge between this set predicate and `TotallyDisconnectedSpace` for the subspace type `cantorSet`.
  - The source defines perfect as closed with no isolated points. Lean’s `Perfect` predicate is closed plus every point is an accumulation point, matching the standard “closed and no isolated points” definition for this nonempty set.
- Source qualifiers:
  - Mathematical object class: the standard ternary Cantor set `𝓒`, considered as a subset of `ℝ` and equivalently as its induced subspace.
  - Quantifier order: no explicit quantified variables; the theorem is a closed proposition about the canonical Cantor set.
  - Parameter domain: none.
  - Output codomain/proposition: a conjunction of propositions, first total disconnectedness and second perfectness.
  - Equality/image/bridge conditions: the proof uses a homeomorphism `e : 𝓒 → {0,1}^ℕ`; Mathlib supplies `cantorSetHomeomorphNatToBool : cantorSet ≃ₜ (ℕ → Bool)` as the representation bridge from the real Cantor set to binary sequences.
  - Side conditions: none stated beyond the usual topology on `ℝ`, the induced subspace topology on `cantorSet`, and the product topology on the binary sequence space used in the proof.
  - Follow-on proof claims: closedness of `𝓒`, no isolated points of `𝓒`, total disconnectedness of products of two-point discrete spaces, and clopen-cylinder separation of distinct binary sequences. These are proof ingredients for the two theorem clauses, not additional source theorem conclusions.
- Lean coverage:
  - Object class covered by `cantorSet : Set ℝ` from `Mathlib.Topology.Instances.CantorSet`.
  - Total disconnectedness clause covered by `IsTotallyDisconnected cantorSet`; the subspace/component interpretation is covered by the existing Mathlib bridge `totallyDisconnectedSpace_subtype_iff`.
  - Perfectness clause covered by `Perfect cantorSet`, whose definition records closedness plus accumulation/no-isolated-point behavior.
  - The proof’s representation bridge is covered by the existing declaration `cantorSetHomeomorphNatToBool : cantorSet ≃ₜ (ℕ → Bool)`; no new bridge definition is needed for statement fidelity.
  - The source proof’s closedness, no-isolated-point, product, and clopen-cylinder claims are recorded as prover notes and dependency hints, not as separate source theorem obligations.
- Scope changes: no theorem-scope change. Notational/representation choices only: informal `\mathcal C` is represented by Mathlib’s lowercase `cantorSet`, and the binary product `{0,1}^ℕ` is represented by the homeomorphic Bool-sequence space `ℕ → Bool` through `cantorSetHomeomorphNatToBool`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text:

```tex
Let $X = \{0, 1\}^\mathbb{N}$ be the space of infinite sequences of $0$s and $1$s, equipped with the product topology (where $\{0, 1\}$ has the discrete topology). It is a standard result in topology that the Cantor set $\mathcal{C}$ is homeomorphic to $X$ via a map $e: \mathcal{C} \to X$. We use this homeomorphism to prove the required properties.

\paragraph{1. Perfect:}
A set is perfect if it is closed and has no isolated points.
\begin{itemize}
    \item \textbf{Closed:} The space $X = \{0, 1\}^\mathbb{N}$ is a product of compact spaces, so it is compact by Tychonoff's theorem. Since $X$ is a compact subset of a Hausdorff space, it is closed. Since $\mathcal{C} \cong X$, $\mathcal{C}$ is also closed in $\mathbb{R}$.
    
    \item \textbf{No isolated points:} Let $x \in \mathcal{C}$ be any point and $U$ be an arbitrary open neighborhood of $x$. We must show there exists $z \in U \cap \mathcal{C}$ such that $z \neq x$.
    Through the homeomorphism $e$, $e(x)$ is a sequence $(s_1, s_2, \dots)$. By the definition of the product topology, there exists a "cylinder set" $W \subset e(U)$ such that:
    \[ W = \{ (y_i) \in X : y_1 = s_1, y_2 = s_2, \dots, y_n = s_n \} \]
    for some finite $n$. Now, define a new sequence $y = (y_i)$ such that:
    \[ y_i = 
    \begin{cases} 
    s_i & \text{if } i \neq n+1 \\
    1 - s_i & \text{if } i = n+1 
    \end{cases} \]
    Since $y$ matches the first $n$ bits of $e(x)$, we have $y \in W \subset e(U)$. However, $y \neq e(x)$ because the $(n+1)$-th bit is different. Letting $z = e^{-1}(y)$, we have $z \in U \cap \mathcal{C}$ and $z \neq x$. Thus, $x$ is not an isolated point.
\end{itemize}

\paragraph{2. Totally Disconnected:}
A topological space is totally disconnected if its only connected components are singletons.
\begin{itemize}
    \item The space $\{0, 1\}$ with the discrete topology is clearly totally disconnected.
    \item A fundamental property of topology is that the product of any family of totally disconnected spaces is itself totally disconnected. 
    \item Since $X = \prod_{n=1}^\infty \{0, 1\}$ is a product of totally disconnected spaces, $X$ is totally disconnected. 
    \item Because $\mathcal{C}$ is homeomorphic to $X$, the Cantor set $\mathcal{C}$ is also totally disconnected.
\end{itemize}
In other words, for any distinct $x, y \in \mathcal{C}$, their images $e(x)$ and $e(y)$ must differ at some coordinate $k$. The set of all sequences whose $k$-th coordinate matches $e(x)_k$ is a clopen (closed and open) set containing $x$ but not $y$, which implies $x$ and $y$ cannot belong to the same connected component.
```

- Source proof / prover notes:
  - For total disconnectedness, prove `TotallyDisconnectedSpace (ℕ → Bool)` by typeclass search from `Pi.totallyDisconnectedSpace`; transfer it across `cantorSetHomeomorphNatToBool.symm` or `cantorSetHomeomorphNatToBool` with `Homeomorph.totallyDisconnectedSpace`, then convert the subtype-space statement to `IsTotallyDisconnected cantorSet` using `totallyDisconnectedSpace_subtype_iff`.
  - For perfectness, combine `isClosed_cantorSet` with the “no isolated points”/accumulation part. The source’s cylinder argument suggests taking a neighbourhood of `x : cantorSet`, transporting it to `ℕ → Bool`, restricting to finitely many coordinates, and flipping a later Boolean coordinate. Search `Perfect`, `preperfect_iff_nhds`, product neighbourhood lemmas, and existing Cantor-space/perfect-space instances before writing manual topology.
  - If a direct theorem/instance already states `PerfectSpace (ℕ → Bool)` or `Perfect cantorSet`, prefer transferring/rewriting over reconstructing the cylinder proof.

## Construction Gaps

- No definitions, structures, classes, or instances are left as construction stubs.
- The only planned proof obligation is the theorem `isTotallyDisconnected_cantorSet`, intentionally left as `by sorry` for the later proof workflow after statement/source review.

## Handoff Checklist

- [x] Source document and preflight manifest read.
- [x] Companion instructions and all candidate skeletons read.
- [x] Local project/Mathlib search performed before choosing identifiers.
- [x] Source theorem inventory includes `line-17`.
- [x] Lean statement contains source proof/prover notes in the declaration doc comment.
- [x] Root project module imports the generated target path.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [x] Proof-ready handoff accepted for the later prove workflow by formalization PASS and 2026-06-05 audit.
