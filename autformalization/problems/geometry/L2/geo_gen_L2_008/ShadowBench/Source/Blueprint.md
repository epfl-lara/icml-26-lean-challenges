# Formalization Blueprint: `geometry/L2/geo_gen_L2_008`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Source Statement Inventory

### line-17

- Source locator: `docs/source.tex`, theorem block lines 17–19; proof environment lines 21–49.
- Source statement: Suppose `A` and `B` are disjoint closed subsets of a smooth manifold `M`. Show that there exists `f ∈ C^∞(M)` such that `0 ≤ f(x) ≤ 1` for all `x ∈ M`, `f⁻¹(0) = A`, and `f⁻¹(1) = B`.
- Planned Lean declarations: `smooth_function_separating_closed_sets` in `ShadowBench/Source/Main.lean`.
- Skeleton candidate used: Skeletons 1–3 gave the expected theorem name and high-level shape (closed disjoint sets, smooth real-valued function, range in `[0,1]`, exact singleton preimages). Their manifold encoding `[Manifold ℝ M]` is not the Mathlib representation used by the available partition-of-unity API, so the draft uses the standard explicit model-with-corners parameters. Skeleton4 is malformed by an extra `:= by sorry` and was not used.
- Direct dependencies:
  - `Mathlib.Geometry.Manifold.PartitionOfUnity` for the smooth partition-of-unity/Urysohn API, especially `exists_contMDiff_zero_iff_one_iff_of_isClosed`.
  - `Mathlib.Geometry.Manifold.ContMDiff.Defs` for explicit `ContMDiff` notation in the statement.
- Source qualifiers:
  - Mathematical object class: a smooth real manifold `M`.
  - Quantifier order: for a chosen smooth manifold `M`, for all subsets `A B ⊆ M` satisfying the side conditions, there exists a function `f`.
  - Parameter domain: `A` and `B` are subsets of the same underlying manifold `M`.
  - Side conditions: `A` and `B` are closed and disjoint.
  - Output codomain and regularity: a real-valued smooth function `f : M → ℝ`, i.e. `f ∈ C^∞(M)`.
  - Range condition: for every `x : M`, `0 ≤ f x` and `f x ≤ 1`.
  - Equality/image conditions: the exact preimage/level set of `0` is `A` and the exact preimage/level set of `1` is `B`.
  - Follow-on claims in the theorem statement: none beyond existence of `f` with the smoothness, range, and exact preimage properties above.
- Lean coverage:
  - Represents the smooth real manifold by explicit Mathlib model-with-corners data `{E H M}`, `[NormedAddCommGroup E]`, `[NormedSpace ℝ E]`, `[FiniteDimensional ℝ E]`, `[TopologicalSpace H]`, `I : ModelWithCorners ℝ E H`, `[TopologicalSpace M]`, `[ChartedSpace H M]`, and `[IsManifold I ∞ M]`.
  - Makes the standard Hausdorff/countability hypotheses needed by the available Mathlib smooth Urysohn theorem explicit as `[T2Space M]` and `[SigmaCompactSpace M]`; these correspond to the textbook smooth-manifold convention used by the source proof's partition-of-unity theorem.
  - States closedness and disjointness as `hA : IsClosed A`, `hB : IsClosed B`, and `hAB : Disjoint A B`.
  - Produces `∃ f : M → ℝ` and states smoothness as `ContMDiff I 𝓘(ℝ) ∞ f`.
  - States the source range and exact preimage requirements as pointwise inequalities and singleton-preimage equalities: `∀ x : M, 0 ≤ f x ∧ f x ≤ 1`, `f ⁻¹' {0} = A`, and `f ⁻¹' {1} = B`.
- Scope changes: representation/assumption bridge only. The source's informal “smooth manifold” is formalized using Mathlib's explicit finite-dimensional model-with-corners representation plus the Hausdorff and sigma-compact assumptions required for the partition-of-unity/Urysohn API; this is the standard textbook smooth-manifold class assumed by the source proof. If the source were instead read as allowing non-Hausdorff or non-sigma-compact smooth spaces, the Lean statement would cover the standard-manifold subclass only. Notation bridge: the source notation `f^{-1}(0)` and `f^{-1}(1)` is formalized as preimages of singleton sets, `f ⁻¹' {0}` and `f ⁻¹' {1}`.
- Formal statement review:
  - Quantifier order follows the source after making the smooth-manifold structure explicit: choose a smooth manifold `M`, then closed disjoint subsets `A` and `B`, then produce `f`.
  - No source conclusion is dropped: the theorem includes smoothness, `[0,1]` bounds, and exact zero/one preimage equalities.
  - Extra typeclass assumptions are recorded above and are the intended Lean representation of the standard source manifold class used by the proof's partition-of-unity theorem.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text:

```text
To construct such a function, we rely on the property that for any closed subset $K \subseteq M$, there exists a smooth nonnegative function $g: M \to \mathbb{R}$ such that $g^{-1}(0) = K$ (this is a known result from the theory of smooth partitions of unity, often labeled as Theorem 2.29 in this text).

Let $A$ and $B$ be disjoint closed subsets of $M$.
\begin{enumerate}
    \item By the aforementioned result, there exists a smooth function $g_A \in C^\infty(M)$ such that $g_A(x) \ge 0$ for all $x \in M$ and $g_A^{-1}(0) = A$.
    \item Similarly, there exists a smooth function $g_B \in C^\infty(M)$ such that $g_B(x) \ge 0$ for all $x \in M$ and $g_B^{-1}(0) = B$.
\end{enumerate}

Now, consider the function $f: M \to \mathbb{R}$ defined by:
\[
f(x) = \frac{g_A(x)}{g_A(x) + g_B(x)}.
\]

First, we check that the denominator $g_A(x) + g_B(x)$ is never zero. Since $A \cap B = \emptyset$, for any $x \in M$, $x$ cannot be in both $A$ and $B$.
\begin{itemize}
    \item If $x \notin A$, then $g_A(x) > 0$.
    \item If $x \in A$, then $x \notin B$, so $g_B(x) > 0$.
\end{itemize}
In either case, $g_A(x) + g_B(x) > 0$ for all $x \in M$. Thus, $f$ is well-defined. Since $g_A$ and $g_B$ are smooth and their sum is non-zero, $f$ is a smooth function, i.e., $f \in C^\infty(M)$.

Next, we verify the required properties:
\begin{itemize}
    \item \textbf{Range:} Since $g_A(x) \ge 0$ and $g_B(x) \ge 0$, it follows that $0 \le \frac{g_A(x)}{g_A(x) + g_B(x)} \le 1$.
    \item \textbf{Preimage of 0:} $f(x) = 0$ if and only if $g_A(x) = 0$. By construction, $g_A(x) = 0 \iff x \in A$. Thus, $f^{-1}(0) = A$.
    \item \textbf{Preimage of 1:} $f(x) = 1$ if and only if $g_A(x) = g_A(x) + g_B(x)$, which implies $g_B(x) = 0$. By construction, $g_B(x) = 0 \iff x \in B$. Thus, $f^{-1}(1) = B$.
\end{itemize}
Therefore, $f$ is the desired smooth function.
```

- Prover notes: preferred route: use `exists_contMDiff_zero_iff_one_iff_of_isClosed (I := I) (n := ∞) hA hB hAB`. It returns `f`, `CMDiff ∞ f`, `Set.range f ⊆ Icc 0 1`, `(∀ x, x ∈ A ↔ f x = 0)`, and `(∀ x, x ∈ B ↔ f x = 1)`.
  - Preferred route theorem: `exists_contMDiff_zero_iff_one_iff_of_isClosed`.
  - Convert `CMDiff ∞ f` to the stated `ContMDiff I 𝓘(ℝ) ∞ f` by unfolding/normalizing the notation if necessary.
  - Convert `Set.range f ⊆ Icc 0 1` to `∀ x, 0 ≤ f x ∧ f x ≤ 1` using `mem_range_self x`.
  - Prove `f ⁻¹' {0} = A` and `f ⁻¹' {1} = B` by extensionality and the returned iff statements, taking care about orientation (`x ∈ A ↔ f x = 0` versus `f x = 0 ↔ x ∈ A`).

## Import Plan

Direct Lean imports for `ShadowBench/Source/Main.lean`:

```lean
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.Defs
```

## Suggested Search Modules

These are proof-search hints only; do not add them to the Lean import block unless a future proof run shows they are needed.

- `Mathlib.Geometry.Manifold.PartitionOfUnity`
- `Mathlib.Geometry.Manifold.ContMDiff.Basic`
- `Mathlib.Topology.UrysohnsLemma`

## Required Names

- `smooth_function_separating_closed_sets`

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the source-backed theorem statement and source-aware prover notes.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main` so the generated source module is in the project import tree.
- `ShadowBench.lean`: imports `ShadowBench.Source` and is the Lake default library root.

## Formalization Rules Snapshot

```text
open Set
open scoped ContDiff Manifold

The theorem must be named `smooth_function_separating_closed_sets`.
Preserve the closed/disjoint hypotheses, smooth real-valued output, pointwise `[0,1]` bounds, and exact preimages of `0` and `1`.
```

## Proof-Ready Checklist

- [x] Source document inspected with theorem block `line-17` identified.
- [x] Local instructions and candidate skeletons read and compared against the source.
- [x] Local/Mathlib search performed before choosing the declaration shape.
- [x] Blueprint source inventory records declaration name, dependencies, source qualifiers, Lean coverage, scope changes, source proof text, and prover notes.
- [x] Root project module imports the generated target module through `ShadowBench.lean` → `ShadowBench.Source` → `ShadowBench.Source.Main`.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
