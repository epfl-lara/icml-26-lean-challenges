# Formalization Blueprint: `topology/L3/top_gen_L3_008`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench.lean` imports `ShadowBench.Source`.
- `ShadowBench/Source.lean` imports `ShadowBench.Source.Main`.
- `ShadowBench/Source/Main.lean` contains the single source-backed theorem skeleton for `line-17`.

No file split is currently useful: the source document contains one theorem and no auxiliary source definitions. The target module is already reachable from the root `ShadowBench` library target.

## Import Plan

```lean
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting
```

The first three imports are the imports allowed by `docs/instructions.md`. `Mathlib.Topology.Homotopy.Lifting` is added because local Mathlib search found the exact lifting-criterion dependency `IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le`, which is the natural proof target for the generated theorem.

## Suggested Search Modules

- `Mathlib.Topology.Homotopy.Lifting`: `IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le`, `IsCoveringMap.liftPath`, `IsCoveringMap.liftHomotopy`, path-lifting uniqueness lemmas.
- `Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup`: `FundamentalGroup.map`, `FundamentalGroup.mapOfEq` and subgroup ranges of induced maps on fundamental groups.
- `Mathlib.Topology.Covering.Basic`: `IsCoveringMap` and `IsCoveringMap.continuous`.
- `Mathlib.Topology.Connected.LocPathConnected`: `PathConnectedSpace` and `LocPathConnectedSpace` assumptions.

## Required Names

- `existsUnique_continuousMap_lifts_of_range_le`

## Candidate Skeleton Review

- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` propose the required theorem name but encode loops incorrectly as functions `A → ℝ` and `E → ℝ`; this does not match the source theorem's fundamental-group image condition.
- `docs/skeletons/Skeleton4.lean` repeats the same non-faithful statement and is syntactically malformed by an extra `:= by sorry`.
- None of the candidate skeleton statements was adopted. The Lean statement below follows the Mathlib theorem shape found by search, using bundled continuous maps and the actual fundamental-group induced homomorphism range inclusion.

## Detected Theorem-Like Blocks

1. `line-17` (theorem, lines 17-41) - `existsUnique_continuousMap_lifts_of_range_le`

## Source Map

- line-17 -> `existsUnique_continuousMap_lifts_of_range_le` (`docs/source.tex` lines 17-41; proof lines 41-151)

## Source inventory

- label: line-17
  source_id: line-17
  kind: theorem
  source_title: existsUnique_continuousMap_lifts_of_range_le
  lean_declaration: existsUnique_continuousMap_lifts_of_range_le
  source_locator: docs/source.tex lines 17-41; proof lines 41-151
  details: Full statement-fidelity details and prover notes are in the matching source statement inventory entry below.

## Source Statement Inventory

### line-17

- Source inventory entry: `line-17`.
- Source label: `line-17`.
- Source locator: `docs/source.tex`, theorem lines 17-41, proof lines 41-151.
- Planned Lean declaration: `existsUnique_continuousMap_lifts_of_range_le` in `ShadowBench/Source/Main.lean`.
- Kind: theorem.
- Source theorem title: `existsUnique_continuousMap_lifts_of_range_le`.
- Skeleton candidate used: no candidate adopted; skeletons used only as naming/import hints.
- Mathlib theorem shape used: `IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le` from `Mathlib.Topology.Homotopy.Lifting`.
- Dependencies:
  - `IsCoveringMap p` for the covering map hypothesis.
  - `[PathConnectedSpace A]` for source path connectedness of `A`.
  - `[LocPathConnectedSpace A]` for source local path connectedness of `A`.
  - `f : C(A, X)` to bundle the source continuous map `f : A → X`.
  - `FundamentalGroup.map f a₀` for `f_* : π₁(A,a₀) → π₁(X,f(a₀))`.
  - `FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he` for `p_* : π₁(E,e₀) → π₁(X,f(a₀))`, transporting along `he : p e₀ = f a₀`.
- Lean declaration statement:

```lean
theorem existsUnique_continuousMap_lifts_of_range_le
    {E X A : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace A]
    [PathConnectedSpace A] [LocPathConnectedSpace A]
    {p : E → X} (hp : IsCoveringMap p)
    {f : C(A, X)} {a₀ : A} {e₀ : E} (he : p e₀ = f a₀)
    (hle : (FundamentalGroup.map f a₀).range ≤
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he).range) :
    ∃! F : C(A, E), F a₀ = e₀ ∧ p ∘ F = f := by
  sorry
```

- Source qualifiers:
  - Mathematical object class: arbitrary topological spaces `E`, `X`, and `A`, with `p : E → X` a covering map.
  - Connectivity assumptions: `A` is path connected and locally path connected.
  - Map assumption: `f : A → X` is continuous.
  - Basepoints: `a₀ : A` and `e₀ : E` with `p e₀ = f a₀`.
  - Fundamental-group condition: the image of `π₁(A,a₀)` under `f_*` is contained in the image of `π₁(E,e₀)` under `p_*`, viewed inside `π₁(X,f(a₀))`.
  - Conclusion: there exists a unique continuous lift `F : A → E` satisfying `F a₀ = e₀` and `p ∘ F = f`.
- Lean coverage:
  - Covers the covering-map hypothesis with `hp : IsCoveringMap p`.
  - Covers path connectedness and local path connectedness with typeclass assumptions `[PathConnectedSpace A]` and `[LocPathConnectedSpace A]`.
  - Covers continuity of `f` by representing it as a bundled continuous map `f : C(A, X)`.
  - Covers the basepoint equality directly as `he : p e₀ = f a₀`.
  - Covers the subgroup image hypothesis as `(FundamentalGroup.map f a₀).range ≤ (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he).range`.
  - Covers the unique continuous lift by existential uniqueness over `F : C(A, E)` with `F a₀ = e₀ ∧ p ∘ F = f`.
- Scope changes:
  - Representation change only: continuous maps are bundled as `C(A, X)` and `C(A, E)`, and connectedness/local connectedness are typeclass assumptions rather than separate proposition-valued hypotheses. This is the standard Mathlib encoding and is not intended as a mathematical weakening.
  - The source's ambient inclusion into `π₁(X,f(a₀))` is represented by both subgroup ranges living in the same Lean fundamental group `FundamentalGroup X (f a₀)`, using `mapOfEq` to transport the basepoint of `p_*` along `p e₀ = f a₀`.
- Formal statement review: compared against source statement lines 17-41. The theorem preserves the same quantifier order up to Lean's typeclass/bundled-continuous-map conventions: spaces and topologies, connectivity assumptions on `A`, covering map `p`, continuous map `f`, basepoints/equality, fundamental-group image inclusion, then unique continuous lift.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: complete source proof text and prover notes are recorded below.
- Source proof text:

```text
For each \(a \in A\), choose a path
\[
\gamma_a : I \to A
\]
from \(a_0\) to \(a\). Since
\[
(f\circ \gamma_a)(0)=f(a_0)=p(e_0),
\]
the path lifting property for covering maps gives a unique lift
\[
\widetilde{\gamma}_a : I \to E
\]
such that
\[
\widetilde{\gamma}_a(0)=e_0
\qquad\text{and}\qquad
p\circ \widetilde{\gamma}_a=f\circ \gamma_a.
\]
Define
\[
F(a):=\widetilde{\gamma}_a(1).
\]

We first show that \(F(a)\) is independent of the choice of \(\gamma_a\).

Let \(\gamma,\gamma' : I \to A\) be two paths from \(a_0\) to the same point \(a\), and let
\[
\widetilde{\gamma},\widetilde{\gamma}' : I \to E
\]
be the lifts of \(f\circ \gamma\) and \(f\circ \gamma'\) starting at \(e_0\). We must prove that
\[
\widetilde{\gamma}(1)=\widetilde{\gamma}'(1).
\]

Consider the loop at \(a_0\)
\[
\alpha:=\gamma\cdot \overline{\gamma'}.
\]
Then \(f\circ \alpha\) is a loop at \(f(a_0)\). Its homotopy class lies in
\[
f_*\bigl(\pi_1(A,a_0)\bigr),
\]
hence, by hypothesis, also in
\[
p_*\bigl(\pi_1(E,e_0)\bigr).
\]
Therefore there exists a loop
\[
\beta : I \to E
\]
based at \(e_0\) such that
\[
[p\circ \beta]=[f\circ \alpha]
\]
in \(\pi_1(X,f(a_0))\). So there exists a homotopy $h_t$ with $h_0 = f \circ \alpha$ and $h_1 = p \circ \beta$. By the covering homotopy property, we have a lifting $\widetilde{h}_t$ of $h_t$ which is a homotopy relative to endpoints such that $\widetilde{h}_0$ is the lift of $f \circ \alpha$ starting at $e_0$ and $\widetilde{h}_1 = \beta$ since $\beta$ is a lift of $p \circ \beta$ starting at $e_0$. As $\widetilde{h}_1$ is a loop at $e_0$, so is $\widetilde{h}_0$.

Let
\[
\widetilde{\alpha} := \widetilde{h}_0.
\]

By the uniqueness of the lifted paths, the first half of $\alpha$ is $\widetilde{\gamma}$ and the second half of $\alpha$ is $\overline{\widetilde{\gamma}'}$ so that the endpoints of $\widetilde{\gamma}$ and $\widetilde{\gamma}'$ coincide, and thus \(F(a)\) is well defined.

By construction,
\[
F(a_0)=e_0.
\]
Also, for every \(a\in A\),
\[
p(F(a))
=
p\bigl(\widetilde{\gamma}_a(1)\bigr)
=
(f\circ \gamma_a)(1)
=
f(a),
\]
so
\[
p\circ F=f.
\]

To prove that \(F\) is continuous, let \(U \subseteq X\) be an open neighborhood of \(f(a)\) having a lift \(\widetilde{U} \subseteq E\)  containing \(F(a)\) such that \(p : \widetilde{U} \to U\) is a homeomorphism. Choose a path-connected open neighborhood \(V\) of \(a\) with \(f(V) \subseteq U\). For paths from \(a_0\) to points \(a' \in V\) we can take a fixed path \(\gamma\) from \(a_0\) to \(a\) followed by paths \(\eta\) in \(V\) from \(a\) to the points \(a'\). Then the paths \((f \circ \gamma )\cdot (f \circ \eta)\) in \(X\) have lifts \((\widetilde{f \circ \gamma}) \cdot (\widetilde{f \circ \eta}) \) where \(\widetilde{(f \circ \eta)} = p^{-1}(f \circ \eta)\) and \(p^{-1} :U \to \widetilde{U}\) is the inverse of \(p:\widetilde{U} \to U\). Thus \(F(V) \subseteq \widetilde{U}\) and \(F|_V = p^{-1} \circ f\), hence \(F\) is continuous at \(a\).

Finally, \(F\) is unique. Indeed, suppose
\[
F' : A \to E
\]
is another continuous map such that
\[
F'(a_0)=e_0
\qquad\text{and}\qquad
p\circ F'=f.
\]
Let \(a\in A\), and let \(\gamma_a\) be any path from \(a_0\) to \(a\). Then
\[
F'\circ \gamma_a
\]
is a lift of \(f\circ \gamma_a\) starting at \(e_0\). By uniqueness of path lifting,
\[
F'\circ \gamma_a=\widetilde{\gamma}_a.
\]
Evaluating at \(1\), we get
\[
F'(a)=\widetilde{\gamma}_a(1)=F(a).
\]
Thus \(F'=F\).
```

- Prover notes:
  - The source proof is exactly the lifting criterion for covering maps.
  - The future proof should first try the existing Mathlib theorem:

```lean
simpa using hp.existsUnique_continuousMap_lifts_of_range_le (f := f) (a₀ := a₀) (e₀ := e₀) he hle
```

  - If explicit proof repair is required, follow the source proof: lift paths from `a₀`, use the range hypothesis on the loop `γ.trans γ'.symm`, use covering homotopy/path-lifting uniqueness to show endpoint independence, use evenly covered neighborhoods and local path connectedness for continuity, and use uniqueness of lifted paths for uniqueness of any other lift.

## Handoff Notes

- The blueprint has a source inventory entry for `line-17` and no construction stubs.
- The Lean theorem proof is intentionally `by sorry` for the later `/prove` workflow.
- The drafting pass stops here so that a separate statement/source review can check the Lean declaration, doc-comment proof nudge, and source proof before proof search begins.
