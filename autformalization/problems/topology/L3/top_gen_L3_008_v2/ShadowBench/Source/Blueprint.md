# Formalization Blueprint: `topology/L3/top_gen_L3_008_v2`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Source Statement Inventory

### line-17

- Source inventory key: `line-17`.
- Source locator: `line-17` (`docs/source.tex`, theorem block lines 17-41; proof lines 41-151).
- Planned Lean declarations: `existsUnique_continuousMap_lifts_of_range_le` in `ShadowBench/Source/Main.lean`.
- Source statement: Let `p : E → X` be a covering map, let `A` be path connected and locally path connected, and let `f : A → X` be continuous. Fix `a₀ : A` and `e₀ : E` with `p e₀ = f a₀`. Assume `f_* (π₁(A,a₀)) ⊆ p_* (π₁(E,e₀)) ⊆ π₁(X,f(a₀))`. Then there exists a unique continuous map `F : A → E` such that `F a₀ = e₀` and `p ∘ F = f`.
- Lean statement summary: for topological spaces `E X A`, a covering map `hp : IsCoveringMap p`, typeclass assumptions `[PathConnectedSpace A]` and `[LocPathConnectedSpace A]`, a continuous map `f : C(A, X)`, basepoints `a₀ : A`, `e₀ : E`, basepoint equality `he₀ : p e₀ = f a₀`, and the induced fundamental-group range inclusion
  ```lean
  (FundamentalGroup.map f a₀).range ≤
    (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ he₀).range
  ```
  the conclusion is
  ```lean
  ∃! F : C(A, E), F a₀ = e₀ ∧ p ∘ F = f
  ```
- Skeleton candidate used: the provided skeletons preserve the required theorem name and broad parameter order, but their `LoopAt`/`FundamentalGroup.mk` hypothesis is not the Mathlib representation of the subgroup-image condition and `Skeleton4.lean` is syntactically malformed. The final draft follows the exact Mathlib lifting-criterion representation found by `lean_search` (`IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le`) while keeping the required top-level source theorem name.
- Dependencies:
  - `IsCoveringMap`, `IsCoveringMap.continuous` for the covering map and induced continuous map on `p`.
  - `PathConnectedSpace A` and `LocPathConnectedSpace A` for the source assumptions on `A`.
  - `C(A, X)` / `C(A, E)` for continuous maps.
  - `FundamentalGroup.map` and `FundamentalGroup.mapOfEq` for the induced maps on fundamental groups and the basepoint transport from `p e₀ = f a₀`.
- Source qualifiers:
  - Mathematical object class: topological spaces `E`, `X`, `A`; covering map `p : E → X`; continuous map `f : A → X`.
  - Quantifier order: choose spaces, covering map, path-connected and locally path-connected domain, continuous map, basepoints, basepoint equality, subgroup-image inclusion, then existential unique lift.
  - Parameter domain/codomain: `f` has domain `A` and codomain `X`; the lift `F` has domain `A` and codomain `E`; `p` has domain `E` and codomain `X`.
  - Equality/image condition: `p e₀ = f a₀`; `F a₀ = e₀`; `p ∘ F = f`.
  - Side conditions: the only nontrivial algebraic side condition is the inclusion of the image of `π₁(A,a₀)` under `f_*` in the image of `π₁(E,e₀)` under `p_*`; the second inclusion in the source is encoded by the codomain of `mapOfEq`.
  - Follow-on claims: existence and uniqueness of a continuous lift; no additional corollaries are stated in the source.
- Lean coverage: exact modulo standard Lean packaging: continuous maps are represented as `C(A, X)` and `C(A, E)` rather than separate functions plus `Continuous` hypotheses; path connectedness and local path connectedness are typeclass assumptions on `A`; the fundamental-group image inclusion is a range inclusion of Mathlib induced homomorphisms, with basepoint equality handled by `FundamentalGroup.mapOfEq`.
- Scope changes: no intentional mathematical weakening or strengthening. Representation bridges are only packaging choices (`C(...)`, typeclasses, and `mapOfEq` for basepoint transport).
- Formal statement review: the Lean statement matches the source theorem's hypotheses and conclusion under Mathlib's representation of continuous maps and fundamental-group homomorphism images. It should be independently checked before marking proof-ready.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof text (verbatim from `docs/source.tex`, lines 43-151):
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
- Prover notes: Mathlib already contains the source theorem as `IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le` in `Mathlib.Topology.Homotopy.Lifting`. The future prover can either import that module and use the namespace theorem directly, or replay its proof using path lifting, monodromy, and the range inclusion. The present formalization intentionally leaves the proof as `by sorry` for the prover queue.

## Import Plan

Direct Lean imports for `ShadowBench/Source/Main.lean`:

```lean
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Covering.Basic
```

## Suggested Search Modules

These are proof-search hints, not current direct imports:

- `Mathlib.Topology.Homotopy.Lifting` for `IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le`, `liftPath`, `liftHomotopy`, and related path-lifting facts.
- `Mathlib.Topology.Homotopy.Path` for path concatenation/reversal and homotopy classes if the proof is replayed manually.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the single source-backed theorem declaration `existsUnique_continuousMap_lifts_of_range_le` with a `by sorry` proof placeholder.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so project-level `lake build`/`lean_verify(mode=project)` covers the generated target module.

## Required Names

- `existsUnique_continuousMap_lifts_of_range_le`

## Handoff Checklist

- [x] Source document and preflight manifest read.
- [x] Candidate skeletons read and compared against the source theorem.
- [x] Local project/Mathlib search performed before drafting.
- [x] Blueprint source inventory includes `line-17` with statement coverage, dependencies, source qualifiers, scope changes, and proof/prover notes.
- [x] Root project module imports the generated target module through `ShadowBench.Source`.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [x] Proof-ready handoff accepted for the later prove workflow by formalization PASS and 2026-06-05 audit.
