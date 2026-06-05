# Formalization Blueprint: `topology/L3/top_gen_L3_006`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Planner state: source-mapped Lean statement draft prepared; independent statement/source verifier PASS is needed before proof handoff; proof-ready handoff remains unchecked until the final organization pass.
- Source inspection: `formalization_document_inspect docs/source.tex` found one theorem block, `line-17` / `existsUnique_continuousMap_lifts`, with proof text in lines 63--205.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: single generated formalization file for the source theorem.
- `ShadowBench/Source.lean`: project aggregator importing `ShadowBench.Source.Main`.
- `ShadowBench.lean`: root project module importing `ShadowBench.Source`.

No split into auxiliary files is planned for the statement draft. The source contains one theorem, so a single target file preserves the source map most clearly.

## Import Plan

```lean
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.UnitInterval
```

These are the direct imports used by `ShadowBench/Source/Main.lean`, matching `docs/instructions.md`.

## Suggested Search Modules

Non-gating hints for the prover, not forced imports:

- `Mathlib.Topology.ContinuousMap.Defs` for notation `C(X, Y)` and coercions to functions.
- `Mathlib.Topology.Connected.PathConnected` / `Mathlib.Topology.Connected.LocPathConnected` for `PathConnectedSpace` and `LocPathConnectedSpace`.
- `Mathlib.Topology.UnitInterval` for the unit interval `I`, its endpoints `0` and `1`, and path constructions.
- `Mathlib.Topology.ContinuousMap.Interval` for continuous-map interval concatenation lemmas, if the later proof follows the source concatenation argument.
- Search term `IsLocalHomeomorph` for local inverse/homeomorphism facts about `p`.

## Required Names

- `existsUnique_continuousMap_lifts`

## Candidate Skeletons Reviewed

- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` have the required theorem name and allowed imports, but encode paths as plain functions `unitInterval → A` and lifts as plain functions `unitInterval → E`. That omits the source word "path" as a continuity requirement, so these candidates were not adopted as-is.
- `docs/skeletons/Skeleton4.lean` correctly uses continuous maps `C(I, A)` and `C(I, E)` for paths and lifts, and `C(A, E)` for the unique continuous map. This candidate shaped the final statement.
- Amendment to Skeleton4: the source calls `f : A → X` a continuous map, so the final statement encodes `f` directly as `f : C(A, X)` rather than as a raw function plus `hf : Continuous f`. The conclusion and lifting hypotheses compare the underlying functions using explicit continuous-map coercions.

## Detected Theorem-Like Blocks

1. `line-17` (theorem, lines 17-63) - existsUnique_continuousMap_lifts

## Source Map

- line-17 -> `existsUnique_continuousMap_lifts` (`docs/source.tex` lines 17-63; proof lines 63-205)

## Source inventory

- label: line-17
  source_id: line-17
  kind: theorem
  source_title: existsUnique_continuousMap_lifts
  planned_lean_declaration: existsUnique_continuousMap_lifts
  source_locator: docs/source.tex lines 17-63, proof lines 63-205
  details: Full statement-fidelity details and prover notes are in the matching source statement inventory entry below.

## Source Statement Inventory

### line-17

- Source inventory entry `line-17`: theorem `[existsUnique_continuousMap_lifts]` in `docs/source.tex`.
- Source label: `line-17`.
- Source locator: `docs/source.tex`, theorem environment lines 17--63; proof lines 63--205.
- Planned Lean declaration: `existsUnique_continuousMap_lifts` in `ShadowBench/Source/Main.lean`.
- Kind: theorem.
- Dependencies: `IsLocalHomeomorph`, `PathConnectedSpace`, `LocPathConnectedSpace`, `ContinuousMap` notation `C(_, _)`, unit interval `I`, function composition.
- Lean statement:

```lean
theorem existsUnique_continuousMap_lifts {E X A : Type*}
    [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace A]
    [PathConnectedSpace A] [LocPathConnectedSpace A]
    (p : E → X) (hp : IsLocalHomeomorph p)
    (f : C(A, X))
    (a₀ : A) (e₀ : E) (he₀ : p e₀ = f a₀)
    (h₁ : ∀ γ : C(I, A), γ 0 = a₀ →
      ∃ Γ : C(I, E), Γ 0 = e₀ ∧
        p ∘ (Γ : I → E) = (f : A → X) ∘ (γ : I → A))
    (h₂ : ∀ γ γ' : C(I, A), γ 0 = a₀ → γ' 0 = a₀ →
      ∀ Γ Γ' : C(I, E), Γ 0 = e₀ → Γ' 0 = e₀ →
        p ∘ (Γ : I → E) = (f : A → X) ∘ (γ : I → A) →
        p ∘ (Γ' : I → E) = (f : A → X) ∘ (γ' : I → A) →
        γ 1 = γ' 1 → Γ 1 = Γ' 1) :
    ∃! F : C(A, E), F a₀ = e₀ ∧ p ∘ (F : A → E) = (f : A → X)
```

- Source statement:

Let `p : E → X` be a local homeomorphism. Let `A` be a path-connected and locally path-connected topological space. Let `f : A → X` be a continuous map, and fix points `a₀ ∈ A` and `e₀ ∈ E` such that `p(e₀) = f(a₀)`. Assume:

1. For every path `γ : I → A` with `γ(0)=a₀`, there exists a path `Γ : I → E` such that `Γ(0)=e₀` and `p ∘ Γ = f ∘ γ`.
2. Whenever `γ, γ' : I → A` are paths with `γ(0)=γ'(0)=a₀`, and `Γ, Γ' : I → E` are lifts satisfying `Γ(0)=Γ'(0)=e₀`, `p ∘ Γ=f ∘ γ`, and `p ∘ Γ'=f ∘ γ'`, then `γ(1)=γ'(1)` implies `Γ(1)=Γ'(1)`.

Then there exists a unique continuous map `F : A → E` such that `F(a₀)=e₀` and `p ∘ F=f`.

- Source qualifiers:
  - Mathematical object class: `E`, `X`, and `A` are topological spaces; `p : E → X` is a local homeomorphism; `A` is path-connected and locally path-connected; `f` and the output `F` are continuous maps; source paths and lifts are continuous maps from the unit interval.
  - Quantifier order: spaces and topological structure, path-connected/local path-connected structure on `A`, local homeomorphism `p`, continuous map `f`, basepoints `a₀` and `e₀`, compatibility `p e₀ = f a₀`, path-lift existence, lifted-endpoint uniqueness, then existence and uniqueness of `F`.
  - Parameter domains/codomains: `p : E → X`; `f : C(A, X)`; paths `γ γ' : C(I, A)`; lifts `Γ Γ' : C(I, E)`; output `F : C(A, E)`.
  - Equality/image conditions: `he₀ : p e₀ = f a₀`; `h₁` requires `Γ 0 = e₀` and equality of underlying functions `p ∘ Γ = f ∘ γ`; `h₂` requires analogous lifting equalities and maps equal endpoints in `A` to equal lifted endpoints in `E`; conclusion requires `F a₀ = e₀` and `p ∘ F = f` as underlying functions.
  - Side conditions: the source's two enumerated path-lifting conditions are represented by `h₁` and `h₂`.
  - Follow-on claims: the conclusion is the existence and uniqueness of the continuous lift `F`; continuity is encoded by the type `C(A, E)` rather than as a separate conjunct.
- Formal statement review: the Lean statement preserves the theorem name, local-homeomorphism assumption, topological-space assumptions, basepoint compatibility, both path-lifting hypotheses, and the unique continuous lifting conclusion. It uses mathlib's structured continuous-map type for `f`, paths/lifts, and `F`, which records the continuity present in the source rather than weakening paths to raw functions.
- Lean coverage:
  - Object classes: `[TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace A]`, `[PathConnectedSpace A]`, `[LocPathConnectedSpace A]`, `hp : IsLocalHomeomorph p`, and bundled maps `f : C(A, X)`, `γ : C(I, A)`, `Γ : C(I, E)`, `F : C(A, E)` cover all source continuity and topology qualifiers.
  - Quantifier order: the Lean binder order follows the source order: spaces/topologies, connectivity structures on `A`, raw map `p` with local-homeomorphism proof, continuous map `f`, basepoints and compatibility, path-lift existence `h₁`, endpoint uniqueness `h₂`, then the unique lift conclusion.
  - Domains/codomains: `p : E → X`, `f : C(A, X)`, paths `C(I, A)`, lifts `C(I, E)`, and output `C(A, E)` match the source domains and codomains.
  - Equality/image conditions: `he₀ : p e₀ = f a₀`, the equations `p ∘ Γ = f ∘ γ` and `p ∘ Γ' = f ∘ γ'`, the endpoint implication `γ 1 = γ' 1 → Γ 1 = Γ' 1`, and the conclusion `F a₀ = e₀ ∧ p ∘ F = f` are all present as equalities of underlying functions where the source writes composition.
  - Side conditions and follow-on claims: the two enumerated source assumptions are exactly `h₁` and `h₂`; the only follow-on claim is the existence and uniqueness of the continuous lift, encoded by `∃! F : C(A, E), ...`.
- Scope changes: none. Representation choices are explicit direct mathlib encodings: `C(_, _)` for continuous maps/paths, `I` for the closed unit interval, and typeclasses for path connectedness/local path connectedness. No separate bridge declaration is needed because the source objects are continuous maps and topological-space properties already represented by these types/classes.
- Ambiguity notes: the source writes `path γ : I → A`; this draft interprets "path" in the standard topological sense as a continuous map from the unit interval. The source does not require `p` to be a bundled local homeomorphism, only that the raw function `p` is locally a homeomorphism, so `IsLocalHomeomorph p` is used.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: complete source proof text and prover notes are recorded in the two fields below.
- Complete source proof text:

```tex
\begin{proof}
We first define \(F\) pointwise.

Since \(A\) is path-connected, for every \(a\in A\) there exists a path
\[
\gamma_a:I\to A
\]
from \(a_0\) to \(a\), meaning
\[
\gamma_a(0)=a_0,\qquad \gamma_a(1)=a.
\]
By assumption (1), there exists a lift
\[
\Gamma_a:I\to E
\]
such that
\[
\Gamma_a(0)=e_0,\qquad p\circ \Gamma_a=f\circ \gamma_a.
\]
Define
\[
F(a):=\Gamma_a(1).
\]

We must check that this does not depend on the choice of \(\gamma_a\) or of the lift \(\Gamma_a\). But this is exactly what assumption (2) gives: if \(\gamma_a,\gamma'_a\) are two paths from \(a_0\) to \(a\), and \(\Gamma_a,\Gamma'_a\) are lifts starting at \(e_0\), then since
\[
\gamma_a(1)=a=\gamma'_a(1),
\]
assumption (2) implies
\[
\Gamma_a(1)=\Gamma'_a(1).
\]
So \(F(a)\) is well defined.

Now for each \(a\in A\),
\[
p(F(a))=p(\Gamma_a(1))=f(\gamma_a(1))=f(a).
\]
Hence
\[
p\circ F=f.
\]
Also, taking the constant path at \(a_0\), the lifted path starts at \(e_0\), so
\[
F(a_0)=e_0.
\]

It remains to prove that \(F\) is continuous.

Fix a point \(a\in A\). Since \(p\) is a local homeomorphism, there exists an open neighborhood \(V\subseteq E\) of \(F(a)\) such that \(p|_V:V\to U\) is a homeomorphism onto an open set \(U\subseteq X\) containing
\[
p(F(a))=f(a).
\]

Since \(f\) is continuous, \(f^{-1}(U)\) is an open neighborhood of \(a\). Because \(A\) is locally path-connected, we may choose an open path-connected neighborhood
\[
W\subseteq f^{-1}(U)
\]
of \(a\).

We claim that on \(W\),
\[
F=(p|_V)^{-1}\circ f.
\]
This will prove continuity of \(F\) at \(a\), since the right-hand side is continuous.

Take any \(x\in W\). Because \(W\) is path-connected, choose a path
\[
\delta:I\to W
\]
from \(a\) to \(x\), so
\[
\delta(0)=a,\qquad \delta(1)=x.
\]
Also choose once and for all a path \(\gamma_a\) from \(a_0\) to \(a\), together with a lift \(\Gamma_a\) from \(e_0\) to \(F(a)\).

Now define a path in \(E\) by
\[
\widetilde\delta := (p|_V)^{-1}\circ f\circ \delta.
\]
This is well defined because \(f(\delta(t))\in U\) for all \(t\), since \(\delta(I)\subseteq W\subseteq f^{-1}(U)\). Moreover,
\[
\widetilde\delta(0)=(p|_V)^{-1}(f(a))=(p|_V)^{-1}(p(F(a)))=F(a),
\]
because \(F(a)\in V\).

Now concatenate \(\Gamma_a\) with \(\widetilde\delta\). This gives a path in \(E\) starting at \(e_0\), and its projection under \(p\) is exactly the concatenation of \(\gamma_a\) with \(\delta\), which is a path from \(a_0\) to \(x\).

By construction, the endpoint of this lifted concatenated path is
\[
\widetilde\delta(1)=(p|_V)^{-1}(f(x)).
\]
But by the definition of \(F(x)\) and the uniqueness of lifted endpoints in assumption (2), the endpoint of any lift of a path from \(a_0\) to \(x\) starting at \(e_0\) must be \(F(x)\). Therefore
\[
F(x)=(p|_V)^{-1}(f(x)).
\]
This proves the claim.

So around every point \(a\), the map \(F\) agrees locally with the continuous map \((p|_V)^{-1}\circ f\). Hence \(F\) is continuous on all of \(A\).

Finally, we prove uniqueness. Suppose
\[
F':A\to E
\]
is another continuous map such that
\[
F'(a_0)=e_0,\qquad p\circ F'=f.
\]
Let \(a\in A\), and choose any path \(\gamma:I\to A\) from \(a_0\) to \(a\). Then
\[
F'\circ \gamma:I\to E
\]
is a path satisfying
\[
(F'\circ \gamma)(0)=F'(a_0)=e_0
\]
and
\[
p\circ(F'\circ \gamma)=f\circ\gamma.
\]
Similarly,
\[
F\circ \gamma:I\to E
\]
is also a lift of \(f\circ \gamma\) starting at \(e_0\). Hence, by assumption (2),
\[
F'(a)=(F'\circ\gamma)(1)=(F\circ\gamma)(1)=F(a).
\]
Since this holds for every \(a\in A\), we get
\[
F'=F.
\]

Therefore there exists a unique continuous map \(F:A\to E\) such that
\[
F(a_0)=e_0
\qquad\text{and}\qquad
p\circ F=f.
\]
This completes the proof.
\end{proof}
```

#### Prover notes

- Build the underlying function by choosing, for each `a`, a path from `a₀` to `a` using `[PathConnectedSpace A]`, then choosing a lift via `h₁`, and taking the endpoint.
- Use `h₂` to prove independence of the chosen path/lift and to get uniqueness of endpoints for any lift from `e₀`.
- For continuity, use `hp : IsLocalHomeomorph p` to obtain a local homeomorphic inverse around `F a`; use `[LocPathConnectedSpace A]` to choose a path-connected open neighborhood inside `f ⁻¹' U`; show locally `F` agrees with the inverse branch composed with `f` by concatenating paths.
- For uniqueness, compose any candidate lift with a path from `a₀` to `a` and apply `h₂` to compare endpoints.

## Handoff Checklist

- [x] Source document `docs/source.tex` and workflow manifest/context read.
- [x] Candidate skeletons read and compared with the source.
- [x] Local project / Mathlib search performed before choosing the declaration shape.
- [x] Blueprint contains source inventory entry `line-17` with source qualifiers, Lean coverage, scope changes, and prover notes.
- [x] Root project module already imports the generated target module through `ShadowBench.lean` and `ShadowBench/Source.lean`.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [x] Proof-ready handoff accepted for the later prove workflow by formalization PASS and 2026-06-05 audit.
