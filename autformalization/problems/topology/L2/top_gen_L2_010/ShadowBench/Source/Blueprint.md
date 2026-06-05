# Formalization Blueprint: `topology/L2/top_gen_L2_010`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: single-file formalization draft for the two source-backed items. The project root already imports `ShadowBench.Source`, and `ShadowBench/Source.lean` imports `ShadowBench.Source.Main`, so plain project builds cover the target module.

## Import Plan

```lean
import Mathlib.Topology.FiberBundle.Constructions
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Analysis.Normed.Operator.Prod
```

## Suggested Search Modules

- `Mathlib.Topology.VectorBundle.Constructions`: contains the upstream Mathlib proof pattern for pullbacks of vector bundles under the names `Bundle.Trivialization.pullback_linear` and `VectorBundle.pullback`. This is a search/reference module, not a direct import in the draft, because the draft uses the required names locally.
- `Mathlib.Topology.FiberBundle.Constructions`: imported directly; provides `Bundle.Pullback`, notation `f *ᵖ E`, `Pullback.TotalSpace.topologicalSpace`, `Pullback.continuous_proj`, `Pullback.continuous_lift`, `Bundle.Trivialization.pullback`, and `FiberBundle.pullback`.

## Required Names

- `Trivialization.pullback_linear` (full Lean name after `open Bundle`: `Bundle.Trivialization.pullback_linear`)
- `VectorBundle.pullback`

## Search and Skeleton Review

- Local/Mathlib search found `Bundle.Pullback`, `Bundle.Trivialization.pullback`, `Pullback.continuous_proj`, `Pullback.continuous_lift`, `FiberBundle.pullback`, `Bundle.Trivialization.pullback_linear`, and `VectorBundle.pullback` as the relevant Mathlib API.
- `Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` model the pullback total space as a raw sigma over preimages of a projection `π : E → B` and leave definition stubs. They were rejected for the final statement because Mathlib's vector bundle API represents bundles as dependent families `E : B → Type*` with total space `Bundle.TotalSpace F E` and pullback notation `f *ᵖ E`.
- `Skeleton4.lean` uses the dependent-family representation and the notation `f *ᵖ E`, so it shaped the final statement. The final draft adjusts Skeleton4 by making `Trivialization.pullback_linear` the fiberwise-linearity instance of the pulled-back trivialization, matching Mathlib's API and avoiding a definition-with-`sorry` construction gap.

## Source Statement Inventory

### line-17

- Title: Definition `Trivialization.pullback_linear`.
- Planned Lean declarations: `Bundle.Trivialization.pullback_linear`
- Declaration kind: instance, visible as `Trivialization.pullback_linear` after `open Bundle`.
- Auxiliary local declarations: `Bundle.Pullback.addCommMonoid` and `Bundle.Pullback.module`, recording that pullback fibers inherit the original fiber algebra.
- Source locator: `docs/source.tex`, lines 17-23.
- Source statement: Let `E` be a vector bundle over a base space `B` with fiber `F`, with `F` a normed space over a normed field `k`. Given a continuous map `f : B' → B`, the pullback bundle `f^*E` over `B'` has fiber `(f^*E)_x = E_{f(x)}` for each `x : B'`; it is the disjoint union of these fibers with the coarsest topology for which the projection to `B'` and the lift to the original bundle `E` are continuous.
- Skeleton candidate used: `Skeleton4.lean` for the dependent-family representation; Mathlib API search for the exact local-trivialization linearity declaration.
- Dependencies: `Bundle.Pullback` / notation `f *ᵖ E`; `Bundle.TotalSpace`; `Pullback.TotalSpace.topologicalSpace`; `Pullback.continuous_proj`; `Pullback.continuous_lift`; `Bundle.Trivialization.pullback`; `Bundle.Pretrivialization.IsLinear`; `Bundle.Trivialization.IsLinear`; bundled continuous maps `C(B', B)`.
- Formal statement review: The Lean declaration states that if a local trivialization `e : Trivialization F (π F E)` is fiberwise `𝕜`-linear, then its pullback `e.pullback f` along a continuous map `f : C(B', B)` is fiberwise `𝕜`-linear. The surrounding imported Mathlib declarations encode the source pullback bundle itself as `(f : B' → B) *ᵖ E`, its total space as `TotalSpace F ((f : B' → B) *ᵖ E)`, its canonical projection as `π F ((f : B' → B) *ᵖ E)`, and its lift to the original total space as `Pullback.lift f`.
- Source qualifiers:
  - mathematical object class: topological vector bundle over a base space with model fiber a normed vector space over a normed field;
  - quantifier order: base `B`, pullback base `B'`, field `k`, model fiber `F`, bundle family `E`, continuous map `f`;
  - parameter domain: `f` is a continuous map `B' → B`;
  - output codomain: a pullback bundle over `B'` whose fiber at `x` is the old fiber at `f x`;
  - equality/image condition: `(f^*E)_x = E_{f(x)}`;
  - side conditions: topology on the total pullback space is induced/coarsest so that projection to `B'` and lift to the original total space are continuous;
  - follow-on claim: pulled-back local trivializations are linear on fibers.
- Lean coverage:
  - dependent family pullback/fiber equality: `Bundle.Pullback` and notation `(f : B' → B) *ᵖ E`, definitionally `(fun x => E (f x))`;
  - total-space/disjoint-union representation: `Bundle.TotalSpace F ((f : B' → B) *ᵖ E)`;
  - coarsest topology: imported `Pullback.TotalSpace.topologicalSpace` / `pullbackTopology` from `Mathlib.Topology.FiberBundle.Constructions`;
  - continuity of projection and lift: imported `Pullback.continuous_proj` and `Pullback.continuous_lift`;
  - local trivialization pullback: imported `Bundle.Trivialization.pullback`;
  - titled local linearity item: drafted `Bundle.Trivialization.pullback_linear`.
- Scope changes: Lean uses Mathlib's dependent-family bundle representation rather than an arbitrary total-space map `π : E_total → B`; the bridge is recorded above. Lean uses bundled continuous maps `f : C(B', B)` instead of a raw function plus a separate proof `hf : Continuous f`. Mathlib's `VectorBundle` API requires `NontriviallyNormedField 𝕜`, a standard strengthening of the source's “normed field” assumption. The source paragraph is titled `Trivialization.pullback_linear` while its body defines the pullback bundle; the named local declaration covers the pulled-back-trivialization linearity item, and the actual pullback object/topology/projection/lift are covered by the imported companion Mathlib declarations listed under Lean coverage.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: There is no separate proof in the source definition. For the local-trivialization declaration, the pulled-back trivialization sends `(x, v)` to `(x, e(v))` with `v` in the fiber over `f x`; the fiberwise linear map is exactly the old linear map for `e` at `f x`, so the implementation should reduce to `e.linear 𝕜`.

### line-25

- Title: Theorem `VectorBundle.pullback`.
- Planned Lean declarations: `VectorBundle.pullback`
- Declaration kind: theorem in `ShadowBench/Source/Main.lean`.
- Source locator: `docs/source.tex`, theorem lines 25-27 and proof lines 27-58.
- Source statement: Given a vector bundle `E` over a base space `B` with fiber `F` and a continuous map `f : B' → B`, the pullback bundle `f^*E` over `B'` inherits the structure of a vector bundle.
- Skeleton candidate used: `Skeleton4.lean`, adjusted from an `instance` skeleton to a theorem skeleton so the nontrivial source theorem remains a prover-queue item after statement/source review.
- Dependencies: `Bundle.Pullback`; `Pullback.TotalSpace.topologicalSpace`; `FiberBundle.pullback`; `Bundle.Trivialization.pullback`; `Bundle.Trivialization.pullback_linear`; `VectorBundle`; `trivialization_linear`; `continuousOn_coordChange`; `Trivialization.coordChangeL`; `Continuous.comp` / `ContinuousOn.comp` for transition maps; bundled continuous maps `C(B', B)`.
- Formal statement review: The Lean theorem assumes `E : B → Type*` is already a Mathlib vector bundle with model fiber `F` over a nontrivially normed field `𝕜`, and it concludes `VectorBundle 𝕜 F ((f : B' → B) *ᵖ E)` for a continuous map `f : C(B', B)`. This is the source claim in Mathlib's dependent-family representation: the pullback family has fibers definitionally `E (f x)` and the pullback total space/topology is the one from `Mathlib.Topology.FiberBundle.Constructions`.
- Source qualifiers:
  - mathematical object class: topological vector bundle with local linear trivializations;
  - quantifier order: field/model fiber/base/original bundle/pullback base/continuous map, with original bundle assumed a vector bundle before forming the pullback;
  - parameter domain: continuous maps from `B'` to `B`;
  - output codomain: a `VectorBundle` structure on the pullback family over `B'` with the same model fiber `F`;
  - equality/image condition: pullback transition maps satisfy `(f^*g)_{f^{-1}(U),f^{-1}(V)} = g_{UV} ∘ f`;
  - side conditions: continuity of `f`, continuity of original transition maps, and local trivialization coverage of the original bundle;
  - follow-on claims: each pullback fiber inherits the vector-space structure of `E (f x)`, pulled-back trivializations are linear, and transition maps are continuous linear automorphisms of `F`.
- Lean coverage:
  - pullback family/fiber equality: conclusion uses `((f : B' → B) *ᵖ E)`;
  - inherited fiber algebra: local instances `Bundle.Pullback.addCommMonoid` and `Bundle.Pullback.module` for `AddCommMonoid` and `Module` on `(f *ᵖ E) x`;
  - local trivialization coverage: `FiberBundle.pullback` supplies the pullback fiber-bundle atlas by pulling back atlas trivializations;
  - pulled-back trivialization linearity: `Bundle.Trivialization.pullback_linear`;
  - transition-map equality/continuity: covered by the imported `Bundle.Trivialization.pullback` API and its simp/computation lemmas for pullback coordinate changes; the prover should reduce `(e.pullback f).coordChangeL 𝕜 (e'.pullback f) b` to `e.coordChangeL 𝕜 e' (f b)` and compose `continuousOn_coordChange 𝕜 e e'` with `f.continuous`.
- Scope changes: Lean uses a bundled continuous map `f : C(B', B)` instead of separate `(f : B' → B) (hf : Continuous f)`. Lean uses Mathlib's dependent-family vector-bundle representation rather than a separate projection map `π : E_total → B`. Lean requires `NontriviallyNormedField 𝕜` because this is part of Mathlib's `VectorBundle` class assumptions.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text:

  ```text
  Let $\pi:E \to B$ be a vector bundle with fiber $F$, a normed space over a normed field $k$, and let $f: B' \to B$ be a continuous map. We aim to show that the pullback bundle $ \pi':f^*E \to B'$ is naturally a vector bundle.

  For each $x \in B'$, the fiber $(f^*E)_x$ is defined as $E_{f(x)}$. Since $E_{f(x)}$ is a vector space over $k$, the fiber $(f^*E)_x$ inherits the same vector space structure.

  Let $e$ be a local trivialization of $E$ over an open set $U \subseteq B$. That is, $e: E|_U \xrightarrow{\simeq} U \times F$ is a homeomorphism such that $\pi = p \circ e$ where $p: U \times F \to U$ is the projection, and $e|_{E_x}: E_x \xrightarrow{\simeq} F$ is a linear isomorphism. The pullback of $ e $ along $ f $ gives a local trivialization
  \begin{align*}
    f^*e:= (f^*E)|_{f^{-1}(U)} \xrightarrow{\simeq} f^{-1}(U) \times F, \quad (x,v) \mapsto (x,e|_{E_{f(x)}}(v)), \quad x \in f^{-1}(U), \, v \in E_{f(x)}
  \end{align*}
  Then, each $(f^*e)|_{E_x} = e|_{E_{f(x)}}$ is a linear isomorphism as desired.

  The transition maps for $f^*E$ are obtained by pulling back the transition maps of $ E $ along $ f $. Explicitly, given two trivializations $e_U:E|_U \xrightarrow{\simeq} U \times F$, $e_V:E|_V \xrightarrow{\simeq} V \times F$ for open subsets $U,V \subseteq B$, we have
  \begin{align*}
    (U \cap V) \times F \xrightarrow[e_U^{-1}]{\simeq} E|_{U \cap V} \xrightarrow[e_V]{\simeq} (U \cap V) \times F, \quad (x,a) \mapsto (e_U|_{E_x})^{-1}(a) \mapsto (x,(e_V|_{E_x} \circ (e_U|_{E_x})^{-1})(a))
  \end{align*}
  and transition map $g_{UV}: U \cap V \to \text{GL}(F)$ is defined to be
  \begin{align*}
    g_{UV}(x) = e_V|_{E_x} \circ (e_U|_{E_x})^{-1}, \quad x \in U \cap V.
  \end{align*}
  Then, the transition maps of the pullback bundle $f^*E$ are of the form
  \begin{align*}
    (f^*g)_{f^{-1}(U) f^{-}(V)}(x) &= (f^*e)_{f^{-1}(V)}|_{(f^*E)_x} \circ ((f^*e)_{f^{-1}(U)}|_{(f^*E)_x})^{-1}, \quad x \in f^{-1}(U) \cap f^{-1}(V) \\
      &= e_V|_{E_{f(x)}} \circ (e_U|_{E_{f(x)}})^{-1} \\
      &= g_{UV}(f(x))
  \end{align*}
  That is, we have
  \begin{align*}
    (f^*g)_{f^{-1}(U) f^{-}(V)} = g_{UV} \circ f.
  \end{align*}
  Since $f$ is continuous, transition maps of $f^*E$ are continuous and define a linear automorphism of $F$ for each $x \in B'$. Therefore, $f^*E$ inherits the natural structure of a vector bundle.
  ```
- Prover notes: Follow the Mathlib proof shape for `VectorBundle.pullback`: atlas members of the pullback fiber bundle are of the form `e.pullback f`; use `Bundle.Trivialization.pullback_linear` for `trivialization_linear'`; for `continuousOn_coordChange'`, destruct the two atlas-members as pullbacks `e.pullback f` and `e'.pullback f`, compose `continuousOn_coordChange 𝕜 e e'` with `f.continuous.continuousOn`, and use the coordinate-change simplification `(e.pullback f).coordChangeL 𝕜 (e'.pullback f) b = e.coordChangeL 𝕜 e' (f b)`.

## Handoff Checklist

- [x] Source document inspected with theorem-like blocks `line-17` and `line-25` recorded.
- [x] Candidate skeletons compared against the source and Mathlib API.
- [x] Direct Lean imports recorded and aligned with `ShadowBench/Source/Main.lean`.
- [x] Root project module covers `ShadowBench.Source.Main` via `ShadowBench/Source.lean`.
- [x] Lean draft contains stable declarations with required names.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [ ] Prover queue has eliminated all `sorry` placeholders in the target file.
