# Formalization Blueprint: `topology/L3/top_gen_L3_007`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: single-file draft containing the three source-backed declarations.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`, so the target module is covered by the root project module.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so project-level verification reaches the generated target.

No file split is currently justified: all source items are short, share the same imports, and the document has no section structure.

## Import Plan

```lean
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Homotopy.Lifting
```

These are the direct imports in `ShadowBench/Source/Main.lean`. The third import is needed because the source's chosen lift is represented by Mathlib's `IsCoveringMap.liftPath` and because Mathlib already contains the corresponding path-lifting API.

## Suggested Search Modules

These are non-gating proof-search hints; they are not additional required imports beyond the import plan unless the prover changes the proof strategy.

- `Mathlib.Topology.Homotopy.Lifting`: `IsCoveringMap.exists_path_lifts`, `IsCoveringMap.liftPath`, `IsCoveringMap.liftPath_lifts`, `IsCoveringMap.liftPath_zero`, `IsCoveringMap.eq_liftPath_iff`.
- `Mathlib.Topology.Covering.Basic`: `IsCoveringMap.eq_of_comp_eq` for uniqueness of lifts over a preconnected space.
- `Mathlib.Topology.Connected.Clopen`: useful if reproving the clopen argument in the source proof instead of using Mathlib's covering-map uniqueness theorem.

## Required Names

- `exists_path_lifts`
- `eq_liftPath_iff`
- `eq_liftPath_iff'`

## Candidate Skeletons Reviewed

- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` give equivalent raw-function statements with explicit `Continuous` hypotheses/conclusions.
- `docs/skeletons/Skeleton4.lean` uses `C(I, X)` and `C(A, E)` to encode paths and continuous maps directly. The final draft follows this representation for the first two items and uses Mathlib's `hp.liftPath` construction for the chosen lift in the third item.
- Skeleton statement order and required names were compared against `docs/source.tex` and `docs/instructions.md`. The source label `liftPath_zero` in line 17 is formalized under the required exported name `exists_path_lifts`.

## Search Results Used

- `lean_search`: `IsCoveringMap.exists_path_lifts` and `IsCoveringMap.liftPath` in `Mathlib.Topology.Homotopy.Lifting` match the source existence/construction of path lifts.
- `lean_search`: `IsCoveringMap.eq_of_comp_eq` in `Mathlib.Topology.Covering.Basic` matches the source uniqueness-of-lifts lemma over a preconnected domain.
- Local Mathlib source inspection confirmed:
  - `IsCoveringMap.exists_path_lifts : ∃ Γ : C(I, E), p ∘ Γ = γ ∧ Γ 0 = e`.
  - `IsCoveringMap.eq_of_comp_eq [PreconnectedSpace A] ... (a : A) (ha : g₁ a = g₂ a) : g₁ = g₂`.
  - `IsCoveringMap.eq_liftPath_iff : Γ = cov.liftPath γ e γ_0 ↔ Continuous Γ ∧ p ∘ Γ = γ ∧ Γ 0 = e`.

## Detected Theorem-Like Blocks

1. `line-17` (lemma, lines 17-40) - liftPath_zero
2. `line-70` (lemma, lines 70-91) - eq_liftPath_iff
3. `line-153` (lemma, lines 153-185) - eq_liftPath_iff'

## Source Map

- line-17 -> `exists_path_lifts` (`docs/source.tex` lines 17-40; proof lines 40-67)
- line-70 -> `eq_liftPath_iff` (`docs/source.tex` lines 70-91; proof lines 91-151)
- line-153 -> `eq_liftPath_iff'` (`docs/source.tex` lines 153-185; proof lines 185-207)

## Source inventory

- label: line-17
  source_id: line-17
  kind: lemma
  source_title: liftPath_zero
  planned_lean_declaration: exists_path_lifts
  source_locator: docs/source.tex lines 17-40, proof lines 40-67
  details: Full statement-fidelity details and prover notes are in the matching source statement inventory entry below.
- label: line-70
  source_id: line-70
  kind: lemma
  source_title: eq_liftPath_iff
  planned_lean_declaration: eq_liftPath_iff
  source_locator: docs/source.tex lines 70-91, proof lines 91-151
  details: Full statement-fidelity details and prover notes are in the matching source statement inventory entry below.
- label: line-153
  source_id: line-153
  kind: lemma
  source_title: eq_liftPath_iff'
  planned_lean_declaration: eq_liftPath_iff'
  source_locator: docs/source.tex lines 153-185, proof lines 185-207
  details: Full statement-fidelity details and prover notes are in the matching source statement inventory entry below.

## Source Statement Inventory

### line-17

- Source inventory entry `line-17`: lemma `[liftPath_zero]` in `docs/source.tex`, exported as `exists_path_lifts` per `docs/instructions.md`.
- Source label: `line-17`.
- Source locator: `docs/source.tex`, lemma environment lines 17--40; proof lines 40--67.
- Planned Lean declaration: `exists_path_lifts` in `ShadowBench/Source/Main.lean`.
- Kind: theorem.

- Source locator: `docs/source.tex`, statement lines 17-40, proof lines 40-67.
- Planned Lean declaration:

```lean
theorem exists_path_lifts {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (hp : IsCoveringMap p) {γ : C(I, X)} {e : E} (he : γ 0 = p e) :
    ∃ Γ : C(I, E), p ∘ Γ = γ ∧ Γ 0 = e
```

- Skeleton candidate used: shaped by `Skeleton4.lean`, renamed from the source display title to the instruction-required `exists_path_lifts`.
- Dependencies: `IsCoveringMap`, `unitInterval.I`, continuous maps `C(I, X)`, and for proof search `IsCoveringMap.exists_path_lifts`.
- Source statement: Let `p : E → X` be a covering map. Let `γ : I → X` be a path and `e ∈ E` with `γ(0) = p(e)`. Then there exists a path `Γ : I → E` with `p ∘ Γ = γ` and `Γ(0) = e`.
- Source qualifiers:
  - Object class: `p` is a covering map between topological spaces `E` and `X`.
  - Quantifier order: choose spaces, covering map, path `γ`, starting lift point `e`, and endpoint compatibility; then assert existence of a lifted path.
  - Parameter domain/codomain: `γ : I → X`, `Γ : I → E`, where `I` is the unit interval.
  - Equality/image condition: `p ∘ Γ = γ` as functions on `I`.
  - Side condition: `γ 0 = p e`.
  - Follow-on claim: `Γ 0 = e`.
- Lean coverage: `γ : C(I, X)` and `Γ : C(I, E)` encode source paths as continuous maps from the unit interval; `hp : IsCoveringMap p` encodes the covering-map object class; `he` covers the initial-point side condition; the existential conclusion covers both lifting equality and initial value.
- Scope changes: no mathematical weakening or strengthening. Representation note: paths are encoded as `ContinuousMap` values, so continuity is in the type rather than a separate conjunct.
- Formal statement review: draft comparison records all source qualifiers in the Lean statement. The exported name follows `docs/instructions.md` rather than the source bracket title.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text:
  > Since `p` is a covering map, every point `x ∈ X` has an evenly covered open neighborhood `U_x`. The image `γ(I)` is compact, so finitely many such neighborhoods cover it. By subdividing the interval `I=[0,1]`, we may choose numbers `0=t_0 ≤ t_1 ≤ ⋯ ≤ t_n=1` such that for each `i`, the image of `γ` on `[t_i,t_{i+1}]` is contained in some evenly covered open set `U_i`.
  >
  > We construct the lift `Γ` inductively. At `t=0`, we require `Γ(0)=e`. Since `p(e)=γ(0)∈U_0`, there is a unique sheet of `p^{-1}(U_0)` containing `e`, and the restriction of `p` to that sheet is a homeomorphism onto `U_0`. Hence `γ|_{[t_0,t_1]}` has a unique lift on `[t_0,t_1]` starting at `e`.
  >
  > Now suppose `Γ` has been defined continuously on `[0,t_i]`. Then the point `Γ(t_i)` lies above `γ(t_i)`. Since `γ([t_i,t_{i+1}])⊆U_i`, there is again a unique sheet over `U_i` containing `Γ(t_i)`, and by inverting the homeomorphism on that sheet we obtain a unique continuation of `Γ` over `[t_i,t_{i+1}]`.
  >
  > Proceeding inductively over all subintervals, we obtain a continuous path `Γ:I→E` such that `p∘Γ=γ` and `Γ(0)=e`.
- Source proof / prover notes: A direct proof should be `exact hp.exists_path_lifts γ e he` after the Homotopy/Lifting import. If reproving, follow the source finite-subdivision argument over evenly covered neighborhoods.

### line-70

- Source inventory entry `line-70`: lemma `[eq_liftPath_iff]` in `docs/source.tex`.
- Source label: `line-70`.
- Source locator: `docs/source.tex`, lemma environment lines 70--91; proof lines 91--151.
- Planned Lean declaration: `eq_liftPath_iff` in `ShadowBench/Source/Main.lean`.
- Kind: lemma.

- Source locator: `docs/source.tex`, statement lines 70-91, proof lines 91-151.
- Planned Lean declaration:

```lean
lemma eq_liftPath_iff {E X A : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace A]
    {f : E → X} (hf : IsCoveringMap f) [PreconnectedSpace A] {g₁ g₂ : C(A, E)}
    (hfg : f ∘ g₁ = f ∘ g₂) (a : A) (ha : g₁ a = g₂ a) :
    g₁ = g₂
```

- Skeleton candidate used: shaped by `Skeleton4.lean`; this matches the source by encoding continuous maps as `C(A, E)` and preconnectedness as a typeclass.
- Dependencies: `IsCoveringMap`, `PreconnectedSpace`, continuous maps `C(A, E)`, and for proof search `IsCoveringMap.eq_of_comp_eq`.
- Source statement: Let `f : E → X` be a covering map, and let `A` be a preconnected topological space. Suppose `g₁,g₂ : A → E` are continuous maps such that `f ∘ g₁ = f ∘ g₂`. If there exists a point `a ∈ A` such that `g₁(a)=g₂(a)`, then `g₁=g₂`.
- Source qualifiers:
  - Object class: `f` is a covering map; `A` is a preconnected topological space.
  - Quantifier order: choose spaces and covering map, choose continuous maps `g₁,g₂`, assume same projection, assume a witness point of agreement; conclude equality.
  - Parameter domain/codomain: `g₁,g₂ : A → E`.
  - Equality/image condition: `f ∘ g₁ = f ∘ g₂`.
  - Side condition: there is a witness `a : A` with `g₁ a = g₂ a`.
  - Follow-on claim: equality of maps `g₁ = g₂`.
- Lean coverage: `g₁,g₂ : C(A, E)` encode continuity; `[PreconnectedSpace A]` encodes the source condition that the whole space `A` is preconnected; the existential witness is represented by explicit parameters `(a : A) (ha : g₁ a = g₂ a)`, which is the curried form of the source implication from an existence hypothesis.
- Scope changes: no mathematical weakening or strengthening. Representation note: source continuity hypotheses are carried by `ContinuousMap`, and the existence hypothesis is represented by an explicit witness.
- Formal statement review: draft comparison records the covering-map hypothesis, preconnected-domain hypothesis, continuous-map hypotheses, same-projection hypothesis, witness of agreement, and equality conclusion.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text:
  > Let `S={x∈A | g₁(x)=g₂(x)}`. We will show that `S` is both open and closed in `A`. Since `a∈S`, the set `S` is nonempty. Because `A` is preconnected, it will follow that `S=A`, hence `g₁=g₂`.
  >
  > First we show that `S` is open. Let `x∈S`. Set `e:=g₁(x)=g₂(x)`. Since `f` is a covering map, there exists an evenly covered open neighborhood `U⊆X` of `f(e)`. Let `V` be the sheet of `f^{-1}(U)` containing `e`. Then `f|_V:V→U` is a homeomorphism.
  >
  > Since `g₁` and `g₂` are continuous and `g₁(x),g₂(x)∈V`, after shrinking to an open neighborhood `W` of `x` in `A`, we may assume that `g₁(W)⊆V` and `g₂(W)⊆V`. For every `y∈W`, we have `f(g₁(y))=f(g₂(y))`. Since `f|_V` is injective, it follows that `g₁(y)=g₂(y)`. Thus `W⊆S`, so `S` is open.
  >
  > Next we show that `S` is closed. Let `x∈overline(S)`. We again choose an evenly covered neighborhood `U⊆X` of `f(g₁(x))=f(g₂(x))`, and let `V₁,V₂` be the sheets containing `g₁(x)` and `g₂(x)`, respectively. By continuity, after shrinking to some open neighborhood `W` of `x`, we may assume that `g₁(W)⊆V₁` and `g₂(W)⊆V₂`.
  >
  > Since `x∈overline(S)`, the set `W∩S` is nonempty. Choose `y∈W∩S`. Then `g₁(y)=g₂(y)`. But `g₁(y)∈V₁` and `g₂(y)∈V₂`, and distinct sheets over `U` are disjoint. Therefore `V₁=V₂`. Hence both `g₁` and `g₂` map `W` into the same sheet `V₁`, and since `f∘g₁=f∘g₂` and `f|_{V₁}` is injective, we get `g₁|_W=g₂|_W`. In particular, `g₁(x)=g₂(x)`, so `x∈S`. Therefore `S` is closed.
  >
  > We have shown that `S` is a nonempty clopen subset of the preconnected space `A`. Hence `S=A`, and therefore `g₁=g₂`.
- Source proof / prover notes: Mathlib already packages this clopen/sheet argument as `hf.eq_of_comp_eq`. With `g₁,g₂ : C(A,E)`, use their `.continuous` fields and then turn equality of underlying functions into equality of continuous maps, likely via `DFunLike.coe_fn_eq` or extensionality.

### line-153

- Source inventory entry `line-153`: lemma `[eq_liftPath_iff']` in `docs/source.tex`.
- Source label: `line-153`.
- Source locator: `docs/source.tex`, lemma environment lines 153--185; proof lines 185--207.
- Planned Lean declaration: `eq_liftPath_iff'` in `ShadowBench/Source/Main.lean`.
- Kind: lemma.

- Source locator: `docs/source.tex`, statement lines 153-185, proof lines 185-207.
- Planned Lean declaration:

```lean
lemma eq_liftPath_iff' {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (hp : IsCoveringMap p) {γ : C(I, X)} {e : E} (he : γ 0 = p e)
    (Γ : I → E) :
    Γ = hp.liftPath γ e he ↔ Continuous Γ ∧ p ∘ Γ = γ ∧ Γ 0 = e
```

- Skeleton candidate used: informed by `Skeleton4.lean`, but revised to use the actual Mathlib chosen lift `hp.liftPath γ e he`, matching the source phrase "the chosen lift" and avoiding an additional construction stub.
- Dependencies: `IsCoveringMap.liftPath`, `IsCoveringMap.liftPath_lifts`, `IsCoveringMap.liftPath_zero`, `IsCoveringMap.eq_liftPath_iff`, and the uniqueness lemma over the preconnected unit interval.
- Source statement: Let `p : E → X` be a covering map, let `γ : I → X` be a path, and let `e ∈ E` satisfy `γ(0)=p(e)`. Let `γ̃ : I → E` be the chosen lift of `γ` starting at `e`, so that `p ∘ γ̃ = γ` and `γ̃(0)=e`. Then for any map `Γ : I → E`, `Γ=γ̃` iff `Γ` is continuous, `p ∘ Γ=γ`, and `Γ(0)=e`.
- Source qualifiers:
  - Object class: `p` is a covering map; `γ` is a path on the unit interval.
  - Quantifier order: choose covering map, path, starting point and compatibility; use the chosen lift; then quantify an arbitrary map `Γ`.
  - Parameter domain/codomain: `γ : I → X`, chosen lift and arbitrary map `Γ : I → E`.
  - Equality/image condition: `p ∘ Γ = γ`.
  - Side conditions: `Γ` is continuous and `Γ 0 = e`; the chosen lift has the corresponding lifting and initial-value properties.
  - Follow-on claim: equivalence between equality to the chosen lift and satisfying the lift conditions.
- Lean coverage: `γ : C(I, X)` encodes the source path; `hp.liftPath γ e he` is the chosen Mathlib lift and is accompanied by `hp.liftPath_lifts` and `hp.liftPath_zero`; the left-to-right direction of the iff asserts that this chosen lift has the required continuity, projection equality, and initial value; `Γ : I → E` remains an arbitrary function, so the right side explicitly includes `Continuous Γ`.
- Scope changes: no mathematical weakening or strengthening. Representation note: the source variable `\widetilde{γ}` is represented by the existing construction `hp.liftPath γ e he` instead of an extra quantified variable; this is the intended bridge for "chosen lift".
- Formal statement review: draft comparison records the covering-map hypothesis, path and start compatibility, chosen-lift representation, arbitrary map `Γ`, and both directions of the iff.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text:
  > If `Γ=γ̃`, then `Γ` is continuous, since `γ̃` is a path, and it satisfies `p∘Γ = p∘γ̃ = γ` and `Γ(0)=γ̃(0)=e`.
  >
  > Conversely, suppose `Γ:I→E` is continuous and satisfies `p∘Γ=γ` and `Γ(0)=e`. Then both `Γ` and `γ̃` are lifts of the same path `γ`, and they agree at the point `0∈I`. Since `p` is a covering map and `I` is connected, the uniqueness of lifts (the Lemma above) implies that `Γ=γ̃`.
- Source proof / prover notes: Mathlib's `hp.eq_liftPath_iff` is essentially this statement. If using the previous uniqueness lemma manually, apply it to the arbitrary `Γ` and to `hp.liftPath γ e he`, with agreement at `0` from the initial-value condition and `hp.liftPath_zero`.

## Handoff Checklist

- [x] Source document `docs/source.tex`, workflow context, and preflight manifest read.
- [x] Candidate skeletons read and compared with the source.
- [x] Local project and Mathlib search performed before choosing declarations.
- [x] Blueprint contains source inventory entries `line-17`, `line-70`, and `line-153` with source qualifiers, Lean coverage, scope changes, complete source proof text, and prover notes.
- [x] Root project module imports the generated target module through `ShadowBench.lean` and `ShadowBench/Source.lean`.
- [x] Project-level Lean verification was run after the generated file and imports were in place; it succeeded with only the intended `sorry` warnings in the theorem skeletons.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [ ] Prover handoff after independent review.

## Statement/Source Review Gate

The draft intentionally stops here with theorem proofs as `by sorry`. Next required action is an independent read-only statement/source verification pass. After that review records its result, a prover run can be launched, for example:

```text
/prove ShadowBench/Source/Main.lean
```
