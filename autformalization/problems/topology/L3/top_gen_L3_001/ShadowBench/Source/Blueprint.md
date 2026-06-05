# Formalization Blueprint: `topology/L3/top_gen_L3_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: single-file formalization draft for all named source items.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`.

No file split is currently useful: the source has one short cluster of definitions/theorems and Mathlib already contains the relevant generalized-loop infrastructure.

## Import Plan

```lean
import Mathlib.Topology.Homotopy.HomotopyGroup
```

This direct import provides the source concepts used in the Lean file: `GenLoop`, `Cube.boundary`, `Cube.insertAt`, `GenLoop.toLoop`, `GenLoop.Homotopic`, `GenLoop.homotopicFrom`, and the scoped notations `I^`, `Ω`, and `Ω^`.  It publicly imports the starting modules listed in `docs/instructions.md`.

## Suggested Search Modules

These are non-gating search hints for the later prover and should not be forced into the Lean import block unless a proof actually needs them.

- `Mathlib.Topology.Homotopy.HomotopyGroup`
- `Mathlib.Topology.Homotopy.Path`
- `Mathlib.Topology.Homotopy.Basic`

Key local/Mathlib names found by search:

- `Cube.boundary`, `Cube.splitAt`, `Cube.insertAt`, `Cube.insertAt_boundary`
- `GenLoop`, `GenLoop.boundary`, `GenLoop.const`, `GenLoop.toLoop`, `GenLoop.toLoop_apply`
- `GenLoop.Homotopic`, `GenLoop.homotopicFrom`
- `Path.Homotopic`, `ContinuousMap.HomotopyRel`

## Candidate Skeletons

Inspected:

- `docs/skeletons/Skeleton1.lean`
- `docs/skeletons/Skeleton2.lean`
- `docs/skeletons/Skeleton3.lean`
- `docs/skeletons/Skeleton4.lean`

Skeleton assessment:

- The skeletons preserve the required declaration names, but they introduce stub definitions such as `GeneralizedLoops` and `canonicalHomeomorphism`, and use an ill-matched expression `N ⊓ {i}` for the deleted index set.  Those construction stubs would block proof handoff.
- The final draft instead uses Mathlib's existing source-matching generalized-loop formalization: `GenLoop N X x` for `Ω^N(X,x)`, `Cube.insertAt i` for the canonical insertion homeomorphism `Ψ_i`, and the subtype `{j // j ≠ i}` for `N \ {i}`.
- Skeletons were used only as naming hints; statement shapes were redrafted against `docs/source.tex` and Mathlib's `HomotopyGroup` API.

## Required Names

- `homotopyTo`
- `homotopyTo_apply`
- `homotopicTo`

## Source Statement Inventory

### line-17

- Source locator: `docs/source.tex`, lines 17-42.
- Environment: definition.
- Planned Lean declarations: `homotopyTo`.
- Lean declaration kind: `def`.
- Skeleton candidate used: skeleton naming only; the final construction uses Mathlib's `GenLoop.toLoop` rather than the skeleton stubs.
- Dependencies: `GenLoop`, `Cube.insertAt`, `GenLoop.toLoop`, `GenLoop.const`, scoped notations `I^`, `Ω`, `Ω^` from `Mathlib.Topology.Homotopy.HomotopyGroup`.
- Planned Lean statement:

```lean
def homotopyTo {N X : Type*} [DecidableEq N] [TopologicalSpace X]
    {x : X} (i : N) (p : Ω^ N X x) : Ω (Ω^ { j // j ≠ i } X x) GenLoop.const :=
  GenLoop.toLoop i p
```

- Source qualifiers:
  - Mathematical object class: a topological space `X`, a base point `x : X`, a finite index set `N`, and a chosen index `i ∈ N`.
  - Quantifier order / parameter domain: after `X`, `x`, `N`, and `i`, the input is a generalized loop `p ∈ Ω^N(X,x)`, i.e. a continuous map `I^N → X` sending `∂ I^N` to `x`.
  - Parameter-domain representation bridge: the deleted index set `N \ {i}` (also written `N \setminus i`) is represented in Lean by the subtype `{j // j ≠ i}`.
  - Homeomorphism / image condition: the canonical coordinate insertion homeomorphism `Ψ_i : I × I^{N\setminus{i}} ≃ₜ I^N` is represented by `Cube.insertAt i`, whose value inserts `t : I` in coordinate `i` and uses `y : I^{N\setminus{i}}` on the other coordinates.
  - Source output codomain: the definition first specifies a path `I → Ω^{N\setminus{i}}(X,x)`; the following source theorem asserts this path is a based loop at the constant generalized loop.
  - Equality condition: `(toLoop_i(p))(t)(y) = p(Ψ_i(t,y))`; in Lean this is the companion theorem `homotopyTo_apply`.
  - Follow-on claims: well-defined slice boundary preservation and endpoint constancy are part of source theorem `line-44`, not additional assumptions on this definition.
- Lean coverage:
  - `Ω^ N X x` covers the source generalized `N`-loop object, including continuity and boundary value `x`.
  - `homotopyTo` returns `Ω (Ω^ {j // j ≠ i} X x) GenLoop.const`; its underlying path covers the definition's path codomain, and its endpoint fields cover the based-loop upgrade proved in `line-44`.
  - `Cube.insertAt i` covers the source homeomorphism `Ψ_i` and the deleted-coordinate subtype explicitly records the representation of `N \ {i}`.
  - `homotopyTo_apply` records the pointwise formula required by the definition.
  - No construction stubs are introduced; the Lean definition is implemented as `GenLoop.toLoop i p`.
- Scope changes:
  - The Lean declaration generalizes the source's finite index-set qualifier to any index type with `[DecidableEq N]`. This explicit strengthening still covers every finite source case after choosing classical decidable equality, and it matches source theorem `line-73`, where `N` is stated as an arbitrary index set.
  - `[DecidableEq N]` is a Lean implementation side condition for coordinate deletion/insertion in `Cube.insertAt`; it is not an extra mathematical hypothesis in the source.
  - The Lean definition packages the path as a based loop, combining the source definition with the well-definedness/endpoint content of `line-44`.
- Formal statement review: The Lean definition matches the source under the explicit subtype representation of `N \ {i}`, the explicit decidable-equality implementation side condition, and the recorded generalization beyond finite index sets.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: This is a definition with no separate source proof. Later proof obligations should unfold `homotopyTo` to `GenLoop.toLoop`; the pointwise computation is `GenLoop.toLoop_apply`/`rfl`, and boundary/endpoints are handled by `Cube.insertAt_boundary` and the `GenLoop` boundary property.

### line-44

- Source locator: `docs/source.tex`, theorem lines 44-54; proof lines 54-68.
- Environment: theorem.
- Planned Lean declarations: `homotopyTo` (well-defined codomain) and `homotopyTo_apply` (pointwise formula).
- Lean declaration kind: `theorem` with proof placeholder for the prover queue; companion definition `homotopyTo` is implemented.
- Skeleton candidate used: skeleton naming only; final theorem avoids existential map wrappers and stub subgoals.
- Dependencies: `homotopyTo`, `GenLoop.toLoop_apply`, `Cube.insertAt_boundary`, `GenLoop.boundary`, `Path.source`, `Path.target`.
- Planned Lean statement:

```lean
theorem homotopyTo_apply {N X : Type*} [DecidableEq N] [TopologicalSpace X]
    {x : X} (i : N) (p : Ω^ N X x) (t : I) (y : I^{ j // j ≠ i }) :
    homotopyTo i p t y = p (Cube.insertAt i (t, y)) := by
  sorry
```

- Source qualifiers:
  - Mathematical object class / quantifier order: topological space `X`, base point `x`, finite index set `N`, index `i ∈ N`, then a generalized `N`-loop `p`.
  - Parameter domain: `Ω^N(X,x)`, the generalized loops `I^N → X` sending `∂ I^N` to `x`.
  - Output codomain: a map into `Ω(Ω^{N\setminus{i}}(X,x), const)`, i.e. a based loop in the generalized-loop space based at the constant generalized loop.
  - Equality/image condition: the associated loop is the slice obtained by evaluating `p` at the canonical inserted coordinate `Ψ_i(t,y)`.
  - Well-definedness side conditions/follow-on claims: for fixed `t`, the slice is a generalized `(N\setminus i)`-loop; for `t = 0` and `t = 1`, the slice is the constant generalized loop.
- Lean coverage:
  - The type of `homotopyTo` enforces the source theorem's well-defined map `Ω^N(X,x) → Ω(Ω^{N\setminus i}(X,x), const)`.
  - The codomain `Ω (Ω^ {j // j ≠ i} X x) GenLoop.const` covers both the loop-space output and the basepoint `const` qualifier.
  - `homotopyTo_apply` records the pointwise equality identifying the Lean map with the source formula using `Cube.insertAt i` for `Ψ_i`.
  - Boundary preservation and endpoint constancy are internal fields of `GenLoop.toLoop`; the source proof's two checks correspond to `Cube.insertAt_boundary` and `GenLoop.boundary`.
- Scope changes:
  - Same explicit generalization from finite `N` to `[DecidableEq N]` as `line-17`.
  - Same subtype representation of `N \ {i}` as `{j // j ≠ i}`.
  - The source's prose theorem is represented by the implemented definition type of `homotopyTo` plus the theorem `homotopyTo_apply`; this split is a Lean packaging change, not a mathematical weakening or omission.
- Formal statement review: The source theorem's well-defined-map content is carried by `homotopyTo`, and the required source formula is carried by `homotopyTo_apply`; together these declarations match the source theorem under the recorded representation bridge.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: For each fixed `t ∈ I`, the map `y ↦ p(Ψ_i(t,y))` is a generalized `(N\setminus i)`-loop based at `x`, since if `y ∈ ∂ I^{N\setminus i}` then `Ψ_i(t,y) ∈ ∂ I^N` and hence `p(Ψ_i(t,y)) = x`. Moreover, `toLoop_i(p)` is a based loop in the loop space `Ω^{N\setminus i}(X,x)`: for all `y ∈ I^{N\setminus i}`, `(toLoop_i(p))(0)(y)=x` and `(toLoop_i(p))(1)(y)=x`, since `Ψ_i(0,y)` and `Ψ_i(1,y)` lie in `∂ I^N`.
- Prover notes: Start with `unfold homotopyTo`; `rfl` or `exact GenLoop.toLoop_apply i` should close the computation theorem. If proving well-definedness directly, use `Cube.insertAt_boundary i (Or.inr yH)` for the deleted-coordinate boundary and `⟨i, Or.inl ...⟩`/`⟨i, Or.inr ...⟩` for endpoint coordinates.

### line-73

- Source locator: `docs/source.tex`, theorem lines 73-85; proof lines 85-161.
- Environment: theorem.
- Planned Lean declarations: `homotopicTo`.
- Lean declaration kind: `theorem` with proof placeholder for the prover queue.
- Skeleton candidate used: skeleton naming only; final theorem uses Mathlib's existing `Path.Homotopic` and `GenLoop.Homotopic` instead of ad hoc existential homotopy records.
- Dependencies: `homotopyTo`, `GenLoop.Homotopic`, `Path.Homotopic`, `GenLoop.homotopicFrom`, `Cube.splitAt`, `Cube.insertAt`, `ContinuousMap.HomotopyRel`.
- Planned Lean statement:

```lean
theorem homotopicTo {N X : Type*} [DecidableEq N] [TopologicalSpace X]
    {x : X} (i : N) {p q : Ω^ N X x}
    (H : (homotopyTo i p).Homotopic (homotopyTo i q)) :
    GenLoop.Homotopic p q := by
  sorry
```

- Source qualifiers:
  - Mathematical object class / quantifier order: topological space `X`, base point `x`, index set `N`, chosen coordinate `i ∈ N`, then generalized loops `p q ∈ Ω^N(X,x)`.
  - Parameter domain: `p` and `q` are generalized loops `I^N → X` sending `∂ I^N` to `x`.
  - Hypothesis: the associated paths `toLoop_i(p)` and `toLoop_i(q)` from `I` to `Ω^{N\setminus{i}}(X,x)` are homotopic relative to endpoints.
  - Output/conclusion codomain: `p` and `q` are homotopic relative to the boundary `∂ I^N`.
  - Representation bridge / equality condition used in the statement: `toLoop_i` is the `homotopyTo` defined above, with pointwise behavior recorded in `homotopyTo_apply`.
  - Source proof construction: use the product homeomorphism `Φ_i : I^N ≃ I × I^{N\setminus{i}}` with inverse `Ψ_i`, then uncurry the loop-space homotopy to a boundary-relative homotopy `I × I^N → X`.
- Lean coverage:
  - `(homotopyTo i p).Homotopic (homotopyTo i q)` is Mathlib's `Path.Homotopic`, i.e. homotopy of paths with endpoints fixed, matching “homotopic relative to endpoints”.
  - `GenLoop.Homotopic p q` is defined as `p.1.HomotopicRel q.1 (Cube.boundary N)`, exactly the boundary-relative conclusion.
  - `Cube.splitAt i` and `Cube.insertAt i` provide the source homeomorphisms `Φ_i` and `Ψ_i`; `{j // j ≠ i}` provides the deleted-index representation.
  - The theorem is stated for arbitrary index sets with `[DecidableEq N]`, matching the theorem's source wording “`N` an index set” modulo the Lean implementation side condition.
- Scope changes:
  - `[DecidableEq N]` is the only added Lean side condition and is needed for the Mathlib coordinate split/insert construction; it is an implementation-side representation requirement.
  - The Lean theorem packages explicit homotopies using Mathlib's `Path.Homotopic`/`ContinuousMap.HomotopyRel` records rather than an informal map `H : I × I → Ω^{N\setminus{i}}(X,x)`. This is a representation bridge, not an omission.
  - `N \ {i}` is represented as the subtype `{j // j ≠ i}`.
- Formal statement review: The Lean hypothesis and conclusion match the source theorem under the explicit representation bridges: path homotopy relative endpoints is `Path.Homotopic`, and boundary-relative generalized-loop homotopy is `GenLoop.Homotopic`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: Identify the cube with a product via `Φ_i : I^N ≃ I × I^{N\setminus{i}}`, `Φ_i(y) = (y(i), y|_{N\setminus{i}})`, with inverse `Ψ_i`. Given a homotopy `H : I × I → Ω^{N\setminus{i}}(X,x)` from `toLoop_i(p)` to `toLoop_i(q)`, define `\widetilde H : I × I^N → X` by `\widetilde H(s,y) = H(t₀,s)(y')`, where `(t₀,y') = Φ_i(y)`. Continuity follows from continuity of `H` and `Φ_i`. If `y ∈ ∂ I^N`, choose a boundary coordinate `j`. If `j=i`, then `t₀ ∈ {0,1}` and, because `H` is a homotopy between based loops, `H(t₀,s)` is the constant loop at `x`. If `j≠i`, then `y' ∈ ∂ I^{N\setminus{i}}`, so every generalized loop `H(t₀,s)` sends `y'` to `x`. Thus `\widetilde H` is constantly `x` on `∂ I^N × I`. At the endpoints, `\widetilde H(0,y)=H(t₀,0)(y')=toLoop_i(p)(t₀)(y')=p(Ψ_i(t₀,y'))=p(y)`, and similarly `\widetilde H(1,y)=q(y)`. Hence `p` and `q` are homotopic relative to the boundary.
- Prover notes: The direct Mathlib theorem is `GenLoop.homotopicFrom`. A likely proof is `simpa [homotopyTo] using (GenLoop.homotopicFrom (i := i) (p := p) (q := q) H)`. For a manual proof, use `GenLoop.homotopyFrom` and the boundary case split from the source proof; the key boundary facts are encoded near lines 370-396 of `Mathlib.Topology.Homotopy.HomotopyGroup`.

## Formalization / Handoff Checklist

- [x] Source document `docs/source.tex` inspected with theorem-like inventory.
- [x] Preflight manifest and planner context read.
- [x] Candidate skeletons read and compared against the source.
- [x] Local project and Mathlib searched before choosing declarations.
- [x] Source inventory entries `line-17`, `line-44`, and `line-73` filled with declaration names, dependencies, source qualifiers, Lean coverage, scope changes, and prover notes.
- [x] Root module chain already imports the generated target module: `ShadowBench.lean` → `ShadowBench.Source` → `ShadowBench.Source.Main`.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [x] Proof-ready handoff accepted for the later prove workflow by formalization PASS and 2026-06-05 audit.
