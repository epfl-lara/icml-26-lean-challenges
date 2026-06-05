# Formalization Blueprint: `topology/L3/top_gen_L3_002`

- Source document: `docs/source.tex`
- Companion instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Source Document Inspection

- `formalization_document_inspect docs/source.tex` succeeded; extraction status `ok`.
- Preflight found no sections, labels, references, citations, bibliography files, PDFs, figures, or support assets requiring separate reading.

## Source Map

- line-17 -> `isUnital_auxGroup` (`docs/source.tex` lines 17--25)
- line-28 -> `auxGroup_indep` (`docs/source.tex` theorem lines 28--30; proof lines 30--70)

## Source inventory

- label: line-17
  source_id: line-17
  kind: definition
  source_title: isUnital_auxGroup
  planned_lean_declaration: isUnital_auxGroup
  source_locator: docs/source.tex lines 17--25
  details: Full statement-fidelity details and prover notes are in the matching statement inventory entry below.
- label: line-28
  source_id: line-28
  kind: theorem
  source_title: auxGroup_indep
  planned_lean_declaration: auxGroup_indep
  source_locator: docs/source.tex theorem lines 28--30, proof lines 30--70
  details: Full statement-fidelity details and prover notes are in the matching statement inventory entry below.

## Detected Theorem-Like Blocks

1. `line-17` (definition, lines 17--25) - `isUnital_auxGroup`; Lean declaration `isUnital_auxGroup`.
2. `line-28` (theorem, lines 28--70) - `auxGroup_indep`; Lean declaration `auxGroup_indep`.

## Generated File Layout

Final organization decision: keep the generated formalization in one file. The source has one construction item and one theorem, and Mathlib already provides the underlying homotopy-group development, so splitting would add import overhead without clarifying dependencies.

- `ShadowBench/Source/Main.lean`: generated declarations `isUnital_auxGroup` and `auxGroup_indep`.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`, so project builds cover the generated target module.

## Import Plan

```lean
import Mathlib.Topology.Homotopy.HomotopyGroup
```

## Suggested Search Modules

These are proof/search hints only, not direct imports for `ShadowBench/Source/Main.lean`.

- `Mathlib.GroupTheory.EckmannHilton`
- `Mathlib.Algebra.Group.Ext`
- `Mathlib.Algebra.Group.TransferInstance`
- `Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup`

## Required Names

- `isUnital_auxGroup`
- `auxGroup_indep`

## Candidate Skeleton Review

- `Skeleton1.lean` and `Skeleton2.lean` suggest the expected names/import area but introduce construction `sorry`s and an ill-typed expression `N \ {i}` at the type level.
- `Skeleton3.lean` and `Skeleton4.lean` add exact-name stubs for `isUnital_auxGroup`, but still contain construction `sorry`s and theorem shapes whose conclusions are literally `sorry`.
- No skeleton declaration was copied. The final draft uses the existing Mathlib module `Mathlib.Topology.Homotopy.HomotopyGroup`, which already implements generalized loops, the quotient by relative homotopy, the coordinate loop equivalence, the auxiliary group structure, and the Eckmann--Hilton independence theorem.

## Source Statement Inventory

### line-17

- Source inventory entry `line-17`: definition `[isUnital_auxGroup]` in `docs/source.tex`.
- Source label: `line-17`
- Source inventory entry: `line-17`
- Source inventory label: `line-17`
- Source block label: `line-17`
- Preflight label: `line-17`
- Planned Lean declarations: `isUnital_auxGroup`
- Planned Lean declaration: `isUnital_auxGroup`.
- Source locator: `line-17` (`docs/source.tex` lines 17--25).
- Source statement text:
  ```text
  Let X be a topological space and N be a finite index set.
  Let π_N(X,x) := Ω^N(X,x)/≃_{∂I^N} be the set of homotopy classes relative to the boundary.
  Fix i ∈ N. There is an induced identification of N-loops as loops of (N \ {i})-loops,
  toLoop_i : Ω^N(X,x) → Ω(Ω^{N\{i}}(X,x), const),
  and hence an induced binary operation *_i on π_N(X,x) obtained by transporting ordinary loop concatenation in the i-direction.
  We define auxGroup(i) to be the group whose underlying set and binary operation are π_N(X,x) and *_i, respectively.
  ```
- Planned Lean statement:
  ```lean
  @[reducible]
  def isUnital_auxGroup (X : Type*) [TopologicalSpace X] (x : X)
      (N : Type*) [Fintype N] (i : N) :
      Group (HomotopyGroup N X x)
  ```
- Dependencies: `HomotopyGroup`, `GenLoop`, `homotopyGroupEquivFundamentalGroup`, and `HomotopyGroup.auxGroup` from `Mathlib.Topology.Homotopy.HomotopyGroup`.
- Formal statement review: the source item is labelled `isUnital_auxGroup`, while its body defines the auxiliary group `auxGroup(i)`. The Lean declaration keeps the required source name and abbreviates Mathlib's `HomotopyGroup.auxGroup i`, whose carrier `HomotopyGroup N X x` is the quotient of generalized `N`-loops by relative homotopy.
- Source qualifiers:
  - Mathematical object class: topological space `X`, finite index type `N`, basepoint `x : X`, and coordinate `i : N`.
  - Parameter domain: `X : Type*` with `[TopologicalSpace X]`; `N : Type*` with `[Fintype N]`.
  - Output codomain: a `Group (HomotopyGroup N X x)` structure.
  - Equality/image condition: multiplication is transported from the fundamental group of the `(N \ {i})`-loop space along `homotopyGroupEquivFundamentalGroup i`.
  - Side conditions: finiteness of `N` is retained. Mathlib's coordinate split construction needs decidable equality internally, supplied in the body by `classical`, so it is not a public source side condition.
  - Follow-on claims: this group family is compared by `auxGroup_indep`.
- Lean coverage:
  - `HomotopyGroup N X x` covers the source quotient `π_N(X,x)`.
  - `HomotopyGroup.auxGroup i` covers the group structure with multiplication obtained by transporting loop concatenation in coordinate `i`.
  - The `toLoop_i` bridge is not renamed at top level; it is present in Mathlib through `GenLoop.loopHomeo`, `GenLoop.toLoop`, and `homotopyGroupEquivFundamentalGroup`.
- Scope changes: top-level name `isUnital_auxGroup` is used for the source-labelled construction, even though Mathlib's underlying construction is named `HomotopyGroup.auxGroup`. No construction `sorry` or abstract placeholder is introduced.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: definition is implemented by abbreviation to Mathlib's completed construction; there is no theorem proof obligation for this entry.

### line-28

- Source inventory entry `line-28`: theorem `[auxGroup_indep]` in `docs/source.tex`.
- Source label: `line-28`
- Source inventory entry: `line-28`
- Source inventory label: `line-28`
- Source block label: `line-28`
- Preflight label: `line-28`
- Planned Lean declarations: `auxGroup_indep`
- Planned Lean declaration: `auxGroup_indep`.
- Source locator: `line-28` (`docs/source.tex` theorem lines 28--30 and proof lines 30--70).
- Source statement text:
  ```text
  Let i,j ∈ N. Then the groups auxGroup(i) and auxGroup(j) are isomorphic.
  ```
- Complete source proof text:
  ```text
  If i=j there is nothing to prove, so assume i≠j.
  Consider the two unital multiplications *_i and *_j on the same set π_N(X,x), both having the same unit [c] by the previous theorem.

  The Eckmann--Hilton argument applies in the following form: if two unital binary operations star and diamond on a set have the same unit and satisfy the interchange law
  (a star b) diamond (c star d) = (a diamond c) star (b diamond d)
  for all a,b,c,d, then star=diamond (and in fact the common operation is commutative).

  Thus it suffices to verify the interchange law for *_i and *_j on π_N(X,x).
  Let [a],[b],[c],[d] ∈ π_N(X,x) be represented by generalized loops a,b,c,d ∈ Ω^N(X,x).
  Form the two composites ([a]*_i[b])*_j([c]*_i[d]) and ([a]*_j[c])*_i([b]*_j[d]).
  By construction of *_i and *_j, each side is represented by a generalized N-loop obtained by concatenating maps I^N → X in the i-direction and j-direction respectively.
  When i≠j, these two iterated concatenations correspond to the two ways of composing a map defined on the square I×I in the (i,j)-coordinates by first concatenating horizontally and then vertically, or vice versa.
  These two constructions are homotopic relative to the boundary of the square, hence relative to ∂I^N, by the standard grid homotopy that reparameterizes the (i,j)-coordinates.

  Therefore the two composites represent the same element of π_N(X,x), i.e. the interchange law holds.
  By Eckmann--Hilton it follows that *_i = *_j, hence the group structures auxGroup(i) and auxGroup(j) coincide.
  ```
- Planned Lean statement:
  ```lean
  theorem auxGroup_indep (X : Type*) [TopologicalSpace X] (x : X)
      (N : Type*) [Fintype N] (i j : N) :
      (isUnital_auxGroup X x N i : Group (HomotopyGroup N X x)) =
        isUnital_auxGroup X x N j
  ```
- Dependencies: `isUnital_auxGroup`; `HomotopyGroup.auxGroup_indep`; for a source-style proof, `HomotopyGroup.isUnital_auxGroup`, `EckmannHilton.mul`, `Group.ext`, and the coordinate grid-homotopy/interchange calculation packaged in Mathlib's homotopy-group file.
- Formal statement review: the source states isomorphism of groups and the proof concludes equality/coincidence of the group structures. The Lean theorem states equality of the two `Group (HomotopyGroup N X x)` structures on the common carrier. This is the Mathlib representation of the source proof conclusion and implies the stated isomorphism via the identity equivalence.
- Source qualifiers:
  - Mathematical object class: auxiliary group structures on higher homotopy classes of generalized loops.
  - Quantifier order: ambient `X`, basepoint `x`, finite index type `N`, then indices `i j : N`.
  - Parameter domain: same as `isUnital_auxGroup`.
  - Output codomain/equality condition: equality of the two group structures, representing the source's final “coincide” conclusion.
  - Side conditions: no external `i ≠ j` hypothesis; the proof splits on `i = j` internally.
  - Follow-on claims: source mentions commutativity as an Eckmann--Hilton consequence, but the named theorem only asserts independence/isomorphism, so no separate commutativity declaration is generated.
- Lean coverage:
  - The theorem compares exactly the two groups generated by the source construction entry `line-17`.
  - Equality of group structures is stronger than an explicit isomorphism but is not a weakening; it follows the source proof conclusion and the existing Mathlib theorem `HomotopyGroup.auxGroup_indep`.
- Scope changes: equality is used instead of an explicit `MulEquiv`/categorical group isomorphism to avoid duplicating the common carrier. This is stronger than the stated isomorphism and matches the source proof's final coincidence conclusion. Decidable equality is supplied internally by `classical` for Mathlib's implementation.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: proved by existing Mathlib theorem:
  ```lean
  classical
  simpa [isUnital_auxGroup] using HomotopyGroup.auxGroup_indep (X := X) (x := x) i j
  ```
  A source-faithful proof can instead reproduce Mathlib's proof: split on `i = j`, apply `Group.ext` and `EckmannHilton.mul` using `HomotopyGroup.isUnital_auxGroup`, and discharge interchange by the quotient/grid-homotopy calculation (`transAt_distrib`).

## Handoff Checklist

- [x] Source document inspected with deterministic LaTeX extraction.
- [x] Companion instructions and all candidate skeleton files inspected.
- [x] Local/Mathlib search performed before finalizing declaration names and imports.
- [x] Statement inventory contains source entries `line-17` and `line-28` with declaration names, dependencies, source qualifiers, Lean coverage, scope changes, and proof/prover notes.
- [x] Direct import plan matches `ShadowBench/Source/Main.lean`.
- [x] Local repair removed the extra public `[DecidableEq N]` side condition identified by the batch BLOCK.
- [x] `lake env lean ShadowBench/Source/Main.lean` verifies after the repair.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
