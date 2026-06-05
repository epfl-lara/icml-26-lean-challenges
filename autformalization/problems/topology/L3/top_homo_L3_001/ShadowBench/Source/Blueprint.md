# Formalization Blueprint: `topology/L3/top_homo_L3_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: single-file draft for the two source-backed declarations.
- Root coverage: `ShadowBench.lean` imports `ShadowBench.Source`, and `ShadowBench/Source.lean` imports `ShadowBench.Source.Main`, so a plain project build covers the generated target module.

## Import Plan

```lean
import Mathlib.Topology.Homotopy.HomotopyGroup
```

The target file should keep this as its direct import. This Mathlib module publicly imports the group-transfer, fundamental-group, and Eckmann--Hilton files needed by the source argument.

## Suggested Search Modules

Non-gating search hints for the proof phase:

- `Mathlib.Topology.Homotopy.HomotopyGroup`
- `Mathlib.GroupTheory.EckmannHilton`
- `Mathlib.Algebra.Group.Ext`
- `Mathlib.Algebra.Group.TransferInstance`
- `Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup`

## Required Names

- `isUnital_auxGroup`
- `auxGroup_indep`

## Source Statement Inventory

### line-17

- Source inventory key: `line-17`.
- Source locator: `line-17` (`docs/source.tex`, definition block lines 17--25).
- Planned Lean declaration: `isUnital_auxGroup` in `ShadowBench/Source/Main.lean`.
- Declaration kind: implemented `noncomputable def`; not a proof obligation.
- Lean statement:

```lean
noncomputable def isUnital_auxGroup
    (X : Type u) [TopologicalSpace X] (N : Type v) [Fintype N]
    (x : X) (i : N) : Group (HomotopyGroup N X x)
```

- Source statement: Let `X` be a topological space and `N` a finite index set. Let
  `π_N(X,x) = Ω^N(X,x)/≃_{∂ I^N}` be homotopy classes relative to the boundary. For fixed
  `i ∈ N`, identify `N`-loops as loops of `(N \ {i})`-loops via `toLoop_i`, transport loop
  concatenation in the `i`-direction, and define `auxGroup(i)` to be the resulting group on
  `π_N(X,x)`.
- Source qualifiers:
  - Mathematical object class: topological space `X` with basepoint `x`, finite index type `N`, and index `i : N`.
  - Quantifier order and parameter domain: first `X`, then finite index type `N`, then basepoint `x`, then fixed index `i : N`.
  - Domain/codomain: returns a `Group` structure on the homotopy classes `π_N(X,x)`.
  - Representation: generalized loops `Ω^N(X,x)` are maps from the unit cube to `X` constant on the boundary, quotiented by relative homotopy.
  - Operation: transported loop concatenation in coordinate `i`.
  - Equality/image condition, side conditions, and follow-on claims: no equality theorem is asserted by this definition; no extra side condition beyond finiteness of `N`; the displayed `toLoop_i` identification and transported multiplication are part of the definition.
- Lean coverage:
  - The generated declaration `isUnital_auxGroup` in `ShadowBench/Source/Main.lean` has exactly the required source name and codomain `Group (HomotopyGroup N X x)`.
  - Uses Mathlib's `HomotopyGroup N X x` for `π_N(X,x)`.
  - Uses Mathlib's `HomotopyGroup.auxGroup i`, which is defined by transporting the fundamental-group loop composition along the coordinate-`i` equivalence `homotopyGroupEquivFundamentalGroup`.
  - The source block title is `isUnital_auxGroup`; the Lean declaration keeps this required name while its value is the source's auxiliary group structure. Mathlib's canonical internal declaration is `HomotopyGroup.auxGroup`.
- Scope changes:
  - The Lean declaration uses a finite typeclass `[Fintype N]` for the source phrase "finite index set" and obtains the coordinate decidable equality class classically inside the implementation.
  - The detailed construction of `toLoop_i` is imported rather than redefined in this file; it is covered by Mathlib's existing `homotopyGroupEquivFundamentalGroup`/`auxGroup` construction, so this is a representation bridge rather than a weakening.
- Dependencies:
  - `HomotopyGroup N X x`
  - `HomotopyGroup.auxGroup`
  - `Mathlib.Topology.Homotopy.HomotopyGroup`
- Skeleton candidate used: none copied. Skeletons 1--4 introduced ad hoc models (`IteratedLoopSpace`, `PiNQuotient`, `toLoop_i`); the current draft instead uses Mathlib's existing homotopy-group implementation found by `lean_search`.
- Formal statement review: draft aligns the source definition with Mathlib's homotopy-group representation and preserves the required source title as the declaration name; independent review should confirm that using the existing Mathlib construction is acceptable for the `toLoop_i`/transport bridge.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: no source proof is attached because this block is a definition. The construction is implemented, not a theorem queue item. For later proofs, use Mathlib facts `HomotopyGroup.auxGroup`, `HomotopyGroup.isUnital_auxGroup`, and `homotopyGroupEquivFundamentalGroup`.

### line-28

- Source inventory key: `line-28`.
- Source locator: `line-28` (`docs/source.tex`, theorem block lines 28--30; proof lines 30--70).
- Planned Lean declaration: `auxGroup_indep` in `ShadowBench/Source/Main.lean`.
- Declaration kind: theorem; proof is intentionally left for the later `/prove` workflow.
- Lean statement:

```lean
theorem auxGroup_indep
    (X : Type u) [TopologicalSpace X] (N : Type v) [Fintype N]
    (x : X) (i j : N) :
    (isUnital_auxGroup X N x i : Group (HomotopyGroup N X x)) =
      isUnital_auxGroup X N x j
```

- Source statement: Let `i,j ∈ N`. Then the groups `auxGroup(i)` and `auxGroup(j)` are isomorphic.
- Source qualifiers:
  - Mathematical object class: the same topological space/basepoint/index data as `line-17`.
  - Quantifier order: after `X`, `N`, and `x`, quantify `i j : N`.
  - Parameter domain: `i` and `j` range over the finite index type `N`; no separate membership predicate is needed in Lean because `i j : N`.
  - Output codomain: the source conclusion is a group isomorphism between `auxGroup(i)` and `auxGroup(j)`.
  - Domain/codomain representation: both groups have the same underlying carrier `π_N(X,x)`.
  - Equality/isomorphism condition: the source statement says isomorphic; the proof strengthens this to equality/coincidence of the two transported group structures.
  - Side conditions: no explicit `i ≠ j`; the source proof splits on equality of indices.
  - Follow-on claim: the source proof invokes the Eckmann--Hilton argument and notes commutativity as a byproduct, but the theorem only records independence of the auxiliary group.
- Lean coverage:
  - Formalizes the conclusion as equality of `Group` structures on `HomotopyGroup N X x`, following Mathlib's `HomotopyGroup.auxGroup_indep` and the final sentence of the source proof that the group structures coincide.
  - Equality of group structures implies the source's requested group isomorphism via the identity map; a separate `MulEquiv` statement is not added in this draft.
- Scope changes:
  - The explicit finite-index assumption is retained as `[Fintype N]`.
  - The source's "isomorphic" is represented by the stronger equality of group structures because the two groups have the same underlying type and the proof concludes equality after Eckmann--Hilton.
  - The low-level grid homotopy/interchange verification is delegated to Mathlib's homotopy-group development; the proof phase can close the theorem from `HomotopyGroup.auxGroup_indep` after unfolding `isUnital_auxGroup`.
- Dependencies:
  - `line-17` / `isUnital_auxGroup`
  - `HomotopyGroup.auxGroup_indep`
  - `HomotopyGroup.isUnital_auxGroup`
  - `EckmannHilton.mul`
  - Mathlib lemmas used in the canonical proof: `fromLoop_trans_toLoop`, `transAt_distrib`, `loopHomeo_apply`, `loopHomeo_symm_apply`.
- Skeleton candidate used: none copied. The skeleton theorem shape did not provide a precise target; the final theorem uses the precise Mathlib homotopy-group equality statement located by search.
- Formal statement review: draft should be reviewed for the equality-versus-isomorphism representation and the use of Mathlib's existing `HomotopyGroup` construction as the bridge for `Ω^N/≃_{∂ I^N}`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text:

```text
If i=j there is nothing to prove, so assume i≠j.
Consider the two unital multiplications *_i and *_j on the same set π_N(X,x), both
having the same unit [c] by the previous theorem.

The Eckmann--Hilton argument applies in the following form: if two unital binary operations
⋆ and ⋄ on a set have the same unit and satisfy the interchange law
  (a⋆b)⋄(c⋆d) = (a⋄c)⋆(b⋄d)  for all a,b,c,d,
then ⋆=⋄ (and in fact the common operation is commutative).

Thus it suffices to verify the interchange law for *_i and *_j on π_N(X,x).
Let [a],[b],[c],[d]∈π_N(X,x) be represented by generalized loops a,b,c,d∈Ω^N(X,x).
Form the two composites
  ([a]*_i [b])*_j([c]*_i [d])
and
  ([a]*_j [c])*_i([b]*_j [d]).
By construction of *_i and *_j, each side is represented by a generalized N-loop obtained
by concatenating maps I^N→X in the i-direction and j-direction respectively.
When i≠j, these two iterated concatenations correspond to the two ways of composing a map
defined on the square I×I (in the (i,j)-coordinates) by first concatenating horizontally
and then vertically, or vice versa. These two constructions are homotopic relative to the boundary
of the square (and hence relative to ∂I^N) by the standard grid homotopy that
reparameterizes the (i,j)-coordinates.

Therefore the two composites represent the same element of π_N(X,x), i.e. the interchange law
holds:
  ([a]*_i [b])*_j([c]*_i [d]) = ([a]*_j [c])*_i([b]*_j [d]).
By Eckmann--Hilton it follows that *_i=*_j, hence the group structures
auxGroup(i) and auxGroup(j) coincide.
```

- Prover notes:
  - Start with `classical` and unfold `isUnital_auxGroup`.
  - The intended one-line close should be `simpa [isUnital_auxGroup] using HomotopyGroup.auxGroup_indep (X := X) (x := x) i j` or a small variant if elaboration requires it.
  - If expanding the proof manually, use `Group.ext` with `EckmannHilton.mul (HomotopyGroup.isUnital_auxGroup i) (HomotopyGroup.isUnital_auxGroup j)`, then the interchange law supplied by Mathlib's `transAt_distrib`.

## Candidate Skeleton Review

- `Skeleton1.lean` and `Skeleton2.lean`: read and compared; they introduce ad hoc definitions of iterated loop spaces and quotients, while the final statement should use Mathlib's homotopy-group representation.
- `Skeleton3.lean` and `Skeleton4.lean`: read and compared; they add exact-name declarations, but the current draft follows the existing Mathlib construction and theorem shape.

## Search Notes

- Local/Mathlib search for `auxGroup`, `isUnital_auxGroup`, and `HomotopyGroup` found the exact Mathlib declarations:
  - `HomotopyGroup.auxGroup`
  - `HomotopyGroup.isUnital_auxGroup`
  - `HomotopyGroup.auxGroup_indep`
- Search for Eckmann--Hilton found `EckmannHilton.IsUnital`, `EckmannHilton.mul`, and `EckmannHilton.commGroup` in `Mathlib.GroupTheory.EckmannHilton`.

## Review Checklist

- [x] Source document `docs/source.tex` inspected.
- [x] Preflight manifest and planner context read.
- [x] Required instructions and all four skeleton files read.
- [x] Mathlib/local search performed before drafting.
- [x] Blueprint source inventory entries `line-17` and `line-28` filled.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [x] Proof-ready handoff accepted for the later prove workflow by formalization PASS and 2026-06-05 audit.
