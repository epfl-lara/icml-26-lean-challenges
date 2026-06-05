# Formalization Blueprint: `Topology/L2/top_gen_L2_001`

- Source document: `docs/source.tex`
- Companion instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Source Document Inspection

- `formalization_document_inspect docs/source.tex` succeeded; extraction status `ok`.
- No LaTeX theorem environments, labels, references, citations, bibliography files, PDFs, figures, or support assets were detected by preflight.
- Source line locators below use `docs/source.tex` line numbers from the project-local file.

## Generated File Layout

Final organization decision: keep the generated formalization single-file.  The source contains one definition and three directly related theorem statements, so it is below the split thresholds (more than 12 declarations, more than 8 proof obligations, or naturally separate definition/construction/results modules).  Splitting would add imports without clarifying the dependency order.

- `ShadowBench/Source/Main.lean`: generated formalization declarations for the source definition and three source theorems.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so plain project builds cover the generated target module.

## Import Plan

```lean
import Mathlib.Order.KrullDimension
import Mathlib.Topology.Irreducible
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Sets.Closeds
```

## Suggested Search Modules

These are proof/search hints only, not direct imports for `ShadowBench/Source/Main.lean`.

- `Mathlib.Topology.KrullDimension`: contains analogous Mathlib declarations and proofs for the same topological Krull dimension API.
- `Mathlib.Topology.Sets.Closeds`: source of `TopologicalSpace.IrreducibleCloseds`, `IrreducibleCloseds.map`, and `map_strictMono_of_isInducing`.
- `Mathlib.Order.KrullDimension`: source of `Order.krullDim`, `Order.krullDim_le_of_strictMono`, and chain-length characterizations.

## Required Names

- `topologicalKrullDim`
- `IsInducing.topologicalKrullDim_le`
- `IsHomeomorph.topologicalKrullDim_eq`
- `topologicalKrullDim_subspace_le`

## Candidate Skeleton Review

- `Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` propose `topologicalKrullDim : ℕ∞` with an unimplemented definition and a bundled-homeomorphism theorem shape. This loses Mathlib's bottom value for empty preorders and is less aligned with the available order-theoretic Krull dimension API.
- `Skeleton4.lean` supplies the adopted definition shape `Order.krullDim (IrreducibleCloseds T)` with codomain `WithBot ℕ∞` and theorem names matching the source/instructions. The final draft follows this candidate, with the homeomorphism theorem adjusted to make the function `f : X → Y` explicit as in the source sentence and Mathlib API.

## Statement Inventory and Source Map

### 1. Definition: topological Krull dimension

- Planned Lean declaration: `topologicalKrullDim`
- Source locator: `docs/source.tex` lines 17--22.
- Source statement text:
  ```text
  Let T be a topological space.
  A chain of irreducible closed subsets of T is a sequence Z_0 ⊂ Z_1 ⊂ ⋯ Z_n ⊂ T with Z_i closed irreducible and Z_i ≠ Z_{i+1} for i=0,⋯,n-1.
  The length of a chain Z_0 ⊂ Z_1 ⊂ ⋯ Z_n ⊂ T of irreducible closed subsets is the integer n.
  The Krull dimension dim(T) of T is the supremum of lengths of chains of irreducible closed subsets.
  ```
- Planned Lean statement:
  ```lean
  noncomputable def topologicalKrullDim (T : Type*) [TopologicalSpace T] : WithBot ℕ∞ :=
    Order.krullDim (IrreducibleCloseds T)
  ```
- Dependencies: `Order.krullDim`; `TopologicalSpace.IrreducibleCloseds`; the order on irreducible closed subsets by inclusion.
- Formal statement review: the Lean definition formalizes chains of closed irreducible subsets by applying Mathlib's order-theoretic Krull dimension to the poset `IrreducibleCloseds T`; strict chains in this poset correspond to strict inclusion chains of irreducible closed subsets.
- Source qualifiers:
  - Mathematical object class: topological space `T`.
  - Chain objects: finite strict chains of closed irreducible subsets.
  - Length: natural number `n` for a chain with `n+1` terms.
  - Output: supremum of possible lengths.
- Lean coverage:
  - `T : Type*` with `[TopologicalSpace T]` covers the topological space.
  - `IrreducibleCloseds T` covers closed irreducible subsets of `T`.
  - `Order.krullDim` covers the supremum of strict finite chain lengths.
  - Codomain `WithBot ℕ∞` covers finite dimensions, infinite dimension, and Mathlib's bottom value for empty orders.
- Scope changes: no theorem weakening. The source's informal supremum is represented using Mathlib's standard `WithBot ℕ∞` Krull dimension value; this is an explicit representation choice, not a mathematical restriction.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: definition is implemented directly; no theorem proof obligation is attached to this item.

### 2. Theorem: inducing maps do not increase topological Krull dimension

- Planned Lean declaration: `IsInducing.topologicalKrullDim_le`
- Source locator: `docs/source.tex` lines 25--33.
- Source statement text:
  ```text
  Let X, Y be topological spaces.
  If f: Y → X is inducing, then dim(Y) ≤ dim(X).
  ```
- Complete source proof text:
  ```text
  If Z_0 ⊂ Z_1 ⊂ ⋯ Z_n ⊂ X is a chain of irreducible closed subsets of X, then f^{-1}(Z_0) ⊂ f^{-1}(Z_1) ⊂ ⋯ f^{-1}(Z_n) ⊂ Y is a chain of irreducible closed subsets of Y.
  ```
- Planned Lean statement:
  ```lean
  theorem IsInducing.topologicalKrullDim_le {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
      {f : Y → X} (hf : IsInducing f) :
      topologicalKrullDim Y ≤ topologicalKrullDim X
  ```
- Dependencies: `topologicalKrullDim`; `IrreducibleCloseds.map`; `map_strictMono_of_isInducing`; `Order.krullDim_le_of_strictMono`.
- Formal statement review: the Lean theorem preserves the quantifier order and direction from the source theorem: topological spaces `X`, `Y`, a map `f : Y → X`, an inducing hypothesis, and the inequality `dim(Y) ≤ dim(X)`.
- Source qualifiers:
  - Mathematical object class: topological spaces `X` and `Y`.
  - Parameter domain/codomain: `f : Y → X`.
  - Side condition: `f` is inducing.
  - Output/equality condition: `topologicalKrullDim Y ≤ topologicalKrullDim X`.
- Lean coverage:
  - `[TopologicalSpace X] [TopologicalSpace Y]` covers the object class.
  - `{f : Y → X}` and `(hf : IsInducing f)` cover the map and inducing assumption.
  - The conclusion is the source inequality, using the definition `topologicalKrullDim` above.
- Scope changes: none in the theorem statement. Proof note: the source proof paragraph appears to describe pulling back chains from `X` to `Y`, which is the opposite direction from the stated inequality; the planned Lean proof should follow the statement by using the strict monotone map on irreducible closed sets supplied by an inducing map.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: use `Order.krullDim_le_of_strictMono _ (map_strictMono_of_isInducing hf)`. The source preimage-chain sentence is recorded verbatim above; if a reviewer treats it as a proof-direction error, keep the theorem statement because it is also used by the following homeomorphism and subspace results.

### 3. Theorem: invariance under homeomorphisms

- Planned Lean declaration: `IsHomeomorph.topologicalKrullDim_eq`
- Source locator: `docs/source.tex` lines 36--42.
- Source statement text:
  ```text
  The topological Krull dimension is invariant under homeomorphisms.
  ```
- Complete source proof text:
  ```text
  Let f:X → Y be a homeomorphism with its inverse f^{-1}:Y → X. Then both f and f^{-1} are inducing, so we have dim(X) ≤ dim(Y) and dim(Y) ≤ dim(X). It follows that dim(X) = dim(Y).
  ```
- Planned Lean statement:
  ```lean
  theorem IsHomeomorph.topologicalKrullDim_eq {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
      (f : X → Y) (h : IsHomeomorph f) :
      topologicalKrullDim X = topologicalKrullDim Y
  ```
- Dependencies: `topologicalKrullDim`; `IsInducing.topologicalKrullDim_le`; homeomorphism-to-inducing facts such as `IsHomeomorph.isInducing` or the closed-embedding/inducing API; `le_antisymm`.
- Formal statement review: the source states invariance under a homeomorphism. The Lean statement represents the homeomorphism as a function `f : X → Y` together with the predicate `IsHomeomorph f`, which includes existence of the inverse/homeomorphism data needed in the source proof.
- Source qualifiers:
  - Mathematical object class: topological spaces `X` and `Y`.
  - Parameter domain/codomain: `f : X → Y`.
  - Side condition: `f` is a homeomorphism with inverse.
  - Output/equality condition: `topologicalKrullDim X = topologicalKrullDim Y`.
- Lean coverage:
  - `[TopologicalSpace X] [TopologicalSpace Y]`, `(f : X → Y)`, and `(h : IsHomeomorph f)` cover the spaces, map, and homeomorphism assumption.
  - The conclusion is equality of the two dimensions using `topologicalKrullDim`.
  - The inverse map mentioned in the source is provided by the `IsHomeomorph` API during proof, rather than named as a separate explicit parameter.
- Scope changes: no mathematical weakening. Representation change: the source's named inverse is implicit in `IsHomeomorph f` instead of an extra theorem parameter.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: prove both inequalities with `IsInducing.topologicalKrullDim_le`, once for `f` and once for the inverse homeomorphism, then close with `le_antisymm`.

### 4. Theorem: subspace monotonicity

- Planned Lean declaration: `topologicalKrullDim_subspace_le`
- Source locator: `docs/source.tex` lines 45--51.
- Source statement text:
  ```text
  For any subspace Y ⊆ X, we have dim(Y) ≤ dim(X).
  ```
- Complete source proof text:
  ```text
  Since any embedding Y → X is inducing, we have dim(Y) ≤ dim(X).
  ```
- Planned Lean statement:
  ```lean
  theorem topologicalKrullDim_subspace_le (X : Type*) [TopologicalSpace X] (Y : Set X) :
      topologicalKrullDim Y ≤ topologicalKrullDim X
  ```
- Dependencies: `topologicalKrullDim`; `IsInducing.topologicalKrullDim_le`; `IsInducing.subtypeVal`.
- Formal statement review: a subspace is represented by a subset `Y : Set X` equipped with Lean's subtype topology. The conclusion compares the dimension of the subtype `Y` with the ambient space `X`.
- Source qualifiers:
  - Mathematical object class: topological space `X` and subspace `Y ⊆ X`.
  - Parameter domain: arbitrary subset/subspace of `X`.
  - Side condition: subspace inclusion/embedding into `X`.
  - Output/equality condition: `topologicalKrullDim Y ≤ topologicalKrullDim X`.
- Lean coverage:
  - `(X : Type*) [TopologicalSpace X] (Y : Set X)` covers any subspace of `X` by subtype topology.
  - `topologicalKrullDim Y` uses the subtype topological space on the set `Y`.
  - `IsInducing.subtypeVal` covers the inducing inclusion from the subspace to `X`.
- Scope changes: no mathematical weakening. Representation change: the source subspace `Y ⊆ X` is encoded as a Lean `Set X` subtype.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: instantiate `IsInducing.topologicalKrullDim_le` with the subtype inclusion and `IsInducing.subtypeVal`.

## Verification Checklist

- [x] Source document, preflight context, manifest, instructions, and skeleton files read.
- [x] Local/Mathlib search performed before final statement drafting.
- [x] Blueprint contains source locators, complete source proof text, dependencies, source qualifiers, Lean coverage, scope changes, and prover notes for each source theorem.
- [x] Direct import plan matches `ShadowBench/Source/Main.lean`.
- [x] Root module path imports the generated target module.
- [x] Project-level verification command `lean_verify(mode=project)` / `lake build` passed after the generated target module was in place. The only diagnostics are the three intentional theorem `sorry` warnings for the future proof queue.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [x] Proof-ready handoff accepted for the later prove workflow by formalization PASS and 2026-06-05 audit.

## Verification Log

- `lean_inspect ShadowBench/Source/Main.lean`: no hard errors or failed dependencies; three expected theorem `sorry` warnings.
- `lean_verify(mode=project)`: build completed successfully; `ShadowBench.Source.Main`, `ShadowBench.Source`, and `ShadowBench` were built.
- `lean_sorries(scope=file)`: three proof obligations remain by design: `IsInducing.topologicalKrullDim_le`, `IsHomeomorph.topologicalKrullDim_eq`, and `topologicalKrullDim_subspace_le`.

## Suggested Next Command After Review

After an independent statement/source review approves or corrects the draft, run:

```text
/prove ShadowBench/Source/Main.lean
```
