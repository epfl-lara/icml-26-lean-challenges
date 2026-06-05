# Formalization Blueprint: `combinatorics/L3/com_gen_L3_003`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the three source-backed theorem declarations with `by sorry` proof placeholders and source-aware prover notes.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so a project build covers the generated target module.

## Import Plan

```lean
import Mathlib.Combinatorics.Matroid.Minor.Delete
import Mathlib.Tactic.TautoSet
import Mathlib.Combinatorics.Matroid.Minor.Contract
```

## Import Rationale

The first two imports are the starting imports from `docs/instructions.md`.  The direct import of `Mathlib.Combinatorics.Matroid.Minor.Contract` is needed for matroid contraction, the unicode contraction/deletion API, `Matroid.Spanning`, and the existing Mathlib lemmas named below.

## Suggested Search Modules

- `Mathlib.Combinatorics.Matroid.Minor.Contract`
- `Mathlib.Combinatorics.Matroid.Minor.Delete`
- `Mathlib.Combinatorics.Matroid.Closure`

Search results used during planning:

- `Matroid.contract_closure_eq_contract_delete`
- `Matroid.contract_closure_eq`
- `Matroid.contract_spanning_iff`
- `Matroid.contract_loops_eq`
- `Matroid.spanning_iff_closure_eq`

## Required Names

- `contract_closure_eq_contract_delete`
- `contract_closure_eq`
- `contract_spanning_iff`

## Source Statement Inventory

### line-17

- Source inventory entry: `line-17`
- Source locator: `docs/source.tex`, lemma lines 17-22; proof lines 23-28.
- Environment: lemma.
- Source statement: For any `C ⊆ E(M)`,
  `M / cl_M(C) = (M / C) \ (cl_M(C) \ C)`.
- Planned Lean declarations: theorem `contract_closure_eq_contract_delete`.
- Lean statement:
  ```lean
  theorem contract_closure_eq_contract_delete (M : Matroid α) (C : Set α)
      (hC : C ⊆ M.E) :
    Matroid.contract M (M.closure C) =
      Matroid.delete (Matroid.contract M C) (M.closure C \ C) := by
    sorry
  ```
- Skeleton candidate used: all four skeletons propose this name and overall equation.  The draft adopts the source/skeleton quantifier over `C` with hypothesis `hC : C ⊆ M.E`, but corrects the skeleton API from `M.groundSet`, ASCII slash/backslash, and method-style deletion to Mathlib's current `M.E`, `Matroid.contract`, and `Matroid.delete` API.
- Dependencies: source-independent wrapper around Mathlib theorem `Matroid.contract_closure_eq_contract_delete`; related proof ingredients in the source are matroid bases, closure of a basis, and associativity/commutativity of contraction/deletion.
- Source qualifiers:
  - Mathematical object class: arbitrary `Matroid α`.
  - Quantifier order: matroid `M`, set `C`, then supportedness assumption `C ⊆ E(M)`.
  - Parameter domain: `C : Set α`.
  - Output codomain: equality in `Matroid α`.
  - Equality condition: equality of matroids after contracting `cl_M(C)` versus contracting `C` then deleting `cl_M(C) \ C`.
  - Side conditions: `C ⊆ E(M)` is explicit in the Lean statement.
  - Follow-on claims: none.
- Lean coverage: exact mathematical content, with `E(M)` encoded by `M.E`, closure by `M.closure`, contraction by `Matroid.contract`, and deletion by `Matroid.delete`.  The imported Mathlib theorem is stronger because it does not require `hC`; this wrapper keeps the source side condition.
- Scope changes: none beyond API notation normalization.
- Formal statement review: drafted and compared against the source statement; independent review still required.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: Reduce to the case `C ⊆ E(M)`. Choose a basis `I` of `C`. Then `cl_M(C)=cl_M(I)`, and contracting `cl_M(I)` can be expressed as contracting `I` and deleting the remaining elements `cl_M(I) \ I`. Rearranging with associativity/commutativity of contraction/deletion gives the displayed equality.
- Prover notes: after statement review, this should follow directly from `Matroid.contract_closure_eq_contract_delete M C`; the source proof explains the basis/contraction-delete decomposition if a direct wrapper proof is not accepted.

### line-30

- Source inventory entry: `line-30`
- Source locator: `docs/source.tex`, lemma lines 30-35; proof lines 36-41.
- Environment: lemma.
- Source statement: For any sets `C, X`,
  `cl_{M/C}(X) = cl_M(X ∪ C) \ C`.
- Planned Lean declarations: theorem `contract_closure_eq`.
- Lean statement:
  ```lean
  theorem contract_closure_eq (M : Matroid α) (C X : Set α) :
    (Matroid.contract M C).closure X = M.closure (X ∪ C) \ C := by
    sorry
  ```
- Skeleton candidate used: all four skeletons propose this name and equation.  The draft adopts the quantification over arbitrary `C X : Set α`, and corrects notation/API to `Matroid.contract` and `M.closure`.
- Dependencies: source proof mentions `Matroid.contract_loops_eq`; direct Mathlib dependency is `Matroid.contract_closure_eq`.
- Source qualifiers:
  - Mathematical object class: arbitrary `Matroid α`.
  - Quantifier order: matroid `M`, set `C`, set `X`.
  - Parameter domain: `C X : Set α`; no supportedness assumption is stated in the source.
  - Output codomain/equality: equality of subsets of `α`.
  - Side conditions: none.
  - Follow-on claims: none.
- Lean coverage: exact mathematical content, with contraction represented by `Matroid.contract M C`; Mathlib closure returns a set in the ground set automatically.
- Scope changes: none beyond API notation normalization.
- Formal statement review: drafted and compared against the source statement; independent review still required.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: Using the loop description `loops(M/C)=cl_M(C) \ C` and the fact that closure can be characterized via loops after contracting, one shows both inclusions: elements in `cl_{M/C}(X)` correspond exactly to elements in `cl_M(X ∪ C)` that are not in `C`. A straightforward manipulation of closure axioms completes the proof.
- Prover notes: after statement review, use `Matroid.contract_closure_eq M C X`; the source proof gives the loop-based route through `Matroid.contract_loops_eq` if direct rewriting needs support.

### line-43

- Source inventory entry: `line-43`
- Source locator: `docs/source.tex`, lemma lines 43-50; proof lines 51-56.
- Environment: lemma.
- Source statement: Assuming `C ⊆ E(M)`,
  `X` is spanning in `M/C` iff `(X ∪ C)` is spanning in `M` and `Disjoint(X,C)`.
- Planned Lean declarations: theorem `contract_spanning_iff`.
- Lean statement:
  ```lean
  theorem contract_spanning_iff (M : Matroid α) (C : Set α) (hC : C ⊆ M.E)
      (X : Set α) :
    (Matroid.contract M C).Spanning X ↔
      M.Spanning (X ∪ C) ∧ Disjoint X C := by
    sorry
  ```
- Skeleton candidate used: all four skeletons propose this name and biconditional.  The draft adopts the source side condition `hC`, but corrects the skeleton's non-current `IsSpanning` spelling to Mathlib's `Matroid.Spanning` predicate and replaces `M.groundSet` with `M.E`.
- Dependencies: source uses the closure formula from source entry `line-30`, the ground-set formula `(M/C).E = M.E \ C`, and the closure characterization of spanning; direct Mathlib dependency is `Matroid.contract_spanning_iff`.
- Source qualifiers:
  - Mathematical object class: arbitrary `Matroid α`.
  - Quantifier order: matroid `M`, set `C`, supportedness assumption `C ⊆ E(M)`, set `X`.
  - Parameter domain: `C X : Set α`.
  - Output codomain/logical target: a proposition.
  - Logical form: biconditional between spanning in the contracted matroid and a conjunction of spanning in `M` plus disjointness from `C`.
  - Side conditions: `C ⊆ E(M)` is explicit; `Matroid.Spanning` includes the appropriate subset-of-ground condition for the spanning set.
  - Follow-on claims: none.
- Lean coverage: exact mathematical content, with source phrase "is spanning in" encoded by Mathlib's structure predicate `Matroid.Spanning`.  `Disjoint X C` is Lean's set-disjointness predicate.
- Scope changes: none beyond API notation normalization.
- Formal statement review: drafted and compared against the source statement; independent review still required.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: By definition, `X` is spanning in `N` iff `cl_N(X)=E(N)`. Apply the closure formula `cl_{M/C}(X)=cl_M(X∪C)\C` and the ground-set formula `E(M/C)=E(M)\C`, and rewrite equality of set-differences as spanning of `X∪C` together with `X∩C=∅`.
- Prover notes: after statement review, first try `Matroid.contract_spanning_iff (M := M) (C := C) (X := X) hC`.  If proving from source, rewrite `Spanning` with `Matroid.spanning_iff_closure_eq`, then use `contract_closure_eq`, `Matroid.contract_ground`, and set extensionality/disjointness rewrites.

## Handoff Notes

- Definition/structure/instance construction gaps: none; all generated obligations are theorem proofs.
- Proof placeholders intentionally remain as `by sorry` for the later `/prove` workflow.
- Statement/source verifier should check the three inventory entries above against `docs/source.tex` before any proof queue is launched.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
