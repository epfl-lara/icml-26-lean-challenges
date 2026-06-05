# Formalization Blueprint: `analysis/L2/ana_mero_L2_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean` contains all generated declarations for this source document.
- `ShadowBench/Source.lean` imports `ShadowBench.Source.Main`.
- `ShadowBench.lean` imports `ShadowBench.Source`, so the default `ShadowBench` target covers the generated file.

## Import Plan

```lean
import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Topology.LocallyFinsupp
```

## Suggested Search Modules

- `Mathlib.Analysis.Meromorphic.Divisor`: contains `MeromorphicOn.divisor`, `MeromorphicOn.divisor_def`, `MeromorphicOn.divisor_apply`, and the bundled locally-finite-support construction that should guide the proof of local finiteness.
- `Mathlib.Topology.LocallyFinsupp`: contains `Function.locallyFinsuppWithin.supportLocallyFiniteWithinDomain` and the neighborhood-filter formulation of locally finite support.
- `Mathlib.Analysis.Meromorphic.Order`: contains `meromorphicOrderAt` and `meromorphicOrderAt_eq_int_iff` for the local normal-form proof strategy.

## Required Names

- `divisor`
- `divisor_support`
- `divisor_support_locally_finite`

## Skeleton Review

All four candidate skeletons used the required names and the same broad parameter list, but left the `divisor` definition as `sorry` and encoded meromorphicity as `∀ z ∈ U, IsMeromorphicAt f z`. The final draft keeps the skeleton names and parameter order, implements `divisor` directly from the source formula using Mathlib's `MeromorphicOn` / `meromorphicOrderAt`, and states the theorem with Mathlib's bundled `MeromorphicOn f U` predicate.

## Source Statement Inventory

1. `line-17` (definition, lines 17-31) - divisor; Lean: `divisor`
2. `line-34` (definition, lines 34-48) - divisor_support; Lean: `divisor_support`, companion `mem_divisor_support_iff`
3. `line-51` (theorem, lines 51-53; proof lines 53-82) - divisor_support_locally_finite; Lean: `divisor_support_locally_finite`

### line-17

- Source item: Definition `divisor`

- Planned Lean declarations: `divisor`
- Source locator: `docs/source.tex`, lines 17-31 (`line-17`)
- Kind: definition
- Skeleton candidate used: naming and parameter order follow `Skeleton1.lean`-`Skeleton4.lean`; the body is replaced by the source formula rather than the skeleton `sorry`.
- Dependencies: `NontriviallyNormedField`, `NormedAddCommGroup`, `NormedSpace`, `MeromorphicOn`, `meromorphicOrderAt`, `WithTop.untop₀`.
- Source statement: Let `K` be a nontrivially normed field, `E` a normed vector space over `K`, `U ⊆ K`, and `f : K → E`. The divisor of `f` on `U` is the function `K → ℤ` with value `ord_z(f)` if `f` is meromorphic on `U` and `z ∈ U`, and `0` otherwise.
- Source qualifiers: mathematical object class is a nontrivially normed field `K` and a normed vector space `E` over `K`; quantifier/parameter order is `K`, then `E`, then a parameter-domain set `U : Set K`, then a function `f : K → E`; output codomain is the integer-valued function space `K → ℤ`; the equality/value condition is the displayed case split `div_U(f)(z) = ord_z(f)` exactly when the side condition “`f` is meromorphic on `U` and `z ∈ U`” holds; the otherwise branch is `0`.
- Formal statement review: the Lean declaration keeps the source parameter classes, parameter order, integer-valued output, meromorphic-on-`U` guard, membership guard, and zero otherwise branch. The only non-literal representation choice is converting Mathlib's `WithTop ℤ` order to the source's integer-valued divisor by `WithTop.untop₀`.
- Lean coverage: `noncomputable def divisor ... : K → ℤ := fun z ↦ if MeromorphicOn f U ∧ z ∈ U then (meromorphicOrderAt f z).untop₀ else 0` directly implements the displayed case distinction. Mathlib's order has type `WithTop ℤ`, so `.untop₀` is the representation bridge from the source's informal integer-valued `ord_z(f)` to the declared codomain `ℤ`.
- Scope changes: none. The representation bridge is fully covered in the Lean definition: Mathlib's order value `meromorphicOrderAt f z : WithTop ℤ` is converted to the source's integer codomain by `WithTop.untop₀`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: definition, no proof. Later proofs should unfold `divisor`; when `hf : MeromorphicOn f U` and `hz : z ∈ U`, it reduces to `(meromorphicOrderAt f z).untop₀`.

### line-34

- Source item: Definition `divisor_support`

- Planned Lean declarations: `divisor_support`; companion lemma `mem_divisor_support_iff` records the displayed equivalence involving `ord_z(f) ≠ 0` and `ord_z(f) ≠ ∞`.
- Source locator: `docs/source.tex`, lines 34-48 (`line-34`)
- Kind: definition with an explicit equivalence claim
- Skeleton candidate used: naming and first displayed set-builder shape follow `Skeleton1.lean`-`Skeleton4.lean`.
- Dependencies: `divisor`, `MeromorphicOn`, `meromorphicOrderAt`, `WithTop.untop₀`.
- Source statement: The support of the divisor is `{ z ∈ U | div_U(f)(z) ≠ 0 }`. Equivalently, it is `{ z ∈ U | ord_z(f) ≠ 0 and ord_z(f) ≠ ∞ }`.
- Source qualifiers: inherited mathematical object class and parameter order are those of `divisor` (`K`, `E`, `U`, `f`); parameter domain is the set `U : Set K`; output codomain is a subset of `K`; the primary equality/set-builder condition is `supp(div_U(f)) = {z ∈ U | div_U(f)(z) ≠ 0}`; the follow-on equivalence claims the same support is `{z ∈ U | ord_z(f) ≠ 0 ∧ ord_z(f) ≠ ∞}`; the side conditions in the equivalence are membership in `U`, nonzero order, and finite (non-infinite) order.
- Formal statement review: the primary definition exactly records the first displayed set-builder. The companion theorem records the source's displayed equivalence in the meromorphic-on-`U` context, which is the branch where the previous guarded divisor definition uses the order value.
- Lean coverage: `divisor_support ... : Set K := {z | z ∈ U ∧ divisor K E U f z ≠ 0}` exactly encodes the first displayed support set. `mem_divisor_support_iff` states the follow-on equivalence under `hf : MeromorphicOn f U`, translating `ord_z(f) ≠ 0` to `meromorphicOrderAt f z ≠ 0` and `ord_z(f) ≠ ∞` to `meromorphicOrderAt f z ≠ (⊤ : WithTop ℤ)`.
- Scope changes: the equivalence companion includes the explicit hypothesis `hf : MeromorphicOn f U`; without this contextual hypothesis the displayed equivalence would not follow from the source's guarded divisor definition when `f` is not meromorphic on all of `U`. This is an intentional clarification of the source context, not a change to the primary support definition. Infinity is represented by Mathlib's top element `(⊤ : WithTop ℤ)`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: the source gives the equivalence as part of the definition, without a separate proof. Provers should unfold `divisor_support` and `divisor`, use `hf` and membership in `U`, then use `WithTop.untop₀_eq_zero` to convert nonzero integer divisor value into order neither `0` nor `⊤`.

### line-51

- Source item: Theorem `divisor_support_locally_finite`

- Planned Lean declarations: `divisor_support_locally_finite`
- Source locator: `docs/source.tex`, theorem lines 51-53 and proof lines 53-82 (`line-51`)
- Kind: theorem
- Skeleton candidate used: required theorem name and broad parameters follow `Skeleton1.lean`-`Skeleton4.lean`; the statement is changed from the skeleton's pointwise `IsMeromorphicAt` predicate to Mathlib's `MeromorphicOn f U`, matching the source phrase "meromorphic on `U`".
- Dependencies: `divisor_support`, `divisor`, `MeromorphicOn`, `meromorphicOrderAt`; proof likely uses the suggested module `Mathlib.Analysis.Meromorphic.Divisor`.
- Source statement: If `f` is meromorphic on `U`, then the support of `div_U(f)` is locally finite in `U`.
- Source qualifiers: inherited object class and parameter order are `K`, `E`, `U`, `f`, followed by the side-condition hypothesis that `f` is meromorphic on `U`; parameter domain for local finiteness is within `U`; the conclusion is that the previously defined support of `div_U(f)` is locally finite in `U`; the local-finiteness condition means each point of `U` has a neighborhood whose intersection with that support is finite. The source proof's stronger phrasing “let `z₀ ∈ K`” is proof commentary; the theorem statement says “in `U`”.
- Formal statement review: the Lean theorem preserves the source's single hypothesis `MeromorphicOn f U`, the same divisor-support object, and the local-finiteness-in-`U` conclusion. The conclusion is encoded as the neighborhood-filter statement `∀ x ∈ U, ∃ V ∈ 𝓝 x, (V ∩ divisor_support K E U f).Finite`, matching the source statement's relative-to-`U` locality and the proof's finite intersection with a neighborhood.
- Lean coverage: the theorem states `hf : MeromorphicOn f U` and concludes `∀ x ∈ U, ∃ V ∈ 𝓝 x, (V ∩ divisor_support K E U f).Finite`. This is the neighborhood-filter formulation of local finiteness in `U` used by `Function.locallyFinsuppWithin`.
- Scope changes: none. The Lean statement uses the standard Mathlib neighborhood-filter encoding `V ∈ 𝓝 x` for the source phrase “there exists a neighborhood `V`”; this is equivalent to an open-neighborhood formulation in topological spaces and does not weaken the theorem hypothesis or conclusion.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: Assume that `f` is meromorphic on `U`. Let `z₀ ∈ K`. By the definition of meromorphicity, there exists a neighborhood `V` of `z₀` such that either `f` has no zeros or poles in `V`, or `z₀` is an isolated zero or pole of `f`. Indeed, near any point `z₀ ∈ U`, there exists an integer `n` and an analytic function `g` with `g(z₀) ≠ 0` such that `f(z) = (z - z₀)^n g(z)` for all `z` in a punctured neighborhood of `z₀`. Since zeros of analytic functions are isolated unless the function vanishes identically, it follows that the set of zeros of `f` in `V` is finite and the set of poles of `f` in `V` is finite. Therefore `V ∩ supp(div_U(f))` is finite. Since `z₀` was arbitrary, the support of `div_U(f)` is locally finite in `U`.
- Prover notes: Prefer the existing Mathlib divisor API. Import `Mathlib.Analysis.Meromorphic.Divisor` if the proof run needs it. Compare `divisor_support` with the support of `MeromorphicOn.divisor f U`, then apply its `supportLocallyFiniteWithinDomain` field. A direct source-style proof can instead use `hf.codiscrete_setOf_meromorphicOrderAt_eq_zero_or_top` and `supportDiscreteWithin_iff_locallyFiniteWithin` after unfolding `divisor` and `divisor_support`.

## Formal Statement Review Summary

- `divisor`: exact source parameters and codomain, with an explicit bridge from `WithTop ℤ` to `ℤ`.
- `divisor_support`: exact first support set; explicit companion statement for the source's equivalence clause.
- `divisor_support_locally_finite`: exact meromorphic-on-set assumption and local-finiteness-in-`U` conclusion, using Mathlib's neighborhood-filter notation for "neighborhood".
- Independent statement/source review accepted by formalization PASS and 2026-06-05 audit; entries are approved for later `/prove` work.

## Proof Handoff Notes

- Current proof obligations expected after review: `mem_divisor_support_iff` and `divisor_support_locally_finite`.
- Construction declarations `divisor` and `divisor_support` are implemented without `sorry`.
- Suggested proof command after independent statement/source approval: `/prove ShadowBench/Source/Main.lean`.
