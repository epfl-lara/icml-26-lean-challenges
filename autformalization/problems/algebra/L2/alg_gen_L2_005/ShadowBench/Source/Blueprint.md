# Formalization Blueprint: `algebra/L2/alg_gen_L2_005`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: generated formalization containing the named definition `S` and the source theorem `zeroLocus_nonempty_of_disjoint_noZeros`.
- `ShadowBench/Source.lean`: root source aggregator, directly imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: project root module, directly imports `ShadowBench.Source` so plain project builds cover the generated target module.

## Import Plan

```lean
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Ideal.Span
```

These are the direct imports for `ShadowBench/Source/Main.lean`, matching `docs/instructions.md`.

## Suggested Search Modules

- `Mathlib.RingTheory.Nullstellensatz`: `MvPolynomial.zeroLocus`, `MvPolynomial.mem_zeroLocus_iff`, `MvPolynomial.zeroLocus_top`.
- `Mathlib.Algebra.MvPolynomial.Eval`: evaluation facts used transitively by `Nullstellensatz`; not a direct import unless a later proof needs it explicitly.
- `Mathlib.RingTheory.Ideal.Span`: allowed starting import from the instructions; useful for ideal membership and generated ideals.

## Required Names

- `S`
- `zeroLocus_nonempty_of_disjoint_noZeros`

## Source Statement Inventory

- `line-17` (theorem, `docs/source.tex` lines 17–19): formalized by `zeroLocus_nonempty_of_disjoint_noZeros`; depends on the named definition `S`.

### Definition item: S

- Planned Lean declarations: `S`
- Source locator: `docs/source.tex`, line 17, phrase “let $S$ be the subset of all polynomials in $k[x_1,\dots,x_n]$ that have no zeros in $k^n$”.
- Skeleton candidate used: `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` give the same basic shape. The draft keeps their `Fin n` indexing of variables but uses `MvPolynomial.aeval` to align with Mathlib’s `MvPolynomial.zeroLocus`; `Skeleton4.lean` is malformed and is not adopted.
- Dependencies: `MvPolynomial`, `MvPolynomial.aeval`, `Fin n`, `Set`.
- Formal statement review: `S k n` is the set of polynomials `p : MvPolynomial (Fin n) k` such that for every `x : Fin n → k`, evaluating `p` at `x` is nonzero.
- Source qualifiers: arbitrary field `k`; natural number of variables `n`; polynomial ring `k[x_1,\dots,x_n]`; points of affine space `k^n`; no zeros at any such point.
- Lean coverage: exact up to the standard Mathlib representation of `n` variables by the type `Fin n` and points of `k^n` by functions `Fin n → k`.
- Scope changes: no intentional weakening or strengthening; only representation bridge is `k[x_1,\dots,x_n]` as `MvPolynomial (Fin n) k`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: no proof is supplied in the source document.
- Source proof / prover notes: definition only; unfold `S` to obtain `∀ x : Fin n → k, MvPolynomial.aeval x p ≠ 0`.

### line-17

- Kind: theorem
- Planned Lean declarations: `zeroLocus_nonempty_of_disjoint_noZeros`
- Source inventory entry: `line-17`
- Source locator: `line-17`; `docs/source.tex`, theorem environment lines 17–19.
- Source statement: “Let $k$ be an arbitrary field and let $S$ be the subset of all polynomials in $k[x_1,\dots,x_n]$ that have no zeros in $k^n$. If $I$ is any ideal in $k[x_1,\dots,x_n]$ such that $I \cap S=\varnothing$, then $\mathbf V(I)\neq\varnothing$.”
- Skeleton candidate used: `Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` match the intended variables and raw zero-locus set. The draft keeps the required theorem name and source quantifiers, changes the hypothesis to the literal set equality `(I : Set _) ∩ S k n = ∅`, and uses Mathlib’s `MvPolynomial.zeroLocus k I` for `\mathbf V(I)`. `Skeleton4.lean` is malformed and is not used.
- Dependencies: `S`, `Ideal`, `Set.inter`, `Set.empty`, `MvPolynomial.zeroLocus`, `MvPolynomial.mem_zeroLocus_iff`.
- Formal statement review: for any field `k`, any `n : ℕ`, and any ideal `I : Ideal (MvPolynomial (Fin n) k)`, if no member of `I` lies in the no-zeros set `S k n`, then the Mathlib zero locus of `I` over the same field `k` is nonempty.
- Source qualifiers: arbitrary field `k`; all variables indexed by `1,\dots,n`; arbitrary ideal `I`; exact side condition `I ∩ S = ∅`; conclusion `\mathbf V(I) \neq \varnothing` as a set of `k`-rational points.
- Lean coverage: exact up to the standard representation bridge: variables are `Fin n`; points of `k^n` are functions `Fin n → k`; `\mathbf V(I)` is `MvPolynomial.zeroLocus k I`, whose membership is definitionally `∀ p ∈ I, MvPolynomial.aeval x p = 0`.
- Scope changes: no intentional weakening or strengthening.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: no proof block appears in `docs/source.tex`.
- Source proof / prover notes: the natural proof target is the contrapositive: assuming `MvPolynomial.zeroLocus k I = ∅`, produce a polynomial in `I` that has no zeros on `k^n`, contradicting `(I : Set _) ∩ S k n = ∅`. Unfold `MvPolynomial.mem_zeroLocus_iff` to translate a point of the zero locus into simultaneous vanishing of every polynomial in `I`. The source gives no additional proof, so a later proof run should first verify whether the arbitrary-field statement is derivable or whether an independent review must request an additional hypothesis.

## Statement-Fidelity Comparison

- `S`: source “all polynomials … that have no zeros in `k^n`” is represented as all `p : MvPolynomial (Fin n) k` with `∀ x : Fin n → k, MvPolynomial.aeval x p ≠ 0`.
- `line-17`: source “any ideal” is an arbitrary `I : Ideal (MvPolynomial (Fin n) k)`; source `I ∩ S = ∅` is the literal set-intersection equality using the coercion of `I` to a set; source `\mathbf V(I) \neq \varnothing` is `MvPolynomial.zeroLocus k I ≠ ∅`.

## Handoff Checklist

- [x] Source document and preflight manifest read.
- [x] Required instruction and skeleton files read and compared with the source.
- [x] Local/Mathlib search performed before choosing declaration shapes.
- [x] Blueprint source inventory contains the source theorem entry `line-17`.
- [x] Direct import plan is limited to direct Lean imports for the generated target file.
- [x] Root project modules import the generated target module path.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [x] Project-level Lean verification recorded after the generated draft is in place: `lean_verify(mode=project)` / `lake build` succeeded, with the expected planner-stage warning that `zeroLocus_nonempty_of_disjoint_noZeros` uses `sorry`.
