# Formalization Blueprint: `algebra/L2/alg_gen_L2_013`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Detected Theorem-Like Blocks

1. `line-17` (theorem, lines 17-19) - zariskiClosure_is_smallest_algebraic_set
   Source statement: If `S \subseteq k^n`, the affine algebraic set `V(I(S))` is the smallest algebraic set that contains `S`, in the sense that if `W \subseteq k^n` is any affine algebraic set containing `S`, then `V(I(S)) \subseteq W`.
   Lean declaration: `zariskiClosure_is_smallest_algebraic_set`.

## Source Inventory

- id: line-17
  kind: theorem
  lean: zariskiClosure_is_smallest_algebraic_set
  source: docs/source.tex:17-19

| Source id | Kind | Source lines | Lean declaration |
|---|---|---|---|
| `line-17` | theorem | `docs/source.tex` lines 17-19; proof lines 21-23 | `zariskiClosure_is_smallest_algebraic_set` |

- `line-17`: theorem `zariskiClosure_is_smallest_algebraic_set` from `docs/source.tex` lines 17-19; proof lines 21-23; Lean declaration `zariskiClosure_is_smallest_algebraic_set`.

## Source Statement Inventory

### line-17

- Source label: `line-17`
- Source inventory entry: `line-17`
- Source kind: theorem
- Source title: `zariskiClosure_is_smallest_algebraic_set`
- Source locator: `docs/source.tex`, theorem lines 17-19; proof lines 21-23.
- Source statement: If `S \subseteq k^n`, the affine algebraic set `V(I(S))` is the smallest algebraic set that contains `S`, in the sense that if `W \subseteq k^n` is any affine algebraic set containing `S`, then `V(I(S)) \subseteq W`.
- Complete source proof text: If `W \supseteq S`, then `I(W) \subseteq I(S)` because `I` is inclusion-reversing. But then `V(I(W)) \supseteq V(I(S))` because `V` also reverses inclusions. Since `W` is an affine algebraic set, `V(I(W)) = W` by The Ideal–Variety Correspondence, and the result follows.
- Planned Lean declarations: `zariskiClosure_is_smallest_algebraic_set` in `ShadowBench/Source/Main.lean`.
- Companion Lean declarations: `IsAffineAlgebraicSet` encodes the source object class “affine algebraic set”; `zariskiClosure` encodes the source expression `V(I(S))`.
- Skeleton candidate used: candidate skeletons `Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` provided the required import/name/parameter shape, but their body used `Ideal.ofSet S` where `S` is a set of points, so the actual draft replaces this with Mathlib's `MvPolynomial.vanishingIdeal`. `Skeleton4.lean` was malformed and not adopted. The final statement also records that the closure contains `S`, which is explicit in the source phrase “that contains `S`”.
- Dependencies: `Mathlib.RingTheory.Nullstellensatz`; Mathlib declarations `MvPolynomial.zeroLocus`, `MvPolynomial.vanishingIdeal`, `MvPolynomial.zeroLocus_vanishingIdeal_le`, `MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal`, and the zero-locus/vanishing-ideal Galois connection.
- Formal statement review: The Lean theorem quantifies over a field `k`, a natural number `n`, and a set `S : Set (Fin n → k)`, representing `S \subseteq k^n`. It states both `S ⊆ zariskiClosure k S` and the minimality clause: for every `W : Set (Fin n → k)`, if `W` is affine algebraic and contains `S`, then `zariskiClosure k S ⊆ W`.
- Source qualifiers:
  - Mathematical object class: field `k`; affine space `k^n`; subsets of `k^n`; affine algebraic sets.
  - Quantifier order: choose `k`, `n`, and `S`; then quantify over any candidate algebraic set `W` containing `S`.
  - Parameter domain: `S` and `W` are subsets of `k^n`.
  - Output codomain: proposition asserting containment and minimality.
  - Equality/image condition: `V(I(S))` is represented as the zero locus of the vanishing ideal of `S`; affine algebraic sets are represented as zero loci of ideals.
  - Side conditions: `W` must be affine algebraic and must contain `S`.
  - Follow-on claims: `V(I(S))` contains `S`, and any affine algebraic `W` containing `S` contains `V(I(S))`.
- Lean coverage:
  - `Fin n → k` covers the source affine space `k^n`.
  - `zariskiClosure k S = MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k S)` covers `V(I(S))`.
  - `IsAffineAlgebraicSet k W := ∃ I, W = MvPolynomial.zeroLocus k I` covers “`W` is an affine algebraic set”.
  - The first conjunct of `zariskiClosure_is_smallest_algebraic_set` covers that `V(I(S))` contains `S`.
  - The second conjunct covers the bracketed minimality statement for every affine algebraic `W` containing `S`.
- Scope changes: No mathematical weakening intended. Representation choices are explicit: `k^n` is encoded as `Fin n → k`, and the source operators `V` and `I` are encoded by Mathlib's `MvPolynomial.zeroLocus` and `MvPolynomial.vanishingIdeal`. The source phrase “affine algebraic set” is bridged by `IsAffineAlgebraicSet`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: First prove `S ⊆ zariskiClosure k S` using `MvPolynomial.zeroLocus_vanishingIdeal_le`. For the minimality clause, unfold `IsAffineAlgebraicSet` and `zariskiClosure`; if `W = MvPolynomial.zeroLocus k I` and `S ⊆ W`, use `MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal` to translate `S ⊆ zeroLocus I` into `I ≤ vanishingIdeal S`, then use order reversal of zero loci from the Galois connection to derive `zeroLocus (vanishingIdeal S) ⊆ zeroLocus I = W`.

## Import Plan

Direct Lean imports for `ShadowBench/Source/Main.lean`:

```lean
import Mathlib.RingTheory.Nullstellensatz
```

## Suggested Search Modules

Non-gating prover search hints:

- `Mathlib.RingTheory.Nullstellensatz`
- Search terms: `MvPolynomial.zeroLocus`, `MvPolynomial.vanishingIdeal`, `zeroLocus_vanishingIdeal_le`, `le_zeroLocus_iff_le_vanishingIdeal`, `GaloisConnection`.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the companion definitions `IsAffineAlgebraicSet`, `zariskiClosure`, and the source theorem skeleton `zariskiClosure_is_smallest_algebraic_set`.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`.

## Required Names

- `zariskiClosure_is_smallest_algebraic_set`

## Handoff Checklist

- [x] Source document inspected with `formalization_document_inspect`.
- [x] Companion instructions and candidate skeletons read.
- [x] Source inventory entry `line-17` recorded with source statement and full source proof.
- [x] Direct import plan recorded and aligned with the target Lean file.
- [x] Root project module already imports the generated target module through `ShadowBench.lean` → `ShadowBench.Source` → `ShadowBench.Source.Main`.
- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [ ] Prover queue has eliminated theorem `sorry` placeholders.
