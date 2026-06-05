# Formalization Blueprint: `algebra/L2/alg_gen_L2_006`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: single-file formalization containing the three required source-backed theorem declarations.
- `ShadowBench/Source.lean`: project aggregator importing `ShadowBench.Source.Main`.
- `ShadowBench.lean`: root project module importing `ShadowBench.Source`.

No split into additional generated files is currently needed because the source theorem is short and the three declarations share the same Mathlib setup.

## Import Plan

```lean
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Nullstellensatz
```

These are exactly the direct imports planned for `ShadowBench/Source/Main.lean`; the root project imports are already `ShadowBench.lean -> ShadowBench.Source -> ShadowBench.Source.Main`, so project-level builds cover the target file.

## Suggested Search Modules

- `Mathlib.RingTheory.Nullstellensatz`: Mathlib definitions `MvPolynomial.zeroLocus`, `MvPolynomial.vanishingIdeal`, and related Galois-connection lemmas.
- `Mathlib.RingTheory.Ideal.Operations`: radical notation and lemmas such as `Ideal.mem_radical_iff`.
- Search results used during planning: `MvPolynomial.zeroLocus`, `MvPolynomial.mem_zeroLocus_iff`, `MvPolynomial.vanishingIdeal`, `MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal`, `MvPolynomial.zeroLocus_vanishingIdeal_galoisConnection`, `Ideal.radical`, `Ideal.mem_radical_iff`.

## Required Names

- `zeroLocus_subset_of_ideal_le`
- `vanishingIdeal_le_of_subset`
- `zeroLocus_radical_eq_zeroLocus`

## Source Statement Inventory

### line-17

- Source locator: `docs/source.tex`, theorem block `line-17`, lines 17--22; proof lines 22--38.
- Source kind: theorem.
- Planned Lean declarations: `zeroLocus_subset_of_ideal_le`, `vanishingIdeal_le_of_subset`, `zeroLocus_radical_eq_zeroLocus`.
- Formal statement review: The source theorem has three claims. The first claim `I₁ ⊆ I₂ => V(I₁) ⊇ V(I₂)` is represented by `zeroLocus_subset_of_ideal_le`, whose conclusion is written as `MvPolynomial.zeroLocus K I₂ ⊆ MvPolynomial.zeroLocus K I₁`. The second claim `V₁ ⊆ V₂ => I(V₁) ⊇ I(V₂)` is represented by `vanishingIdeal_le_of_subset`, whose conclusion is `MvPolynomial.vanishingIdeal k V₂ ≤ MvPolynomial.vanishingIdeal k V₁`. The final claim `V(√I)=V(I)` is represented by `zeroLocus_radical_eq_zeroLocus`, using Lean's `I.radical` notation for `√I`. The Mathlib setup uses a coefficient field `k`, a point field `K`, and `[Algebra k K]`; the source's same-field notation is the special case `k = K`.
- Source qualifiers: ideals in a multivariate polynomial ring; affine zero loci of ideals; affine point sets `V₁`, `V₂`; subset hypotheses `I₁ ≤ I₂` and `V₁ ⊆ V₂`; vanishing ideals of point sets; equality of zero loci for an ideal and its radical; field-valued evaluation for the radical-power argument; quantifiers are universal over the relevant ideals, sets, and fields.
- Lean coverage: Mathlib's `MvPolynomial.zeroLocus K I` covers the source variety notation `V(I)`, and `MvPolynomial.vanishingIdeal k V` covers the source notation `I(V)`. The three planned Lean declarations cover respectively the ideal-to-variety reverse inclusion, the set-to-ideal reverse inclusion, and the radical-zero-locus equality. The arbitrary-set statement for `vanishingIdeal_le_of_subset` covers affine algebraic sets as a special class.
- Scope changes: The Lean statements use Mathlib's standard two-field affine-space representation with coefficient field `k`, point field `K`, and `[Algebra k K]`, which generalizes the source's single-field notation. The second statement is stated for all point sets rather than only affine algebraic sets because the source proof uses only set inclusion and pointwise vanishing. Source cases are all covered.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: Complete source proof text: first, if `I₁ ⊆ I₂` and `a ∈ V(I₂)`, every `f ∈ I₁` is also in `I₂`, so `f(a)=0` and `a ∈ V(I₁)`. Second, if `V₁ ⊆ V₂` and `f ∈ I(V₂)`, then every point of `V₁` is a point of `V₂`, so `f` vanishes on `V₁` and lies in `I(V₁)`. Finally, for `V(√I)=V(I)`, one inclusion follows from `I ⊆ √I` and reverse inclusion; for the converse, if `a ∈ V(I)` and `f ∈ √I`, take a positive power `f^m ∈ I`, evaluate to get `(f(a))^m=0`, and use field behavior to conclude `f(a)=0`. Prover notes: unfold `MvPolynomial.zeroLocus` or use `MvPolynomial.mem_zeroLocus_iff`; unfold `MvPolynomial.vanishingIdeal` for the set inclusion; for the radical theorem use `Ideal.mem_radical_iff`, evaluation preserving powers, and a power-zero lemma over a field.

## Candidate Skeleton Review

- Skeletons 1--3 are identical and Skeleton 4 only adds a malformed duplicate `:= by sorry` at the end.
- Adopted from skeletons: required theorem names and the high-level three-way split of the source theorem.
- Not adopted from skeletons: local redefinitions of `zeroLocus` and `vanishingIdeal`, the unnecessary `[Fintype σ]` assumption, and the general `[CommRing R]` setting for the radical equality. Mathlib already provides `MvPolynomial.zeroLocus` and `MvPolynomial.vanishingIdeal` in `Mathlib.RingTheory.Nullstellensatz`, and the source proof explicitly uses field behavior for the radical step.

## Formalization Rules

```text
open scoped BigOperators
open MvPolynomial

/-
Formalize in Lean the following named statements from the theorem in the text.

The Lean declarations must be named exactly:
- `zeroLocus_subset_of_ideal_le`
- `vanishingIdeal_le_of_subset`
- `zeroLocus_radical_eq_zeroLocus`

Matched text (candidate 0, theorem):
\begin{theorem}
Prove that the ideal-variety correspondence is inclusion-reversing, i.e.,
if $I_1 \subseteq I_2$ are ideals, then $\mathbf V(I_1) \supseteq \mathbf V(I_2)$,
and similarly, if $V_1 \subseteq V_2$ are affine algebraic sets, then
$\mathbf I(V_1) \supseteq \mathbf I(V_2)$.
Also prove that $\mathbf V(\sqrt{I})=\mathbf V(I)$ for any ideal $I$.
\end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
