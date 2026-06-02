# Formalization Blueprint: `analysis/L2/ana_four_L2_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Candidate Skeletons

- Dataset: `Lemmy00/ShadowBench-skeletons-prod`
- `docs/skeletons/Skeleton1.lean`
- `docs/skeletons/Skeleton2.lean`
- `docs/skeletons/Skeleton3.lean`
- `docs/skeletons/Skeleton4.lean`

Use skeletons as candidate declaration shapes. Record which candidate, if any, was adopted and why it matches the source.

## Import Plan

```lean
import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Fourier.Notation
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
```

## Required Names

- `fourierIntegral`
- `fourierIntegral_const_smul`

## Statement Inventory

For each source theorem, lemma, definition, or named item:

- Planned Lean declaration: _pending_
- Source locator: `docs/source.tex`
- Skeleton candidate used: _pending_
- Dependencies: _pending_
- Formal statement review: _pending_
- Source qualifiers: _pending_
- Lean coverage: _pending_
- Scope changes: _pending_
- Statement verification status: _pending_
- Source proof / prover notes: _pending_

## Formalization Rules

```text
open MeasureTheory Filter
open scoped Topology

/-
Formalize in Lean the following named items from Text.

1. Definition (fourierIntegral)
   The definition must be named `fourierIntegral`.
   Matched text (candidate 0, definition, label=fourierIntegral): \begin{definition}[fourierIntegral] Let $K$ be a commutative ring and let $V, W$ be modules
                                                                  over $K$. Let $E$ be a complete normed $\mathbb{C}$-vector space, $\mu$ be a measure on $V$,
                                                                  $L : V \times W \to K$ a bilinear form, and let $e : K \to \mathbb{S}$ be an additive
                                                                  character. For a function $f : V \to E$, its Fourier transform is defined: \[
                                                                  \widehat{f}_{e,\mu,L}(w) \;:=\; \int_V e\!\bigl(-L(v,w)\bigr)\, f(v)\,…
2. Theorem (fourierIntegral_const_smul)
   The theorem must be named `fourierIntegral_const_smul`.
   Matched text (candidate 1, theorem, label=fourierIntegral_const_smul): \begin{theorem}[fourierIntegral_const_smul] Let $r \in \mathbb{C}$. Then $ \mathcal
                                                                          F_{e,\mu,L}(r \cdot f) \;=\; r \cdot \widehat{f}_{e,\mu,L}. $ \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
