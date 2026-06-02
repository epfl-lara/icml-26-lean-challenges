# Formalization Blueprint: `algebra/L2/alg_gen_L2_016`

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
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
```

## Required Names

- `span_pow_card_mul_le_span_image_pow`

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
/-
Formalize in Lean the Theorem (span_pow_card_mul_le_span_image_pow) from Text.

The theorem must be named `span_pow_card_mul_le_span_image_pow`.
   Matched text (candidate 0, theorem, label=span_pow_card_mul_le_span_image_pow): \begin{theorem}[span_pow_card_mul_le_span_image_pow] Let $s=\{g_1,\dots,g_r\}$ be a finite
                                                                                   subset of $k[x_1,\dots,x_n]$. Set $J := \langle s\rangle$ and let $M\ge 0$. Then \[ J^{\,rM}
                                                                                   \;\subseteq\; \left\langle\, g^M \mid g\in s \,\right\rangle. \] \end{theorem}
-/
```
