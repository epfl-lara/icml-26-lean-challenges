# Formalization Blueprint: `algebra/L2/alg_gen_L2_002`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import ABM.Buchberger.GroebnerBases_normalForm
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Ideal
```

## Required Names

- `exists_nonzero_remainder_of_lt_span_leadingTerms`

## Statement Inventory

For each source theorem, lemma, definition, or named item:

- Planned Lean declaration: _pending_
- Source locator: `docs/source.tex`
- Dependencies: _pending_
- Formal statement review: _pending_
- Source qualifiers: _pending_
- Lean coverage: _pending_
- Scope changes: _pending_
- Statement verification status: _pending_
- Source proof / prover notes: _pending_

## Formalization Rules

```text
open MvPolynomial MonomialOrder
open scoped MonomialOrder

/-
Formalize in Lean the Theorem (exists_nonzero_remainder_of_lt_span_leadingTerms) from Text.

The theorem must be named `exists_nonzero_remainder_of_lt_span_leadingTerms`.
   Matched text (candidate 0, theorem, label=exists_nonzero_remainder_of_lt_span_leadingTerms): \begin{theorem}[exists_nonzero_remainder_of_lt_span_leadingTerms] Suppose that $I=\langle
                                                                                                f_1,\dots,f_s\rangle$ is an ideal such that $\langle
                                                                                                \operatorname{LT}(f_1),\dots,\operatorname{LT}(f_s)\rangle$ is strictly smaller than
                                                                                                $\langle \operatorname{LT}(I)\rangle$. \begin{enumerate} \item[(a)] Prove that there is some
                                                                                                $f\in I$ whose remainder on division by $f_1,\dots,f_s$ is nonzero. \end{enumerate}
                                                                                                \end{theorem}
-/
```
