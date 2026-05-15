# ShadowBench Instructions: `algebra/L2/alg_gen_L2_002`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import ABM.Buchberger.GroebnerBases_normalForm
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Ideal
```

## Expected Declaration Names

- `exists_nonzero_remainder_of_lt_span_leadingTerms`

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

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
