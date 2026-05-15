# ShadowBench Instructions: `algebra/L2/alg_comp_L2_001`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Data.Finsupp.MonomialOrder
```

## Expected Declaration Names

- `expSet`

## Formalization Rules

```text
open MvPolynomial
open scoped MonomialOrder

/-
Formalize in Lean the Definition (expSet) from Text.

The definition must be named `expSet`.
   Matched text (candidate 0, definition, label=expSet): \begin{definition}[expSet] Suppose that $I = \langle x^\alpha \mid \alpha \in A \rangle$ is
                                                         a monomial ideal, and let $S$ be the set of all exponents that occur as monomials of $I$.
                                                         For any monomial order $>$, prove that the smallest element of $S$ with respect to $>$ must
                                                         lie in $A$. \end{definition}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
