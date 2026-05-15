# ShadowBench Instructions: `algebra/L2/alg_gen_L2_005`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Ideal.Span
```

## Expected Declaration Names

- `S`

## Formalization Rules

```text
/-
Formalize in Lean the Definition (S) from Text.

The definition must be named `S`.
   Matched text (candidate 0, definition, label=S): \begin{definition}[S] Let $k$ be an arbitrary field and let $S$ be the subset of all
                                                    polynomials in $k[x_1,\dots,x_n]$ that have no zeros in $k^n$. If $I$ is any ideal in
                                                    $k[x_1,\dots,x_n]$ such that $I \cap S=\varnothing$, show that $\mathbf
                                                    V(I)\neq\varnothing$. \end{definition}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
