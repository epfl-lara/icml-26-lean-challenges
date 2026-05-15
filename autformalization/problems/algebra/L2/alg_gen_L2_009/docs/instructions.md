# ShadowBench Instructions: `algebra/L2/alg_gen_L2_009`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.AdjoinRoot
```

## Expected Declaration Names

- `J`

## Formalization Rules

```text
open scoped BigOperators
open MvPolynomial

/-
Formalize in Lean the Definition (J) from Text.

The definition must be named `J`.
   Matched text (candidate 0, definition, label=J): \begin{definition}[J] Let $k$ be an arbitrary field and let $I,J$ be ideals in
                                                    $k[x_1,\ldots,x_n]$. Show the following: \begin{enumerate} \item $\sqrt{IJ} = \sqrt{I \cap
                                                    J}$. \item In $k[x,y]$, let $I=\langle x\rangle$ and $J=\langle x,y\rangle$. Show that $I$
                                                    and $J$ are radical ideals, but $IJ$ is not a radical ideal. \item In $k[x,y]$, with
                                                    $I=\langle x\rangle$ and $J=\langle x,y\rangle$ as above, show that $\sqr…
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
