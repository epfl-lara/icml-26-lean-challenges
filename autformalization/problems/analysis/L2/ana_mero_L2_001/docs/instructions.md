# ShadowBench Instructions: `analysis/L2/ana_mero_L2_001`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Topology.LocallyFinsupp
```

## Expected Declaration Names

- `ABM_analysis_L2_ana_mero_L2_001_item_1`
- `ABM_analysis_L2_ana_mero_L2_001_item_2`
- `divisor`

## Formalization Rules

```text
open Filter Topology

/-
Formalize in Lean the following named items from Text.

1. Definition (ABM_analysis_L2_ana_mero_L2_001_item_1)
   The definition must be named `ABM_analysis_L2_ana_mero_L2_001_item_1`.
   Matched text (candidate 0, definition): \begin{definition} Let $\mathbb K$ be a nontrivially normed field and let $E$ be a normed
                                           vector space over $\mathbb K$. Let $U \subseteq \mathbb K$ be a set and let $f : \mathbb K
                                           \to E$ be a function. The \emph{divisor} of $f$ on $U$ is the function \[
                                           \operatorname{div}_U(f) : \mathbb K \longrightarrow \mathbb{Z} \] defined by \[
                                           \operatorname{div}_U(f)(z) = \begin{cases} \operatorname{ord}_z(f), & \text{if $f$ i…
2. Definition (ABM_analysis_L2_ana_mero_L2_001_item_2)
   The definition must be named `ABM_analysis_L2_ana_mero_L2_001_item_2`.
   Matched text (candidate 1, definition): \begin{definition} The \emph{support} of the divisor is \[
                                           \operatorname{supp}(\operatorname{div}_U(f)) = \{ z \in U \mid \operatorname{div}_U(f)(z)
                                           \neq 0 \}. \] Equivalently, \[ \operatorname{supp}(\operatorname{div}_U(f)) = \{ z \in U
                                           \mid \operatorname{ord}_z(f) \neq 0 \text{ and } \operatorname{ord}_z(f) \neq \infty \}. \]
                                           \end{definition}
3. Definition (divisor)
   The definition must be named `divisor`.
   Matched text (candidate 2, definition, label=divisor): \begin{definition}[divisor] If $f$ is meromorphic on $U$, then the support of
                                                          $\operatorname{div}_U(f)$ is locally finite in $U$. \end{definition}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
