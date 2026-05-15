# ShadowBench Instructions: `analysis/L2/ana_gen_L2_002`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Real.ConjExponents
```

## Expected Declaration Names

- `geom_mean_le_arith_mean_weighted`
- `geom_mean_le_arith_mean2_weighted`
- `young_inequality_of_nonneg`

## Formalization Rules

```text
open Finset NNReal ENNReal
open scoped BigOperators

/-
Formalize in Lean the following named items from Text.

1. Theorem (geom_mean_le_arith_mean_weighted)
   The theorem must be named `geom_mean_le_arith_mean_weighted`.
   Matched text (candidate 0, paragraph): Theorem (Young's inequility)
2. Theorem (geom_mean_le_arith_mean2_weighted)
   The theorem must be named `geom_mean_le_arith_mean2_weighted`.
   Matched text (candidate 1, paragraph): If $a,b \ge 0$ are non-negative real numbers and $p,q$ are positive real numbers satisfying
                                          $\frac{1}{p} + \frac{1}{q} = 1$, then $$ ab \le \frac{a^p}{p} + \frac{b^q}{q}$$
3. Theorem (geom_mean_le_arith_mean2_weighted)
   The theorem must be named `geom_mean_le_arith_mean2_weighted`.
   Matched text (candidate 2, paragraph): proof
4. Theorem (young_inequality_of_nonneg)
   The theorem must be named `young_inequality_of_nonneg`.
   Matched text (candidate 3, paragraph): Since $p^{-1} + q^{-1} = 1$, by the weighted AM-GM inequality, we have $$
                                          {a^p}^{p^{-1}}{b^q}^{q^{-1}} \le p^{-1}a^p + q^{-1} b^q$$ which is equivalent to $$ ab \le
                                          \frac{a^p}{p} + \frac{b^q}{q}$$

Every listed named item must be formalized with exactly the stated Lean name.
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
