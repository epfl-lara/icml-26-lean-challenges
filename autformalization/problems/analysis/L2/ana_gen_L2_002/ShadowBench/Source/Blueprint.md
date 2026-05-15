# Formalization Blueprint: `analysis/L2/ana_gen_L2_002`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Real.ConjExponents
```

## Required Names

- `geom_mean_le_arith_mean_weighted`
- `geom_mean_le_arith_mean2_weighted`
- `young_inequality_of_nonneg`

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
