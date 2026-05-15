# Formalization Blueprint: `number-theory/L4/nt_gen_L4_002`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib
```

## Required Names

- `LCM`
- `LCM_gt_0`
- `LCM_monotone`
- `LCM_dvd_by`
- `LCM_range_lower_bdd`

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
/-
Formalize in Lean the following named items from Text.

1. Definition (LCM)
   The definition must be named `LCM`.
   Matched text (candidate 0, definition, label=Least Common Multiple): \begin{definition}[Least Common Multiple] Define \(\text{LCM}(m)\) as the least common
                                                                        multiple of all positive integers up to a given natural number \( m \). \end{definition}
2. Lemma (LCM_gt_0)
   The lemma must be named `LCM_gt_0`.
   Matched text (candidate 1, lemma, label=LCM Greater Than Zero): \begin{lemma}[LCM Greater Than Zero] For any natural number \( m \), the least common
                                                                   multiple \( \text{LCM}(m) \) is greater than zero. \end{lemma}
3. Lemma (LCM_monotone)
   The lemma must be named `LCM_monotone`.
   Matched text (candidate 2, lemma, label=LCM monotonicity): \begin{lemma}[LCM monotonicity] For all natural numbers \( m \le n \), \( \mathrm{LCM}(m)
                                                              \le \mathrm{LCM}(n) \). \end{lemma}
4. Lemma (LCM_dvd_by)
   The lemma must be named `LCM_dvd_by`.
   Matched text (candidate 3, lemma, label=Divisibility of binomial coefficients by least common multiple): \begin{lemma}[Divisibility of binomial coefficients by least common multiple] For natural
                                                                                                            numbers \( m \) and \( n \) with \( 1 \leq m \leq n \), the product \( m \cdot \binom{n}{m}
                                                                                                            \) divides the least common multiple \( \mathrm{LCM}(1, 2, \dots, n) \). That is, \( m \cdot
                                                                                                            \binom{n}{m} \mid \mathrm{LCM}(n) \). \end{lemma}
5. Lemma (LCM_range_lower_bdd)
   The lemma must be named `LCM_range_lower_bdd`.
   Matched text (candidate 4, theorem, label=LCM_range_lower_bdd): \begin{theorem}[LCM_range_lower_bdd] For all natural numbers \( m \geq 7 \), the least
                                                                   common multiple of the numbers from \( 1 \) to \( m \) satisfies \( \mathrm{LCM}(m) \geq 2^m
                                                                   \). \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
