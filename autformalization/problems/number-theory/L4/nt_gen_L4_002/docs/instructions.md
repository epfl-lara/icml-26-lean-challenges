# ShadowBench Instructions: `number-theory/L4/nt_gen_L4_002`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Candidate Skeletons

Dataset: `Lemmy00/ShadowBench-skeletons-prod`

- `docs/skeletons/Skeleton1.lean`
- `docs/skeletons/Skeleton2.lean`
- `docs/skeletons/Skeleton3.lean`
- `docs/skeletons/Skeleton4.lean`

Treat these as candidate statement/definition shapes, not authoritative answers. Prefer the source theorem and formalization rules when candidates disagree.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib
```

## Expected Declaration Names

- `LCM`
- `LCM_gt_0`
- `LCM_monotone`
- `LCM_dvd_by`
- `LCM_range_lower_bdd`

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

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
