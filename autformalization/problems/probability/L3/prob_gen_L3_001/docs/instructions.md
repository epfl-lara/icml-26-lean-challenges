# ShadowBench Instructions: `probability/L3/prob_gen_L3_001`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib
```

## Expected Declaration Names

- `BuffonNeedle`
- `BuffonProb`

## Formalization Rules

```text
open Real MeasureTheory ProbabilityTheory

/-
Formalize in Lean the following named items from Text.


0. Definition (Ω_pos)
   The definition must be named `Ω_pos`.
   Matched text (candidate 0, paragraph): Theorem(`BuffonNeedle`).
1. Definition (Ω_angle)
   The definition must be named `Ω_angle`.
   Matched text (candidate 0, paragraph): Theorem(`BuffonNeedle`).
2. Definition (Ω)
   The definition must be named `Ω`.
   Matched text (candidate 1, paragraph): Suppose a short needle of length $\ell$ is dropped onto a paper ruled with equally spaced
                                          lines of distance $d \ge \ell$. Then the probability that the needle crosses a line on the
                                          paper is $\frac{2\ell}{\pi d}$.
3. Definition (BuffonProb)
   The definition must be named `BuffonProb`.
   Matched text (candidate 2, paragraph): Proof.
4. Theorem (BuffonNeedle)
   The theorem must be named `BuffonNeedle`.
   Matched text (candidate 3, paragraph): We can assume the uniform probability distribution over $[0, d] \times [0, \pi]$, where each
                                          component means the midpoint position relative to the closest lower line and the angle
                                          relative to a fixed direction of the ruling respectively. Then the needle crosses a line
                                          with angle $\theta$ exactly when its height $y$ of midpoint is lower than $\frac{\ell \sin
                                          \theta}{2}$ or higher than $d - \frac{\ell \sin \theta}{2}$…

Every listed named item must be formalized with exactly the stated Lean name.
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
