# ShadowBench Instructions: `analysis/L3/ana_gen_L3_008`

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

- `intervalIntegrable_g_and_integral_g_eq_integral`

## Formalization Rules

```text
open Set MeasureTheory

/-
Formalize in Lean the Theorem (intervalIntegrable_g_and_integral_g_eq_integral) from Text.

The theorem must be named `intervalIntegrable_g_and_integral_g_eq_integral`.
   Matched text (candidate 0, theorem, label=intervalIntegrable_g_and_integral_g_eq_integral): \begin{theorem}[intervalIntegrable_g_and_integral_g_eq_integral] Suppose $f$ is integrable
                                                                                               on $[0, b]$, and \[ g(x) = \int_x^b \frac{f(t)}{t} dt \quad \text{for } 0 < x \le b. \]
                                                                                               Prove that $g$ is integrable on $[0, b]$ and \[ \int_0^b g(x) dx = \int_0^b f(t) dt. \]
                                                                                               \end{theorem}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
