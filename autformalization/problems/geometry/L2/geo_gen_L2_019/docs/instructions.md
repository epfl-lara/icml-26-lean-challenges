# ShadowBench Instructions: `geometry/L2/geo_gen_L2_019`

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

- `X`

## Formalization Rules

```text
open scoped Manifold ContDiff

/-
Formalize in Lean the Definition (X) from Text.

The definition must be named `X`.
   Matched text (candidate 0, definition, label=X): \begin{definition}[X] Proposition 8.19 states that if $F: M \to N$ is a diffeomorphism and
                                                    $X$ is a smooth vector field on $M$, then there is a unique smooth vector field $Y$ on $N$
                                                    such that $dF_p (X_p) = Y_{F(p)}$ for every $p \in M$. Show that this can be false if $F$ is
                                                    assumed only to be smooth and bijective: take $F: \mathbb{R} \to \mathbb{R}$ defined by
                                                    $F(x) = x^3$ and $X = d/dx$ on $\mathbb{R}$. \end{defini…
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
