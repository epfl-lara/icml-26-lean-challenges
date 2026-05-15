# ShadowBench Instructions: `analysis/L3/ana_pde_L3_001`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
```

## Expected Declaration Names

- `satisfies_interior_sphere`

## Formalization Rules

```text
/-
Formalize in Lean the Definition (satisfies_interior_sphere) from Text.

The definition must be named `satisfies_interior_sphere`.
   Matched text (candidate 0, definition, label=satisfies_interior_sphere): \begin{definition}[satisfies_interior_sphere] Let $\Omega\subset \mathbb{R}^n$ be connected
                                                                            and open. Let \[ Lu = \sum_{i,j=1}^n a^{ij}(x)u_{ij} + \sum_{i=1}^n b^i(x)u_i + c(x)u \] be
                                                                            uniformly elliptic in $\Omega$, where $a^{ij},b^i,c$ are continuous and \[ c(x)\le 0 \qquad
                                                                            \text{in } \Omega. \] Suppose \[ u\in C^2(\Omega), \qquad Lu\ge 0 \quad \text{in } \Omega.
                                                                            \] If $u$ attains a nonnegative maximum at an interi…
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
