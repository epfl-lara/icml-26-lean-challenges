# ShadowBench Instructions: `analysis/L4/ana_pde_L4_001`

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
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
```

## Expected Declaration Names

- `no_interior_max_of_Lu_pos`
- `main_theorem`

## Formalization Rules

```text
open Set Filter Topology Metric Real

/-
Formalize in Lean the following named items from Text.

1. Lemma (no_interior_max_of_Lu_pos)
   The lemma must be named `no_interior_max_of_Lu_pos`.
   Matched text (candidate 0, lemma, label=no_interior_max_of_Lu_pos): \begin{lemma}[no_interior_max_of_Lu_pos] Suppose $\Omega$ is a bounded and connected domain
                                                                       in $\mathbb{R}^n$. Let \[ Lu=\sum_{i,j} a^{ij}(x)u_{ij}+\sum_i b^i(x)u_i+c(x)u \] be
                                                                       uniformly elliptic with continuous coefficients and $c\le 0$ with $a_{ij}$ , $b_i$ and $c$
                                                                       are continuous and hence bounded. Suppose $u \in C^2(\Omega) \cap C(\bar{\Omega})$ satisfies
                                                                       $L u > 0$ in $\Omega$ with $c(x) \le 0$ in $\Omega$. If $u…
2. Theorem (main_theorem)
   The theorem must be named `main_theorem`.
   Matched text (candidate 1, theorem): \begin{theorem} Suppose $\Omega$ is a bounded and connected domain in $\mathbb{R}^n$. Let \[
                                        Lu=\sum_{i,j} a^{ij}(x)u_{ij}+\sum_i b^i(x)u_i+c(x)u \] be uniformly elliptic with
                                        continuous coefficients and $c\le 0$ with $a_{ij}$ , $b_i$ and $c$ are continuous and hence
                                        bounded. Suppose $u \in C^2(\Omega) \cap C(\bar{\Omega})$ satisfies $L u > 0$ in $\Omega$
                                        with $c(x) \le 0$. Then $u$ attains on $\partial \Omega$ its…

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
