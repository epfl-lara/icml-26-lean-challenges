# Formalization Blueprint: `analysis/L4/ana_pde_L4_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Candidate Skeletons

- Dataset: `Lemmy00/ShadowBench-skeletons-prod`
- `docs/skeletons/Skeleton1.lean`
- `docs/skeletons/Skeleton2.lean`
- `docs/skeletons/Skeleton3.lean`
- `docs/skeletons/Skeleton4.lean`

Use skeletons as candidate declaration shapes. Record which candidate, if any, was adopted and why it matches the source.

## Import Plan

```lean
import Mathlib
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
```

## Required Names

- `no_interior_max_of_Lu_pos`
- `main_theorem`

## Statement Inventory

For each source theorem, lemma, definition, or named item:

- Planned Lean declaration: _pending_
- Source locator: `docs/source.tex`
- Skeleton candidate used: _pending_
- Dependencies: _pending_
- Formal statement review: _pending_
- Source qualifiers: _pending_
- Lean coverage: _pending_
- Scope changes: _pending_
- Statement verification status: _pending_
- Source proof / prover notes: _pending_

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
