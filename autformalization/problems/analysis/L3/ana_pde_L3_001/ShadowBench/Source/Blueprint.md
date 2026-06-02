# Formalization Blueprint: `analysis/L3/ana_pde_L3_001`

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
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
```

## Required Names

- `satisfies_interior_sphere`

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
/-
Formalize in Lean the Theorem (satisfies_interior_sphere) from Text.

The theorem must be named `satisfies_interior_sphere`.
   Matched text (candidate 0, theorem, label=satisfies_interior_sphere): \begin{theorem}[satisfies_interior_sphere] Let $\Omega\subset \mathbb{R}^n$ be connected and
                                                                         open. Let \[ Lu = \sum_{i,j=1}^n a^{ij}(x)u_{ij} + \sum_{i=1}^n b^i(x)u_i + c(x)u \] be
                                                                         uniformly elliptic in $\Omega$, where $a^{ij},b^i,c$ are continuous and \[ c(x)\le 0 \qquad
                                                                         \text{in } \Omega. \] Suppose \[ u\in C^2(\Omega), \qquad Lu\ge 0 \quad \text{in } \Omega.
                                                                         \] If $u$ attains a nonnegative maximum at an interior…
-/
```
