# Formalization Blueprint: `algebra/L4/alg_geom_L4_003`

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
```

## Required Names

- `constructible_iff`
- `cyclotomic_angle_constructible_iff`

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
open Metric EuclideanSpace IntermediateField Module Polynomial
open scoped PiLp Real

/-
Formalize in Lean the following named items from Text.

1. Theorem (constructible_iff)
   The theorem must be named `constructible_iff`.
   Matched text (candidate 0, theorem):
Theorem(`constructible_iff`)

Let $\alpha \in \mathbb{R}$ and $K$ the normal closure of $\mathbb{Q}(\alpha)/\mathbb{Q}$
in $\mathbb{C}$. The number $\alpha$ is constructible if and only if
$[K:\mathbb{Q}]$ is a power of 2.

2. Theorem (cyclotomic_angle_constructible_iff)
   The theorem must be named `cyclotomic_angle_constructible_iff`.
   Matched text (candidate 1, theorem):
Theorem(`cyclotomic_angle_constructible_iff`)

An angle $2\pi/n$ is constructible if and only if $n$ is a product of a power of $2$
and some distinct Fermat primes. Here, a Fermat prime is a prime number of the form
$2^{2^a}+1$ for some nonnegative integer $a$. This is equivalent to constructibility
of a regular $n$-gon.

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
