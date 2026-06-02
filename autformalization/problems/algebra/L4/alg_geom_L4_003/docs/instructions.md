# ShadowBench Instructions: `algebra/L4/alg_geom_L4_003`

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

- `constructible_iff`
- `cyclotomic_angle_constructible_iff`

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

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
