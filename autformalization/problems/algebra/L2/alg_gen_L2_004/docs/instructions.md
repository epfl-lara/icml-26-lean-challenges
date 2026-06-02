# ShadowBench Instructions: `algebra/L2/alg_gen_L2_004`

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
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Nullstellensatz
```

## Expected Declaration Names

- `J`
- `exists_vanishingIdeal_zeroLocus_not_mem_J`

## Formalization Rules

```text
/-
Formalize in Lean the following named items from the theorem in the text.

1. Definition (J)
   The definition must be named `J`.
   Matched text (candidate 0, definition):
Let $J = \langle x^2 + y^2 - 1, y - 1\rangle \subseteq \mathbb R[x,y]$.

2. Theorem (exists_vanishingIdeal_zeroLocus_not_mem_J)
   The theorem must be named `exists_vanishingIdeal_zeroLocus_not_mem_J`.
   Matched text (candidate 0, theorem):
\begin{theorem}
Let $J = \langle x^2 + y^2 - 1, y - 1\rangle \subseteq \mathbb R[x,y]$.
Find a polynomial $f \in \mathbf I(\mathbf V(J))$ such that $f \notin J$.
\end{theorem}

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
