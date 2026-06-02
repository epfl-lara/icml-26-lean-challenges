# ShadowBench Instructions: `analysis/L2/ana_gen_L2_004`

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
import Aesop
```

## Expected Declaration Names

- `exists_seq_finite_rank_strongly_convergent_to`

## Formalization Rules

```text
open Filter TopologicalSpace
open scoped Topology

/-
Formalize in Lean the Theorem (exists_seq_finite_rank_strongly_convergent_to) from Text.

The theorem must be named `exists_seq_finite_rank_strongly_convergent_to`.
   Matched text (candidate 0, theorem, label=exists_seq_finite_rank_strongly_convergent_to): \begin{theorem}[exists_seq_finite_rank_strongly_convergent_to] Consider a separable Hilbert
                                                                                             space $\mathcal{H}$. Show that for any bounded operator $T$ there is a sequence $\{T_n\}$ of
                                                                                             bounded operators of finite rank so that $T_n \to T$ strongly as $n \to \infty$.
                                                                                             \end{theorem}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
