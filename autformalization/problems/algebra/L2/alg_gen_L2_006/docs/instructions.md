# ShadowBench Instructions: `algebra/L2/alg_gen_L2_006`

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
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Nullstellensatz
```

## Expected Declaration Names

- `zeroLocus_subset_of_ideal_le`
- `vanishingIdeal_le_of_subset`
- `zeroLocus_radical_eq_zeroLocus`

## Formalization Rules

```text
open scoped BigOperators
open MvPolynomial

/-
Formalize in Lean the following named statements from the theorem in the text.

The Lean declarations must be named exactly:
- `zeroLocus_subset_of_ideal_le`
- `vanishingIdeal_le_of_subset`
- `zeroLocus_radical_eq_zeroLocus`

Matched text (candidate 0, theorem):
\begin{theorem}
Prove that the ideal-variety correspondence is inclusion-reversing, i.e.,
if $I_1 \subseteq I_2$ are ideals, then $\mathbf V(I_1) \supseteq \mathbf V(I_2)$,
and similarly, if $V_1 \subseteq V_2$ are affine algebraic sets, then
$\mathbf I(V_1) \supseteq \mathbf I(V_2)$.
Also prove that $\mathbf V(\sqrt{I})=\mathbf V(I)$ for any ideal $I$.
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
