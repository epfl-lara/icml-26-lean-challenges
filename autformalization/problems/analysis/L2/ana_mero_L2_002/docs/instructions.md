# ShadowBench Instructions: `analysis/L2/ana_mero_L2_002`

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
import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Topology.LocallyFinsupp
```

## Expected Declaration Names

- `min_divisor_le_divisor_add`

## Formalization Rules

```text
open Filter Topology

/-
Formalize in Lean the Theorem (min_divisor_le_divisor_add) from Text.

The theorem must be named `min_divisor_le_divisor_add`.
   Matched text (candidate 0, theorem, label=min_divisor_le_divisor_add): \begin{theorem}[min_divisor_le_divisor_add] Let $f_1,f_2 : \mathbb K \to E$ be meromorphic
                                                                          on a set $U \subseteq \mathbb K$, and let $z \in U$. Assume that the order of $f_1+f_2$ at
                                                                          $z$ is finite. Then \[
                                                                          \min\bigl(\operatorname{div}_U(f_1)(z),\operatorname{div}_U(f_2)(z)\bigr) \;\le\;
                                                                          \operatorname{div}_U(f_1+f_2)(z). \] \end{theorem}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
