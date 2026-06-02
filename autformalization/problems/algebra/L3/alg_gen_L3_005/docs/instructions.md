# ShadowBench Instructions: `algebra/L3/alg_gen_L3_005`

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

- `I_isPrimary`
- `I_not_infIrred`

## Formalization Rules

```text
open MvPolynomial

/-
Formalize in Lean the two named statements from the theorem in the text.

The Lean declarations must be named:
- `I_isPrimary`
- `I_not_infIrred`

Matched text (candidate 0, theorem):
\begin{theorem}
Let $I = \langle x^2, xy, y^2 \rangle \subseteq k[x, y]$.
\begin{enumerate}
    \item[I_isPrimary] $I$ is primary.
    \item[I_not_infIrred] $I = \langle x^2, y \rangle \cap \langle x, y^2 \rangle$ and conclude that $I$ is not irreducible.
\end{enumerate}
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
