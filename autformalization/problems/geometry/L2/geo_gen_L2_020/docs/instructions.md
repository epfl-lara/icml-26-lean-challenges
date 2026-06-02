# ShadowBench Instructions: `geometry/L2/geo_gen_L2_020`

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
import Mathlib.Manifold.SmoothManifold
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Basic
```

## Expected Declaration Names

- `exists_smooth_vectorField_on_graph`

## Formalization Rules

```text
open scoped Manifold ContDiff

/-
Formalize in Lean the Theorem (exists_smooth_vectorField_on_graph) from Text.

The theorem must be named `exists_smooth_vectorField_on_graph`.
   Matched text (candidate 0, theorem, label=exists_smooth_vectorField_on_graph): \begin{theorem}[exists_smooth_vectorField_on_graph] Let $M$ be a smooth manifold with or
                                                                                  without boundary, let $N$ be a smooth manifold, and let $f: M \to N$ be a smooth map. Define
                                                                                  $F: M \to M \times N$ by $F(x) = (x, f(x))$. Show that for every $X \in \mathfrak{X}(M)$,
                                                                                  there is a smooth vector field $Y$ on $M \times N$ that is $F$-related to $X$; that is,
                                                                                  $dF_p(X_p) = Y_{F(p)}$ for every $p \in M$. \end{theorem}
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Use candidate skeletons as search hints for initial theorem statements and definitions; verify source fidelity before keeping one.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
