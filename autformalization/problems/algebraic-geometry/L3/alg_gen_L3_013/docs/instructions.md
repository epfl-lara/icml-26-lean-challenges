# ShadowBench Instructions: `algebraic-geometry/L3/alg_gen_L3_013`

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

- `IsQuasiFiniteModule`
- `isolated_in_fiber_iff_stalk_quasiFinite`

## Formalization Rules

```text
open CategoryTheory

/-
Formalize in Lean the following named items from Text.

1. Definition (IsQuasiFiniteModule)
   The definition must be named `IsQuasiFiniteModule`.
   Matched text (candidate 0, definition): \begin{definition} Given a local ring $A$ with the maximal ideal \(\mathfrak{m}\), we say
                                           that an \(A\)-module \(M\) is quasi-finite over \(A\) if \(M/\mathfrak{m} M \) has finite
                                           rank over the residue field \(k = A/\mathfrak{m}\). \end{definition}
2. Theorem (isolated_in_fiber_iff_stalk_quasiFinite)
   The theorem must be named `isolated_in_fiber_iff_stalk_quasiFinite`.
   Matched text (candidate 1, theorem): \begin{theorem} Let \(f:X\to Y\) be a morphism locally of finite type, and let \(x\) be a
                                        point of \(X\). The following conditions are equivalent: \begin{enumerate}[label=(\alph*)]
                                        \item The point \(x\) is isolated in its fiber \(f^{-1}(f(x))\). \item The ring \(\mathcal
                                        O_x\) is a quasi-finite \(\mathcal O_{f(x)}\)-module \((0,7.4.1)\). \end{enumerate}
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
