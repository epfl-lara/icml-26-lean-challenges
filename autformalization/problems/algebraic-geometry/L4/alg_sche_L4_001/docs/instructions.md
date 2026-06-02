# ShadowBench Instructions: `algebraic-geometry/L4/alg_sche_L4_001`

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

- `flat_is_open`
- `flat_open_image`
- `flat_morphism_complement_of_image_is_closed`

## Formalization Rules

```text
open CategoryTheory AlgebraicGeometry

/-
Formalize in Lean the following named items from Text.

1. Theorem (flat_is_open)
   The theorem must be named `flat_is_open`.
   Matched text (candidate 0, theorem, label=flat_is_open): \begin{theorem}[flat_is_open] Let $f : X \to Y$ be a flat morphism of finite type of
                                                            Noetherian schemes. Then $f$ is an open morphism. \end{theorem}
2. Corollary (flat_open_image)
   The corollary must be named `flat_open_image`.
   Matched text (candidate 1, corollary, label=flat_open_image): \begin{corollary}[flat_open_image] Let \(f \colon X \to Y\) be a flat morphism of finite
                                                                 type of Noetherian schemes. Let \(U \subset X\) be open. Then $f(U)$ is open in $Y$.
                                                                 \end{corollary}
3. Theorem (flat_morphism_complement_of_image_is_closed)
   The theorem must be named `flat_morphism_complement_of_image_is_closed`.
   Matched text (candidate 2, theorem, label=flat_morphism_complement_of_image_is_closed): \begin{theorem}[flat_morphism_complement_of_image_is_closed] Let \(f \colon X \to Y\) be a
                                                                                           flat morphism of schemes. Let \(U \subset X\) be open, and let \(V = \operatorname{Spec} B
                                                                                           \subset Y\) be an affine open subset. Then there exists an ideal \(I \subset B\) such that
                                                                                           \[ V \setminus \bigl(f(U) \cap V\bigr) = V(I). \] \end{theorem}

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
