# ShadowBench Instructions: `algebraic-geometry/L3/alg_gen_L3_008`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib
```

## Expected Declaration Names

- `FiniteType`
- `hasPropertyP_of_finiteType`
- `immersion_is_of_finiteType`

## Formalization Rules

```text
open CategoryTheory Opposite
open TopologicalSpace

/-
Formalize in Lean the following named items from Text.

1. Definition (FiniteType)
   The definition must be named `FiniteType`.
   Matched text (candidate 0, theorem, label=Morphism of finite type): \begin{theorem}[Morphism of finite type] A morphism \(f : X \to Y\) is said to be \emph{of
                                                                       finite type} if \(Y\) is the union of a family \((V_\alpha)\) of affine open subsets having
                                                                       the following property: \medskip \noindent (P) The inverse image \(f^{-1}(V_\alpha)\) is a
                                                                       finite union of affine open subsets \(U_{\alpha i}\) such that each of the rings
                                                                       \(\Gamma(U_{\alpha i},\mathcal O_X)\) is a finitely type \(\Gamm…
2. Theorem (hasPropertyP_of_finiteType)
   The theorem must be named `hasPropertyP_of_finiteType`.
   Matched text (candidate 1, lemma): \begin{lemma} If \(f:X \to Y \) is a morphism of finite type, then every open affine subset
                                      \(W\) of \(Y\) has the property (P). \end{lemma}
3. Theorem (immersion_is_of_finiteType)
   The theorem must be named `immersion_is_of_finiteType`.
   Matched text (candidate 2, theorem, label=immersion_is_of_finiteType): \begin{theorem}[immersion_is_of_finiteType] Let \(f : X \to Y\) be an immersion. If the
                                                                          underlying space of \(Y\) (resp. of \(X\)) is locally noetherian (resp. noetherian), then
                                                                          \(f\) is of finite type. \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
