# Formalization Blueprint: `algebraic-geometry/L3/alg_gen_L3_009`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Candidate Skeletons

- Dataset: `Lemmy00/ShadowBench-skeletons-prod`
- `docs/skeletons/Skeleton1.lean`
- `docs/skeletons/Skeleton2.lean`
- `docs/skeletons/Skeleton3.lean`
- `docs/skeletons/Skeleton4.lean`

Use skeletons as candidate declaration shapes. Record which candidate, if any, was adopted and why it matches the source.

## Import Plan

```lean
import Mathlib
```

## Required Names

- `FiniteType`
- `surjective_iff_surjective_on_algClosed_points_of_finiteType`

## Statement Inventory

For each source theorem, lemma, definition, or named item:

- Planned Lean declaration: _pending_
- Source locator: `docs/source.tex`
- Skeleton candidate used: _pending_
- Dependencies: _pending_
- Formal statement review: _pending_
- Source qualifiers: _pending_
- Lean coverage: _pending_
- Scope changes: _pending_
- Statement verification status: _pending_
- Source proof / prover notes: _pending_

## Formalization Rules

```text
open CategoryTheory Opposite

/-
Formalize in Lean the following named items from Text.

1. Definition (FiniteType)
   The definition must be named `FiniteType`.
   Matched text (candidate 0, theorem, label=Morphism of finite type): \begin{theorem}[Morphism of finite type] A morphism \(f : X \to Y\) is said to be \emph{of
                                                                       finite type} if \(Y\) is the union of a family \((V_\alpha)\) of affine open subsets having
                                                                       the following property: \medskip \noindent (P) The inverse image \(f^{-1}(V_\alpha)\) is a
                                                                       finite union of affine open subsets \(U_{\alpha i}\) such that each of the rings
                                                                       \(\Gamma(U_{\alpha i},\mathcal O_X)\) is a finitely type \(\Gamm…
2. Theorem (surjective_iff_surjective_on_algClosed_points_of_finiteType)
   The theorem must be named `surjective_iff_surjective_on_algClosed_points_of_finiteType`.
   Matched text (candidate 1, theorem, label=surjective_iff_surjective_on_algClosed_points_of_finiteType): \begin{theorem}[surjective_iff_surjective_on_algClosed_points_of_finiteType] Let \(f:X\to
                                                                                                           Y\) be a morphism of finite type. In order that \(f\) be surjective, it is necessary and
                                                                                                           sufficient that, for every algebraically closed field \(\Omega\), the map \( X(\Omega)\to
                                                                                                           Y(\Omega)\) corresponding to \(f\) be surjective. \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
