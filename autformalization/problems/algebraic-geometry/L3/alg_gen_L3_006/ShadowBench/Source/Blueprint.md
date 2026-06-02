# Formalization Blueprint: `algebraic-geometry/L3/alg_gen_L3_006`

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
import Mathlib.Algebra.Ring.Basic
import Mathlib.Topology.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Scheme.Basic
import Mathlib.Sheaf.Basic
import Mathlib.Sheaf.GlobalSections
import Mathlib.CategoryTheory.Basic
import Mathlib.CategoryTheory.Opposite
```

## Required Names

- `FiniteType`
- `affineFiniteType_iff_globalSectionsFiniteType`

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
2. Theorem (affineFiniteType_iff_globalSectionsFiniteType)
   The theorem must be named `affineFiniteType_iff_globalSectionsFiniteType`.
   Matched text (candidate 1, theorem, label=affineFiniteType_iff_globalSectionsFiniteType): \begin{theorem}[affineFiniteType_iff_globalSectionsFiniteType] Let \(X\) and \(Y\) be two
                                                                                             affine schemes. Then, \(X\) is of finite type over \(Y\) if and only if \(\Gamma(X,\mathcal
                                                                                             O_X)\) is a finite type algebra over \(\Gamma(Y,\mathcal O_Y)\). \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
