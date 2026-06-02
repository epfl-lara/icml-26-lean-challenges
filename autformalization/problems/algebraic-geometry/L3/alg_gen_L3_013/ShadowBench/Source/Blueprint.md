# Formalization Blueprint: `algebraic-geometry/L3/alg_gen_L3_013`

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

- `IsQuasiFiniteModule`
- `isolated_in_fiber_iff_stalk_quasiFinite`

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
