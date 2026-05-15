# Formalization Blueprint: `analysis/L3/ana_gen_L3_006`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Bases
import Mathlib.Analysis.InnerProductSpace.l2Space
```

## Required Names

- `IsCompactOperator`
- `ABM_analysis_L3_ana_gen_L3_006_item_2`
- `ABM_analysis_L3_ana_gen_L3_006_item_3`
- `weyl_von_neumann`

## Statement Inventory

For each source theorem, lemma, definition, or named item:

- Planned Lean declaration: _pending_
- Source locator: `docs/source.tex`
- Dependencies: _pending_
- Formal statement review: _pending_
- Source qualifiers: _pending_
- Lean coverage: _pending_
- Scope changes: _pending_
- Statement verification status: _pending_
- Source proof / prover notes: _pending_

## Formalization Rules

```text
open ContinuousLinearMap
open HilbertBasis

/-
Formalize in Lean the following named items from Text.

1. Definition (IsCompactOperator)
   The definition must be named `IsCompactOperator`.
   Matched text (candidate 0, theorem, label=Weyl--von Neumann theorem): \begin{theorem}[Weyl--von Neumann theorem] Let \(H\) be a separable Hilbert space and let
                                                                         \(A=A^*\in\mathcal B(H)\). Then for every \(\varepsilon>0\), there exist a diagonal self-
                                                                         adjoint operator \(D\) and a compact self-adjoint operator \(K\) such that \[ A=D+K, \qquad
                                                                         \|K\|<\varepsilon. \] \end{theorem}
2. Lemma (ABM_analysis_L3_ana_gen_L3_006_item_2)
   The lemma must be named `ABM_analysis_L3_ana_gen_L3_006_item_2`.
   Matched text (candidate 1, lemma, label=Spectral localization): \begin{lemma}[Spectral localization] Let \(A=A^*\in\mathcal B(H)\), and let \(E\) be its
                                                                   spectral measure. If \(I\subset\mathbb R\) is an interval and \(x\in E(I)H\), then for every
                                                                   \(\lambda_I\in I\), \[ \|(A-\lambda_I I_H)x\| \le |I|\,\|x\|. \] \end{lemma}
3. Lemma (ABM_analysis_L3_ana_gen_L3_006_item_3)
   The lemma must be named `ABM_analysis_L3_ana_gen_L3_006_item_3`.
   Matched text (candidate 2, lemma, label=Compact-tail criterion): \begin{lemma}[Compact-tail criterion] Let \((e_n)_{n=1}^\infty\) be an orthonormal basis of
                                                                    \(H\). Suppose \(K\in\mathcal B(H)\) satisfies \[ \|K e_n\|\to 0. \] Then \(K\) is compact.
                                                                    \end{lemma}
4. Theorem (weyl_von_neumann)
   The theorem must be named `weyl_von_neumann`.
   Matched text (candidate 3, theorem, label=weyl_von_neumann): \begin{theorem}[weyl_von_neumann] Let \(A=A^*\in\mathcal B(H)\), where \(H\) is separable.
                                                                Then for every \(\varepsilon>0\), there exist an orthonormal basis \((e_n)\) of \(H\) and
                                                                scalars \(\lambda_n\in\mathbb R\) such that \[ \|(A-\lambda_n I_H)e_n\|<\varepsilon
                                                                \quad\text{for all }n, \] and \[ \|(A-\lambda_n I_H)e_n\|\to 0. \] \end{theorem}

Every listed named item must be formalized with exactly the stated Lean name.
-/
```
