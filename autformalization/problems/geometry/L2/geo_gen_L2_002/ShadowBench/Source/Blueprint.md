# Formalization Blueprint: `geometry/L2/geo_gen_L2_002`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: scaffold created; replace pending entries during formalization.

## Import Plan

```lean
import imports: import Mathlib.Geometry.Manifold.MFDeriv.Tangent
```

## Required Names

- `isMIntegralCurveAt_iff'`

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
open scoped Manifold Topology
open Set

/-
Formalize in Lean the Lemma (isMIntegralCurveAt_iff') from Text.

The lemma must be named `isMIntegralCurveAt_iff'`.
   Matched text (candidate 0, theorem, label=isMIntegralCurveAt_iff'): \begin{theorem}[isMIntegralCurveAt_iff'] 다양체 $M$과 $M$상의 벡터장 $v$이 주어졌다고 하자. $\Gamma : ℝ → M$가
                                                                       $t_o$에서 $v$의 적분곡선인 것은 $\Gamma$가 $t_o$의 어떤 열린근방 $U$에서 $v$의 적분곡선인 것과 동치이다. \end{theorem}
-/
```
