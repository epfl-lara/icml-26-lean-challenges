# ShadowBench Instructions: `geometry/L2/geo_gen_L2_002`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import imports: import Mathlib.Geometry.Manifold.MFDeriv.Tangent
```

## Expected Declaration Names

- `isMIntegralCurveAt_iff'`

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

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
