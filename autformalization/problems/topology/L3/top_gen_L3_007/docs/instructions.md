# ShadowBench Instructions: `topology/L3/top_gen_L3_007`

## Source

- Formalize `docs/source.tex`.
- Put the final Lean snippet in `ShadowBench/Source/Main.lean`.
- Keep `ShadowBench/Source/Blueprint.md` synchronized with statement choices, source coverage, and proof notes.

## Allowed Imports

Use these imports as the starting import block. Add imports only when Lean verification proves one is missing, and record the change in the blueprint.

```lean
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.UnitInterval
```

## Expected Declaration Names

- `exists_path_lifts`
- `eq_liftPath_iff`
- `eq_liftPath_iff'`

## Formalization Rules

```text
open Topology unitInterval

/-
Formalize in Lean the following named items from Text.

1. Theorem (exists_path_lifts)
   The theorem must be named `exists_path_lifts`.
   Matched text (candidate 0, theorem, label=Existence of a path lifting): \begin{theorem}[Existence of a path lifting] Let \[ p:E\to X \] be a covering map. Let \[
                                                                           \gamma:I\to X \] be a path, and let \(e\in E\) be such that \[ \gamma(0)=p(e). \] Then there
                                                                           exists a path \[ \Gamma:I\to E \] such that \[ p\circ \Gamma=\gamma \qquad\text{and}\qquad
                                                                           \Gamma(0)=e. \] \end{theorem}
2. Lemma (eq_liftPath_iff)
   The lemma must be named `eq_liftPath_iff`.
   Matched text (candidate 1, lemma, label=Uniqueness of lifts): \begin{lemma}[Uniqueness of lifts] Let \[ f:E\to X \] be a covering map, and let \(A\) be a
                                                                 preconnected topological space. Suppose \[ g_1,g_2:A\to E \] are continuous maps such that
                                                                 \[ f\circ g_1=f\circ g_2. \] If there exists a point \(a\in A\) such that \[ g_1(a)=g_2(a),
                                                                 \] then \[ g_1=g_2. \] \end{lemma}
3. Lemma (eq_liftPath_iff')
   The lemma must be named `eq_liftPath_iff'`.
   Matched text (candidate 2, theorem, label=eq_liftPath_iff'): \begin{theorem}[eq_liftPath_iff'] Let \[ p:E\to X \] be a covering map, let \[ \gamma:I\to X
                                                                \] be a path, and let \(e\in E\) satisfy \[ \gamma(0)=p(e). \] Let \[
                                                                \widetilde{\gamma}:I\to E \] be the chosen lift of \(\gamma\) starting at \(e\), so that \[
                                                                p\circ \widetilde{\gamma}=\gamma \qquad\text{and}\qquad \widetilde{\gamma}(0)=e. \] Then for
                                                                any map \(\Gamma:I\to E\), \[ \Gamma=\widetilde{\gamma} \] if and only…

Every listed named item must be formalized with exactly the stated Lean name.
-/
```

## Workflow Rules

- Every generated Lean file must begin with all imports before comments, namespace commands, or declarations.
- Preserve quantifier order, domains, codomains, side conditions, and named declarations from the source.
- Do not silently weaken a theorem to make the proof easier. Record ambiguity or intentional scope changes in the blueprint.
- During drafting, `by sorry` is acceptable only as a temporary handoff to the prover loop.
- Before export, `ShadowBench/Source/Main.lean` must verify with no `sorry`, `admit`, or open goals in the submitted declarations.
