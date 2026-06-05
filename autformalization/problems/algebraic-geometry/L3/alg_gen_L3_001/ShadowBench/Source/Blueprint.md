# Formalization Blueprint: `algebraic-geometry/L3/alg_gen_L3_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Source Statement Inventory

### line-17

- Source kind: lemma.
- Source locator: `docs/source.tex`, statement lines 17-19, proof lines 19-55.
- Source statement: If `G` is a group scheme over an algebraically closed field `k` that is reduced and locally of finite type, then `G` is smooth over `k`.
- Planned Lean declarations: `smooth_of_grpObj_of_isAlgClosed` in `ShadowBench/Source/Main.lean`.
- Dependencies:
  - `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec` for schemes and the base `Spec (.of K)`.
  - `CategoryTheory.Over.mk` and `CategoryTheory.GrpObj` to represent a group scheme over `Spec K` as a group object in the over-category.
  - `AlgebraicGeometry.IsReduced` for reducedness of the total scheme.
  - `AlgebraicGeometry.LocallyOfFiniteType` for the source finite-type hypothesis.
  - `AlgebraicGeometry.Smooth` for the conclusion.
- Candidate skeletons used: Skeletons 1-3 preserve the informal name and English statement but use non-Mathlib typeclass placeholders such as `[Scheme G]`, `[Algebra k G]`, `[ContinuousGroup G]`, `[IsLocallyFiniteType G k]`, and `IsSmooth G k`. Skeleton4 duplicates the same shape and has an extra malformed `:= by sorry`. The final statement keeps the required name but uses Mathlib's scheme/morphism encoding instead of the skeleton placeholders.
- Formal statement review:
  - Source quantifies over an algebraically closed field `k`; Lean uses `{K : Type u} [Field K] [IsAlgClosed K]`.
  - Source quantifies over a group scheme `G` over `k`; Lean uses `{G : Scheme}` and a structure morphism `f : G ⟶ Spec (.of K)` together with `[GrpObj (Over.mk f)]`.
  - Source assumes `G` is reduced; Lean uses `[IsReduced G]`.
  - Source assumes the structure morphism is locally of finite type; Lean uses `[LocallyOfFiniteType f]`.
  - Source concludes smoothness over `k`; Lean concludes `Smooth f`.
- Source qualifiers:
  - Mathematical object class: group scheme over an algebraically closed field.
  - Quantifier order: field, field structure and algebraic closedness, scheme, structure morphism to `Spec K`, then side-condition typeclasses.
  - Parameter domain: schemes over `Spec (.of K)`.
  - Output codomain/conclusion: proposition `Smooth f` for the structure morphism.
  - Side conditions: `Field K`, `IsAlgClosed K`, `LocallyOfFiniteType f`, `IsReduced G`, and `GrpObj (Over.mk f)`.
  - Equality/image conditions and follow-on claims: none in the lemma statement; the proof uses smooth-locus invariance under group translations.
- Lean coverage: the planned Lean declaration covers each source qualifier directly using Mathlib's native morphism-property and group-object encodings. The group-scheme representation bridge is the `[GrpObj (Over.mk f)]` typeclass.
- Scope changes: none intended. The source proof invokes local finite presentation for the smooth locus; because the source assumes locally finite type over a field, the prover may need the standard locally-Noetherian bridge from locally finite type to locally finite presentation, but the statement itself keeps the source's locally-finite-type hypothesis.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text:

  Let \(U \subseteq G\) be the smooth locus of \(f\). Since smoothness is an open condition for morphisms locally of finite presentation, \(U\) is an open subset of \(G\). We must show that \(U=G\).

  Suppose for contradiction that \(U \neq G\). Then \(G \setminus U\) is a nonempty closed subset of \(G\).

  Because \(f\) is locally of finite presentation over the field \(k\), the scheme \(G\) is Jacobson. On the other hand, since \(k\) is algebraically closed, hence perfect, and \(G\) is reduced, the smooth locus \(U\) is dense in \(G\). Therefore both \(G \setminus U\) and \(U\) contain closed points. Choose closed points
  \[
  x \in G \setminus U
  \qquad\text{and}\qquad
  y \in U.
  \]

  Since \(k\) is algebraically closed, every closed point of \(G\) is a \(k\)-rational point. Thus \(x\) and \(y\) arise from morphisms
  \[
  x,y : \mathrm{Spec} k \to G
  \]
  over \(\mathrm{Spec} k\).

  Now use the group structure on \(G\). For every \(k\)-point \(a : \mathrm{Spec} K \to G\), right translation by \(a'\) defines an automorphism of the group scheme \(G\) over \(\mathrm{Spec} k\). In particular, right translation by \(x\) and by \(y\) are automorphisms of \(G\), so
  \[
  \alpha := R_{y} \circ R_{x}^{-1}
  \]
  is an automorphism of \(G\) over \(\mathrm{Spec} k\). By construction, \(\alpha\) sends \(x\) to \(y\); hence, on underlying topological points,
  \[
  \alpha(x)=y.
  \]

  Because \(\alpha\) is an isomorphism over \(\mathrm{Spec} k\), it preserves the smooth locus:
  \[
  \alpha^{-1}(U)=U.
  \]
  Since \(y\in U\), it follows that \(x \in U\), contradicting the choice of \(x \in G \setminus U\).

  This contradiction shows that \(G \setminus U\) is empty. Therefore \(U=G\), so \(f\) is smooth.

- Prover notes:
  - Mathlib search found an existing theorem `AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed` in `Mathlib.AlgebraicGeometry.Group.Smooth`; it proves the locally-finite-presentation version using exactly the smooth-locus, closed-points, and right-translation argument from the source.
  - The drafted ShadowBench statement keeps the source hypothesis `[LocallyOfFiniteType f]`. A later proof can either reproduce the Mathlib proof, or import/use the Mathlib theorem after deriving `[LocallyOfFinitePresentation f]` from `[LocallyOfFiniteType f]` over the locally Noetherian base `Spec (.of K)`.
  - Useful proof ingredients from search: `LocallyOfFiniteType.jacobsonSpace`, `Scheme.Hom.smoothLocus`, `Scheme.Hom.smoothLocus_eq_top_iff`, `Scheme.Hom.dense_smoothLocus_of_perfectField`, `nonempty_inter_closedPoints`, `pointEquivClosedPoint`, `GrpObj.mulRight`, and `Scheme.Hom.preimage_smoothLocus_eq`.

## Import Plan

```lean
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.Monoidal.Grp_
```

These are the direct imports in `ShadowBench/Source/Main.lean`.

## Suggested Search Modules

- `Mathlib.AlgebraicGeometry.Group.Smooth` — contains `AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed`, the Mathlib proof of the finite-presentation version.
- `Mathlib.AlgebraicGeometry.Noetherian` — search here for the bridge from locally finite type to locally finite presentation over a locally Noetherian base.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation` — source of the finite-type and finite-presentation morphism properties.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: single source-backed declaration for `line-17`.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so the project target `ShadowBench` covers the generated source file.

## Required Names

- `smooth_of_grpObj_of_isAlgClosed`

## Verification Plan

- Draft readiness: run `lean_inspect` on `ShadowBench/Source/Main.lean` after editing.
- Project gate: run `lean_verify(mode=project)` after the generated file and root imports are in place.
- Proof-ready checklist: [ ] independent statement/source verification completed for `line-17`. This drafting pass intentionally leaves this unchecked.
