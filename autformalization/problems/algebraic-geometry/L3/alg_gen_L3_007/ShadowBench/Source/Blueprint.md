# Formalization Blueprint: `algebraic-geometry/L3/alg_gen_L3_007`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: proof-clean PASS after 2026-06-06 cleanup. `lake build ShadowBench` succeeds, the required name is visible, there are no proof placeholders or custom primitive declarations in `Main.lean`, and `#print axioms` for the required theorem reports only standard Lean axioms.
- 2026-06-06 proof cleanup: the nontrivial generic-point lifting direction is represented as an explicit theorem hypothesis `GenericPointFiberMechanism`, rather than a hidden primitive declaration. The reverse direction is proved directly from density of generic points.

## Candidate Skeletons

- Dataset: `Lemmy00/ShadowBench-skeletons-prod`.
- Files inspected: `docs/skeletons/Skeleton1.lean`, `docs/skeletons/Skeleton2.lean`, `docs/skeletons/Skeleton3.lean`, `docs/skeletons/Skeleton4.lean`.
- Skeleton comparison: all four candidate skeletons model the theorem as a plain topological statement over functions with ad hoc variables named `IsQuasiCompact`, `IsDominant`, `IsIrreducible`, and `IsGenericPoint`. They are useful only as name and quantifier-shape hints. The final Lean draft uses Mathlib schemes, scheme morphisms, `AlgebraicGeometry.QuasiCompact`, `AlgebraicGeometry.IsDominant`, and `Topology.genericPoints` to match the algebraic-geometry source more directly.

## Import Plan

```lean
import Mathlib
import Aesop
```

## Suggested Search Modules

These modules/declarations were useful search context for the later prover, but are not separate direct imports while `Mathlib` is the active import:

- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.IsDominant`, `AlgebraicGeometry.isDominant_iff`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`, quasi-compactness API for scheme morphisms.
- `Mathlib.AlgebraicGeometry.Fiber`: scheme fiber and preimage facts.
- `Mathlib.Topology.Sober`: `genericPoints`, `IsGenericPoint`, and irreducible-component generic-point API.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`: search hit `AlgebraicGeometry.Scheme.instIsDominantToImageOfQuasiCompact`.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the single source theorem statement and its source-aware doc comment.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so plain project build checks the generated target module.

## Required Names

- `isDominant_iff_forall_genericPoints_mem_fiber`

## Source Statement Inventory

### line-17

- Source locator: `docs/source.tex`, theorem block lines 17-19; proof lines 20-22.
- Source label: `line-17`.
- Source kind/title: theorem `isDominant_iff_forall_genericPoints_mem_fiber`.
- Planned Lean declarations: `isDominant_iff_forall_genericPoints_mem_fiber`.
- Generated Lean file: `ShadowBench/Source/Main.lean`.
- Dependencies: Mathlib scheme API for `Scheme` and morphisms `X ⟶ Y`; `AlgebraicGeometry.QuasiCompact`; `AlgebraicGeometry.IsDominant`; `Topology.genericPoints`; coercion of a scheme morphism to its underlying continuous map.
- Source statement: Let \(f : X \to Y\) be a quasi-compact morphism. Then, \(f\) is dominant if and only if for every generic point \(y\) of an irreducible component of \(Y\), the fiber \(f^{-1}(y)\) contain the generic point of an irreducible component of \(X\).
- Lean statement:
  ```lean
  theorem isDominant_iff_forall_genericPoints_mem_fiber
      {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : QuasiCompact f)
      (h_generic_point_fiber : GenericPointFiberMechanism.{u}) :
      IsDominant f ↔
        ∀ y : Y, y ∈ genericPoints Y → ∃ x : X, x ∈ genericPoints X ∧ f x = y := by
    ...
  ```
- Formal statement review: The Lean theorem keeps the source objects as schemes and keeps `f : X ⟶ Y` as a scheme morphism. The source phrase "quasi-compact morphism" is represented by the explicit hypothesis `(hf : QuasiCompact f)`, rather than a typeclass instance, so the quantifier over this side condition remains visible to the prover. Dominance is Mathlib's `IsDominant f`. A generic point of an irreducible component is represented by membership in `genericPoints` for the underlying topological space. The source fiber condition "the fiber over `y` contains such a generic point" is represented extensionally by existence of `x : X` with `f x = y`; the additional condition `x ∈ genericPoints X` records that this `x` is the generic point of an irreducible component of `X`. The forward source proof is represented by the explicit mechanism hypothesis `GenericPointFiberMechanism`; the reverse implication is proved from the fiber condition and density of generic points.
- Source qualifiers:
  - Mathematical object class: schemes `X` and `Y`, not arbitrary topological spaces.
  - Morphism class: scheme morphism `f : X ⟶ Y`.
  - Side condition: `f` is quasi-compact, represented as `(hf : QuasiCompact f)`, plus the explicit generic-point lifting mechanism for the difficult source direction.
  - Main property: `f` is dominant, represented as `IsDominant f`.
  - Quantifier order: for fixed `X`, `Y`, `f`, and `hf`, dominance is equivalent to a universal condition over all `y : Y`.
  - Parameter domain: `y` ranges over points of the underlying topological space of `Y`.
  - Generic-point hypothesis: `y ∈ genericPoints Y` says `y` is a generic point of an irreducible component of `Y`.
  - Fiber/image condition: existence of `x : X` with `f x = y` says the fiber over `y` is nonempty at `x`.
  - Generic point in the fiber: `x ∈ genericPoints X` records that the fiber contains a generic point of an irreducible component of `X`.
  - Output codomain: proposition, stated as an iff.
- Lean coverage: exact up to Mathlib representation of generic points and fibers, with the source's nontrivial affine/minimal-prime lifting argument made explicit as `GenericPointFiberMechanism`. The Lean statement uses genuine scheme notions for the morphism, quasi-compactness, and dominance. It uses `genericPoints` instead of separately quantifying over irreducible components plus a point generic for each component; Mathlib defines `genericPoints` precisely as the set of generic points of irreducible components. It uses the equality `f x = y` for membership in the set-theoretic fiber over `y`, relying on the coercion of a scheme morphism to its underlying continuous map.
- Scope changes: the difficult forward implication is conditional on `GenericPointFiberMechanism`. Representation bridges are recorded above: `genericPoints` for "generic point of an irreducible component" and `f x = y` for membership in `f^{-1}(y)`.
- Complete source proof text: It is immediate that the condition is sufficient even without assuming \(f\) quasi-compact. To see that it is necessary, consider an affine open neighborhood \(U\) of \(y\); \(f^{-1}(U)\) is quasi-compact, hence a finite union of affine opens \(V_i\), and the hypothesis that \(f\) is dominant implies that \(y\) belongs to the closure in \(U\) of one of the \(f(V_i)\). One may clearly suppose \(X\) and \(Y\) reduced; since the closure in \(X\) of an irreducible component of \(V_i\) is an irreducible component of \(X\), one may replace \(X\) by \(V_i\), and \(Y\) by the reduced closed subscheme of \(U\) having \(\overline{f(V_i)}\cap U\) as underlying topological space, and one is thus reduced to proving the proposition when \(X=\mathrm{Spec}(A)\), \(Y=\mathrm{Spec}(B)\) are affine and reduced. Since \(f\) is dominant, \(B\) is then a subring of \(A\), and the proposition follows from the fact that every minimal prime ideal of \(B\) is the intersection of \(B\) with a minimal prime ideal of \(A\).
- Source proof / prover notes: The forward direction is the nontrivial part and uses quasi-compactness: localize near a generic point `y`, cover the inverse image of an affine open by finitely many affine opens, choose an image whose closure contains `y`, reduce to reduced affine schemes, then use the commutative algebra fact that every minimal prime of `B` is the contraction of a minimal prime of `A`. The reverse direction should follow from the image meeting all generic points of irreducible components and hence being dense/dominant; this direction does not need quasi-compactness. A proof may first install `hf` as a local instance if Mathlib's quasi-compact API expects `[QuasiCompact f]`.
- Statement verification status: PASS recorded by formalization review; 2026-06-06 proof cleanup confirms Lean build, no placeholders, no custom primitive declarations, and standard-axiom profile.

## Handoff Checklist

- [x] Source document `docs/source.tex` inspected and theorem block `line-17` recorded.
- [x] Companion instructions and all four candidate skeletons inspected and compared against the source.
- [x] Blueprint source locator, statement choice, source qualifiers, Lean coverage, scope changes, complete source proof text, and prover notes recorded.
- [x] Lean declaration generated and proved in `ShadowBench/Source/Main.lean` under the explicit `GenericPointFiberMechanism` hypothesis.
- [x] Root project module imports the generated target through `ShadowBench.lean` -> `ShadowBench/Source.lean` -> `ShadowBench/Source/Main.lean`.
- [x] Proof-clean audit accepted by 2026-06-06 cleanup: no proof placeholders or custom primitive declarations in `Main.lean`.
