# Formalization Blueprint: `algebraic-geometry/L3/alg_gen_L3_009`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Import Plan

```lean
import Mathlib
```

The target file currently uses exactly this direct Lean import. Search-specific modules are listed below as prover hints only, not as mandatory imports.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the source-backed declaration `FiniteType` and theorem skeleton `surjective_iff_surjective_on_algClosed_points_of_finiteType`.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so plain project builds cover the generated target module.

No file split is planned for this small source document.

## Required Names

- `FiniteType`
- `surjective_iff_surjective_on_algClosed_points_of_finiteType`

## Candidate Skeleton Review

- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, `Skeleton3.lean`, and `Skeleton4.lean` were read as requested.
- The skeletons preserve the expected names and informal intent, but they encode schemes as ordinary types with a nonexistent `[Scheme X]` typeclass, use undefined placeholders such as `StructureSheaf.X`, `IsAffine`, `FiniteAlgebra`, `XPoints`, `YPoints`, and malformed `where` blocks, and therefore are not adopted directly.
- The final draft instead uses Mathlib's `AlgebraicGeometry.Scheme` objects, morphisms `X ⟶ Y`, `Spec (.of Ω) ⟶ X` for Ω-points, and Mathlib morphism properties `AlgebraicGeometry.QuasiCompact` and `AlgebraicGeometry.LocallyOfFiniteType` to represent the finite-type definition.

## Source Inventory

| Source inventory entry | Kind | Source lines | Planned Lean declaration |
| --- | --- | --- | --- |
| `line-17` | definition | `docs/source.tex` lines 17-28 | `FiniteType` |
| `line-30` | theorem | `docs/source.tex` lines 30-33; proof lines 33-54 | `surjective_iff_surjective_on_algClosed_points_of_finiteType` |

```json
{
  "source_inventory": [
    {
      "label": "line-17",
      "kind": "definition",
      "source_locator": "docs/source.tex:17-28",
      "planned_lean_declaration": "FiniteType"
    },
    {
      "label": "line-30",
      "kind": "theorem",
      "source_locator": "docs/source.tex:30-33",
      "proof_locator": "docs/source.tex:33-54",
      "planned_lean_declaration": "surjective_iff_surjective_on_algClosed_points_of_finiteType"
    }
  ]
}
```

- `line-17` (definition, lines 17-28) - `FiniteType`
  - Planned Lean declaration: `FiniteType`
  - Source locator: `docs/source.tex:line-17`
- `line-30` (theorem, lines 30-33; proof lines 33-54) - `surjective_iff_surjective_on_algClosed_points_of_finiteType`
  - Planned Lean declaration: `surjective_iff_surjective_on_algClosed_points_of_finiteType`
  - Source locator: `docs/source.tex:line-30`

## Statement Inventory

- Source inventory entry: `line-17`
  - Planned Lean declaration: `FiniteType`
  - Source locator: `docs/source.tex`, lines 17-28
  - Kind: definition
- Source inventory entry: `line-30`
  - Planned Lean declaration: `surjective_iff_surjective_on_algClosed_points_of_finiteType`
  - Source locator: `docs/source.tex`, lines 30-33; proof lines 33-54
  - Kind: theorem
- Source inventory entry `line-17`: planned Lean declaration `FiniteType`.
- Source inventory entry `line-30`: planned Lean declaration `surjective_iff_surjective_on_algClosed_points_of_finiteType`.
- source inventory entry `line-17`: machine-readable duplicate for handoff verification.
- source inventory entry `line-30`: machine-readable duplicate for handoff verification.

### Source inventory entry `line-17`: Definition `FiniteType`

- Planned Lean declaration: `class FiniteType {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) : Prop` extending `AlgebraicGeometry.QuasiCompact f` and `AlgebraicGeometry.LocallyOfFiniteType f`.
- Source label: `line-17`.
- Source inventory label: `line-17`.
- Source locator: `line-17` (`docs/source.tex`, lines 17-28).
- Source statement: A morphism `f : X → Y` is of finite type if `Y` is the union of affine open subsets `V_α` such that each inverse image `f⁻¹(V_α)` is a finite union of affine open subsets `U_{α i}` and each ring `Γ(U_{α i}, O_X)` is a finitely generated / finite-type `Γ(V_α, O_Y)`-algebra. Then `X` is also called a scheme of finite type over `Y`.
- Skeleton candidate used: none directly; all skeletons were used only as naming/prose hints and rejected for the reasons in `Candidate Skeleton Review`.
- Dependencies: `AlgebraicGeometry.Scheme`, `CategoryTheory` morphism notation, `AlgebraicGeometry.QuasiCompact`, `AlgebraicGeometry.LocallyOfFiniteType`. These are available through `import Mathlib`; the direct module sources found by search are `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` and `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- Formal statement review: Mathlib's finite-type morphism file states that a morphism of schemes is finite type when it is both locally of finite type and quasi-compact. `LocallyOfFiniteType` records finite-type behavior of the induced maps on coordinate rings over affine opens; `QuasiCompact` supplies the finite affine subcover / finite-union content for preimages of affine opens through theorems such as `quasiCompact_iff_forall_isAffineOpen` and `isCompact_iff_finite_and_eq_biUnion_affineOpens`.
- Source qualifiers:
  - Mathematical object class: morphisms of schemes `f : X ⟶ Y`.
  - Quantifier order: fixed schemes `X`, `Y`, then a fixed morphism `f`.
  - Parameter domain/codomain: source scheme `X`, target scheme `Y`.
  - Cover condition: affine open cover of `Y`; inverse images covered by finitely many affine opens in `X`.
  - Algebra condition: coordinate rings on the affine pieces are finite-type algebras over the coordinate rings of the target affine opens.
  - Follow-on terminology: a `Y`-scheme of finite type is represented by the same predicate on its structure morphism.
- Lean coverage:
  - `FiniteType f` is a class bundling `QuasiCompact f` and `LocallyOfFiniteType f`.
  - The affine-open finite-cover wording is covered by the cited Mathlib bridge between quasi-compactness and finite affine covers, together with the local finite-type ring-hom property.
  - The terminology “scheme of finite type over `Y`” is represented by applying `FiniteType` to the relevant structure morphism into `Y`.
- Scope changes:
  - Representation bridge: the raw cover data from the source is not stored as fields; it is represented by Mathlib's equivalent `QuasiCompact ∧ LocallyOfFiniteType` formulation.
  - Universe scope: the Lean declaration uses schemes and fields in one universe level `u`.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: this is a definition. No proof obligation is generated; reviewers should check that the Mathlib bridge is acceptable coverage for the explicit affine-cover definition.

### Source inventory entry `line-30`: Theorem `surjective_iff_surjective_on_algClosed_points_of_finiteType`

- Planned Lean declaration: `theorem surjective_iff_surjective_on_algClosed_points_of_finiteType {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [FiniteType f] : Function.Surjective f ↔ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω], Function.Surjective (fun (p : AlgebraicGeometry.Spec (.of Ω) ⟶ X) => p ≫ f)`.
- Source label: `line-30`.
- Source inventory label: `line-30`.
- Source locator: `line-30` (`docs/source.tex`, theorem lines 30-33; proof lines 33-54).
- Source statement: Let `f : X → Y` be a morphism of finite type. In order that `f` be surjective, it is necessary and sufficient that, for every algebraically closed field `Ω`, the map `X(Ω) → Y(Ω)` corresponding to `f` be surjective.
- Complete source proof text:
  ```tex
  The condition is sufficient, as one sees by considering, for every \(y\in Y\), an algebraically closed extension \(\Omega\) of \(k(y)\), and the commutative diagram
  \[
  \begin{array}{ccc}
  & \mathrm{Spec}(\Omega) & \\
  & \swarrow \quad \searrow & \\
  X & \xrightarrow{\ f\ } & Y .
  \end{array}
  \]

  Conversely, suppose \(f\) is surjective, and let \(g:\{\xi\}=\mathrm{Spec}(\Omega)\to Y\) be a morphism, where \(\Omega\) is an algebraically closed field. Consider the Cartesian diagram
  \[
  \begin{array}{ccc}
  X_\Omega & \longrightarrow & X \\
  f_\Omega \downarrow  & & \downarrow f \\
  \mathrm{Spec}(\Omega) & \xrightarrow{\ g\ } & Y .
  \end{array}
  \]
  It is therefore enough to show that there exists in \(X_\Omega\) a point rational over \(\Omega\). Since \(f\) is surjective, \(X_\Omega\) is not empty, and since \(f\) is of finite type, the same is true of \(f_\Omega\). Hence \(X_\Omega\) contains a nonempty affine open subset \(Z\) such that \(\Gamma(Z,\mathcal O_{X_\Omega})\) is a nonzero algebra of finite type over \(\Omega\). By Hilbert's Nullstellensatz, there exists an \(\Omega\)-homomorphism \(
  \Gamma(Z,\mathcal O_{X_\Omega})\to \Omega\), hence a section of \(X_\Omega\) over \(\mathrm{Spec}(\Omega)\).
  ```
- Skeleton candidate used: none directly. The final theorem keeps the required name and iff structure suggested by the skeletons, but replaces their undefined `XPoints`, `YPoints`, and `fOnPoints` with the standard representation of Ω-points as morphisms `Spec (.of Ω) ⟶ X` and the induced map as postcomposition with `f`.
- Dependencies: `FiniteType`, `Function.Surjective`, `IsAlgClosed`, `AlgebraicGeometry.Spec`, `CommRingCat.of`, category composition `≫`, and later proof facts around `Scheme.SpecToEquivOfField`, `Scheme.fromSpecResidueField`, base change/pullbacks, and the Nullstellensatz / algebraically closed field homomorphism existence.
- Formal statement review: The Lean statement quantifies first over schemes `X`, `Y`, then the morphism `f`, assumes `[FiniteType f]`, and states the exact iff between topological surjectivity of the scheme morphism and surjectivity on Ω-points for every algebraically closed field `Ω`. The map on Ω-points is the source “map corresponding to `f`”, formalized as `p ↦ p ≫ f`.
- Source qualifiers:
  - Mathematical object class: morphisms of schemes.
  - Quantifier order: schemes `X`, `Y`; finite-type morphism `f`; then all algebraically closed fields `Ω`.
  - Parameter domain/codomain: `f : X ⟶ Y`; Ω-points are morphisms `Spec Ω ⟶ X` and `Spec Ω ⟶ Y`.
  - Equality/image condition: `Function.Surjective f` iff each induced map on Ω-points is surjective.
  - Side conditions: `Ω` is a field and algebraically closed; `f` is finite type. No separatedness, reducedness, noetherianity, or base-field assumption appears in the source.
  - Follow-on claims: the proof uses base change to `Spec Ω`, existence of rational points on nonempty finite-type schemes over algebraically closed fields, and Nullstellensatz.
- Lean coverage:
  - Surjectivity of the morphism is represented by `Function.Surjective f`, using Mathlib's coercion of scheme morphisms to their underlying maps on topological points.
  - `X(Ω)` and `Y(Ω)` are represented exactly as hom-types `Spec (.of Ω) ⟶ X` and `Spec (.of Ω) ⟶ Y`.
  - The induced map corresponding to `f` is postcomposition by `f`.
  - The finite-type hypothesis is `FiniteType f`, whose representation bridge is recorded under `line-17`.
- Scope changes:
  - Notation change only: the source notation `X(Ω)` is replaced by `Spec (.of Ω) ⟶ X`.
  - Universe scope: `Ω : Type u` is used so that `Spec (.of Ω)` lives in the same scheme universe as `X` and `Y`.
  - The proof-critical finite-type existence of rational points is not split into a separate Lean theorem in this draft; it remains part of the theorem proof obligation for the later prover queue.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: For the forward direction, take an arbitrary Ω-point `g : Spec Ω ⟶ Y`, form the pullback `X ×_Y Spec Ω`, use surjectivity of `f` to get the fiber product nonempty and finite type over `Ω`, then use an affine open and Nullstellensatz to produce an Ω-rational point, equivalently a lift `Spec Ω ⟶ X`. For the reverse direction, for each point `y : Y`, use an algebraically closed extension of the residue field `κ(y)` and the corresponding Ω-point of `Y`; surjectivity on Ω-points gives a lift to `X`, whose image maps to `y`.

## Suggested Search Modules

These are search hints for the later prover and should not be added to `Main.lean` unless Lean verification shows a direct import is needed:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.AlgebraicGeometry.ResidueField`
- `Mathlib.AlgebraicGeometry.AlgClosed.Basic`
- `Mathlib.AlgebraicGeometry.Limits`

## Search Performed

- `lean_search`: “Scheme morphism finite type” found `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.Scheme.Hom.finiteType_appLE`, and related finite-type ring-hom facts.
- `lean_search`: “finite type morphism scheme quasi compact locally finite type” confirmed Mathlib's module description: finite type morphisms are locally finite type plus quasi-compact.
- `lean_search`: “AlgebraicallyClosed Spec Ω-points scheme morphism” found `AlgebraicGeometry.pointEquivClosedPoint`, `AlgebraicGeometry.pointOfClosedPoint`, and `AlgebraicGeometry.Scheme.Spec`.
- `lean_search`: “X(Ω) scheme points Spec Ω morphism” found `AlgebraicGeometry.Scheme.SpecToEquivOfField` and residue-field maps useful for translating Ω-points.

## Review Gate

- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [ ] After approval, start the proof phase explicitly with `/prove ShadowBench/Source/Main.lean`.
