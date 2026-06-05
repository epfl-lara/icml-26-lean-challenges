# Formalization Blueprint: `algebraic-geometry/L3/alg_gen_L3_005`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Source Documents and Support Files Read

- `docs/source.tex`: primary LaTeX source.
- `.epflemma/workflow-state/formalization/docs-source/manifest.json`: preflight manifest; no bibliography files, labels, references, citations, PDFs, figures, or other support assets were listed.
- `.epflemma/workflow-state/formalization/docs-source/context.md`: workflow contract and extracted source inventory.
- `docs/instructions.md`, `docs/metadata.json`, and `docs/skeletons/README.md`.
- Candidate skeletons `docs/skeletons/Skeleton1.lean` through `Skeleton4.lean`.

## Source Inventory

- Source inventory entry: `line-17`; definition `IsProjective`; formalized by Lean declaration `IsProjective`.
- Source inventory entry: `line-29`; theorem `is_projective_proper`; formalized by Lean declaration `is_projective_proper`.
- Source inventory entry: `line-49`; theorem `projective_isProper`; formalized by Lean declaration `projective_isProper`.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the projective-space bridge construction, the source definition `IsProjective`, and theorem skeletons `is_projective_proper` and `projective_isProper`.
- `ShadowBench/Source.lean`: root project module; already imports `ShadowBench.Source.Main`, so project-level builds include the generated target module.

A single generated Lean file is sufficient for this short source. No split into `Basic`/`Theorems` files is planned before review.

## Import Plan

```lean
import Mathlib
```

The target Lean file currently uses exactly this direct import block. This matches `docs/instructions.md`; narrower direct imports may be substituted later by a refactor/proof pass if desired.

## Suggested Search Modules

These are search hints only, not additional required imports for the draft:

- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic`
- `Mathlib.RingTheory.MvPolynomial.Homogeneous`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.Over`
- `Mathlib.AlgebraicGeometry.AffineSpace` for analogous pullback-over-terminal construction style.

## Mathlib / Local Search Notes

- `AlgebraicGeometry.Scheme` is the Mathlib type of schemes; morphisms are category morphisms `X ⟶ S`.
- `AlgebraicGeometry.Proj` constructs the scheme `Proj 𝒜` for an `ℕ`-graded ring `𝒜`.
- `MvPolynomial.homogeneousSubmodule σ R` with local instance `MvPolynomial.gradedAlgebra` gives the standard grading by total degree on multivariable polynomials.
- `AlgebraicGeometry.IsClosedImmersion` is the closed-immersion morphism property for scheme morphisms.
- `AlgebraicGeometry.IsProper` is the proper morphism property; search found `AlgebraicGeometry.IsProper.stableUnderComposition` and instances expressing stability under composition/base change.
- The candidate skeletons use non-Mathlib types such as `[Scheme S]`, `ProjectiveSpace n S` as a type, `Proper`, `IsMonomorphism`, and `IsLocallyClosed`; those shapes are not adopted as statements. They served only as naming hints.

## Companion Construction Plan

### `ProjectiveSpaceModel`

- Planned Lean declarations: `AlgebraicGeometry.ProjectiveSpaceModel`
- Role: a bridge declaration for the integral model of projective `n`-space.
- Lean shape: for `n : ℕ`, define `Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift ℤ))`, with the standard homogeneous grading supplied by `MvPolynomial.gradedAlgebra`.
- Source coverage: realizes the source notation `\mathbf{P}^n` using `n + 1` homogeneous coordinates indexed by `Fin (n + 1)`.
- Scope changes: none intended; `ULift ℤ` is a universe-management representation of the base ring of integers.

### `ProjectiveSpace`

- Planned Lean declarations: `AlgebraicGeometry.ProjectiveSpace`
- Role: a bridge declaration for `\mathbf{P}^n_S`.
- Lean shape: the pullback of the base scheme `S` and `ProjectiveSpaceModel n` over the terminal object in `Scheme`.
- Source coverage: realizes base change of the integral projective space to an arbitrary base scheme `S`.
- Scope changes: none intended.

### `ProjectiveSpace.π`

- Planned Lean declarations: `AlgebraicGeometry.ProjectiveSpace.π`
- Role: structure morphism `\pi : \mathbf{P}^n_S \to S`.
- Lean shape: the first projection from the pullback defining `ProjectiveSpace n S`, also registered through `Scheme.CanonicallyOver`.
- Source coverage: covers every occurrence of the structure morphism `\pi` in the source.
- Scope changes: none intended.

## Source Statement Inventory

### line-17

- Source locator: `docs/source.tex`, lines 17--27.
- Source statement: Let `f : X \to S` be a morphism of schemes. We say that `f` is projective, in the Hartshorne or `H`-projective sense, if there exists an integer `n ≥ 0` and a closed immersion `i : X \hookrightarrow \mathbf{P}^n_S` over `S` such that `f = \pi \circ i`, where `\pi : \mathbf{P}^n_S \to S` is the structure morphism.
- Planned Lean declarations: `IsProjective`.
- Lean statement:
  ```lean
  ∃ (n : ℕ) (i : X ⟶ ProjectiveSpace n S),
    IsClosedImmersion i ∧ i ≫ ProjectiveSpace.π n S = f
  ```
- Skeleton candidate used: Skeletons 1--4 supplied the expected Lean name only. Their typeclass encoding `[Scheme S]`, function morphisms `X → S`, and predicates `Proper`, `IsMonomorphism`, `IsLocallyClosed` were rejected in favor of Mathlib's scheme category and morphism properties.
- Dependencies: `ProjectiveSpace`, `ProjectiveSpace.π`, `AlgebraicGeometry.IsClosedImmersion`, category composition.
- Formal statement review: the existential over `n : ℕ` represents the source side condition `n ≥ 0`; the morphism `i` targets `ProjectiveSpace n S`; `IsClosedImmersion i` records that `i` is a closed immersion; the equality `i ≫ ProjectiveSpace.π n S = f` records that `i` is over `S` and that `f = \pi \circ i` with Lean's left-to-right categorical composition.
- Source qualifiers:
  - Mathematical object class: schemes `X` and `S`, morphism `f : X ⟶ S`.
  - Quantifier order: for any morphism `f`, projectivity is a proposition asserting existence of data.
  - Parameter domain: `n` is a nonnegative integer, represented by `ℕ`.
  - Output codomain: proposition on scheme morphisms.
  - Equality/image condition: `f = π ∘ i`, represented as `i ≫ ProjectiveSpace.π n S = f`.
  - Side conditions: `i` is a closed immersion and targets projective space over `S`.
  - Follow-on claims: none in the definition.
- Lean coverage: all qualifiers are covered directly by the declaration and the companion construction declarations.
- Scope changes: none intended.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: this is a definition; no proof. Later proofs may unfold `IsProjective` to obtain witnesses `n`, `i`, closed immersion of `i`, and the factorization equality.

### line-29

- Source locator: `docs/source.tex`, theorem lines 29--35; proof lines 37--47.
- Source statement: Let `S` be a scheme and `n ≥ 0`. The structure morphism `π : \mathbf{P}^n_S \to S` is proper.
- Planned Lean declarations: `is_projective_proper`.
- Skeleton candidate used: Skeletons 1--4 supplied the theorem name only. Their statement was rewritten to Mathlib's `Scheme`, `ProjectiveSpace.π`, and `IsProper` vocabulary.
- Dependencies: `ProjectiveSpace.π`, `AlgebraicGeometry.IsProper`; likely proof dependencies include finite type, separatedness, universal closedness, valuative criterion, and properness of projective space.
- Formal statement review: the theorem quantifies first over the base scheme `S`, then over `n : ℕ`, matching the source's `S` and `n ≥ 0`. The target morphism is exactly the structure morphism defined by `ProjectiveSpace.π n S`. The conclusion uses Mathlib's scheme-morphism property `IsProper`.
- Source qualifiers:
  - Mathematical object class: base scheme `S`; projective space over `S`.
  - Quantifier order: `S` then `n`.
  - Parameter domain: nonnegative integer `n`, represented by `ℕ`.
  - Output codomain: proposition that a scheme morphism is proper.
  - Equality/image condition: none beyond identifying the morphism as the structure morphism `π`.
  - Side conditions: none beyond `S` being a scheme and `n ≥ 0`.
  - Follow-on claims: none.
- Lean coverage: covered by `ProjectiveSpace`, `ProjectiveSpace.π`, and `IsProper (ProjectiveSpace.π n S)`.
- Scope changes: none intended.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: The morphism `π : \mathbf{P}^n_S \to S` is of finite type, separated, and universally closed. It is of finite type because `\mathbf{P}^n_S` is obtained by gluing finitely many affine schemes of finite type over `S`. It is separated because projective space is separated over the base. To prove universal closedness, use the valuative criterion. Let `R` be a valuation ring with fraction field `K`. Given a morphism `Spec K \to \mathbf{P}^n_S` compatible with a morphism `Spec R \to S`, it corresponds to a point `[x_0 : \cdots : x_n]` with `x_i ∈ K` not all zero. After scaling, assume `x_i ∈ R` and at least one `x_i` is a unit. This determines a morphism `Spec R \to \mathbf{P}^n_S` extending the given one. Uniqueness follows from separatedness. Thus `π` satisfies the valuative criterion for properness and is proper.
- Source proof / prover notes: The intended proof is the standard properness of projective space over a base. Search first for any existing Mathlib theorem that `Proj` of a finitely generated graded algebra is proper, or for properness of projective space if it exists after import changes. If unavailable, unfold `IsProper` using `isProper_iff` and prove finite type, separatedness, and universal closedness. The source proof suggests the valuative criterion for universal closedness and the affine-open cover by finitely many standard opens `D_+(x_i)` for finite type.

### line-49

- Source locator: `docs/source.tex`, theorem lines 49--51; proof lines 53--60.
- Source statement: Every projective morphism is proper.
- Planned Lean declarations: `projective_isProper`.
- Skeleton candidate used: Skeletons 1--4 supplied the theorem name only. The final statement uses Mathlib scheme morphisms and the drafted `IsProjective` definition.
- Dependencies: `IsProjective`, `is_projective_proper`, `AlgebraicGeometry.IsClosedImmersion`, `AlgebraicGeometry.IsProper`, and properness stability under composition.
- Formal statement review: the theorem quantifies over any scheme morphism `f : X ⟶ S` and assumes it is projective in the source definition. The conclusion is Mathlib properness for the same morphism `f`.
- Source qualifiers:
  - Mathematical object class: arbitrary schemes `X`, `S` and morphism `f : X ⟶ S`.
  - Quantifier order: `X`, `S`, `f`, then projectivity hypothesis.
  - Parameter domain: all scheme morphisms.
  - Output codomain: proposition `IsProper f`.
  - Equality/image condition: inherited through `IsProjective f`, which supplies the factorization equality.
  - Side conditions: `f` is projective in the Hartshorne sense.
  - Follow-on claims: none.
- Lean coverage: covered directly by the theorem statement together with `IsProjective`.
- Scope changes: none intended.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: Let `f : X \to S` be projective. Then there exists a factorization `X \xrightarrow{i} \mathbf{P}^n_S \xrightarrow{\pi} S` where `i` is a closed immersion. Closed immersions are proper, hence `i` is proper. The morphism `π` is proper by the previous theorem. Since proper morphisms are stable under composition, it follows that `f = π \circ i` is proper.
- Source proof / prover notes: Unfold `IsProjective` to obtain `n`, `i`, `hi : IsClosedImmersion i`, and `hfac : i ≫ ProjectiveSpace.π n S = f`. Use a Mathlib instance or theorem that closed immersions are proper, then combine it with `is_projective_proper S n` via properness stability under composition (`IsProper.stableUnderComposition` or the appropriate typeclass instance). Finish by rewriting along `hfac`.

## Proof Handoff Queue

The theorem/lemma/example proof obligations introduced by the draft are:

1. `is_projective_proper`
2. `projective_isProper`

The construction and definition declarations `ProjectiveSpaceModel`, `ProjectiveSpace`, `ProjectiveSpace.π`, and `IsProjective` are implemented without `sorry`; they are not theorem-queue proof stubs.

## Review Gate

- [x] Independent statement/source review accepted by formalization PASS and 2026-06-05 audit.
- [ ] After review approval, run the suggested command below to start proof search if the user wants proofs completed.

Suggested next command after review approval:

```text
/prove ShadowBench/Source/Main.lean
```
