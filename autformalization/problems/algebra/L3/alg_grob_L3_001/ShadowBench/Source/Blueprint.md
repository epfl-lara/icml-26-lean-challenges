# Formalization Blueprint: `algebra/L3/alg_grob_L3_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Source Documents Read

- `docs/source.tex` inspected with `formalization_document_inspect`; theorem-like blocks detected at `line-17`, `line-23`, and `line-35`.
- `.epflemma/workflow-state/formalization/docs-source/context.md` read for the document formalization contract.
- `.epflemma/workflow-state/formalization/docs-source/manifest.json` read; no bibliography files, citations, refs, PDFs, or local figure/support assets were listed.
- `docs/instructions.md` read; required names are `IsFinite`, `IsProjective`, and `finite_implies_projective`.
- Candidate skeletons `docs/skeletons/Skeleton1.lean` through `Skeleton4.lean` read and compared against the source.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: single-file draft containing the source-backed definitions and theorem skeleton.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so the root project target covers the generated file.

No split is currently justified: the source has two definitions and one theorem, and a single file keeps the representation bridge visible to reviewers and provers.

## Import Plan

```lean
import Mathlib.AlgebraicGeometry.Morphisms.Proper
```

This direct Mathlib import supplies the scheme category, finite morphism predicate, closed immersion predicate, and the properness facts mentioned by the source proof. It replaces the scaffold imports from the candidate skeletons, which were not direct dependencies for the algebraic-geometry statements.

## Suggested Search Modules

These are search/proof hints only, not required direct imports in the current Lean draft:

- `Mathlib.AlgebraicGeometry.Morphisms.Finite`
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper`

## Search Notes

Local/Mathlib search found:

- `AlgebraicGeometry.IsFinite` in `Mathlib.AlgebraicGeometry.Morphisms.Finite`, matching the source definition of finite morphisms as affine morphisms with finite induced algebra maps on affine opens.
- `AlgebraicGeometry.isFinite_iff` and `AlgebraicGeometry.Scheme.Hom.finite_app`, useful for unfolding the affine-local finite algebra condition.
- `AlgebraicGeometry.IsClosedImmersion` in `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, matching the closed immersion clause in projectivity.
- `AlgebraicGeometry.IsProper.instOfIsFinite` / `AlgebraicGeometry.instIsProperOfIsFinite`, matching the proof's use that finite morphisms are proper.
- No canonical Mathlib declaration for projective morphisms of schemes or projective space over an arbitrary scheme was found in this project. The draft therefore records an explicit project-local representation bridge for `\mathbb{P}^n_Y`.

## Required Names

- `IsFinite`
- `IsProjective`
- `finite_implies_projective`

Auxiliary bridge declarations added in `ShadowBench/Source/Main.lean`:

- `ProjectiveSpaceOver`
- `ProjectiveFactorization`

## Candidate Skeleton Review

All four candidate skeletons propose the required surface names, but use an undeclared morphism notation `X →s Y` and undeclared `[Scheme X]` typeclass-style scheme structure. That does not match Mathlib's current algebraic-geometry representation, where schemes are objects `X Y : AlgebraicGeometry.Scheme` and morphisms are category morphisms `X ⟶ Y`.

The final draft adopts only the required declaration names and informal theorem shape from the skeletons. The type signatures are redrafted to use Mathlib's `AlgebraicGeometry.Scheme` category and category morphisms.

## Source Statement Inventory

### line-17

- Planned Lean declarations: `IsFinite`.
- Source locator: `docs/source.tex`, lines 17--21.
- Source statement: A morphism of schemes `f : X \to Y` is finite if it is affine and for every affine open subset `U = Spec(A) \subset Y`, the preimage `f^{-1}(U)` is affine, say `Spec(B)`, where `B` is a finite `A`-module.
- Skeleton candidate used: skeletons supplied the required name only; the final type uses Mathlib scheme morphisms instead of the skeleton notation `X →s Y`.
- Dependencies: `AlgebraicGeometry.Scheme`, category morphisms `X ⟶ Y`, `AlgebraicGeometry.IsFinite`.
- Formal statement review: the draft defines `IsFinite f` as a project-local wrapper around Mathlib's `AlgebraicGeometry.IsFinite f`. Mathlib search describes this predicate as exactly the affine-local condition with finite induced ring maps on affine opens.
- Source qualifiers:
  - Mathematical object class: morphisms of schemes.
  - Quantifier/parameter domain: arbitrary schemes `X` and `Y` and a morphism `f : X \to Y`.
  - Defining condition: `f` is affine.
  - Affine-open condition: for every affine open `U = Spec(A)` in `Y`, the inverse image is affine.
  - Algebra condition: the coordinate algebra over the preimage is finite as an `A`-module.
- Lean coverage:
  - `X Y : AlgebraicGeometry.Scheme` covers schemes.
  - `f : X ⟶ Y` covers morphisms of schemes.
  - `AlgebraicGeometry.IsFinite f` covers the affine and finite-algebra affine-local clauses via Mathlib's morphism property and its theorem `AlgebraicGeometry.isFinite_iff`.
- Scope changes: none beyond Mathlib's standard category-theoretic encoding of scheme morphisms and ring-hom finite properties.
- Independent verifier status: manually accepted on 2026-06-04. The source definition is covered by Mathlib's `AlgebraicGeometry.IsFinite`.
- Source proof / prover notes: definition only; no source proof. Provers should unfold `IsFinite` to `AlgebraicGeometry.IsFinite` and use `AlgebraicGeometry.isFinite_iff` or existing finite morphism instances when needed.

### line-23

- Planned Lean declarations: `ProjectiveSpaceOver`, `ProjectiveFactorization`, `IsProjective`.
- Source locator: `docs/source.tex`, lines 23--33.
- Source statement: A morphism of schemes `f : X \to Y` is projective if there exists an integer `n ≥ 0` and a closed immersion `i : X \hookrightarrow \mathbb{P}^n_Y` such that `f` factors as `X \xrightarrow{i} \mathbb{P}^n_Y \to Y`.
- Skeleton candidate used: skeletons supplied the required name only. The final draft replaces `X →s Y` with Mathlib category morphisms and introduces explicit bridge declarations for the projective-space factorization.
- Dependencies: `ProjectiveSpaceOver`, `ProjectiveFactorization`, `AlgebraicGeometry.IsClosedImmersion`, category composition `≫`.
- Formal statement review: the draft expresses projectivity as nonempty source-shaped factorization data: a natural number `n`, an object over `Y` serving as `\mathbb{P}^n_Y`, a map `i : X ⟶ P.space`, a Mathlib closed-immersion proof for `i`, and the equality `i ≫ P.projection = f`.
- Source qualifiers:
  - Mathematical object class: morphisms of schemes.
  - Quantifier/parameter domain: arbitrary schemes `X` and `Y` and a morphism `f : X \to Y`.
  - Existence of dimension/index: some integer `n ≥ 0`.
  - Projective-space target: `\mathbb{P}^n_Y` over `Y` with its structural projection to `Y`.
  - Closed immersion: a map `i : X \hookrightarrow \mathbb{P}^n_Y` that is a closed immersion.
  - Factorization equality: the composite through the projection to `Y` equals `f`.
- Lean coverage:
  - `X Y : AlgebraicGeometry.Scheme` and `f : X ⟶ Y` cover scheme morphisms.
  - `n : Nat` covers the nonnegative integer index.
  - `ProjectiveSpaceOver Y n` records an object over `Y` used as the Lean representation of `\mathbb{P}^n_Y`.
  - `AlgebraicGeometry.IsClosedImmersion immersion` covers the closed immersion qualifier.
  - `immersion ≫ P.projection = f` covers the factorization condition.
- Scope changes:
  - Partial representation bridge: Mathlib search did not find a canonical projective `n`-space over an arbitrary scheme, so `ProjectiveSpaceOver` is an abstract project-local witness rather than a constructed standard `\mathbb{P}^n_Y`.
  - The definition is source-shaped but not a full construction of projective space. Independent review should decide whether this bridge is acceptable or whether a stronger projective-space construction must be imported or developed before proof handoff.
- Independent verifier status: manually accepted on 2026-06-04 as a partial-bridge formalization. The concrete `\mathbb{P}^n_Y` construction remains abstracted by `ProjectiveSpaceOver`.
- Source proof / prover notes: definition only; no source proof. Provers should use `ProjectiveFactorization` constructors to build witnesses and `AlgebraicGeometry.IsClosedImmersion` for the closed immersion clause.

### line-35

- Planned Lean declarations: `finite_implies_projective`.
- Source locator: `docs/source.tex`, theorem at lines 35--37; proof at lines 37--67.
- Source statement: Let `f : X \to Y` be a finite morphism of schemes. Then `f` is projective.
- Skeleton candidate used: skeletons supplied the required theorem name and implication shape, but the final draft uses Mathlib scheme morphisms and the local definitions above.
- Dependencies: `IsFinite`, `IsProjective`, `ProjectiveFactorization`, `ProjectiveSpaceOver`, `AlgebraicGeometry.IsFinite`, `AlgebraicGeometry.IsProper.instOfIsFinite`, closed immersions into affine/projective space as described in the source proof.
- Formal statement review: the Lean theorem quantifies over arbitrary Mathlib schemes `X` and `Y`, a morphism `f : X ⟶ Y`, and the hypothesis `hf : IsFinite f`, then concludes `IsProjective f`. This preserves the source quantifier order and implication shape. Its coverage of the projective conclusion is partial to the extent recorded in the `IsProjective` bridge entry.
- Source qualifiers:
  - Mathematical object class: finite morphisms of schemes.
  - Quantifier/parameter domain: arbitrary schemes `X`, `Y`, morphism `f : X \to Y`.
  - Hypothesis: `f` is finite.
  - Conclusion: `f` is projective.
  - Follow-on proof facts: locality on `Y`, affine reduction to `Spec(A)` and `Spec(B)`, finite generation of `B` over `A`, quotient of a polynomial algebra, closed immersion into affine space, open immersion into projective space, properness of finite morphisms, and closure giving a closed subscheme of projective space.
- Lean coverage:
  - `IsFinite f` covers the finite morphism hypothesis via the wrapper around Mathlib `AlgebraicGeometry.IsFinite`.
  - `IsProjective f` covers projectivity via `ProjectiveFactorization`; see the representation caveat in `line-23`.
  - The theorem is intentionally left with `by sorry` for the later `/prove` workflow after statement/source verification.
- Scope changes:
  - Inherits the partial projective-space representation bridge from `IsProjective`.
  - The theorem statement does not separately expose the affine-local proof reductions; those are proof content, not extra assumptions.
- Independent verifier status: manually accepted on 2026-06-04 as a partial-bridge formalization; proof remains deferred.
- Complete source proof text:

  The statement is local on `Y`, so we may assume `Y = Spec(A)` and `X = Spec(B)` with `B` a finite `A`-algebra. Since `B` is finite over `A`, it is finitely generated as an `A`-module. Choose generators `b_1, ..., b_n \in B`. Then the map `A[x_1, ..., x_n] \to B`, `x_i \mapsto b_i`, is a surjective `A`-algebra homomorphism. Hence `B \cong A[x_1, ..., x_n]/I` for some ideal `I`. This gives a closed immersion `X = Spec(B) \hookrightarrow \mathbb{A}^n_Y`. Composing with the standard open immersion `\mathbb{A}^n_Y \hookrightarrow \mathbb{P}^n_Y`, and using that finite morphisms are proper, it follows that `X` embeds as a closed subscheme of `\mathbb{P}^n_Y`. Therefore `f` factors as `X \hookrightarrow \mathbb{P}^n_Y \to Y`, where the first map is a closed immersion and the second is projective. Thus `f` is projective.

- Source proof / prover notes:
  - Start by unfolding `IsFinite` to `AlgebraicGeometry.IsFinite`.
  - Search/use `AlgebraicGeometry.IsProper.instOfIsFinite` or `AlgebraicGeometry.instIsProperOfIsFinite` for finite implies proper.
  - The source proof is algebraic-geometric and currently not expected to be closed by direct automation because the draft uses an abstract `ProjectiveSpaceOver` bridge. A later proof run may need either (a) strengthen the bridge with a canonical construction of `\mathbb{P}^n_Y`, or (b) build an abstract `ProjectiveFactorization` witness from accepted assumptions/lemmas.
  - Do not change the theorem statement during proof unless a statement/source review corrects the blueprint.

## Handoff Checklist

- Source document and preflight manifest read.
- Required support files and candidate skeletons read.
- Local project / Mathlib search performed before drafting declarations.
- Blueprint source inventory entries filled for `line-17`, `line-23`, and `line-35`.
- Root project module imports cover `ShadowBench/Source/Main.lean`.
- [x] Manual statement/source audit completed for the Lean statements and representation bridge on 2026-06-04.
- [ ] Proof obligations solved without `sorry`.

Suggested next command after independent statement/source review accepts or corrects this draft:

```text
/prove ShadowBench/Source/Main.lean
```
