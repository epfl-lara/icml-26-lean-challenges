# Formalization Blueprint: `algebraic-geometry/L3/alg_gen_L3_004`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Candidate skeletons: `docs/skeletons/`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: one source-backed theorem skeleton for Zariski's main theorem in the namespace used by Mathlib.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so the default project target covers the generated target module.

## Candidate Skeletons

- Dataset: `Lemmy00/ShadowBench-skeletons-prod`
- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` all propose the required short name and the allowed starting imports, but use noncanonical or unavailable surface syntax such as `OpenSubscheme`, `IsNormalization`, `f'.restrict`, and `IsQuasiFiniteAt`.
- `docs/skeletons/Skeleton4.lean` repeats the same shape and has an extra trailing `:= by sorry`, so it is not adopted.
- Final statement source: local/Mathlib search located the existing Mathlib theorem shape in `Mathlib.AlgebraicGeometry.ZariskisMainTheorem`, whose statement matches the source theorem for the canonical relative normalization.

## Import Plan

```lean
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.RingTheory.Etale.QuasiFinite
```

## Suggested Search Modules

- `Mathlib.AlgebraicGeometry.ZariskisMainTheorem`: contains the matching theorem statement, the local neighborhood lemma `Scheme.Hom.exists_mem_and_isIso_morphismRestrict_toNormalization`, the openness of the quasi-finite locus, and related corollaries.

## Required Names

- Source name: `Scheme.Hom.exists_isIso_morphismRestrict_toNormalization`
- Lean declaration in file: `AlgebraicGeometry.Scheme.Hom.exists_isIso_morphismRestrict_toNormalization` (declared as `Scheme.Hom.exists_isIso_morphismRestrict_toNormalization` inside `namespace AlgebraicGeometry`).

## Source Statement Inventory

### line-17

- Source inventory entry: `line-17`
- Source theorem name: `Scheme.Hom.exists_isIso_morphismRestrict_toNormalization`
- Planned Lean declarations: `Scheme.Hom.exists_isIso_morphismRestrict_toNormalization`
- Source locator: `line-17` in `docs/source.tex`, theorem lines 17-23, proof lines 23-49.
- Generated Lean file: `ShadowBench/Source/Main.lean`
- Skeleton candidate used: no skeleton adopted verbatim. Skeletons 1-3 supplied the required name/import hints but used noncanonical/unavailable API; Skeleton4 was malformed. The final statement follows the Mathlib relative-normalization API discovered by `lean_search`.
- Dependencies:
  - objects and morphisms: `Scheme`, `X ⟶ Y`, `CategoryTheory` notation;
  - hypotheses: `[LocallyOfFiniteType f]`, `[QuasiCompact f]`, `[IsSeparated f]` for “finite type and separated”;
  - normalization/factorization: `f.normalization`, `f.toNormalization : X ⟶ f.normalization`, and `f.fromNormalization : f.normalization ⟶ Y` from `Mathlib.AlgebraicGeometry.Normalization`;
  - open subschemes and restriction: `f.normalization.Opens`, `f.toNormalization ∣_ U`, `f.toNormalization ⁻¹ᵁ U`;
  - quasi-finite locus: pointwise predicate `f.QuasiFiniteAt x`.
- Formal statement review:
  - Source says: for a finite-type separated morphism `f : X → Y`, let `Y'` be the normalization of `Y` in `X` with factorization `X --f'--> Y' --ν--> Y`; then there is an open subscheme `U' ⊆ Y'` such that `(f')⁻¹(U') → U'` is an isomorphism and `(f')⁻¹(U')` is exactly the set of points of `X` at which `f` is quasi-finite.
  - Lean says: for `f : X ⟶ Y`, under `[LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]`, there exists `U : f.normalization.Opens` such that `IsIso (f.toNormalization ∣_ U)` and `(f.toNormalization ⁻¹ᵁ U).1 = { x | f.QuasiFiniteAt x }`.
  - Comparison: `f.normalization` is Mathlib's canonical relative normalization of `Y` in `X`; `f.toNormalization` and `f.fromNormalization` are the canonical factorization maps. The source's “finite type” is represented by the standard pair `[LocallyOfFiniteType f] [QuasiCompact f]`.
- Source qualifiers:
  - mathematical object class: schemes and scheme morphisms;
  - quantifier order: `X`, `Y`, then morphism `f : X ⟶ Y`, then typeclass hypotheses;
  - parameter domain/codomain: `f : X ⟶ Y`, open `U` in `f.normalization`;
  - side conditions: finite type and separated, represented as locally finite type plus quasi-compact, and separated;
  - output codomain: an open subscheme/open subset of the relative normalization;
  - isomorphism condition: the morphism restricted to the preimage of that open is an isomorphism;
  - equality/image condition: the preimage open in `X` has carrier exactly `{ x | f.QuasiFiniteAt x }`;
  - follow-on claims in proof: openness of the quasi-finite locus, local isomorphism neighborhoods, étale descent, and reduction to the finite summand after elementary étale base change.
- Lean coverage:
  - Covers the theorem for Mathlib's canonical relative normalization and canonical factorization maps.
  - Covers both enumerated conclusions: restriction isomorphism and equality with the quasi-finite locus.
  - Covers the finite-type hypothesis via `[LocallyOfFiniteType f] [QuasiCompact f]` rather than a single `FiniteType` class.
  - Does not separately quantify over an arbitrary isomorphic normalization object `Y'` with arbitrary maps `f'` and `ν`.
- Scope changes:
  - Representation change: the source's named normalization `Y'` is formalized as the canonical object `f.normalization`; no separate bridge theorem for arbitrary chosen normalizations is included in this draft. If the statement/source reviewer requires arbitrary-choice normalization support, add a companion bridge declaration before proof handoff.
  - This is intended as the standard canonical-normalization interpretation of the source, but the representation decision remains for the independent review pass.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text:

```text
The subset U ⊂ X of points where f is quasi-finite is open. The theorem is equivalent to
(a) U' = f'(U) ⊂ Y' is open,
(b) U = (f')^{-1}(U'), and
(c) U → U' is an isomorphism.

Let x ∈ U be arbitrary. We claim that there exists an open neighborhood f'(x) ∈ V ⊂ Y' such that (f')^{-1}V → V is an isomorphism. We first prove that the claim implies the lemma. Indeed, then (f')^{-1}V ≃ V is both locally of finite type over Y (as an open subscheme of X) and for v ∈ V the residue field extension κ(v)/κ(ν(v)) is algebraic (as V ⊂ Y' and Y' is integral over Y). Hence the fibers of V → Y are discrete and (f')^{-1}V → Y is locally quasi-finite. This implies (f')^{-1}V ⊂ U and V ⊂ U'. Since x was arbitrary we see that (a), (b), and (c) are true.

Let y = f(x). Let (Z,z) → (Y,y) be an elementary étale neighbourhood. Denote by a subscript _Z the base change to Z. Let x'=(x,z) ∈ X_Z be the unique point in the fiber X_z lying over x. Note that U_Z ⊂ X_Z is the set of points where f_Z is quasi-finite. Note that X_Z → Y'_Z → Z is the normalization of Z in X_Z. Suppose that the claim holds for x' ∈ U_Z ⊂ X_Z → Y'_Z → Z, i.e., suppose that we can find an open neighborhood f'_Z(x') ∈ V' ⊂ Y'_Z such that (f'_Z)^{-1}V' → V' is an isomorphism. The morphism Y'_Z → Y' is étale hence the image V ⊂ Y' of V' is open. Observe that f'(x) ∈ V as f'_Z(x') ∈ V' and (f'_Z)^{-1}V' = (f')^{-1}V ×_V V' as Y'_Z ×_{Y'} X = X_Z. Since the map (f'_Z)^{-1}V' → V' is an isomorphism and {V' → V} is an étale covering, we conclude that (f')^{-1}V → V is an isomorphism by descent. In other words, the claim holds for x ∈ U ⊂ X → Y' → Y.

By the result of the previous paragraph we may replace Y by an elementary étale neighbourhood of y = f(x) in order to prove the claim. Thus we may assume there is a decomposition X = V ⨿ W into open and closed subschemes where V → Y is finite and x ∈ V. Since X is a disjoint union of V and W over Y and since V → Y is finite we see that the normalization of Y in X is the morphism X = V ⨿ W → V ⨿ W' → Y where W' is the normalization of Y in W. Hence, the claim follows.
```

- Source proof / prover notes: Full source proof text is recorded above. Use the local normalization-isomorphism neighborhoods at quasi-finite points, descend them along an elementary étale cover, and glue them to obtain the open of the relative normalization whose preimage is the quasi-finite locus.
- Prover notes:
  - Mathlib already contains the proof in `Mathlib.AlgebraicGeometry.ZariskisMainTheorem` under the same full declaration name; if proving from this skeleton, consult that file first.
  - The local claim corresponds to `Scheme.Hom.exists_mem_and_isIso_morphismRestrict_toNormalization`.
  - The global proof chooses local neighborhoods for each point of the quasi-finite locus, uses `Opens.iSupOpenCover`, proves the restriction is an isomorphism Zariski-locally on the target, and identifies the preimage with `{ x | f.QuasiFiniteAt x }`.

## Handoff Notes

- Current draft intentionally leaves theorem proof as `by sorry`; do not start proof search until an independent statement/source verification pass checks or corrects the statement and the canonical-normalization representation choice.
- Suggested next command after a successful review pass: `/prove ShadowBench/Source/Main.lean AlgebraicGeometry.Scheme.Hom.exists_isIso_morphismRestrict_toNormalization`.
