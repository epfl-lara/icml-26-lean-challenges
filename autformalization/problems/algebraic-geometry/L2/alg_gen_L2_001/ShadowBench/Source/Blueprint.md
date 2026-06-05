# Formalization Blueprint: `algebraic-geometry/L2/alg_gen_L2_001`

- Source: `docs/source.tex`
- Instructions: `docs/instructions.md`
- Target Lean entry file: `ShadowBench/Source/Main.lean`
- Status: formalization review PASS recorded in batch state; 2026-06-05 full audit verified required files, expected names, and `lake build`. Proof obligations remain for later prove workflows where present.

## Generated File Layout

- `ShadowBench/Source/Main.lean`: contains the source-backed alias/definition, the finite-localization claim extracted from the proof, and the affine-cover theorem skeleton.
- `ShadowBench/Source.lean`: imports `ShadowBench.Source.Main`.
- `ShadowBench.lean`: imports `ShadowBench.Source`, so project-level `lake build` checks the generated target module.

## Source Inventory Entries

- Source inventory entry `line-17`: definition `isNoetherianRing_of_away`, source `docs/source.tex:17-19`, Lean declaration `isNoetherianRing_of_away`.
- Source inventory entry `line-21`: theorem `isLocallyNoetherian_of_affine_cover`, source `docs/source.tex:21-62`, Lean declaration `isLocallyNoetherian_of_affine_cover`.
- Source inventory entry `line-32`: claim inside the theorem proof, source `docs/source.tex:32-62`, Lean declaration `isNoetherianRing_of_away_claim`.

## Import Plan

```lean
import Mathlib.AlgebraicGeometry.Noetherian
```

## Suggested Search Modules

These modules were useful as search or skeleton context, but are not direct imports of the generated target file unless a later proof pass needs them explicitly.

- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.RingTheory.Localization.Submodule`
- `Mathlib.RingTheory.Spectrum.Prime.Noetherian`
- Mathlib declarations found by search:
  - `AlgebraicGeometry.IsLocallyNoetherian`
  - `AlgebraicGeometry.isNoetherianRing_of_away`
  - `AlgebraicGeometry.isLocallyNoetherian_of_affine_cover`
  - `AlgebraicGeometry.isLocallyNoetherian_iff_of_affine_openCover`

## Required Names

- `isNoetherianRing_of_away`
- `isLocallyNoetherian_of_affine_cover`

## Candidate Skeletons

- `docs/skeletons/Skeleton1.lean`, `Skeleton2.lean`, and `Skeleton3.lean` are identical candidate sketches using `OpenSubscheme`, `IsAffineOpen U`, and `structureSheaf X U`. They preserve the intended names but do not match current Mathlib's preferred encoding of affine opens and sections.
- `docs/skeletons/Skeleton4.lean` repeats that sketch and contains an extra trailing `:= by sorry`, so it was not adopted verbatim.
- The final statements instead use Mathlib's existing `X.affineOpens`, `Γ(X, U)`, and `AlgebraicGeometry.IsLocallyNoetherian`, which exactly encode the source qualifiers.

## Source Statement Inventory

### line-17

- Source inventory entry: `line-17`
- Source label: `line-17`
- Source block id: `line-17`
- Planned Lean declarations: `isNoetherianRing_of_away`
- Lean statement: `def isNoetherianRing_of_away (X : Scheme) : Prop := AlgebraicGeometry.IsLocallyNoetherian X`
- Source locator: `docs/source.tex:17-19` (`line-17`).
- Source statement: "A scheme `X` is locally Noetherian if `𝒪_X(U)` is Noetherian for every affine open `U`."
- Skeleton candidate used: the candidate skeleton supplied the required external name, but its raw statement was replaced by the Mathlib class `AlgebraicGeometry.IsLocallyNoetherian`.
- Dependencies: `Mathlib.AlgebraicGeometry.Noetherian`, especially `AlgebraicGeometry.IsLocallyNoetherian` and its field `component_noetherian`.
- Formal statement review: Mathlib defines `class AlgebraicGeometry.IsLocallyNoetherian (X : Scheme) : Prop` with field `component_noetherian : ∀ (U : X.affineOpens), IsNoetherianRing Γ(X, U)`. This is the source definition with affine opens represented by the subtype `X.affineOpens` and sheaf sections by `Γ(X, U)`.
- Source qualifiers:
  - Mathematical object class: scheme `X`.
  - Quantifier order: for every affine open `U` of `X`.
  - Parameter domain: affine opens, encoded as `X.affineOpens`.
  - Output/codomain: proposition that the section ring is Noetherian.
  - Equality/image condition: none.
  - Side conditions: `U` is affine, built into the subtype.
  - Follow-on claims: this definition is the target conclusion of `line-21`.
- Lean coverage: exact coverage via a reducible alias to Mathlib's class.
- Scope changes: none mathematically; Lean uses the established class name and Γ notation rather than restating the field manually.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Source proof / prover notes: this is a definition, so no proof text is present in the source. The alias is reducible, so later proofs may unfold it or use Mathlib facts about `AlgebraicGeometry.IsLocallyNoetherian` directly.

### line-32

- Source inventory entry: `line-32`
- Source label: `line-32`
- Source block id: `line-32`
- Planned Lean declarations: `isNoetherianRing_of_away_claim`
- Lean statement: `theorem isNoetherianRing_of_away_claim {R : Type u} [CommRing R] (S : Finset R) (hS : Ideal.span (α := R) S = ⊤) (hN : ∀ s : S, IsNoetherianRing (Away (M := R) s)) : IsNoetherianRing R := by sorry`
- Source locator: `docs/source.tex:32-62` (`line-32`).
- Source statement: "Let `R` be a commutative ring. If `f_1, …, f_r ∈ R` generate the unit ideal and each `R_{f_i}` is Noetherian, then `R` is Noetherian."
- Skeleton candidate used: no candidate skeleton explicitly included this claim; it is extracted from the source proof as a helper theorem for proof handoff.
- Dependencies: `Mathlib.AlgebraicGeometry.Noetherian`; the matching Mathlib theorem is `AlgebraicGeometry.isNoetherianRing_of_away`.
- Formal statement review: the finite list `f_1, …, f_r` is encoded as a `Finset R`; generating the unit ideal is `Ideal.span (α := R) S = ⊤`; the localized rings `R_{f_i}` are encoded by `Away (M := R) s` for `s : S`.
- Source qualifiers:
  - Mathematical object class: commutative ring `R`.
  - Quantifier order: choose a finite family of elements, assume it generates the unit ideal, assume each localization is Noetherian, conclude `R` is Noetherian.
  - Parameter domain: finite family of elements of `R`, represented by a finset.
  - Output/codomain: `IsNoetherianRing R`.
  - Equality/image condition: `Ideal.span S = ⊤` records generation of the unit ideal.
  - Side conditions: each localized ring `Away s` is Noetherian.
  - Follow-on claims: used in the open-cover step of `line-21`.
- Lean coverage: exact modulo representing an indexed finite list by a finset/subtype; no multiplicity or ordering is used in the source proof.
- Scope changes: the source writes `R_{f_i}` and `f_1, …, f_r`; Lean uses `Localization.Away` and `Finset`. This is a representation change only, not a mathematical weakening.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: Let `φ_i : R → R_{f_i}` be the localization map. For any ideal `𝔞 ⊆ R`, we have `𝔞 = ⋂_{i=1}^r φ_i^{-1}(φ_i(𝔞) · R_{f_i})`. The inclusion `⊆` is obvious. Conversely, suppose `b` is in the intersection. Then `φ_i(b) = a_i / f_i^{n_i}` in `R_{f_i}` for each `i`, where `a_i ∈ 𝔞` and `n_i > 0`. Increasing the exponents if necessary, choose a common `n > 0`. Then `f_i^{m_i}(f_i^n b - a_i) = 0` for some `m_i > 0`; again choose a common `m > 0`. Let `N = m + n`. Since the `f_i` generate the unit ideal, so do the `f_i^N`, hence `∑ c_i f_i^N = 1`. Therefore `b = ∑ c_i f_i^N b = ∑ c_i f_i^m a_i ∈ 𝔞`. Now given an ascending chain of ideals in `R`, localize it at each `f_i`; each localized chain stabilizes because `R_{f_i}` is Noetherian. Since there are finitely many `f_i`, the original chain stabilizes by the ideal-intersection equality.
- Prover notes: Mathlib's theorem `AlgebraicGeometry.isNoetherianRing_of_away` already proves exactly this statement using `IsLocalization.ideal_eq_iInf_comap_map_away` and `monotone_stabilizes_iff_noetherian`. A proof pass can close the skeleton by applying that theorem.

### line-21

- Source inventory entry: `line-21`
- Source label: `line-21`
- Source block id: `line-21`
- Planned Lean declarations: `isLocallyNoetherian_of_affine_cover`
- Lean statement: `theorem isLocallyNoetherian_of_affine_cover {X : Scheme} {ι : Type v} {S : ι → X.affineOpens} (hS : (⨆ i, S i : X.Opens) = ⊤) (hS' : ∀ i, IsNoetherianRing Γ(X, S i)) : isNoetherianRing_of_away X := by sorry`
- Source locator: `docs/source.tex:21-62` (`line-21`).
- Source statement: "If a scheme `X` has an affine open covering `X = ⋃_{i ∈ I} U_i` such that each `Γ(X, U_i)` is Noetherian, then `X` is locally Noetherian."
- Skeleton candidate used: the candidate skeleton supplied the required external name and the broad cover/noetherian hypotheses, but it was replaced by Mathlib's current affine-open-cover encoding.
- Dependencies: `isNoetherianRing_of_away` (`line-17`), `isNoetherianRing_of_away_claim` (`line-32`), and Mathlib theorem `AlgebraicGeometry.isLocallyNoetherian_of_affine_cover`.
- Formal statement review: the source's affine open family `U_i` is represented as `S : ι → X.affineOpens`; `X = ⋃ U_i` is represented by `(⨆ i, S i : X.Opens) = ⊤`; `Γ(X, U_i)` Noetherian is represented by `∀ i, IsNoetherianRing Γ(X, S i)`; the conclusion "`X` is locally Noetherian" is the alias `isNoetherianRing_of_away X` from `line-17`.
- Source qualifiers:
  - Mathematical object class: scheme `X`.
  - Quantifier order: choose an index type and affine-open family, assume it covers `X`, assume each section ring is Noetherian, conclude local Noetherianity.
  - Parameter domain: affine opens of `X`, represented by `X.affineOpens`.
  - Output/codomain: proposition `isNoetherianRing_of_away X`, reducibly `AlgebraicGeometry.IsLocallyNoetherian X`.
  - Equality/image condition: the union cover condition is encoded by `iSup = ⊤` in `X.Opens`.
  - Side conditions: each `S i` is affine by construction; each section ring is Noetherian by hypothesis.
  - Follow-on claims: proof uses stability under basic opens and the finite-localization criterion.
- Lean coverage: exact coverage using Mathlib's affine-open-cover formulation. The theorem quantifies over an arbitrary index type, so it matches the source's possibly infinite affine open covering.
- Scope changes: none mathematically; Lean replaces set-theoretic union notation by complete-lattice supremum of opens.
- Statement verification status: PASS recorded by formalization review; 2026-06-05 audit confirms Lean build and expected-name visibility.
- Complete source proof text: By the Affine communication lemma, it suffices to prove the following. (1) If `U` is an affine open such that `Γ(X, U)` is Noetherian, then `Γ(X, U_f)` is Noetherian for every `f ∈ Γ(X, U)`. (2) If there is a finite cover `U = ⋃_{i∈S} U_{f_i}` by basic opens with `f_i ∈ Γ(X, U)` and each `Γ(X, U_{f_i})` Noetherian, then `Γ(X, U)` is Noetherian. Since `Γ(X, U_f) = Γ(X, U)_f` and localization of a Noetherian ring is Noetherian, (1) follows. For (2), the `f_i` generate the unit ideal in `Γ(X, U)`, so it suffices to prove the finite-localization claim: if `f_1, …, f_r` generate the unit ideal and each `R_{f_i}` is Noetherian, then `R` is Noetherian. The proof of the claim identifies every ideal with the intersection of the comaps of its localized extensions, clears denominators using a common exponent, uses a unit-ideal expression in powers of the `f_i`, and then applies this equality to ascending chains of ideals.
- Prover notes: Mathlib's `AlgebraicGeometry.isLocallyNoetherian_of_affine_cover` proves exactly the chosen Lean statement with conclusion `AlgebraicGeometry.IsLocallyNoetherian X`; since `isNoetherianRing_of_away` is reducible to that class, the theorem should close by unfolding the alias and applying the Mathlib theorem. The source's internal claim is separately queued as `isNoetherianRing_of_away_claim` for documentation and possible proof reuse.

## Handoff Notes

- The Lean proofs for source theorem/claim declarations are intentionally `by sorry` for the formalization draft. They should be solved only after independent statement/source review approves or corrects these statements.
- Suggested proof command after review: `/prove ShadowBench/Source/Main.lean`.
