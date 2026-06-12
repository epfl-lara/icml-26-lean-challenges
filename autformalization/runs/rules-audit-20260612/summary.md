# ShadowBench Rules Audit - 2026-06-12

Scope: local `problems/*/*/*/ShadowBench/Source/Main.lean` checked against `RULES.md` and local `data/test.jsonl` from `DicoTiar/ShadowBench` (`default/test`).

## Summary
- `problem_count`: 126
- `code_banned_construct_problems`: 0
- `mechanism_problems`: 9
- `missing_local_expected_name_problems`: 3
- `external_only_expected_name_problems`: 3
- `raw_import_problems`: 126
- `extra_import_problems`: 126
- `missing_abm_namespace_problems`: 126
- `fatal_issue_count`: 10
- `warning_count`: 3

## Fatal Findings
### Submission Packaging
- `scripts/export_submission.py` exports raw local project files. Under `RULES.md`, the submitted `formal_proof` should be a namespace-wrapped snippet under `ABM.<area>.<level>.<problem_slug>`, while the evaluator supplies the problem imports. All 126 local files currently contain import lines and no ABM wrapper, so a direct export is not rule-compliant.

### Mechanism Assumptions
These rows compile locally but add a non-source `*Mechanism` hypothesis to the required declaration. That changes the statement shape and is a likely hidden-checker/SA-pass failure.

#### `algebra/L3/alg_grob_L3_001`
- File: `problems/algebra/L3/alg_grob_L3_001/ShadowBench/Source/Main.lean`
- Mechanism declarations: `FiniteProjectiveFactorizationMechanism` line 103
- Expected names: `finite_implies_projective`, `IsFinite`, `IsProjective`
- Affected target header(s):
  - `theorem finite_implies_projective {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : _root_.IsFinite f) (h_factorization : FiniteProjectiveFactorizationMechanism.{u}) : _root_.IsProjective f`
  - `theorem finite_implies_projective {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : _root_.IsFinite f) (h_factorization : FiniteProjectiveFactorizationMechanism.{u}) : _root_.IsProjective f`

#### `algebra/L4/alg_geom_L4_003`
- File: `problems/algebra/L4/alg_geom_L4_003/ShadowBench/Source/Main.lean`
- Mechanism declarations: `ConstructibleIffMechanism` line 38, `CyclotomicAngleConstructibleMechanism` line 81
- Expected names: `constructible_iff`, `cyclotomic_angle_constructible_iff`
- Affected target header(s):
  - `theorem constructible_iff (α : ℝ) (h_constructible_iff : ConstructibleIffMechanism) : IsConstructible α ↔ IsPowerOfTwo (normalClosureDegree α)`
  - `theorem constructible_iff (α : ℝ) (h_constructible_iff : ConstructibleIffMechanism) : IsConstructible α ↔ IsPowerOfTwo (normalClosureDegree α)`
  - `theorem cyclotomic_angle_constructible_iff (n : ℕ) (h_cyclotomic_angle : CyclotomicAngleConstructibleMechanism) : IsAngleConstructible n ↔ IsProductOfPowerOfTwoAndDistinctFermatPrimes n`
  - `theorem cyclotomic_angle_constructible_iff (n : ℕ) (h_cyclotomic_angle : CyclotomicAngleConstructibleMechanism) : IsAngleConstructible n ↔ IsProductOfPowerOfTwoAndDistinctFermatPrimes n`

#### `algebraic-geometry/L3/alg_gen_L3_007`
- File: `problems/algebraic-geometry/L3/alg_gen_L3_007/ShadowBench/Source/Main.lean`
- Mechanism declarations: `GenericPointFiberMechanism` line 13
- Expected names: `isDominant_iff_forall_genericPoints_mem_fiber`
- Affected target header(s):
  - `theorem isDominant_iff_forall_genericPoints_mem_fiber {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : QuasiCompact f) (h_generic_point_fiber : GenericPointFiberMechanism.{u}) : IsDominant f ↔ ∀ y : Y, y ∈ genericPoints Y → ∃ x : X, x ∈ genericPoints X ∧ f x = y`
  - `theorem isDominant_iff_forall_genericPoints_mem_fiber {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : QuasiCompact f) (h_generic_point_fiber : GenericPointFiberMechanism.{u}) : IsDominant f ↔ ∀ y : Y, y ∈ genericPoints Y → ∃ x : X, x ∈ genericPoints X ∧ f x = y`

#### `algebraic-geometry/L3/alg_gen_L3_012`
- File: `problems/algebraic-geometry/L3/alg_gen_L3_012/ShadowBench/Source/Main.lean`
- Mechanism declarations: `LocallyOfFinitePresentationFunctorMechanism` line 9
- Expected names: `locallyOfFinitePresentation_iff_functorOfPoints_limitPreserving`, `functorOfPointsOver`
- Affected target header(s):
  - `theorem locallyOfFinitePresentation_iff_functorOfPoints_limitPreserving {X S : Scheme.{u}} (f : X ⟶ S) (h_lfp_mechanism : LocallyOfFinitePresentationFunctorMechanism.{u}) : LocallyOfFinitePresentation f ↔ functorOfPointsOver (yoneda.obj (Over.mk f))`
  - `theorem locallyOfFinitePresentation_iff_functorOfPoints_limitPreserving {X S : Scheme.{u}} (f : X ⟶ S) (h_lfp_mechanism : LocallyOfFinitePresentationFunctorMechanism.{u}) : LocallyOfFinitePresentation f ↔ functorOfPointsOver (yoneda.obj (Over.mk f))`

#### `combinatorics/L3/com_gen_L3_006`
- File: `problems/combinatorics/L3/com_gen_L3_006/ShadowBench/Source/Main.lean`
- Mechanism declarations: `CayleyTreeCountMechanism` line 19
- Expected names: `CayleyTreeCount`
- Affected target header(s):
  - `theorem CayleyTreeCount (n : ℕ) (hn : 0 < n) (h_cayley : CayleyTreeCountMechanism) : Nat.card (LabeledTree n) = n ^ (n - 2)`
  - `theorem CayleyTreeCount (n : ℕ) (hn : 0 < n) (h_cayley : CayleyTreeCountMechanism) : Nat.card (LabeledTree n) = n ^ (n - 2)`

#### `geometry/L2/geo_gen_L2_003`
- File: `problems/geometry/L2/geo_gen_L2_003/ShadowBench/Source/Main.lean`
- Mechanism declarations: `ErdosMordellInequalityMechanism` line 33
- Expected names: `erdos_mordell_inequality`
- Affected target header(s):
  - `theorem erdos_mordell_inequality (A B C P : EuclideanSpace ℝ (Fin 2)) (h_triangle : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2)))) (h_inside : ∃ u v w : ℝ, 0 < u ∧ 0 < v ∧ 0 < w ∧ u + v + w = 1 ∧ P = u • A + v • B + w • C) (h_erdos_mordell : ErdosMordellInequalityMechanism) : let PL`
  - `theorem erdos_mordell_inequality (A B C P : EuclideanSpace ℝ (Fin 2)) (h_triangle : ¬ Collinear ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2)))) (h_inside : ∃ u v w : ℝ, 0 < u ∧ 0 < v ∧ 0 < w ∧ u + v + w = 1 ∧ P = u • A + v • B + w • C) (h_erdos_mordell : ErdosMordellInequalityMechanism) : let PL`

#### `geometry/L2/geo_gen_L2_010`
- File: `problems/geometry/L2/geo_gen_L2_010/ShadowBench/Source/Main.lean`
- Mechanism declarations: `CircleTangentBundleTrivializationMechanism` line 9
- Expected names: `circle_tangent_bundle_trivialization`
- Affected target header(s):
  - `theorem circle_tangent_bundle_trivialization (h_trivialization : CircleTangentBundleTrivializationMechanism) : Nonempty (TangentBundle (𝓡 1) SourceCircle ≃ₘ⟮(𝓡 1).tangent, (𝓡 1).prod 𝓘(ℝ, ℝ)⟯ (SourceCircle × ℝ))`
  - `theorem circle_tangent_bundle_trivialization (h_trivialization : CircleTangentBundleTrivializationMechanism) : Nonempty (TangentBundle (𝓡 1) SourceCircle ≃ₘ⟮(𝓡 1).tangent, (𝓡 1).prod 𝓘(ℝ, ℝ)⟯ (SourceCircle × ℝ))`

#### `geometry/L2/geo_gen_L2_020`
- File: `problems/geometry/L2/geo_gen_L2_020/ShadowBench/Source/Main.lean`
- Mechanism declarations: `SmoothGraphVectorFieldExtensionMechanism` line 35
- Expected names: `exists_smooth_vectorField_on_graph`
- Affected target header(s):
  - `theorem exists_smooth_vectorField_on_graph {E H M E' H' N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [BoundarylessManifold J N] (f : M → N) (_hf : ContMDiff I J ∞ f) (h_extension : SmoothGraphVectorFieldExtensionMechanism (I`
  - `theorem exists_smooth_vectorField_on_graph {E H M E' H' N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [BoundarylessManifold J N] (f : M → N) (_hf : ContMDiff I J ∞ f) (h_extension : SmoothGraphVectorFieldExtensionMechanism (I`

#### `geometry/L3/geo_gen_L3_001`
- File: `problems/geometry/L3/geo_gen_L3_001/ShadowBench/Source/Main.lean`
- Mechanism declarations: `MorleyTrisectorTheoremMechanism` line 119
- Expected names: `morleys_trisector_theorem`
- Affected target header(s):
  - `theorem morleys_trisector_theorem (A B C X Y Z : PlanePoint) (hABC : IsTriangle A B C) (hMorley : IsFirstMorleyTriangle A B C X Y Z) (h_morley : MorleyTrisectorTheoremMechanism) : IsEquilateralTriangle X Y Z`
  - `theorem morleys_trisector_theorem (A B C X Y Z : PlanePoint) (hABC : IsTriangle A B C) (hMorley : IsFirstMorleyTriangle A B C X Y Z) (h_morley : MorleyTrisectorTheoremMechanism) : IsEquilateralTriangle X Y Z`

### Missing Expected Names
- None after resolving namespace-qualified declarations, apostrophe names, aliases, and imported exact names.

## Warnings
These expected names are not declared locally in `Main.lean`, but `#check` succeeds after importing the project, so they appear to be supplied by Mathlib or another import. This may be acceptable, but review if the challenge expects each row to contain the named declaration directly.

- `analysis/L2/ana_four_L2_004`: `MeasureTheory.Integrable.fourierInv_fourier_eq`
- `topology/L2/top_gen_L2_004`: `exists_preirreducible`
- `topology/L2/top_gen_L2_011`: `Bundle.ContinuousLinearMap.vectorBundle`

## Banned Constructs
- No actual code-level `axiom`, `opaque`, `sorry`, `admit`, `native_decide`, or top-level `unsafe` was found after stripping Lean comments.

## Recommended Fix Order
1. Fix the exporter/submission generator first: strip local imports and wrap the proof body in the required `ABM` namespace for each `idx`.
2. Treat the 9 mechanism-parametrized rows as not strict-solved. Either prove the required statement without the mechanism parameter, or mark them compile-only/high-risk.
3. Review the imported-exact-name warnings and decide whether relying on imported declarations is acceptable for Codabench.
4. Re-run compile and `#print axioms` on the generated submission snippets, not only on local Lake modules.
