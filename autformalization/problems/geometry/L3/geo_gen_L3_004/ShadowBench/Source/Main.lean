import Mathlib

open scoped Manifold ContDiff
open Filter

noncomputable section

/--
The Lean representation of the source notation `𝔛(M)`: smooth vector fields are
infinitely differentiable sections of the tangent bundle.
-/
abbrev SmoothVectorFields
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] :
    Type _ :=
  ContMDiffSection I E ∞ (TangentSpace I : M → Type _)

private noncomputable def bumpLocalFrameVectorField
    (E H M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [FiniteDimensional ℝ E]
    (c : M) (f : SmoothBumpFunction I c) (i : Fin (Module.finrank ℝ E)) :
    SmoothVectorFields I M := by
  classical
  let e := trivializationAt E (TangentSpace I) c
  let b := Module.finBasis ℝ E
  refine ⟨fun x => f x • e.localFrame b i x, ?_⟩
  dsimp [e, b]
  exact ContMDiffOn.smul_section_of_tsupport
    (s := (trivializationAt E (TangentSpace I) c).localFrame (Module.finBasis ℝ E) i)
    (f.contMDiff.contMDiffOn)
    (trivializationAt E (TangentSpace I) c).open_baseSet
    (by simpa [TangentBundle.trivializationAt_baseSet] using f.tsupport_subset_chartAt_source)
    ((trivializationAt E (TangentSpace I) c).contMDiffOn_localFrame_baseSet
      (n := ∞) (b := Module.finBasis ℝ E) i)

private lemma exists_smoothVectorField_ne_zero_at_vanish_on_fin_family
    (E H M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [FiniteDimensional ℝ E]
    (h_pos : 0 < Module.finrank ℝ E)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → M) (hp : Function.Injective p) (i : ι) :
    ∃ X : SmoothVectorFields I M, X (p i) ≠ 0 ∧ ∀ j, j ≠ i → X (p j) = 0 := by
  classical
  let U : Set M := Set.iInter (fun j : {j // j ≠ i} => ({p j.1}ᶜ : Set M))
  have hU_open : IsOpen U := by
    dsimp [U]
    exact isOpen_iInter_of_finite (fun j => isOpen_compl_singleton)
  have hU_mem : p i ∈ U := by
    dsimp [U]
    exact Set.mem_iInter.mpr (fun j => by
      simpa using hp.ne (Ne.symm j.2))
  have hU_nhds : U ∈ nhds (p i) := hU_open.mem_nhds hU_mem
  have hex : ∃ f : SmoothBumpFunction I (p i), tsupport (f : M → ℝ) ⊆ U := by
    simpa using (SmoothBumpFunction.nhds_basis_tsupport (I := I) (p i)).mem_iff.mp hU_nhds
  rcases hex with ⟨f, hfU⟩
  let k : Fin (Module.finrank ℝ E) := ⟨0, h_pos⟩
  refine ⟨bumpLocalFrameVectorField E H M I (p i) f k, ?_, ?_⟩
  · have hc : p i ∈ (trivializationAt E (TangentSpace I) (p i)).baseSet := by
      simp [TangentBundle.trivializationAt_baseSet]
    have hlf :
        (trivializationAt E (TangentSpace I) (p i)).localFrame
          (Module.finBasis ℝ E) k (p i) ≠ 0 := by
      rw [(trivializationAt E (TangentSpace I) (p i)).localFrame_apply_of_mem_baseSet
        (b := Module.finBasis ℝ E) hc]
      exact ((trivializationAt E (TangentSpace I) (p i)).basisAt
        (Module.finBasis ℝ E) hc).ne_zero k
    simpa [bumpLocalFrameVectorField, k] using hlf
  · intro j hji
    have hpj_notU : p j ∉ U := by
      intro hpjU
      have hpjU' : ∀ l : {l // l ≠ i}, p j ∈ ({p l.1}ᶜ : Set M) := by
        exact Set.mem_iInter.mp (by simpa [U] using hpjU)
      have hmem : p j ∈ ({p j}ᶜ : Set M) := hpjU' ⟨j, hji⟩
      exact hmem rfl
    have hpj_not_tsupport : p j ∉ tsupport (f : M → ℝ) := fun h => hpj_notU (hfU h)
    have hf_zero : (f : M → ℝ) (p j) = 0 := by
      have hpj_not_support : p j ∉ Function.support (f : M → ℝ) :=
        fun h => hpj_not_tsupport (subset_tsupport (f := (f : M → ℝ)) h)
      simpa [Function.support] using hpj_not_support
    simp [bumpLocalFrameVectorField, hf_zero]

private def smoothVectorFieldEval
    (E H M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (x : M) : SmoothVectorFields I M →ₗ[ℝ] TangentSpace I x where
  toFun X := X x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma linearIndependent_of_eval_ne_zero_vanish
    (E H M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → M) (X : ι → SmoothVectorFields I M)
    (hne : ∀ i, X i (p i) ≠ 0)
    (hzero : ∀ i j, i ≠ j → X i (p j) = 0) :
    LinearIndependent ℝ X := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  let ev := smoothVectorFieldEval E H M I (p i)
  have hsum' : (∑ j, g j • X j (p i)) = 0 := by
    simpa [ev, smoothVectorFieldEval] using congrArg (fun Y => ev Y) hg
  rw [Finset.sum_eq_single i] at hsum'
  · exact (smul_eq_zero.mp hsum').resolve_right (hne i)
  · intro j _ hji
    simp [hzero j i hji]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

private lemma exists_linearIndependent_smoothVectorFields_of_injective_points
    (E H M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [FiniteDimensional ℝ E]
    (h_pos : 0 < Module.finrank ℝ E)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → M) (hp : Function.Injective p) :
    ∃ X : ι → SmoothVectorFields I M, LinearIndependent ℝ X := by
  classical
  choose X hne hzero using fun i =>
    exists_smoothVectorField_ne_zero_at_vanish_on_fin_family E H M I h_pos p hp i
  exact ⟨X,
    linearIndependent_of_eval_ne_zero_vanish E H M I p X hne
      (fun i j hij => hzero i j (Ne.symm hij))⟩

private lemma infinite_positive_dimensional_manifold
    (E H M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Nonempty M] [FiniteDimensional ℝ E]
    (h_pos : 0 < Module.finrank ℝ E) : Infinite M := by
  classical
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) h_pos
  haveI : Infinite E := Module.Free.infinite ℝ E
  let x : M := Classical.choice inferInstance
  let t : Set E := interior (extChartAt I x).target
  have htopen : IsOpen t := isOpen_interior
  have htne : t.Nonempty := by
    simpa [t] using interior_extChartAt_target_nonempty (I := I) x
  have htinf : Infinite t := by
    rw [Cardinal.infinite_iff]
    have hcard : Cardinal.mk t = Cardinal.mk E := cardinal_eq_of_isOpen ℝ htopen htne
    rw [hcard]
    exact Cardinal.infinite_iff.mp inferInstance
  let f : t → M := fun y => (extChartAt I x).symm y.1
  have hf : Function.Injective f := by
    intro y z hyz
    apply Subtype.ext
    have hyT : y.1 ∈ (extChartAt I x).target := interior_subset y.2
    have hzT : z.1 ∈ (extChartAt I x).target := interior_subset z.2
    calc
      y.1 = (extChartAt I x) ((extChartAt I x).symm y.1) := by
        rw [PartialEquiv.right_inv]
        exact hyT
      _ = (extChartAt I x) ((extChartAt I x).symm z.1) := by
        simpa [f] using congrArg (fun m : M => (extChartAt I x) m) hyz
      _ = z.1 := by
        rw [PartialEquiv.right_inv]
        exact hzT
  exact Infinite.of_injective f hf

/--
Source theorem `line-17` (`smoothVectorField_infinite_dimensional`).
Let `M` be a nonempty positive-dimensional smooth manifold with or without boundary;
then the space `𝔛(M)` of smooth vector fields on `M` is infinite-dimensional.

Source proof: argue by contradiction. If `𝔛(M)` had finite dimension `k`, choose
`k + 1` distinct points in one positive-dimensional coordinate chart, separate them by
pairwise disjoint open neighborhoods, and choose smooth bump functions `fᵢ` supported
there with `fᵢ xᵢ = 1`. Multiplying a nonzero local coordinate vector field
`∂/∂x¹` by these bumps and extending by zero gives global smooth vector fields `Xᵢ`
with disjoint supports. Evaluating a linear relation at `xⱼ` forces its `j`th
coefficient to vanish, giving `k + 1` independent vector fields, a contradiction.

Prover notes: `SmoothVectorFields I M` abbreviates Mathlib's
`ContMDiffSection I E ∞ (TangentSpace I)`. The side conditions make explicit that the
source manifold is Hausdorff, nonempty, and modeled on a finite-dimensional real vector
space of positive dimension; the model-with-corners parameter `I` represents the
source's “with or without boundary” cases.
-/
theorem smoothVectorField_infinite_dimensional
    (E H M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [Nonempty M] [FiniteDimensional ℝ E]
    (h_pos : 0 < Module.finrank ℝ E) :
    ¬ FiniteDimensional ℝ (SmoothVectorFields I M) := by
  classical
  intro hfd
  haveI : FiniteDimensional ℝ (SmoothVectorFields I M) := hfd
  let n := Module.finrank ℝ (SmoothVectorFields I M)
  have hMinf : Infinite M := infinite_positive_dimensional_manifold E H M I h_pos
  haveI : Infinite M := hMinf
  let e := Infinite.natEmbedding M
  let p : Fin (n + 1) → M := fun i => e i.1
  have hp : Function.Injective p := by
    intro i j hij
    apply Fin.ext
    exact e.injective hij
  obtain ⟨X, hli⟩ :=
    exists_linearIndependent_smoothVectorFields_of_injective_points E H M I h_pos p hp
  have hle : Fintype.card (Fin (n + 1)) ≤ Module.finrank ℝ (SmoothVectorFields I M) :=
    hli.fintype_card_le_finrank
  have hle' : n + 1 ≤ n := by
    simpa only [Fintype.card_fin] using hle
  exact Nat.not_succ_le_self n hle'
