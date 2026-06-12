import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Real.Hom

open Set

/--
An explicit affine-function bridge for real-valued functions on `ℝ^n`, represented
in Lean as functions on `Fin n → ℝ`. The source proof obtains a continuous
linear functional from Hahn--Banach and then adds a constant.
-/
def IsAffineRealMap {n : ℕ} (h : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ l : ((Fin n → ℝ) →L[ℝ] ℝ), ∃ b : ℝ, ∀ x, h x = l x + b

/--
Source theorem `line-17` from `docs/source.tex`: a convex finite-valued function
`f : ℝ^n → ℝ` above a concave finite-valued function `g : ℝ^n → ℝ` admits an
affine separator `h` with `g x ≤ h x ≤ f x` for every `x`.

Proof sketch: form the strict upper epigraph `E = {(x,t) | t > f x}` and strict
lower hypograph `H = {(x,t) | t < g x}` in `ℝ^n × ℝ`. They are nonempty,
open, convex, and disjoint. Separate them by the open-open geometric Hahn--Banach
theorem, write the separating functional as `A x + c t`, prove `c > 0`, and set
`h x = (u - A x) / c`. The epsilon argument in the source then gives
`g x ≤ h x ≤ f x`.

Prover notes: the Lean statement represents the affine function as `x ↦ l x + b`,
where `l : (Fin n → ℝ) →L[ℝ] ℝ` and `b : ℝ`, matching the linear-functional-plus-
constant construction from the source proof.
-/
theorem exists_affine_between_of_concaveOn_le_convexOn {n : ℕ}
    (f g : (Fin n → ℝ) → ℝ)
    (hf : ConvexOn ℝ Set.univ f)
    (hg : ConcaveOn ℝ Set.univ g)
    (hfg : ∀ x, g x ≤ f x) :
    ∃ h : (Fin n → ℝ) → ℝ, IsAffineRealMap h ∧
      ∀ x, g x ≤ h x ∧ h x ≤ f x := by
  have hf_cont : Continuous f := hf.locallyLipschitz.continuous
  have hg_cont : Continuous g := hg.locallyLipschitz.continuous
  let S : Set (((Fin n → ℝ) × ℝ)) := {p | f p.1 < p.2}
  let T : Set (((Fin n → ℝ) × ℝ)) := {p | p.2 < g p.1}
  have hSconv : Convex ℝ S := by
    simpa [S] using hf.convex_strict_epigraph
  have hTconv : Convex ℝ T := by
    simpa [T] using hg.convex_strict_hypograph
  have hSopen : IsOpen S := by
    simpa [S] using isOpen_lt (hf_cont.comp continuous_fst) continuous_snd
  have hTopen : IsOpen T := by
    simpa [T] using isOpen_lt continuous_snd (hg_cont.comp continuous_fst)
  have hdisj : Disjoint S T := by
    rw [Set.disjoint_iff]
    rintro p ⟨hpS, hpT⟩
    have hpS' : f p.1 < p.2 := by simpa [S] using hpS
    have hpT' : p.2 < g p.1 := by simpa [T] using hpT
    exact (not_lt_of_ge (hfg p.1)) (lt_trans hpS' hpT')
  obtain ⟨L, u, hLS, hLT⟩ :=
    geometric_hahn_banach_open_open hSconv hSopen hTconv hTopen hdisj
  let A : ((Fin n → ℝ) →L[ℝ] ℝ) :=
    L.comp ((ContinuousLinearMap.id ℝ (Fin n → ℝ)).prod (0 : (Fin n → ℝ) →L[ℝ] ℝ))
  let alpha : ℝ := L ((0 : Fin n → ℝ), (1 : ℝ))
  have hL_zero_t (t : ℝ) : L ((0 : Fin n → ℝ), t) = t * alpha := by
    have hp : ((0 : Fin n → ℝ), t) = t • ((0 : Fin n → ℝ), (1 : ℝ)) := by
      ext i <;> simp
    rw [hp, map_smul]
    simp [alpha, smul_eq_mul]
  have hL_decomp (x : Fin n → ℝ) (t : ℝ) : L (x, t) = A x + t * alpha := by
    have hp : (x, t) = (x, (0 : ℝ)) + ((0 : Fin n → ℝ), t) := by
      ext i <;> simp
    rw [hp, map_add, hL_zero_t]
    simp [A]
  have halpha_neg : alpha < 0 := by
    have hS0 : ((0 : Fin n → ℝ), f (0 : Fin n → ℝ) + 1) ∈ S := by
      dsimp [S]
      linarith
    have hT0 : ((0 : Fin n → ℝ), g (0 : Fin n → ℝ) - 1) ∈ T := by
      dsimp [T]
      linarith
    have hu := hLS _ hS0
    have hl := hLT _ hT0
    rw [hL_zero_t] at hu hl
    have hmul : (f (0 : Fin n → ℝ) + 1) * alpha <
        (g (0 : Fin n → ℝ) - 1) * alpha := lt_trans hu hl
    have hdiff : 0 < (f (0 : Fin n → ℝ) + 1) -
        (g (0 : Fin n → ℝ) - 1) := by
      nlinarith [hfg (0 : Fin n → ℝ)]
    nlinarith
  let c : ℝ := -alpha
  have hc_pos : 0 < c := by
    dsimp [c]
    nlinarith [halpha_neg]
  have hc_ne : c ≠ 0 := by nlinarith [hc_pos]
  have h_upper (x : Fin n → ℝ) : A x + f x * alpha ≤ u := by
    refine le_of_forall_pos_le_add ?_
    intro η hη
    let eps : ℝ := η / c
    have heps_pos : 0 < eps := div_pos hη hc_pos
    have hmem : (x, f x + eps) ∈ S := by
      dsimp [S]
      linarith
    have hsep := hLS _ hmem
    rw [hL_decomp] at hsep
    have heq : c * eps = η := by
      dsimp [eps]
      field_simp [hc_ne]
    have hcalc : A x + f x * alpha < u + η := by
      calc
        A x + f x * alpha = A x + (f x + eps) * alpha + c * eps := by
          dsimp [c]
          ring
        _ = A x + (f x + eps) * alpha + η := by rw [heq]
        _ < u + η := by nlinarith [hsep]
    exact le_of_lt hcalc
  have h_lower (x : Fin n → ℝ) : u ≤ A x + g x * alpha := by
    refine le_of_forall_pos_le_add ?_
    intro η hη
    let eps : ℝ := η / c
    have heps_pos : 0 < eps := div_pos hη hc_pos
    have hmem : (x, g x - eps) ∈ T := by
      dsimp [T]
      linarith
    have hsep := hLT _ hmem
    rw [hL_decomp] at hsep
    have heq : c * eps = η := by
      dsimp [eps]
      field_simp [hc_ne]
    have hcalc : u < A x + g x * alpha + η := by
      calc
        u < A x + (g x - eps) * alpha := hsep
        _ = A x + g x * alpha + η := by
          rw [← heq]
          dsimp [c]
          ring
    exact le_of_lt hcalc
  refine ⟨fun x => (A x - u) / c, ?_, ?_⟩
  · refine ⟨(c⁻¹) • A, (-u) / c, ?_⟩
    intro x
    dsimp
    field_simp [hc_ne]
    ring
  · intro x
    constructor
    · exact (le_div_iff₀ hc_pos).2 (by
        dsimp [c]
        nlinarith [h_lower x])
    · exact (div_le_iff₀ hc_pos).2 (by
        dsimp [c]
        nlinarith [h_upper x])
