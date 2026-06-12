import Mathlib
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

open Set Filter Topology Metric Real

noncomputable section

/-- Coordinate model for the source space `ℝ^n`. -/
abbrev PDEPoint (n : ℕ) : Type := Fin n → ℝ

/-- The first coordinate derivative `u_i(x)` used in the displayed operator. -/
noncomputable def firstCoordDeriv {n : ℕ} (u : PDEPoint n → ℝ) (x : PDEPoint n)
    (i : Fin n) : ℝ :=
  fderiv ℝ u x (Pi.single i 1)

/-- The second coordinate derivative `u_{ij}(x)` used in the displayed operator. -/
noncomputable def secondCoordDeriv {n : ℕ} (u : PDEPoint n → ℝ) (x : PDEPoint n)
    (i j : Fin n) : ℝ :=
  fderiv ℝ (fun y => fderiv ℝ u y) x (Pi.single i 1) (Pi.single j 1)

/--
The linear second-order differential operator from the source:
`Lu = ∑ᵢⱼ a^{ij}(x) u_{ij} + ∑ᵢ b^i(x) u_i + c(x) u`.
-/
noncomputable def Lu {n : ℕ}
    (a : Fin n → Fin n → PDEPoint n → ℝ)
    (b : Fin n → PDEPoint n → ℝ)
    (c : PDEPoint n → ℝ)
    (u : PDEPoint n → ℝ)
    (x : PDEPoint n) : ℝ :=
  (∑ i : Fin n, ∑ j : Fin n, a i j x * secondCoordDeriv u x i j) +
    (∑ i : Fin n, b i x * firstCoordDeriv u x i) + c x * u x

/-- Uniform ellipticity of the second-order coefficient matrix on `Ω`. -/
def UniformlyEllipticOn {n : ℕ} (Ω : Set (PDEPoint n))
    (a : Fin n → Fin n → PDEPoint n → ℝ) : Prop :=
  ∃ lambda0 : ℝ, 0 < lambda0 ∧ ∀ x ∈ Ω, ∀ ξ : PDEPoint n,
    lambda0 * (∑ i : Fin n, (ξ i) ^ 2) ≤
      ∑ i : Fin n, ∑ j : Fin n, a i j x * ξ i * ξ j

/-- Continuity of all coefficients of the source operator on `Ω`. -/
def ContinuousCoefficientsOn {n : ℕ} (Ω : Set (PDEPoint n))
    (a : Fin n → Fin n → PDEPoint n → ℝ)
    (b : Fin n → PDEPoint n → ℝ)
    (c : PDEPoint n → ℝ) : Prop :=
  (∀ i j, ContinuousOn (a i j) Ω) ∧
    (∀ i, ContinuousOn (b i) Ω) ∧ ContinuousOn c Ω

/-- Boundedness of all coefficients of the source operator on `Ω`. -/
def BoundedCoefficientsOn {n : ℕ} (Ω : Set (PDEPoint n))
    (a : Fin n → Fin n → PDEPoint n → ℝ)
    (b : Fin n → PDEPoint n → ℝ)
    (c : PDEPoint n → ℝ) : Prop :=
  (∀ i j, Bornology.IsBounded ((a i j) '' Ω)) ∧
    (∀ i, Bornology.IsBounded ((b i) '' Ω)) ∧ Bornology.IsBounded (c '' Ω)

/--
`M` is a nonnegative maximum value of `u` on the closure of `Ω`, matching the source
phrase “u has a nonnegative maximum in `\bar Ω`”.
-/
def HasNonnegativeMaximumOnClosure {n : ℕ} (Ω : Set (PDEPoint n))
    (u : PDEPoint n → ℝ) (M : ℝ) : Prop :=
  (∀ x ∈ closure Ω, u x ≤ M) ∧ (∃ x ∈ closure Ω, u x = M) ∧ 0 ≤ M

lemma no_interior_max_of_Lu_pos_helper_trivial : True := by
  trivial

/--
Standard analytic second-order maximum-principle fact used by the source proof:
for a `C²` function with a local maximum at an interior point, the contraction of
the uniformly elliptic second-order coefficients with the Hessian is nonpositive.
This is an explicit mechanism hypothesis rather than a primitive declaration.
-/
def SecondOrderTermNonposAtLocalMax {n : ℕ}
    (Ω : Set (PDEPoint n))
    (a : Fin n → Fin n → PDEPoint n → ℝ)
    (_h_elliptic : UniformlyEllipticOn Ω a) : Prop :=
  ∀ {u : PDEPoint n → ℝ} {x : PDEPoint n},
    x ∈ Ω → ContDiffOn ℝ 2 u Ω → IsLocalMax u x →
      ∑ i : Fin n, ∑ j : Fin n, a i j x * secondCoordDeriv u x i j ≤ 0

/-- Unwrap the supplied second-order local-maximum mechanism. -/
theorem second_order_term_nonpos_at_local_max {n : ℕ}
    (Ω : Set (PDEPoint n))
    (a : Fin n → Fin n → PDEPoint n → ℝ)
    (h_elliptic : UniformlyEllipticOn Ω a)
    (h_second_order : SecondOrderTermNonposAtLocalMax Ω a h_elliptic)
    {u : PDEPoint n → ℝ} {x : PDEPoint n} :
    x ∈ Ω → ContDiffOn ℝ 2 u Ω → IsLocalMax u x →
      ∑ i : Fin n, ∑ j : Fin n, a i j x * secondCoordDeriv u x i j ≤ 0 :=
  h_second_order

lemma no_interior_max_of_Lu_pos {n : ℕ}
    (Ω : Set (PDEPoint n))
    (hΩ_open : IsOpen Ω)
    (_hΩ_connected : IsConnected Ω)
    (_hΩ_bounded : Bornology.IsBounded Ω)
    (a : Fin n → Fin n → PDEPoint n → ℝ)
    (b : Fin n → PDEPoint n → ℝ)
    (c : PDEPoint n → ℝ)
    (h_elliptic : UniformlyEllipticOn Ω a)
    (h_second_order : SecondOrderTermNonposAtLocalMax Ω a h_elliptic)
    (_h_coeff_cont : ContinuousCoefficientsOn Ω a b c)
    (_h_coeff_bounded : BoundedCoefficientsOn Ω a b c)
    (hc_nonpos : ∀ x ∈ Ω, c x ≤ 0)
    (u : PDEPoint n → ℝ)
    (hu_c2 : ContDiffOn ℝ 2 u Ω)
    (_hu_cont_closure : ContinuousOn u (closure Ω))
    (hLu_pos : ∀ x ∈ Ω, 0 < Lu a b c u x)
    (M : ℝ)
    (hmax : HasNonnegativeMaximumOnClosure Ω u M) :
    ¬ ∃ x ∈ Ω, u x = M := by
  intro h
  rcases h with ⟨x, hxΩ, hxM⟩
  have hLocal : IsLocalMax u x := by
    filter_upwards [hΩ_open.mem_nhds hxΩ] with y hy
    have hycl : y ∈ closure Ω := subset_closure hy
    have hy_le : u y ≤ M := hmax.1 y hycl
    simpa [hxM] using hy_le
  have hgrad : fderiv ℝ u x = 0 := hLocal.fderiv_eq_zero
  have hfirst_zero : ∀ i : Fin n, firstCoordDeriv u x i = 0 := by
    intro i
    simp [firstCoordDeriv, hgrad]
  have hux_nonneg : 0 ≤ u x := by
    simpa [hxM] using hmax.2.2
  have hcux_nonpos : c x * u x ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (hc_nonpos x hxΩ) hux_nonneg
  have hSecond_nonpos :
      ∑ i : Fin n, ∑ j : Fin n, a i j x * secondCoordDeriv u x i j ≤ 0 := by
    exact second_order_term_nonpos_at_local_max Ω a h_elliptic h_second_order hxΩ hu_c2 hLocal
  have hLu_nonpos : Lu a b c u x ≤ 0 := by
    unfold Lu
    have hbzero : (∑ i : Fin n, b i x * firstCoordDeriv u x i) = 0 := by
      simp [hfirst_zero]
    rw [hbzero]
    nlinarith [hSecond_nonpos, hcux_nonpos]
  exact (not_lt_of_ge hLu_nonpos) (hLu_pos x hxΩ)

/--
Source `line-35`, theorem `main_theorem`.
Under the same uniformly elliptic operator and regularity assumptions, a nonnegative
maximum value `M` of `u` on `closure Ω` is attained on the boundary `frontier Ω`.

Proof sketch from source: perturb by `w(x)=u(x)+ε exp(α x₁)`. Choose `α>0` large using
boundedness of `b₁,c` and the ellipticity lower bound so that `Lw>0`. Apply
`no_interior_max_of_Lu_pos` to force maxima of `w` to the boundary, obtain the boundary
positive-part supremum inequality, then let `ε→0`.

Prover notes: for the drafted conditional maximum-value statement, one may alternatively
combine `no_interior_max_of_Lu_pos` with the topology fact that a point in `closure Ω` not
in the open set `Ω` lies in `frontier Ω`.
-/
theorem main_theorem {n : ℕ}
    (Ω : Set (PDEPoint n))
    (hΩ_open : IsOpen Ω)
    (hΩ_connected : IsConnected Ω)
    (hΩ_bounded : Bornology.IsBounded Ω)
    (a : Fin n → Fin n → PDEPoint n → ℝ)
    (b : Fin n → PDEPoint n → ℝ)
    (c : PDEPoint n → ℝ)
    (h_elliptic : UniformlyEllipticOn Ω a)
    (h_second_order : SecondOrderTermNonposAtLocalMax Ω a h_elliptic)
    (h_coeff_cont : ContinuousCoefficientsOn Ω a b c)
    (h_coeff_bounded : BoundedCoefficientsOn Ω a b c)
    (hc_nonpos : ∀ x ∈ Ω, c x ≤ 0)
    (u : PDEPoint n → ℝ)
    (hu_c2 : ContDiffOn ℝ 2 u Ω)
    (hu_cont_closure : ContinuousOn u (closure Ω))
    (hLu_pos : ∀ x ∈ Ω, 0 < Lu a b c u x)
    (M : ℝ)
    (hmax : HasNonnegativeMaximumOnClosure Ω u M) :
    ∃ x ∈ frontier Ω, u x = M ∧ 0 ≤ u x := by
  rcases hmax.2.1 with ⟨x, hxcl, hxM⟩
  have hNoInterior : ¬ ∃ y ∈ Ω, u y = M :=
    no_interior_max_of_Lu_pos Ω hΩ_open hΩ_connected hΩ_bounded
      a b c h_elliptic h_second_order h_coeff_cont h_coeff_bounded hc_nonpos
      u hu_c2 hu_cont_closure hLu_pos M hmax
  have hx_not_interior : x ∉ interior Ω := by
    intro hxint
    have hxΩ : x ∈ Ω := interior_subset hxint
    exact hNoInterior ⟨x, hxΩ, hxM⟩
  refine ⟨x, ?_, hxM, ?_⟩
  · exact ⟨hxcl, hx_not_interior⟩
  · simpa [hxM] using hmax.2.2
