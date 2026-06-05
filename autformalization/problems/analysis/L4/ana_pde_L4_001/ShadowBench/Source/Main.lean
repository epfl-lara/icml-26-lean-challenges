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

/--
Source `line-17`, lemma `no_interior_max_of_Lu_pos`.
If `u` has a nonnegative maximum value `M` on `closure Ω`, satisfies `Lu > 0` in
`Ω`, and the operator is uniformly elliptic with continuous bounded coefficients and
`c ≤ 0`, then `u` cannot attain this maximum value at a point of `Ω`.

Source proof: at an assumed interior maximum `x₀`, all first derivatives vanish and the
Hessian is negative semidefinite. Ellipticity makes the coefficient matrix positive
definite, so the second-order term is nonpositive; with `c≤0` and `u x₀≥0`, this gives
`Lu x₀≤0`, contradicting `Lu x₀>0`.

Prover notes: likely needs helper lemmas for Fréchet derivatives at an interior maximum
and for contracting a positive-definite coefficient matrix with a negative-semidefinite
Hessian.
-/
lemma no_interior_max_of_Lu_pos {n : ℕ}
    (Ω : Set (PDEPoint n))
    (hΩ_open : IsOpen Ω)
    (hΩ_connected : IsConnected Ω)
    (hΩ_bounded : Bornology.IsBounded Ω)
    (a : Fin n → Fin n → PDEPoint n → ℝ)
    (b : Fin n → PDEPoint n → ℝ)
    (c : PDEPoint n → ℝ)
    (h_elliptic : UniformlyEllipticOn Ω a)
    (h_coeff_cont : ContinuousCoefficientsOn Ω a b c)
    (h_coeff_bounded : BoundedCoefficientsOn Ω a b c)
    (hc_nonpos : ∀ x ∈ Ω, c x ≤ 0)
    (u : PDEPoint n → ℝ)
    (hu_c2 : ContDiffOn ℝ 2 u Ω)
    (hu_cont_closure : ContinuousOn u (closure Ω))
    (hLu_pos : ∀ x ∈ Ω, 0 < Lu a b c u x)
    (M : ℝ)
    (hmax : HasNonnegativeMaximumOnClosure Ω u M) :
    ¬ ∃ x ∈ Ω, u x = M := by
  sorry

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
  sorry
