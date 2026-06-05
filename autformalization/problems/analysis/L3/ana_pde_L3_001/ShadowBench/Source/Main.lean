import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Data.Real.Basic

open scoped BigOperators

/-- Coordinate model for the source space `ℝ^n`. -/
abbrev CoordinateSpace (n : ℕ) := Fin n → ℝ

/--
First coordinate derivative `u_i`, using the Fréchet derivative in the
`i`-th basis direction.
-/
noncomputable def firstPartial {n : ℕ} (i : Fin n)
    (u : CoordinateSpace n → ℝ) (x : CoordinateSpace n) : ℝ :=
  fderiv ℝ u x (Pi.single i 1)

/--
Second coordinate derivative `u_{ij}`, differentiating `u_j` in the
`i`-th direction.
-/
noncomputable def secondPartial {n : ℕ} (i j : Fin n)
    (u : CoordinateSpace n → ℝ) (x : CoordinateSpace n) : ℝ :=
  fderiv ℝ (fun y => firstPartial j u y) x (Pi.single i 1)

/-- The non-divergence form linear operator from the source statement. -/
noncomputable def linearEllipticOperator {n : ℕ}
    (a : Fin n → Fin n → CoordinateSpace n → ℝ)
    (b : Fin n → CoordinateSpace n → ℝ)
    (c : CoordinateSpace n → ℝ)
    (u : CoordinateSpace n → ℝ)
    (x : CoordinateSpace n) : ℝ :=
  (∑ i : Fin n, ∑ j : Fin n, a i j x * secondPartial i j u x) +
    (∑ i : Fin n, b i x * firstPartial i u x) + c x * u x

/-- Uniform ellipticity on `Ω`, encoded by a positive lower quadratic-form bound. -/
def UniformlyEllipticOn {n : ℕ}
    (a : Fin n → Fin n → CoordinateSpace n → ℝ)
    (Ω : Set (CoordinateSpace n)) : Prop :=
  ∃ lambda : ℝ, 0 < lambda ∧
    ∀ x ∈ Ω, ∀ ξ : CoordinateSpace n,
      lambda * (∑ i : Fin n, ξ i * ξ i) ≤
        ∑ i : Fin n, ∑ j : Fin n, a i j x * ξ i * ξ j

/--
Source: `docs/source.tex`, source inventory entry `line-17`.

Source proof: set `v = M - u`. Then `v ≥ 0`, `v x₀ = 0`, and the operator
inequality reverses to `Lv ≤ 0`. The zero set `A = {x ∈ Ω | v x = 0}` is
closed and nonempty.
If a point of `A` is not interior, the source uses an interior tangent ball and the Hopf
lemma to get a strictly negative normal derivative, contradicting the zero gradient at an
interior minimum. Hence `A` is open; since `Ω` is connected, `A = Ω`, so `u ≡ M` on `Ω`.

Prover notes: the present statement records the PDE assumptions needed for that argument:
coordinate `C^2` regularity, continuity of coefficients on `Ω`, uniform ellipticity,
`c ≤ 0`, `Lu ≥ 0`, and an attained nonnegative maximum. The missing hard ingredient for the
future proof queue is a formal Hopf lemma/strong maximum principle for this operator.
-/
theorem satisfies_interior_sphere {n : ℕ}
    (Ω : Set (CoordinateSpace n))
    (hΩ_open : IsOpen Ω)
    (hΩ_connected : IsConnected Ω)
    (a : Fin n → Fin n → CoordinateSpace n → ℝ)
    (b : Fin n → CoordinateSpace n → ℝ)
    (c : CoordinateSpace n → ℝ)
    (ha_cont : ∀ i j, ContinuousOn (a i j) Ω)
    (hb_cont : ∀ i, ContinuousOn (b i) Ω)
    (hc_cont : ContinuousOn c Ω)
    (h_elliptic : UniformlyEllipticOn a Ω)
    (hc_nonpos : ∀ x ∈ Ω, c x ≤ 0)
    (u : CoordinateSpace n → ℝ)
    (hu_C2 : ContDiffOn ℝ 2 u Ω)
    (h_Lu_nonneg : ∀ x ∈ Ω, linearEllipticOperator a b c u x ≥ 0)
    (x₀ : CoordinateSpace n)
    (hx₀ : x₀ ∈ Ω)
    (M : ℝ)
    (hM_nonneg : 0 ≤ M)
    (hM_attained : u x₀ = M)
    (hM_isMax : ∀ x ∈ Ω, u x ≤ M) :
    ∀ x ∈ Ω, u x = M := by
  sorry
