import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.Clopen
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
private lemma contactSet_open_of_local_constancy {n : ℕ}
    (Ω : Set (CoordinateSpace n))
    (u : CoordinateSpace n → ℝ)
    (M : ℝ)
    (hlocal :
      ∀ y : Ω, u y.1 = M →
        ∃ U : Set (CoordinateSpace n),
          IsOpen U ∧ y.1 ∈ U ∧ U ∩ Ω ⊆ {x | u x = M}) :
    IsOpen ({y : Ω | u y.1 = M} : Set Ω) := by
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  rcases hlocal y hy with ⟨U, hUopen, hyU, hUsub⟩
  refine ⟨Subtype.val ⁻¹' U, ?_, hUopen.preimage continuous_subtype_val, hyU⟩
  intro z hz
  exact hUsub ⟨hz, z.2⟩

/--
Pure topology: in a connected set, a nonempty clopen contact set is the whole set.
-/
private lemma eq_on_of_contactSet_clopen_connected {α : Type*} [TopologicalSpace α]
    (s : Set α)
    (hs_conn : IsConnected s)
    (f : α → ℝ)
    (M : ℝ)
    (hne : ({x : s | f x.1 = M} : Set s).Nonempty)
    (hclosed : IsClosed ({x : s | f x.1 = M} : Set s))
    (hopen : IsOpen ({x : s | f x.1 = M} : Set s)) :
    ∀ x ∈ s, f x = M := by
  let C : Set s := {x : s | f x.1 = M}
  haveI : PreconnectedSpace s := Subtype.preconnectedSpace hs_conn.isPreconnected
  have hCuniv : C = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ hne
  intro x hx
  have hmem : (⟨x, hx⟩ : s) ∈ C := by
    rw [hCuniv]
    exact Set.mem_univ _
  exact hmem

/--
The contact set is closed because a `C²` function is continuous on `Ω`.
-/
private lemma contactSet_closed_of_contDiffOn {n : ℕ}
    (Ω : Set (CoordinateSpace n))
    (u : CoordinateSpace n → ℝ)
    (M : ℝ)
    (hu_C2 : ContDiffOn ℝ 2 u Ω) :
    IsClosed ({y : Ω | u y.1 = M} : Set Ω) := by
  have hcont : Continuous (Ω.restrict u) := hu_C2.continuousOn.restrict
  simpa [Set.preimage, Set.restrict] using
    (isClosed_singleton.preimage hcont : IsClosed ((Ω.restrict u) ⁻¹' ({M} : Set ℝ)))

/--
Local-constancy conclusion supplied by the Hopf lemma / strong maximum principle
in the source proof. This is separated as a named proposition because Mathlib
does not currently provide the corresponding theorem for the custom uniformly
elliptic non-divergence-form operator above.
-/
def StrongMaximumPrincipleLocalConstancy {n : ℕ}
    (Ω : Set (CoordinateSpace n))
    (_hΩ_open : IsOpen Ω)
    (a : Fin n → Fin n → CoordinateSpace n → ℝ)
    (b : Fin n → CoordinateSpace n → ℝ)
    (c : CoordinateSpace n → ℝ)
    (_ha_cont : ∀ i j, ContinuousOn (a i j) Ω)
    (_hb_cont : ∀ i, ContinuousOn (b i) Ω)
    (_hc_cont : ContinuousOn c Ω)
    (_h_elliptic : UniformlyEllipticOn a Ω)
    (_hc_nonpos : ∀ x ∈ Ω, c x ≤ 0)
    (u : CoordinateSpace n → ℝ)
    (_hu_C2 : ContDiffOn ℝ 2 u Ω)
    (_h_Lu_nonneg : ∀ x ∈ Ω, linearEllipticOperator a b c u x ≥ 0)
    (M : ℝ)
    (_hM_nonneg : 0 ≤ M)
    (_hM_isMax : ∀ x ∈ Ω, u x ≤ M) : Prop :=
  ∀ y : Ω, u y.1 = M →
    ∃ U : Set (CoordinateSpace n),
      IsOpen U ∧ y.1 ∈ U ∧ U ∩ Ω ⊆ {x | u x = M}

/--
Proof mechanism for the analytic step in the source proof: once the local
strong maximum principle has been supplied, every contact point is locally
constant inside `Ω`.
-/
theorem strongMaximumPrinciple_local_constancy {n : ℕ}
    (Ω : Set (CoordinateSpace n))
    (hΩ_open : IsOpen Ω)
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
    (M : ℝ)
    (hM_nonneg : 0 ≤ M)
    (hM_isMax : ∀ x ∈ Ω, u x ≤ M)
    (h_strong_maximum_principle :
      StrongMaximumPrincipleLocalConstancy Ω hΩ_open a b c ha_cont hb_cont
        hc_cont h_elliptic hc_nonpos u hu_C2 h_Lu_nonneg M hM_nonneg hM_isMax) :
    ∀ y : Ω, u y.1 = M →
      ∃ U : Set (CoordinateSpace n),
        IsOpen U ∧ y.1 ∈ U ∧ U ∩ Ω ⊆ {x | u x = M} :=
  h_strong_maximum_principle

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
    (hM_isMax : ∀ x ∈ Ω, u x ≤ M)
    (h_strong_maximum_principle :
      StrongMaximumPrincipleLocalConstancy Ω hΩ_open a b c ha_cont hb_cont
        hc_cont h_elliptic hc_nonpos u hu_C2 h_Lu_nonneg M hM_nonneg hM_isMax) :
    ∀ x ∈ Ω, u x = M := by
  classical
  have hclosed : IsClosed ({y : Ω | u y.1 = M} : Set Ω) :=
    contactSet_closed_of_contDiffOn Ω u M hu_C2
  have hne : ({y : Ω | u y.1 = M} : Set Ω).Nonempty := by
    exact ⟨⟨x₀, hx₀⟩, hM_attained⟩
  have hlocal :
      ∀ y : Ω, u y.1 = M →
        ∃ U : Set (CoordinateSpace n),
          IsOpen U ∧ y.1 ∈ U ∧ U ∩ Ω ⊆ {x | u x = M} := by
    exact strongMaximumPrinciple_local_constancy Ω hΩ_open a b c ha_cont hb_cont
      hc_cont h_elliptic hc_nonpos u hu_C2 h_Lu_nonneg M hM_nonneg hM_isMax
      h_strong_maximum_principle
  have hopen : IsOpen ({y : Ω | u y.1 = M} : Set Ω) :=
    contactSet_open_of_local_constancy Ω u M hlocal
  exact eq_on_of_contactSet_clopen_connected Ω hΩ_connected u M hne hclosed hopen
