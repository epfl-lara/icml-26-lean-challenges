import Mathlib.Algebra.Order.WithTop.Untop0
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Topology.LocallyFinsupp

open Filter Topology

/-!
ShadowBench problem `analysis/L2/ana_mero_L2_001`.
Source document: `docs/source.tex`.
Blueprint and source map: `ShadowBench/Source/Blueprint.md`.
-/

/--
Source `line-17` (`divisor`): the divisor of `f` on `U` is the integer-valued
function whose value at `z` is the order of `f` at `z` when `f` is meromorphic
on `U` and `z ∈ U`, and is zero otherwise.

The source writes `ord_z(f)` with codomain `ℤ`.  Mathlib's
`meromorphicOrderAt` has codomain `WithTop ℤ`; `.untop₀` is the explicit bridge
that sends infinite order to `0`, matching the following support definition's
exclusion of `∞`.
-/
noncomputable def divisor (K : Type*) [NontriviallyNormedField K]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace K E]
    (U : Set K) (f : K → E) : K → ℤ := by
  classical
  exact fun z ↦ if MeromorphicOn f U ∧ z ∈ U then (meromorphicOrderAt f z).untop₀ else 0

/--
Source `line-34` (`divisor_support`): the support of the divisor is the subset
of `U` where the divisor value is nonzero.
-/
noncomputable def divisor_support (K : Type*) [NontriviallyNormedField K]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace K E]
    (U : Set K) (f : K → E) : Set K :=
  {z | z ∈ U ∧ divisor K E U f z ≠ 0}

/--
Source `line-34`, equivalence clause: under the source assumption that `f` is
meromorphic on `U`, membership in the support is equivalent to lying in `U` and
having order neither zero nor infinite.

Source proof: the source presents this as the displayed "Equivalently" form of
the support definition.
Prover notes: unfold `divisor_support` and `divisor`; use `hf` and the membership
hypothesis to simplify the `if`; then use `WithTop.untop₀_eq_zero` to translate
the nonzero integer value into `meromorphicOrderAt f z ≠ 0` and
`meromorphicOrderAt f z ≠ ⊤`.
-/
theorem mem_divisor_support_iff (K : Type*) [NontriviallyNormedField K]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace K E]
    (U : Set K) (f : K → E) (hf : MeromorphicOn f U) (z : K) :
    z ∈ divisor_support K E U f ↔
      z ∈ U ∧ meromorphicOrderAt f z ≠ 0 ∧ meromorphicOrderAt f z ≠ (⊤ : WithTop ℤ) := by
  classical
  simp [divisor_support, divisor, hf, WithTop.untop₀_eq_zero]
  tauto

/--
Source `line-51` (`divisor_support_locally_finite`): if `f` is meromorphic on
`U`, then the support of `div_U(f)` is locally finite in `U`.

Source proof: near each point of `U`, meromorphicity gives a local normal form
`f z = (z - z₀)^n • g z` on a punctured neighborhood with `g` analytic and
`g z₀ ≠ 0`; zeros of analytic functions are isolated unless the function
vanishes identically, so only finitely many zeros or poles occur in a suitable
neighborhood, and hence the intersection with the divisor support is finite.

Prover notes: the quickest proof should compare this `divisor_support` with the
support of Mathlib's `MeromorphicOn.divisor f U` from
`Mathlib.Analysis.Meromorphic.Divisor`, then use its
`supportLocallyFiniteWithinDomain` field.  A source-style proof can instead use
the codiscrete theorem for the set where `meromorphicOrderAt f z` is zero or
infinite, together with `supportDiscreteWithin_iff_locallyFiniteWithin`.
-/
theorem divisor_support_locally_finite (K : Type*) [NontriviallyNormedField K]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace K E]
    (U : Set K) (f : K → E) (hf : MeromorphicOn f U) :
    ∀ x ∈ U, ∃ V ∈ 𝓝 x, (V ∩ divisor_support K E U f).Finite := by
  classical
  have hsub : (divisor K E U f).support ⊆ U := by
    intro z hz
    by_contra hzU
    have hz0 : divisor K E U f z = 0 := by
      simp [divisor, hzU]
    have hzne : divisor K E U f z ≠ 0 := by
      simpa [Function.mem_support] using hz
    exact hzne hz0
  have hlocSupport : ∀ z ∈ U, ∃ t ∈ 𝓝 z,
      Set.Finite (t ∩ (divisor K E U f).support) := by
    apply (supportDiscreteWithin_iff_locallyFiniteWithin hsub).1
    filter_upwards [mem_codiscrete_subtype_iff_mem_codiscreteWithin.1
      hf.codiscrete_setOf_meromorphicOrderAt_eq_zero_or_top] with y hy
    simp [divisor, hf, WithTop.untop₀_eq_zero] at hy ⊢
    tauto
  intro x hx
  rcases hlocSupport x hx with ⟨V, hV, hfin⟩
  refine ⟨V, hV, hfin.subset ?_⟩
  intro y hy
  exact ⟨hy.1, by simpa [divisor_support, Function.mem_support] using hy.2.2⟩
