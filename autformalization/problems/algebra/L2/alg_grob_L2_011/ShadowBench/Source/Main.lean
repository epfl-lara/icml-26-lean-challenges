import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.MonomialOrder

open scoped MonomialOrder

/--
Source notation bridge: `leadingMonomial m f` represents the source notation `LM(f)`
for the exponent vector of the leading monomial of `f` under the fixed monomial order `m`.
-/
noncomputable abbrev leadingMonomial {R σ : Type*} [CommSemiring R] (m : MonomialOrder σ)
    (f : MvPolynomial σ R) : σ →₀ ℕ :=
  m.toSyn.symm (f.support.sup m.toSyn)

/--
Source proof: no monomial in `f₁` or `f₂` is greater than `LM(g)` under the fixed
monomial order; every monomial occurring in `f₁ + f₂` occurs in at least one of `f₁`
or `f₂`, so its leading monomial is also bounded by `LM(g)`.

Prover notes: unfold `leadingMonomial` and use the scoped notation `≼[m]`. The proof
can follow the support argument directly from `MvPolynomial.coeff_add`, or a later
prover may add `Mathlib.RingTheory.MvPolynomial.MonomialOrder` and use
`MonomialOrder.degree_add_le`, since the bridge matches `m.degree`. The nonzero
hypotheses are kept for source fidelity, although the packaged degree bound may not
need them.
-/
theorem lm'_add_le_of_both_lm'_le {R σ : Type*} [CommSemiring R] (m : MonomialOrder σ)
    (f₁ f₂ g : MvPolynomial σ R)
    (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0) (hg : g ≠ 0) (hsum : f₁ + f₂ ≠ 0)
    (h₁ : leadingMonomial m f₁ ≼[m] leadingMonomial m g)
    (h₂ : leadingMonomial m f₂ ≼[m] leadingMonomial m g) :
    leadingMonomial m (f₁ + f₂) ≼[m] leadingMonomial m g := by
  classical
  by_cases hf₁' : f₁ = 0
  · exact False.elim (hf₁ hf₁')
  by_cases hf₂' : f₂ = 0
  · exact False.elim (hf₂ hf₂')
  by_cases hg' : g = 0
  · exact False.elim (hg hg')
  by_cases hsum' : f₁ + f₂ = 0
  · exact False.elim (hsum hsum')
  unfold leadingMonomial at h₁ h₂ ⊢
  simp only [AddEquiv.apply_symm_apply] at h₁ h₂ ⊢
  rw [Finset.sup_le_iff]
  intro b hb
  have hb_or : b ∈ f₁.support ∨ b ∈ f₂.support := by
    by_cases hb₁ : b ∈ f₁.support
    · exact Or.inl hb₁
    · right
      rw [MvPolynomial.mem_support_iff] at hb ⊢
      rw [MvPolynomial.notMem_support_iff] at hb₁
      intro h₂zero
      apply hb
      simp [MvPolynomial.coeff_add, hb₁, h₂zero]
  cases hb_or with
  | inl hb₁ =>
      exact le_trans (Finset.le_sup (f := m.toSyn) hb₁) h₁
  | inr hb₂ =>
      exact le_trans (Finset.le_sup (f := m.toSyn) hb₂) h₂
