import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.RingTheory.MvPolynomial.MonomialOrder

/-!
ShadowBench problem: algebra/L2/alg_grob_L2_005
Source: docs/source.tex
Blueprint: ShadowBench/Source/Blueprint.md
-/

open scoped MonomialOrder

/--
`leadingMonomialWithBot m f` is the source convention for `LM(f)`:
it is `⊥` for the zero polynomial and otherwise the `m`-leading exponent vector.
-/
noncomputable def leadingMonomialWithBot {σ : Type*} {R : Type*} [CommSemiring R]
    (m : MonomialOrder σ) (f : MvPolynomial σ R) : WithBot (σ →₀ ℕ) := by
  classical
  exact if f = 0 then (⊥ : WithBot (σ →₀ ℕ)) else (m.degree f : WithBot (σ →₀ ℕ))

/--
The monomial-order strict comparison on `WithBot (σ →₀ ℕ)`, with `⊥` below every
actual monomial. This is the Lean bridge for the source's fixed monomial order on
leading monomials with the zero-polynomial bottom convention.
-/
def leadingMonomialWithBotLT {σ : Type*} (m : MonomialOrder σ)
    (a b : WithBot (σ →₀ ℕ)) : Prop :=
  match a, b with
  | none, none => False
  | none, some _ => True
  | some _, none => False
  | some a, some b => a ≺[m] b

/-- Reverse form of `leadingMonomialWithBotLT`, used to read `LM(g) > LM(f)`. -/
def leadingMonomialWithBotGT {σ : Type*} (m : MonomialOrder σ)
    (a b : WithBot (σ →₀ ℕ)) : Prop :=
  leadingMonomialWithBotLT m b a

/--
Source proof: if `f = 0`, every coefficient of `f` is zero. Otherwise the leading
monomial of `f` exists; every monomial with nonzero coefficient in `f` is at most
`LM(f)`, while the hypothesis says `LM(g) > LM(f)`, so no support monomial of
`f` can equal `LM(g)`.

Prover notes: split on `f = 0`. In the nonzero case, unfold
`leadingMonomialWithBotGT`, `leadingMonomialWithBotLT`, and
`leadingMonomialWithBot`; use `h_g_ne_zero` and `hf` to obtain
`m.degree f ≺[m] m.degree g`, then apply `MonomialOrder.coeff_eq_zero_of_lt`.
-/
theorem coeff_zero_of_lt_lm {σ : Type*} {R : Type*} [CommSemiring R]
    (m : MonomialOrder σ) (f g : MvPolynomial σ R)
    (h_g_ne_zero : g ≠ 0)
    (h_order :
      leadingMonomialWithBotGT m (leadingMonomialWithBot m g)
        (leadingMonomialWithBot m f)) :
    f.coeff (m.degree g) = 0 := by
  by_cases hf : f = 0
  · simp [hf]
  · apply MonomialOrder.coeff_eq_zero_of_lt (m := m)
    have hg_lm : leadingMonomialWithBot m g = (m.degree g : WithBot (σ →₀ ℕ)) := by
      simp [leadingMonomialWithBot, h_g_ne_zero]
    have hf_lm : leadingMonomialWithBot m f = (m.degree f : WithBot (σ →₀ ℕ)) := by
      simp [leadingMonomialWithBot, hf]
    simpa [leadingMonomialWithBotGT, leadingMonomialWithBotLT, hg_lm, hf_lm] using h_order
