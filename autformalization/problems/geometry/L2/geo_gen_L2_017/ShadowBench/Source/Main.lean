import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Basic

open Set

/-- Bridge for the source's standard identification `ℝ^(m+n) ≃ ℝ^m × ℝ^n`.
The theorem below is stated in product coordinates because the source's partial-sum
formula writes points as `(x, y)`. -/
def productCoordinatesEquiv (m n : ℕ) :
    (Fin m → ℝ) × (Fin n → ℝ) ≃ (Fin (m + n) → ℝ) :=
  Fin.appendEquiv m n

/-- The source's partial sum set.  Points in the source's split copy of `ℝ^(m+n)`
are represented as pairs `(x, y)` with `x : Fin m → ℝ` and `y : Fin n → ℝ`.
A point belongs to `partialSum S₁ S₂` exactly when it has the form
`(x, y₁ + y₂)` with `(x, y₁) ∈ S₁` and `(x, y₂) ∈ S₂`. -/
def partialSum {m n : ℕ} (S₁ S₂ : Set ((Fin m → ℝ) × (Fin n → ℝ))) :
    Set ((Fin m → ℝ) × (Fin n → ℝ)) :=
  {p | ∃ x : Fin m → ℝ, ∃ y₁ y₂ : Fin n → ℝ,
    (x, y₁) ∈ S₁ ∧ (x, y₂) ∈ S₂ ∧ p = (x, y₁ + y₂)}

/-- Source theorem `convex_partialSum`, `docs/source.tex` lines 17-56.

Source proof: take two points of the partial sum, write them as
`(x, y₁ + y₂)` and `(x', y₁' + y₂')`, and take a convex coefficient `θ`.
The convex combination equals
`(θ x + (1 - θ) x', (θ y₁ + (1 - θ) y₁') + (θ y₂ + (1 - θ) y₂'))`.
By convexity of `S₁`, the first pair `(θ x + (1 - θ) x', θ y₁ + (1 - θ) y₁')`
lies in `S₁`; by convexity of `S₂`, the analogous pair with `y₂` lies in `S₂`.
These two witnesses show that the convex combination is again in the partial sum.

Prover notes: unfold `partialSum`, destruct the two membership witnesses, apply convexity of
`S₁` and `S₂` to the corresponding pairs, then provide the three coordinatewise convex
combination witnesses.  The final equality is product/Pi extensionality and module algebra. -/
theorem convex_partialSum (m n : ℕ) (S₁ S₂ : Set ((Fin m → ℝ) × (Fin n → ℝ)))
    (h₁ : Convex ℝ S₁) (h₂ : Convex ℝ S₂) :
    Convex ℝ (partialSum S₁ S₂) := by
  rw [convex_iff_add_mem]
  intro p hp q hq a b ha hb hab
  rcases hp with ⟨x, y₁, y₂, hx₁, hx₂, rfl⟩
  rcases hq with ⟨x', y₁', y₂', hx₁', hx₂', rfl⟩
  refine ⟨a • x + b • x', a • y₁ + b • y₁', a • y₂ + b • y₂', ?_, ?_, ?_⟩
  · simpa [Prod.smul_def, Prod.add_def] using
      (convex_iff_add_mem.mp h₁ hx₁ hx₁' ha hb hab)
  · simpa [Prod.smul_def, Prod.add_def] using
      (convex_iff_add_mem.mp h₂ hx₂ hx₂' ha hb hab)
  · ext i <;> simp [smul_add, add_assoc, add_left_comm]
