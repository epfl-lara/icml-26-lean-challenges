import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Vector.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base


variable {α β γ δ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ] [LinearOrder δ]

def contains_pattern (M : α → ℕ) (P : β → ℕ) : Prop :=
  ∃ f : β → α, StrictMono f ∧ ∀ x y, (P x < P y ↔ M (f x) < M (f y))

instance [Fintype α] [DecidableRel (α := α) (· < ·)] [DecidableRel (α := γ) (· < ·)] {f : α → γ} :
  Decidable (StrictMono f) := inferInstanceAs (Decidable (∀ _ _, _ → _))

instance {M : α → ℕ} {P : β → ℕ} [DecidableRel (α := α) (· < ·)]
    [DecidableRel (α := β) (· < ·)]
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] :
    Decidable (contains_pattern M P) :=
    inferInstanceAs <| Decidable <|
    ∃ f : β → α, StrictMono f ∧ ∀ x y, (P x < P y ↔ M (f x) < M (f y))

def avoids (M : α → ℕ) (P : β → ℕ) : Prop := ¬ contains_pattern M P

notation:50 M " avoids " P => avoids M P
notation:50 M " contains " P => contains_pattern M P

def one_to_n (n : ℕ) : Fin n → ℕ := fun x ↦ x
