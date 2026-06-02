import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Combinatorics.SimpleGraph.Copy

open Finset Fintype

def IsExtremal {V : Type*} [Fintype V] (p : SimpleGraph V → Prop) (G : SimpleGraph V) : Prop :=
  p G ∧ ∀ G' : SimpleGraph V, p G' → (G'.edges).card ≤ (G.edges).card

theorem IsExtremal.prop {V : Type*} [Fintype V] (p : SimpleGraph V → Prop) :
  (∃ G : SimpleGraph V, p G) ↔ (∃ G : SimpleGraph V, IsExtremal p G) := by sorry

theorem exists_isExtremal_iff_exists {V : Type*} [Fintype V] (p : SimpleGraph V → Prop) :
  (∃ G : SimpleGraph V, p G) ↔ (∃ G : SimpleGraph V, IsExtremal p G) := by sorry
