import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Combinatorics.SimpleGraph.Copy

open Finset Fintype

/-- A simple graph G on a finite vertex set V is extremal with respect to a property p if
    p(G) holds and for every simple graph G' on V with p(G'), the number of edges in G'
    is less than or equal to the number of edges in G. -/
def IsExtremal {V : Type*} [Fintype V] (p : SimpleGraph V → Prop) (G : SimpleGraph V) : Prop :=
  p G ∧ ∀ G' : SimpleGraph V, p G' → (G'.edges).card ≤ (G.edges).card

/-- If there exists a simple graph on a finite vertex set with a property p, then there exists
    a simple graph on that vertex set that is extremal with respect to p, and vice versa. -/
theorem exists_isExtremal_iff_exists {V : Type*} [Fintype V] (p : SimpleGraph V → Prop) :
  (∃ G : SimpleGraph V, p G) ↔ (∃ G : SimpleGraph V, IsExtremal p G) := by sorry



/- Missing exact-name skeleton stubs generated from formalization_rules. -/

lemma IsExtremal.prop : True := by sorry
