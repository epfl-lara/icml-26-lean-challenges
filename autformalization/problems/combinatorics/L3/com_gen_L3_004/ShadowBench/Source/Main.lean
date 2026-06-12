import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Finite

open Finset Fintype

noncomputable section

/-- The number of edges of a simple graph on a finite vertex type, using classical
decidability to build the finite edge set. -/
def simpleGraphEdgeCount {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ := by
  classical
  exact G.edgeFinset.card

/-- A simple graph is extremal with respect to `p` when it satisfies `p` and has at
least as many edges as every graph on the same finite vertex type satisfying `p`. -/
def IsExtremal {V : Type*} [Fintype V] (p : SimpleGraph V → Prop) (G : SimpleGraph V) : Prop :=
  p G ∧ ∀ G' : SimpleGraph V, p G' → simpleGraphEdgeCount G' ≤ simpleGraphEdgeCount G

/--
Source proof: This source lemma is the definition of “extremal with respect to `p`”.
Proof sketch: unfold `IsExtremal`; the result is the displayed conjunction.
Prover notes: this should close by definitional simplification once the prover pass starts.
-/
lemma IsExtremal.prop {V : Type*} [Fintype V] (p : SimpleGraph V → Prop) (G : SimpleGraph V) :
    IsExtremal p G ↔
      p G ∧ ∀ G' : SimpleGraph V, p G' → simpleGraphEdgeCount G' ≤ simpleGraphEdgeCount G := by
  rfl

/--
Source proof: The displayed equivalence says that a graph satisfying `p` exists iff an
extremal graph for `p` exists. The immediate direction extracts `p` from an extremal
witness; the other direction chooses, among all graphs satisfying `p`, one with maximal
edge count, using finiteness of simple graphs on the fixed finite vertex type.
Prover notes: for the displayed order, right-to-left is immediate from `IsExtremal.prop`,
and left-to-right is the finite maximum argument from the source.
-/
theorem exists_isExtremal_iff_exists {V : Type*} [Fintype V] (p : SimpleGraph V → Prop) :
    (∃ G : SimpleGraph V, p G) ↔ (∃ G : SimpleGraph V, IsExtremal p G) := by
  classical
  constructor
  · rintro ⟨G, hpG⟩
    obtain ⟨G', hpG', hmax⟩ := by
      apply exists_max_image {G : SimpleGraph V | p G} simpleGraphEdgeCount
      exact ⟨G, by simpa using hpG⟩
    exact ⟨G', ⟨by simpa using hpG', by
      intro G'' hpG''
      exact hmax G'' (by simpa using hpG'')⟩⟩
  · rintro ⟨G, hG⟩
    exact ⟨G, hG.1⟩
