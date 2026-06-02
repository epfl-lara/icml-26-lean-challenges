import Mathlib.Topology.FiberBundle.Constructions
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Analysis.Normed.Operator.Prod

open Bundle Set FiberBundle

variable {𝕜 : Type*} [NormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {B : Type*} [TopologicalSpace B] {E : B → Type*}
variable [∀ x, TopologicalSpace (E x)] [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace E)]
variable {B' : Type*} [TopologicalSpace B']

def Trivialization.pullback_linear (e : Trivialization F (π E)) (he : e.IsLinear 𝕜)
    (f : B' → B) (hf : Continuous f) :
    Trivialization F (π (f *ᵖ E)) := sorry

instance VectorBundle.pullback [VectorBundle 𝕜 F E] (f : B' → B) (hf : Continuous f) :
    VectorBundle 𝕜 F (f *ᵖ E) := by sorry
