import Mathlib.Topology.FiberBundle.Constructions
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Analysis.Normed.Operator.Prod

open Topology FiberBundle

/-- The projection map of the pullback bundle -/
def pullbackProjection {B B' F k : Type*} 
  [TopologicalSpace B] [TopologicalSpace B'] 
  [NormedAddCommGroup F] [NormedSpace k F] [NormedField k]
  {E : Type*} [TopologicalSpace E]
  (π : E → B) (f : B' → B) : 
  (Σ' x : B', π⁻¹' {f x}) → B' := sorry

/-- The map from the pullback bundle to the original bundle -/
def pullbackMap {B B' F k : Type*} 
  [TopologicalSpace B] [TopologicalSpace B'] 
  [NormedAddCommGroup F] [NormedSpace k F] [NormedField k]
  {E : Type*} [TopologicalSpace E]
  (π : E → B) (f : B' → B) : 
  (Σ' x : B', π⁻¹' {f x}) → E := sorry

/-- Definition of the pullback bundle construction -/
def Trivialization.pullback_linear {B B' F k : Type*} 
  [TopologicalSpace B] [TopologicalSpace B'] 
  [NormedAddCommGroup F] [NormedSpace k F] [NormedField k]
  {E : Type*} [TopologicalSpace E]
  (π : E → B) (f : B' → B) (hf : Continuous f) :
  -- The pullback bundle is the disjoint union of fibers E_{f(x)} for x in B'
  Σ' x : B', π⁻¹' {f x} := sorry

/-- Theorem: The pullback bundle inherits the structure of a vector bundle -/
theorem VectorBundle.pullback {B B' F k : Type*} 
  [TopologicalSpace B] [TopologicalSpace B'] 
  [NormedAddCommGroup F] [NormedSpace k F] [NormedField k]
  {E : Type*} [TopologicalSpace E]
  (π : E → B) [hVec : VectorBundle E B F k π]
  (f : B' → B) (hf : Continuous f) :
  -- The assertion is that the pullback_linear has the structure of a vector bundle
  VectorBundle (Trivialization.pullback_linear B B' F k E π f hf) B' F k (pullbackProjection π f) := sorry
