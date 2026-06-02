import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.Sheaves.Stalks

open TopCat Opposite TopologicalSpace CategoryTheory

universe u v

def stalkToFiber_injective {X : TopCat.{u}} (F : X.Presheaf (Type v)) : X.Presheaf (Type v) := sorry

theorem sheafifyStalkIso {X : TopCat.{u}} (F : X.Presheaf (Type v)) (x : X) :
    IsIso (show (stalkToFiber_injective F).stalk x ⟶ F.stalk x from sorry) := by sorry
