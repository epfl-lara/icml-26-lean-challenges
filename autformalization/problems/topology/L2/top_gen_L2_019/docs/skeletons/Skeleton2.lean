import Mathlib.Topology.Instances.CantorSet
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.Perfect

open Set Topology

theorem isTotallyDisconnected_cantorSet :
  let C := CantorSet
  IsTotallyDisconnected (C : Set ℝ) ∧ IsPerfect (C : Set ℝ) := by sorry
