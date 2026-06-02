import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.Monoidal.Grp_

open CategoryTheory

/-- If G is a group scheme over an algebraically closed field k that is reduced and locally of finite type, then G is smooth over k. -/
lemma smooth_of_grpObj_of_isAlgClosed {k : Type*} [Field k] [IsAlgClosed k]
    {G : Type*} [Scheme G] [Algebra k G] [Group G] [ContinuousGroup G]
    [IsReduced G] [IsLocallyFiniteType G k] : IsSmooth G k := by sorry
:= by sorry
