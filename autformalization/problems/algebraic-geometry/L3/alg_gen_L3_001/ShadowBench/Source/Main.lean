import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Monoidal.Grp_

open CategoryTheory
open AlgebraicGeometry

universe u

/--
Source proof: Let `U` be the smooth locus of the structure morphism. It is open; if its
complement were nonempty, Jacobsonness and density of the smooth locus over the perfect field
`K` give closed points `x ∉ U` and `y ∈ U`. Algebraic closedness identifies closed points with
`K`-points, and the group-object structure gives right translations carrying `x` to `y`. Smooth
loci are preserved by isomorphisms, forcing `x ∈ U`, contradiction.

Prover notes: The source's group scheme over `K` is encoded as `[GrpObj (Over.mk f)]` for
`f : G ⟶ Spec (.of K)`. The statement keeps the source hypothesis `[LocallyOfFiniteType f]`;
a proof may use the locally-Noetherian bridge to obtain local finite presentation, then follow
`AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed` from `Mathlib.AlgebraicGeometry.Group.Smooth`.
-/
lemma smooth_of_grpObj_of_isAlgClosed {K : Type u} [Field K] [IsAlgClosed K]
    {G : Scheme} (f : G ⟶ Spec (.of K)) [LocallyOfFiniteType f] [IsReduced G]
    [GrpObj (Over.mk f)] : Smooth f := by
  letI : LocallyOfFinitePresentation f := inferInstance
  exact AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed f
