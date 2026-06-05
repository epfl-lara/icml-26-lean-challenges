import Mathlib

open Real MeasureTheory

namespace Brahmagupta

abbrev Point := EuclideanSpace ℝ (Fin 2)

def xCoord (P : Point) : ℝ :=
  P 0

def yCoord (P : Point) : ℝ :=
  P 1

def twiceOrientedTriangleArea (P Q R : Point) : ℝ :=
  (xCoord Q - xCoord P) * (yCoord R - yCoord P) -
    (yCoord Q - yCoord P) * (xCoord R - xCoord P)

noncomputable def triangleArea (P Q R : Point) : ℝ :=
  |twiceOrientedTriangleArea P Q R| / 2

noncomputable def quadrilateralArea (A B C D : Point) : ℝ :=
  triangleArea A B C + triangleArea A C D

noncomputable def semiperimeter (A B C D : Point) : ℝ :=
  (dist A B + dist B C + dist C D + dist D A) / 2

def IsCyclicQuadrilateral (A B C D : Point) : Prop :=
  ∃ (O : Point) (r : ℝ),
    0 ≤ r ∧ dist A O = r ∧ dist B O = r ∧ dist C O = r ∧ dist D O = r

def IsConvexQuadrilateralInOrder (A B C D : Point) : Prop :=
  (0 < twiceOrientedTriangleArea A B C ∧
      0 < twiceOrientedTriangleArea B C D ∧
      0 < twiceOrientedTriangleArea C D A ∧
      0 < twiceOrientedTriangleArea D A B) ∨
    (twiceOrientedTriangleArea A B C < 0 ∧
      twiceOrientedTriangleArea B C D < 0 ∧
      twiceOrientedTriangleArea C D A < 0 ∧
      twiceOrientedTriangleArea D A B < 0)

end Brahmagupta

/--
Source theorem `thm:brahmagupta_formula` (`docs/source.tex`, lines 17--27):
for a convex cyclic quadrilateral `A B C D` in order, with side lengths
`a = |AB|`, `b = |BC|`, `c = |CD|`, `d = |DA|`, semiperimeter
`s = (a + b + c + d) / 2`, and area `K`, Brahmagupta's formula states
`K = sqrt ((s - a) * (s - b) * (s - c) * (s - d))`.

Source proof: none is included in the source document.
Proof sketch / prover notes: use the standard derivation from Bretschneider's
formula and the cyclic-quadrilateral fact that opposite angles are supplementary,
or derive Bretschneider by decomposing the quadrilateral into two triangles along
diagonal `AC`, applying the law of cosines and the sine area formula, then use
`h_area` to replace the formal area bridge `Brahmagupta.quadrilateralArea` by `K`.
-/
theorem brahmagupta_formula (A B C D : Brahmagupta.Point) (K : ℝ)
    (h_cyclic : Brahmagupta.IsCyclicQuadrilateral A B C D)
    (h_convex : Brahmagupta.IsConvexQuadrilateralInOrder A B C D)
    (h_area : K = Brahmagupta.quadrilateralArea A B C D) :
    let a := dist A B
    let b := dist B C
    let c := dist C D
    let d := dist D A
    let s := (a + b + c + d) / 2
    K = Real.sqrt ((s - a) * (s - b) * (s - c) * (s - d)) := by
  sorry
