import Mathlib

namespace EuclideanGeometry

structure Point := (x y : ℝ)

structure Circle where
  center : Point
  radius : ℝ

def CircleNotContains (c1 c2 : Circle) : Prop :=
  ¬(∀ p : Point, (p.x - c1.center.x)^2 + (p.y - c1.center.y)^2 ≤ c1.radius^2 →
               (p.x - c2.center.x)^2 + (p.y - c2.center.y)^2 ≤ c2.radius^2)

structure Line where
  a : ℝ
  b : ℝ
  c : ℝ
  h : a ≠ 0 ∨ b ≠ 0

def PointOnLine (p : Point) (l : Line) : Prop := l.a * p.x + l.b * p.y + l.c = 0

def LineIsTangentToCircle (l : Line) (c : Circle) : Prop := sorry

def IsExternalTangent (l : Line) (c1 c2 : Circle) : Prop :=
  LineIsTangentToCircle l c1 ∧ LineIsTangentToCircle l c2 ∧ sorry

/-- The external homothetic center of two circles. -/
def EuclideanGeometry.external_homothetic_center (c1 c2 : Circle) : Point := sorry

def Collinear (p1 p2 p3 : Point) : Prop :=
  ∃ (l : Line), PointOnLine p1 l ∧ PointOnLine p2 l ∧ PointOnLine p3 l

/-- Monge's Circle Theorem -/
theorem EuclideanGeometry.monges_circle_theorem (c1 c2 c3 : Circle)
  (h_not_contains : CircleNotContains c1 c2 ∧ CircleNotContains c2 c1 ∧
                    CircleNotContains c1 c3 ∧ CircleNotContains c3 c1 ∧
                    CircleNotContains c2 c3 ∧ CircleNotContains c3 c2)
  (h_distinct_radii : c1.radius ≠ c2.radius ∧ c1.radius ≠ c3.radius ∧ c2.radius ≠ c3.radius) :
  let p1 := EuclideanGeometry.external_homothetic_center c1 c2
  let p2 := EuclideanGeometry.external_homothetic_center c2 c3
  let p3 := EuclideanGeometry.external_homothetic_center c1 c3
  Collinear p1 p2 p3 := by sorry

end EuclideanGeometry
