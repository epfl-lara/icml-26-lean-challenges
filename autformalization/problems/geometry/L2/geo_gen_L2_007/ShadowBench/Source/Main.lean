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

private lemma isCyclicQuadrilateral_cospherical {A B C D : Brahmagupta.Point}
    (h : Brahmagupta.IsCyclicQuadrilateral A B C D) :
    EuclideanGeometry.Cospherical ({A, B, C, D} : Set Brahmagupta.Point) := by
  rcases h with ⟨O, r, _hr, hA, hB, hC, hD⟩
  rw [EuclideanGeometry.cospherical_def]
  refine ⟨O, r, ?_⟩
  intro P hP
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
  rcases hP with hP | hP | hP | hP
  · simpa [hP] using hA
  · simpa [hP] using hB
  · simpa [hP] using hC
  · simpa [hP] using hD

private lemma nonneg_eq_sqrt_of_sq_eq {x y : ℝ} (hx : 0 ≤ x) (hxy : x ^ 2 = y) :
    x = Real.sqrt y := by
  rw [← hxy]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hx]

private lemma quadrilateralArea_nonneg (A B C D : Brahmagupta.Point) :
    0 ≤ Brahmagupta.quadrilateralArea A B C D := by
  unfold Brahmagupta.quadrilateralArea Brahmagupta.triangleArea
  positivity

private lemma twiceArea_cyclic (P Q R : Brahmagupta.Point) :
    Brahmagupta.twiceOrientedTriangleArea P Q R =
      Brahmagupta.twiceOrientedTriangleArea Q R P := by
  unfold Brahmagupta.twiceOrientedTriangleArea Brahmagupta.xCoord Brahmagupta.yCoord
  ring

private lemma twiceArea_cyclic_two (P Q R : Brahmagupta.Point) :
    Brahmagupta.twiceOrientedTriangleArea P Q R =
      Brahmagupta.twiceOrientedTriangleArea R P Q := by
  unfold Brahmagupta.twiceOrientedTriangleArea Brahmagupta.xCoord Brahmagupta.yCoord
  ring

private lemma twiceArea_add_diag (A B C D : Brahmagupta.Point) :
    Brahmagupta.twiceOrientedTriangleArea A B C +
      Brahmagupta.twiceOrientedTriangleArea A C D =
    Brahmagupta.twiceOrientedTriangleArea A B D +
      Brahmagupta.twiceOrientedTriangleArea B C D := by
  unfold Brahmagupta.twiceOrientedTriangleArea Brahmagupta.xCoord Brahmagupta.yCoord
  ring

private lemma diagonal_intersection_point_eq (A B C D : Brahmagupta.Point)
    (hden : Brahmagupta.twiceOrientedTriangleArea A B C +
        Brahmagupta.twiceOrientedTriangleArea A C D ≠ 0) :
    (AffineMap.lineMap A C)
        (Brahmagupta.twiceOrientedTriangleArea A B D /
          (Brahmagupta.twiceOrientedTriangleArea A B C +
            Brahmagupta.twiceOrientedTriangleArea A C D)) =
      (AffineMap.lineMap B D)
        (Brahmagupta.twiceOrientedTriangleArea A B C /
          (Brahmagupta.twiceOrientedTriangleArea A B C +
            Brahmagupta.twiceOrientedTriangleArea A C D)) := by
  apply PiLp.ext
  intro i
  fin_cases i
  · simp [AffineMap.lineMap_apply]
    field_simp [hden]
    unfold Brahmagupta.twiceOrientedTriangleArea Brahmagupta.xCoord Brahmagupta.yCoord
    ring
  · simp [AffineMap.lineMap_apply]
    field_simp [hden]
    unfold Brahmagupta.twiceOrientedTriangleArea Brahmagupta.xCoord Brahmagupta.yCoord
    ring

private lemma convex_diagonals_sbtw (A B C D : Brahmagupta.Point)
    (h_convex : Brahmagupta.IsConvexQuadrilateralInOrder A B C D) :
    ∃ p, Sbtw ℝ A p C ∧ Sbtw ℝ B p D := by
  rcases h_convex with hpos | hneg
  · rcases hpos with ⟨hABC, hBCD, hCDA, hDAB⟩
    let den := Brahmagupta.twiceOrientedTriangleArea A B C +
      Brahmagupta.twiceOrientedTriangleArea A C D
    let t := Brahmagupta.twiceOrientedTriangleArea A B D / den
    let u := Brahmagupta.twiceOrientedTriangleArea A B C / den
    have hACD : 0 < Brahmagupta.twiceOrientedTriangleArea A C D := by
      simpa [twiceArea_cyclic_two] using hCDA
    have hABD : 0 < Brahmagupta.twiceOrientedTriangleArea A B D := by
      simpa [twiceArea_cyclic] using hDAB
    have hden_pos : 0 < den := by
      dsimp [den]
      nlinarith
    have hden_ne : den ≠ 0 := ne_of_gt hden_pos
    have hden_eq : den = Brahmagupta.twiceOrientedTriangleArea A B D +
        Brahmagupta.twiceOrientedTriangleArea B C D := by
      dsimp [den]
      rw [twiceArea_add_diag]
    have hAC_ne : A ≠ C := by
      intro hAC
      subst C
      unfold Brahmagupta.twiceOrientedTriangleArea Brahmagupta.xCoord Brahmagupta.yCoord at hABC
      nlinarith
    have hBD_ne : B ≠ D := by
      intro hBD
      subst D
      unfold Brahmagupta.twiceOrientedTriangleArea Brahmagupta.xCoord Brahmagupta.yCoord at hBCD
      nlinarith
    refine ⟨(AffineMap.lineMap A C) t, ?_, ?_⟩
    · rw [sbtw_lineMap_iff]
      refine ⟨hAC_ne, ?_⟩
      constructor
      · dsimp [t]
        exact div_pos hABD hden_pos
      · dsimp [t]
        rw [div_lt_one hden_pos]
        nlinarith
    · have hp : (AffineMap.lineMap A C) t = (AffineMap.lineMap B D) u := by
        dsimp [t, u, den]
        exact diagonal_intersection_point_eq A B C D (by simpa [den] using hden_ne)
      rw [hp]
      rw [sbtw_lineMap_iff]
      refine ⟨hBD_ne, ?_⟩
      constructor
      · dsimp [u]
        exact div_pos hABC hden_pos
      · dsimp [u]
        rw [div_lt_one hden_pos]
        nlinarith
  · rcases hneg with ⟨hABC, hBCD, hCDA, hDAB⟩
    let den := Brahmagupta.twiceOrientedTriangleArea A B C +
      Brahmagupta.twiceOrientedTriangleArea A C D
    let t := Brahmagupta.twiceOrientedTriangleArea A B D / den
    let u := Brahmagupta.twiceOrientedTriangleArea A B C / den
    have hACD : Brahmagupta.twiceOrientedTriangleArea A C D < 0 := by
      simpa [twiceArea_cyclic_two] using hCDA
    have hABD : Brahmagupta.twiceOrientedTriangleArea A B D < 0 := by
      simpa [twiceArea_cyclic] using hDAB
    have hden_neg : den < 0 := by
      dsimp [den]
      nlinarith
    have hden_ne : den ≠ 0 := ne_of_lt hden_neg
    have hden_eq : den = Brahmagupta.twiceOrientedTriangleArea A B D +
        Brahmagupta.twiceOrientedTriangleArea B C D := by
      dsimp [den]
      rw [twiceArea_add_diag]
    have hAC_ne : A ≠ C := by
      intro hAC
      subst C
      unfold Brahmagupta.twiceOrientedTriangleArea Brahmagupta.xCoord Brahmagupta.yCoord at hABC
      nlinarith
    have hBD_ne : B ≠ D := by
      intro hBD
      subst D
      unfold Brahmagupta.twiceOrientedTriangleArea Brahmagupta.xCoord Brahmagupta.yCoord at hBCD
      nlinarith
    refine ⟨(AffineMap.lineMap A C) t, ?_, ?_⟩
    · rw [sbtw_lineMap_iff]
      refine ⟨hAC_ne, ?_⟩
      constructor
      · dsimp [t]
        exact div_pos_of_neg_of_neg hABD hden_neg
      · dsimp [t]
        rw [div_lt_one_of_neg hden_neg]
        nlinarith
    · have hp : (AffineMap.lineMap A C) t = (AffineMap.lineMap B D) u := by
        dsimp [t, u, den]
        exact diagonal_intersection_point_eq A B C D (by simpa [den] using hden_ne)
      rw [hp]
      rw [sbtw_lineMap_iff]
      refine ⟨hBD_ne, ?_⟩
      constructor
      · dsimp [u]
        exact div_pos_of_neg_of_neg hABC hden_neg
      · dsimp [u]
        rw [div_lt_one_of_neg hden_neg]
        nlinarith

private lemma brahmagupta_ptolemy
    (A B C D : Brahmagupta.Point)
    (h_cyclic : Brahmagupta.IsCyclicQuadrilateral A B C D)
    (h_convex : Brahmagupta.IsConvexQuadrilateralInOrder A B C D) :
    dist A C * dist B D = dist A B * dist C D + dist B C * dist D A := by
  rcases convex_diagonals_sbtw A B C D h_convex with ⟨p, hpAC, hpBD⟩
  have hcos := isCyclicQuadrilateral_cospherical h_cyclic
  have hangleAC : EuclideanGeometry.angle A p C = Real.pi :=
    EuclideanGeometry.angle_eq_pi_iff_sbtw.mpr hpAC
  have hangleBD : EuclideanGeometry.angle B p D = Real.pi :=
    EuclideanGeometry.angle_eq_pi_iff_sbtw.mpr hpBD
  exact (EuclideanGeometry.mul_dist_add_mul_dist_eq_mul_dist_of_cospherical
    hcos hangleAC hangleBD).symm

private lemma dist_sq_coords (P Q : Brahmagupta.Point) :
    dist P Q ^ 2 = (Brahmagupta.xCoord P - Brahmagupta.xCoord Q) ^ 2 +
      (Brahmagupta.yCoord P - Brahmagupta.yCoord Q) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp [Fin.sum_univ_two, Brahmagupta.xCoord, Brahmagupta.yCoord, Real.dist_eq, sq_abs,
    sub_eq_add_neg]

private lemma quadrilateral_det_sq_identity (A B C D : Brahmagupta.Point) :
    (Brahmagupta.twiceOrientedTriangleArea A B C +
        Brahmagupta.twiceOrientedTriangleArea A C D) ^ 2 / 4 =
      (4 * ((dist A C * dist B D) ^ 2) -
          ((dist A B) ^ 2 + (dist C D) ^ 2 - (dist B C) ^ 2 - (dist D A) ^ 2) ^ 2) / 16 := by
  rw [mul_pow]
  repeat rw [dist_sq_coords]
  unfold Brahmagupta.twiceOrientedTriangleArea Brahmagupta.xCoord Brahmagupta.yCoord
  ring

private lemma quadrilateralArea_sq_det (A B C D : Brahmagupta.Point)
    (h_convex : Brahmagupta.IsConvexQuadrilateralInOrder A B C D) :
    Brahmagupta.quadrilateralArea A B C D ^ 2 =
      (Brahmagupta.twiceOrientedTriangleArea A B C +
        Brahmagupta.twiceOrientedTriangleArea A C D) ^ 2 / 4 := by
  rcases h_convex with hpos | hneg
  · rcases hpos with ⟨hABC, _hBCD, hCDA, _hDAB⟩
    have hACD : 0 < Brahmagupta.twiceOrientedTriangleArea A C D := by
      simpa [twiceArea_cyclic_two] using hCDA
    unfold Brahmagupta.quadrilateralArea Brahmagupta.triangleArea
    rw [abs_of_pos hABC, abs_of_pos hACD]
    ring
  · rcases hneg with ⟨hABC, _hBCD, hCDA, _hDAB⟩
    have hACD : Brahmagupta.twiceOrientedTriangleArea A C D < 0 := by
      simpa [twiceArea_cyclic_two] using hCDA
    unfold Brahmagupta.quadrilateralArea Brahmagupta.triangleArea
    rw [abs_of_neg hABC, abs_of_neg hACD]
    ring

private lemma convex_quadrilateralArea_sq_diagonals
    (A B C D : Brahmagupta.Point)
    (h_convex : Brahmagupta.IsConvexQuadrilateralInOrder A B C D) :
    Brahmagupta.quadrilateralArea A B C D ^ 2 =
      (4 * ((dist A C * dist B D) ^ 2) -
          ((dist A B) ^ 2 + (dist C D) ^ 2 - (dist B C) ^ 2 - (dist D A) ^ 2) ^ 2) / 16 := by
  rw [quadrilateralArea_sq_det A B C D h_convex]
  exact quadrilateral_det_sq_identity A B C D

private lemma brahmagupta_area_sq_opposite_sides
    (A B C D : Brahmagupta.Point)
    (h_cyclic : Brahmagupta.IsCyclicQuadrilateral A B C D)
    (h_convex : Brahmagupta.IsConvexQuadrilateralInOrder A B C D) :
    Brahmagupta.quadrilateralArea A B C D ^ 2 =
      (4 * ((dist A B * dist C D + dist B C * dist D A) ^ 2) -
          ((dist A B) ^ 2 + (dist C D) ^ 2 - (dist B C) ^ 2 - (dist D A) ^ 2) ^ 2) / 16 := by
  rw [convex_quadrilateralArea_sq_diagonals A B C D h_convex]
  rw [brahmagupta_ptolemy A B C D h_cyclic h_convex]

private lemma brahmagupta_opposite_sides_algebra (a b c d : ℝ) :
    (4 * ((a * c + b * d) ^ 2) -
        (a ^ 2 + c ^ 2 - b ^ 2 - d ^ 2) ^ 2) / 16 =
      (((a + b + c + d) / 2 - a) *
        ((a + b + c + d) / 2 - b) *
        ((a + b + c + d) / 2 - c) *
        ((a + b + c + d) / 2 - d)) := by
  ring

private lemma brahmagupta_area_sq_semiperimeter
    (A B C D : Brahmagupta.Point)
    (h_cyclic : Brahmagupta.IsCyclicQuadrilateral A B C D)
    (h_convex : Brahmagupta.IsConvexQuadrilateralInOrder A B C D) :
    let a := dist A B
    let b := dist B C
    let c := dist C D
    let d := dist D A
    let s := (a + b + c + d) / 2
    Brahmagupta.quadrilateralArea A B C D ^ 2 =
      (s - a) * (s - b) * (s - c) * (s - d) := by
  dsimp
  rw [brahmagupta_area_sq_opposite_sides A B C D h_cyclic h_convex]
  simpa using brahmagupta_opposite_sides_algebra (dist A B) (dist B C) (dist C D) (dist D A)

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
  dsimp
  apply nonneg_eq_sqrt_of_sq_eq
  · rw [h_area]
    exact quadrilateralArea_nonneg A B C D
  · rw [h_area]
    exact brahmagupta_area_sq_semiperimeter A B C D h_cyclic h_convex
