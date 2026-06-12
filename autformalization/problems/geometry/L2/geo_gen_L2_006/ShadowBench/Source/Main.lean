import Mathlib.Analysis.Normed.Affine.Simplex
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation
import Mathlib.Geometry.Euclidean.Circumcenter

open Module
open scoped Real RealInnerProductSpace BigOperators

/-- The two-dimensional Euclidean plane used by the source statement. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Twice the signed area/orientation determinant of the ordered triangle `P Q R`. -/
noncomputable def twiceSignedArea (P Q R : Plane) : ℝ :=
  (Q 0 - P 0) * (R 1 - P 1) - (Q 1 - P 1) * (R 0 - P 0)

/-- `R` and `S` lie on the same open side of the oriented line through `P` and `Q`. -/
def SameSide (P Q R S : Plane) : Prop :=
  0 < twiceSignedArea P Q R * twiceSignedArea P Q S

/-- `R` and `S` lie on opposite open sides of the oriented line through `P` and `Q`. -/
def OppositeSide (P Q R S : Plane) : Prop :=
  twiceSignedArea P Q R * twiceSignedArea P Q S < 0

/-- A metric predicate for an equilateral triangle. -/
def EquilateralTriangle (P Q R : Plane) : Prop :=
  dist P Q = dist Q R ∧ dist Q R = dist R P

/-- Centroid of three points, written in vector coordinates for `EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def TriangleCentroid (P Q R : Plane) : Plane :=
  (1 / 3 : ℝ) • (P + Q + R)

/-- Configuration for the three internally constructed equilateral triangles in
Napoleon's theorem. -/
def InternalNapoleonConfiguration (A B C D E F : Plane) : Prop :=
  EquilateralTriangle A B D ∧
    EquilateralTriangle B C E ∧
    EquilateralTriangle C A F ∧
    SameSide A B D C ∧
    SameSide B C E A ∧
    SameSide C A F B

/-- Configuration for the three externally constructed equilateral triangles in
Napoleon's theorem. -/
def ExternalNapoleonConfiguration (A B C D E F : Plane) : Prop :=
  EquilateralTriangle A B D ∧
    EquilateralTriangle B C E ∧
    EquilateralTriangle C A F ∧
    OppositeSide A B D C ∧
    OppositeSide B C E A ∧
    OppositeSide C A F B

private lemma plane_dist_sq_eq (P Q : Plane) :
    dist P Q ^ 2 = (P 0 - Q 0) ^ 2 + (P 1 - Q 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  rw [Fin.sum_univ_two]
  simp [Real.dist_eq, sq_abs]

private lemma triangleCentroid_coord (P Q R : Plane) (i : Fin 2) :
    TriangleCentroid P Q R i = (P i + Q i + R i) / 3 := by
  simp [TriangleCentroid]
  ring

private lemma dist_eq_of_sq_eq (P Q R S : Plane)
    (h : dist P Q ^ 2 = dist R S ^ 2) : dist P Q = dist R S := by
  have hcases : dist P Q = dist R S ∨ dist P Q = -dist R S :=
    sq_eq_sq_iff_eq_or_eq_neg.mp h
  rcases hcases with hsame | hopp
  · exact hsame
  · have hPQ : 0 ≤ dist P Q := dist_nonneg
    have hRS : 0 ≤ dist R S := dist_nonneg
    linarith

private lemma equilateral_oriented_vertex_alg (r x y p q T : ℝ)
    (hr : r ^ 2 = 3)
    (h1 : x ^ 2 + y ^ 2 = (x - p) ^ 2 + (y - q) ^ 2)
    (h2 : (x - p) ^ 2 + (y - q) ^ 2 = p ^ 2 + q ^ 2)
    (hsame : 0 < (x * q - y * p) * T)
    (hrT : 0 < r * T) :
    p = x / 2 - r * y / 2 ∧ q = r * x / 2 + y / 2 := by
  let n : ℝ := x ^ 2 + y ^ 2
  let det : ℝ := x * q - y * p
  let target : ℝ := r * n / 2
  have hdot : x * p + y * q = n / 2 := by
    dsimp [n]
    nlinarith [h2]
  have hnorm : p ^ 2 + q ^ 2 = n := by
    dsimp [n]
    nlinarith [h1, h2]
  have hlag : det ^ 2 + (x * p + y * q) ^ 2 = n * (p ^ 2 + q ^ 2) := by
    dsimp [det, n]
    ring
  have hlag' : det ^ 2 + (n / 2) ^ 2 = n * n := by
    rw [hdot, hnorm] at hlag
    exact hlag
  have hdet_sq : det ^ 2 = target ^ 2 := by
    dsimp [target]
    nlinarith [hr, hlag']
  have hdet_ne : det ≠ 0 := by
    intro hzero
    dsimp [det] at hzero
    rw [hzero, zero_mul] at hsame
    linarith
  have hn_nonneg : 0 ≤ n := by
    dsimp [n]
    nlinarith [sq_nonneg x, sq_nonneg y]
  have hn_pos : 0 < n := by
    by_contra hnpos
    have hn0 : n = 0 := by linarith
    have hdet0sq : det ^ 2 = 0 := by
      rw [hdet_sq]
      dsimp [target]
      rw [hn0]
      ring
    have hdet0 : det = 0 := sq_eq_zero_iff.mp hdet0sq
    exact hdet_ne hdet0
  have hn2 : 0 < n / 2 := by nlinarith
  have htargetT : 0 < target * T := by
    have hmul : 0 < (r * T) * (n / 2) := mul_pos hrT hn2
    dsimp [target]
    nlinarith [hmul]
  have hdet_eq : det = target := by
    have hcases : det = target ∨ det = -target := sq_eq_sq_iff_eq_or_eq_neg.mp hdet_sq
    rcases hcases with h | h
    · exact h
    · exfalso
      have hsame' : 0 < det * T := by simpa [det] using hsame
      have hdetT : det * T = -target * T := by rw [h]
      nlinarith
  have hp_mul : n * p = n * (x / 2 - r * y / 2) := by
    calc
      n * p = x * (x * p + y * q) - y * (x * q - y * p) := by
        dsimp [n]
        ring
      _ = x * (n / 2) - y * (r * n / 2) := by
        rw [hdot]
        have hdet_eq' : x * q - y * p = r * n / 2 := by simpa [det, target] using hdet_eq
        rw [hdet_eq']
      _ = n * (x / 2 - r * y / 2) := by ring
  have hq_mul : n * q = n * (r * x / 2 + y / 2) := by
    calc
      n * q = y * (x * p + y * q) + x * (x * q - y * p) := by
        dsimp [n]
        ring
      _ = y * (n / 2) + x * (r * n / 2) := by
        rw [hdot]
        have hdet_eq' : x * q - y * p = r * n / 2 := by simpa [det, target] using hdet_eq
        rw [hdet_eq']
      _ = n * (r * x / 2 + y / 2) := by ring
  constructor
  · exact mul_left_cancel₀ (ne_of_gt hn_pos) hp_mul
  · exact mul_left_cancel₀ (ne_of_gt hn_pos) hq_mul

private lemma equilateral_sameSide_coords (r : ℝ) (P Q R S : Plane)
    (hr : r ^ 2 = 3)
    (heq : EquilateralTriangle P Q R)
    (hside : SameSide P Q R S)
    (hrT : 0 < r * twiceSignedArea P Q S) :
    R 0 = P 0 + ((Q 0 - P 0) / 2 - r * (Q 1 - P 1) / 2) ∧
      R 1 = P 1 + (r * (Q 0 - P 0) / 2 + (Q 1 - P 1) / 2) := by
  have hPQ_QR : dist P Q ^ 2 = dist Q R ^ 2 := by rw [heq.1]
  have hQR_RP : dist Q R ^ 2 = dist R P ^ 2 := by rw [heq.2]
  rw [plane_dist_sq_eq P Q, plane_dist_sq_eq Q R] at hPQ_QR
  rw [plane_dist_sq_eq Q R, plane_dist_sq_eq R P] at hQR_RP
  have h1 : (Q 0 - P 0) ^ 2 + (Q 1 - P 1) ^ 2 =
      ((Q 0 - P 0) - (R 0 - P 0)) ^ 2 + ((Q 1 - P 1) - (R 1 - P 1)) ^ 2 := by
    nlinarith [hPQ_QR]
  have h2 : ((Q 0 - P 0) - (R 0 - P 0)) ^ 2 + ((Q 1 - P 1) - (R 1 - P 1)) ^ 2 =
      (R 0 - P 0) ^ 2 + (R 1 - P 1) ^ 2 := by
    nlinarith [hQR_RP]
  have hside' : 0 <
      (((Q 0 - P 0) * (R 1 - P 1) - (Q 1 - P 1) * (R 0 - P 0)) * twiceSignedArea P Q S) := by
    simpa [SameSide, twiceSignedArea] using hside
  have h := equilateral_oriented_vertex_alg r (Q 0 - P 0) (Q 1 - P 1)
      (R 0 - P 0) (R 1 - P 1) (twiceSignedArea P Q S) hr h1 h2 hside' hrT
  constructor
  · nlinarith [h.1]
  · nlinarith [h.2]

private lemma equilateral_oppositeSide_coords (r : ℝ) (P Q R S : Plane)
    (hr : r ^ 2 = 3)
    (heq : EquilateralTriangle P Q R)
    (hside : OppositeSide P Q R S)
    (hrT : r * twiceSignedArea P Q S < 0) :
    R 0 = P 0 + ((Q 0 - P 0) / 2 - r * (Q 1 - P 1) / 2) ∧
      R 1 = P 1 + (r * (Q 0 - P 0) / 2 + (Q 1 - P 1) / 2) := by
  have hPQ_QR : dist P Q ^ 2 = dist Q R ^ 2 := by rw [heq.1]
  have hQR_RP : dist Q R ^ 2 = dist R P ^ 2 := by rw [heq.2]
  rw [plane_dist_sq_eq P Q, plane_dist_sq_eq Q R] at hPQ_QR
  rw [plane_dist_sq_eq Q R, plane_dist_sq_eq R P] at hQR_RP
  have h1 : (Q 0 - P 0) ^ 2 + (Q 1 - P 1) ^ 2 =
      ((Q 0 - P 0) - (R 0 - P 0)) ^ 2 + ((Q 1 - P 1) - (R 1 - P 1)) ^ 2 := by
    nlinarith [hPQ_QR]
  have h2 : ((Q 0 - P 0) - (R 0 - P 0)) ^ 2 + ((Q 1 - P 1) - (R 1 - P 1)) ^ 2 =
      (R 0 - P 0) ^ 2 + (R 1 - P 1) ^ 2 := by
    nlinarith [hQR_RP]
  have hopp :
      (((Q 0 - P 0) * (R 1 - P 1) - (Q 1 - P 1) * (R 0 - P 0)) * twiceSignedArea P Q S) < 0 := by
    simpa [OppositeSide, twiceSignedArea] using hside
  have hside' : 0 <
      (((Q 0 - P 0) * (R 1 - P 1) - (Q 1 - P 1) * (R 0 - P 0)) *
        (-twiceSignedArea P Q S)) := by
    nlinarith
  have hrT' : 0 < r * (-twiceSignedArea P Q S) := by
    nlinarith
  have h := equilateral_oriented_vertex_alg r (Q 0 - P 0) (Q 1 - P 1)
      (R 0 - P 0) (R 1 - P 1) (-twiceSignedArea P Q S) hr h1 h2 hside' hrT'
  constructor
  · nlinarith [h.1]
  · nlinarith [h.2]

private lemma napoleon_centroid_sq_eq12_alg
    (r a0 a1 b0 b1 c0 c1 d0 d1 e0 e1 f0 f1 : ℝ)
    (hr : r ^ 2 = 3)
    (hd0 : d0 = a0 + ((b0 - a0) / 2 - r * (b1 - a1) / 2))
    (hd1 : d1 = a1 + (r * (b0 - a0) / 2 + (b1 - a1) / 2))
    (he0 : e0 = b0 + ((c0 - b0) / 2 - r * (c1 - b1) / 2))
    (he1 : e1 = b1 + (r * (c0 - b0) / 2 + (c1 - b1) / 2))
    (hf0 : f0 = c0 + ((a0 - c0) / 2 - r * (a1 - c1) / 2))
    (hf1 : f1 = c1 + (r * (a0 - c0) / 2 + (a1 - c1) / 2)) :
    ((a0 + b0 + d0) / 3 - (b0 + c0 + e0) / 3) ^ 2 +
        ((a1 + b1 + d1) / 3 - (b1 + c1 + e1) / 3) ^ 2 =
      ((b0 + c0 + e0) / 3 - (c0 + a0 + f0) / 3) ^ 2 +
        ((b1 + c1 + e1) / 3 - (c1 + a1 + f1) / 3) ^ 2 := by
  subst d0
  subst d1
  subst e0
  subst e1
  subst f0
  subst f1
  ring_nf
  rw [hr]
  ring

private lemma napoleon_centroid_sq_eq23_alg
    (r a0 a1 b0 b1 c0 c1 d0 d1 e0 e1 f0 f1 : ℝ)
    (hr : r ^ 2 = 3)
    (hd0 : d0 = a0 + ((b0 - a0) / 2 - r * (b1 - a1) / 2))
    (hd1 : d1 = a1 + (r * (b0 - a0) / 2 + (b1 - a1) / 2))
    (he0 : e0 = b0 + ((c0 - b0) / 2 - r * (c1 - b1) / 2))
    (he1 : e1 = b1 + (r * (c0 - b0) / 2 + (c1 - b1) / 2))
    (hf0 : f0 = c0 + ((a0 - c0) / 2 - r * (a1 - c1) / 2))
    (hf1 : f1 = c1 + (r * (a0 - c0) / 2 + (a1 - c1) / 2)) :
      ((b0 + c0 + e0) / 3 - (c0 + a0 + f0) / 3) ^ 2 +
        ((b1 + c1 + e1) / 3 - (c1 + a1 + f1) / 3) ^ 2 =
      ((c0 + a0 + f0) / 3 - (a0 + b0 + d0) / 3) ^ 2 +
        ((c1 + a1 + f1) / 3 - (a1 + b1 + d1) / 3) ^ 2 := by
  subst d0
  subst d1
  subst e0
  subst e1
  subst f0
  subst f1
  ring_nf
  rw [hr]
  ring

/--
Source theorem `thm:napoleon_inner` (`napoleons_theorem_inner`): for non-collinear
points `A B C`, build equilateral triangles on `AB`, `BC`, and `CA` internally;
their centroids form an equilateral triangle.

Proof sketch / prover notes: The source gives no proof. Use coordinates or the
standard complex-plane proof of Napoleon's theorem. The predicates above encode
"internal" by requiring the third vertices `D E F` to lie on the same open side
of the relevant side as the opposite vertex of `ABC`. With this common
orientation, express the third vertices by rotation through `± π / 3`, expand the
three centroid differences, and use that rotation by sixty degrees is an isometry
to prove the three resulting distances equal.
-/
theorem napoleons_theorem_inner (A B C : Plane)
    (h_noncol : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    ∀ D E F : Plane,
      InternalNapoleonConfiguration A B C D E F →
        EquilateralTriangle (TriangleCentroid A B D)
          (TriangleCentroid B C E)
          (TriangleCentroid C A F) := by
  intro D E F hcfg
  have _h_noncol_used := h_noncol
  rcases hcfg with ⟨hD, hE, hF, hDside, hEside, hFside⟩
  let T : ℝ := twiceSignedArea A B C
  have hT_def : T = twiceSignedArea A B C := rfl
  have hT_ne : T ≠ 0 := by
    intro hT0
    have h := hDside
    dsimp [SameSide] at h
    rw [← hT_def, hT0, mul_zero] at h
    linarith
  let r : ℝ := if 0 < T then Real.sqrt 3 else -Real.sqrt 3
  have hsqrt_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hsqrt_pos : 0 < Real.sqrt 3 := Real.sqrt_pos_of_pos (by norm_num)
  have hr : r ^ 2 = 3 := by
    dsimp [r]
    by_cases hpos : 0 < T
    · rw [if_pos hpos]
      exact hsqrt_sq
    · rw [if_neg hpos]
      calc
        (-Real.sqrt 3) ^ 2 = (Real.sqrt 3) ^ 2 := by ring
        _ = 3 := hsqrt_sq
  have hrT : 0 < r * T := by
    dsimp [r]
    by_cases hpos : 0 < T
    · rw [if_pos hpos]
      exact mul_pos hsqrt_pos hpos
    · rw [if_neg hpos]
      have hT_le : T ≤ 0 := le_of_not_gt hpos
      have hT_neg : T < 0 := lt_of_le_of_ne hT_le hT_ne
      have hsqrt_neg : -Real.sqrt 3 < 0 := by linarith
      exact mul_pos_of_neg_of_neg hsqrt_neg hT_neg
  have hBCA : twiceSignedArea B C A = T := by
    dsimp [T, twiceSignedArea]
    ring
  have hCAB : twiceSignedArea C A B = T := by
    dsimp [T, twiceSignedArea]
    ring
  have hrBCA : 0 < r * twiceSignedArea B C A := by
    rw [hBCA]
    exact hrT
  have hrCAB : 0 < r * twiceSignedArea C A B := by
    rw [hCAB]
    exact hrT
  have hDcoord := equilateral_sameSide_coords r A B D C hr hD hDside hrT
  have hEcoord := equilateral_sameSide_coords r B C E A hr hE hEside hrBCA
  have hFcoord := equilateral_sameSide_coords r C A F B hr hF hFside hrCAB
  have hsq12 :
      dist (TriangleCentroid A B D) (TriangleCentroid B C E) ^ 2 =
        dist (TriangleCentroid B C E) (TriangleCentroid C A F) ^ 2 := by
    rw [plane_dist_sq_eq, plane_dist_sq_eq]
    simp only [triangleCentroid_coord]
    exact napoleon_centroid_sq_eq12_alg r (A 0) (A 1) (B 0) (B 1) (C 0) (C 1)
      (D 0) (D 1) (E 0) (E 1) (F 0) (F 1) hr
      hDcoord.1 hDcoord.2 hEcoord.1 hEcoord.2 hFcoord.1 hFcoord.2
  have hsq23 :
      dist (TriangleCentroid B C E) (TriangleCentroid C A F) ^ 2 =
        dist (TriangleCentroid C A F) (TriangleCentroid A B D) ^ 2 := by
    rw [plane_dist_sq_eq, plane_dist_sq_eq]
    simp only [triangleCentroid_coord]
    exact napoleon_centroid_sq_eq23_alg r (A 0) (A 1) (B 0) (B 1) (C 0) (C 1)
      (D 0) (D 1) (E 0) (E 1) (F 0) (F 1) hr
      hDcoord.1 hDcoord.2 hEcoord.1 hEcoord.2 hFcoord.1 hFcoord.2
  exact ⟨dist_eq_of_sq_eq _ _ _ _ hsq12, dist_eq_of_sq_eq _ _ _ _ hsq23⟩

/--
Source theorem `thm:napoleon_outer` (`napoleons_theorem_outer`): for non-collinear
points `A B C`, build equilateral triangles on `AB`, `BC`, and `CA` externally;
their centroids form an equilateral triangle.

Proof sketch / prover notes: The source gives no proof. This is the same
coordinate/rotation argument as the internal theorem, with the opposite common
orientation. The predicates above encode "external" by putting each third vertex
on the opposite open side of the corresponding side from the remaining vertex of
`ABC`. After translating to rotations by the other sign of `π / 3`, the
centroid-difference identities are the same up to sign/rotation, so the three
distances are equal.
-/
theorem napoleons_theorem_outer (A B C : Plane)
    (h_noncol : ¬ Collinear ℝ ({A, B, C} : Set Plane)) :
    ∀ D E F : Plane,
      ExternalNapoleonConfiguration A B C D E F →
        EquilateralTriangle (TriangleCentroid A B D)
          (TriangleCentroid B C E)
          (TriangleCentroid C A F) := by
  intro D E F hcfg
  have _h_noncol_used := h_noncol
  rcases hcfg with ⟨hD, hE, hF, hDside, hEside, hFside⟩
  let T : ℝ := twiceSignedArea A B C
  have hT_def : T = twiceSignedArea A B C := rfl
  have hT_ne : T ≠ 0 := by
    intro hT0
    have h := hDside
    dsimp [OppositeSide] at h
    rw [← hT_def, hT0, mul_zero] at h
    linarith
  let r : ℝ := if 0 < T then -Real.sqrt 3 else Real.sqrt 3
  have hsqrt_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hsqrt_pos : 0 < Real.sqrt 3 := Real.sqrt_pos_of_pos (by norm_num)
  have hr : r ^ 2 = 3 := by
    dsimp [r]
    by_cases hpos : 0 < T
    · rw [if_pos hpos]
      calc
        (-Real.sqrt 3) ^ 2 = (Real.sqrt 3) ^ 2 := by ring
        _ = 3 := hsqrt_sq
    · rw [if_neg hpos]
      exact hsqrt_sq
  have hrT : r * T < 0 := by
    dsimp [r]
    by_cases hpos : 0 < T
    · rw [if_pos hpos]
      have hsqrt_neg : -Real.sqrt 3 < 0 := by linarith
      exact mul_neg_of_neg_of_pos hsqrt_neg hpos
    · rw [if_neg hpos]
      have hT_le : T ≤ 0 := le_of_not_gt hpos
      have hT_neg : T < 0 := lt_of_le_of_ne hT_le hT_ne
      exact mul_neg_of_pos_of_neg hsqrt_pos hT_neg
  have hBCA : twiceSignedArea B C A = T := by
    dsimp [T, twiceSignedArea]
    ring
  have hCAB : twiceSignedArea C A B = T := by
    dsimp [T, twiceSignedArea]
    ring
  have hrBCA : r * twiceSignedArea B C A < 0 := by
    rw [hBCA]
    exact hrT
  have hrCAB : r * twiceSignedArea C A B < 0 := by
    rw [hCAB]
    exact hrT
  have hDcoord := equilateral_oppositeSide_coords r A B D C hr hD hDside hrT
  have hEcoord := equilateral_oppositeSide_coords r B C E A hr hE hEside hrBCA
  have hFcoord := equilateral_oppositeSide_coords r C A F B hr hF hFside hrCAB
  have hsq12 :
      dist (TriangleCentroid A B D) (TriangleCentroid B C E) ^ 2 =
        dist (TriangleCentroid B C E) (TriangleCentroid C A F) ^ 2 := by
    rw [plane_dist_sq_eq, plane_dist_sq_eq]
    simp only [triangleCentroid_coord]
    exact napoleon_centroid_sq_eq12_alg r (A 0) (A 1) (B 0) (B 1) (C 0) (C 1)
      (D 0) (D 1) (E 0) (E 1) (F 0) (F 1) hr
      hDcoord.1 hDcoord.2 hEcoord.1 hEcoord.2 hFcoord.1 hFcoord.2
  have hsq23 :
      dist (TriangleCentroid B C E) (TriangleCentroid C A F) ^ 2 =
        dist (TriangleCentroid C A F) (TriangleCentroid A B D) ^ 2 := by
    rw [plane_dist_sq_eq, plane_dist_sq_eq]
    simp only [triangleCentroid_coord]
    exact napoleon_centroid_sq_eq23_alg r (A 0) (A 1) (B 0) (B 1) (C 0) (C 1)
      (D 0) (D 1) (E 0) (E 1) (F 0) (F 1) hr
      hDcoord.1 hDcoord.2 hEcoord.1 hEcoord.2 hFcoord.1 hFcoord.2
  exact ⟨dist_eq_of_sq_eq _ _ _ _ hsq12, dist_eq_of_sq_eq _ _ _ _ hsq23⟩
