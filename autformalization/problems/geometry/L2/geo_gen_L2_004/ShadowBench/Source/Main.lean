import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Sphere.Ptolemy
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Real.Sqrt

/-!
ShadowBench problem: `geometry/L2/geo_gen_L2_004` (Casey's theorem).
Source: `docs/source.tex`; Blueprint: `ShadowBench/Source/Blueprint.md`.

All declarations for this problem are consolidated into this single file (Main.lean):
the analytic-plane basics, the configuration constructions, and the two source
theorems. Required declaration names: `EuclideanGeometry.external_tangent_length`,
`EuclideanGeometry.circlePoint`, `EuclideanGeometry.caseys_theorem`.
-/

/-!
Basic analytic-plane definitions for the Casey theorem formalization.
-/

namespace EuclideanGeometry

/-- Analytic points in the real Euclidean plane used for this source formalization. -/
abbrev Point : Type := ℝ × ℝ

/-- Squared Euclidean distance in the analytic plane. -/
def sqDist (p q : Point) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/--
The point set of the circle with the given center and radius, represented in the
analytic plane by the squared-distance equation.
-/
def circlePoint (center : Point) (radius : ℝ) : Set Point :=
  {p | sqDist p center = radius ^ 2}

/--
The length of the exterior common bitangent segment of two circles in the analytic
center/radius model.
-/
noncomputable def external_tangent_length (c₁ c₂ : Point) (r₁ r₂ : ℝ) : ℝ :=
  Real.sqrt (sqDist c₁ c₂ - (r₁ - r₂) ^ 2)

/-- Ordinary analytic distance between two points, used for the degenerate Ptolemy bridge. -/
noncomputable def pointDistance (p q : Point) : ℝ :=
  Real.sqrt (sqDist p q)

/-- Ptolemy's equality for four points in the analytic plane. -/
noncomputable def ptolemyEquality (p₁ p₂ p₃ p₄ : Point) : Prop :=
  let d₁₂ := pointDistance p₁ p₂
  let d₁₃ := pointDistance p₁ p₃
  let d₁₄ := pointDistance p₁ p₄
  let d₂₃ := pointDistance p₂ p₃
  let d₂₄ := pointDistance p₂ p₄
  let d₃₄ := pointDistance p₃ p₄
  d₁₂ * d₃₄ + d₁₄ * d₂₃ = d₁₃ * d₂₄

/-- Signed area/orientation determinant for three analytic points. -/
def orientation (a b c : Point) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Strict cyclic order of four points, allowing either orientation. -/
def strictlyCyclicallyOrdered (p₁ p₂ p₃ p₄ : Point) : Prop :=
  (0 < orientation p₁ p₂ p₃ ∧
    0 < orientation p₂ p₃ p₄ ∧
    0 < orientation p₃ p₄ p₁ ∧
    0 < orientation p₄ p₁ p₂) ∨
  (orientation p₁ p₂ p₃ < 0 ∧
    orientation p₂ p₃ p₄ < 0 ∧
    orientation p₃ p₄ p₁ < 0 ∧
    orientation p₄ p₁ p₂ < 0)

end EuclideanGeometry

/-!
Configuration predicates and constructions for the Casey theorem formalization.
-/

namespace EuclideanGeometry

/--
For an inner circle tangent internally to an outer circle, this is the radial contact
point on the outer circle determined by the two centers and radii.
-/
noncomputable def radialContactPoint (outerCenter : Point) (outerRadius : ℝ)
    (innerCenter : Point) (innerRadius : ℝ) : Point :=
  let scale := outerRadius / (outerRadius - innerRadius)
  (outerCenter.1 + scale * (innerCenter.1 - outerCenter.1),
    outerCenter.2 + scale * (innerCenter.2 - outerCenter.2))

/--
The source phrase that the four inner circles are “in that order”, encoded as strict
cyclic order of their radial contact points on the outer circle.
-/
noncomputable def caseyInOrder (outerCenter : Point) (outerRadius : ℝ)
    (c₁ c₂ c₃ c₄ : Point) (r₁ r₂ r₃ r₄ : ℝ) : Prop :=
  strictlyCyclicallyOrdered
    (radialContactPoint outerCenter outerRadius c₁ r₁)
    (radialContactPoint outerCenter outerRadius c₂ r₂)
    (radialContactPoint outerCenter outerRadius c₃ r₃)
    (radialContactPoint outerCenter outerRadius c₄ r₄)

/--
An inner circle lies inside and is tangent to an outer circle: nonnegative inner radius,
strictly smaller than the outer radius, and center distance equal to `outerRadius - innerRadius`.
The zero-radius case covers the source's degenerate point-circle note.
-/
def liesInsideAndTangentTo (innerCenter outerCenter : Point)
    (innerRadius outerRadius : ℝ) : Prop :=
  0 ≤ innerRadius ∧ innerRadius < outerRadius ∧
    sqDist innerCenter outerCenter = (outerRadius - innerRadius) ^ 2

/-- Strict pairwise nonintersection of two circular disks in the center/radius model. -/
def nonintersectingCircles (c₁ c₂ : Point) (r₁ r₂ : ℝ) : Prop :=
  0 ≤ r₁ ∧ 0 ≤ r₂ ∧ (r₁ + r₂) ^ 2 < sqDist c₁ c₂

/-- The six pairwise nonintersection conditions for four circles. -/
def fourCirclesNonintersecting (c₁ c₂ c₃ c₄ : Point) (r₁ r₂ r₃ r₄ : ℝ) : Prop :=
  nonintersectingCircles c₁ c₂ r₁ r₂ ∧
    nonintersectingCircles c₁ c₃ r₁ r₃ ∧
    nonintersectingCircles c₁ c₄ r₁ r₄ ∧
    nonintersectingCircles c₂ c₃ r₂ r₃ ∧
    nonintersectingCircles c₂ c₄ r₂ r₄ ∧
    nonintersectingCircles c₃ c₄ r₃ r₄

end EuclideanGeometry

/-- The positive radial gap of an internally tangent inner circle. -/
private lemma casey_gap_pos_of_liesInside
    {innerCenter outerCenter : EuclideanGeometry.Point} {innerRadius outerRadius : ℝ}
    (h : EuclideanGeometry.liesInsideAndTangentTo innerCenter outerCenter innerRadius outerRadius) :
    0 < outerRadius - innerRadius := by
  rcases h with ⟨_, hlt, _⟩
  linarith

/-- The radicand defining an exterior tangent length is strictly positive for
strictly nonintersecting nonnegative-radius circles. -/
private lemma casey_tangent_radicand_pos_of_nonintersecting
    {c₁ c₂ : EuclideanGeometry.Point} {r₁ r₂ : ℝ}
    (h : EuclideanGeometry.nonintersectingCircles c₁ c₂ r₁ r₂) :
    0 < EuclideanGeometry.sqDist c₁ c₂ - (r₁ - r₂) ^ 2 := by
  rcases h with ⟨hr₁, hr₂, hsep⟩
  have hsq : (r₁ - r₂) ^ 2 ≤ (r₁ + r₂) ^ 2 := by
    have hmul : 0 ≤ r₁ * r₂ := mul_nonneg hr₁ hr₂
    nlinarith
  linarith

/-- Pure algebraic last step for Casey's equality: if each of the six tangent
lengths is a product of endpoint scale factors and a chord length, then Ptolemy
for the six chord lengths gives the required Casey product identity. -/
private lemma caseys_scaled_ptolemy_algebra
    (s₁ s₂ s₃ s₄ : ℝ)
    (t₁₂ t₁₃ t₁₄ t₂₃ t₂₄ t₃₄ c₁₂ c₁₃ c₁₄ c₂₃ c₂₄ c₃₄ : ℝ)
    (h₁₂ : t₁₂ = s₁ * s₂ * c₁₂)
    (h₁₃ : t₁₃ = s₁ * s₃ * c₁₃)
    (h₁₄ : t₁₄ = s₁ * s₄ * c₁₄)
    (h₂₃ : t₂₃ = s₂ * s₃ * c₂₃)
    (h₂₄ : t₂₄ = s₂ * s₄ * c₂₄)
    (h₃₄ : t₃₄ = s₃ * s₄ * c₃₄)
    (hP : c₁₂ * c₃₄ + c₁₄ * c₂₃ = c₁₃ * c₂₄) :
    t₁₂ * t₃₄ + t₁₄ * t₂₃ = t₁₃ * t₂₄ := by
  rw [h₁₂, h₁₃, h₁₄, h₂₃, h₂₄, h₃₄]
  calc
    (s₁ * s₂ * c₁₂) * (s₃ * s₄ * c₃₄) +
        (s₁ * s₄ * c₁₄) * (s₂ * s₃ * c₂₃)
        = s₁ * s₂ * s₃ * s₄ * (c₁₂ * c₃₄ + c₁₄ * c₂₃) := by ring
    _ = s₁ * s₂ * s₃ * s₄ * (c₁₃ * c₂₄) := by rw [hP]
    _ = (s₁ * s₃ * c₁₃) * (s₂ * s₄ * c₂₄) := by ring

/-- The same algebraic reduction, specialized to the exact let-bound shape of
`caseys_theorem`.  The remaining geometric work is to supply the six scaling
identities and the Ptolemy equality for the contact-point chords. -/
private lemma caseys_theorem_of_scale_data
    (O₁ O₂ O₃ O₄ : EuclideanGeometry.Point) (r₁ r₂ r₃ r₄ : ℝ)
    (s₁ s₂ s₃ s₄ c₁₂ c₁₃ c₁₄ c₂₃ c₂₄ c₃₄ : ℝ)
    (h₁₂ : EuclideanGeometry.external_tangent_length O₁ O₂ r₁ r₂ = s₁ * s₂ * c₁₂)
    (h₁₃ : EuclideanGeometry.external_tangent_length O₁ O₃ r₁ r₃ = s₁ * s₃ * c₁₃)
    (h₁₄ : EuclideanGeometry.external_tangent_length O₁ O₄ r₁ r₄ = s₁ * s₄ * c₁₄)
    (h₂₃ : EuclideanGeometry.external_tangent_length O₂ O₃ r₂ r₃ = s₂ * s₃ * c₂₃)
    (h₂₄ : EuclideanGeometry.external_tangent_length O₂ O₄ r₂ r₄ = s₂ * s₄ * c₂₄)
    (h₃₄ : EuclideanGeometry.external_tangent_length O₃ O₄ r₃ r₄ = s₃ * s₄ * c₃₄)
    (hP : c₁₂ * c₃₄ + c₁₄ * c₂₃ = c₁₃ * c₂₄) :
    let t₁₂ := EuclideanGeometry.external_tangent_length O₁ O₂ r₁ r₂
    let t₁₃ := EuclideanGeometry.external_tangent_length O₁ O₃ r₁ r₃
    let t₁₄ := EuclideanGeometry.external_tangent_length O₁ O₄ r₁ r₄
    let t₂₃ := EuclideanGeometry.external_tangent_length O₂ O₃ r₂ r₃
    let t₂₄ := EuclideanGeometry.external_tangent_length O₂ O₄ r₂ r₄
    let t₃₄ := EuclideanGeometry.external_tangent_length O₃ O₄ r₃ r₄
    t₁₂ * t₃₄ + t₁₄ * t₂₃ = t₁₃ * t₂₄ := by
  exact caseys_scaled_ptolemy_algebra s₁ s₂ s₃ s₄
    (EuclideanGeometry.external_tangent_length O₁ O₂ r₁ r₂)
    (EuclideanGeometry.external_tangent_length O₁ O₃ r₁ r₃)
    (EuclideanGeometry.external_tangent_length O₁ O₄ r₁ r₄)
    (EuclideanGeometry.external_tangent_length O₂ O₃ r₂ r₃)
    (EuclideanGeometry.external_tangent_length O₂ O₄ r₂ r₄)
    (EuclideanGeometry.external_tangent_length O₃ O₄ r₃ r₄)
    c₁₂ c₁₃ c₁₄ c₂₃ c₂₄ c₃₄ h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ h₃₄ hP

/-- The constructed radial contact point lies on the outer circle. -/
private lemma casey_radialContactPoint_mem_circle
    {O C : EuclideanGeometry.Point} {R r : ℝ}
    (h : EuclideanGeometry.liesInsideAndTangentTo C O r R) :
    EuclideanGeometry.radialContactPoint O R C r ∈ EuclideanGeometry.circlePoint O R := by
  rcases h with ⟨_, hr_lt, hdist⟩
  have hgap : R - r ≠ 0 := by linarith
  have hdist' : (C.1 - O.1) ^ 2 + (C.2 - O.2) ^ 2 = (R - r) ^ 2 := by
    simpa [EuclideanGeometry.sqDist] using hdist
  unfold EuclideanGeometry.radialContactPoint EuclideanGeometry.circlePoint EuclideanGeometry.sqDist
  dsimp
  field_simp [hgap]
  nlinarith

/-- Squared chord length between radial contact points in terms of the center data. -/
private lemma casey_contact_sqDist_scale
    (O : EuclideanGeometry.Point) (R : ℝ)
    (Oi Oj : EuclideanGeometry.Point) (ri rj : ℝ)
    (hi : EuclideanGeometry.liesInsideAndTangentTo Oi O ri R)
    (hj : EuclideanGeometry.liesInsideAndTangentTo Oj O rj R) :
    EuclideanGeometry.sqDist
        (EuclideanGeometry.radialContactPoint O R Oi ri)
        (EuclideanGeometry.radialContactPoint O R Oj rj) =
      (R ^ 2 / ((R - ri) * (R - rj))) *
        (EuclideanGeometry.sqDist Oi Oj - (ri - rj) ^ 2) := by
  rcases hi with ⟨_, hri_lt, hdi⟩
  rcases hj with ⟨_, hrj_lt, hdj⟩
  set ai : ℝ := R - ri with hai
  set aj : ℝ := R - rj with haj
  set xi : ℝ := Oi.1 - O.1 with hxi
  set yi : ℝ := Oi.2 - O.2 with hyi
  set xj : ℝ := Oj.1 - O.1 with hxj
  set yj : ℝ := Oj.2 - O.2 with hyj
  have hgi : ai ≠ 0 := by rw [hai]; linarith
  have hgj : aj ≠ 0 := by rw [haj]; linarith
  have hdi' : xi ^ 2 + yi ^ 2 = ai ^ 2 := by
    rw [hxi, hyi, hai]
    simpa [EuclideanGeometry.sqDist] using hdi
  have hdj' : xj ^ 2 + yj ^ 2 = aj ^ 2 := by
    rw [hxj, hyj, haj]
    simpa [EuclideanGeometry.sqDist] using hdj
  have hcoord :
      (R / ai * xi - R / aj * xj) ^ 2 + (R / ai * yi - R / aj * yj) ^ 2 =
        (R ^ 2 / (ai * aj)) * (((xi - xj) ^ 2 + (yi - yj) ^ 2) - (aj - ai) ^ 2) := by
    field_simp [hgi, hgj]
    linear_combination R ^ 2 * (aj - ai) * aj * hdi' -
      R ^ 2 * (aj - ai) * ai * hdj'
  unfold EuclideanGeometry.radialContactPoint EuclideanGeometry.sqDist
  dsimp
  rw [show R - ri = ai by rw [hai], show R - rj = aj by rw [haj]]
  rw [show Oi.1 - O.1 = xi by rw [hxi], show Oi.2 - O.2 = yi by rw [hyi]]
  rw [show Oj.1 - O.1 = xj by rw [hxj], show Oj.2 - O.2 = yj by rw [hyj]]
  rw [show ri - rj = aj - ai by rw [hai, haj]; ring]
  convert hcoord using 1 <;> ring

/-- Exterior tangent length as the contact chord multiplied by the two radial scale factors. -/
private lemma external_tangent_length_eq_scaled_contact
    (O : EuclideanGeometry.Point) (R : ℝ)
    (Oi Oj : EuclideanGeometry.Point) (ri rj : ℝ)
    (hR : 0 < R)
    (hi : EuclideanGeometry.liesInsideAndTangentTo Oi O ri R)
    (hj : EuclideanGeometry.liesInsideAndTangentTo Oj O rj R)
    (hsep : EuclideanGeometry.nonintersectingCircles Oi Oj ri rj) :
    EuclideanGeometry.external_tangent_length Oi Oj ri rj =
      (Real.sqrt (R - ri) / Real.sqrt R) *
        (Real.sqrt (R - rj) / Real.sqrt R) *
          EuclideanGeometry.pointDistance
            (EuclideanGeometry.radialContactPoint O R Oi ri)
            (EuclideanGeometry.radialContactPoint O R Oj rj) := by
  let P := EuclideanGeometry.radialContactPoint O R Oi ri
  let Q := EuclideanGeometry.radialContactPoint O R Oj rj
  let D := EuclideanGeometry.sqDist Oi Oj - (ri - rj) ^ 2
  let C := EuclideanGeometry.sqDist P Q
  have ha_pos : 0 < R - ri := casey_gap_pos_of_liesInside hi
  have hb_pos : 0 < R - rj := casey_gap_pos_of_liesInside hj
  have hD_pos : 0 < D := by
    dsimp [D]
    exact casey_tangent_radicand_pos_of_nonintersecting hsep
  have hC_nonneg : 0 ≤ C := by
    dsimp [C, P, Q, EuclideanGeometry.sqDist]
    nlinarith [
      sq_nonneg ((EuclideanGeometry.radialContactPoint O R Oi ri).1 -
        (EuclideanGeometry.radialContactPoint O R Oj rj).1),
      sq_nonneg ((EuclideanGeometry.radialContactPoint O R Oi ri).2 -
        (EuclideanGeometry.radialContactPoint O R Oj rj).2)]
  have hscale : C = (R ^ 2 / ((R - ri) * (R - rj))) * D := by
    dsimp [C, D, P, Q]
    exact casey_contact_sqDist_scale O R Oi Oj ri rj hi hj
  have hD_from_C : D = (((R - ri) * (R - rj)) / R ^ 2) * C := by
    have hRne : R ≠ 0 := ne_of_gt hR
    have hane : R - ri ≠ 0 := ne_of_gt ha_pos
    have hbne : R - rj ≠ 0 := ne_of_gt hb_pos
    field_simp [hRne, hane, hbne] at hscale ⊢
    nlinarith
  have hrhs_nonneg : 0 ≤ (Real.sqrt (R - ri) / Real.sqrt R) *
        (Real.sqrt (R - rj) / Real.sqrt R) * Real.sqrt C := by
    positivity
  unfold EuclideanGeometry.external_tangent_length EuclideanGeometry.pointDistance
  dsimp [P, Q, D, C] at hD_pos hC_nonneg hD_from_C hrhs_nonneg hscale ⊢
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) hrhs_nonneg).mp
  calc
    (Real.sqrt (EuclideanGeometry.sqDist Oi Oj - (ri - rj) ^ 2)) ^ 2
        = EuclideanGeometry.sqDist Oi Oj - (ri - rj) ^ 2 := by
          exact Real.sq_sqrt (le_of_lt hD_pos)
    _ = (((R - ri) * (R - rj)) / R ^ 2) *
          EuclideanGeometry.sqDist (EuclideanGeometry.radialContactPoint O R Oi ri)
            (EuclideanGeometry.radialContactPoint O R Oj rj) := hD_from_C
    _ = ((Real.sqrt (R - ri) / Real.sqrt R) * (Real.sqrt (R - rj) / Real.sqrt R) *
          Real.sqrt (EuclideanGeometry.sqDist (EuclideanGeometry.radialContactPoint O R Oi ri)
            (EuclideanGeometry.radialContactPoint O R Oj rj))) ^ 2 := by
          rw [mul_pow, mul_pow, div_pow, div_pow]
          rw [Real.sq_sqrt (le_of_lt ha_pos), Real.sq_sqrt (le_of_lt hb_pos),
            Real.sq_sqrt (le_of_lt hR), Real.sq_sqrt hC_nonneg]
          field_simp [ne_of_gt hR]

/-!
Source-backed theorem statements for the Casey theorem formalization.
-/

namespace EuclideanGeometry

/-- Embed the elementary `ℝ × ℝ` point model into mathlib's Euclidean plane. -/
noncomputable def caseyToEuclidean (p : Point) : EuclideanSpace ℝ (Fin 2) :=
  !₂[p.1, p.2]

/-- The mathlib Euclidean distance of embedded points is the local `pointDistance`. -/
lemma dist_caseyToEuclidean (p q : Point) :
    dist (caseyToEuclidean p) (caseyToEuclidean q) = pointDistance p q := by
  rw [EuclideanSpace.dist_eq]
  simp [caseyToEuclidean, pointDistance, sqDist, Real.dist_eq]

/-- The coordinate embedding respects affine line maps. -/
lemma caseyToEuclidean_lineMap (A C : Point) (s : ℝ) :
    (AffineMap.lineMap (caseyToEuclidean A) (caseyToEuclidean C)) s =
      caseyToEuclidean (A.1 + s * (C.1 - A.1), A.2 + s * (C.2 - A.2)) := by
  ext i
  fin_cases i
  · simp [caseyToEuclidean, AffineMap.lineMap_apply_module']
    ring
  · simp [caseyToEuclidean, AffineMap.lineMap_apply_module']
    ring

lemma caseyToEuclidean_injective : Function.Injective caseyToEuclidean := by
  intro p q h
  have h0 := congr_fun (congr_arg WithLp.ofLp h) (0 : Fin 2)
  have h1 := congr_fun (congr_arg WithLp.ofLp h) (1 : Fin 2)
  ext
  · simpa [caseyToEuclidean] using h0
  · simpa [caseyToEuclidean] using h1

lemma casey_pointDistance_comm (p q : Point) : pointDistance p q = pointDistance q p := by
  simp [pointDistance, sqDist]
  ring_nf

/-- For a positively oriented convex quadrilateral in the elementary coordinate model,
the two diagonals meet at a point strictly between each pair of opposite vertices after
embedding into mathlib's Euclidean plane. -/
lemma casey_diagonal_sbtw_of_pos
    {A B C D : Point}
    (hABC : 0 < orientation A B C)
    (hBCD : 0 < orientation B C D)
    (hCDA : 0 < orientation C D A)
    (hDAB : 0 < orientation D A B) :
    ∃ X : EuclideanSpace ℝ (Fin 2),
      Sbtw ℝ (caseyToEuclidean A) X (caseyToEuclidean C) ∧
      Sbtw ℝ (caseyToEuclidean B) X (caseyToEuclidean D) := by
  let den : ℝ := orientation A C D + orientation A B C
  let s : ℝ := orientation A B D / den
  let t : ℝ := orientation A B C / den
  have hACD_pos : 0 < orientation A C D := by
    have hcyc : orientation A C D = orientation C D A := by
      unfold orientation
      ring
    rwa [hcyc]
  have hABD_pos : 0 < orientation A B D := by
    have hcyc : orientation A B D = orientation D A B := by
      unfold orientation
      ring
    rwa [hcyc]
  have hden_pos : 0 < den := by
    dsimp [den]
    linarith
  have hden_ne : den ≠ 0 := ne_of_gt hden_pos
  have hden_eq_s : den = orientation A B D + orientation B C D := by
    dsimp [den]
    unfold orientation
    ring
  have hs_pos : 0 < s := by
    dsimp [s]
    exact div_pos hABD_pos hden_pos
  have hs_lt : s < 1 := by
    dsimp [s]
    rw [div_lt_one hden_pos]
    rw [hden_eq_s]
    linarith
  have ht_pos : 0 < t := by
    dsimp [t]
    exact div_pos hABC hden_pos
  have ht_lt : t < 1 := by
    dsimp [t]
    rw [div_lt_one hden_pos]
    dsimp [den]
    linarith
  have hAC_ne : caseyToEuclidean A ≠ caseyToEuclidean C := by
    intro h
    have h' : A = C := caseyToEuclidean_injective h
    subst C
    simp [orientation] at hABC
  have hBD_ne : caseyToEuclidean B ≠ caseyToEuclidean D := by
    intro h
    have h' : B = D := caseyToEuclidean_injective h
    subst D
    simp [orientation] at hBCD
  have hpoint :
      (A.1 + s * (C.1 - A.1), A.2 + s * (C.2 - A.2)) =
        (B.1 + t * (D.1 - B.1), B.2 + t * (D.2 - B.2)) := by
    ext <;> dsimp [s, t] <;> field_simp [hden_ne] <;> dsimp [den] <;>
      unfold orientation <;> ring
  have hline :
      (AffineMap.lineMap (caseyToEuclidean A) (caseyToEuclidean C)) s =
        (AffineMap.lineMap (caseyToEuclidean B) (caseyToEuclidean D)) t := by
    rw [caseyToEuclidean_lineMap, caseyToEuclidean_lineMap]
    exact congrArg caseyToEuclidean hpoint
  refine ⟨(AffineMap.lineMap (caseyToEuclidean A) (caseyToEuclidean C)) s, ?_, ?_⟩
  · rw [sbtw_lineMap_iff]
    exact ⟨hAC_ne, ⟨hs_pos, hs_lt⟩⟩
  · rw [hline, sbtw_lineMap_iff]
    exact ⟨hBD_ne, ⟨ht_pos, ht_lt⟩⟩

lemma casey_diagonal_sbtw_of_strictlyCyclicallyOrdered
    {A B C D : Point} (hord : strictlyCyclicallyOrdered A B C D) :
    ∃ X : EuclideanSpace ℝ (Fin 2),
      Sbtw ℝ (caseyToEuclidean A) X (caseyToEuclidean C) ∧
      Sbtw ℝ (caseyToEuclidean B) X (caseyToEuclidean D) := by
  rcases hord with hpos | hneg
  · rcases hpos with ⟨hABC, hBCD, hCDA, hDAB⟩
    exact casey_diagonal_sbtw_of_pos hABC hBCD hCDA hDAB
  · rcases hneg with ⟨hABC, hBCD, hCDA, hDAB⟩
    have hADC : 0 < orientation A D C := by
      have h1 : orientation A D C = - orientation C D A := by
        unfold orientation
        ring
      rw [h1]
      linarith
    have hDCB : 0 < orientation D C B := by
      have h1 : orientation D C B = - orientation B C D := by
        unfold orientation
        ring
      rw [h1]
      linarith
    have hCBA : 0 < orientation C B A := by
      have h1 : orientation C B A = - orientation A B C := by
        unfold orientation
        ring
      rw [h1]
      linarith
    have hBAD : 0 < orientation B A D := by
      have h1 : orientation B A D = - orientation D A B := by
        unfold orientation
        ring
      rw [h1]
      linarith
    rcases casey_diagonal_sbtw_of_pos (A := A) (B := D) (C := C) (D := B)
        hADC hDCB hCBA hBAD with ⟨X, hAC, hDB⟩
    exact ⟨X, hAC, hDB.symm⟩

lemma dist_caseyToEuclidean_eq_radius_of_mem_circle
    {O P : Point} {R : ℝ} (hR : 0 < R) (hP : P ∈ circlePoint O R) :
    dist (caseyToEuclidean P) (caseyToEuclidean O) = R := by
  rw [dist_caseyToEuclidean]
  unfold pointDistance circlePoint at *
  rw [hP]
  exact Real.sqrt_sq_eq_abs R ▸ abs_of_pos hR

/-- Ptolemy, transferred from mathlib's Euclidean plane back to the local
`pointDistance` notation for four points on one local circle and in strict cyclic order. -/
lemma casey_pointDistance_ptolemy_of_strictlyCyclicallyOrdered
    {O A B C D : Point} {R : ℝ} (hR : 0 < R)
    (hA : A ∈ circlePoint O R) (hB : B ∈ circlePoint O R)
    (hC : C ∈ circlePoint O R) (hD : D ∈ circlePoint O R)
    (hord : strictlyCyclicallyOrdered A B C D) :
    pointDistance A B * pointDistance C D + pointDistance A D * pointDistance B C =
      pointDistance A C * pointDistance B D := by
  rcases casey_diagonal_sbtw_of_strictlyCyclicallyOrdered hord with ⟨X, hAC, hBD⟩
  have hcos : EuclideanGeometry.Cospherical
      ({caseyToEuclidean A, caseyToEuclidean B, caseyToEuclidean C, caseyToEuclidean D} :
        Set (EuclideanSpace ℝ (Fin 2))) := by
    rw [EuclideanGeometry.cospherical_def]
    refine ⟨caseyToEuclidean O, R, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact dist_caseyToEuclidean_eq_radius_of_mem_circle hR hA
    · exact dist_caseyToEuclidean_eq_radius_of_mem_circle hR hB
    · exact dist_caseyToEuclidean_eq_radius_of_mem_circle hR hC
    · exact dist_caseyToEuclidean_eq_radius_of_mem_circle hR hD
  have hpt := EuclideanGeometry.mul_dist_add_mul_dist_eq_mul_dist_of_cospherical
    (a := caseyToEuclidean A) (b := caseyToEuclidean B)
    (c := caseyToEuclidean C) (d := caseyToEuclidean D) (p := X)
    hcos (Sbtw.angle₁₂₃_eq_pi hAC) (Sbtw.angle₁₂₃_eq_pi hBD)
  rw [dist_caseyToEuclidean, dist_caseyToEuclidean, dist_caseyToEuclidean,
      dist_caseyToEuclidean, dist_caseyToEuclidean, dist_caseyToEuclidean] at hpt
  rw [casey_pointDistance_comm D A] at hpt
  calc
    pointDistance A B * pointDistance C D + pointDistance A D * pointDistance B C
        = pointDistance A B * pointDistance C D + pointDistance B C * pointDistance A D := by ring
    _ = pointDistance A C * pointDistance B D := hpt

end EuclideanGeometry

/--
Source theorem `thm:casey` (`caseys_theorem`).
Let `O` be a circle of radius `R`.  Let `O₁, O₂, O₃, O₄` be, in that order, four
nonintersecting circles lying inside `O` and tangent to it.  If `tᵢⱼ` denotes the
length of the exterior common bitangent of `Oᵢ` and `Oⱼ`, then
`t₁₂ * t₃₄ + t₁₄ * t₂₃ = t₁₃ * t₂₄`.

Source proof: no proof is included in `docs/source.tex`.
Proof sketch / prover notes: take the radial contact points of the four inner circles
with the outer circle.  These contact points are cyclically ordered on the outer circle,
so Ptolemy applies to their chord lengths.  For an inner circle with
`aᵢ = R - rᵢ`, the exterior tangent length between `Oᵢ` and `Oⱼ` is the corresponding
chord length multiplied by `sqrt (aᵢ * aⱼ) / R`; the same product factor appears in
every term, yielding Casey's equality.  When all `rᵢ = 0`, the tangent-length formula
reduces to ordinary chord length, giving the Ptolemy theorem noted in the source.
-/
theorem EuclideanGeometry.caseys_theorem
    (O : EuclideanGeometry.Point) (R : ℝ)
    (O₁ O₂ O₃ O₄ : EuclideanGeometry.Point) (r₁ r₂ r₃ r₄ : ℝ)
    (hR : 0 < R)
    (h₁ : EuclideanGeometry.liesInsideAndTangentTo O₁ O r₁ R)
    (h₂ : EuclideanGeometry.liesInsideAndTangentTo O₂ O r₂ R)
    (h₃ : EuclideanGeometry.liesInsideAndTangentTo O₃ O r₃ R)
    (h₄ : EuclideanGeometry.liesInsideAndTangentTo O₄ O r₄ R)
    (hNonintersecting : EuclideanGeometry.fourCirclesNonintersecting O₁ O₂ O₃ O₄ r₁ r₂ r₃ r₄)
    (hOrder : EuclideanGeometry.caseyInOrder O R O₁ O₂ O₃ O₄ r₁ r₂ r₃ r₄) :
    let t₁₂ := EuclideanGeometry.external_tangent_length O₁ O₂ r₁ r₂
    let t₁₃ := EuclideanGeometry.external_tangent_length O₁ O₃ r₁ r₃
    let t₁₄ := EuclideanGeometry.external_tangent_length O₁ O₄ r₁ r₄
    let t₂₃ := EuclideanGeometry.external_tangent_length O₂ O₃ r₂ r₃
    let t₂₄ := EuclideanGeometry.external_tangent_length O₂ O₄ r₂ r₄
    let t₃₄ := EuclideanGeometry.external_tangent_length O₃ O₄ r₃ r₄
    t₁₂ * t₃₄ + t₁₄ * t₂₃ = t₁₃ * t₂₄ := by
  let P₁ := EuclideanGeometry.radialContactPoint O R O₁ r₁
  let P₂ := EuclideanGeometry.radialContactPoint O R O₂ r₂
  let P₃ := EuclideanGeometry.radialContactPoint O R O₃ r₃
  let P₄ := EuclideanGeometry.radialContactPoint O R O₄ r₄
  let s₁ := Real.sqrt (R - r₁) / Real.sqrt R
  let s₂ := Real.sqrt (R - r₂) / Real.sqrt R
  let s₃ := Real.sqrt (R - r₃) / Real.sqrt R
  let s₄ := Real.sqrt (R - r₄) / Real.sqrt R
  let c₁₂ := EuclideanGeometry.pointDistance P₁ P₂
  let c₁₃ := EuclideanGeometry.pointDistance P₁ P₃
  let c₁₄ := EuclideanGeometry.pointDistance P₁ P₄
  let c₂₃ := EuclideanGeometry.pointDistance P₂ P₃
  let c₂₄ := EuclideanGeometry.pointDistance P₂ P₄
  let c₃₄ := EuclideanGeometry.pointDistance P₃ P₄
  rcases hNonintersecting with ⟨h₁₂sep, h₁₃sep, h₁₄sep, h₂₃sep, h₂₄sep, h₃₄sep⟩
  have hP₁ : P₁ ∈ EuclideanGeometry.circlePoint O R := by
    dsimp [P₁]
    exact casey_radialContactPoint_mem_circle h₁
  have hP₂ : P₂ ∈ EuclideanGeometry.circlePoint O R := by
    dsimp [P₂]
    exact casey_radialContactPoint_mem_circle h₂
  have hP₃ : P₃ ∈ EuclideanGeometry.circlePoint O R := by
    dsimp [P₃]
    exact casey_radialContactPoint_mem_circle h₃
  have hP₄ : P₄ ∈ EuclideanGeometry.circlePoint O R := by
    dsimp [P₄]
    exact casey_radialContactPoint_mem_circle h₄
  have hChordPtolemy : c₁₂ * c₃₄ + c₁₄ * c₂₃ = c₁₃ * c₂₄ := by
    have hord : EuclideanGeometry.strictlyCyclicallyOrdered P₁ P₂ P₃ P₄ := by
      simpa [EuclideanGeometry.caseyInOrder, P₁, P₂, P₃, P₄] using hOrder
    have hraw := EuclideanGeometry.casey_pointDistance_ptolemy_of_strictlyCyclicallyOrdered
      (O := O) (A := P₁) (B := P₂) (C := P₃) (D := P₄) (R := R)
      hR hP₁ hP₂ hP₃ hP₄ hord
    simpa [c₁₂, c₁₃, c₁₄, c₂₃, c₂₄, c₃₄] using hraw
  have ht₁₂ : EuclideanGeometry.external_tangent_length O₁ O₂ r₁ r₂ = s₁ * s₂ * c₁₂ := by
    simpa [s₁, s₂, c₁₂, P₁, P₂] using
      external_tangent_length_eq_scaled_contact (O := O) (R := R)
        (Oi := O₁) (Oj := O₂) (ri := r₁) (rj := r₂) hR h₁ h₂ h₁₂sep
  have ht₁₃ : EuclideanGeometry.external_tangent_length O₁ O₃ r₁ r₃ = s₁ * s₃ * c₁₃ := by
    simpa [s₁, s₃, c₁₃, P₁, P₃] using
      external_tangent_length_eq_scaled_contact (O := O) (R := R)
        (Oi := O₁) (Oj := O₃) (ri := r₁) (rj := r₃) hR h₁ h₃ h₁₃sep
  have ht₁₄ : EuclideanGeometry.external_tangent_length O₁ O₄ r₁ r₄ = s₁ * s₄ * c₁₄ := by
    simpa [s₁, s₄, c₁₄, P₁, P₄] using
      external_tangent_length_eq_scaled_contact (O := O) (R := R)
        (Oi := O₁) (Oj := O₄) (ri := r₁) (rj := r₄) hR h₁ h₄ h₁₄sep
  have ht₂₃ : EuclideanGeometry.external_tangent_length O₂ O₃ r₂ r₃ = s₂ * s₃ * c₂₃ := by
    simpa [s₂, s₃, c₂₃, P₂, P₃] using
      external_tangent_length_eq_scaled_contact (O := O) (R := R)
        (Oi := O₂) (Oj := O₃) (ri := r₂) (rj := r₃) hR h₂ h₃ h₂₃sep
  have ht₂₄ : EuclideanGeometry.external_tangent_length O₂ O₄ r₂ r₄ = s₂ * s₄ * c₂₄ := by
    simpa [s₂, s₄, c₂₄, P₂, P₄] using
      external_tangent_length_eq_scaled_contact (O := O) (R := R)
        (Oi := O₂) (Oj := O₄) (ri := r₂) (rj := r₄) hR h₂ h₄ h₂₄sep
  have ht₃₄ : EuclideanGeometry.external_tangent_length O₃ O₄ r₃ r₄ = s₃ * s₄ * c₃₄ := by
    simpa [s₃, s₄, c₃₄, P₃, P₄] using
      external_tangent_length_eq_scaled_contact (O := O) (R := R)
        (Oi := O₃) (Oj := O₄) (ri := r₃) (rj := r₄) hR h₃ h₄ h₃₄sep
  exact caseys_theorem_of_scale_data O₁ O₂ O₃ O₄ r₁ r₂ r₃ r₄
    s₁ s₂ s₃ s₄ c₁₂ c₁₃ c₁₄ c₂₃ c₂₄ c₃₄
    ht₁₂ ht₁₃ ht₁₄ ht₂₃ ht₂₄ ht₃₄ hChordPtolemy

/--
Source follow-on claim in `thm:casey`: in the degenerate zero-radius case, the
Casey equality is exactly Ptolemy's equality for the four resulting points.

Source proof: no proof is included in `docs/source.tex`.
Proof sketch / prover notes: unfold `external_tangent_length`, `pointDistance`, and
`ptolemyEquality`; with all radii equal to zero, each bitangent length becomes the
ordinary point distance `sqrt (sqDist Pᵢ Pⱼ)`.
-/
theorem EuclideanGeometry.caseys_theorem_degenerate_ptolemy_bridge
    (P₁ P₂ P₃ P₄ : EuclideanGeometry.Point) :
    (let t₁₂ := EuclideanGeometry.external_tangent_length P₁ P₂ 0 0
     let t₁₃ := EuclideanGeometry.external_tangent_length P₁ P₃ 0 0
     let t₁₄ := EuclideanGeometry.external_tangent_length P₁ P₄ 0 0
     let t₂₃ := EuclideanGeometry.external_tangent_length P₂ P₃ 0 0
     let t₂₄ := EuclideanGeometry.external_tangent_length P₂ P₄ 0 0
     let t₃₄ := EuclideanGeometry.external_tangent_length P₃ P₄ 0 0
     t₁₂ * t₃₄ + t₁₄ * t₂₃ = t₁₃ * t₂₄) ↔
      EuclideanGeometry.ptolemyEquality P₁ P₂ P₃ P₄ := by
  constructor <;> intro h
  · simpa [EuclideanGeometry.external_tangent_length,
      EuclideanGeometry.ptolemyEquality, EuclideanGeometry.pointDistance] using h
  · simpa [EuclideanGeometry.external_tangent_length,
      EuclideanGeometry.ptolemyEquality, EuclideanGeometry.pointDistance] using h
