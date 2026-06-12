import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/--
An axis-aligned open rectangle in `ℝ × ℝ`, represented as a Cartesian product of
open real intervals. This companion definition records the convention used for
the source phrase "open rectangles".
-/
def IsOpenRectangle (R : Set (ℝ × ℝ)) : Prop :=
  ∃ a b c d : ℝ, a < b ∧ c < d ∧ R = Set.Ioo a b ×ˢ Set.Ioo c d

private lemma IsOpenRectangle.isOpen {R : Set (ℝ × ℝ)}
    (hR : IsOpenRectangle R) : IsOpen R := by
  rcases hR with ⟨a, b, c, d, hab, hcd, rfl⟩
  exact isOpen_Ioo.prod isOpen_Ioo

/--
Source theorem `line-17` (`open_disc_not_disjoint_union_rectangles`): an open disc
in `ℝ^2` is not the disjoint union of open rectangles.

Source proof: no proof is supplied in `docs/source.tex`.
Proof sketch: interpret the disc as the genuine Euclidean disc
`{p | (p.1 - c.1)^2 + (p.2 - c.2)^2 < r^2}` in `ℝ × ℝ` and open rectangles as
products of open intervals. A later proof can use connectedness or
path-connectedness of the disc: a pairwise-disjoint cover by nonempty open
rectangles would force at most one rectangle, and a positive-radius round disc is
not a single axis-aligned open rectangle.

Representation note: the disc must be the EUCLIDEAN disc, written out explicitly as
a quadratic inequality. Mathlib's `Metric.ball`/`dist` on `ℝ × ℝ` use the sup
(L∞) metric, so they describe an axis-aligned open SQUARE, which is itself an open
rectangle; using them here would make the theorem false. This matches `Skeleton4`.

Prover notes: `hrectangles` makes every family member a nonempty open rectangle;
`hdisjoint` is the formal disjointness condition; the conclusion denies equality
with the indexed union of the family.
-/
theorem open_disc_not_disjoint_union_rectangles
    (center : ℝ × ℝ) (radius : ℝ) (hradius : 0 < radius)
    (ι : Type*) (rectangles : ι → Set (ℝ × ℝ))
    (hrectangles : ∀ i, IsOpenRectangle (rectangles i))
    (hdisjoint : Pairwise (fun i j => Disjoint (rectangles i) (rectangles j))) :
    {p : ℝ × ℝ | (p.1 - center.1) ^ 2 + (p.2 - center.2) ^ 2 < radius ^ 2} ≠
      ⋃ i, rectangles i := by
  intro hEq
  rcases center with ⟨cx, cy⟩
  have hcenter_disk : ((cx, cy) : ℝ × ℝ) ∈
      {p : ℝ × ℝ | (p.1 - cx) ^ 2 + (p.2 - cy) ^ 2 < radius ^ 2} := by
    simp [sq_pos_of_pos hradius]
  have hcenter_union : ((cx, cy) : ℝ × ℝ) ∈ ⋃ i, rectangles i := by
    simpa [hEq] using hcenter_disk
  rcases Set.mem_iUnion.mp hcenter_union with ⟨i0, hi0center⟩
  have hrect_subset_disk : ∀ i, rectangles i ⊆
      {p : ℝ × ℝ | (p.1 - cx) ^ 2 + (p.2 - cy) ^ 2 < radius ^ 2} := by
    intro i p hp
    have hp_union : p ∈ ⋃ j, rectangles j := Set.mem_iUnion.mpr ⟨i, hp⟩
    simpa [hEq] using hp_union
  have h_horizontal : ∀ x : ℝ, x ∈ Set.Ioo (cx - radius) (cx + radius) →
      ((x, cy) : ℝ × ℝ) ∈ rectangles i0 := by
    intro x hx
    let H : Set (ℝ × ℝ) :=
      (fun x : ℝ => (x, cy)) '' Set.Ioo (cx - radius) (cx + radius)
    let others : Set (ℝ × ℝ) := ⋃ j : {j : ι // j ≠ i0}, rectangles j.1
    have hHpre : IsPreconnected H := by
      dsimp [H]
      exact isPreconnected_Ioo.image (fun x : ℝ => (x, cy))
        (Continuous.prodMk_left cy).continuousOn
    have hOthersOpen : IsOpen others := by
      dsimp [others]
      exact isOpen_iUnion (fun j => IsOpenRectangle.isOpen (hrectangles j.1))
    have hDisj : Disjoint (rectangles i0) others := by
      rw [Set.disjoint_left]
      intro p hp0 hpothers
      rcases Set.mem_iUnion.mp hpothers with ⟨j, hpj⟩
      exact (Set.disjoint_left.mp (hdisjoint (Ne.symm j.2))) hp0 hpj
    have hCover : H ⊆ rectangles i0 ∪ others := by
      intro p hp
      rcases hp with ⟨x, hx, rfl⟩
      have hpdisk : ((x, cy) : ℝ × ℝ) ∈
          {p : ℝ × ℝ | (p.1 - cx) ^ 2 + (p.2 - cy) ^ 2 < radius ^ 2} := by
        dsimp
        rcases hx with ⟨hx1, hx2⟩
        ring_nf
        nlinarith [sq_nonneg (x - cx - radius), sq_nonneg (x - cx + radius)]
      have hpunion : ((x, cy) : ℝ × ℝ) ∈ ⋃ j, rectangles j := by
        simpa [hEq] using hpdisk
      rcases Set.mem_iUnion.mp hpunion with ⟨j, hj⟩
      by_cases hji : j = i0
      · left
        simpa [hji] using hj
      · right
        exact Set.mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩
    have hSubOr : H ⊆ rectangles i0 ∨ H ⊆ others :=
      IsPreconnected.subset_or_subset (IsOpenRectangle.isOpen (hrectangles i0))
        hOthersOpen hDisj hCover hHpre
    have hHpoint : ((x, cy) : ℝ × ℝ) ∈ H := ⟨x, hx, rfl⟩
    rcases hSubOr with hSub | hSub
    · exact hSub hHpoint
    · have hCenterH : ((cx, cy) : ℝ × ℝ) ∈ H := by
        refine ⟨cx, ?_, rfl⟩
        constructor <;> linarith
      have hCenterOthers : ((cx, cy) : ℝ × ℝ) ∈ others := hSub hCenterH
      exact False.elim ((Set.disjoint_left.mp hDisj) hi0center hCenterOthers)
  have h_vertical : ∀ y : ℝ, y ∈ Set.Ioo (cy - radius) (cy + radius) →
      ((cx, y) : ℝ × ℝ) ∈ rectangles i0 := by
    intro y hy
    let V : Set (ℝ × ℝ) :=
      (fun y : ℝ => (cx, y)) '' Set.Ioo (cy - radius) (cy + radius)
    let others : Set (ℝ × ℝ) := ⋃ j : {j : ι // j ≠ i0}, rectangles j.1
    have hVpre : IsPreconnected V := by
      dsimp [V]
      exact isPreconnected_Ioo.image (fun y : ℝ => (cx, y))
        (Continuous.prodMk_right cx).continuousOn
    have hOthersOpen : IsOpen others := by
      dsimp [others]
      exact isOpen_iUnion (fun j => IsOpenRectangle.isOpen (hrectangles j.1))
    have hDisj : Disjoint (rectangles i0) others := by
      rw [Set.disjoint_left]
      intro p hp0 hpothers
      rcases Set.mem_iUnion.mp hpothers with ⟨j, hpj⟩
      exact (Set.disjoint_left.mp (hdisjoint (Ne.symm j.2))) hp0 hpj
    have hCover : V ⊆ rectangles i0 ∪ others := by
      intro p hp
      rcases hp with ⟨y, hy, rfl⟩
      have hpdisk : ((cx, y) : ℝ × ℝ) ∈
          {p : ℝ × ℝ | (p.1 - cx) ^ 2 + (p.2 - cy) ^ 2 < radius ^ 2} := by
        dsimp
        rcases hy with ⟨hy1, hy2⟩
        ring_nf
        nlinarith [sq_nonneg (y - cy - radius), sq_nonneg (y - cy + radius)]
      have hpunion : ((cx, y) : ℝ × ℝ) ∈ ⋃ j, rectangles j := by
        simpa [hEq] using hpdisk
      rcases Set.mem_iUnion.mp hpunion with ⟨j, hj⟩
      by_cases hji : j = i0
      · left
        simpa [hji] using hj
      · right
        exact Set.mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩
    have hSubOr : V ⊆ rectangles i0 ∨ V ⊆ others :=
      IsPreconnected.subset_or_subset (IsOpenRectangle.isOpen (hrectangles i0))
        hOthersOpen hDisj hCover hVpre
    have hVpoint : ((cx, y) : ℝ × ℝ) ∈ V := ⟨y, hy, rfl⟩
    rcases hSubOr with hSub | hSub
    · exact hSub hVpoint
    · have hCenterV : ((cx, cy) : ℝ × ℝ) ∈ V := by
        refine ⟨cy, ?_, rfl⟩
        constructor <;> linarith
      have hCenterOthers : ((cx, cy) : ℝ × ℝ) ∈ others := hSub hCenterV
      exact False.elim ((Set.disjoint_left.mp hDisj) hi0center hCenterOthers)
  let d : ℝ := 3 * radius / 4
  have hxd : cx + d ∈ Set.Ioo (cx - radius) (cx + radius) := by
    dsimp [d]
    constructor <;> nlinarith [hradius]
  have hyd : cy + d ∈ Set.Ioo (cy - radius) (cy + radius) := by
    dsimp [d]
    constructor <;> nlinarith [hradius]
  have hxpoint : ((cx + d, cy) : ℝ × ℝ) ∈ rectangles i0 := h_horizontal (cx + d) hxd
  have hypoint : ((cx, cy + d) : ℝ × ℝ) ∈ rectangles i0 := h_vertical (cy + d) hyd
  rcases hrectangles i0 with ⟨a, b, c, e, hab, hce, hi0eq⟩
  have hx_ab : cx + d ∈ Set.Ioo a b := by
    have hprod : ((cx + d, cy) : ℝ × ℝ) ∈ Set.Ioo a b ×ˢ Set.Ioo c e := by
      simpa [hi0eq] using hxpoint
    exact hprod.1
  have hy_ce : cy + d ∈ Set.Ioo c e := by
    have hprod : ((cx, cy + d) : ℝ × ℝ) ∈ Set.Ioo a b ×ˢ Set.Ioo c e := by
      simpa [hi0eq] using hypoint
    exact hprod.2
  have hcorner_rect : ((cx + d, cy + d) : ℝ × ℝ) ∈ rectangles i0 := by
    rw [hi0eq]
    exact ⟨hx_ab, hy_ce⟩
  have hcorner_disk : ((cx + d, cy + d) : ℝ × ℝ) ∈
      {p : ℝ × ℝ | (p.1 - cx) ^ 2 + (p.2 - cy) ^ 2 < radius ^ 2} :=
    hrect_subset_disk i0 hcorner_rect
  have hcorner_not_disk : ((cx + d, cy + d) : ℝ × ℝ) ∉
      {p : ℝ × ℝ | (p.1 - cx) ^ 2 + (p.2 - cy) ^ 2 < radius ^ 2} := by
    intro h
    dsimp [d] at h
    ring_nf at h
    nlinarith [sq_pos_of_pos hradius]
  exact hcorner_not_disk hcorner_disk
