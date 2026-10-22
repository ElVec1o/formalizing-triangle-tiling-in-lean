import Erdos634.Draft.LaczFormalThm33if1
import Erdos634.Draft.LaczFormalL37Plane
import Erdos634.Draft.LaczFormalL22Grid

/-!
# Laczkovich DCG 48 (2012) Thm 3.3, "if" direction, module 2 of 4: `γ = π/3` (Laczkovich 1995 Thm 3.1, trapezoid assembly)

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Thm 3.1, Lemma 2.1, Lemma 2.2 (iii); DCG 48 (2012) 330-372,
Thm 3.3), Beeson, Beeson-Zhang, Zhang.

Printed proof (Thm 3.1): the trapezoid `S` with angles `π/3, π/3, 2π/3, 2π/3`, sides `AB = 2`, `AD = DC = BC = 1`, is dissected into
rational triangles similar to the tile by Lemma 2.2 (iii) (`LaczL37.lemma22_iii_plane`, base `W = 2`, leg `D = 1`, top ratio
`tTauI = 1/2`); three copies of `S` make the equilateral triangle of side 3.  Here, in the chart `(u, v)` with `|u| = |v| = 1`,
`<u, v> = 1/2`: the triangle `{z0, z1 >= 0, z0 + z1 <= 3}` is the union of `Q1, Q2, Q3` (the three trapezoids, each the image of
`trapPlane`), pairwise separated by lines.  Hypothesis: a rational tile `R` with `vang R.Δ 1 = π/3`.
`thm33_if_rtri_pi3` : `Thm33If (vang R.Δ 0) (vang R.Δ 1) (vang R.Δ 2)`.
-/

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
  Erdos634.Draft.LaczFormal Erdos634.LaczL35 Erdos634.LaczL22 Erdos634.CertCoord Erdos634.LaczL37
  Erdos634.DissectionMap Erdos634.CertGeom

namespace Erdos634.LaczThm33If

theorem mkPt_eta (q : Plane) : mkPt (q 0) (q 1) = q := by
  ext i; fin_cases i <;> simp

/-- Inner products in the chart basis. -/
theorem inner_comb (u v : Plane) (hu : inner ℝ u u = 1) (hv : inner ℝ v v = 1) (huv : inner ℝ u v = 1 / 2)
    (a b c d : ℝ) :
    inner ℝ (a • u + b • v) (c • u + d • v) = a * c + (a * d + b * c) / 2 + b * d := by
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, hu, hv, huv,
    real_inner_comm u v]
  ring

theorem piece_gram (w d : Plane) (hw : inner ℝ w w = 4) (hd : inner ℝ d d = 1) (hwd : inner ℝ w d = 1) :
    ‖w‖ = ((2 : ℚ) : ℝ) ∧ ‖d‖ = ((1 : ℚ) : ℝ) ∧ InnerProductGeometry.angle w d = Real.pi / 3 := by
  have hwn : ‖w‖ = ((2 : ℚ) : ℝ) := by
    have : ‖w‖ ^ 2 = ((2 : ℚ) : ℝ) ^ 2 := by rw [← real_inner_self_eq_norm_sq, hw]; norm_num
    exact (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp this
  have hdn : ‖d‖ = ((1 : ℚ) : ℝ) := by
    have : ‖d‖ ^ 2 = ((1 : ℚ) : ℝ) ^ 2 := by rw [← real_inner_self_eq_norm_sq, hd]; norm_num
    exact (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).mp this
  refine ⟨hwn, hdn, ?_⟩
  apply angle_eq_of_cos (InnerProductGeometry.angle_nonneg _ _) (InnerProductGeometry.angle_le_pi _ _)
    (by positivity) (by linarith [Real.pi_pos])
  rw [InnerProductGeometry.cos_angle, hwn, hdn, hwd, Real.cos_pi_div_three]
  norm_num

/-- One trapezoid piece, for a rational tile with `vang 1 = π/3`. -/
theorem piece_ratsim (R : RTri) (hτ : tTauI R.a R.b R.c 2 1 = 1 / 2) (hβ : vang R.Δ 1 = Real.pi / 3)
    (A w d : Plane) (hw : inner ℝ w w = 4) (hd : inner ℝ d d = 1) (hwd : inner ℝ w d = 1) :
    RatSimDiss R.Δ (trapPlane A w d (1 / 2 : ℝ)) := by
  obtain ⟨hwn, hdn, hang⟩ := piece_gram w d hw hd hwd
  have h := lemma22_iii_plane R A w d 2 1 (by norm_num) (by norm_num) hwn hdn (by rw [hβ]; exact hang)
    (by rw [hτ]; norm_num)
  rw [hτ] at h
  simpa using h

/-- `tTauI = 1/2` when the angle at vertex 1 is `π/3`. -/
theorem tTauI_half (R : RTri) (hβ : vang R.Δ 1 = Real.pi / 3) : tTauI R.a R.b R.c 2 1 = 1 / 2 := by
  have hc := RTri.cos_vang1 R
  rw [hβ, Real.cos_pi_div_three] at hc
  have ha : (R.a : ℝ) ≠ 0 := by exact_mod_cast R.pa.ne'
  have hcc : (R.c : ℝ) ≠ 0 := by exact_mod_cast R.pc.ne'
  have h1 : (R.a : ℝ) ^ 2 + R.c ^ 2 - R.b ^ 2 = R.a * R.c := by
    field_simp at hc; nlinarith [hc]
  have h2 : R.a ^ 2 + R.c ^ 2 - R.b ^ 2 = R.a * R.c := by exact_mod_cast h1
  unfold tTauI
  rw [h2]
  have : R.a ≠ 0 := R.pa.ne'
  have : R.c ≠ 0 := R.pc.ne'
  field_simp
  norm_num

/-! ### the coordinate sets -/

def Q1 : Set Plane := {z | 0 ≤ z 1 ∧ z 1 ≤ 1 ∧ 0 ≤ z 0 ∧ z 0 + z 1 ≤ 2}
def Q2 : Set Plane := {z | 1 ≤ z 0 ∧ 2 ≤ z 0 + z 1 ∧ z 0 + z 1 ≤ 3 ∧ 0 ≤ z 1}
def Q3 : Set Plane := {z | 1 ≤ z 1 ∧ z 0 ≤ 1 ∧ 0 ≤ z 0 ∧ z 0 + z 1 ≤ 3}
def Qtri : Set Plane := {z | 0 ≤ z 0 ∧ 0 ≤ z 1 ∧ z 0 + z 1 ≤ 3}

theorem Q_union : Q1 ∪ Q2 ∪ Q3 = Qtri := by
  ext z
  simp only [Q1, Q2, Q3, Qtri, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro ((h | h) | h) <;> refine ⟨?_, ?_, ?_⟩ <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]
  · rintro ⟨h0, h1, h2⟩
    by_cases a : z 1 ≤ 1 ∧ z 0 + z 1 ≤ 2
    · exact Or.inl (Or.inl ⟨h1, a.1, h0, a.2⟩)
    · by_cases b : z 1 ≤ 1
      · have : 2 < z 0 + z 1 := by by_contra hh; exact a ⟨b, by linarith⟩
        exact Or.inl (Or.inr ⟨by linarith, this.le, h2, h1⟩)
      · by_cases c : 1 ≤ z 0
        · have : 2 ≤ z 0 + z 1 := by linarith
          exact Or.inl (Or.inr ⟨c, this, h2, h1⟩)
        · exact Or.inr ⟨by linarith, by linarith, h0, h2⟩

/-- generic trapezoid in the chart basis. -/
theorem trap_img (u v : Plane) (hdet : u 0 * v 1 - u 1 * v 0 ≠ 0) (α0 α1 ω0 ω1 δ0 δ1 τ : ℝ) :
    trapPlane (α0 • u + α1 • v) (ω0 • u + ω1 • v) (δ0 • u + δ1 • v) τ
      = chartEquiv 0 u v hdet '' {z | ∃ s t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ 0 ≤ s ∧ s ≤ 1 + (τ - 1) * t ∧
          z 0 = α0 + s * ω0 + t * δ0 ∧ z 1 = α1 + s * ω1 + t * δ1} := by
  ext X
  constructor
  · rintro ⟨s, t, h1, h2, h3, h4, rfl⟩
    refine ⟨mkPt (α0 + s * ω0 + t * δ0) (α1 + s * ω1 + t * δ1), ⟨s, t, h1, h2, h3, h4, by simp, by simp⟩, ?_⟩
    rw [chartEquiv_apply]
    simp only [mkPt_zero, mkPt_one]
    module
  · rintro ⟨z, ⟨s, t, h1, h2, h3, h4, e0, e1⟩, rfl⟩
    refine ⟨s, t, h1, h2, h3, h4, ?_⟩
    rw [chartEquiv_apply, e0, e1]
    module

/-- interior points of a set on one side of a line are strictly inside. -/
theorem interior_lt_of_le {S : Set Plane} (f : Plane →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) (c : ℝ)
    (h : ∀ x ∈ S, f x ≤ c) : ∀ x ∈ interior S, f x < c := by
  intro x hx
  have hxS : x ∈ S := interior_subset hx
  by_contra hcon
  have hxc : f x = c := le_antisymm (h x hxS) (not_lt.mp hcon)
  set g : Plane →ᵃ[ℝ] ℝ := AffineMap.const ℝ Plane c - f with hg
  have hglin : g.linear ≠ 0 := by
    intro hc
    apply hf
    have : (AffineMap.const ℝ Plane c).linear - f.linear = 0 := hc
    have hzero : (AffineMap.const ℝ Plane c).linear = 0 := rfl
    rw [hzero, zero_sub, neg_eq_zero] at this
    exact this
  have hgx : g x = 0 := by simp [hg, hxc]
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  obtain ⟨y, hy, hyneg⟩ := Erdos634.Geometry.exists_neg_near_of_affine_zero g hglin hgx hr
  have hyS : y ∈ S := hball hy
  have : c < f y := by
    have hgy : g y = c - f y := rfl
    rw [hgy] at hyneg
    linarith
  exact absurd (h y hyS) (not_le.mpr this)

/-- The three trapezoids assemble the equilateral triangle: `RatSimDiss` of the image of `Qtri`. -/
theorem qtri_ratsim (R : RTri) (hβ : vang R.Δ 1 = Real.pi / 3) (u v : Plane) (hu : inner ℝ u u = 1)
    (hv : inner ℝ v v = 1) (huv : inner ℝ u v = 1 / 2) (hdet : u 0 * v 1 - u 1 * v 0 ≠ 0) :
    RatSimDiss R.Δ (chartEquiv 0 u v hdet '' Qtri) := by
  have hτ := tTauI_half R hβ
  have ic := inner_comb u v hu hv huv
  -- the three pieces
  have P1 : RatSimDiss R.Δ (chartEquiv 0 u v hdet '' Q1) := by
    have h := piece_ratsim R hτ hβ ((0 : ℝ) • u + (0 : ℝ) • v) ((2 : ℝ) • u + (0 : ℝ) • v)
      ((0 : ℝ) • u + (1 : ℝ) • v) (by rw [ic]; norm_num) (by rw [ic]; norm_num) (by rw [ic]; norm_num)
    rw [trap_img u v hdet] at h
    convert h using 2
    ext z
    simp only [Q1, Set.mem_setOf_eq]
    constructor
    · rintro ⟨a, b, c, d⟩
      exact ⟨z 0 / 2, z 1, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
    · rintro ⟨s, t, h1, h2, h3, h4, e0, e1⟩
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have P2 : RatSimDiss R.Δ (chartEquiv 0 u v hdet '' Q2) := by
    have h := piece_ratsim R hτ hβ ((3 : ℝ) • u + (0 : ℝ) • v) ((-2 : ℝ) • u + (2 : ℝ) • v)
      ((-1 : ℝ) • u + (0 : ℝ) • v) (by rw [ic]; norm_num) (by rw [ic]; norm_num) (by rw [ic]; norm_num)
    rw [trap_img u v hdet] at h
    convert h using 2
    ext z
    simp only [Q2, Set.mem_setOf_eq]
    constructor
    · rintro ⟨a, b, c, d⟩
      exact ⟨z 1 / 2, 3 - z 0 - z 1, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
    · rintro ⟨s, t, h1, h2, h3, h4, e0, e1⟩
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have P3 : RatSimDiss R.Δ (chartEquiv 0 u v hdet '' Q3) := by
    have h := piece_ratsim R hτ hβ ((0 : ℝ) • u + (3 : ℝ) • v) ((0 : ℝ) • u + (-2 : ℝ) • v)
      ((1 : ℝ) • u + (-1 : ℝ) • v) (by rw [ic]; norm_num) (by rw [ic]; norm_num) (by rw [ic]; norm_num)
    rw [trap_img u v hdet] at h
    convert h using 2
    ext z
    simp only [Q3, Set.mem_setOf_eq]
    constructor
    · rintro ⟨a, b, c, d⟩
      exact ⟨(3 - z 0 - z 1) / 2, z 0, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
    · rintro ⟨s, t, h1, h2, h3, h4, e0, e1⟩
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  -- separations
  have d12 : Disjoint (interior Q1) (interior Q2) :=
    disjoint_interior_of_sep (lineFun 0 2 2 0) (lineFun_linear_ne_zero (Or.inl (by norm_num))) 0
      (by rintro x ⟨a, b, c, d⟩; simp only [lineFun_apply]; nlinarith)
      (by rintro x ⟨a, b, c, d⟩; simp only [lineFun_apply]; nlinarith)
  have d123 : Disjoint (interior (Q1 ∪ Q2)) (interior Q3) := by
    rw [Set.disjoint_left]
    intro x hx12 hx3
    have l1 := interior_lt_of_le (lineFun 1 1 0 1) (lineFun_linear_ne_zero (Or.inl (by norm_num))) 0
      (by rintro y ⟨a, b, c, d⟩; simp only [lineFun_apply]; nlinarith) x hx3
    have l2 := interior_lt_of_le (lineFun 1 1 1 0) (lineFun_linear_ne_zero (Or.inr (by norm_num))) 0
      (by rintro y ⟨a, b, c, d⟩; simp only [lineFun_apply]; nlinarith) x hx3
    simp only [lineFun_apply] at l1 l2
    rcases interior_subset hx12 with h | h
    · obtain ⟨a, b, c, d⟩ := h; nlinarith
    · obtain ⟨a, b, c, d⟩ := h; nlinarith
  have U12 : RatSimDiss R.Δ (chartEquiv 0 u v hdet '' Q1 ∪ chartEquiv 0 u v hdet '' Q2) :=
    P1.union P2 (disjoint_interior_image _ d12)
  have U : RatSimDiss R.Δ (chartEquiv 0 u v hdet '' (Q1 ∪ Q2) ∪ chartEquiv 0 u v hdet '' Q3) := by
    rw [Set.image_union]
    exact U12.union P3 (by
      rw [← Set.image_union]; exact disjoint_interior_image _ d123)
  rw [← Set.image_union, Q_union] at U
  exact U

end Erdos634.LaczThm33If
