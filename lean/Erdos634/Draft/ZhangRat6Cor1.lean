import Erdos634.Draft.ZhangRat5Wit2

/-!
# Zhang Corollary 1 with the ANGLES of the tiled triangle (arXiv 2512.22696v4)

Printed: "There exists a tiling of a triangle with angles `(2 beta, 2 alpha, alpha + beta)` into 3575 copies of
`(3,5,7)`."  Earlier (`ZhangProp6b.zhang_prop6_2_357`) the 3575-tiling of a region `LT ...` existed without
a statement about its angles.  Here, for ANY tile `R` with `c^2 = a^2+ab+b^2` and any triangle `A D B` with
`|AD| = (a+2b) a m`, `|BD| = (b+2a) b m`, `|AB| = c^2 m` (the triangle of Prop 6(2) at `m`-scale):
angle at `D` is `pi/3 = alpha + beta`, at `A` it is `2 beta`, at `B` it is `2 alpha`
(`alpha = angleAt R.Δ 0`, `beta = angleAt R.Δ 1`).  `cor1`: the witness for the tile `(3/2,5/2,7/2)`
(= `(3,5,7)` scaled by `1/2`): points with `TileDis R (TriSet A D B) 3575` AND these three angles.
UNAUDITED.  Credit Zhang (arXiv 2512.22696v4), Beeson, Beeson-Zhang, Laczkovich.
-/

set_option maxHeartbeats 3200000

namespace Erdos634.ZhangRat6

open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.ZhangRat Erdos634.ZhangRat3
  Erdos634.LaczL22 Erdos634.ZhangSporadic Erdos634.ZhangL1 Erdos634.CertGeom Erdos634.ZhangRat4
  Erdos634.ZhangRational Erdos634.TilePlacement Erdos634.ZhangRat5

theorem angle_pi3 (D A B : Plane) (p q c m : ℝ) (hp : 0 < p) (hq : 0 < q) (hc0 : 0 < c) (hm : 0 < m)
    (hc : c ^ 2 = p ^ 2 + p * q + q ^ 2)
    (hAD : dist A D = (p + 2 * q) * p * m) (hBD : dist B D = (q + 2 * p) * q * m)
    (hAB : dist A B = c ^ 2 * m) :
    EuclideanGeometry.angle A D B = Real.pi / 3 := by
  have h := ZhangRat4.cosang A D B (u := (p + 2 * q) * p * m) (w := (q + 2 * p) * q * m) (s := c ^ 2 * m)
    hAD hBD hAB (by positivity) (by positivity)
  have hcos : Real.cos (EuclideanGeometry.angle A D B) = 1 / 2 := by
    rw [h, div_eq_iff (by positivity)]
    linear_combination (m ^ 2 * (-(c ^ 2) - (p ^ 2 + p * q + q ^ 2))) * hc
  apply Real.injOn_cos ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  rw [hcos, Real.cos_pi_div_three]

theorem angle_double (V X Y : Plane) (p q c m : ℝ) (hp : 0 < p) (hq : 0 < q) (hc0 : 0 < c) (hm : 0 < m)
    (hc : c ^ 2 = p ^ 2 + p * q + q ^ 2)
    (hXV : dist X V = (p + 2 * q) * p * m) (hYV : dist Y V = c ^ 2 * m)
    (hXY : dist X Y = (q + 2 * p) * q * m) :
    EuclideanGeometry.angle X V Y = 2 * Real.arccos ((2 * p + q) / (2 * c)) := by
  set y : ℝ := (2 * p + q) / (2 * c) with hy
  have hypos : 0 < y := by positivity
  have hy1 : y ≤ 1 := by
    rw [hy, div_le_one (by positivity)]
    nlinarith [sq_nonneg (c - (2 * p + q)), mul_pos hp hq]
  have hy2 : 1 / 2 ≤ y := by
    rw [hy, le_div_iff₀ (by positivity)]
    nlinarith [mul_pos hp hq, sq_nonneg (c - (2 * p + q)), mul_pos hp hp]
  have hφ : Real.cos (Real.arccos y) = y := Real.cos_arccos (by linarith) hy1
  have hφ0 : 0 ≤ Real.arccos y := Real.arccos_nonneg y
  have hφ3 : Real.arccos y ≤ Real.pi / 3 := by
    by_contra hcon
    push Not at hcon
    have h1 := Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos]) (Real.arccos_le_pi y) hcon
    rw [Real.cos_pi_div_three, hφ] at h1
    linarith
  have hx2 : 4 * c ^ 2 * y ^ 2 = (2 * p + q) ^ 2 := by
    rw [hy]; field_simp; norm_num
  have h := ZhangRat4.cosang X V Y (u := (p + 2 * q) * p * m) (w := c ^ 2 * m) (s := (q + 2 * p) * q * m)
    hXV hYV hXY (by positivity) (by positivity)
  have hcos : Real.cos (EuclideanGeometry.angle X V Y) = 2 * y ^ 2 - 1 := by
    rw [h, div_eq_iff (by positivity)]
    linear_combination (-((p + 2 * q) * p * m ^ 2)) * hx2
      + (m ^ 2 * (c ^ 2 + (p ^ 2 + p * q + q ^ 2) + 2 * (p + 2 * q) * p)) * hc
  apply Real.injOn_cos ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
    ⟨by linarith, by linarith [Real.pi_pos]⟩
  rw [hcos, Real.cos_two_mul, hφ]

section tri
variable (R : RTri) (hrel : R.c ^ 2 = R.a ^ 2 + R.b ^ 2 + R.a * R.b)
include hrel

theorem cor1_angles (Ax Ay Bx By Dx Dy m : ℝ) (hm : 0 < m)
    (eAD : (Ax - Dx) ^ 2 + (Ay - Dy) ^ 2 = (((R.a : ℝ) + 2 * R.b) * R.a * m) ^ 2)
    (eBD : (Bx - Dx) ^ 2 + (By - Dy) ^ 2 = (((R.b : ℝ) + 2 * R.a) * R.b * m) ^ 2)
    (eAB : (Ax - Bx) ^ 2 + (Ay - By) ^ 2 = ((R.c : ℝ) ^ 2 * m) ^ 2) :
    EuclideanGeometry.angle (mkPt Ax Ay) (mkPt Dx Dy) (mkPt Bx By) = Real.pi / 3 ∧
    EuclideanGeometry.angle (mkPt Dx Dy) (mkPt Ax Ay) (mkPt Bx By) = 2 * angleAt R.Δ 1 ∧
    EuclideanGeometry.angle (mkPt Dx Dy) (mkPt Bx By) (mkPt Ax Ay) = 2 * angleAt R.Δ 0 := by
  have ha : (0 : ℝ) < R.a := by exact_mod_cast R.pa
  have hb : (0 : ℝ) < R.b := by exact_mod_cast R.pb
  have hc : (0 : ℝ) < R.c := by exact_mod_cast R.pc
  have hcR : (R.c : ℝ) ^ 2 = (R.a : ℝ) ^ 2 + (R.b : ℝ) ^ 2 + R.a * R.b := by exact_mod_cast hrel
  have dAD : dist (mkPt Ax Ay) (mkPt Dx Dy) = ((R.a : ℝ) + 2 * R.b) * R.a * m :=
    dist_mk_of_sq (by positivity) eAD
  have dBD : dist (mkPt Bx By) (mkPt Dx Dy) = ((R.b : ℝ) + 2 * R.a) * R.b * m :=
    dist_mk_of_sq (by positivity) eBD
  have dAB : dist (mkPt Ax Ay) (mkPt Bx By) = (R.c : ℝ) ^ 2 * m :=
    dist_mk_of_sq (by positivity) eAB
  have hc' : (R.c : ℝ) ^ 2 = (R.a : ℝ) ^ 2 + R.a * R.b + (R.b : ℝ) ^ 2 := by rw [hcR]; ring
  have hc'' : (R.c : ℝ) ^ 2 = (R.b : ℝ) ^ 2 + R.b * R.a + (R.a : ℝ) ^ 2 := by rw [hcR]; ring
  refine ⟨angle_pi3 _ _ _ _ _ _ _ ha hb hc hm hc' dAD dBD dAB, ?_, ?_⟩
  · rw [ZhangRat4.tile_angle1 R hrel]
    exact angle_double _ _ _ _ _ _ _ ha hb hc hm hc' (by rw [dist_comm]; exact dAD)
      (by rw [dist_comm]; exact dAB) (by rw [dist_comm]; exact dBD)
  · rw [ZhangRat4.tile_angle0 R hrel]
    have := angle_double (mkPt Bx By) (mkPt Dx Dy) (mkPt Ax Ay) (R.b : ℝ) (R.a : ℝ) _ _ hb ha hc hm
      hc'' (by rw [dist_comm]; exact dBD) dAB (by rw [dist_comm]; exact dAD)
    rw [this]
    congr 2
    rw [show (2 * (R.b : ℝ) + R.a) = (R.a + 2 * R.b) by ring]

end tri

/-- **Zhang Corollary 1 (printed form, tile `(3,5,7)` at scale `1/2`).** -/
theorem cor1 : ∃ R : RTri, R.a = 3 / 2 ∧ R.b = 5 / 2 ∧ R.c = 7 / 2 ∧
    ∃ Ax Ay Bx By Dx Dy : ℝ, 0 < det3 Ax Ay Dx Dy Bx By ∧
      TileDis R (TriSet Ax Ay Dx Dy Bx By) 3575 ∧
      EuclideanGeometry.angle (mkPt Ax Ay) (mkPt Dx Dy) (mkPt Bx By) = Real.pi / 3 ∧
      EuclideanGeometry.angle (mkPt Dx Dy) (mkPt Ax Ay) (mkPt Bx By) = 2 * angleAt R.Δ 1 ∧
      EuclideanGeometry.angle (mkPt Dx Dy) (mkPt Bx By) (mkPt Ax Ay) = 2 * angleAt R.Δ 0 := by
  obtain ⟨R, ha, hb, hc, hrel, hab⟩ := rat_wit
  refine ⟨R, ha, hb, hc, ?_⟩
  obtain ⟨A, B, C, k, hA, hB, hk, ea, eb, ec, hh, hcop, hne, H⟩ := zhang_prop11_1_final R hrel
  have ha' : k * (A : ℚ) = 3 / 2 := by rw [← ea, ha]
  have hb' : k * (B : ℚ) = 5 / 2 := by rw [← eb, hb]
  obtain ⟨rfl, rfl, rfl, rfl⟩ := data_357 A B C k hA hk hcop hh ha' hb'
  obtain ⟨Ax, Ay, Bx, By, Dx, Dy, hD, h1, h2, h3⟩ := ptsA
  have hRa : (R.a : ℝ) = 3 / 2 := by rw [ha]; norm_num
  have hRb : (R.b : ℝ) = 5 / 2 := by rw [hb]; norm_num
  have hRc : (R.c : ℝ) = 7 / 2 := by rw [hc]; norm_num
  have g1 : (Ax - Dx) ^ 2 + (Ay - Dy) ^ 2 = (((R.a : ℝ) + 2 * R.b) * R.a * 10) ^ 2 := by
    rw [h1, hRa, hRb]; norm_num
  have g2 : (Bx - Dx) ^ 2 + (By - Dy) ^ 2 = (((R.b : ℝ) + 2 * R.a) * R.b * 10) ^ 2 := by
    rw [h2, hRa, hRb]; norm_num
  have g3 : (Ax - Bx) ^ 2 + (Ay - By) ^ 2 = ((R.c : ℝ) ^ 2 * 10) ^ 2 := by
    rw [h3, hRc]; norm_num
  obtain ⟨Cx, Cy, -, -, -, -, T0, -, -, -⟩ :=
    H 10 5 (by norm_num) (by push_cast; norm_num) ⟨1, 0, by norm_num⟩ Ax Ay Bx By Dx Dy hD g1 g2 g3
  obtain ⟨a1, a2, a3⟩ := cor1_angles R hrel Ax Ay Bx By Dx Dy 10 (by norm_num) g1 g2 g3
  exact ⟨Ax, Ay, Bx, By, Dx, Dy, hD, by simpa using T0, a1, a2, a3⟩

end Erdos634.ZhangRat6

#print axioms Erdos634.ZhangRat6.cor1
#print axioms Erdos634.ZhangRat6.cor1_angles
