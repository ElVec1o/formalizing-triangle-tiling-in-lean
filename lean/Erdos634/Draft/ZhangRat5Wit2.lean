import Erdos634.Draft.ZhangRat5Wit

/-!
# Witnesses: Prop 11 part 2, the angles clauses, and the case `a > b`

Tile `R = (3/2, 5/2, 7/2)` (`R = (1/2) (3,5,7)`), `m = 10`, `m' = 5`, `m' = 5*1 + 7*0` in `<5, 7>`:
* `wit_prop11_2`: part 2 (the exchange `a <-> b` of `ZhangRat4Wit.wit_prop11_1`): hypothesis triangle tiled by 3575,
  extended triangle by `3575 + 55^2 = 6600` tiles, and the angles `(beta, 2 beta, 3 alpha)` of the extended triangle.
* `wit_prop11_1_angles`: part 1 (7800 tiles) with the angles `(alpha, 2 alpha, 3 beta)`.
* `wit_prop11_swapped`: the tile `swapR R = (5/2, 3/2, 7/2)` (`a > b`) through `zhang_prop11_1_final` and the case
  `b < a`: 3575 and 6600 tiles, angles `(alpha', 2 alpha', 3 beta')`.
All hypotheses of `zhang_prop11_{1,2}_final` are discharged by explicit points (`ptsA`, `ptsB`).  UNAUDITED.
Credit Zhang (arXiv 2512.22696v4), Beeson, Beeson-Zhang, Laczkovich.
-/

set_option maxHeartbeats 3200000

namespace Erdos634.ZhangRat5

open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.ZhangRat Erdos634.ZhangRat3
  Erdos634.LaczL22 Erdos634.ZhangSporadic Erdos634.ZhangL1 Erdos634.CertGeom Erdos634.ZhangRat4
  Erdos634.ZhangRational Erdos634.TilePlacement

theorem wit_prop11_2 : ∃ R : RTri, R.a = 3 / 2 ∧ R.b = 5 / 2 ∧ R.c = 7 / 2 ∧
    ∃ Ax Ay Bx By Dx Dy Cx Cy : ℝ, 0 < det3 Ax Ay Dx Dy Bx By ∧
      (Ax - Dx) ^ 2 + (Ay - Dy) ^ 2 = ((((R.b : ℝ) + 2 * R.a) * R.b * 10)) ^ 2 ∧
      (Bx - Dx) ^ 2 + (By - Dy) ^ 2 = ((((R.a : ℝ) + 2 * R.b) * R.a * 10)) ^ 2 ∧
      (Ax - Bx) ^ 2 + (Ay - By) ^ 2 = (((R.c : ℝ) ^ 2 * 10)) ^ 2 ∧
      (Cx - Bx) ^ 2 + (Cy - By) ^ 2 = (3 * ((R.a : ℝ) + R.b) * R.a * 10) ^ 2 ∧
      (Cx - Ax) ^ 2 + (Cy - Ay) ^ 2 = (((R.b : ℝ) + 2 * R.a) * 10 * R.c) ^ 2 ∧
      TileDis R (TriSet Ax Ay Dx Dy Bx By) 3575 ∧
      TileDis R (TriSet Ax Ay Cx Cy Bx By) 6600 ∧
      EuclideanGeometry.angle (mkPt Ax Ay) (mkPt Cx Cy) (mkPt Bx By) = angleAt R.Δ 1 ∧
      EuclideanGeometry.angle (mkPt Cx Cy) (mkPt Bx By) (mkPt Ax Ay) = 2 * angleAt R.Δ 1 ∧
      EuclideanGeometry.angle (mkPt Bx By) (mkPt Ax Ay) (mkPt Cx Cy) = 3 * angleAt R.Δ 0 := by
  obtain ⟨R, ha, hb, hc, hrel, hab⟩ := rat_wit
  refine ⟨R, ha, hb, hc, ?_⟩
  obtain ⟨A, B, C, k, hA, hB, hk, ea, eb, ec, hh, hcop, hne, H⟩ := zhang_prop11_2_final R hrel
  have ha' : k * (A : ℚ) = 3 / 2 := by rw [← ea, ha]
  have hb' : k * (B : ℚ) = 5 / 2 := by rw [← eb, hb]
  obtain ⟨rfl, rfl, rfl, rfl⟩ := data_357 A B C k hA hk hcop hh ha' hb'
  obtain ⟨Ax, Ay, Bx, By, Dx, Dy, hD, h1, h2, h3⟩ := ptsB
  have hRa : (R.a : ℝ) = 3 / 2 := by rw [ha]; norm_num
  have hRb : (R.b : ℝ) = 5 / 2 := by rw [hb]; norm_num
  have hRc : (R.c : ℝ) = 7 / 2 := by rw [hc]; norm_num
  have g1 : (Ax - Dx) ^ 2 + (Ay - Dy) ^ 2 = (((R.b : ℝ) + 2 * R.a) * R.b * 10) ^ 2 := by
    rw [h1, hRa, hRb]; norm_num
  have g2 : (Bx - Dx) ^ 2 + (By - Dy) ^ 2 = (((R.a : ℝ) + 2 * R.b) * R.a * 10) ^ 2 := by
    rw [h2, hRa, hRb]; norm_num
  have g3 : (Ax - Bx) ^ 2 + (Ay - By) ^ 2 = ((R.c : ℝ) ^ 2 * 10) ^ 2 := by
    rw [h3, hRc]; norm_num
  obtain ⟨Cx, Cy, -, -, e3, e4, T0, -, T1, -⟩ :=
    H 10 5 (by norm_num) (by push_cast; norm_num) ⟨1, 0, by norm_num⟩ Ax Ay Bx By Dx Dy hD g1 g2 g3
  refine ⟨Ax, Ay, Bx, By, Dx, Dy, Cx, Cy, hD, g1, g2, g3, e3, e4, by simpa using T0, by simpa using T1, ?_⟩
  exact angles2_of_sq R hrel Ax Ay Bx By Cx Cy 10 (by norm_num) g3 e4 e3

theorem wit_prop11_1_angles : ∃ R : RTri, R.a = 3 / 2 ∧ R.b = 5 / 2 ∧ R.c = 7 / 2 ∧
    ∃ Ax Ay Bx By Dx Dy Cx Cy : ℝ, 0 < det3 Ax Ay Dx Dy Bx By ∧
      (Ax - Dx) ^ 2 + (Ay - Dy) ^ 2 = ((((R.a : ℝ) + 2 * R.b) * R.a * 10)) ^ 2 ∧
      (Bx - Dx) ^ 2 + (By - Dy) ^ 2 = ((((R.b : ℝ) + 2 * R.a) * R.b * 10)) ^ 2 ∧
      (Ax - Bx) ^ 2 + (Ay - By) ^ 2 = (((R.c : ℝ) ^ 2 * 10)) ^ 2 ∧
      (Cx - Bx) ^ 2 + (Cy - By) ^ 2 = (3 * ((R.a : ℝ) + R.b) * R.b * 10) ^ 2 ∧
      (Cx - Ax) ^ 2 + (Cy - Ay) ^ 2 = (((R.a : ℝ) + 2 * R.b) * 10 * R.c) ^ 2 ∧
      TileDis R (TriSet Ax Ay Dx Dy Bx By) 3575 ∧
      TileDis R (TriSet Ax Ay Cx Cy Bx By) 7800 ∧
      EuclideanGeometry.angle (mkPt Ax Ay) (mkPt Cx Cy) (mkPt Bx By) = angleAt R.Δ 0 ∧
      EuclideanGeometry.angle (mkPt Cx Cy) (mkPt Bx By) (mkPt Ax Ay) = 2 * angleAt R.Δ 0 ∧
      EuclideanGeometry.angle (mkPt Bx By) (mkPt Ax Ay) (mkPt Cx Cy) = 3 * angleAt R.Δ 1 := by
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
  obtain ⟨Cx, Cy, -, -, e3, e4, T0, -, T1, -⟩ :=
    H 10 5 (by norm_num) (by push_cast; norm_num) ⟨1, 0, by norm_num⟩ Ax Ay Bx By Dx Dy hD g1 g2 g3
  refine ⟨Ax, Ay, Bx, By, Dx, Dy, Cx, Cy, hD, g1, g2, g3, e3, e4, by simpa using T0, by simpa using T1, ?_⟩
  exact angles1_of_sq R hrel Ax Ay Bx By Cx Cy 10 (by norm_num) g3 e4 e3

theorem wit_prop11_swapped : ∃ R : RTri, R.a = 5 / 2 ∧ R.b = 3 / 2 ∧ R.c = 7 / 2 ∧
    ∃ Ax Ay Bx By Dx Dy Cx Cy : ℝ, 0 < det3 Ax Ay Dx Dy Bx By ∧
      (Ax - Dx) ^ 2 + (Ay - Dy) ^ 2 = ((((R.a : ℝ) + 2 * R.b) * R.a * 10)) ^ 2 ∧
      (Bx - Dx) ^ 2 + (By - Dy) ^ 2 = ((((R.b : ℝ) + 2 * R.a) * R.b * 10)) ^ 2 ∧
      (Ax - Bx) ^ 2 + (Ay - By) ^ 2 = (((R.c : ℝ) ^ 2 * 10)) ^ 2 ∧
      (Cx - Bx) ^ 2 + (Cy - By) ^ 2 = (3 * ((R.a : ℝ) + R.b) * R.b * 10) ^ 2 ∧
      (Cx - Ax) ^ 2 + (Cy - Ay) ^ 2 = (((R.a : ℝ) + 2 * R.b) * 10 * R.c) ^ 2 ∧
      TileDis R (TriSet Ax Ay Dx Dy Bx By) 3575 ∧
      TileDis R (TriSet Ax Ay Cx Cy Bx By) 6600 ∧
      EuclideanGeometry.angle (mkPt Ax Ay) (mkPt Cx Cy) (mkPt Bx By) = angleAt R.Δ 0 ∧
      EuclideanGeometry.angle (mkPt Cx Cy) (mkPt Bx By) (mkPt Ax Ay) = 2 * angleAt R.Δ 0 ∧
      EuclideanGeometry.angle (mkPt Bx By) (mkPt Ax Ay) (mkPt Cx Cy) = 3 * angleAt R.Δ 1 := by
  obtain ⟨R0, ha0, hb0, hc0, hrel0, hab0⟩ := rat_wit
  let R := swapR R0
  have ha : R.a = 5 / 2 := hb0
  have hb : R.b = 3 / 2 := ha0
  have hc : R.c = 7 / 2 := hc0
  have hrel : R.c ^ 2 = R.a ^ 2 + R.b ^ 2 + R.a * R.b := swapR_rel R0 hrel0
  refine ⟨R, ha, hb, hc, ?_⟩
  obtain ⟨A, B, C, k, hA, hB, hk, ea, eb, ec, hh, hcop, hne, H⟩ := zhang_prop11_1_final R hrel
  have ha' : k * (A : ℚ) = 5 / 2 := by rw [← ea, ha]
  have hb' : k * (B : ℚ) = 3 / 2 := by rw [← eb, hb]
  obtain ⟨rfl, rfl, rfl, rfl⟩ := data_357 B A C k hB hk hcop.symm (by nlinarith [hh]) hb' ha'
  obtain ⟨Ax, Ay, Bx, By, Dx, Dy, hD, h1, h2, h3⟩ := ptsB
  have hRa : (R.a : ℝ) = 5 / 2 := by rw [ha]; norm_num
  have hRb : (R.b : ℝ) = 3 / 2 := by rw [hb]; norm_num
  have hRc : (R.c : ℝ) = 7 / 2 := by rw [hc]; norm_num
  have g1 : (Ax - Dx) ^ 2 + (Ay - Dy) ^ 2 = (((R.a : ℝ) + 2 * R.b) * R.a * 10) ^ 2 := by
    rw [h1, hRa, hRb]; norm_num
  have g2 : (Bx - Dx) ^ 2 + (By - Dy) ^ 2 = (((R.b : ℝ) + 2 * R.a) * R.b * 10) ^ 2 := by
    rw [h2, hRa, hRb]; norm_num
  have g3 : (Ax - Bx) ^ 2 + (Ay - By) ^ 2 = ((R.c : ℝ) ^ 2 * 10) ^ 2 := by
    rw [h3, hRc]; norm_num
  obtain ⟨Cx, Cy, -, -, e3, e4, T0, -, T1, -⟩ :=
    H 10 5 (by norm_num) (by push_cast; norm_num) ⟨1, 0, by norm_num⟩ Ax Ay Bx By Dx Dy hD g1 g2 g3
  refine ⟨Ax, Ay, Bx, By, Dx, Dy, Cx, Cy, hD, g1, g2, g3, e3, e4, by simpa using T0, by simpa using T1, ?_⟩
  exact angles1_of_sq R hrel Ax Ay Bx By Cx Cy 10 (by norm_num) g3 e4 e3

end Erdos634.ZhangRat5

#print axioms Erdos634.ZhangRat5.wit_prop11_2
#print axioms Erdos634.ZhangRat5.wit_prop11_1_angles
#print axioms Erdos634.ZhangRat5.wit_prop11_swapped
