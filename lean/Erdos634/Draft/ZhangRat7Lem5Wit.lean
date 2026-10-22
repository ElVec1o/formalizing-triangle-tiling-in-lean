import Erdos634.Draft.ZhangRat7Lem5
import Erdos634.Draft.ZhangRat6Cor1

/-!
# Witness for `ZhangRat7Lem5.zhang_lemma5_geom`

Every hypothesis is satisfied by the 3575-tile triangle of Cor 1 (tile `(3,5,7)`, `3575 = 143 * 25`): the Cor 1
region dissection (tile at scale `1/2`) is dilated by `2` (`ZhangRational.transfer`), re-modelled on the integer tile
`(3,5,7)` (`reModel`), exited at the triangle `mkTri B A D` (`toCongruentDissection`), and its three vertex angles are
`2 alpha, 2 beta, alpha + beta` (`cor1_angles` at the doubled points, scale `5`; `alpha + beta = pi/3` from
`model_trig`).  Conclusion obtained: `3575 = 13 * 11 * k^2`.  UNAUDITED.  Credit Zhang (arXiv 2512.22696v4),
Beeson, Beeson-Zhang.
-/

set_option maxHeartbeats 6400000

namespace Erdos634.ZhangRat7Lem5Wit

open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.ZhangRat Erdos634.ZhangRat3
  Erdos634.LaczL22 Erdos634.ZhangSporadic Erdos634.ZhangL1 Erdos634.CertGeom Erdos634.ZhangRat4
  Erdos634.ZhangRational Erdos634.TilePlacement Erdos634.ZhangRat5 Erdos634.ZhangRat6
  Erdos634.ZhangRat7Lem5 Erdos634.Realizable

theorem alpha_add_beta (T : Erdos634.Geometry.Tri) (A B C : ℕ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hh : C * C = A * A + B * B + A * B)
    (h0 : sideOpp T 0 = A) (h1 : sideOpp T 1 = B) (h2 : sideOpp T 2 = C) :
    angleAt T 0 + angleAt T 1 = Real.pi / 3 := by
  obtain ⟨hc0, hc1, hs0, hs1⟩ := model_trig T A B C hA hB hC hh h0 h1 h2
  have hAr : (0 : ℝ) < A := Nat.cast_pos.mpr hA
  have hBr : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  have hCr : (0 : ℝ) < C := Nat.cast_pos.mpr hC
  have hcR : (C : ℝ) ^ 2 = (A : ℝ) ^ 2 + (B : ℝ) ^ 2 + A * B := by
    exact_mod_cast (by nlinarith [hh] : C ^ 2 = A ^ 2 + B ^ 2 + A * B)
  have hr3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hcos : Real.cos (angleAt T 0 + angleAt T 1) = 1 / 2 := by
    rw [Real.cos_add, hc0, hc1, hs0, hs1]
    field_simp
    have : Real.sqrt 3 * A * (Real.sqrt 3 * B) = 3 * A * B := by nlinarith [hr3]
    nlinarith [hcR, this]
  have hsum : angleAt T 0 + angleAt T 1 + angleAt T 2 = Real.pi := Erdos634.Geometry.cornerAngle_sum T
  have g2 : 0 ≤ angleAt T 2 := EuclideanGeometry.angle_nonneg _ _ _
  have g0 : 0 ≤ angleAt T 0 := EuclideanGeometry.angle_nonneg _ _ _
  have g1 : 0 ≤ angleAt T 1 := EuclideanGeometry.angle_nonneg _ _ _
  apply Real.injOn_cos ⟨by linarith, by linarith⟩ ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  rw [hcos, Real.cos_pi_div_three]

theorem angle_dil2 (x1 y1 x2 y2 x3 y3 : ℝ) :
    EuclideanGeometry.angle (mkPt (2 * x1) (2 * y1)) (mkPt (2 * x2) (2 * y2)) (mkPt (2 * x3) (2 * y3))
      = EuclideanGeometry.angle (mkPt x1 y1) (mkPt x2 y2) (mkPt x3 y3) := by
  have e : ∀ a b c d : ℝ, mkPt (2 * a) (2 * b) -ᵥ mkPt (2 * c) (2 * d) = (2 : ℝ) • (mkPt a b -ᵥ mkPt c d) := by
    intro a b c d
    ext i
    fin_cases i <;> simp [mkPt] <;> ring
  unfold EuclideanGeometry.angle
  rw [e, e]
  exact InnerProductGeometry.angle_smul_smul (by norm_num) _ _

theorem lemma5_wit : ∃ k : ℕ, 3575 = (3 + 2 * 5) * (5 + 2 * 3) * k ^ 2 := by
  obtain ⟨R, ha, hb, hc, Ax, Ay, Bx, By, Dx, Dy, hD, ⟨C, hreg, hcong⟩, an1, an2, an3⟩ := cor1
  have hrel : R.c ^ 2 = R.a ^ 2 + R.b ^ 2 + R.a * R.b := by rw [ha, hb, hc]; norm_num
  obtain ⟨R', ha', hb', hc'⟩ := exists_RTri_thm4 3 5 7 (by norm_num) (by norm_num) (by norm_num) 1 one_pos
  have hrel' : R'.c ^ 2 = R'.a ^ 2 + R'.b ^ 2 + R'.a * R'.b := by rw [ha', hb', hc']; norm_num
  have hRa : (R.a : ℝ) = 3 / 2 := by rw [ha]; norm_num
  have hRb : (R.b : ℝ) = 5 / 2 := by rw [hb]; norm_num
  have hRc : (R.c : ℝ) = 7 / 2 := by rw [hc]; norm_num
  have hRa' : (R'.a : ℝ) = 3 := by rw [ha']; norm_num
  have hRb' : (R'.b : ℝ) = 5 := by rw [hb']; norm_num
  have hRc' : (R'.c : ℝ) = 7 := by rw [hc']; norm_num
  have hang0 : angleAt R'.Δ 0 = angleAt R.Δ 0 := by
    rw [tile_angle0 R hrel, tile_angle0 R' hrel', hRa, hRb, hRc, hRa', hRb', hRc']; norm_num
  have hang1 : angleAt R'.Δ 1 = angleAt R.Δ 1 := by
    rw [tile_angle1 R hrel, tile_angle1 R' hrel', hRa, hRb, hRc, hRa', hRb', hRc']; norm_num
  let C1 := reModel C R.Δ hcong
  obtain ⟨C2, hr2, hc2⟩ := transfer C1 2 two_pos R'.Δ (hd_of_three R'.Δ R.Δ 2
    (by rw [R'.hc, R.hc, hRc, hRc']; norm_num)
    (by rw [R'.ha, R.ha, hRa, hRa']; norm_num)
    (by rw [dist_comm (R'.Δ.pts 0), dist_comm (R.Δ.pts 0), R'.hb, R.hb, hRb, hRb']; norm_num))
  let C3 := reModel C2 R'.Δ hc2
  have hreg3 : C3.region = TriSet (2 * Ax) (2 * Ay) (2 * Dx) (2 * Dy) (2 * Bx) (2 * By) := by
    show C2.region = _
    rw [hr2]
    show (homothetyEquiv 0 2 two_pos.ne') '' C.region = _
    rw [hom_image_eq 2 two_pos, hreg, dil_TriSet 2 two_pos]
  have hD' : 0 < det3 (2 * Bx) (2 * By) (2 * Ax) (2 * Ay) (2 * Dx) (2 * Dy) := by
    have : det3 (2 * Bx) (2 * By) (2 * Ax) (2 * Ay) (2 * Dx) (2 * Dy) = 4 * det3 Ax Ay Dx Dy Bx By := by
      simp only [det3]; ring
    rw [this]; positivity
  have hreg4 : C3.region = (mkTri (2 * Bx) (2 * By) (2 * Ax) (2 * Ay) (2 * Dx) (2 * Dy) hD'.ne').carrier := by
    rw [hreg3, ← TriSet_eq_carrier hD', ← TriSet_rot (2 * Bx) (2 * By) (2 * Ax) (2 * Ay) (2 * Dx) (2 * Dy)]
  let CD := C3.toCongruentDissection _ hreg4
  have hs0 : sideOpp R'.Δ 0 = ((3 : ℕ) : ℝ) := by
    rw [show sideOpp R'.Δ 0 = dist (R'.Δ.pts 1) (R'.Δ.pts 2) from rfl, R'.ha, hRa']; norm_num
  have hs1 : sideOpp R'.Δ 1 = ((5 : ℕ) : ℝ) := by
    rw [show sideOpp R'.Δ 1 = dist (R'.Δ.pts 2) (R'.Δ.pts 0) from rfl, R'.hb, hRb']; norm_num
  have hs2 : sideOpp R'.Δ 2 = ((7 : ℕ) : ℝ) := by
    rw [show sideOpp R'.Δ 2 = dist (R'.Δ.pts 0) (R'.Δ.pts 1) from rfl, R'.hc, hRc']; norm_num
  have hab := alpha_add_beta R'.Δ 3 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) hs0 hs1 hs2
  have t0 : angleAt (mkTri (2 * Bx) (2 * By) (2 * Ax) (2 * Ay) (2 * Dx) (2 * Dy) hD'.ne') 0
      = EuclideanGeometry.angle (mkPt (2 * Ax) (2 * Ay)) (mkPt (2 * Bx) (2 * By)) (mkPt (2 * Dx) (2 * Dy)) := by
    simp [angleAt, cornerAngle]
  have t1 : angleAt (mkTri (2 * Bx) (2 * By) (2 * Ax) (2 * Ay) (2 * Dx) (2 * Dy) hD'.ne') 1
      = EuclideanGeometry.angle (mkPt (2 * Dx) (2 * Dy)) (mkPt (2 * Ax) (2 * Ay)) (mkPt (2 * Bx) (2 * By)) := by
    simp [angleAt, cornerAngle]
  have t2 : angleAt (mkTri (2 * Bx) (2 * By) (2 * Ax) (2 * Ay) (2 * Dx) (2 * Dy) hD'.ne') 2
      = EuclideanGeometry.angle (mkPt (2 * Bx) (2 * By)) (mkPt (2 * Dx) (2 * Dy)) (mkPt (2 * Ax) (2 * Ay)) := by
    simp [angleAt, cornerAngle]
  obtain ⟨k, hk⟩ := Erdos634.ZhangRat7Lem5.zhang_lemma5_geom 3 5 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) CD (by norm_num) hs0 hs1 hs2
    (by
      show angleAt (mkTri (2 * Bx) (2 * By) (2 * Ax) (2 * Ay) (2 * Dx) (2 * Dy) hD'.ne') 0 = 2 * angleAt R'.Δ 0
      rw [t0, EuclideanGeometry.angle_comm, angle_dil2, an3, hang0])
    (by
      show angleAt (mkTri (2 * Bx) (2 * By) (2 * Ax) (2 * Ay) (2 * Dx) (2 * Dy) hD'.ne') 1 = 2 * angleAt R'.Δ 1
      rw [t1, angle_dil2, an2, hang1])
    (by
      show angleAt (mkTri (2 * Bx) (2 * By) (2 * Ax) (2 * Ay) (2 * Dx) (2 * Dy) hD'.ne') 2
        = angleAt R'.Δ 0 + angleAt R'.Δ 1
      rw [t2, EuclideanGeometry.angle_comm, angle_dil2, an1, hab])
  exact ⟨k, hk⟩

end Erdos634.ZhangRat7Lem5Wit
#print axioms Erdos634.ZhangRat7Lem5Wit.lemma5_wit
