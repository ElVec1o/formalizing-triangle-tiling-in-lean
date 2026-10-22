import Erdos634.Draft.ZhangProp6b

/-!
# Zhang Proposition 11 (arXiv 2512.22696v4, Fig. 12): triangles `(alpha, 2 alpha, 3 beta)`

If the `(2 beta, 2 alpha, alpha+beta)` triangle `A D B` with sides `AD = (a+2b) m a`,
`BD = (b+2a) b m`, `AB = c^2 m` is tiled by `(a,b,c)`, then adding on the ray `BD` beyond `D` the
point `C` with `DC = (a+2b) m b` gives a triangle `ACB` (`BC = 3(a+b) m b`) whose second piece
`A D C` (angle `120` degrees at `D`) is the tile scaled by `k = (a+2b) m`.  Count
`n0 + k^2 = 3 m^2 (a+2b)(a+b)` when `n0 = (a+2b)(b+2a) m^2`.  Part (2) is the exchange `a <-> b`
(not stated separately here).  Credit Zhang (arXiv 2512.22696), Beeson, Beeson-Rosu, Laczkovich.
UNAUDITED.  `c` never appears: `c^2 = a^2+ab+b^2` is the metric condition on `AB`.
-/

set_option maxHeartbeats 1600000

namespace Erdos634.ZhangProp11

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.GlueCut Erdos634.SssCongruent Erdos634.ZhangL1 Erdos634.ZhangPara
  Erdos634.ZhangProp3 Erdos634.ZhangThm4 Erdos634.ZhangSporadic

/-- **Zhang Prop. 11 (1), metric form.**  `A, D, B` counterclockwise with the three side lengths
above and `Dis (RM a b) (A D B) n0`; then `ACB`, `C = D + ((a+2b)/(b+2a)) (D - B)`, carries
`n0 + ((a+2b) m)^2` tiles. -/
theorem zhang_prop11_core (a b m : ℕ) (ha : 0 < a) (hb : 0 < b) (hm : 0 < m) {n0 : ℕ}
    (Ax Ay Bx By Dx Dy : ℝ) (hD : 0 < det3 Ax Ay Dx Dy Bx By)
    (hAD : (Ax - Dx) ^ 2 + (Ay - Dy) ^ 2 = (((a : ℝ) + 2 * b) * m * a) ^ 2)
    (hBD : (Bx - Dx) ^ 2 + (By - Dy) ^ 2 = (((b : ℝ) + 2 * a) * b * m) ^ 2)
    (hAB : (Ax - Bx) ^ 2 + (Ay - By) ^ 2 = (((a : ℝ) ^ 2 + a * b + b ^ 2) * m) ^ 2)
    (hT : Dis (RM a b ha hb) (TriSet Ax Ay Dx Dy Bx By) n0) :
    Dis (RM a b ha hb)
      (TriSet Ax Ay (Dx + ((a + 2 * b : ℝ) / (b + 2 * a)) * (Dx - Bx))
        (Dy + ((a + 2 * b : ℝ) / (b + 2 * a)) * (Dy - By)) Bx By)
      (n0 + ((a + 2 * b) * m) * ((a + 2 * b) * m)) := by
  have ha' : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hb' : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hkn : 0 < (a + 2 * b) * m := Nat.mul_pos (by omega) hm
  have hk : (0 : ℝ) < (((a + 2 * b) * m : ℕ) : ℝ) := Nat.cast_pos.mpr hkn
  have hkc : (((a + 2 * b) * m : ℕ) : ℝ) = ((a : ℝ) + 2 * b) * m := by push_cast; ring
  have hk0 : ((a : ℝ) + 2 * b) * m ≠ 0 := by positivity
  have hl0 : ((b : ℝ) + 2 * a) ≠ 0 := by positivity
  have hs : (a : ℝ) + 2 * b ≠ 0 := by positivity
  set lam : ℝ := ((a : ℝ) + 2 * b) / (b + 2 * a) with hlam
  have hlp : 0 < lam := by rw [hlam]; positivity
  set Cx := Dx + lam * (Dx - Bx) with hCx
  set Cy := Dy + lam * (Dy - By) with hCy
  set K : ℝ := ((a : ℝ) + 2 * b) * m with hK
  -- unit tile at D
  set U1x := Dx + (Ax - Dx) / K with hU1x
  set U1y := Dy + (Ay - Dy) / K with hU1y
  set U2x := Dx + (Cx - Dx) / K with hU2x
  set U2y := Dy + (Cy - Dy) / K with hU2y
  have hdet : det3 Dx Dy U1x U1y U2x U2y = lam / K ^ 2 * det3 Ax Ay Dx Dy Bx By := by
    simp only [det3, hU1x, hU1y, hU2x, hU2y, hCx, hCy]
    field_simp
    ring
  have hU : 0 < det3 Dx Dy U1x U1y U2x U2y := by rw [hdet]; positivity
  have hCD : (Cx - Dx) ^ 2 + (Cy - Dy) ^ 2 = (((a : ℝ) + 2 * b) * m * b) ^ 2 := by
    simp only [hCx, hCy]
    have : (lam * (Dx - Bx)) ^ 2 + (lam * (Dy - By)) ^ 2
        = lam ^ 2 * ((Bx - Dx) ^ 2 + (By - Dy) ^ 2) := by ring
    simp only [add_sub_cancel_left]
    rw [this, hBD, hlam]; field_simp
  have hAC : (Cx - Ax) ^ 2 + (Cy - Ay) ^ 2 = (((a : ℝ) + 2 * b) * m) ^ 2 * (a ^ 2 + b ^ 2 + a * b) := by
    -- |C-A|^2 = |u|^2 + 2 lam u.v + lam^2 |v|^2 with u = A-D, v = B-D
    have hdot : (Ax - Dx) * (Bx - Dx) + (Ay - Dy) * (By - Dy)
        = (((a : ℝ) + 2 * b) * m * a) ^ 2 / 2 + (((b : ℝ) + 2 * a) * b * m) ^ 2 / 2
          - (((a : ℝ) ^ 2 + a * b + b ^ 2) * m) ^ 2 / 2 := by
      linear_combination (1/2) * hAD + (1/2) * hBD - (1/2) * hAB
    have e : (Cx - Ax) ^ 2 + (Cy - Ay) ^ 2
        = ((Ax - Dx) ^ 2 + (Ay - Dy) ^ 2) + 2 * lam * ((Ax - Dx) * (Bx - Dx) + (Ay - Dy) * (By - Dy))
          + lam ^ 2 * ((Bx - Dx) ^ 2 + (By - Dy) ^ 2) := by
      simp only [hCx, hCy]; ring
    rw [e, hdot, hAD, hBD, hlam]
    field_simp
    ring
  have h01 : (U1x - Dx) ^ 2 + (U1y - Dy) ^ 2 = (a : ℝ) ^ 2 := by
    simp only [hU1x, hU1y, add_sub_cancel_left]
    have : ((Ax - Dx) / K) ^ 2 + ((Ay - Dy) / K) ^ 2 = ((Ax - Dx) ^ 2 + (Ay - Dy) ^ 2) / K ^ 2 := by
      ring
    rw [this, hAD, hK]; field_simp
  have h02 : (U2x - Dx) ^ 2 + (U2y - Dy) ^ 2 = (b : ℝ) ^ 2 := by
    simp only [hU2x, hU2y, add_sub_cancel_left]
    have : ((Cx - Dx) / K) ^ 2 + ((Cy - Dy) / K) ^ 2 = ((Cx - Dx) ^ 2 + (Cy - Dy) ^ 2) / K ^ 2 := by
      ring
    rw [this, hCD, hK]; field_simp
  have h12 : (U2x - U1x) ^ 2 + (U2y - U1y) ^ 2 = (a : ℝ) ^ 2 + b ^ 2 + a * b := by
    have e : (U2x - U1x) ^ 2 + (U2y - U1y) ^ 2
        = ((Cx - Ax) ^ 2 + (Cy - Ay) ^ 2) / K ^ 2 := by
      simp only [hU1x, hU1y, hU2x, hU2y]; field_simp; ring
    rw [e, hAC, hK]; field_simp
  have hUR := unit_cong1 ha' hb' Dx Dy U1x U1y U2x U2y hU h01 h02 h12
  have hsc := Dis_scaled Dx Dy U1x U1y U2x U2y hU hUR ((a + 2 * b) * m) hkn Ax Ay Cx Cy
    (by rw [hkc, hU1x]; field_simp; ring) (by rw [hkc, hU1y]; field_simp; ring)
    (by rw [hkc, hU2x]; field_simp; ring) (by rw [hkc, hU2y]; field_simp; ring)
  have hsc' := Dis_rot _ _ _ _ _ _ hsc
  -- cevian from A: P = C, Q = B, D = (1-t) P + t Q
  have hl1 : 0 < 1 + lam := by linarith
  refine (Dis_cevian Ax Ay Cx Cy Bx By Dx Dy (lam / (1 + lam)) (by positivity) ?_ ?_ ?_ hD
    hsc' hT).congr rfl (Nat.add_comm _ _)
  · rw [div_lt_one hl1]; linarith
  · simp only [hCx]; field_simp; ring
  · simp only [hCy]; field_simp; ring

/-! ### Witness `(a,b,c) = (3,5,7)`, `m = 5` -/

/-- Prop 11 (1) witness: `ABD` is the `3575`-tile triangle of Prop 6(2) (`A=(-18,0)`, `D=(177,0)`,
`B=(-98,275)` lattice coordinates); the triangle `ACB`, `C = D + (13/11)(D-B)`, carries
`3575 + 65^2 = 7800 = 3*25*13*8` tiles.  Area check: `ABD` has area `3575 T` and `ADC` is the
tile scaled by `65`: `4225 T`. -/
theorem zhang_prop11_357 :
    Dis (RM 3 5 (by norm_num) (by norm_num))
      (TriSet (shx 0 (-18) 0) (shy 0 0)
        (shx 0 177 0 + ((3 + 2 * 5 : ℝ) / (5 + 2 * 3)) * (shx 0 177 0 - shx 0 (-98) 275))
        (shy 0 0 + ((3 + 2 * 5 : ℝ) / (5 + 2 * 3)) * (shy 0 0 - shy 0 275))
        (shx 0 (-98) 275) (shy 0 275)) 7800 := by
  have h := ZhangProp6b.zhang_prop6_2 3 2 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hz := zs_sq
  have hzp := zs_pos
  have := zhang_prop11_core 3 5 5 (by norm_num) (by norm_num) (by norm_num)
    (shx 0 (-18) 0) (shy 0 0) (shx 0 (-98) 275) (shy 0 275) (shx 0 177 0) (shy 0 0)
    (by simp only [det3, shx, shy]; nlinarith)
    (by simp only [shx, shy]; norm_num <;> nlinarith)
    (by simp only [shx, shy]; norm_num <;> nlinarith)
    (by simp only [shx, shy]; norm_num <;> nlinarith)
    (n0 := 3575) (h.congr (by
      simp only [ZhangProp6b.qAu, ZhangProp6.pFu, ZhangProp6.pX, ZhangProp6.pY, ZhangProp6.pW,
        ZhangProp6b.qBu, ZhangProp6b.qBv, ZhangLat.LT]
      norm_num <;> rfl) (by norm_num))
  exact this.congr rfl (by norm_num)

end Erdos634.ZhangProp11
