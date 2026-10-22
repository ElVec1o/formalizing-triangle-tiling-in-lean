import Erdos634.Draft.BeesonT24Abs
import Erdos634.Draft.BeesonT14Grid

/-!
# Beeson Theorem 24, general parameters: the parallelogram `G R L V` as strips

`x` strips of cells with sides `(U1, V1)` and `y` strips of cells with sides `(c1 U1, c2 V1)` stacked along `V1`.
Credit Beeson (arXiv 1206.2229), Zhang (arXiv 2512.22696).  UNAUDITED.
-/

namespace Erdos634.BeesonT24Strips

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.GlueCut Erdos634.SssCongruent Erdos634.ZhangL1 Erdos634.ZhangPara
  Erdos634.ZhangSporadic Erdos634.ZhangThm4 Erdos634.BeesonT14Chart Erdos634.BeesonT14Abs
  Erdos634.BeesonT14Piece Erdos634.BeesonT14Grid Erdos634.BeesonT24Abs

variable {Rt : Tri} {α β : ℝ}

/-- one group of strips: `GrlvP` is the parallelogram `PgP` -/
theorem grlv_iff_pgp {ux uw vx vw Gx Gw m n Rx Rw Lx Lw Vx Vw : ℝ} (hm : 0 < m) (hn : 0 < n)
    (hRx : Rx = Gx + m * ux) (hRw : Rw = Gw + m * uw)
    (hLx : Lx = Rx + n * vx) (hLw : Lw = Rw + n * vw)
    (hVx : Vx = Gx + n * vx) (hVw : Vw = Gw + n * vw) (X W : ℝ) :
    GrlvP Gx Gw Rx Rw Lx Lw Vx Vw X W ↔ PgP ux uw vx vw Gx Gw m n X W :=
  (pgp_iff hm hn hRx hRw hLx hLw hVx hVw X W).symm

theorem grlv_one (hα : 0 < α) (hβ : 0 < β) {ux uw vx vw : ℝ} (hu : ux ≠ 0 ∨ uw ≠ 0)
    (hv : vx ≠ 0 ∨ vw ≠ 0)
    (hcell : ∀ Ox Ow, Dis Rt (CS α β (PgP ux uw vx vw Ox Ow 1 1)) 2) (m x : ℕ)
    (Gx Gw Rx Rw Lx Lw Vx Vw : ℝ)
    (hRx : Rx = Gx + (m + 1 : ℕ) * ux) (hRw : Rw = Gw + (m + 1 : ℕ) * uw)
    (hLx : Lx = Rx + (x + 1 : ℕ) * vx) (hLw : Lw = Rw + (x + 1 : ℕ) * vw)
    (hVx : Vx = Gx + (x + 1 : ℕ) * vx) (hVw : Vw = Gw + (x + 1 : ℕ) * vw) :
    Dis Rt (CS α β (GrlvP Gx Gw Rx Rw Lx Lw Vx Vw)) (2 * (m + 1) * (x + 1)) := by
  have hm : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hn : (0 : ℝ) < ((x + 1 : ℕ) : ℝ) := by positivity
  refine (grid_dis hα hβ hu hv hcell x m Gx Gw).congr ?_ rfl
  ext q
  exact (grlv_iff_pgp hm hn hRx hRw hLx hLw hVx hVw _ _).symm

set_option maxHeartbeats 4000000 in
theorem grlv_two (hα : 0 < α) (hβ : 0 < β) {ux uw vx vw : ℝ} (hu : ux ≠ 0 ∨ uw ≠ 0)
    (hv : vx ≠ 0 ∨ vw ≠ 0) (hδ : 0 < ux * vw - uw * vx) (c1 c2 : ℝ) (hc1 : 0 < c1) (hc2 : 0 < c2)
    (u2x u2w v2x v2w : ℝ) (e1 : u2x = c1 * ux) (e2 : u2w = c1 * uw) (e3 : v2x = c2 * vx)
    (e4 : v2w = c2 * vw)
    (hcellA : ∀ Ox Ow, Dis Rt (CS α β (PgP ux uw vx vw Ox Ow 1 1)) 2)
    (hcellB : ∀ Ox Ow, Dis Rt (CS α β (PgP u2x u2w v2x v2w Ox Ow 1 1)) 2)
    (m1 m2 x y : ℕ) (hm : ((m1 + 1 : ℕ) : ℝ) = c1 * ((m2 + 1 : ℕ) : ℝ))
    (Gx Gw Rx Rw Lx Lw Vx Vw : ℝ)
    (hRx : Rx = Gx + (m1 + 1 : ℕ) * ux) (hRw : Rw = Gw + (m1 + 1 : ℕ) * uw)
    (hLx : Lx = Rx + ((x + 1 : ℕ) : ℝ) * vx + ((y + 1 : ℕ) : ℝ) * v2x)
    (hLw : Lw = Rw + ((x + 1 : ℕ) : ℝ) * vw + ((y + 1 : ℕ) : ℝ) * v2w)
    (hVx : Vx = Gx + ((x + 1 : ℕ) : ℝ) * vx + ((y + 1 : ℕ) : ℝ) * v2x)
    (hVw : Vw = Gw + ((x + 1 : ℕ) : ℝ) * vw + ((y + 1 : ℕ) : ℝ) * v2w) :
    Dis Rt (CS α β (GrlvP Gx Gw Rx Rw Lx Lw Vx Vw))
      (2 * (m1 + 1) * (x + 1) + 2 * (m2 + 1) * (y + 1)) := by
  subst e1 e2 e3 e4
  have hM1 : (0 : ℝ) < ((m1 + 1 : ℕ) : ℝ) := by positivity
  have hM2 : (0 : ℝ) < ((m2 + 1 : ℕ) : ℝ) := by positivity
  have hX : (0 : ℝ) < ((x + 1 : ℕ) : ℝ) := by positivity
  have hY : (0 : ℝ) < ((y + 1 : ℕ) : ℝ) := by positivity
  set M1 : ℝ := ((m1 + 1 : ℕ) : ℝ) with hM1d
  set M2 : ℝ := ((m2 + 1 : ℕ) : ℝ) with hM2d
  set X1 : ℝ := ((x + 1 : ℕ) : ℝ) with hX1d
  set Y1 : ℝ := ((y + 1 : ℕ) : ℝ) with hY1d
  have hu' : c1 * ux ≠ 0 ∨ c1 * uw ≠ 0 :=
    hu.imp (fun h => mul_ne_zero hc1.ne' h) (fun h => mul_ne_zero hc1.ne' h)
  have hv' : c2 * vx ≠ 0 ∨ c2 * vw ≠ 0 :=
    hv.imp (fun h => mul_ne_zero hc2.ne' h) (fun h => mul_ne_zero hc2.ne' h)
  have hA := grid_dis hα hβ hu hv hcellA x m1 Gx Gw
  have hB := grid_dis hα hβ hu' hv' hcellB y m2 (Gx + X1 * vx) (Gw + X1 * vw)
  have g := glueR hα hβ hA hB (Gx + X1 * vx) (Gw + X1 * vw) (Gx + X1 * vx + M1 * ux)
    (Gw + X1 * vw + M1 * uw)
    (hu.imp (fun h e => h (by nlinarith)) (fun h e => h (by nlinarith)))
    (fun X W h => by
      obtain ⟨a1, a2, a3, a4⟩ := h
      have e : lnR (Gx + X1 * vx) (Gw + X1 * vw) (Gx + X1 * vx + M1 * ux) (Gw + X1 * vw + M1 * uw) X W
          = M1 * (cyf ux uw Gx Gw X W - X1 * (ux * vw - uw * vx)) := by
        simp only [lnR, cyf]; ring
      rw [e]
      exact mul_nonpos_of_nonneg_of_nonpos hM1.le (by linarith))
    (fun X W h => by
      obtain ⟨a1, a2, a3, a4⟩ := h
      have e : lnR (Gx + X1 * vx) (Gw + X1 * vw) (Gx + X1 * vx + M1 * ux) (Gw + X1 * vw + M1 * uw) X W
          = M1 / c1 * cyf (c1 * ux) (c1 * uw) (Gx + X1 * vx) (Gw + X1 * vw) X W := by
        simp only [lnR, cyf]; field_simp; ring
      rw [e]
      exact mul_nonneg (div_nonneg hM1.le hc1.le) a3)
  have hn : (0 : ℝ) < X1 + Y1 * c2 := by positivity
  refine (g.congr ?_ (by ring)).congr rfl rfl
  ext q
  simp only [CS, Set.mem_setOf_eq]
  rw [grlv_iff_pgp (ux := ux) (uw := uw) (vx := vx) (vw := vw) (n := X1 + Y1 * c2) hM1 hn hRx hRw (by rw [hLx]; ring) (by rw [hLw]; ring) (by rw [hVx]; ring)
    (by rw [hVw]; ring)]
  simp only [PgP, cxf, cyf]
  -- coordinates
  have eB1 : (q 0 / α - (Gx + X1 * vx)) * (c2 * vw) - (q 1 / β - (Gw + X1 * vw)) * (c2 * vx)
      = c2 * ((q 0 / α - Gx) * vw - (q 1 / β - Gw) * vx) := by ring
  have eB2 : (c1 * ux) * (q 1 / β - (Gw + X1 * vw)) - (c1 * uw) * (q 0 / α - (Gx + X1 * vx))
      = c1 * (ux * (q 1 / β - Gw) - uw * (q 0 / α - Gx) - X1 * (ux * vw - uw * vx)) := by ring
  have eB3 : (c1 * ux) * (c2 * vw) - (c1 * uw) * (c2 * vx) = c1 * c2 * (ux * vw - uw * vx) := by ring
  have k1 : c1 * c2 * (ux * vw - uw * vx) * M2 = c2 * ((ux * vw - uw * vx) * M1) := by
    rw [hm]; ring
  rw [eB1, eB2, eB3, k1]
  set cx := (q 0 / α - Gx) * vw - (q 1 / β - Gw) * vx with hcx
  set cy := ux * (q 1 / β - Gw) - uw * (q 0 / α - Gx) with hcy
  set δ := ux * vw - uw * vx with hδd
  have hcm : c1 * c2 * δ * Y1 = c1 * (c2 * δ * Y1) := by ring
  constructor
  · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
    · refine ⟨h1, h2, h3, ?_⟩
      nlinarith [mul_pos hδ hn, mul_pos (mul_pos hδ hY) hc2]
    · refine ⟨(mul_nonneg_iff_of_pos_left hc2).mp h1, ?_, ?_, ?_⟩
      · exact le_of_mul_le_mul_left h2 hc2
      · have := (mul_nonneg_iff_of_pos_left hc1).mp h3
        nlinarith [mul_pos hδ hX]
      · have := le_of_mul_le_mul_left (by nlinarith [h4] : c1 * (cy - X1 * δ) ≤ c1 * (c2 * δ * Y1)) hc1
        nlinarith
  · rintro ⟨h1, h2, h3, h4⟩
    rcases le_total cy (δ * X1) with h' | h'
    · left; exact ⟨h1, h2, h3, h'⟩
    · right
      refine ⟨mul_nonneg hc2.le h1, mul_le_mul_of_nonneg_left h2 hc2.le, ?_, ?_⟩
      · exact mul_nonneg hc1.le (by linarith)
      · have : c1 * (cy - X1 * δ) ≤ c1 * (c2 * δ * Y1) := mul_le_mul_of_nonneg_left (by nlinarith) hc1.le
        nlinarith

end Erdos634.BeesonT24Strips
