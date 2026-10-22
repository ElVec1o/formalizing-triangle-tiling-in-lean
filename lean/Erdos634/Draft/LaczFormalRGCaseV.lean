-- Draft/LaczFormalRGCaseV.lean -- S4 of PLAN_THM21: assembly of Case V (gamma = pi/2) of Laczkovich's Theorem 2.1, subcase Va (`a` not a nonnegative rational combination of `b, c`).
-- A quadrilateral with four right angles is a parallelogram; Lemma 4.1 + `some_side_multiple` give conclusion (i).
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 9, Lemma 4.1, Lemma 9.1), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRGCorner

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21

namespace Erdos634.Draft.LaczFormal.RG

/-- Right angle at `v_i` in coordinates. -/
theorem inner_of_angle (P : ConvPoly 4) (i : Fin 4) (h : P.angle i = Real.pi / 2) :
    (P.v (i - 1) 0 - P.v i 0) * (P.v (i + 1) 0 - P.v i 0) + (P.v (i - 1) 1 - P.v i 1) * (P.v (i + 1) 1 - P.v i 1) = 0 := by
  unfold ConvPoly.angle cornerAngle EuclideanGeometry.angle at h
  have := (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _).mpr h
  simpa [PiLp.inner_apply, Fin.sum_univ_two, mul_comm] using this

theorem sum_sq_zero' {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 ∧ y = 0 := by
  constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]

/-- **A quadrilateral with four right angles is a parallelogram (rectangle).** -/
theorem rect_of_angles (P : ConvPoly 4) (h : ∀ i, P.angle i = Real.pi / 2) : P.v 0 + P.v 2 = P.v 1 + P.v 3 := by
  have i0 := inner_of_angle P 0 (h 0)
  have i1 := inner_of_angle P 1 (h 1)
  have i2 := inner_of_angle P 2 (h 2)
  have i3 := inner_of_angle P 3 (h 3)
  have e1 : (0 : Fin 4) - 1 = 3 := by decide
  have e2 : (0 : Fin 4) + 1 = 1 := by decide
  have e3 : (1 : Fin 4) - 1 = 0 := by decide
  have e4 : (1 : Fin 4) + 1 = 2 := by decide
  have e5 : (2 : Fin 4) - 1 = 1 := by decide
  have e6 : (2 : Fin 4) + 1 = 3 := by decide
  have e7 : (3 : Fin 4) - 1 = 2 := by decide
  have e8 : (3 : Fin 4) + 1 = 0 := by decide
  rw [e1, e2] at i0; rw [e3, e4] at i1; rw [e5, e6] at i2; rw [e7, e8] at i3
  set x0 := P.v 0 0; set y0 := P.v 0 1; set x1 := P.v 1 0; set y1 := P.v 1 1
  set x2 := P.v 2 0; set y2 := P.v 2 1; set x3 := P.v 3 0; set y3 := P.v 3 1
  -- e0 = v1 - v0 = (a,b), e1 = (c,d), e2 = (e,f), e3 = (g,h)
  have k1 : (x1 - x0) * (x2 - x1) + (y1 - y0) * (y2 - y1) = 0 := by linarith [i1]
  have k2 : (x2 - x1) * (x3 - x2) + (y2 - y1) * (y3 - y2) = 0 := by linarith [i2]
  have k3 : (x3 - x2) * (x0 - x3) + (y3 - y2) * (y0 - y3) = 0 := by linarith [i3]
  have k0 : (x0 - x3) * (x1 - x0) + (y0 - y3) * (y1 - y0) = 0 := by linarith [i0]
  -- with a = x1-x0, b = y1-y0, c = x2-x1, d = y2-y1, e = x3-x2, f = y3-y2:  x0-x3 = -(a+c+e), y0-y3 = -(b+d+f)
  have hx : x0 - x3 = -((x1 - x0) + (x2 - x1) + (x3 - x2)) := by ring
  have hy : y0 - y3 = -((y1 - y0) + (y2 - y1) + (y3 - y2)) := by ring
  rw [hx, hy] at k3 k0
  have l1 : (x1 - x0) * (x3 - x2) + (y1 - y0) * (y3 - y2) = -((x1 - x0) ^ 2 + (y1 - y0) ^ 2) := by linear_combination (-1 : ℝ) * k0 - k1
  have l2 : (x1 - x0) * (x3 - x2) + (y1 - y0) * (y3 - y2) = -((x3 - x2) ^ 2 + (y3 - y2) ^ 2) := by linear_combination (-1 : ℝ) * k3 - k2
  have hsq : (x1 - x0 + (x3 - x2)) ^ 2 + (y1 - y0 + (y3 - y2)) ^ 2 = 0 := by linear_combination l1 + l2
  obtain ⟨hxs, hys⟩ := sum_sq_zero' hsq
  ext j
  fin_cases j
  · show x0 + x2 = x1 + x3; linarith
  · show y0 + y2 = y1 + y3; linarith

end Erdos634.Draft.LaczFormal.RG
