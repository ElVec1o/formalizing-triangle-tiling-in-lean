import Erdos634.Draft.ZhangRat5All
import Erdos634.Draft.ZhangRat4Wit
import Erdos634.Draft.ZhangRat4Angles

/-!
# Witnesses for the unified Prop 11 (`ZhangRat5All`), part 2, the exchange `a <-> b`, and the angles clause

* `angles1_of_sq`, `angles2_of_sq`: the angles clause of Prop 11 (1), (2) (`ZhangRat4Angles`) stated for the points
  `mkPt` from the SQUARED side lengths delivered by the conclusions of `zhang_prop11_{1,2}_final`.
* `ptsA`, `ptsB`: explicit points (rational tile `(3/2, 5/2, 7/2)`, `m = 10`, `m' = 5`) for the hypothesis
  triangle in the order `(AD, BD) = (195/2, 275/2)` resp. `(275/2, 195/2)` (reflection of the Prop 6(2) triangle
  of `ZhangRat2.prop11_wit`, halved).
* `wit_prop11_2`: part 2 for the tile `(3/2,5/2,7/2)`: hypothesis triangle tiled by 3575, extended triangle by
  `3575 + 55^2 = 6600 = 3 m^2 (b+2a)(a+b)` tiles, and the angles `(beta, 2 beta, 3 alpha)`.
* `wit_prop11_1_angles`: part 1 with the angles `(alpha, 2 alpha, 3 beta)` (7800 tiles).
* `wit_prop11_swapped`: the tile `swapR R = (5/2, 3/2, 7/2)` with `a > b`: part 1 (the exchange of part 2), with
  the same points as `ptsB`, 3575 and 7800 tiles.
Every hypothesis (orientation, three squared lengths, `k m = m'`, `m' in <max(A,B), C>`) is satisfied.  UNAUDITED.
Credit Zhang (arXiv 2512.22696v4), Beeson, Beeson-Zhang, Laczkovich.
-/

set_option maxHeartbeats 3200000

namespace Erdos634.ZhangRat5

open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.ZhangRat Erdos634.ZhangRat3
  Erdos634.LaczL22 Erdos634.ZhangSporadic Erdos634.ZhangL1 Erdos634.CertGeom Erdos634.ZhangRat4
  Erdos634.ZhangRational Erdos634.TilePlacement

theorem dist_mk_of_sq {x1 y1 x2 y2 r : ℝ} (hr : 0 ≤ r) (h : (x1 - x2) ^ 2 + (y1 - y2) ^ 2 = r ^ 2) :
    dist (mkPt x1 y1) (mkPt x2 y2) = r :=
  dist_eq_of_sq dist_nonneg hr (by rw [dist_sq_mkPt]; exact h)

section angles
variable (R : RTri) (hrel : R.c ^ 2 = R.a ^ 2 + R.b ^ 2 + R.a * R.b)
include hrel

theorem angles1_of_sq (Ax Ay Bx By Cx Cy m : ℝ) (hm : 0 < m)
    (eAB : (Ax - Bx) ^ 2 + (Ay - By) ^ 2 = ((R.c : ℝ) ^ 2 * m) ^ 2)
    (eAC : (Cx - Ax) ^ 2 + (Cy - Ay) ^ 2 = (((R.a : ℝ) + 2 * R.b) * m * R.c) ^ 2)
    (eBC : (Cx - Bx) ^ 2 + (Cy - By) ^ 2 = (3 * ((R.a : ℝ) + R.b) * R.b * m) ^ 2) :
    EuclideanGeometry.angle (mkPt Ax Ay) (mkPt Cx Cy) (mkPt Bx By) = angleAt R.Δ 0 ∧
      EuclideanGeometry.angle (mkPt Cx Cy) (mkPt Bx By) (mkPt Ax Ay) = 2 * angleAt R.Δ 0 ∧
      EuclideanGeometry.angle (mkPt Bx By) (mkPt Ax Ay) (mkPt Cx Cy) = 3 * angleAt R.Δ 1 := by
  have ha : (0 : ℝ) < R.a := by exact_mod_cast R.pa
  have hb : (0 : ℝ) < R.b := by exact_mod_cast R.pb
  have hc : (0 : ℝ) < R.c := by exact_mod_cast R.pc
  refine prop11_1_angles R hrel _ _ _ m hm ?_ ?_ ?_
  · exact dist_mk_of_sq (by positivity) eAB
  · exact dist_mk_of_sq (by positivity) (by rw [← eAC]; ring)
  · exact dist_mk_of_sq (by positivity) (by rw [← eBC]; ring)

theorem angles2_of_sq (Ax Ay Bx By Cx Cy m : ℝ) (hm : 0 < m)
    (eAB : (Ax - Bx) ^ 2 + (Ay - By) ^ 2 = ((R.c : ℝ) ^ 2 * m) ^ 2)
    (eAC : (Cx - Ax) ^ 2 + (Cy - Ay) ^ 2 = (((R.b : ℝ) + 2 * R.a) * m * R.c) ^ 2)
    (eBC : (Cx - Bx) ^ 2 + (Cy - By) ^ 2 = (3 * ((R.a : ℝ) + R.b) * R.a * m) ^ 2) :
    EuclideanGeometry.angle (mkPt Ax Ay) (mkPt Cx Cy) (mkPt Bx By) = angleAt R.Δ 1 ∧
      EuclideanGeometry.angle (mkPt Cx Cy) (mkPt Bx By) (mkPt Ax Ay) = 2 * angleAt R.Δ 1 ∧
      EuclideanGeometry.angle (mkPt Bx By) (mkPt Ax Ay) (mkPt Cx Cy) = 3 * angleAt R.Δ 0 := by
  have ha : (0 : ℝ) < R.a := by exact_mod_cast R.pa
  have hb : (0 : ℝ) < R.b := by exact_mod_cast R.pb
  have hc : (0 : ℝ) < R.c := by exact_mod_cast R.pc
  refine prop11_2_angles R hrel _ _ _ m hm ?_ ?_ ?_
  · exact dist_mk_of_sq (by positivity) eAB
  · exact dist_mk_of_sq (by positivity) (by rw [← eAC]; ring)
  · exact dist_mk_of_sq (by positivity) (by rw [← eBC]; ring)

end angles

/-- points, order `(AD, BD, AB) = (195/2, 275/2, 245/2)`: half of the Prop 6(2) triangle for `(3,5,7)`, `m = 10`. -/
theorem ptsA : ∃ Ax Ay Bx By Dx Dy : ℝ, 0 < det3 Ax Ay Dx Dy Bx By ∧
    (Ax - Dx) ^ 2 + (Ay - Dy) ^ 2 = (195 / 2) ^ 2 ∧
    (Bx - Dx) ^ 2 + (By - Dy) ^ 2 = (275 / 2) ^ 2 ∧
    (Ax - Bx) ^ 2 + (Ay - By) ^ 2 = (245 / 2) ^ 2 := by
  obtain ⟨Ax, Ay, Bx, By, Dx, Dy, hD, h1, h2, h3⟩ := ZhangRat2.prop11_wit
  refine ⟨Ax / 2, Ay / 2, Bx / 2, By / 2, Dx / 2, Dy / 2, ?_, ?_, ?_, ?_⟩
  · have : det3 (Ax / 2) (Ay / 2) (Dx / 2) (Dy / 2) (Bx / 2) (By / 2)
        = (1 / 4) * det3 Ax Ay Dx Dy Bx By := by simp only [det3]; ring
    rw [this]; positivity
  · have e : (Ax / 2 - Dx / 2) ^ 2 + (Ay / 2 - Dy / 2) ^ 2 = (1 / 4) * ((Ax - Dx) ^ 2 + (Ay - Dy) ^ 2) := by ring
    rw [e, h1]; push_cast; norm_num
  · have e : (Bx / 2 - Dx / 2) ^ 2 + (By / 2 - Dy / 2) ^ 2 = (1 / 4) * ((Bx - Dx) ^ 2 + (By - Dy) ^ 2) := by ring
    rw [e, h2]; push_cast; norm_num
  · have e : (Ax / 2 - Bx / 2) ^ 2 + (Ay / 2 - By / 2) ^ 2 = (1 / 4) * ((Ax - Bx) ^ 2 + (Ay - By) ^ 2) := by ring
    rw [e, h3]; push_cast; norm_num

/-- the same triangle with `A` and `B` exchanged (and reflected in the `x`-axis to keep the orientation). -/
theorem ptsB : ∃ Ax Ay Bx By Dx Dy : ℝ, 0 < det3 Ax Ay Dx Dy Bx By ∧
    (Ax - Dx) ^ 2 + (Ay - Dy) ^ 2 = (275 / 2) ^ 2 ∧
    (Bx - Dx) ^ 2 + (By - Dy) ^ 2 = (195 / 2) ^ 2 ∧
    (Ax - Bx) ^ 2 + (Ay - By) ^ 2 = (245 / 2) ^ 2 := by
  obtain ⟨Ax, Ay, Bx, By, Dx, Dy, hD, h1, h2, h3⟩ := ptsA
  refine ⟨Bx, -By, Ax, -Ay, Dx, -Dy, ?_, ?_, ?_, ?_⟩
  · have : det3 Bx (-By) Dx (-Dy) Ax (-Ay) = det3 Ax Ay Dx Dy Bx By := by simp only [det3]; ring
    rw [this]; exact hD
  · rw [← h2]; ring
  · rw [← h1]; ring
  · rw [← h3]; ring

end Erdos634.ZhangRat5

#print axioms Erdos634.ZhangRat5.angles1_of_sq
#print axioms Erdos634.ZhangRat5.angles2_of_sq
#print axioms Erdos634.ZhangRat5.ptsA
#print axioms Erdos634.ZhangRat5.ptsB
