import Erdos634.Draft.LaczFormalL27Ang

/-!
# Laczkovich Theorem 2.4, triples 2, 3, 5: explicit triangles and their angles

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.4, Fig. 5), Beeson, Beeson-Zhang, Zhang.

`B5 = P X R` (angles `β, α+β` at `X, R`; `2α` at `P`), `B2 = P X Y` (`β, β` at `X, Y`), `B3 = A P V` (`α+α` at `P`, `α` at `V`,
`2β` at `A`).  Each carries the explicit angle facts used to transport the dissection to an arbitrary triangle of the shape.
-/

namespace Erdos634.LaczL27

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24 Erdos634.LaczL26 EuclideanGeometry

variable {a : ℝ}

/-! ### plain-coordinate identities -/

theorem idp_L01 (hb : gb a ≠ 0) :
    Qf a (sP a - xL a) (tP a - 0) = kk a ^ 2 * a ^ 2 * (1 - a ^ 2) ^ 2 := by
  unfold Qf sP tP xL kk gb gK at *; field_simp; ring
theorem idp_L12 (hb : gb a ≠ 0) :
    Qf a (xL a - 0) (0 - 0) = kk a ^ 2 * a ^ 4 * (1 - a ^ 2) ^ 2 := by
  unfold Qf xL kk gb gK at *; field_simp; ring
theorem idp_L20 (hb : gb a ≠ 0) :
    Qf a (0 - sP a) (0 - tP a) = kk a ^ 2 * a ^ 2 * (1 - a ^ 2) ^ 4 := by
  unfold Qf sP tP kk gb gK at *; field_simp; ring
theorem idp_R01 (hb : gb a ≠ 0) :
    Qf a (sP a - xY a) (tP a - 0) = kk a ^ 2 * a ^ 2 * (1 - a ^ 2) ^ 2 := by
  unfold Qf sP tP xY kk gb gK at *; field_simp; ring
theorem idp_R12 (hb : gb a ≠ 0) :
    Qf a (xY a - sR a) (0 - 0) = kk a ^ 2 * a ^ 4 * (1 - a ^ 2) ^ 2 := by
  unfold Qf xY sR kk gb gK at *; field_simp; ring
theorem idp_R20 (hb : gb a ≠ 0) :
    Qf a (sR a - sP a) (0 - tP a) = kk a ^ 2 * a ^ 2 * (1 - a ^ 2) ^ 4 := by
  unfold Qf sP tP sR kk gb gK at *; field_simp; ring

/-! ### axis and line rays -/

theorem ang_axis (w d : Plane) (hdet : w 0 * d 1 - w 1 * d 0 ≠ 0) (p : Plane) {x s l c : ℝ} (t : ℝ) (hc : 0 < c)
    (h : s - x = c * (l - x)) :
    ∠ p (chartEquiv 0 w d hdet (mkPt x t)) (chartEquiv 0 w d hdet (mkPt s t))
      = ∠ p (chartEquiv 0 w d hdet (mkPt x t)) (chartEquiv 0 w d hdet (mkPt l t)) := by
  refine angle_ray hc ?_
  rw [chart_pt, chart_pt, chart_pt]
  have e1 : s • w + t • d - (x • w + t • d) = (s - x) • w := by module
  have e2 : l • w + t • d - (x • w + t • d) = (l - x) • w := by module
  rw [e1, e2, smul_smul, ← h]

theorem line_pt (w d : Plane) (hdet : w 0 * d 1 - w 1 * d 0 ≠ 0) (e1 e2 x : ℝ) :
    chartEquiv 0 w d hdet (mkPt (0 + x * e1) (0 + x * e2)) = x • (e1 • w + e2 • d) := by
  rw [chart_pt]; module

theorem ang_line (w d : Plane) (hdet : w 0 * d 1 - w 1 * d 0 ≠ 0) (e1 e2 : ℝ) (p : Plane) {x s l c : ℝ} (hc : 0 < c)
    (h : s - x = c * (l - x)) :
    ∠ p (chartEquiv 0 w d hdet (mkPt (0 + x * e1) (0 + x * e2))) (chartEquiv 0 w d hdet (mkPt (0 + s * e1) (0 + s * e2)))
      = ∠ p (chartEquiv 0 w d hdet (mkPt (0 + x * e1) (0 + x * e2))) (chartEquiv 0 w d hdet (mkPt (0 + l * e1) (0 + l * e2))) := by
  refine angle_ray hc ?_
  rw [line_pt, line_pt, line_pt]
  have : x • (e1 • w + e2 • d) = x • (e1 • w + e2 • d) := rfl
  rw [← sub_smul, ← sub_smul, smul_smul, ← h]

end Erdos634.LaczL27
