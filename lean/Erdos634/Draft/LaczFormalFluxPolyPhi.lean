-- Draft/LaczFormalFluxPolyPhi.lean -- the Laczkovich functional Phi for a convex polygon (DCG 48 (2012), p. 351, formulas (14),(15)):
--   Phi_G(P) := P.flux G.weight = sum_i (side length d_i) * weight(direction of side i),  G a grid character (anchored at a direction),
-- the TURN LEMMA for polygons (direction of side i+1 = direction of side i + (pi - interior angle at v_{i+1})), and formula (15):
-- weight(side i+1) = chi(pi - interior angle) * weight(side i)  when pi - angle lies in the grid.
-- NOTE / UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 7.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalFluxPolyFin
import Erdos634.Draft.FluxPaperCorIntAnchored

open scoped Classical
open Erdos634.Geometry

namespace Erdos634.Draft.LaczFormal.Thm21

variable {M : ℕ} [NeZero M]

namespace ConvPoly
variable (P : ConvPoly M)

theorem cross_e_next (j : Fin M) : 0 < cross (P.e j) (P.e (j + 1)) := by
  have hM := P.three_le
  have h := P.ori_pos hM j
  have e1 : P.e (j + 1) = (P.v (j + 2) - P.v j) - P.e j := by
    unfold e
    rw [(fin_facts hM j).2.2.2.2.2]
    abel
  rw [e1, cross_sub_right, cross_self, sub_zero]
  simpa [e, cross2, cross] using h

theorem pi_sub_angle (j : Fin M) :
    Real.pi - P.angle (j + 1) = InnerProductGeometry.angle (P.e j) (P.e (j + 1)) := by
  have hM := P.three_le
  have h1 : j + 1 + 1 = j + 2 := (fin_facts hM j).2.2.2.2.2
  have h2 : j + 1 - 1 = j := by simp
  unfold ConvPoly.angle cornerAngle EuclideanGeometry.angle
  rw [h2, h1]
  simp only [vsub_eq_sub]
  rw [show P.v j - P.v (j + 1) = -(P.e j) by unfold e; abel,
    InnerProductGeometry.angle_neg_left]
  have : P.v (j + 2) - P.v (j + 1) = P.e (j + 1) := by unfold e; rw [h1]
  rw [this]; ring

theorem sideDir_angle (j : Fin M) : (P.sideDir j).angle = (Complex.arg (toC (P.e j)) : Real.Angle) := by
  unfold Dir.angle
  show ((Complex.arg (toC (‖P.e j‖⁻¹ • P.e j)) : ℝ) : Real.Angle) = _
  rw [map_smul, Complex.real_smul,
    Complex.arg_real_mul _ (inv_pos.mpr (norm_pos_iff.mpr (P.e_ne_zero P.three_le j)))]

/-- **The turn lemma for polygons**: the direction of side `j+1` is the direction of side `j` turned left by `pi - (interior angle at v_{j+1})`. -/
theorem sideDir_turn (j : Fin M) :
    (P.sideDir (j + 1)).angle = (P.sideDir j).angle + ((Real.pi - P.angle (j + 1) : ℝ) : Real.Angle) := by
  rw [P.sideDir_angle, P.sideDir_angle, P.pi_sub_angle]
  exact arg_turn (P.e_ne_zero P.three_le j) (P.e_ne_zero P.three_le (j + 1)) (P.cross_e_next j)

/-- **Formula (15) of Laczkovich**, one step: `weight(side j+1) = chi(pi - angle) * weight(side j)` when `pi - angle` is in the grid. -/
theorem weight_next (G : GridChar ℝ) (j : Fin M) (h : ((Real.pi - P.angle (j + 1) : ℝ) : Real.Angle) ∈ G.L) :
    G.weight (P.sideDir (j + 1)) = G.chi ((Real.pi - P.angle (j + 1) : ℝ) : Real.Angle) * G.weight (P.sideDir j) := by
  unfold GridChar.weight
  rw [P.sideDir_turn, G.val_add _ h]

end ConvPoly

end Erdos634.Draft.LaczFormal.Thm21
