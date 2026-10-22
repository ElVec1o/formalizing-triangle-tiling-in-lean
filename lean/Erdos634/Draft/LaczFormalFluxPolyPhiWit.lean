-- Draft/LaczFormalFluxPolyPhiWit.lean -- WITNESSES for Lemma 7.2 (LaczFormalFluxPolyPhi3): explicit convex polygons with the angle patterns of `lemma72_three/four/five/six`:
--   N = 3: equilateral triangle (0,0),(1,0),(1/2,sqrt3/2);  N = 4: trapezoid (0,0),(2,0),(3/2,sqrt3/2),(1/2,sqrt3/2);
--   N = 5: pentagon (0,0),(2,0),(1,sqrt3),(0,sqrt3),(-1/2,sqrt3/2);  N = 6: regular hexagon.
-- Each satisfies the hypotheses, the conclusions are obtained, and the side relations / Phi value are checked on the actual side lengths (negative control: the values are those of the lemma).
-- NOTE / UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Lemma 7.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalFluxPolyPhi3
import Erdos634.Draft.LaczFormalThm21AreaWit
import Erdos634.CertCoord

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.Thm21

/-- Angle at `q` of three explicit points, from the two squared lengths and the inner product. -/
theorem angle_mk (x1 y1 x2 y2 x3 y3 n1 n2 c x : ℝ) (h1 : (x1 - x2) ^ 2 + (y1 - y2) ^ 2 = n1 ^ 2)
    (h2 : (x3 - x2) ^ 2 + (y3 - y2) ^ 2 = n2 ^ 2) (hn1 : 0 < n1) (hn2 : 0 < n2)
    (hc : (x1 - x2) * (x3 - x2) + (y1 - y2) * (y3 - y2) = c) (hx : c / (n1 * n2) = Real.cos x)
    (h0 : 0 ≤ x) (hπ : x ≤ Real.pi) :
    EuclideanGeometry.angle (mkPt x1 y1) (mkPt x2 y2) (mkPt x3 y3) = x := by
  unfold EuclideanGeometry.angle InnerProductGeometry.angle
  simp only [vsub_eq_sub]
  have hn1' : ‖mkPt x1 y1 - mkPt x2 y2‖ = n1 := by
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, mkPt]
    rw [h1, Real.sqrt_sq hn1.le]
  have hn2' : ‖mkPt x3 y3 - mkPt x2 y2‖ = n2 := by
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, mkPt]
    rw [h2, Real.sqrt_sq hn2.le]
  have hin : inner ℝ (mkPt x1 y1 - mkPt x2 y2) (mkPt x3 y3 - mkPt x2 y2) = c := by
    simp [PiLp.inner_apply, Fin.sum_univ_two, mkPt]
    rw [← hc]; ring
  rw [hin, hn1', hn2', hx, Real.arccos_cos h0 hπ]

/-- `sqrt 3`. -/
noncomputable def rr : ℝ := Real.sqrt 3
theorem rr_pos : 0 < rr := by unfold rr; positivity
theorem rr_sq : rr ^ 2 = 3 := Real.sq_sqrt (by norm_num)

/-- The regular hexagon of side 1. -/
noncomputable def hexPoly : ConvPoly 6 where
  v := ![mkPt 1 0, mkPt (1/2) (rr/2), mkPt (-1/2) (rr/2), mkPt (-1) 0, mkPt (-1/2) (-rr/2), mkPt (1/2) (-rr/2)]
  three_le := by norm_num
  left := by
    intro i j hji hji1
    have := rr_pos; have := rr_sq
    fin_cases i <;> fin_cases j <;> first | (exfalso; revert hji hji1; decide) | (simp [cross2, mkPt]; nlinarith)

theorem cos_two_pi_third : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num

theorem hex_angle (i : Fin 6) : hexPoly.angle i = 2 * Real.pi / 3 := by
  have := rr_sq
  fin_cases i <;>
  · unfold ConvPoly.angle cornerAngle
    simp [hexPoly]
    refine angle_mk _ _ _ _ _ _ 1 1 (-1/2) (2 * Real.pi / 3) ?_ ?_ one_pos one_pos ?_ ?_ ?_ ?_
    all_goals first | nlinarith | (rw [cos_two_pi_third]; norm_num) | positivity | (have := Real.pi_pos; linarith)

theorem dist_mk (a b c d n : ℝ) (h : (a - c) ^ 2 + (b - d) ^ 2 = n ^ 2) (hn : 0 ≤ n) :
    dist (mkPt a b) (mkPt c d) = n := by
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt, Real.dist_eq, sq_abs]
  rw [h, Real.sqrt_sq hn]

theorem hex_side (j : Fin 6) : hexPoly.side j = 1 := by
  have := rr_sq
  fin_cases j <;>
  · unfold ConvPoly.side
    simp [hexPoly]
    apply dist_mk _ _ _ _ 1 _ zero_le_one
    nlinarith

/-- **Witness for `lemma72_six`**: on the regular hexagon all hypotheses hold; `Phi = 0` (the alternating sum of equal sides), and the relations hold. -/
theorem lemma72_six_witness (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) :
    hexPoly.Phi α hα = 0 := by
  obtain ⟨-, -, h⟩ := lemma72_six α hα hexPoly hex_angle
  rw [h]; simp [hex_side]

/-- The equilateral triangle of side 1. -/
noncomputable def triPoly : ConvPoly 3 where
  v := ![mkPt 0 0, mkPt 1 0, mkPt (1/2) (rr/2)]
  three_le := le_refl _
  left := by
    intro i j hji hji1
    have := rr_pos; have := rr_sq
    fin_cases i <;> fin_cases j <;> first | (exfalso; revert hji hji1; decide) | (simp [cross2, mkPt]; nlinarith)

theorem cos_pi_third' : (1 : ℝ) / 2 = Real.cos (Real.pi / 3) := by rw [Real.cos_pi_div_three]

theorem tri_angle (i : Fin 3) : triPoly.angle i = Real.pi / 3 := by
  have := rr_sq
  fin_cases i <;>
  · unfold ConvPoly.angle cornerAngle
    simp [triPoly]
    refine angle_mk _ _ _ _ _ _ 1 1 (1/2) (Real.pi / 3) ?_ ?_ one_pos one_pos ?_ ?_ ?_ ?_
    all_goals first | nlinarith | (rw [Real.cos_pi_div_three]; norm_num) | positivity | (have := Real.pi_pos; linarith)

theorem tri_side (j : Fin 3) : triPoly.side j = 1 := by
  have := rr_sq
  fin_cases j <;>
  · unfold ConvPoly.side
    simp [triPoly]
    apply dist_mk _ _ _ _ 1 _ zero_le_one
    nlinarith

theorem lemma72_three_witness (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) :
    triPoly.Phi α hα = 3 := by
  obtain ⟨-, -, h⟩ := lemma72_three α hα triPoly tri_angle
  rw [h, tri_side]; norm_num

/-- The trapezoid with angles `pi/3, pi/3, 2pi/3, 2pi/3` and sides `2, 1, 1, 1`. -/
noncomputable def trapPoly : ConvPoly 4 where
  v := ![mkPt 0 0, mkPt 2 0, mkPt (3/2) (rr/2), mkPt (1/2) (rr/2)]
  three_le := by norm_num
  left := by
    intro i j hji hji1
    have := rr_pos; have := rr_sq
    fin_cases i <;> fin_cases j <;> first | (exfalso; revert hji hji1; decide) | (simp [cross2, mkPt]; nlinarith)

theorem trap_angle1 : trapPoly.angle 1 = Real.pi / 3 := by
  have := rr_sq
  unfold ConvPoly.angle cornerAngle
  simp [trapPoly]
  refine angle_mk _ _ _ _ _ _ 2 1 1 (Real.pi / 3) ?_ ?_ two_pos one_pos ?_ ?_ ?_ ?_
  all_goals first | nlinarith | (rw [Real.cos_pi_div_three]; norm_num) | positivity | (have := Real.pi_pos; linarith)

theorem trap_angle2 : trapPoly.angle 2 = 2 * Real.pi / 3 := by
  have := rr_sq
  unfold ConvPoly.angle cornerAngle
  simp [trapPoly]
  refine angle_mk _ _ _ _ _ _ 1 1 (-1/2) (2 * Real.pi / 3) ?_ ?_ one_pos one_pos ?_ ?_ ?_ ?_
  all_goals first | nlinarith | (rw [cos_two_pi_third]; norm_num) | positivity | (have := Real.pi_pos; linarith)

theorem trap_angle3 : trapPoly.angle 3 = 2 * Real.pi / 3 := by
  have := rr_sq
  unfold ConvPoly.angle cornerAngle
  simp [trapPoly]
  refine angle_mk _ _ _ _ _ _ 1 1 (-1/2) (2 * Real.pi / 3) ?_ ?_ one_pos one_pos ?_ ?_ ?_ ?_
  all_goals first | nlinarith | (rw [cos_two_pi_third]; norm_num) | positivity | (have := Real.pi_pos; linarith)

theorem trap_side0 : trapPoly.side 0 = 2 := by
  have := rr_sq
  unfold ConvPoly.side; simp [trapPoly]; apply dist_mk _ _ _ _ 2 _ (by norm_num); nlinarith
theorem trap_side1 : trapPoly.side 1 = 1 := by
  have := rr_sq
  unfold ConvPoly.side; simp [trapPoly]; apply dist_mk _ _ _ _ 1 _ (by norm_num); nlinarith
theorem trap_side2 : trapPoly.side 2 = 1 := by
  have := rr_sq
  unfold ConvPoly.side; simp [trapPoly]; apply dist_mk _ _ _ _ 1 _ (by norm_num); nlinarith
theorem trap_side3 : trapPoly.side 3 = 1 := by
  have := rr_sq
  unfold ConvPoly.side; simp [trapPoly]; apply dist_mk _ _ _ _ 1 _ (by norm_num); nlinarith

theorem lemma72_four_witness (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) :
    trapPoly.Phi α hα = 3 := by
  obtain ⟨-, -, h⟩ := lemma72_four α hα trapPoly trap_angle1 trap_angle2 trap_angle3
  rw [h, trap_side3]; norm_num

/-- The pentagon with angle `pi/3` at `v_1` and `2pi/3` elsewhere, sides `2, 2, 1, 1, 1`. -/
noncomputable def pentPoly : ConvPoly 5 where
  v := ![mkPt 0 0, mkPt 2 0, mkPt 1 rr, mkPt 0 rr, mkPt (-1/2) (rr/2)]
  three_le := by norm_num
  left := by
    intro i j hji hji1
    have := rr_pos; have := rr_sq
    fin_cases i <;> fin_cases j <;> first | (exfalso; revert hji hji1; decide) | (simp [cross2, mkPt]; nlinarith)

theorem pent_angle1 : pentPoly.angle 1 = Real.pi / 3 := by
  have := rr_sq
  unfold ConvPoly.angle cornerAngle
  simp [pentPoly]
  refine angle_mk _ _ _ _ _ _ 2 2 2 (Real.pi / 3) ?_ ?_ two_pos two_pos ?_ ?_ ?_ ?_
  all_goals first | nlinarith | (rw [Real.cos_pi_div_three]; norm_num) | positivity | (have := Real.pi_pos; linarith)

theorem pent_angle2 : pentPoly.angle 2 = 2 * Real.pi / 3 := by
  have := rr_sq
  unfold ConvPoly.angle cornerAngle
  simp [pentPoly]
  refine angle_mk _ _ _ _ _ _ 2 1 (-1) (2 * Real.pi / 3) ?_ ?_ two_pos one_pos ?_ ?_ ?_ ?_
  all_goals first | nlinarith | (rw [cos_two_pi_third]; norm_num) | positivity | (have := Real.pi_pos; linarith)

theorem pent_angle3 : pentPoly.angle 3 = 2 * Real.pi / 3 := by
  have := rr_sq
  unfold ConvPoly.angle cornerAngle
  simp [pentPoly]
  refine angle_mk _ _ _ _ _ _ 1 1 (-1/2) (2 * Real.pi / 3) ?_ ?_ one_pos one_pos ?_ ?_ ?_ ?_
  all_goals first | nlinarith | (rw [cos_two_pi_third]; norm_num) | positivity | (have := Real.pi_pos; linarith)

theorem pent_angle4 : pentPoly.angle 4 = 2 * Real.pi / 3 := by
  have := rr_sq
  unfold ConvPoly.angle cornerAngle
  simp [pentPoly]
  refine angle_mk _ _ _ _ _ _ 1 1 (-1/2) (2 * Real.pi / 3) ?_ ?_ one_pos one_pos ?_ ?_ ?_ ?_
  all_goals first | nlinarith | (rw [cos_two_pi_third]; norm_num) | positivity | (have := Real.pi_pos; linarith)

theorem pent_side3 : pentPoly.side 3 = 1 := by
  have := rr_sq
  unfold ConvPoly.side; simp [pentPoly]; apply dist_mk _ _ _ _ 1 _ (by norm_num); nlinarith

theorem lemma72_five_witness (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) :
    pentPoly.Phi α hα = 3 := by
  obtain ⟨-, -, h⟩ := lemma72_five α hα pentPoly pent_angle1 pent_angle2 pent_angle3 pent_angle4
  rw [h, pent_side3]; norm_num

/-- Witness for `Phi_additive`: the unit square cut along its diagonal into two triangles (`sqTiling`). -/
theorem Phi_additive_square (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) :
    ∑ i, (sqTiling.C.toRegionDissection.tile i).flux (fAlphaAt α hα (sqTiling.P.sideDir 0).angle).weight
      = sqTiling.P.Phi α hα :=
  sqTiling.P.Phi_additive sqTiling.C.toRegionDissection sqTiling.region_eq α hα

#print axioms Phi_additive_square
#print axioms lemma72_three_witness
#print axioms lemma72_four_witness
#print axioms lemma72_five_witness
#print axioms lemma72_six_witness

end Erdos634.Draft.LaczFormal.Thm21
