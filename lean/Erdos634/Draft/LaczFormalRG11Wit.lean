-- Draft/LaczFormalRG11Wit.lean -- NON-VACUITY of `caseII_a` (Case II, Subcase IIa): the two-triangle parallelogram of the triangle with sides (a, b, c) = (sqrt 2, 1, 3/2),
-- `cos gamma = 3 sqrt2 / 16 > 0` (`gamma < pi/2`, `gamma != pi/3`), `a` not a nonnegative rational combination of `b, c` (`r sqrt 2 = p + 3q/2` is impossible for `r > 0`):
-- all hypotheses hold and conclusion (i) is obtained.  Caveat: a 2-tile tiling (the side rule, the counting and the blocked-side argument are not exercised nontrivially).  NOTE, UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 6.1).
import Erdos634.Draft.LaczFormalRG11Final
import Erdos634.Draft.LaczFormalRG9IaWit

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

noncomputable def yQ : ℝ := Real.sqrt 119 / 8

theorem yQ_pos : 0 < yQ := by unfold yQ; positivity

theorem sqrt119_sq' : Real.sqrt 119 ^ 2 = 119 := Real.sq_sqrt (by norm_num)

noncomputable def yTiling2 : PolyTiling 2 4 := pTiling 1 (3 / 8) yQ (by norm_num) yQ_pos

theorem yDiss2_slen0 : slen yTiling2.C 0 = Real.sqrt 2 := by
  show dist (mkPt (3 / 8) yQ) (mkPt 0 0) = Real.sqrt 2
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt, yQ]
  rw [abs_of_nonneg (Real.sqrt_nonneg 119)]
  congr 1
  nlinarith [sqrt119_sq']

theorem yDiss2_slen1 : slen yTiling2.C 1 = 1 := by
  show dist (mkPt 0 0) (mkPt 1 0) = 1
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt]

theorem yDiss2_slen2 : slen yTiling2.C 2 = 3 / 2 := by
  show dist (mkPt 1 0) (mkPt (3 / 8) yQ) = 3 / 2
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt, yQ]
  rw [Real.dist_eq, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 - 3 / 8), abs_of_nonneg (Real.sqrt_nonneg 119)]
  rw [show ((1 : ℝ) - 3 / 8) ^ 2 + (Real.sqrt 119 / 8) ^ 2 = (3 / 2) ^ 2 by nlinarith [sqrt119_sq']]
  exact Real.sqrt_sq (by norm_num)

theorem yTiling2_notComb : NotComb (slen yTiling2.C 0) (slen yTiling2.C 1) (slen yTiling2.C 2) := by
  rw [yDiss2_slen0, yDiss2_slen1, yDiss2_slen2]
  intro r p q hr e
  have h2 : Irrational (Real.sqrt 2) := irrational_sqrt_two
  apply h2
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  refine ⟨((p : ℚ) + 3 / 2 * q) / r, ?_⟩
  push_cast
  field_simp
  linarith

theorem yTiling2_cos : Real.cos (angleAt yTiling2.C.model 2) = 3 * Real.sqrt 2 / 16 ∧ 0 ≤ angleAt yTiling2.C.model 2 ∧ angleAt yTiling2.C.model 2 ≤ Real.pi := by
  show Real.cos (EuclideanGeometry.angle (mkPt 1 0) (mkPt 0 0) (mkPt (3 / 8) yQ)) = 3 * Real.sqrt 2 / 16 ∧ _
  unfold EuclideanGeometry.angle
  simp only [vsub_eq_sub]
  have hn : ‖mkPt (3 / 8) yQ - mkPt 0 0‖ = Real.sqrt 2 := by
    rw [← dist_eq_norm]; have := yDiss2_slen0; unfold slen at this; exact this
  have hn1 : ‖mkPt 1 0 - mkPt 0 0‖ = 1 := by
    rw [← dist_eq_norm]; have := yDiss2_slen1; unfold slen at this; rw [dist_comm]; exact this
  have hin : inner ℝ (mkPt 1 0 - mkPt 0 0) (mkPt (3 / 8) yQ - mkPt 0 0) = 3 / 8 := by
    simp [PiLp.inner_apply, Fin.sum_univ_two, mkPt]
  unfold InnerProductGeometry.angle
  rw [hin, hn, hn1]
  refine ⟨?_, Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  have hs2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hq : 3 / 8 / (1 * Real.sqrt 2) = 3 * Real.sqrt 2 / 16 := by
    field_simp
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [hq]
  have hb : 3 * Real.sqrt 2 / 16 ≤ 1 := by
    have : Real.sqrt 2 ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    linarith
  exact Real.cos_arccos (by linarith [hs2]) (by linarith)

/-- **NON-VACUITY of Case II, Subcase IIa**: all hypotheses hold on this two-triangle parallelogram and conclusion (i) is obtained. -/
theorem caseII_a_witness : Concl1 yTiling2.C yTiling2.P := by
  obtain ⟨hc, h0, hπ⟩ := yTiling2_cos
  have hs2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  apply caseII_a yTiling2 (pDiss_regular (by norm_num) yQ_pos)
  · have hlt : angleAt yTiling2.C.model 2 < Real.pi / 2 := by
      by_contra hle
      push Not at hle
      have := Real.cos_nonpos_of_pi_div_two_le_of_le hle (by linarith [Real.pi_pos])
      linarith
    exact hlt
  · intro h
    rw [h, Real.cos_pi_div_three] at hc
    have h22 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have : Real.sqrt 2 = 8 / 3 := by linarith
    nlinarith [h22]
  · exact yTiling2_notComb

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.caseII_a_witness
