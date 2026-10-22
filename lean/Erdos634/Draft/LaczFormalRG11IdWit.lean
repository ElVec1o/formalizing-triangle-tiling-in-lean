-- Draft/LaczFormalRG11IdWit.lean -- NON-VACUITY of `caseII_b` (Case II, commensurable branch): two-triangle parallelogram of the triangle with sides (a, b, c) = (2, 3, 3), `cos gamma = 1/3`
-- (`gamma < pi/2`, `gamma != pi/3`, integer sides): all hypotheses hold, conclusion (iii) obtained.  Caveat: 2-tile tiling.  NOTE, UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 6.2).
import Erdos634.Draft.LaczFormalRG11Id
import Erdos634.Draft.LaczFormalRG9IdWit

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

noncomputable def wT2b : ℝ := 4 * Real.sqrt 2 / 3

theorem wT2b_pos : 0 < wT2b := by unfold wT2b; positivity

theorem sqrt2_sq' : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

noncomputable def wTiling2b : PolyTiling 2 4 := pTiling 3 (2 / 3) wT2b (by norm_num) wT2b_pos

theorem wDiss2b_slen0 : slen wTiling2b.C 0 = 2 := by
  show dist (mkPt (2 / 3) wT2b) (mkPt 0 0) = 2
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt, wT2b]
  rw [abs_of_nonneg (Real.sqrt_nonneg 2)]
  rw [show (2 / 3 : ℝ) ^ 2 + (4 * Real.sqrt 2 / 3) ^ 2 = 2 ^ 2 by nlinarith [sqrt2_sq']]
  exact Real.sqrt_sq (by norm_num)

theorem wDiss2b_slen1 : slen wTiling2b.C 1 = 3 := by
  show dist (mkPt 0 0) (mkPt 3 0) = 3
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt]

theorem wDiss2b_slen2 : slen wTiling2b.C 2 = 3 := by
  show dist (mkPt 3 0) (mkPt (2 / 3) wT2b) = 3
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt, wT2b]
  rw [abs_of_nonneg (Real.sqrt_nonneg 2), Real.dist_eq, abs_of_nonneg (by norm_num : (0 : ℝ) <= 3 - 2 / 3)]
  rw [show (3 - 2 / 3 : ℝ) ^ 2 + (4 * Real.sqrt 2 / 3) ^ 2 = 3 ^ 2 by nlinarith [sqrt2_sq']]
  exact Real.sqrt_sq (by norm_num)

theorem wTiling2b_comm : Comm (slen wTiling2b.C 0) (slen wTiling2b.C 1) := by
  rw [wDiss2b_slen0, wDiss2b_slen1]; exact ⟨3, 2, by norm_num, by norm_num, by norm_num⟩

theorem wTiling2b_comm2 : Comm (slen wTiling2b.C 0) (slen wTiling2b.C 2) := by
  rw [wDiss2b_slen0, wDiss2b_slen2]; exact ⟨3, 2, by norm_num, by norm_num, by norm_num⟩

/-- `cos γ = (a² + b² - c²)/(2ab) = 1/3` via the law of cosines `model_cos_gamma`. -/
theorem wTiling2b_cos : Real.cos (angleAt wTiling2b.C.model 2) = 1 / 3 := by
  have h := model_cos_gamma wTiling2b.C
  rw [wDiss2b_slen0, wDiss2b_slen1, wDiss2b_slen2] at h
  have e : wTiling2b.C.model.angleAt 2 = angleAt wTiling2b.C.model 2 := rfl
  rw [e] at h
  linarith

/-- **NON-VACUITY of Case II, commensurable branch**: all hypotheses hold on this two-triangle parallelogram and conclusion (iii) is obtained. -/
theorem caseII_b_witness : Concl3 wTiling2b.C wTiling2b.P := by
  have hc := wTiling2b_cos
  have hpi := Real.pi_pos
  have h0 := (model_angle_pos' wTiling2b.C 2)
  have hγ := model_gamma_lt_pi wTiling2b.C
  apply caseII_b wTiling2b (pDiss_regular (by norm_num) wT2b_pos)
  · by_contra hle
    push Not at hle
    have h2 : angleAt wTiling2b.C.model 2 ≤ Real.pi := hγ.le
    have : Real.cos (angleAt wTiling2b.C.model 2) ≤ 0 := by
      apply Real.cos_nonpos_of_pi_div_two_le_of_le hle (by linarith)
    linarith
  · intro h
    rw [h, Real.cos_pi_div_three] at hc
    linarith
  · exact wTiling2b_comm
  · exact wTiling2b_comm2

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.caseII_b_witness
