-- Draft/LaczFormalRG9IdWit.lean -- NON-VACUITY of `caseI_d` (Case I, commensurable branch): the two-triangle parallelogram of the triangle with sides (a, b, c) = (2, 3, 4), `cos gamma = -1/4`
-- (`gamma > pi/2`, `gamma != 2 pi/3`, `a, b, c` integers): all hypotheses hold and conclusion (ii) is obtained.  Caveat: 2-tile tiling.  UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 5.2).
import Erdos634.Draft.LaczFormalRG9Id
import Erdos634.Draft.LaczFormalRG6IVcWit

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

noncomputable def qT : ℝ := Real.sqrt 15 / 2

theorem qT_pos : 0 < qT := by unfold qT; positivity

theorem sqrt15_sq : Real.sqrt 15 ^ 2 = 15 := Real.sq_sqrt (by norm_num)

noncomputable def qTiling : PolyTiling 2 4 := pTiling 3 (-(1 / 2)) qT (by norm_num) qT_pos

theorem qDiss_slen0 : slen qTiling.C 0 = 2 := by
  show dist (mkPt (-(1 / 2)) qT) (mkPt 0 0) = 2
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt, qT]
  rw [abs_of_nonneg (Real.sqrt_nonneg 15)]
  rw [show ((2 : ℝ) ^ 2)⁻¹ + (Real.sqrt 15 / 2) ^ 2 = 2 ^ 2 by nlinarith [sqrt15_sq]]
  exact Real.sqrt_sq (by norm_num)

theorem qDiss_slen1 : slen qTiling.C 1 = 3 := by
  show dist (mkPt 0 0) (mkPt 3 0) = 3
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt]

theorem qDiss_slen2 : slen qTiling.C 2 = 4 := by
  show dist (mkPt 3 0) (mkPt (-(1 / 2)) qT) = 4
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt, qT]
  rw [Real.dist_eq, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 - -2⁻¹), abs_of_nonneg (Real.sqrt_nonneg 15)]
  rw [show ((3 : ℝ) - -2⁻¹) ^ 2 + (Real.sqrt 15 / 2) ^ 2 = 4 ^ 2 by nlinarith [sqrt15_sq]]
  exact Real.sqrt_sq (by norm_num)

theorem qTiling_comm : Comm (slen qTiling.C 0) (slen qTiling.C 1) := by
  rw [qDiss_slen0, qDiss_slen1]; exact ⟨3, 2, by norm_num, by norm_num, by norm_num⟩

theorem qTiling_comm2 : Comm (slen qTiling.C 0) (slen qTiling.C 2) := by
  rw [qDiss_slen0, qDiss_slen2]; exact ⟨2, 1, by norm_num, by norm_num, by norm_num⟩

theorem qTiling_cos : Real.cos (angleAt qTiling.C.model 2) = -(1 / 4) ∧ 0 ≤ angleAt qTiling.C.model 2 ∧ angleAt qTiling.C.model 2 ≤ Real.pi := by
  show Real.cos (EuclideanGeometry.angle (mkPt 3 0) (mkPt 0 0) (mkPt (-(1 / 2)) qT)) = -(1 / 4) ∧ _
  unfold EuclideanGeometry.angle
  simp only [vsub_eq_sub]
  have hn : ‖mkPt (-(1 / 2)) qT - mkPt 0 0‖ = 2 := by
    rw [← dist_eq_norm]; have := qDiss_slen0; unfold slen at this; exact this
  have hn1 : ‖mkPt 3 0 - mkPt 0 0‖ = 3 := by
    rw [← dist_eq_norm]; have := qDiss_slen1; unfold slen at this; rw [dist_comm]; exact this
  have hin : inner ℝ (mkPt 3 0 - mkPt 0 0) (mkPt (-(1 / 2)) qT - mkPt 0 0) = -(3 / 2) := by
    simp [PiLp.inner_apply, Fin.sum_univ_two, mkPt]; norm_num
  unfold InnerProductGeometry.angle
  rw [hin, hn, hn1]
  refine ⟨?_, Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  rw [Real.cos_arccos (by norm_num) (by norm_num)]
  norm_num

/-- **NON-VACUITY of Case I, commensurable branch**: all hypotheses hold on this two-triangle parallelogram and conclusion (ii) is obtained. -/
theorem caseI_d_witness : Concl2 qTiling.C qTiling.P := by
  obtain ⟨hc, h0, hπ⟩ := qTiling_cos
  apply caseI_d qTiling (pDiss_regular (by norm_num) qT_pos)
  · by_contra hle
    push Not at hle
    have := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, h0], hle⟩
    linarith
  · intro h
    have : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
      rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
    rw [h] at hc
    linarith
  · exact qTiling_comm
  · exact qTiling_comm2

end Erdos634.Draft.LaczFormal.RG
