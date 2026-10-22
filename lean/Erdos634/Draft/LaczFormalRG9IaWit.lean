-- Draft/LaczFormalRG9IaWit.lean -- NON-VACUITY of `caseI_a` (Case I, Subcase Ia): the two-triangle parallelogram of the triangle with sides (a, b, c) = (sqrt 2, 1, 2), `cos gamma = -sqrt2/4` (`gamma > pi/2`,
-- `gamma != 2pi/3`), `a` not a nonnegative rational combination of `b, c` (`r sqrt 2 = p + 2q` is impossible for `r > 0`): all hypotheses hold and conclusion (i) is obtained.
-- Caveat: a 2-tile tiling.  UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 5.1).
import Erdos634.Draft.LaczFormalRG9Ib
import Erdos634.Draft.LaczFormalRG6IVcWit

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

noncomputable def zT : ℝ := Real.sqrt 7 / 2

theorem zT_pos : 0 < zT := by unfold zT; positivity

theorem sqrt7_sq : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)

noncomputable def zTiling : PolyTiling 2 4 := pTiling 1 (-(1 / 2)) zT (by norm_num) zT_pos

theorem zDiss_slen0 : slen zTiling.C 0 = Real.sqrt 2 := by
  show dist (mkPt (-(1 / 2)) zT) (mkPt 0 0) = Real.sqrt 2
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt, zT]
  rw [abs_of_nonneg (Real.sqrt_nonneg 7)]
  congr 1
  nlinarith [sqrt7_sq]

theorem zDiss_slen1 : slen zTiling.C 1 = 1 := by
  show dist (mkPt 0 0) (mkPt 1 0) = 1
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt]

theorem zDiss_slen2 : slen zTiling.C 2 = 2 := by
  show dist (mkPt 1 0) (mkPt (-(1 / 2)) zT) = 2
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt, zT]
  rw [Real.dist_eq, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 - -2⁻¹), abs_of_nonneg (Real.sqrt_nonneg 7)]
  rw [show ((1 : ℝ) - -2⁻¹) ^ 2 + (Real.sqrt 7 / 2) ^ 2 = 2 ^ 2 by nlinarith [sqrt7_sq]]
  exact Real.sqrt_sq (by norm_num)

theorem zTiling_notComb : NotComb (slen zTiling.C 0) (slen zTiling.C 1) (slen zTiling.C 2) := by
  rw [zDiss_slen0, zDiss_slen1, zDiss_slen2]
  intro r p q hr e
  have h2 : Irrational (Real.sqrt 2) := irrational_sqrt_two
  apply h2
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  refine ⟨((p : ℚ) + 2 * q) / r, ?_⟩
  push_cast
  field_simp
  linarith

theorem zTiling_cos : Real.cos (angleAt zTiling.C.model 2) = -(Real.sqrt 2 / 4) ∧ 0 ≤ angleAt zTiling.C.model 2 ∧ angleAt zTiling.C.model 2 ≤ Real.pi := by
  show Real.cos (EuclideanGeometry.angle (mkPt 1 0) (mkPt 0 0) (mkPt (-(1 / 2)) zT)) = -(Real.sqrt 2 / 4) ∧ _
  unfold EuclideanGeometry.angle
  simp only [vsub_eq_sub]
  have hn : ‖mkPt (-(1 / 2)) zT - mkPt 0 0‖ = Real.sqrt 2 := by
    rw [← dist_eq_norm]; have := zDiss_slen0; unfold slen at this; exact this
  have hn1 : ‖mkPt 1 0 - mkPt 0 0‖ = 1 := by
    rw [← dist_eq_norm]; have := zDiss_slen1; unfold slen at this; rw [dist_comm]; exact this
  have hin : inner ℝ (mkPt 1 0 - mkPt 0 0) (mkPt (-(1 / 2)) zT - mkPt 0 0) = -(1 / 2) := by
    simp [PiLp.inner_apply, Fin.sum_univ_two, mkPt]
  unfold InnerProductGeometry.angle
  rw [hin, hn, hn1]
  refine ⟨?_, Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  have hs2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hq : -(1 / 2) / (1 * Real.sqrt 2) = -(Real.sqrt 2 / 4) := by
    field_simp
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [hq]
  have hb : Real.sqrt 2 / 4 ≤ 1 := by
    have : Real.sqrt 2 ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    linarith
  exact Real.cos_arccos (by linarith) (by linarith [hs2])

/-- **NON-VACUITY of Case I, Subcase Ia**: all hypotheses hold on this two-triangle parallelogram and conclusion (i) is obtained. -/
theorem caseI_a_witness : Concl1 zTiling.C zTiling.P := by
  obtain ⟨hc, h0, hπ⟩ := zTiling_cos
  apply caseI_a zTiling (pDiss_regular (by norm_num) zT_pos)
  · by_contra hle
    push Not at hle
    have := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, h0], hle⟩
    have hs2 : (0 : ℝ) < Real.sqrt 2 := by positivity
    linarith
  · intro h
    have : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
      rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
    rw [h] at hc
    have h22 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have : Real.sqrt 2 = 2 := by linarith
    nlinarith [h22]
  · exact zTiling_notComb

end Erdos634.Draft.LaczFormal.RG
