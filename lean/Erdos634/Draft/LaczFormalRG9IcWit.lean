-- Draft/LaczFormalRG9IcWit.lean -- NON-VACUITY of `caseI_c` (Case I, Subcase Ic): the two-triangle parallelogram (0,0), (1,0), (1 - sqrt2/2, sqrt2/2), (-sqrt2/2, sqrt2/2) tiled by two copies of the isosceles triangle
-- with sides (a, b, c) = (1, 1, sqrt(2 + sqrt 2)), gamma = 3 pi/4 (> pi/2, != 2 pi/3): a, b commensurable, c not a rational multiple of a, regular.  All hypotheses of `caseI_c` hold, conclusion (i) obtained.
-- Caveat: a 2-tile tiling (all tile vertices are polygon vertices), so the counting of exceptional vertices and the side rule are not exercised nontrivially.  UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 5.3).
import Erdos634.Draft.LaczFormalRG9Ic
import Erdos634.Draft.LaczFormalRG6IVcWit

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

noncomputable def oT : ℝ := Real.sqrt 2 / 2
noncomputable def oS : ℝ := -(Real.sqrt 2 / 2)

theorem oT_pos : 0 < oT := by unfold oT; positivity

theorem sqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

noncomputable def oTiling : PolyTiling 2 4 := pTiling 1 oS oT one_pos oT_pos

theorem oDiss_slen0 : slen oTiling.C 0 = 1 := by
  show dist (mkPt oS oT) (mkPt 0 0) = 1
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt, oS, oT]
  rw [abs_of_nonneg (Real.sqrt_nonneg 2)]
  nlinarith [sqrt2_sq]

theorem oDiss_slen1 : slen oTiling.C 1 = 1 := by
  show dist (mkPt 0 0) (mkPt 1 0) = 1
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt]

theorem oDiss_slen2 : slen oTiling.C 2 = Real.sqrt (2 + Real.sqrt 2) := by
  show dist (mkPt 1 0) (mkPt oS oT) = Real.sqrt (2 + Real.sqrt 2)
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt, oS, oT]
  rw [Real.dist_eq, abs_of_nonneg (by have := Real.sqrt_nonneg 2; linarith : (0 : ℝ) ≤ 1 - -(Real.sqrt 2 / 2)), abs_of_nonneg (Real.sqrt_nonneg 2)]
  congr 1
  nlinarith [sqrt2_sq]

theorem oTiling_comm : Comm (slen oTiling.C 0) (slen oTiling.C 1) := by
  rw [oDiss_slen0, oDiss_slen1]
  exact ⟨1, 1, one_pos, one_pos, by norm_num⟩

theorem oTiling_notComm : ¬ Comm (slen oTiling.C 0) (slen oTiling.C 2) := by
  rw [oDiss_slen0, oDiss_slen2]
  rintro ⟨p, q, hp, hq, e⟩
  have h2 : Irrational (Real.sqrt 2) := irrational_sqrt_two
  apply h2
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hc : Real.sqrt (2 + Real.sqrt 2) = (p : ℝ) / q := by
    field_simp; linarith
  have hsq : (Real.sqrt (2 + Real.sqrt 2)) ^ 2 = 2 + Real.sqrt 2 := Real.sq_sqrt (by positivity)
  refine ⟨((p : ℚ) / q) ^ 2 - 2, ?_⟩
  push_cast
  rw [← hc]
  linarith

theorem oTiling_gamma : angleAt oTiling.C.model 2 = 3 * Real.pi / 4 := by
  show EuclideanGeometry.angle (mkPt 1 0) (mkPt 0 0) (mkPt oS oT) = 3 * Real.pi / 4
  unfold EuclideanGeometry.angle
  simp only [vsub_eq_sub]
  have hn : ‖mkPt oS oT - mkPt 0 0‖ = 1 := by
    rw [← dist_eq_norm]
    have := oDiss_slen0
    unfold slen at this
    exact this
  have hn1 : ‖mkPt 1 0 - mkPt 0 0‖ = 1 := by
    rw [← dist_eq_norm]
    have := oDiss_slen1
    unfold slen at this
    rw [dist_comm]; exact this
  have hin : inner ℝ (mkPt 1 0 - mkPt 0 0) (mkPt oS oT - mkPt 0 0) = oS := by
    simp [PiLp.inner_apply, Fin.sum_univ_two, mkPt]
  unfold InnerProductGeometry.angle
  rw [hin, hn, hn1]
  have : oS / (1 * 1) = Real.cos (3 * Real.pi / 4) := by
    rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring, Real.cos_pi_sub, Real.cos_pi_div_four]
    unfold oS; ring
  rw [this, Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]

/-- **NON-VACUITY of Case I, Subcase Ic**: all hypotheses hold on this two-triangle parallelogram and conclusion (i) is obtained. -/
theorem caseI_c_witness : Concl1 oTiling.C oTiling.P := by
  apply caseI_c oTiling (pDiss_regular one_pos oT_pos)
  · rw [oTiling_gamma]; linarith [Real.pi_pos]
  · rw [oTiling_gamma]; intro h; linarith [Real.pi_pos]
  · exact oTiling_comm
  · exact oTiling_notComm

end Erdos634.Draft.LaczFormal.RG
