-- Draft/LaczFormalRG6IVcWit.lean -- NON-VACUITY of `caseIVc_small` (Subcase IVc, N <= 4): the two-triangle parallelogram (0,0), (1,0), (2,sqrt3), (1,sqrt3) tiled by two copies of the 30-60-90 triangle with
-- sides (a, b, c) = (2, 1, sqrt 3), alpha = pi/2, beta = pi/6, gamma = pi/3: a, b commensurable, c not a rational multiple of a, gamma = pi/3, regular.  All hypotheses of `caseIVc_small` hold and its
-- conclusion (i) is obtained.  UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3).
import Erdos634.Draft.LaczFormalRG6IVcSmall
import Erdos634.Draft.LaczFormalRG4Wit
import Erdos634.CertCoord

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

noncomputable def vT : ℝ := Real.sqrt 3

theorem vT_pos : 0 < vT := by unfold vT; positivity

noncomputable def vTiling : PolyTiling 2 4 := pTiling 1 1 vT one_pos vT_pos

theorem vDiss_slen0 : slen vTiling.C 0 = 2 := by
  show dist (mkPt 1 vT) (mkPt 0 0) = 2
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt, vT]
  rw [show (1 + 3 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)

theorem vDiss_slen1 : slen vTiling.C 1 = 1 := by
  show dist (mkPt 0 0) (mkPt 1 0) = 1
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt]

theorem vDiss_slen2 : slen vTiling.C 2 = Real.sqrt 3 := by
  show dist (mkPt 1 0) (mkPt 1 vT) = Real.sqrt 3
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt, vT]

theorem vTiling_comm : Comm (slen vTiling.C 0) (slen vTiling.C 1) := by
  rw [vDiss_slen0, vDiss_slen1]
  exact ⟨1, 2, one_pos, two_pos, by norm_num⟩

theorem vTiling_notComm : ¬ Comm (slen vTiling.C 0) (slen vTiling.C 2) := by
  rw [vDiss_slen0, vDiss_slen2]
  rintro ⟨p, q, hp, hq, e⟩
  have h3 : Irrational (Real.sqrt 3) := by exact_mod_cast Nat.Prime.irrational_sqrt (by norm_num : Nat.Prime 3)
  apply h3
  refine ⟨(2 * p : ℚ) / q, ?_⟩
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  push_cast
  field_simp
  linarith

theorem vTiling_gamma : angleAt vTiling.C.model 2 = Real.pi / 3 := by
  show EuclideanGeometry.angle (mkPt 1 0) (mkPt 0 0) (mkPt 1 vT) = Real.pi / 3
  unfold EuclideanGeometry.angle
  simp only [vsub_eq_sub]
  have hn : ‖mkPt 1 vT - mkPt 0 0‖ = 2 := by
    rw [← dist_eq_norm]
    have := vDiss_slen0
    unfold slen at this
    exact this
  have hn1 : ‖mkPt 1 0 - mkPt 0 0‖ = 1 := by
    rw [← dist_eq_norm]
    have := vDiss_slen1
    unfold slen at this
    rw [dist_comm]; exact this
  have hin : inner ℝ (mkPt 1 0 - mkPt 0 0) (mkPt 1 vT - mkPt 0 0) = 1 := by
    simp [PiLp.inner_apply, Fin.sum_univ_two, mkPt]
  unfold InnerProductGeometry.angle
  rw [hin, hn, hn1]
  have : (1 : ℝ) / (1 * 2) = Real.cos (Real.pi / 3) := by
    rw [Real.cos_pi_div_three]; norm_num
  rw [this, Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]

/-- **NON-VACUITY of `caseIVc_small`**: on the two-triangle parallelogram of the 30-60-90 tile `(2, 1, sqrt 3)`, all hypotheses hold and conclusion (i) of Theorem 2.1 is obtained. -/
theorem caseIVc_small_witness : Concl1 vTiling.C vTiling.P :=
  caseIVc_small vTiling (pDiss_regular one_pos vT_pos) vTiling_gamma vTiling_comm vTiling_notComm le_rfl

end Erdos634.Draft.LaczFormal.RG
