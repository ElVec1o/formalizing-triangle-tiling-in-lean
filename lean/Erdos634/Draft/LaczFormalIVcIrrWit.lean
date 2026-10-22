-- Draft/LaczFormalIVcIrrWit.lean -- NON-VACUITY (tile data) of `ivc_final_ge5` / `caseIVc_concl`: the tile (a, b, c) = (1, 3, sqrt 7), gamma = pi/3 at the vertex between a and b,
-- carried by the two-triangle parallelogram `pTiling 3 (1/2) (sqrt3/2)` (M = 4).  PROVED here: gamma = pi/3, a, b commensurable, c not commensurable with a, alpha/pi IRRATIONAL
-- (via `ivc_rat_alpha`: rational alpha would force alpha in {pi/6, pi/2}, i.e. sin alpha/sin beta in {1/2, 2}, but it is a/b = 1/3), and caseIVc_small gives Concl1.
-- NOTE, UNAUDITED.  This witnesses every hypothesis of `ivc_final_ge5` EXCEPT `5 <= M`.  The M = 6 tiling is NOT constructed in Lean: Laczkovich's own construction (Sect. 2, (vi)) gives it by hand
-- (centrally symmetric equiangular hexagon with sides 1,3,3,1,3,3 = three parallelograms (1,3),(3,1),(3,3); the (3,3) rhombus is 3 cells (1,3); 10 tiles), so the branch is NOT vacuous.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 2 (vi), 8.3), Beeson-Zhang.
import Erdos634.Draft.LaczFormalThm21Partial3
import Erdos634.Draft.LaczFormalRG6IVcWit

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

noncomputable def iT : ℝ := Real.sqrt 3 / 2
theorem iT_pos : 0 < iT := by unfold iT; positivity
theorem sqrt3_sq' : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

noncomputable def iTiling : PolyTiling 2 4 := pTiling 3 (1 / 2) iT (by norm_num) iT_pos

theorem iDiss_slen0 : slen iTiling.C 0 = 1 := by
  show dist (mkPt (1 / 2) iT) (mkPt 0 0) = 1
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt, iT]
  rw [abs_of_nonneg (Real.sqrt_nonneg 3), div_pow, sqrt3_sq']; norm_num

theorem iDiss_slen1 : slen iTiling.C 1 = 3 := by
  show dist (mkPt 0 0) (mkPt 3 0) = 3
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt]

theorem iDiss_slen2 : slen iTiling.C 2 = Real.sqrt 7 := by
  show dist (mkPt 3 0) (mkPt (1 / 2) iT) = Real.sqrt 7
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt, iT]
  congr 1
  rw [Real.dist_eq, sq_abs, abs_of_nonneg (Real.sqrt_nonneg 3), div_pow, sqrt3_sq']
  norm_num

theorem iTiling_comm : Comm (slen iTiling.C 0) (slen iTiling.C 1) := by
  rw [iDiss_slen0, iDiss_slen1]
  exact ⟨3, 1, by norm_num, one_pos, by norm_num⟩

theorem iTiling_notComm : ¬ Comm (slen iTiling.C 0) (slen iTiling.C 2) := by
  rw [iDiss_slen0, iDiss_slen2]
  rintro ⟨p, q, hp, hq, e⟩
  have h7 : Irrational (Real.sqrt 7) := by exact_mod_cast Nat.Prime.irrational_sqrt (by norm_num : Nat.Prime 7)
  apply h7
  refine ⟨(p : ℚ) / q, ?_⟩
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  push_cast
  field_simp
  linarith

theorem iTiling_gamma : angleAt iTiling.C.model 2 = Real.pi / 3 := by
  show EuclideanGeometry.angle (mkPt 3 0) (mkPt 0 0) (mkPt (1 / 2) iT) = Real.pi / 3
  unfold EuclideanGeometry.angle
  simp only [vsub_eq_sub]
  have hn : ‖mkPt (1 / 2) iT - mkPt 0 0‖ = 1 := by
    rw [← dist_eq_norm]
    have := iDiss_slen0
    unfold slen at this
    exact this
  have hn1 : ‖mkPt 3 0 - mkPt 0 0‖ = 3 := by
    rw [← dist_eq_norm]
    have := iDiss_slen1
    unfold slen at this
    rw [dist_comm]; exact this
  have hin : inner ℝ (mkPt 3 0 - mkPt 0 0) (mkPt (1 / 2) iT - mkPt 0 0) = 3 / 2 := by
    simp [PiLp.inner_apply, Fin.sum_univ_two, mkPt]
    norm_num
  unfold InnerProductGeometry.angle
  rw [hin, hn, hn1]
  have : (3 / 2 : ℝ) / (3 * 1) = Real.cos (Real.pi / 3) := by
    rw [Real.cos_pi_div_three]; norm_num
  rw [this, Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]

theorem iTiling_alpha_irr : ¬ ∃ r : ℚ, angleAt iTiling.C.model 0 = (r : ℝ) * Real.pi := by
  rintro ⟨r, hr⟩
  have hγ := iTiling_gamma
  have h := ivc_rat_alpha iTiling hγ iTiling_comm iTiling_notComm ⟨r, hr⟩
  have hratio : Real.sin (angleAt iTiling.C.model 0) / Real.sin (angleAt iTiling.C.model 1) = slen iTiling.C 0 / slen iTiling.C 1 := sin_ratio_eq iTiling.C
  have hsum : angleAt iTiling.C.model 0 + angleAt iTiling.C.model 1 + angleAt iTiling.C.model 2 = Real.pi :=
    Erdos634.Draft.LaczFormal.angleAt_sum iTiling.C.model
  rw [iDiss_slen0, iDiss_slen1] at hratio
  have hpi := Real.pi_pos
  have hb : angleAt iTiling.C.model 1 = 2 * Real.pi / 3 - angleAt iTiling.C.model 0 := by linarith
  rw [hb] at hratio
  rcases h with h | h
  · rw [h] at hratio
    have e : 2 * Real.pi / 3 - Real.pi / 6 = Real.pi / 2 := by ring
    rw [e, Real.sin_pi_div_six, Real.sin_pi_div_two] at hratio
    norm_num at hratio
  · rw [h] at hratio
    have e : 2 * Real.pi / 3 - Real.pi / 2 = Real.pi / 6 := by ring
    rw [e, Real.sin_pi_div_six, Real.sin_pi_div_two] at hratio
    norm_num at hratio

/-- All hypotheses of `ivc_final_ge5` except `5 <= M` hold on the tile (1, 3, sqrt 7): gamma = pi/3, a ~ b, c not ~ a, alpha/pi irrational, regular; and the M = 4 conclusion (i). -/
theorem ivc_irr_tile_data :
    angleAt iTiling.C.model 2 = Real.pi / 3 ∧ Comm (slen iTiling.C 0) (slen iTiling.C 1) ∧ ¬ Comm (slen iTiling.C 0) (slen iTiling.C 2) ∧
    (¬ ∃ r : ℚ, angleAt iTiling.C.model 0 = (r : ℝ) * Real.pi) ∧ RegularPQ iTiling.C ∧ Concl1 iTiling.C iTiling.P :=
  ⟨iTiling_gamma, iTiling_comm, iTiling_notComm, iTiling_alpha_irr, pDiss_regular (by norm_num) iT_pos,
    caseIVc_small iTiling (pDiss_regular (by norm_num) iT_pos) iTiling_gamma iTiling_comm iTiling_notComm le_rfl⟩

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.ivc_irr_tile_data
