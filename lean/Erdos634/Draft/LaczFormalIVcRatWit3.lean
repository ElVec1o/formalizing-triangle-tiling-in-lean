-- Draft/LaczFormalIVcRatWit3.lean -- NON-VACUITY of `ivc_rat_final` (Laczkovich DCG 48 (2012), Sect. 2 (vi), 8.3, Concl9 / Thm 2.1 (ix)):
-- the 12-tile tiling `rhexT` of the regular hexagon of side 2 by the tile (1, 2, sqrt 3) satisfies EVERY hypothesis of `ivc_rat_final`
-- (RegularPQ, gamma = pi/3, a ~ b, c not ~ a, 5 <= M with M = 6, alpha = pi/6 rational), and `rat_hex_witness` is `ivc_rat_final` applied to it.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 2 (vi), 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatWit2

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

theorem rT_slen0 : slen rT.C 0 = 1 := by
  show dist (mkPt (1 / 2) iT) (mkPt 0 0) = 1
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt, iT]
  rw [abs_of_nonneg (Real.sqrt_nonneg 3), div_pow, sqrt3_sq']; norm_num

theorem rT_slen1 : slen rT.C 1 = 2 := by
  show dist (mkPt 0 0) (mkPt 2 0) = 2
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt]

theorem rT_slen2 : slen rT.C 2 = Real.sqrt 3 := by
  show dist (mkPt 2 0) (mkPt (1 / 2) iT) = Real.sqrt 3
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt, iT]
  congr 1
  rw [Real.dist_eq, sq_abs, abs_of_nonneg (Real.sqrt_nonneg 3), div_pow, sqrt3_sq']
  norm_num

theorem rT_comm : Comm (slen rT.C 0) (slen rT.C 1) := by
  rw [rT_slen0, rT_slen1]
  exact ⟨2, 1, by norm_num, one_pos, by norm_num⟩

theorem rT_notComm : ¬ Comm (slen rT.C 0) (slen rT.C 2) := by
  rw [rT_slen0, rT_slen2]
  rintro ⟨p, q, hp, hq, e⟩
  have h3 : Irrational (Real.sqrt 3) := by exact_mod_cast Nat.Prime.irrational_sqrt (by norm_num : Nat.Prime 3)
  apply h3
  refine ⟨(p : ℚ) / q, ?_⟩
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  push_cast
  field_simp
  linarith

theorem rT_gamma : angleAt rT.C.model 2 = Real.pi / 3 := by
  show EuclideanGeometry.angle (mkPt 2 0) (mkPt 0 0) (mkPt (1 / 2) iT) = Real.pi / 3
  unfold EuclideanGeometry.angle
  simp only [vsub_eq_sub]
  have hn : ‖mkPt (1 / 2) iT - mkPt 0 0‖ = 1 := by
    rw [← dist_eq_norm]
    have := rT_slen0
    unfold slen at this
    exact this
  have hn1 : ‖mkPt 2 0 - mkPt 0 0‖ = 2 := by
    rw [← dist_eq_norm]
    have := rT_slen1
    unfold slen at this
    rw [dist_comm]; exact this
  have hin : inner ℝ (mkPt 2 0 - mkPt 0 0) (mkPt (1 / 2) iT - mkPt 0 0) = 1 := by
    simp [PiLp.inner_apply, Fin.sum_univ_two, mkPt]
  unfold InnerProductGeometry.angle
  rw [hin, hn, hn1]
  have : (1 : ℝ) / (2 * 1) = Real.cos (Real.pi / 3) := by
    rw [Real.cos_pi_div_three]; norm_num
  rw [this, Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]

theorem rT_beta : angleAt rT.C.model 1 = Real.pi / 2 := by
  show EuclideanGeometry.angle (mkPt 0 0) (mkPt (1 / 2) iT) (mkPt 2 0) = Real.pi / 2
  unfold EuclideanGeometry.angle
  simp only [vsub_eq_sub]
  rw [← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  have hh := iT_sq
  simp [PiLp.inner_apply, Fin.sum_univ_two, mkPt]
  nlinarith

theorem rT_alpha : angleAt rT.C.model 0 = Real.pi / 6 := by
  have hsum : angleAt rT.C.model 0 + angleAt rT.C.model 1 + angleAt rT.C.model 2 = Real.pi :=
    Erdos634.Draft.LaczFormal.angleAt_sum rT.C.model
  rw [rT_beta, rT_gamma] at hsum
  linarith

/-- The 12-tile tiling of the regular hexagon of side 2 by the tile (1, 2, sqrt 3). -/
noncomputable def rhexT : PolyTiling (2 + 2 + 2 + 2 + 2 + 2) 6 where
  C := rhexC
  P := rhexPoly
  region_eq := rhexC_region_eq

/-- **NON-VACUITY of `ivc_rat_final`:** every hypothesis (RegularPQ, gamma = pi/3, a ~ b, c not ~ a, 5 <= M = 6, alpha/pi rational) holds on `rhexT`. -/
theorem rat_hex_witness : Thm21Concl rhexT.C rhexT.P :=
  Erdos634.Draft.LaczFormal.RG.ivc_rat_final rhexT rhexC_regular rT_gamma rT_comm rT_notComm (by norm_num) ⟨1 / 6, by have h : angleAt rhexT.C.model 0 = Real.pi / 6 := rT_alpha; rw [h]; push_cast; ring⟩

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.rat_hex_witness
#print axioms Erdos634.Draft.LaczFormal.RG.rhexC_region_eq
