import Erdos634.Draft.LaczFormalBZL7i2

-- Draft/LaczFormalBZL7i3.lean -- WITNESS for row 5 of Beeson-Zhang Thm 1.1 (gamma = 2pi/3): target (alpha, 2 beta, 2 alpha + beta), N = 7128, tile (3,5,7)
--   (Zhang arXiv 2512.22696v4 Prop 10(1), `ZhangSporadic.zhang_prop10_1_357`).  Same shape as BZL7i2.  NOTE, UNAUDITED.
-- Credit: Zhang (the construction), Herdt (the 1215 equilateral tiling used inside), Beeson-Zhang (arXiv 2604.01314), Laczkovich (DCG 48 (2012)).

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Thm21 Erdos634.Draft.LaczFormal.RG
  Erdos634.Draft.LaczFormal.BZL7Wit Erdos634.Draft.G3CAng Erdos634.Draft.TheoremPConditional Erdos634.LaczL22 Erdos634.ZhangSporadic
  Erdos634.ZhangRat Erdos634.ZhangRat3 Erdos634.ZhangL1 Erdos634.ZhangPara

namespace Erdos634.Draft.LaczFormal.BZL7i

theorem witness_row5 : ∃ (D : CongruentDissection 7128) (α a b c : ℝ), D.model.TwoPiThreeData α a b c ∧
    (¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) ∧ NotSim D ∧ D.target.angleAt 0 = 2 * (Real.pi / 3 - α) ∧ D.target.angleAt 1 = α ∧
    D.target.angleAt 2 = Real.pi / 3 + α ∧ Comm a b ∧ Comm a c := by
  have hz := zs_pos
  have hzz := zs_sq
  obtain ⟨R, ha, hb, hc, C, hr, hm⟩ := half_dis zhang_prop10_1_357
  rw [dil_TriSet (1 / 2) (by norm_num)] at hr
  have hdet : 0 < det3 (1 / 2 * -81) (1 / 2 * 0) (1 / 2 * 315) (1 / 2 * -(180 * zs)) (1 / 2 * (135 / 2)) (1 / 2 * (135 * zs / 2)) := by
    simp only [det3]; nlinarith
  obtain ⟨D, hDt, τ, o0, o1, o2⟩ := region_to_D C R ha hb hc hm _ _ _ _ _ _ hdet hr
  obtain ⟨data, c0, c1, hab, hirr⟩ := tile_angles D.model τ o0 o1 o2
  have hs := mk_oppLen _ _ _ _ _ _ hdet.ne' (495 / 2) (189 / 2) 252 (by norm_num) (by norm_num) (by norm_num)
    (by nlinarith) (by nlinarith) (by nlinarith)
  rw [← hDt] at hs
  obtain ⟨k0, k1, k2⟩ := tri_cos D.target _ _ _ (by norm_num) (by norm_num) (by norm_num) hs.1 hs.2.1 hs.2.2
  have hpi := Real.pi_pos
  obtain ⟨hr0, hr1⟩ := data.alpha_range
  have e1 : D.target.angleAt 1 = D.model.angleAt (τ 0) := angle_eq_of_cos (T := D.target) (U := D.model) 1 (τ 0) (by rw [k1, c0]; norm_num)
  have k0' : Real.cos (D.target.angleAt 0) = Real.cos (2 * D.model.angleAt (τ 1)) := by
    rw [k0, Real.cos_two_mul, c1]; norm_num
  have e0' : D.target.angleAt 0 = 2 * D.model.angleAt (τ 1) :=
    Real.injOn_cos (Erdos634.Draft.FluxPaperWitness.cornerAngle_mem' _ _ _) ⟨by linarith, by linarith⟩ k0'
  have e0 : D.target.angleAt 0 = 2 * (Real.pi / 3 - D.model.angleAt (τ 0)) := by rw [e0']; congr 1; linarith
  have e2 : D.target.angleAt 2 = Real.pi / 3 + D.model.angleAt (τ 0) := by
    have := D.target.angleAt_sum
    simp only [Fin.sum_univ_three] at this
    linarith
  obtain ⟨hNS, hcm⟩ := bz_apply D hirr data 0 (by rw [e0]; intro e; exact hirr ⟨2 / 9, by push_cast; linarith⟩)
    (by rw [e0]; intro e; linarith) (by rw [e0]; intro e; linarith)
  exact ⟨D, _, _, _, _, data, hirr, hNS, e0, e1, e2, hcm⟩

end Erdos634.Draft.LaczFormal.BZL7i

#print axioms Erdos634.Draft.LaczFormal.BZL7i.witness_row5
