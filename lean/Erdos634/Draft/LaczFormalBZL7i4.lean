import Erdos634.Draft.LaczFormalBZL7i3
import Erdos634.Draft.ZhangRat5All
import Erdos634.Draft.ZhangRat4Wit

-- Draft/LaczFormalBZL7i4.lean -- WITNESS for row 4 of Beeson-Zhang Thm 1.1 (gamma = 2pi/3): target (alpha, 2 alpha, pi - 3 alpha) = (alpha, 2 alpha, 3 beta), N = 7800, tile (3,5,7)
--   (Zhang arXiv 2512.22696v4 Prop 11(1), via `ZhangRat5.zhang_prop11_1_final` with the hypothesis triangle of the 3575-tiling, m = 10, m' = 5).  NOTE, UNAUDITED.
-- Credit: Zhang (the construction), Beeson-Zhang (arXiv 2604.01314), Laczkovich (DCG 48 (2012)).

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Thm21 Erdos634.Draft.LaczFormal.RG
  Erdos634.Draft.LaczFormal.BZL7Wit Erdos634.Draft.G3CAng Erdos634.Draft.TheoremPConditional Erdos634.LaczL22 Erdos634.ZhangSporadic
  Erdos634.ZhangRat Erdos634.ZhangRat3 Erdos634.ZhangL1 Erdos634.ZhangPara Erdos634.ZhangRat5

set_option maxHeartbeats 3200000

namespace Erdos634.Draft.LaczFormal.BZL7i

theorem witness_row4 : ∃ (D : CongruentDissection 7800) (α a b c : ℝ), D.model.TwoPiThreeData α a b c ∧
    (¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) ∧ NotSim D ∧ D.target.angleAt 0 = Real.pi - 3 * α ∧ D.target.angleAt 1 = α ∧
    D.target.angleAt 2 = 2 * α ∧ Comm a b ∧ Comm a c := by
  obtain ⟨R, ha, hb, hc, hrel, hab⟩ := rat_wit
  obtain ⟨A, B, C, k, hA, hB, hk, ea, eb, ec, hh, hcop, hne, H⟩ := zhang_prop11_1_final R hrel
  have ha' : k * (A : ℚ) = 3 / 2 := by rw [← ea, ha]
  have hb' : k * (B : ℚ) = 5 / 2 := by rw [← eb, hb]
  obtain ⟨rfl, rfl, rfl, rfl⟩ := ZhangRat4.data_357 A B C k hA hk hcop hh ha' hb'
  obtain ⟨Ax, Ay, Bx, By, Dx, Dy, hD, h1, h2, h3⟩ := ZhangRat2.prop11_wit
  have hD' : 0 < det3 (Ax / 2) (Ay / 2) (Dx / 2) (Dy / 2) (Bx / 2) (By / 2) := by
    have : det3 (Ax / 2) (Ay / 2) (Dx / 2) (Dy / 2) (Bx / 2) (By / 2)
        = (1 / 4) * det3 Ax Ay Dx Dy Bx By := by simp only [det3]; ring
    rw [this]; positivity
  have hRa : (R.a : ℝ) = 3 / 2 := by rw [ha]; norm_num
  have hRb : (R.b : ℝ) = 5 / 2 := by rw [hb]; norm_num
  have hRc : (R.c : ℝ) = 7 / 2 := by rw [hc]; norm_num
  have e1 : (Ax / 2 - Dx / 2) ^ 2 + (Ay / 2 - Dy / 2) ^ 2 = (1 / 4) * ((Ax - Dx) ^ 2 + (Ay - Dy) ^ 2) := by ring
  have e2 : (Bx / 2 - Dx / 2) ^ 2 + (By / 2 - Dy / 2) ^ 2 = (1 / 4) * ((Bx - Dx) ^ 2 + (By - Dy) ^ 2) := by ring
  have e3 : (Ax / 2 - Bx / 2) ^ 2 + (Ay / 2 - By / 2) ^ 2 = (1 / 4) * ((Ax - Bx) ^ 2 + (Ay - By) ^ 2) := by ring
  have g1 : (Ax / 2 - Dx / 2) ^ 2 + (Ay / 2 - Dy / 2) ^ 2 = (((R.a : ℝ) + 2 * R.b) * R.a * 10) ^ 2 := by
    rw [e1, h1, hRa, hRb]; push_cast; norm_num
  have g2 : (Bx / 2 - Dx / 2) ^ 2 + (By / 2 - Dy / 2) ^ 2 = (((R.b : ℝ) + 2 * R.a) * R.b * 10) ^ 2 := by
    rw [e2, h2, hRa, hRb]; push_cast; norm_num
  have g3 : (Ax / 2 - Bx / 2) ^ 2 + (Ay / 2 - By / 2) ^ 2 = ((R.c : ℝ) ^ 2 * 10) ^ 2 := by
    rw [e3, h3, hRc]; push_cast; norm_num
  obtain ⟨Cx, Cy, hCx, hCy, hBC, hAC, -, -, hT1, -⟩ :=
    H 10 5 (by norm_num) (by push_cast; norm_num) ⟨1, 0, by norm_num⟩ (Ax / 2) (Ay / 2) (Bx / 2) (By / 2)
      (Dx / 2) (Dy / 2) hD' g1 g2 g3
  have hq : (((R.a : ℝ) + 2 * R.b) / ((R.b : ℝ) + 2 * R.a)) = 13 / 11 := by rw [hRa, hRb]; norm_num
  rw [hq] at hCx hCy
  have hdet : 0 < det3 (Ax / 2) (Ay / 2) Cx Cy (Bx / 2) (By / 2) := by
    have : det3 (Ax / 2) (Ay / 2) Cx Cy (Bx / 2) (By / 2) = (24 / 11) * det3 (Ax / 2) (Ay / 2) (Dx / 2) (Dy / 2) (Bx / 2) (By / 2) := by
      rw [hCx, hCy]; simp only [det3]; ring
    rw [this]; positivity
  have hT1' : TileDis R (TriSet (Ax / 2) (Ay / 2) Cx Cy (Bx / 2) (By / 2)) 7800 := by simpa using hT1
  obtain ⟨C0, hr, hm⟩ := hT1'
  obtain ⟨D0, hDt, τ, o0, o1, o2⟩ := region_to_D C0 R ha hb hc hm _ _ _ _ _ _ hdet hr
  obtain ⟨data, c0, c1, hab', hirr⟩ := tile_angles D0.model τ o0 o1 o2
  have hs := mk_oppLen _ _ _ _ _ _ hdet.ne' 300 (245 / 2) (455 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by rw [hRa, hRb] at hBC; nlinarith) (by have g3' := g3; rw [hRc] at g3'; nlinarith) (by rw [hRa, hRb, hRc] at hAC; nlinarith)
  rw [← hDt] at hs
  obtain ⟨k0, k1, k2⟩ := tri_cos D0.target _ _ _ (by norm_num) (by norm_num) (by norm_num) hs.1 hs.2.1 hs.2.2
  have hpi := Real.pi_pos
  obtain ⟨hr0, hr1⟩ := data.alpha_range
  have f1 : D0.target.angleAt 1 = D0.model.angleAt (τ 0) := angle_eq_of_cos (T := D0.target) (U := D0.model) 1 (τ 0) (by rw [k1, c0]; norm_num)
  have k2' : Real.cos (D0.target.angleAt 2) = Real.cos (2 * D0.model.angleAt (τ 0)) := by
    rw [k2, Real.cos_two_mul, c0]; norm_num
  have f2 : D0.target.angleAt 2 = 2 * D0.model.angleAt (τ 0) :=
    Real.injOn_cos (Erdos634.Draft.FluxPaperWitness.cornerAngle_mem' _ _ _) ⟨by linarith, by linarith⟩ k2'
  have f0 : D0.target.angleAt 0 = Real.pi - 3 * D0.model.angleAt (τ 0) := by
    have := D0.target.angleAt_sum
    simp only [Fin.sum_univ_three] at this
    linarith
  obtain ⟨hNS, hcm⟩ := bz_apply D0 hirr data 2 (by rw [f2]; intro e; linarith)
    (by rw [f2]; intro e; exact hirr ⟨1 / 9, by push_cast; linarith⟩) (by rw [f2]; intro e; linarith)
  exact ⟨D0, _, _, _, _, data, hirr, hNS, f0, f1, f2, hcm⟩

end Erdos634.Draft.LaczFormal.BZL7i

#print axioms Erdos634.Draft.LaczFormal.BZL7i.witness_row4
