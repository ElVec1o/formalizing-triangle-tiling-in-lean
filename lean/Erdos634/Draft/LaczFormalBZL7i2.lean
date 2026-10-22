import Erdos634.Draft.LaczFormalBZL7i1
import Erdos634.Draft.ZhangSporadic
import Erdos634.Draft.ZhangRat

-- Draft/LaczFormalBZL7i2.lean -- WITNESSES for rows 3 and 6 of Beeson-Zhang Thm 1.1 (gamma = 2pi/3), from Zhang's constructions (arXiv 2512.22696v4, Props 8, 9, tile (3,5,7), m = 9):
--   row 3 `witness_row3` : isosceles target (alpha, alpha, pi - 2 alpha), N = 5265 (Prop 8(1), `ZhangSporadic.zhang_prop8_1_357`);
--   row 6 `witness_row6` : target (alpha, pi/3, 2pi/3 - alpha) = (alpha, alpha + beta, alpha + 2 beta), N = 3240 (Prop 9(1), `zhang_prop9_1_357`).
-- Each is a genuine `CongruentDissection N` (region dissection of the dilated coordinate triangle, `toCongruentDissection`), satisfies every hypothesis of `bz_thm11` (data, alpha not in Q pi, NotSim), and `Comm a b /\ Comm a c` holds (rational sides).
-- NOTE, UNAUDITED.  Credit: Zhang (arXiv 2512.22696v4; the constructions), Herdt (the 1215 equilateral tiling used inside), Beeson-Zhang (arXiv 2604.01314), Laczkovich (DCG 48 (2012)).

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Thm21 Erdos634.Draft.LaczFormal.RG
  Erdos634.Draft.LaczFormal.BZL7Wit Erdos634.Draft.G3CAng Erdos634.Draft.TheoremPConditional Erdos634.LaczL22 Erdos634.ZhangSporadic
  Erdos634.ZhangRat Erdos634.ZhangRat3 Erdos634.ZhangL1 Erdos634.ZhangPara

namespace Erdos634.Draft.LaczFormal.BZL7i

theorem half_dis {S : Set Plane} {n : ℕ} (h : Dis (RM 3 5 (by norm_num) (by norm_num)) S n) :
    ∃ R : RTri, R.a = 3 / 2 ∧ R.b = 5 / 2 ∧ R.c = 7 / 2 ∧ ∃ C : CongruentRegionDissection n,
      C.region = dil (1 / 2 : ℝ) S ∧ C.model.Congruent R.Δ := by
  obtain ⟨R, ha, hb, hc, -, -⟩ := rat_wit
  obtain ⟨C, hr, hm⟩ := rat_dis R 3 5 7 (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [ha]; norm_num) (by rw [hb]; norm_num) (by rw [hc]; norm_num) h
  exact ⟨R, ha, hb, hc, C, by rw [hr]; norm_num, hm⟩

theorem witness_row3 : ∃ (D : CongruentDissection 5265) (α a b c : ℝ), D.model.TwoPiThreeData α a b c ∧
    (¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) ∧ NotSim D ∧ D.target.angleAt 0 = Real.pi - 2 * α ∧ D.target.angleAt 1 = α ∧
    D.target.angleAt 2 = α ∧ Comm a b ∧ Comm a c := by
  have hz := zs_pos
  have hzz := zs_sq
  obtain ⟨R, ha, hb, hc, C, hr, hm⟩ := half_dis zhang_prop8_1_357
  rw [dil_TriSet (1 / 2) (by norm_num)] at hr
  have hdet : 0 < det3 (1 / 2 * (135 / 2)) (1 / 2 * (135 * zs / 2)) (1 / 2 * -225) (1 / 2 * 0) (1 / 2 * 360) (1 / 2 * 0) := by
    simp only [det3]; nlinarith
  obtain ⟨D, hDt, τ, o0, o1, o2⟩ := region_to_D C R ha hb hc hm _ _ _ _ _ _ hdet hr
  obtain ⟨data, c0, c1, hab, hirr⟩ := tile_angles D.model τ o0 o1 o2
  have hs := mk_oppLen _ _ _ _ _ _ hdet.ne' (585 / 2) (315 / 2) (315 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by nlinarith) (by nlinarith)
  rw [← hDt] at hs
  obtain ⟨k0, k1, k2⟩ := tri_cos D.target _ _ _ (by norm_num) (by norm_num) (by norm_num) hs.1 hs.2.1 hs.2.2
  have e1 : D.target.angleAt 1 = D.model.angleAt (τ 0) := angle_eq_of_cos (T := D.target) (U := D.model) 1 (τ 0) (by rw [k1, c0]; norm_num)
  have e2 : D.target.angleAt 2 = D.model.angleAt (τ 0) := angle_eq_of_cos (T := D.target) (U := D.model) 2 (τ 0) (by rw [k2, c0]; norm_num)
  have e0 : D.target.angleAt 0 = Real.pi - 2 * D.model.angleAt (τ 0) := by
    have := D.target.angleAt_sum
    simp only [Fin.sum_univ_three] at this
    linarith
  obtain ⟨hr0, hr1⟩ := data.alpha_range
  have hpi := Real.pi_pos
  obtain ⟨hNS, hcm⟩ := bz_apply D hirr data 0 (by rw [e0]; intro e; linarith) (by rw [e0]; intro e; linarith)
    (by rw [e0]; intro e; exact hirr ⟨1 / 6, by push_cast; linarith⟩)
  exact ⟨D, _, _, _, _, data, hirr, hNS, e0, e1, e2, hcm⟩

theorem witness_row6 : ∃ (D : CongruentDissection 3240) (α a b c : ℝ), D.model.TwoPiThreeData α a b c ∧
    (¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) ∧ NotSim D ∧ D.target.angleAt 0 = 2 * Real.pi / 3 - α ∧ D.target.angleAt 1 = α ∧
    D.target.angleAt 2 = Real.pi / 3 ∧ Comm a b ∧ Comm a c := by
  have hz := zs_pos
  have hzz := zs_sq
  obtain ⟨R, ha, hb, hc, C, hr, hm⟩ := half_dis zhang_prop9_1_357
  rw [dil_TriSet (1 / 2) (by norm_num)] at hr
  have hdet : 0 < det3 (1 / 2 * (135 / 2)) (1 / 2 * (135 * zs / 2)) (1 / 2 * -225) (1 / 2 * 0) (1 / 2 * 135) (1 / 2 * 0) := by
    simp only [det3]; nlinarith
  obtain ⟨D, hDt, τ, o0, o1, o2⟩ := region_to_D C R ha hb hc hm _ _ _ _ _ _ hdet hr
  obtain ⟨data, c0, c1, hab, hirr⟩ := tile_angles D.model τ o0 o1 o2
  have hs := mk_oppLen _ _ _ _ _ _ hdet.ne' 180 (135 / 2) (315 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by nlinarith) (by nlinarith)
  rw [← hDt] at hs
  obtain ⟨k0, k1, k2⟩ := tri_cos D.target _ _ _ (by norm_num) (by norm_num) (by norm_num) hs.1 hs.2.1 hs.2.2
  have hpi := Real.pi_pos
  have e1 : D.target.angleAt 1 = D.model.angleAt (τ 0) := angle_eq_of_cos (T := D.target) (U := D.model) 1 (τ 0) (by rw [k1, c0]; norm_num)
  have k2' : Real.cos (D.target.angleAt 2) = Real.cos (Real.pi / 3) := by rw [k2, Real.cos_pi_div_three]; norm_num
  have e2 : D.target.angleAt 2 = Real.pi / 3 :=
    Real.injOn_cos (Erdos634.Draft.FluxPaperWitness.cornerAngle_mem' _ _ _) ⟨by positivity, by linarith⟩ k2'
  have e0 : D.target.angleAt 0 = 2 * Real.pi / 3 - D.model.angleAt (τ 0) := by
    have := D.target.angleAt_sum
    simp only [Fin.sum_univ_three] at this
    linarith
  obtain ⟨hr0, hr1⟩ := data.alpha_range
  obtain ⟨hNS, hcm⟩ := bz_apply D hirr data 0 (by rw [e0]; intro e; linarith) (by rw [e0]; intro e; linarith)
    (by rw [e0]; intro e; linarith)
  exact ⟨D, _, _, _, _, data, hirr, hNS, e0, e1, e2, hcm⟩

end Erdos634.Draft.LaczFormal.BZL7i

#print axioms Erdos634.Draft.LaczFormal.BZL7i.witness_row3
#print axioms Erdos634.Draft.LaczFormal.BZL7i.witness_row6
