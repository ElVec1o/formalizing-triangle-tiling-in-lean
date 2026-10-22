-- Draft/LaczFormalBZL7c8.lean -- WITNESS for Beeson-Zhang Thm 5.3 (`RG.bz_thm53`): the kernel-checked N = 143 tiling (R143Tiling, scale 14: tile 14*(3,5,7), target 14*(39,49,55)) is a congruent dissection of a triangle with
-- angles (2 alpha, pi/3, 2 beta) at the vertices (2, 0, 1) by the tile (alpha, pi/3 - alpha, 2 pi/3), cos alpha = 13/14, alpha not in Q pi.  EVERY hypothesis of `bz_thm53` holds; the conclusion (sides 3:5:7 commensurable) holds.
-- This is the control that `bz_thm53` and the hypotheses of `bz_ab_comm_row`, `bz_phi_gen` are not vacuous on the (2 alpha, pi/3, 2 beta) row (N143 is the least area count, 143 = (a+2b)(2a+b)).
-- NOTE, UNAUDITED.  Credit: the 143-tiling (this project, mrv2 search, exact verification), Beeson-Zhang (arXiv 2604.01314v1, Thm 5.3), Laczkovich (DCG 48 (2012)), Beeson.
import Erdos634.Draft.LaczFormalBZL7c7
import Erdos634.R143TilingBridge
import Erdos634.Draft.G3CAng

open scoped Classical
open Erdos634.Geometry Erdos634.Draft.LaczFormal.Thm21 Erdos634.Draft.LaczFormal.RG Erdos634.Draft.G3CAng Erdos634.Draft.TheoremPConditional

namespace Erdos634.Draft.LaczFormal.BZL7Wit

theorem dist_of_sq {x : ℝ} {s : ℝ} (hs : 0 ≤ s) (hx : 0 ≤ x) (h : x ^ 2 = s ^ 2) : x = s :=
  (pow_left_inj₀ hx hs two_ne_zero).mp h

theorem witness_143 : Comm (14 * 3) (14 * 5) ∧ Comm (14 * 3) (14 * 7) := by
  obtain ⟨D, t01, t12, t20, m01, m12, m20⟩ := Erdos634.R143TilingBridge.r143_dissection_shape
  have T2 : D.target.oppLen 2 = 14 * 39 :=
    dist_of_sq (by norm_num) dist_nonneg (by rw [show (14 * 39 : ℝ) ^ 2 = 298116 by norm_num]; exact t01)
  have T0 : D.target.oppLen 0 = 14 * 49 :=
    dist_of_sq (by norm_num) dist_nonneg (by rw [show (14 * 49 : ℝ) ^ 2 = 470596 by norm_num]; exact t12)
  have T1 : D.target.oppLen 1 = 14 * 55 :=
    dist_of_sq (by norm_num) dist_nonneg (by rw [show (14 * 55 : ℝ) ^ 2 = 592900 by norm_num]; exact t20)
  have M2 : D.model.oppLen 2 = 14 * 3 :=
    dist_of_sq (by norm_num) dist_nonneg (by rw [show (14 * 3 : ℝ) ^ 2 = 1764 by norm_num]; exact m01)
  have M0 : D.model.oppLen 0 = 14 * 5 :=
    dist_of_sq (by norm_num) dist_nonneg (by rw [show (14 * 5 : ℝ) ^ 2 = 4900 by norm_num]; exact m12)
  have M1 : D.model.oppLen 1 = 14 * 7 :=
    dist_of_sq (by norm_num) dist_nonneg (by rw [show (14 * 7 : ℝ) ^ 2 = 9604 by norm_num]; exact m20)
  set σ : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 0 2 with hσ
  have σ0 : σ 0 = 2 := by decide
  have σ1 : σ 1 = 0 := by decide
  have σ2 : σ 2 = 1 := by decide
  have o0 : D.model.oppLen (σ 0) = 14 * 3 := by rw [σ0]; exact M2
  have o1 : D.model.oppLen (σ 1) = 14 * 5 := by rw [σ1]; exact M0
  have o2 : D.model.oppLen (σ 2) = 14 * 7 := by rw [σ2]; exact M1
  have data : D.model.TwoPiThreeData (D.model.angleAt (σ 0)) (14 * 3) (14 * 5) (14 * 7) :=
    tp_data D.model σ 14 3 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) o0 o1 o2
  set α := D.model.angleAt (σ 0) with hα
  have cosα : Real.cos α = 13 / 14 := by
    rw [hα, cos_s0 D.model σ (by rw [o1]; norm_num) (by rw [o2]; norm_num), o0, o1, o2]; norm_num
  have α_irr : IrrPi α :=
    irrPi_of_cos α (13 / 14) (by rw [cosα]; norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hpi := Real.pi_pos
  obtain ⟨hr0, hr1⟩ := data.alpha_range
  -- the target angles
  have A0 : D.target.angleAt 0 = Real.pi / 3 := by
    have key : Real.cos (D.target.angleAt 0) = 1 / 2 := by
      have := cos_s0 D.target 1 (by simp [T1]) (by simp [T2])
      simp only [Equiv.Perm.coe_one, id_eq] at this
      rw [this, T0, T1, T2]; norm_num
    exact Real.injOn_cos (Erdos634.Draft.FluxPaperWitness.cornerAngle_mem' _ _ _)
      ⟨by positivity, by linarith⟩ (key.trans Real.cos_pi_div_three.symm)
  have A2 : D.target.angleAt 2 = 2 * α := by
    have key : Real.cos (D.target.angleAt 2) = Real.cos (2 * α) := by
      have := cos_s2 D.target 1 (by simp [T0]) (by simp [T1])
      simp only [Equiv.Perm.coe_one, id_eq] at this
      rw [this, T0, T1, T2, Real.cos_two_mul, cosα]; norm_num
    exact Real.injOn_cos (Erdos634.Draft.FluxPaperWitness.cornerAngle_mem' _ _ _)
      ⟨by linarith, by linarith⟩ key
  have A1 : D.target.angleAt 1 = 2 * (Real.pi / 3 - α) := by
    have hs := D.target.angleAt_sum
    simp only [Fin.sum_univ_three] at hs
    linarith
  exact bz_thm53 D α_irr data σ (by rw [σ0]; exact A2) (by rw [σ1]; exact A0) (by rw [σ2]; exact A1)

end Erdos634.Draft.LaczFormal.BZL7Wit

#print axioms Erdos634.Draft.LaczFormal.BZL7Wit.witness_143
