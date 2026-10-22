-- Draft/LaczFormalBZL7d7.lean -- WITNESS for `bz_thm11` (Beeson-Zhang Thm 1.1 for every triangle target not similar to the tile) and `NotSim`:
--   `notSim_of_no_match`   : a target angle different from alpha, pi/3 - alpha, 2 pi/3 gives `NotSim`;
--   `witness_1215_thm11`   : the certified N = 1215 tiling (equilateral target, tile 1890*(3,5,7)) satisfies every hypothesis of `bz_thm11` (NotSim included); conclusion 3:5:7 commensurable;
--   `witness_143_thm11`    : the kernel-checked N = 143 tiling (target 14*(39,49,55), angles (pi/3, 2 beta, 2 alpha)) likewise.
-- Both witnesses lie in the two rows that were already known (equilateral, (2alpha,2beta,pi/3)); NO tiling is known for any other target, so the other rows of the theorem are not witnessed.
-- NOTE, UNAUDITED.  Credit: Herdt, Zhang (the 1215-tiling), the 143-tiling (this project), Beeson-Zhang (arXiv 2604.01314v1), Laczkovich (DCG 48 (2012)), Beeson.
import Erdos634.Draft.LaczFormalBZL7d6
import Erdos634.Draft.LaczFormalBZL7c8
import Erdos634.R143TilingBridge
import Erdos634.Draft.LaczFormalBZWit

open scoped Classical
open Erdos634.Geometry Erdos634.Draft.LaczFormal.Thm21 Erdos634.Draft.LaczFormal.RG Erdos634.Draft.LaczFormal.BZL7Wit Erdos634.Draft.G3CAng Erdos634.Draft.TheoremPConditional

namespace Erdos634.Draft.LaczFormal.BZL7Wit

theorem notSim_of_no_match {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ} (h : D.model.TwoPiThreeData α a b c) (j : Fin 3)
    (h0 : D.target.angleAt j ≠ α) (h1 : D.target.angleAt j ≠ Real.pi / 3 - α) (h2 : D.target.angleAt j ≠ 2 * Real.pi / 3) : NotSim D := by
  rintro ⟨ρ, hρ⟩
  obtain ⟨σ, e0, -, e1, -, e2, -⟩ := h
  obtain ⟨k, hk⟩ := σ.surjective (ρ j)
  have := hρ j
  rw [← hk] at this
  have hk3 : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  rcases hk3 with rfl | rfl | rfl
  · exact h0 (this.trans e0)
  · exact h1 (this.trans e1)
  · exact h2 (this.trans e2)

theorem witness_1215_thm11 : Comm (1890 * 3) (1890 * 5) ∧ Comm (1890 * 3) (1890 * 7) := by
  open Erdos634.Draft.G3CEqui135Control in
  have hpi := Real.pi_pos
  open Erdos634.Draft.G3CEqui135Control in
  obtain ⟨hr0, hr1⟩ := data.alpha_range
  open Erdos634.Draft.G3CEqui135Control in
  have hNS : NotSim D := notSim_of_no_match D data 0 (by rw [t_angle]; intro e; exact α_irr ⟨1 / 3, by push_cast; linarith⟩)
    (by rw [t_angle]; intro e; linarith) (by rw [t_angle]; intro e; linarith)
  open Erdos634.Draft.G3CEqui135Control in
  exact bz_thm11 D α_irr data hNS

theorem witness_143_thm11 : Comm (14 * 3) (14 * 5) ∧ Comm (14 * 3) (14 * 7) := by
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
  have hNS : NotSim D := notSim_of_no_match D data 0 (by rw [A0]; intro e; exact α_irr ⟨1 / 3, by push_cast; linarith⟩)
    (by rw [A0]; intro e; linarith) (by rw [A0]; intro e; linarith)
  exact bz_thm11 D α_irr data hNS

end Erdos634.Draft.LaczFormal.BZL7Wit

#print axioms Erdos634.Draft.LaczFormal.BZL7Wit.notSim_of_no_match
#print axioms Erdos634.Draft.LaczFormal.BZL7Wit.witness_1215_thm11
#print axioms Erdos634.Draft.LaczFormal.BZL7Wit.witness_143_thm11
