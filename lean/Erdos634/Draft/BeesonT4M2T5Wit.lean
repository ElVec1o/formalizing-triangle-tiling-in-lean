import Erdos634.Draft.BeesonT4M2T5
import Erdos634.Draft.G3HRows

/-!
# Witnesses for `t4_M2_T5` (Beeson Theorems 4, 5): the 84-tiling and the 48-tiling

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Thms 4, 5), Beeson-Zhang, Laczkovich.
* 84-tiling (`G3CS3Control.D`): target `(alpha, alpha, alpha + 2 beta)` with sides `(192, 192, 336)`, tile `(16, 24, 32)`,
  `s = 1/2`.  `Lambda = 192/16 = 12` from the sides opposite `alpha`; the printed `M1 = Lambda s(2+s)/(1+s) = 10`,
  `M2 = -Lambda s(2-s)/(1-s) = -18`.  Cross-check by hand: `10 * (16+24+32) = 720 = 192 + 192 + 336` and
  `18 * (32+24-16) = 720`.
* 48-tiling (`G3CAtomControl.D`): target `(alpha+beta, alpha+beta, alpha)` with sides `(192, 192, 96)`, tile `(16, 24, 32)`,
  `s = 1/2`, `Lambda = 96/16 = 6`; `M1 = Lambda/(1+s) = 4`, `M2 = -Lambda/(1-s) = -12`, and Theorem 5's
  `s = (M1 + M2)/(M2 - M1) = 1/2`.  Cross-check: `4 * 72 = 288 = 192 + 192 - 96`, `12 * 40 = 480 = 192 + 192 + 96`.
All hypotheses of `t4_M2_T5` hold (H1 is `alpha44_irr`).  No joint witness is given for the row `(beta, 3alpha, beta)`.
-/

open scoped Classical

namespace Erdos634.BeesonColoring.W84

open Erdos634.Geometry Erdos634.Geometry.A1Field
open Erdos634.Draft.FluxGridWitness (α44 β44 α44_irr three_α_two_β)

theorem t4_M2_at_84 : ∃ M1 M2 : ℤ, (M1 : ℝ) = 10 ∧ (M2 : ℝ) = -18 := by
  have hrel := three_α_two_β
  have hd := Erdos634.Draft.G3CS3Control.data
  have e0 := Erdos634.Draft.G3CS3Control.target_angle0
  have e1 := Erdos634.Draft.G3CS3Control.target_angle1
  have e2 : Erdos634.Draft.G3CS3Control.D.target.angleAt 2 = α44 + 2 * β44 := by
    have := Erdos634.Draft.G3CS3Control.D.target.angleAt_sum
    rw [e0, e1] at this; linarith
  obtain ⟨T1, -, -⟩ := t4_M2_T5 Erdos634.Draft.G3CS3Control.D α44_irr hrel hd
  obtain ⟨M1, M2, h1, h2⟩ := T1 ⟨e0, e1, e2⟩
  have hsa : 0 < Real.sin α44 := by
    obtain ⟨-, -, -, hα, hβ⟩ := model_abc_pos hd
    exact Real.sin_pos_of_pos_of_lt_pi hα (by linarith [Real.pi_pos])
  have hDm := circD_pos Erdos634.Draft.G3CS3Control.D.model
  have t0 : Erdos634.Draft.G3CS3Control.D.target.oppLen 0 = 192 := by
    unfold Tri.oppLen
    simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl]
    exact Erdos634.Draft.G3CS3Control.t_d12
  have m0 := (Erdos634.Draft.G3CS3Control.model_opp).1
  have ht := oppLen_eq Erdos634.Draft.G3CS3Control.D.target 0
  have hm := oppLen_eq Erdos634.Draft.G3CS3Control.D.model 0
  rw [t0, e0] at ht
  rw [m0, Erdos634.Draft.G3CS3Control.model_angle0] at hm
  have hΛ : circD Erdos634.Draft.G3CS3Control.D.target / circD Erdos634.Draft.G3CS3Control.D.model = 12 := by
    rw [div_eq_iff hDm.ne']
    have : circD Erdos634.Draft.G3CS3Control.D.target * Real.sin α44
        = 12 * circD Erdos634.Draft.G3CS3Control.D.model * Real.sin α44 := by
      linarith
    exact mul_right_cancel₀ hsa.ne' this
  refine ⟨M1, M2, ?_, ?_⟩
  · rw [h1, hΛ]; norm_num
  · rw [h2, hΛ]; norm_num

theorem t4_M2_at_48 : ∃ M1 M2 : ℤ, (M1 : ℝ) = 4 ∧ (M2 : ℝ) = -12 ∧
    (1 / 2 : ℝ) = ((M1 : ℝ) + M2) / ((M2 : ℝ) - M1) := by
  have hrel := three_α_two_β
  have hd := Erdos634.Draft.G3CAtomControl.threeAlpha
  have e0 := Erdos634.Draft.G3CAtomControl.t_angle0
  have e1 := Erdos634.Draft.G3CAtomControl.t_angle1
  have e2 := Erdos634.Draft.G3CAtomControl.t_angle2
  obtain ⟨-, -, T3⟩ := t4_M2_T5 Erdos634.Draft.G3CAtomControl.D α44_irr hrel hd
  obtain ⟨M1, M2, h1, h2, h3, -⟩ := T3 ⟨e0, e1, e2⟩
  have hsa : 0 < Real.sin α44 := by
    obtain ⟨-, -, -, hα, hβ⟩ := model_abc_pos hd
    exact Real.sin_pos_of_pos_of_lt_pi hα (by linarith [Real.pi_pos])
  have hDm := circD_pos Erdos634.Draft.G3CAtomControl.D.model
  have t2 := Erdos634.Draft.G3CAtomControl.t_opp2
  have m0 := Erdos634.Draft.G3CAtomControl.m_opp0
  have ht := oppLen_eq Erdos634.Draft.G3CAtomControl.D.target 2
  have hm := oppLen_eq Erdos634.Draft.G3CAtomControl.D.model 0
  rw [t2, e2] at ht
  rw [m0, Erdos634.Draft.G3CAtomControl.model_angle0] at hm
  have hΛ : circD Erdos634.Draft.G3CAtomControl.D.target / circD Erdos634.Draft.G3CAtomControl.D.model = 6 := by
    rw [div_eq_iff hDm.ne']
    have : circD Erdos634.Draft.G3CAtomControl.D.target * Real.sin α44
        = 6 * circD Erdos634.Draft.G3CAtomControl.D.model * Real.sin α44 := by
      linarith
    exact mul_right_cancel₀ hsa.ne' this
  have h4 : (M1 : ℝ) = 4 := by rw [h1, hΛ]; norm_num
  have h5 : (M2 : ℝ) = -12 := by rw [h2, hΛ]; norm_num
  refine ⟨M1, M2, h4, h5, ?_⟩
  rw [h4, h5]; norm_num

end Erdos634.BeesonColoring.W84

#print axioms Erdos634.BeesonColoring.W84.t4_M2_at_84
#print axioms Erdos634.BeesonColoring.W84.t4_M2_at_48
