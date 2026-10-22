import Erdos634.Draft.BeesonT4Final
import Erdos634.Draft.BeesonColoringThm1ColourWit77

/-!
# Witness for `t4_final` (row `(2alpha, alpha, 2beta)`): the 77-tiling

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Fig. 15, Thm 4), Beeson-Zhang, Laczkovich.
77-tiling of `(2 alpha, alpha, 2 beta)` by the tile `(2,3,4)`, `s = 1/2`, `Lambda = 8` (computed from the sides opposite
`alpha`, independently of `t4_final`).  Printed `M1 = Lambda s (1-s)(2+s) = 5`, `M2 = -Lambda s (2-s)(1+s) = -9`.
H1 is `alpha44_irr`.  All hypotheses of `t4_final` hold, and the conclusion yields `M1 = 5, M2 = -9`, both nonzero.
-/

open scoped Classical

namespace Erdos634.BeesonColoring.W77

open Erdos634.Geometry Erdos634.Draft.FluxGridWitness Erdos634.Geometry.A1Field

theorem t4_final_at_77 : ∃ D : CongruentDissection 77,
    circD D.target / circD D.model = 8 ∧ ∃ M1 M2 : ℤ, (M1 : ℝ) = 5 ∧ (M2 : ℝ) = -9 ∧ M1 ≠ 0 ∧ M2 ≠ 0 := by
  obtain ⟨D, h, e0, e1, e2, o0, o1, o2⟩ := exists_D77'
  refine ⟨D, ?_⟩
  have hrel := three_α_two_β
  obtain ⟨-, -, -, hαpos, hβpos⟩ := model_abc_pos h
  have hsa : 0 < Real.sin α44 :=
    Real.sin_pos_of_pos_of_lt_pi hαpos (by linarith [Real.pi_pos])
  have hD := circD_pos D.model
  have hfull := h
  obtain ⟨σ, h0, ma, -, -, -, -⟩ := h
  have e16 : (16 : ℝ) = circD D.target * Real.sin α44 := by
    rw [← o1, oppLen_eq, e1]
  have e2' : (2 : ℝ) = circD D.model * Real.sin α44 := by
    rw [← ma, oppLen_eq, h0]
  have hΛ : circD D.target / circD D.model = 8 := by
    rw [div_eq_iff hD.ne']
    have : circD D.target * Real.sin α44 = 8 * circD D.model * Real.sin α44 := by
      rw [← e16]; linarith
    exact mul_right_cancel₀ hsa.ne' this
  refine ⟨hΛ, ?_⟩
  obtain ⟨-, -, -, T4, -⟩ := t4_final D α44_irr hrel hfull
  obtain ⟨M1, M2, h1, h2, n1, n2⟩ := T4 ⟨e0, e1, e2⟩
  refine ⟨M1, M2, ?_, ?_, n1, n2⟩
  · rw [h1, hΛ]; norm_num
  · rw [h2, hΛ]; norm_num

end Erdos634.BeesonColoring.W77

#print axioms Erdos634.BeesonColoring.W77.t4_final_at_77
