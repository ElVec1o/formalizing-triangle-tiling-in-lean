import Erdos634.Draft.BeesonT6
import Erdos634.Draft.BeesonColoringThm1ColourWit77

/-!
# Witness for `lemma27` and `t6` (shape `(2alpha, alpha, 2beta)`): the 77-tiling

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Lemma 27, Thm 6, Fig. 15 and the table after Lemma 27),
Beeson-Zhang, Laczkovich.  77-tiling by `(2,3,4)`, `s = 1/2`, `Lambda = 8`, `M1 = 5`, `M2 = -9`: `N + M1 M2 = 32`,
`(M1+M2)^2/(2*32) = 1/4 = s^2`, and `lemma27` gives `77 = 64 * (1/4)(7/4)(11/4)`.  H1 is `alpha44_irr`.
-/

open scoped Classical

namespace Erdos634.BeesonColoring.W77

open Erdos634.Geometry Erdos634.Draft.FluxGridWitness Erdos634.Geometry.A1Field

theorem t6_at_77 : ∃ D : CongruentDissection 77, circD D.target / circD D.model = 8 ∧
    ((77 : ℝ) = 8 ^ 2 * ((1 / 2) ^ 2 * (2 - (1 / 2) ^ 2) * (3 - (1 / 2) ^ 2))) ∧
    ∃ M1 M2 : ℤ, (M1 : ℝ) = 5 ∧ (M2 : ℝ) = -9 ∧ ((77 : ℕ) : ℝ) + M1 * M2 = 32 := by
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
  refine ⟨hΛ, ?_, ?_⟩
  · norm_num
  · obtain ⟨-, -, -, -, L5⟩ := lemma27 D hrel hfull
    obtain ⟨M1, M2, h1, h2, hne, hb, -⟩ := (t6 D α44_irr hrel hfull).2 ⟨e0, e1, e2⟩
    have hN := L5 ⟨e0, e1, e2⟩
    refine ⟨M1, M2, ?_, ?_, ?_⟩
    · rw [h1, hΛ]; norm_num
    · rw [h2, hΛ]; norm_num
    · have a1 : (M1 : ℝ) = 5 := by rw [h1, hΛ]; norm_num
      have a2 : (M2 : ℝ) = -9 := by rw [h2, hΛ]; norm_num
      rw [a1, a2]; norm_num

end Erdos634.BeesonColoring.W77

#print axioms Erdos634.BeesonColoring.W77.t6_at_77
