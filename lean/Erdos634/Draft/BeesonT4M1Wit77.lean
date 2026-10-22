import Erdos634.Draft.BeesonT4M1
import Erdos634.Draft.BeesonColoringThm1ColourWit77

/-!
# Witness for `t4_M1` (Beeson Theorem 4, `M1` column): the 77-tiling

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Fig. 15, Thm 4), Beeson-Zhang, Laczkovich.
77-tiling of `(2 alpha, alpha, 2 beta)` by the tile `(2,3,4)`, `s = a/c = 1/2`.  The circumdiameter ratio is computed
independently of `t4_M1` from the two sides opposite the angle `alpha` (target side `16`, tile side `2`): `Lambda = 8`.
Then the printed `M1 = Lambda s (1-s)(2+s) = 8 * (1/4) * (5/2) = 5` agrees with the number of black tiles minus the
number of white tiles, `5` (`colouring_at_77`).  Every hypothesis of `t4_M1` holds here (H1 is `alpha44_irr`).
-/

open scoped Classical

namespace Erdos634.BeesonColoring.W77

open Erdos634.Geometry Erdos634.Draft.FluxGridWitness Erdos634.Geometry.A1Field

theorem t4_at_77 : ∃ D : CongruentDissection 77,
    circD D.target / circD D.model = 8 ∧ ∃ M : ℤ, 0 < M ∧ (M : ℝ) = 5 := by
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
  obtain ⟨-, -, -, T4, -⟩ := t4_M1 D α44_irr hrel hfull
  obtain ⟨M, hM, hMe⟩ := T4 ⟨e0, e1, e2⟩
  refine ⟨M, hM, ?_⟩
  rw [hMe, hΛ]
  norm_num

end Erdos634.BeesonColoring.W77

#print axioms Erdos634.BeesonColoring.W77.t4_at_77
