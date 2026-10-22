import Erdos634.Draft.BeesonL28c3
import Erdos634.Draft.BeesonColoringThm1ColourWit77

/-!
# Witness for `lemma28_printed2`: the 77-tiling by `(2,3,4)` gives the PRINTED `(M1, M2) = (5, -9)`, `kappa = 2/7`

NOTE, UNAUDITED.  The sums `M1 = sum eps1`, `M2 = sum eps2` of the tile-flux signs of the 77-tiling (shape
`(2 alpha, alpha, 2 beta)`, anchored at `AB`) are `5` and `-9`, `Lambda = 8`, `s = 1/2`, `kappa = (5-9)/(-9-5) = 2/7`:
exactly Beeson's table after Lemma 27 and his remark after Def. 8.  Credit: Michael Beeson (arXiv 1206.2229 v4),
Beeson-Zhang, Laczkovich.
-/

open scoped Classical

namespace Erdos634.BeesonColoring.W77

open Erdos634.Geometry Erdos634.Draft.FluxGridWitness Erdos634.Geometry.A1Field

theorem lemma28_printed2_at_77 : ∃ D : CongruentDissection 77, ∃ ε1 ε2 : Fin 77 → ℤ,
    D.toDissection.ProperColouring ε1 ∧
    SignsFor D (Phi1 D α44 α44_irr) ε1 ∧ SignsFor D (Phi2 D α44 α44_irr) ε2 ∧
    (∑ i, ε1 i : ℤ) = 5 ∧ (∑ i, ε2 i : ℤ) = -9 ∧
    ((((∑ i, ε1 i : ℤ) : ℝ) + ((∑ i, ε2 i : ℤ) : ℝ)) /
      (((∑ i, ε2 i : ℤ) : ℝ) - ((∑ i, ε1 i : ℤ) : ℝ)) = 2 / 7) := by
  obtain ⟨D, h, e0, e1, e2, o0, o1, o2⟩ := exists_D77'
  have hrel := three_α_two_β
  obtain ⟨ε1, hε1, hc⟩ := exists_signs1 D α44_irr hrel h
  obtain ⟨ε2, hε2, -⟩ := exists_signs2 D α44_irr hrel h
  obtain ⟨-, -, -, hαpos, hβpos⟩ := model_abc_pos h
  have hsa : 0 < Real.sin α44 := Real.sin_pos_of_pos_of_lt_pi hαpos (by linarith [Real.pi_pos])
  have hD := circD_pos D.model
  have hfull := h
  obtain ⟨σ, h0, ma, -, -, -, -⟩ := h
  have e16 : (16 : ℝ) = circD D.target * Real.sin α44 := by rw [← o1, oppLen_eq, e1]
  have e2' : (2 : ℝ) = circD D.model * Real.sin α44 := by rw [← ma, oppLen_eq, h0]
  have hΛ : circD D.target / circD D.model = 8 := by
    rw [div_eq_iff hD.ne']
    have : circD D.target * Real.sin α44 = 8 * circD D.model * Real.sin α44 := by
      rw [← e16]; linarith
    exact mul_right_cancel₀ hsa.ne' this
  obtain ⟨v1, v2⟩ := val_2a2b D α44_irr hrel hfull ε1 ε2 hε1 hε2 e0 e1 e2
  rw [hΛ] at v1 v2
  have m1 : ((∑ i, ε1 i : ℤ) : ℝ) = 5 := by rw [v1]; norm_num
  have m2 : ((∑ i, ε2 i : ℤ) : ℝ) = -9 := by rw [v2]; norm_num
  refine ⟨D, ε1, ε2, hc, hε1, hε2, by exact_mod_cast m1, by exact_mod_cast m2, ?_⟩
  rw [m1, m2]; norm_num

end Erdos634.BeesonColoring.W77

#print axioms Erdos634.BeesonColoring.W77.lemma28_printed2_at_77
