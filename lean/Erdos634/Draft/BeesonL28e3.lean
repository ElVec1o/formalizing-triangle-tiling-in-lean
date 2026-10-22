import Erdos634.Draft.BeesonL28e2
import Erdos634.Draft.BeesonL28c4

/-!
# Beeson Lemma 28 (printed), unconditional, at the 77-tiling: `M1 = 5`, `M2 = -9` tile by tile

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4), Laczkovich, Beeson-Zhang.  Formalization debt.
For the 77-tiling by `(2,3,4)` (shape `(2 alpha, alpha, 2 beta)`) the printed data `(k_i, n_i, eps_i)` EXIST (no hypothesis,
`exists_printed_unc`), and for ANY such data `sum (-1)^{eps_i} = 5`, `sum (-1)^{n_i+eps_i} = -9`.
-/

open scoped Classical

namespace Erdos634.BeesonColoring.W77

open Erdos634.Geometry Erdos634.Draft.FluxGridWitness Erdos634.Geometry.A1Field

theorem printed_sums_at_77 : ∃ D : CongruentDissection 77,
    ∃ (k : Fin 77 → Fin 3) (n e : Fin 77 → ℤ), (∀ i, (D.tile i).angleAt (k i + 2) = α44) ∧
      (∀ i, ((D.tile i).leftUnit (k i)).angle
        = (D.target.leftUnit 0).angle + (((n i : ℝ) * (α44 + β44) + (e i : ℝ) * Real.pi : ℝ) : Real.Angle)) ∧
      (∀ (k' : Fin 77 → Fin 3) (n' e' : Fin 77 → ℤ), (∀ i, (D.tile i).angleAt (k' i + 2) = α44) →
        (∀ i, ((D.tile i).leftUnit (k' i)).angle
          = (D.target.leftUnit 0).angle + (((n' i : ℝ) * (α44 + β44) + (e' i : ℝ) * Real.pi : ℝ) : Real.Angle)) →
        (∑ i, (-1 : ℝ) ^ (e' i) = 5 ∧ ∑ i, (-1 : ℝ) ^ (n' i + e' i) = -9)) := by
  obtain ⟨D, h, e0, e1, e2, o0, o1, o2⟩ := exists_D77'
  have hrel := three_α_two_β
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
  obtain ⟨ε1, hε1, -⟩ := exists_signs1 D α44_irr hrel hfull
  obtain ⟨ε2, hε2, -⟩ := exists_signs2 D α44_irr hrel hfull
  obtain ⟨v1, v2⟩ := val_2a2b D α44_irr hrel hfull ε1 ε2 hε1 hε2 e0 e1 e2
  rw [hΛ] at v1 v2
  have hδ : ¬ ∃ r : ℚ, α44 + β44 = (r : ℝ) * Real.pi := (delta_irr_iff hrel).mp α44_irr
  obtain ⟨k, n, e, hk, hd⟩ := exists_printed_unc D hδ hrel hfull
  refine ⟨D, k, n, e, hk, hd, fun k' n' e' hk' hd' => ?_⟩
  obtain ⟨s1, s2⟩ := printed_sums D α44_irr hrel hfull ε1 ε2 hε1 hε2 k' n' e' hk' hd'
  rw [← s1, ← s2]
  exact ⟨by rw [v1]; norm_num, by rw [v2]; norm_num⟩

end Erdos634.BeesonColoring.W77

#print axioms Erdos634.BeesonColoring.W77.printed_sums_at_77
