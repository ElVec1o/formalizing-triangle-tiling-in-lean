-- Draft/FluxFRow15AnyLabel.lean — Row 15 (`Row15.rational_real`) for EVERY placement of the angles.
-- `Row15.rational_real` fixed model angles `α, β` at model vertices 0, 1 and target angles `2α, α`
-- at target vertices 0, 1.  Here: `α, β` at ANY two distinct model vertices `m₀, m₁` (`m₂` the
-- third, angle `γ = 2α+β`), and `2α, α` at ANY two distinct target vertices `t₀, t₁`.
-- Conclusion: (side opposite α) = r·(side opposite γ), (side opposite β) = (1 − r²)·(side opp. γ),
-- r ∈ ℚ.  Relabelling wrapper reusing `CongruentDissection.relabelTarget'`,
-- `CongruentDissection.relabelModel` and `Row14AnyLabel.{angleAt_of_pts, oppLen_of_pts,
-- exists_perm, third_eq}`: no new mathematics.  Formalization debt, not /goal progress.
import Erdos634.Draft.FluxFRow15Close
import Erdos634.Draft.FluxFRow14AnyLabel

open scoped Classical

namespace Erdos634.Geometry

open Row14AnyLabel in
/-- **Row 15, any labelling.** -/
theorem Row15.rational_any_label {N : ℕ} (D : CongruentDissection N) (α β : ℝ)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    {m₀ m₁ m₂ : Fin 3} (hm01 : m₀ ≠ m₁) (hm20 : m₂ ≠ m₀) (hm21 : m₂ ≠ m₁)
    (hm0 : D.model.angleAt m₀ = α) (hm1 : D.model.angleAt m₁ = β)
    {t₀ t₁ : Fin 3} (ht01 : t₀ ≠ t₁)
    (hP0 : D.target.angleAt t₀ = 2 * α) (hP1 : D.target.angleAt t₁ = α) :
    ∃ r : ℚ, D.model.oppLen m₀ = (r : ℝ) * D.model.oppLen m₂ ∧
      D.model.oppLen m₁ = (1 - (r : ℝ) ^ 2) * D.model.oppLen m₂ := by
  obtain ⟨τ, hτ0, hτ1⟩ := exists_perm m₀ m₁ hm01
  obtain ⟨σ, hσ0, hσ1⟩ := exists_perm t₀ t₁ ht01
  have hτ2 : τ 2 = m₂ := third_eq τ m₂ (hτ0 ▸ hm20) (hτ1 ▸ hm21)
  set D' := (D.relabelTarget' σ).relabelModel τ
  have hM : ∀ k, D'.model.pts k = D.model.pts (τ k) := fun k => rfl
  have hT : ∀ k, D'.target.pts k = D.target.pts (σ k) := fun k => rfl
  obtain ⟨r, hr1, hr2⟩ := Row15.rational_real D' α β hirr hrel
    (by rw [angleAt_of_pts τ hM, hτ0, hm0]) (by rw [angleAt_of_pts τ hM, hτ1, hm1])
    (by rw [angleAt_of_pts σ hT, hσ0, hP0]) (by rw [angleAt_of_pts σ hT, hσ1, hP1])
  rw [oppLen_of_pts τ hM, oppLen_of_pts τ hM, hτ0, hτ2] at hr1
  rw [oppLen_of_pts τ hM, oppLen_of_pts τ hM, hτ1, hτ2] at hr2
  exact ⟨r, hr1, hr2⟩

/-- Non-vacuity of the labelling hypotheses: the 3-cycle-free instance `m = (1, 2, 0)`,
`t = (2, 0)` has all distinctness hypotheses true. -/
example : (1 : Fin 3) ≠ 2 ∧ (0 : Fin 3) ≠ 1 ∧ (0 : Fin 3) ≠ 2 ∧ (2 : Fin 3) ≠ 0 := by decide

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row15.rational_any_label
