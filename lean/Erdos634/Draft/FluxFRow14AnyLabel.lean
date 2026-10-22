-- Draft/FluxFRow14AnyLabel.lean — Row 14 (`Row14.rational_real`) for EVERY placement of the angles.
-- `Row14.rational_real` fixed the model angles `α, β` at model vertices 0, 1 and the target angles
-- `2α, β` at target vertices 0, 1.  Here: `α, β` at ANY two distinct model vertices `m₀, m₁`, and
-- `2α, β` at ANY two distinct target vertices `t₀, t₁`; conclusion: (side opposite the `α`-vertex)
-- / (side opposite the third model vertex, angle `γ = 2α+β`) is rational.
-- A relabelling wrapper (target via `CongruentDissection.relabelTarget'`, model via
-- `CongruentDissection.relabelModel`): no new mathematics.  Formalization debt, not /goal progress.
import Erdos634.Draft.FluxFRow14Close
import Erdos634.Draft.FluxDRow4AnyLabel

open scoped Classical

namespace Erdos634.Geometry

namespace Row14AnyLabel

private theorem corner_any (T : Tri) (j a b : Fin 3) (ha : a ≠ j) (hb : b ≠ j) (hab : a ≠ b) :
    cornerAngle (T.pts a) (T.pts j) (T.pts b) = T.angleAt j := by
  fin_cases j <;> fin_cases a <;> fin_cases b <;> simp at ha hb hab <;>
    first | rfl | exact EuclideanGeometry.angle_comm (V := Plane) _ _ _

private theorem dist_any (T : Tri) (j a b : Fin 3) (ha : a ≠ j) (hb : b ≠ j) (hab : a ≠ b) :
    dist (T.pts a) (T.pts b) = T.oppLen j := by
  fin_cases j <;> fin_cases a <;> fin_cases b <;> simp at ha hb hab <;>
    first | rfl | exact dist_comm _ _

private theorem succ_ne (k : Fin 3) : k + 1 ≠ k ∧ k + 2 ≠ k ∧ k + 1 ≠ k + 2 := by
  fin_cases k <;> decide

/-- Angles of a relabelled triangle. -/
theorem angleAt_of_pts {T U : Tri} (σ : Equiv.Perm (Fin 3)) (h : ∀ k, U.pts k = T.pts (σ k))
    (k : Fin 3) : U.angleAt k = T.angleAt (σ k) := by
  obtain ⟨h1, h2, h12⟩ := succ_ne k
  simp only [Tri.angleAt, h]
  exact corner_any T _ _ _ (σ.injective.ne h1) (σ.injective.ne h2) (σ.injective.ne h12)

/-- Side lengths of a relabelled triangle. -/
theorem oppLen_of_pts {T U : Tri} (σ : Equiv.Perm (Fin 3)) (h : ∀ k, U.pts k = T.pts (σ k))
    (k : Fin 3) : U.oppLen k = T.oppLen (σ k) := by
  obtain ⟨h1, h2, h12⟩ := succ_ne k
  simp only [Tri.oppLen, h]
  exact dist_any T _ _ _ (σ.injective.ne h1) (σ.injective.ne h2) (σ.injective.ne h12)

theorem exists_perm (i j : Fin 3) (hij : i ≠ j) : ∃ τ : Equiv.Perm (Fin 3), τ 0 = i ∧ τ 1 = j := by
  revert i j; decide

theorem third_eq (τ : Equiv.Perm (Fin 3)) (k : Fin 3) (h0 : k ≠ τ 0) (h1 : k ≠ τ 1) : τ 2 = k := by
  have h02 : τ 2 ≠ τ 0 := τ.injective.ne (by decide)
  have h12 : τ 2 ≠ τ 1 := τ.injective.ne (by decide)
  have h01 : τ 0 ≠ τ 1 := τ.injective.ne (by decide)
  revert h0 h1 h02 h12 h01
  generalize τ 0 = x; generalize τ 1 = y; generalize τ 2 = z
  revert x y z k; decide

end Row14AnyLabel

open Row14AnyLabel in
/-- **Row 14, any labelling.**  `α ∉ ℚπ`, `3α + 2β = π`; model angles `α, β` at any two distinct
model vertices `m₀, m₁` (`m₂` the third); target angles `2α, β` at any two distinct target vertices.
Then (side opposite `α`) / (side opposite `γ = 2α+β`) is rational. -/
theorem Row14.rational_any_label {N : ℕ} (D : CongruentDissection N) (α β : ℝ)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    {m₀ m₁ m₂ : Fin 3} (hm01 : m₀ ≠ m₁) (hm20 : m₂ ≠ m₀) (hm21 : m₂ ≠ m₁)
    (hm0 : D.model.angleAt m₀ = α) (hm1 : D.model.angleAt m₁ = β)
    {t₀ t₁ : Fin 3} (ht01 : t₀ ≠ t₁)
    (hP0 : D.target.angleAt t₀ = 2 * α) (hP1 : D.target.angleAt t₁ = β) :
    ∃ r : ℚ, D.model.oppLen m₀ = (r : ℝ) * D.model.oppLen m₂ := by
  obtain ⟨τ, hτ0, hτ1⟩ := exists_perm m₀ m₁ hm01
  obtain ⟨σ, hσ0, hσ1⟩ := exists_perm t₀ t₁ ht01
  have hτ2 : τ 2 = m₂ := third_eq τ m₂ (hτ0 ▸ hm20) (hτ1 ▸ hm21)
  set D' := (D.relabelTarget' σ).relabelModel τ
  have hM : ∀ k, D'.model.pts k = D.model.pts (τ k) := fun k => rfl
  have hT : ∀ k, D'.target.pts k = D.target.pts (σ k) := fun k => rfl
  obtain ⟨r, hr⟩ := Row14.rational_real D' α β hirr hrel
    (by rw [angleAt_of_pts τ hM, hτ0, hm0]) (by rw [angleAt_of_pts τ hM, hτ1, hm1])
    (by rw [angleAt_of_pts σ hT, hσ0, hP0]) (by rw [angleAt_of_pts σ hT, hσ1, hP1])
  refine ⟨r, ?_⟩
  rw [oppLen_of_pts τ hM, oppLen_of_pts τ hM, hτ0, hτ2] at hr
  exact hr

/-- Consistency check of the relabel lemmas on a concrete permutation (non-vacuity of
`exists_perm`/`third_eq`'s hypotheses): the swap `(0 1)` sends `0 ↦ 1, 1 ↦ 0`, third vertex `2`. -/
example : ∃ τ : Equiv.Perm (Fin 3), τ 0 = 1 ∧ τ 1 = 0 ∧ τ 2 = 2 :=
  ⟨Equiv.swap 0 1, by decide, by decide, by decide⟩

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row14.rational_any_label
