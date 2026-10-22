-- Draft/Rows11_13AnyLabel.lean — rows 11, 12, 13 of Theorem RAT for EVERY labelling of the target.
-- `Row11.rational`, `Row12.rational`, `Row13.rational`, `Row11.prime_excluded` fix the two equal
-- (base) target angles at target vertices 0, 1; the model is already label-free (`Tri.ThreeAlphaData`
-- quantifies a vertex permutation).  Here: base angles at ANY two distinct target vertices `t₀, t₁`,
-- and the written consequence `b = (1 − s²)c` is exported with `s = a/c ∈ ℚ`.
-- Relabelling wrapper (target via `CongruentDissection.relabelTarget'`, lemmas of Row14AnyLabel) plus
-- one tile-only law-of-sines identity `b·c = c² − a²`.  No new mathematics.
-- Statement-match audit: (private working notes, not included)
-- Formalization debt, not /goal progress.
import Erdos634.Draft.FluxDRow11Prime
import Erdos634.Draft.FluxDRow12a
import Erdos634.Draft.FluxDRow13
import Erdos634.Draft.FluxFRow14AnyLabel
import Erdos634.Draft.FluxCRow12Witness

open scoped Classical

namespace Erdos634.Geometry

namespace Rows11_13AnyLabel

/-- **Tile-only identity** for the `3α + 2β = π` tile: `b·c = c² − a²`, i.e. `b = (1 − s²)c`. -/
theorem threeAlpha_b_eq {T : Tri} {α β a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (h : T.ThreeAlphaData α β a b c) : b * c = c ^ 2 - a ^ 2 := by
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  obtain ⟨tγ, tα, tβ, -⟩ := threeAlpha_sin_table hrel
  have ls1 := T.lawSin (σ 0) (σ 2)
  have ls2 := T.lawSin (σ 1) (σ 2)
  rw [h0, o2, h2, o0, tα, tγ] at ls1
  rw [h1, o2, h2, o1, tβ, tγ] at ls2
  have hαpos : 0 < α := h0 ▸ T.angleAt_pos' (σ 0)
  have hβpos : 0 < β := h1 ▸ T.angleAt_pos' (σ 1)
  have hπ := Real.pi_pos
  have hco : 0 < Real.cos (α / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  set u := Real.sin (α / 2)
  have ha : a = 2 * u * c :=
    mul_left_cancel₀ hco.ne' (by linear_combination (-1 : ℝ) * ls1)
  have hb : b = (1 - 4 * u ^ 2) * c :=
    mul_left_cancel₀ hco.ne' (by linear_combination (-1 : ℝ) * ls2)
  rw [ha, hb]; ring

theorem b_of_rational {T : Tri} {α β a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (h : T.ThreeAlphaData α β a b c) {r : ℚ} (hr : a = (r : ℝ) * c) :
    b = (1 - (r : ℝ) ^ 2) * c := by
  have hc : 0 < c := by obtain ⟨σ, -, -, -, -, -, o2⟩ := h; exact o2 ▸ T.oppLen_pos (σ 2)
  have e := threeAlpha_b_eq hrel h
  rw [hr] at e
  exact mul_right_cancel₀ hc.ne' (by linear_combination e)

/-- Transport target-angle hypotheses at `t₀ ≠ t₁` to vertices `0, 1` of a relabelled dissection. -/
theorem transport {N : ℕ} (D : CongruentDissection N) {t₀ t₁ : Fin 3} (ht : t₀ ≠ t₁) (x : ℝ)
    (h0 : D.target.angleAt t₀ = x) (h1 : D.target.angleAt t₁ = x) :
    ∃ σ : Equiv.Perm (Fin 3), (D.relabelTarget' σ).model = D.model ∧
      (D.relabelTarget' σ).target.angleAt 0 = x ∧ (D.relabelTarget' σ).target.angleAt 1 = x := by
  obtain ⟨σ, hσ0, hσ1⟩ := Row14AnyLabel.exists_perm t₀ t₁ ht
  have hT : ∀ k, (D.relabelTarget' σ).target.pts k = D.target.pts (σ k) := fun k => rfl
  exact ⟨σ, rfl, by rw [Row14AnyLabel.angleAt_of_pts σ hT, hσ0, h0],
    by rw [Row14AnyLabel.angleAt_of_pts σ hT, hσ1, h1]⟩

end Rows11_13AnyLabel

open Rows11_13AnyLabel

/-- **Row 11 (R11), any labelling**: base-α target `(α, α, α+2β)`, base angles at any two distinct
target vertices; any `N`: `a = s c`, `b = (1 − s²) c`, `s ∈ ℚ`. -/
theorem Row11.rational_any_label {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) {t₀ t₁ : Fin 3} (ht : t₀ ≠ t₁)
    (hP0 : D.target.angleAt t₀ = α) (hP1 : D.target.angleAt t₁ = α) :
    ∃ r : ℚ, a = (r : ℝ) * c ∧ b = (1 - (r : ℝ) ^ 2) * c := by
  obtain ⟨σ, hm, h0, h1⟩ := transport D ht α hP0 hP1
  obtain ⟨r, hr⟩ := Row11.rational (D.relabelTarget' σ) hα hrel (hm ▸ h) h0 h1
  exact ⟨r, hr, b_of_rational hrel h hr⟩

/-- **Row 11 at prime `N` (R15's conclusion via R11 + prop:isoalphaprime), any labelling.** -/
theorem Row11.prime_excluded_any_label {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) {t₀ t₁ : Fin 3} (ht : t₀ ≠ t₁)
    (hP0 : D.target.angleAt t₀ = α) (hP1 : D.target.angleAt t₁ = α) (hN : N.Prime) : False := by
  obtain ⟨σ, hm, h0, h1⟩ := transport D ht α hP0 hP1
  exact Row11.prime_excluded (D.relabelTarget' σ) hα hrel (hm ▸ h) h0 h1 hN

/-- **Row 12 (R12 / 12(b)), any labelling**: base-β target `(β, β, 3α)`; any `N`. -/
theorem Row12.rational_any_label {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) {t₀ t₁ : Fin 3} (ht : t₀ ≠ t₁)
    (hP0 : D.target.angleAt t₀ = β) (hP1 : D.target.angleAt t₁ = β) :
    ∃ r : ℚ, a = (r : ℝ) * c ∧ b = (1 - (r : ℝ) ^ 2) * c := by
  obtain ⟨σ, hm, h0, h1⟩ := transport D ht β hP0 hP1
  obtain ⟨r, hr⟩ := Row12.rational (D.relabelTarget' σ) hα hrel (hm ▸ h) h0 h1
  exact ⟨r, hr, b_of_rational hrel h hr⟩

/-- **Row 13, any labelling**: base-(α+β) target `(α+β, α+β, α)`; any `N`. -/
theorem Row13.rational_any_label {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) {t₀ t₁ : Fin 3} (ht : t₀ ≠ t₁)
    (hP0 : D.target.angleAt t₀ = α + β) (hP1 : D.target.angleAt t₁ = α + β) :
    ∃ r : ℚ, a = (r : ℝ) * c ∧ b = (1 - (r : ℝ) ^ 2) * c := by
  obtain ⟨σ, hm, h0, h1⟩ := transport D ht (α + β) hP0 hP1
  obtain ⟨-, -, -, -, -, r, hr⟩ := Row13.rational (D.relabelTarget' σ) hα hrel (hm ▸ h) h0 h1
  exact ⟨r, hr, b_of_rational hrel h hr⟩

end Erdos634.Geometry

/-- Non-vacuity on a real tiling: `Row12.rational_any_label` applied to the certified 44-tiling
(`Tiling44Bridge.dissection`, base angles at target vertices 0, 1, tile `(16, 24, 32)`). -/
example : ∃ r : ℚ, (16 : ℝ) = (r : ℝ) * 32 ∧ (24 : ℝ) = (1 - (r : ℝ) ^ 2) * 32 := by
  obtain ⟨r, hr, hb⟩ := Erdos634.Geometry.Row12.rational_any_label
    Erdos634.Tiling44Bridge.dissection Erdos634.Draft.FluxGridWitness.α44_irr
    Erdos634.Draft.FluxGridWitness.three_α_two_β Erdos634.Draft.FluxRow11Witness.data44
    (show (0 : Fin 3) ≠ 1 by decide)
    Erdos634.Draft.FluxGridWitness.t_angle0 Erdos634.Draft.FluxGridWitness.t_angle1
  exact ⟨r, hr, hb⟩

#print axioms Erdos634.Geometry.Rows11_13AnyLabel.threeAlpha_b_eq
#print axioms Erdos634.Geometry.Row11.rational_any_label
#print axioms Erdos634.Geometry.Row11.prime_excluded_any_label
#print axioms Erdos634.Geometry.Row12.rational_any_label
#print axioms Erdos634.Geometry.Row13.rational_any_label
