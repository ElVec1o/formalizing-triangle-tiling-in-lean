import Erdos634.Draft.BeesonL28c1

/-!
# Beeson (arXiv 1206.2229v4) Lemma 28, step 2: Theorem 4 for the printed `M1, M2` (sums of tile signs)

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Thm 4, Lemmas 23, 24), Laczkovich (DCG 48 (2012)),
Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.

For each printed shape (angles listed at `A, B, C` = target vertices `0, 1, 2`) and signs `eps^1`, `eps^2` of the tile
fluxes of `Phi_1`, `Phi_2` anchored at `AB` (`SignsFor`), `M1 = sum eps^1`, `M2 = sum eps^2` equal the printed Theorem 4
values `Lambda * poly(s)`.  No existential: `M1, M2` are the sums themselves.  Hypothesis (H1) `alpha notin Q pi`
replaces Beeson's Lemma 1 (as in `t4_final`).
-/

open scoped Classical

namespace Erdos634.BeesonColoring

open Erdos634.Geometry Erdos634.Geometry.A1Field

variable {N : ℕ}

theorem ctx (D : CongruentDissection N) {α β a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ 0 < c ∧ a = s * c ∧ b = (1 - s ^ 2) * c ∧
      (∀ (k : Fin 3) (x : ℝ), Real.sin (D.target.angleAt k) = x * Real.sin (α + β) →
        D.target.oppLen k = (circD D.target / circD D.model) * c * x) ∧
      Real.sin α = s * Real.sin (α + β) ∧ Real.sin β = (1 - s ^ 2) * Real.sin (α + β) ∧
      Real.sin (2 * α) = s * (2 - s ^ 2) * Real.sin (α + β) ∧
      Real.sin (α + 2 * β) = s * (2 - s ^ 2) * Real.sin (α + β) ∧
      Real.sin (3 * α) = s * (1 - s ^ 2) * (3 - s ^ 2) * Real.sin (α + β) ∧
      Real.sin (2 * β) = s * (1 - s ^ 2) * (3 - s ^ 2) * Real.sin (α + β) := by
  obtain ⟨ha, hb, hc, hαpos, hβpos⟩ := model_abc_pos h
  obtain ⟨s, hs0, hs1, sA, sB, sG, s2A, sAB, s3A, s2B⟩ := sin_table hrel hαpos hβpos
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  have ea : a = circD D.model * Real.sin α := by rw [← o0, oppLen_eq, h0]
  have eb : b = circD D.model * Real.sin β := by rw [← o1, oppLen_eq, h1]
  have ec : c = circD D.model * Real.sin (α + β) := by rw [← o2, oppLen_eq, h2, sG]
  have hD : 0 < circD D.model := circD_pos _
  have hsδ : 0 < Real.sin (α + β) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hsa : a / c = s := by rw [ea, ec, sA]; field_simp
  have hcs : a = s * c := by rw [← hsa]; field_simp
  have hbs : b = (1 - s ^ 2) * c := by rw [eb, ec, sB]; ring
  have hDt : circD D.target = (circD D.target / circD D.model) * circD D.model := by field_simp
  refine ⟨s, hs0, hs1, hc, hcs, hbs, ?_, sA, sB, s2A, sAB, s3A, s2B⟩
  intro k x hx
  rw [oppLen_eq, hx, ec]; field_simp

/-- Theorem 4, shape `(2 alpha, beta, alpha+beta)`: `M1 = M2 = Lambda s`. -/
theorem val_tri (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) (ε1 ε2 : Fin N → ℤ)
    (hε1 : SignsFor D (Phi1 D α hα) ε1) (hε2 : SignsFor D (Phi2 D α hα) ε2)
    (e0 : D.target.angleAt 0 = 2 * α) (e1 : D.target.angleAt 1 = β)
    (e2 : D.target.angleAt 2 = α + β) :
    ((∑ i, ε1 i : ℤ) : ℝ) = (circD D.target / circD D.model) * (a / c) ∧
    ((∑ i, ε2 i : ℤ) : ℝ) = (circD D.target / circD D.model) * (a / c) := by
  obtain ⟨s, hs0, hs1, hc, has, hbs, side, sA, sB, s2A, sAB, s3A, s2B⟩ := ctx D hrel h
  have hsa : a / c = s := by rw [has]; field_simp
  rw [hsa]
  have k1 := phi1_sum D hα hrel h 2 0 0 1 1 1 (by rw [e0]; push_cast; ring) (by rw [e1]; push_cast; ring)
    (by rw [e2]; push_cast; ring) ε1 hε1
  have k2 := phi2_sum D hα hrel h 2 0 0 1 1 1 (by rw [e0]; push_cast; ring) (by rw [e1]; push_cast; ring)
    (by rw [e2]; push_cast; ring) ε2 hε2
  simp only [sg_20, sg_01, sg_11, sg0_0, sg0_1, sg0_2] at k1 k2
  rw [side 0 (s * (2 - s ^ 2)) (by rw [e0, s2A]), side 1 (1 - s ^ 2) (by rw [e1, sB]),
    side 2 1 (by rw [e2, one_mul])] at k1 k2
  have hK1 : c * ((2 - s) * (1 + s)) ≠ 0 := mul_ne_zero hc.ne' (mul_ne_zero (by linarith) (by linarith))
  have hK2 : c * ((2 + s) * (1 - s)) ≠ 0 := mul_ne_zero hc.ne' (mul_ne_zero (by linarith) (by linarith))
  have hsum : a + b + c = c * ((2 - s) * (1 + s)) := by rw [has, hbs]; ring
  have hdif : a - b - c = -(c * ((2 + s) * (1 - s))) := by rw [has, hbs]; ring
  constructor
  · refine mul_right_cancel₀ hK1 ?_
    rw [hsum] at k1; rw [k1]; ring
  · refine mul_right_cancel₀ hK2 ?_
    rw [hdif] at k2; linear_combination (-1 : ℝ) * k2


/-- Theorem 4, shape `(beta, 3 alpha, beta)`: `M1 = Lambda (1-s)(1+s)^2`, `M2 = -Lambda (1-s)^2 (1+s)`. -/
theorem val_beta3 (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) (ε1 ε2 : Fin N → ℤ)
    (hε1 : SignsFor D (Phi1 D α hα) ε1) (hε2 : SignsFor D (Phi2 D α hα) ε2)
    (e0 : D.target.angleAt 0 = β) (e1 : D.target.angleAt 1 = 3 * α)
    (e2 : D.target.angleAt 2 = β) :
    ((∑ i, ε1 i : ℤ) : ℝ) = (circD D.target / circD D.model) * ((1 - (a / c)) * (1 + (a / c)) ^ 2) ∧
    ((∑ i, ε2 i : ℤ) : ℝ) = -((circD D.target / circD D.model) * ((1 - (a / c)) ^ 2 * (1 + (a / c)))) := by
  obtain ⟨s, hs0, hs1, hc, has, hbs, side, sA, sB, s2A, sAB, s3A, s2B⟩ := ctx D hrel h
  have hsa : a / c = s := by rw [has]; field_simp
  rw [hsa]
  have k1 := phi1_sum D hα hrel h 0 1 3 0 0 1 (by rw [e0]; push_cast; ring)
    (by rw [e1]; push_cast; ring) (by rw [e2]; push_cast; ring) ε1 hε1
  have k2 := phi2_sum D hα hrel h 0 1 3 0 0 1 (by rw [e0]; push_cast; ring)
    (by rw [e1]; push_cast; ring) (by rw [e2]; push_cast; ring) ε2 hε2
  simp only [sg_01, sg_30, sg0_0, sg0_3] at k1 k2
  rw [side 0 (1 - s ^ 2) (by rw [e0, sB]), side 1 (s * (1 - s ^ 2) * (3 - s ^ 2)) (by rw [e1, s3A]),
    side 2 (1 - s ^ 2) (by rw [e2, sB])] at k1 k2
  have hsum : a + b + c = c * ((2 - s) * (1 + s)) := by rw [has, hbs]; ring
  have hdif : a - b - c = -(c * ((2 + s) * (1 - s))) := by rw [has, hbs]; ring
  have hK1 : a + b + c ≠ 0 := by
    rw [hsum]; exact mul_ne_zero hc.ne' (mul_ne_zero (by linarith) (by linarith))
  have hK2 : a - b - c ≠ 0 := by
    rw [hdif]; exact neg_ne_zero.mpr (mul_ne_zero hc.ne' (mul_ne_zero (by linarith) (by linarith)))
  have n1 : (1 - s) ≠ 0 := by linarith
  have n2 : (1 + s) ≠ 0 := by linarith
  have n3 : (2 - s) ≠ 0 := by linarith
  have n4 : (2 + s) ≠ 0 := by linarith
  have n5 : c ≠ 0 := hc.ne'
  constructor
  · refine mul_right_cancel₀ hK1 ?_
    rw [k1, hsum]; field_simp; ring
  · refine mul_right_cancel₀ hK2 ?_
    rw [k2, hdif]; field_simp; ring

/-- Theorem 4, shape `(alpha+beta, alpha, alpha+beta)`: `M1 = Lambda/(1+s)`, `M2 = -Lambda/(1-s)`. -/
theorem val_apb (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) (ε1 ε2 : Fin N → ℤ)
    (hε1 : SignsFor D (Phi1 D α hα) ε1) (hε2 : SignsFor D (Phi2 D α hα) ε2)
    (e0 : D.target.angleAt 0 = α + β) (e1 : D.target.angleAt 1 = α)
    (e2 : D.target.angleAt 2 = α + β) :
    ((∑ i, ε1 i : ℤ) : ℝ) = (circD D.target / circD D.model) * (1 / (1 + (a / c))) ∧
    ((∑ i, ε2 i : ℤ) : ℝ) = -((circD D.target / circD D.model) * (1 / (1 - (a / c)))) := by
  obtain ⟨s, hs0, hs1, hc, has, hbs, side, sA, sB, s2A, sAB, s3A, s2B⟩ := ctx D hrel h
  have hsa : a / c = s := by rw [has]; field_simp
  rw [hsa]
  have k1 := phi1_sum D hα hrel h 1 1 1 0 1 1 (by rw [e0]; push_cast; ring)
    (by rw [e1]; push_cast; ring) (by rw [e2]; push_cast; ring) ε1 hε1
  have k2 := phi2_sum D hα hrel h 1 1 1 0 1 1 (by rw [e0]; push_cast; ring)
    (by rw [e1]; push_cast; ring) (by rw [e2]; push_cast; ring) ε2 hε2
  simp only [sg_11, sg_10, sg0_1] at k1 k2
  rw [side 0 1 (by rw [e0, one_mul]), side 1 s (by rw [e1, sA]),
    side 2 1 (by rw [e2, one_mul])] at k1 k2
  have hsum : a + b + c = c * ((2 - s) * (1 + s)) := by rw [has, hbs]; ring
  have hdif : a - b - c = -(c * ((2 + s) * (1 - s))) := by rw [has, hbs]; ring
  have hK1 : a + b + c ≠ 0 := by
    rw [hsum]; exact mul_ne_zero hc.ne' (mul_ne_zero (by linarith) (by linarith))
  have hK2 : a - b - c ≠ 0 := by
    rw [hdif]; exact neg_ne_zero.mpr (mul_ne_zero hc.ne' (mul_ne_zero (by linarith) (by linarith)))
  have n1 : (1 - s) ≠ 0 := by linarith
  have n2 : (1 + s) ≠ 0 := by linarith
  have n3 : (2 - s) ≠ 0 := by linarith
  have n4 : (2 + s) ≠ 0 := by linarith
  have n5 : c ≠ 0 := hc.ne'
  constructor
  · refine mul_right_cancel₀ hK1 ?_
    rw [k1, hsum]; field_simp; ring
  · refine mul_right_cancel₀ hK2 ?_
    rw [k2, hdif]; field_simp; ring

/-- Theorem 4, shape `(alpha, alpha+2beta, alpha)`: `M1 = Lambda s(2+s)/(1+s)`, `M2 = -Lambda s(2-s)/(1-s)`. -/
theorem val_a2b (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) (ε1 ε2 : Fin N → ℤ)
    (hε1 : SignsFor D (Phi1 D α hα) ε1) (hε2 : SignsFor D (Phi2 D α hα) ε2)
    (e0 : D.target.angleAt 0 = α) (e1 : D.target.angleAt 1 = α + 2 * β)
    (e2 : D.target.angleAt 2 = α) :
    ((∑ i, ε1 i : ℤ) : ℝ) = (circD D.target / circD D.model) * ((a / c) * (2 + (a / c)) / (1 + (a / c))) ∧
    ((∑ i, ε2 i : ℤ) : ℝ) = -((circD D.target / circD D.model) * ((a / c) * (2 - (a / c)) / (1 - (a / c)))) := by
  obtain ⟨s, hs0, hs1, hc, has, hbs, side, sA, sB, s2A, sAB, s3A, s2B⟩ := ctx D hrel h
  have hsa : a / c = s := by rw [has]; field_simp
  rw [hsa]
  have k1 := phi1_sum D hα hrel h 1 0 1 2 1 0 (by rw [e0]; push_cast; ring)
    (by rw [e1]; push_cast; ring) (by rw [e2]; push_cast; ring) ε1 hε1
  have k2 := phi2_sum D hα hrel h 1 0 1 2 1 0 (by rw [e0]; push_cast; ring)
    (by rw [e1]; push_cast; ring) (by rw [e2]; push_cast; ring) ε2 hε2
  simp only [sg_10, sg_12, sg0_1] at k1 k2
  rw [side 0 s (by rw [e0, sA]), side 1 (s * (2 - s ^ 2)) (by rw [e1, sAB]),
    side 2 s (by rw [e2, sA])] at k1 k2
  have hsum : a + b + c = c * ((2 - s) * (1 + s)) := by rw [has, hbs]; ring
  have hdif : a - b - c = -(c * ((2 + s) * (1 - s))) := by rw [has, hbs]; ring
  have hK1 : a + b + c ≠ 0 := by
    rw [hsum]; exact mul_ne_zero hc.ne' (mul_ne_zero (by linarith) (by linarith))
  have hK2 : a - b - c ≠ 0 := by
    rw [hdif]; exact neg_ne_zero.mpr (mul_ne_zero hc.ne' (mul_ne_zero (by linarith) (by linarith)))
  have n1 : (1 - s) ≠ 0 := by linarith
  have n2 : (1 + s) ≠ 0 := by linarith
  have n3 : (2 - s) ≠ 0 := by linarith
  have n4 : (2 + s) ≠ 0 := by linarith
  have n5 : c ≠ 0 := hc.ne'
  constructor
  · refine mul_right_cancel₀ hK1 ?_
    rw [k1, hsum]; field_simp; ring
  · refine mul_right_cancel₀ hK2 ?_
    rw [k2, hdif]; field_simp; ring

/-- Theorem 4, shape `(2alpha, alpha, 2beta)`: `M1 = Lambda s(1-s)(2+s)`, `M2 = -Lambda s(2-s)(1+s)`. -/
theorem val_2a2b (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) (ε1 ε2 : Fin N → ℤ)
    (hε1 : SignsFor D (Phi1 D α hα) ε1) (hε2 : SignsFor D (Phi2 D α hα) ε2)
    (e0 : D.target.angleAt 0 = 2 * α) (e1 : D.target.angleAt 1 = α)
    (e2 : D.target.angleAt 2 = 2 * β) :
    ((∑ i, ε1 i : ℤ) : ℝ) = (circD D.target / circD D.model) * ((a / c) * (1 - (a / c)) * (2 + (a / c))) ∧
    ((∑ i, ε2 i : ℤ) : ℝ) = -((circD D.target / circD D.model) * ((a / c) * (2 - (a / c)) * (1 + (a / c)))) := by
  obtain ⟨s, hs0, hs1, hc, has, hbs, side, sA, sB, s2A, sAB, s3A, s2B⟩ := ctx D hrel h
  have hsa : a / c = s := by rw [has]; field_simp
  rw [hsa]
  have k1 := phi1_sum D hα hrel h 2 0 1 0 0 2 (by rw [e0]; push_cast; ring)
    (by rw [e1]; push_cast; ring) (by rw [e2]; push_cast; ring) ε1 hε1
  have k2 := phi2_sum D hα hrel h 2 0 1 0 0 2 (by rw [e0]; push_cast; ring)
    (by rw [e1]; push_cast; ring) (by rw [e2]; push_cast; ring) ε2 hε2
  simp only [sg_20, sg_10, sg_02, sg0_2, sg0_1, sg0_0] at k1 k2
  rw [side 0 (s * (2 - s ^ 2)) (by rw [e0, s2A]), side 1 s (by rw [e1, sA]),
    side 2 (s * (1 - s ^ 2) * (3 - s ^ 2)) (by rw [e2, s2B])] at k1 k2
  have hsum : a + b + c = c * ((2 - s) * (1 + s)) := by rw [has, hbs]; ring
  have hdif : a - b - c = -(c * ((2 + s) * (1 - s))) := by rw [has, hbs]; ring
  have hK1 : a + b + c ≠ 0 := by
    rw [hsum]; exact mul_ne_zero hc.ne' (mul_ne_zero (by linarith) (by linarith))
  have hK2 : a - b - c ≠ 0 := by
    rw [hdif]; exact neg_ne_zero.mpr (mul_ne_zero hc.ne' (mul_ne_zero (by linarith) (by linarith)))
  have n1 : (1 - s) ≠ 0 := by linarith
  have n2 : (1 + s) ≠ 0 := by linarith
  have n3 : (2 - s) ≠ 0 := by linarith
  have n4 : (2 + s) ≠ 0 := by linarith
  have n5 : c ≠ 0 := hc.ne'
  constructor
  · refine mul_right_cancel₀ hK1 ?_
    rw [k1, hsum]; field_simp; ring
  · refine mul_right_cancel₀ hK2 ?_
    rw [k2, hdif]; field_simp; ring

end Erdos634.BeesonColoring

#print axioms Erdos634.BeesonColoring.val_tri
#print axioms Erdos634.BeesonColoring.val_beta3
#print axioms Erdos634.BeesonColoring.val_apb
#print axioms Erdos634.BeesonColoring.val_a2b
#print axioms Erdos634.BeesonColoring.val_2a2b
