import Erdos634.Draft.BeesonT4M1
import Erdos634.Draft.FluxDRow11
import Erdos634.Draft.FluxCRow12
import Erdos634.Draft.FluxDRow13

/-!
# Beeson (arXiv 1206.2229v4) Theorem 4 (`M2` column, three rows) and Theorem 5

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Thms 3, 4, 5), Laczkovich (DCG 48 (2012)), Beeson-Zhang.
Formalization debt, not progress on the /goal outcomes.

Printed Theorem 4 (rows with `M1, M2`), Theorem 5: `(beta, 3alpha, beta)` and `(alpha+beta, alpha, alpha+beta)`: the tile
is rational, `s = (M1 + M2)/(M1 - M2)` resp. `s = (M1 + M2)/(M2 - M1)`.  Formalized here for the three isosceles rows,
`M1` as `t4_M1` and `M2` from the second flux integer `K` of `Row11.boundary_baseAlpha`, `Row12.flux_identities`,
`Row13.boundary` (the same flux layer; project `K` equals Beeson `M2` for `(beta,3alpha,beta)`, and Beeson `M2 = -K`
for `(alpha,alpha+2beta,alpha)` and `(alpha+beta,alpha,alpha+beta)`; checked against the printed table, which the
statements below reproduce).  Here `Lambda = circD target / circD model`, `s = a/c`.
NOT formalized: `M2` for `(2alpha,alpha,2beta)` and `(2alpha,beta,alpha+beta)` (`Row15.setup`, `Row14.setup` discard
the second flux integer); Theorem 6.
Project hypothesis (H1) `alpha not in Q * pi` replaces Beeson's Lemma 1 (Laczkovich 5.1, 5.3; not in Lean).
Vertex order as in `thm1`.
-/

open scoped Classical

namespace Erdos634.BeesonColoring

open Erdos634.Geometry

variable {N : ℕ}

open Erdos634.Geometry.A1Field in
theorem t4_M2_T5 (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) :
    ((D.target.angleAt 0 = α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + 2 * β) →
      ∃ M1 M2 : ℤ, (M1 : ℝ) = (circD D.target / circD D.model) * ((a / c) * (2 + a / c) / (1 + a / c)) ∧
        (M2 : ℝ) = -((circD D.target / circD D.model) * ((a / c) * (2 - a / c) / (1 - a / c)))) ∧
    ((D.target.angleAt 0 = β ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = 3 * α) →
      ∃ M1 M2 : ℤ, (M1 : ℝ) = (circD D.target / circD D.model) * ((1 - a / c) * (1 + a / c) ^ 2) ∧
        (M2 : ℝ) = -((circD D.target / circD D.model) * ((1 - a / c) ^ 2 * (1 + a / c))) ∧
        a / c = ((M1 : ℝ) + M2) / ((M1 : ℝ) - M2) ∧ ∃ q : ℚ, a / c = (q : ℝ)) ∧
    ((D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α + β ∧ D.target.angleAt 2 = α) →
      ∃ M1 M2 : ℤ, (M1 : ℝ) = (circD D.target / circD D.model) * (1 / (1 + a / c)) ∧
        (M2 : ℝ) = -((circD D.target / circD D.model) * (1 / (1 - a / c))) ∧
        a / c = ((M1 : ℝ) + M2) / ((M2 : ℝ) - M1) ∧ ∃ q : ℚ, a / c = (q : ℝ)) := by
  obtain ⟨ha, hb, hc, hαpos, hβpos⟩ := model_abc_pos h
  obtain ⟨s, hs0, hs1, sA, sB, sG, s2A, sAB, s3A, s2B⟩ := sin_table hrel hαpos hβpos
  have hsδ : 0 < Real.sin (α + β) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  -- model sides from the law of sines
  have hfull := h
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  have ea : a = circD D.model * Real.sin α := by rw [← o0, oppLen_eq, h0]
  have eb : b = circD D.model * Real.sin β := by rw [← o1, oppLen_eq, h1]
  have ec : c = circD D.model * Real.sin (α + β) := by rw [← o2, oppLen_eq, h2, sG]
  have hD : 0 < circD D.model := circD_pos _
  have hDne := hD.ne'
  have hsδne := hsδ.ne'
  have hsa : a / c = s := by rw [ea, ec, sA]; field_simp
  have hcs : a = s * c := by rw [← hsa]; field_simp
  have hbs : b = (1 - s ^ 2) * c := by rw [eb, ec, sB]; ring
  have hDt : circD D.target = (circD D.target / circD D.model) * circD D.model := by field_simp
  set Λ := circD D.target / circD D.model with hΛ
  have hsum : a + b + c = c * ((2 - s) * (1 + s)) := by rw [hcs, hbs]; ring
  have hpos : 0 < c * ((2 - s) * (1 + s)) := mul_pos hc (mul_pos (by linarith) (by linarith))
  -- target sides: X_k = Λ * c * (poly) given the angle
  have side : ∀ (k : Fin 3) (x : ℝ), Real.sin (D.target.angleAt k) = x * Real.sin (α + β) →
      D.target.oppLen k = Λ * c * x := by
    intro k x hx
    rw [oppLen_eq, hx, hDt, ec]; ring
  have hpos2 : 0 < c * ((1 - s) * (2 + s)) := mul_pos hc (mul_pos (by linarith) (by linarith))
  have hcb : c + b - a = c * ((1 - s) * (2 + s)) := by rw [hcs, hbs]; ring
  have hΛpos : 0 < Λ := div_pos (circD_pos _) hD
  rw [hsa]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨e0, e1, e2⟩
    obtain ⟨K, M, -, -, -, -, hK, hM⟩ := Row11.boundary_baseAlpha D hα hrel hfull e0 e1 e2
    rw [side 0 s (by rw [e0, sA]), side 1 s (by rw [e1, sA]),
      side 2 (s * (2 - s ^ 2)) (by rw [e2, sAB])] at hK hM
    rw [hsum] at hM
    rw [hcb] at hK
    refine ⟨M, -K, ?_, ?_⟩
    · refine mul_right_cancel₀ hpos.ne' (hM.trans ?_)
      field_simp
      ring
    · have h1 : 0 < 1 - s := by linarith
      have hK1 : (K : ℝ) = Λ * (s * (2 - s) / (1 - s)) := by
        refine mul_right_cancel₀ hpos2.ne' (hK.trans ?_)
        field_simp
        ring
      push_cast
      rw [hK1]
  · rintro ⟨e0, e1, e2⟩
    obtain ⟨K, M, -, -, -, -, hK, hM⟩ := Row12.flux_identities D hα hrel hfull e0 e1 e2
    rw [side 0 (1 - s ^ 2) (by rw [e0, sB]), side 1 (1 - s ^ 2) (by rw [e1, sB]),
      side 2 (s * (1 - s ^ 2) * (3 - s ^ 2)) (by rw [e2, s3A])] at hK hM
    rw [hsum] at hM
    rw [hcb] at hK
    have hM1 : (M : ℝ) = Λ * ((1 - s) * (1 + s) ^ 2) := by
      refine mul_right_cancel₀ hpos.ne' (hM.trans ?_)
      ring
    have hM2 : (K : ℝ) = -(Λ * ((1 - s) ^ 2 * (1 + s))) := by
      refine mul_right_cancel₀ hpos2.ne' (hK.trans ?_)
      ring
    have h1 : 0 < 1 - s := by linarith
    have h2 : 0 < 1 + s := by linarith
    have hs' : s = ((M : ℝ) + K) / ((M : ℝ) - K) := by
      rw [hM1, hM2]
      field_simp
      ring
    refine ⟨M, K, hM1, hM2, hs', ⟨((M : ℚ) + K) / ((M : ℚ) - K), ?_⟩⟩
    push_cast
    rw [← hs']
  · rintro ⟨e0, e1, e2⟩
    obtain ⟨K, M, -, -, -, -, hK, hM⟩ := Row13.boundary D hα hrel hfull e0 e1 e2
    rw [side 0 1 (by rw [e0]; ring), side 1 1 (by rw [e1]; ring),
      side 2 s (by rw [e2, sA])] at hK hM
    rw [hsum] at hM
    rw [hcb] at hK
    have h1 : 0 < 1 - s := by linarith
    have h2 : 0 < 1 + s := by linarith
    have hM1 : (M : ℝ) = Λ * (1 / (1 + s)) := by
      refine mul_right_cancel₀ hpos.ne' (hM.trans ?_)
      field_simp
      ring
    have hK' : (K : ℝ) = Λ * (1 / (1 - s)) := by
      refine mul_right_cancel₀ hpos2.ne' (hK.trans ?_)
      field_simp
      ring
    have hs' : s = ((M : ℝ) + -K) / ((-K : ℝ) - M) := by
      rw [hM1, hK']
      field_simp
      ring
    refine ⟨M, -K, hM1, ?_, ?_, ⟨((M : ℚ) + -K) / ((-K : ℚ) - M), ?_⟩⟩
    · push_cast; rw [hK']
    · push_cast; exact hs'
    · push_cast; exact hs'

end Erdos634.BeesonColoring

#print axioms Erdos634.BeesonColoring.t4_M2_T5
