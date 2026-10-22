import Erdos634.Draft.BeesonColoringThm1
import Erdos634.Draft.A1FieldClause

/-!
# Beeson (arXiv 1206.2229v4) Lemma 24 and the `M1` column of Theorem 4, for a real `CongruentDissection`

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Lemma 24, Theorem 4), Laczkovich (DCG 48 (2012)),
Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.

Printed Theorem 4: for the five shapes of Lemma 11, with `Lambda` the ratio of the circumdiameter of ABC to that of T
and `c = 1`, `s = a/c`, the integers `M1, M2` (Theorem 3) are `Lambda * (poly in s)`.  Formalized here: Lemma 24
(`sin_table`, with `s = 2 cos(alpha+beta)`) and the **`M1` column of all five rows** (`t4_M1`), obtained from
`thm1` (the Phi_1 flux integer, same as blacks minus whites by `thm1_colouring`) and the law of sines.
NOT formalized: the `M2` column (Phi_2; `Row15.setup` and `Row14.setup` discard the second flux integer, and the
Lemma 23 sign convention for Phi_2 is not in Lean), and the final sentence "M1, M2 != 0, Lambda = M1/s".
Project hypothesis (H1) `alpha not in Q * pi` replaces Beeson's Lemma 1 (Laczkovich 5.1, 5.3; not in Lean).
Vertex order as in `thm1`: shapes `(alpha, alpha, alpha+2beta)`, `(beta, beta, 3alpha)`, `(alpha+beta, alpha+beta, alpha)`,
`(2alpha, alpha, 2beta)`, `(2alpha, beta, alpha+beta)` at target vertices `0, 1, 2`.
-/

open scoped Classical

namespace Erdos634.BeesonColoring

open Erdos634.Geometry

/-- **Beeson Lemma 24** (the trigonometric table), with `s = 2 cos (alpha + beta)`; `sin (alpha+beta) = sin gamma`. -/
theorem sin_table {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (hα : 0 < α) (hβ : 0 < β) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ Real.sin α = s * Real.sin (α + β) ∧
      Real.sin β = (1 - s ^ 2) * Real.sin (α + β) ∧ Real.sin (2 * α + β) = Real.sin (α + β) ∧
      Real.sin (2 * α) = s * (2 - s ^ 2) * Real.sin (α + β) ∧
      Real.sin (α + 2 * β) = s * (2 - s ^ 2) * Real.sin (α + β) ∧
      Real.sin (3 * α) = s * (1 - s ^ 2) * (3 - s ^ 2) * Real.sin (α + β) ∧
      Real.sin (2 * β) = s * (1 - s ^ 2) * (3 - s ^ 2) * Real.sin (α + β) := by
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = α + β := ⟨_, rfl⟩
  have hαδ : α = Real.pi - 2 * δ := by linarith
  have hβδ : β = 3 * δ - Real.pi := by linarith
  have hpi := Real.pi_pos
  have hsδ : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hcδ : 0 < Real.cos δ := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have pyth := Real.sin_sq_add_cos_sq δ
  have sα : Real.sin α = 2 * Real.sin δ * Real.cos δ := by
    rw [hαδ, Real.sin_pi_sub, Real.sin_two_mul]
  have cα : Real.cos α = 1 - 2 * Real.cos δ ^ 2 := by
    rw [hαδ, Real.cos_pi_sub, Real.cos_two_mul]; ring
  have sβ : Real.sin β = - (3 * Real.sin δ - 4 * Real.sin δ ^ 3) := by
    rw [hβδ, Real.sin_sub_pi, Real.sin_three_mul]
  have sγ : Real.sin (2 * α + β) = Real.sin δ := by
    rw [show 2 * α + β = Real.pi - δ by linarith, Real.sin_pi_sub]
  have s2α : Real.sin (2 * α) = 2 * Real.sin α * Real.cos α := Real.sin_two_mul α
  have sab : Real.sin (α + 2 * β) = Real.sin (2 * α) := by
    rw [show α + 2 * β = Real.pi - 2 * α by linarith, Real.sin_pi_sub]
  have s3 : Real.sin (3 * α) = 3 * Real.sin α - 4 * Real.sin α ^ 3 := Real.sin_three_mul α
  have s2β : Real.sin (2 * β) = Real.sin (3 * α) := by
    rw [show 2 * β = Real.pi - 3 * α by linarith, Real.sin_pi_sub]
  rw [← hδ]
  have hβpos : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi hβ (by linarith)
  have hs1 : 1 - (2 * Real.cos δ) ^ 2 > 0 := by
    have : Real.sin β = (1 - (2 * Real.cos δ) ^ 2) * Real.sin δ := by
      rw [sβ]; nlinarith [pyth]
    rw [this] at hβpos
    exact pos_of_mul_pos_left hβpos hsδ.le |> fun h => by nlinarith [h]
  refine ⟨2 * Real.cos δ, by linarith, ?_, ?_, ?_, sγ, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · rw [sα]; ring
  · rw [sβ]; nlinarith [pyth]
  · rw [s2α, sα, cα]; ring
  · rw [sab, s2α, sα, cα]; ring
  · rw [s3, sα]
    have : Real.sin δ ^ 2 = 1 - Real.cos δ ^ 2 := by linarith
    have e : Real.sin δ ^ 3 = Real.sin δ * (1 - Real.cos δ ^ 2) := by rw [← this]; ring
    have : (2 * Real.sin δ * Real.cos δ) ^ 3 = 8 * Real.cos δ ^ 3 * Real.sin δ * (1 - Real.cos δ ^ 2) := by
      rw [mul_pow, mul_pow, e]; ring
    rw [this]; ring
  · rw [s2β, s3, sα]
    have : Real.sin δ ^ 2 = 1 - Real.cos δ ^ 2 := by linarith
    have e : Real.sin δ ^ 3 = Real.sin δ * (1 - Real.cos δ ^ 2) := by rw [← this]; ring
    have : (2 * Real.sin δ * Real.cos δ) ^ 3 = 8 * Real.cos δ ^ 3 * Real.sin δ * (1 - Real.cos δ ^ 2) := by
      rw [mul_pow, mul_pow, e]; ring
    rw [this]; ring

open Erdos634.Geometry.A1Field in
/-- **Beeson Theorem 4, `M1` column** (UNAUDITED; (H1)).  `Lambda = circD target / circD model`, `s = a / c`.
Each of the five shapes gives an integer `M > 0` (the `thm1` flux integer) with `M` equal to the printed `M1`. -/
theorem t4_M1 (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) :
    ((D.target.angleAt 0 = α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + 2 * β) →
      ∃ M : ℤ, 0 < M ∧ (M : ℝ) = (circD D.target / circD D.model) * ((a / c) * (2 + a / c) / (1 + a / c))) ∧
    ((D.target.angleAt 0 = β ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = 3 * α) →
      ∃ M : ℤ, 0 < M ∧ (M : ℝ) = (circD D.target / circD D.model) * ((1 - a / c) * (1 + a / c) ^ 2)) ∧
    ((D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α + β ∧ D.target.angleAt 2 = α) →
      ∃ M : ℤ, 0 < M ∧ (M : ℝ) = (circD D.target / circD D.model) * (1 / (1 + a / c))) ∧
    ((D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = 2 * β) →
      ∃ M : ℤ, 0 < M ∧ (M : ℝ) = (circD D.target / circD D.model) *
        ((a / c) * (1 - a / c) * (2 + a / c))) ∧
    ((D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β) →
      ∃ M : ℤ, 0 < M ∧ (M : ℝ) = (circD D.target / circD D.model) * (a / c)) := by
  obtain ⟨ha, hb, hc, hαpos, hβpos⟩ := model_abc_pos h
  obtain ⟨s, hs0, hs1, sA, sB, sG, s2A, sAB, s3A, s2B⟩ := sin_table hrel hαpos hβpos
  have hsδ : 0 < Real.sin (α + β) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  -- model sides from the law of sines
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
  obtain ⟨T1, T2, T3, T4, T5⟩ := thm1 D hα hrel ⟨σ, h0, o0, h1, o1, h2, o2⟩
  rw [hsa]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨e0, e1, e2⟩
    obtain ⟨M, hMp, hM⟩ := T1 ⟨e0, e1, e2⟩
    refine ⟨M, hMp, ?_⟩
    rw [side 0 s (by rw [e0, sA]), side 1 s (by rw [e1, sA]),
      side 2 (s * (2 - s ^ 2)) (by rw [e2, sAB])] at hM
    rw [hsum] at hM
    have h1 : 0 < 1 + s := by linarith
    refine mul_right_cancel₀ hpos.ne' (hM.trans ?_)
    field_simp
    ring
  · rintro ⟨e0, e1, e2⟩
    obtain ⟨M, hMp, hM⟩ := T2 ⟨e0, e1, e2⟩
    refine ⟨M, hMp, ?_⟩
    rw [side 0 (1 - s ^ 2) (by rw [e0, sB]), side 1 (1 - s ^ 2) (by rw [e1, sB]),
      side 2 (s * (1 - s ^ 2) * (3 - s ^ 2)) (by rw [e2, s3A])] at hM
    rw [hsum] at hM
    have h1 : 0 < 1 + s := by linarith
    refine mul_right_cancel₀ hpos.ne' (hM.trans ?_)
    field_simp
    ring
  · rintro ⟨e0, e1, e2⟩
    obtain ⟨M, hMp, hM⟩ := T3 ⟨e0, e1, e2⟩
    refine ⟨M, hMp, ?_⟩
    rw [side 0 1 (by rw [e0]; ring), side 1 1 (by rw [e1]; ring),
      side 2 s (by rw [e2, sA])] at hM
    rw [hsum] at hM
    have h1 : 0 < 1 + s := by linarith
    refine mul_right_cancel₀ hpos.ne' (hM.trans ?_)
    field_simp
    ring
  · rintro ⟨e0, e1, e2⟩
    obtain ⟨M, hMp, hM⟩ := T4 ⟨e0, e1, e2⟩
    refine ⟨M, hMp, ?_⟩
    rw [side 0 (s * (2 - s ^ 2)) (by rw [e0, s2A]), side 1 s (by rw [e1, sA]),
      side 2 (s * (1 - s ^ 2) * (3 - s ^ 2)) (by rw [e2, s2B])] at hM
    rw [hsum] at hM
    have h1 : 0 < 1 + s := by linarith
    refine mul_right_cancel₀ hpos.ne' (hM.trans ?_)
    field_simp
    ring
  · rintro ⟨e0, e1, e2⟩
    obtain ⟨M, hMp, hM⟩ := T5 ⟨e0, e1, e2⟩
    refine ⟨M, hMp, ?_⟩
    rw [side 0 (s * (2 - s ^ 2)) (by rw [e0, s2A]), side 1 (1 - s ^ 2) (by rw [e1, sB]),
      side 2 1 (by rw [e2]; ring)] at hM
    rw [hsum] at hM
    have h1 : 0 < 1 + s := by linarith
    refine mul_right_cancel₀ hpos.ne' (hM.trans ?_)
    field_simp
    ring

end Erdos634.BeesonColoring

#print axioms Erdos634.BeesonColoring.sin_table
#print axioms Erdos634.BeesonColoring.t4_M1
