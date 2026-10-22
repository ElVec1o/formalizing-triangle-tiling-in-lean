import Erdos634.Draft.BeesonColoringThm21
import Erdos634.Draft.FluxFRow14Close
import Erdos634.Draft.FluxFRow15Setup
import Erdos634.Draft.FluxDRow11
import Erdos634.Draft.FluxCRow12
import Erdos634.Draft.FluxCRow5

/-!
# Beeson (arXiv 1206.2229v4) Theorem 1 (coloring equation), unified over the five target shapes

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Thm 1), Laczkovich (DCG 48 (2012)), Beeson-Zhang.
Formalization debt, not progress on the /goal outcomes.  Assembled from the pre-existing flux-layer theorems
`Row11.boundary_baseAlpha`, `Row12.flux_identities`, `Row13.boundary`, `Row14.setup`, `Row15.setup`.

Differences from the printed statement, all named:
* (H1) `alpha not in Q * pi` replaces Beeson's Lemma 1 (Laczkovich Thm 5.1, 5.3, not in Lean); the hypothesis
  "ABC not similar to the tile" is not needed.
* (H2) `M` is the flux integer, not shown equal to the black-minus-white count of Beeson's Lemma 12 (not in Lean).
* LABELLING: Beeson labels `A, C` to carry equally many tiles and writes `(X, Y, Z) = (BC, AC, AB)`.  Here the
  vertices are labelled by the target angles `(angleAt 0, angleAt 1, angleAt 2)` as in the hypotheses of each case and
  `X0, X1, X2 = oppLen 0, 1, 2`.  Isosceles cases: the apex `B` is target vertex 2, `Y = X2` is the base, `X0 = X1`
  the legs.  Cases `(2 alpha, alpha, 2 beta)` and `(2 alpha, beta, alpha + beta)`: `A, B, C` are vertices `0, 1, 2`
  (so `X = X0, Y = X1, Z = X2`).  The equation read: `M (a + b + c) = X0 + X1 + X2` (bases `alpha`, `beta`; Beeson's
  `+`), and `X0 - X1 + X2` or `X0 + X1 - X2` (Beeson's `-`: base `alpha+beta`, `(2alpha, alpha, 2beta)`,
  `(2alpha, beta, alpha+beta)`).  Positivity `M > 0` (Beeson's Lemma 13, `M != 0`) is added.
-/

open scoped Classical

namespace Erdos634.BeesonColoring

open Erdos634.Geometry

variable {N : ℕ}

theorem pos_M {M : ℤ} {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (h : (M : ℝ) * p = q) : 0 < M := by
  by_contra hn
  push Not at hn
  have h1 : (M : ℝ) ≤ 0 := by exact_mod_cast hn
  have := mul_nonpos_of_nonpos_of_nonneg h1 hp.le
  have : (M : ℝ) * p ≤ 0 := this
  linarith

theorem model_abc_pos {T : Tri} {α β a b c : ℝ} (h : T.ThreeAlphaData α β a b c) :
    0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < α ∧ 0 < β := by
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  exact ⟨o0 ▸ T.oppLen_pos (σ 0), o1 ▸ T.oppLen_pos (σ 1), o2 ▸ T.oppLen_pos (σ 2),
    h0 ▸ T.angleAt_pos' (σ 0), h1 ▸ T.angleAt_pos' (σ 1)⟩

set_option maxHeartbeats 2000000 in
/-- **Beeson Theorem 1, five shapes** (UNAUDITED; (H1), (H2), labelling: see the module header). -/
theorem thm1 (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) :
    -- base angles alpha: `+`
    ((D.target.angleAt 0 = α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + 2 * β) →
      ∃ M : ℤ, 0 < M ∧ (M : ℝ) * (a + b + c) =
        D.target.oppLen 0 + D.target.oppLen 1 + D.target.oppLen 2) ∧
    -- base angles beta: `+`
    ((D.target.angleAt 0 = β ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = 3 * α) →
      ∃ M : ℤ, 0 < M ∧ (M : ℝ) * (a + b + c) =
        D.target.oppLen 0 + D.target.oppLen 1 + D.target.oppLen 2) ∧
    -- base angles alpha + beta: `-` on the base
    ((D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α + β ∧ D.target.angleAt 2 = α) →
      ∃ M : ℤ, 0 < M ∧ (M : ℝ) * (a + b + c) =
        D.target.oppLen 0 + D.target.oppLen 1 - D.target.oppLen 2) ∧
    -- (2 alpha, alpha, 2 beta): `X - Y + Z`
    ((D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = 2 * β) →
      ∃ M : ℤ, 0 < M ∧ (M : ℝ) * (a + b + c) =
        D.target.oppLen 0 - D.target.oppLen 1 + D.target.oppLen 2) ∧
    -- (2 alpha, beta, alpha + beta): `X - Y + Z`
    ((D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β) →
      ∃ M : ℤ, 0 < M ∧ (M : ℝ) * (a + b + c) =
        D.target.oppLen 0 - D.target.oppLen 1 + D.target.oppLen 2) := by
  obtain ⟨ha0, hb0, hc0, hαpos, hβpos⟩ := model_abc_pos h
  have hsum : 0 < a + b + c := by linarith
  have p0 := D.target.oppLen_pos 0
  have p1 := D.target.oppLen_pos 1
  have p2 := D.target.oppLen_pos 2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨e0, e1, e2⟩
    obtain ⟨K, M, -, -, -, -, -, hM⟩ := Row11.boundary_baseAlpha D hα hrel h e0 e1 e2
    exact ⟨M, pos_M hsum (by linarith) hM, by linarith⟩
  · rintro ⟨e0, e1, e2⟩
    obtain ⟨K, M, -, -, -, -, -, hM⟩ := Row12.flux_identities D hα hrel h e0 e1 e2
    exact ⟨M, pos_M hsum (by linarith) hM, by linarith⟩
  · rintro ⟨e0, e1, e2⟩
    obtain ⟨K, M, -, -, -, -, -, hM⟩ := Row13.boundary D hα hrel h e0 e1 e2
    have hlt := D.target.oppLen_lt 2
    have h20 : ((2 : Fin 3) + 1) = 0 := by decide
    have h21 : ((2 : Fin 3) + 2) = 1 := by decide
    rw [h20, h21] at hlt
    exact ⟨M, pos_M hsum (by linarith) hM, by linarith⟩
  · rintro ⟨e0, e1, e2⟩
    obtain ⟨s, S, hs0, hs1, hc, hsa, hsb, hX, hZ, hSc, -⟩ := Row15.setup D hα hrel h e0 e1 e2
    refine ⟨S, pos_M hc (mul_pos (mul_pos (by linarith) (by linarith)) p1) hSc, ?_⟩
    rw [hsa, hsb, hX, hZ]
    linear_combination (2 + s - s ^ 2) * hSc
  · rintro ⟨e0, e1, e2⟩
    obtain ⟨s, S, hs0, hs1, hc, hsa, hsb, hY, hSc, -⟩ := Row14.setup D hα hrel h e0 e1 e2
    obtain ⟨-, haeq⟩ := model_a_eq hrel h
    have hs : s = 2 * Real.sin (α / 2) := mul_right_cancel₀ hc.ne' (hsa.symm.trans haeq)
    obtain ⟨-, tα, -, -⟩ := threeAlpha_sin_table hrel
    have hπ := Real.pi_pos
    have hco : 0 < Real.cos (α / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    have hAB : Real.sin (α + β) = Real.cos (α / 2) := by
      rw [show α + β = Real.pi / 2 - α / 2 by linarith, Real.sin_pi_div_two_sub]
    have hcos : Real.cos α = 1 - 2 * Real.sin (α / 2) ^ 2 := by
      have e := Real.cos_two_mul (α / 2)
      rw [show 2 * (α / 2) = α by ring] at e
      have p := Real.sin_sq_add_cos_sq (α / 2)
      linear_combination e + 2 * p
    have h2α : Real.sin (2 * α)
        = 2 * Real.sin (α / 2) * Real.cos (α / 2) * (2 - 4 * Real.sin (α / 2) ^ 2) := by
      rw [Real.sin_two_mul, tα, hcos]; ring
    have lt0 := D.target.lawSin 0 2
    rw [e0, e2, h2α, hAB] at lt0
    have hX : D.target.oppLen 0 = s * (2 - s ^ 2) * D.target.oppLen 2 :=
      mul_left_cancel₀ hco.ne' (by rw [hs]; linear_combination (-1 : ℝ) * lt0)
    refine ⟨S, pos_M hc (mul_pos hs0 p2) hSc, ?_⟩
    rw [hsa, hsb, hX, hY]
    linear_combination (2 + s - s ^ 2) * hSc

end Erdos634.BeesonColoring

#print axioms Erdos634.BeesonColoring.thm1
