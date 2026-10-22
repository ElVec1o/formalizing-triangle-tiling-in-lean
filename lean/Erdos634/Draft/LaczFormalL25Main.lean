import Erdos634.Draft.LaczFormalL25Geo

/-!
# Laczkovich Theorem 2.5, first triple `(α, α+β, α+2β)`: assembly

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.5, Fig. 6), Beeson,
Beeson-Zhang, Zhang.

`thm25_first`: `Δ` a rational triangle (sides `a, b, c` opposite `α, β, γ`) with `γ = 2π/3` (`c² = a² + ab + b²`).
Then the triangle `T = D E B` of Fig. 6 (angles `α` at `D`, `α+β = π/3` at `E`, `α+2β` at `B`) is a union of finitely
many congruent triangles similar to `Δ`.  Construction: `ABC` (tile), `FDAC` (Lemma 2.2 (ii), `trap_ii`), `BEFC`
(Lemma 2.2 (iii), `trap_iii`), with the free rational length `CF = a` of the paper.
-/

namespace Erdos634.LaczL25

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL21 Erdos634.LaczL24 Erdos634.Realizable

theorem gram2 (w d : Plane) (p q p' q' : ℝ) :
    inner ℝ (p • w + q • d) (p' • w + q' • d)
      = p * p' * inner ℝ w w + (p * q' + q * p') * inner ℝ w d + q * q' * inner ℝ d d := by
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm d w]; ring

theorem det_comb (w d : Plane) (p q p' q' : ℝ) :
    (p • w + q • d) 0 * (p' • w + q' • d) 1 - (p • w + q • d) 1 * (p' • w + q' • d) 0
      = (p * q' - q * p') * (w 0 * d 1 - w 1 * d 0) := by
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-- The sub-chart image of `trapSet 2` is the chart set `SB`. -/
theorem sub_image (A w d : Plane) (h : w 0 * d 1 - w 1 * d 0 ≠ 0) (τ : ℝ) (h0 : 0 < τ) (h1 : τ < 1 / 2)
    (h' : ((1 - τ) • w + (-1 : ℝ) • d) 0 * ((-τ) • w + (1 : ℝ) • d) 1
      - ((1 - τ) • w + (-1 : ℝ) • d) 1 * ((-τ) • w + (1 : ℝ) • d) 0 ≠ 0) :
    chartEquiv (A + τ • w + (1 : ℝ) • d) ((1 - τ) • w + (-1 : ℝ) • d) ((-τ) • w + (1 : ℝ) • d) h' ''
        trapSet 2 = chartEquiv A w d h '' SB τ := by
  have hd : 0 < 1 - 2 * τ := by linarith
  ext y
  constructor
  · rintro ⟨x, ⟨x1, x2, x3, x4⟩, rfl⟩
    refine ⟨mkPt (τ + (1 - τ) * x 0 - τ * x 1) (1 - x 0 + x 1), ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [mkPt_zero, mkPt_one] <;> nlinarith
    · rw [chartEquiv_apply, chartEquiv_apply]; simp only [mkPt_zero, mkPt_one]; module
  · rintro ⟨z, ⟨z1, z2, z3, z4⟩, rfl⟩
    obtain ⟨X0, hX0⟩ : ∃ X0 : ℝ, X0 * (1 - 2 * τ) = z 0 + τ * z 1 - 2 * τ :=
      ⟨(z 0 + τ * z 1 - 2 * τ) / (1 - 2 * τ), div_mul_cancel₀ _ hd.ne'⟩
    obtain ⟨X1, hX1⟩ : ∃ X1 : ℝ, X1 * (1 - 2 * τ) = z 0 + (1 - τ) * z 1 - 1 :=
      ⟨(z 0 + (1 - τ) * z 1 - 1) / (1 - 2 * τ), div_mul_cancel₀ _ hd.ne'⟩
    have g1 : 0 ≤ X1 := le_of_mul_le_mul_right (by nlinarith) hd
    have g2 : X1 ≤ 1 := le_of_mul_le_mul_right (by nlinarith) hd
    have g3 : 0 ≤ X0 := le_of_mul_le_mul_right (by nlinarith) hd
    have g4 : X0 ≤ 1 + X1 := le_of_mul_le_mul_right (by nlinarith) hd
    have e1 : z 1 = 1 - X0 + X1 := by
      refine mul_right_cancel₀ hd.ne' ?_
      linarith
    have e0 : z 0 = τ + (1 - τ) * X0 - τ * X1 := by
      refine mul_right_cancel₀ hd.ne' ?_
      linear_combination (-(1 - τ)) * hX0 + τ * hX1
    refine ⟨mkPt X0 X1, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp only [mkPt_one]; exact g1
    · simp only [mkPt_one]; exact g2
    · simp only [mkPt_zero]; exact g3
    · simp only [mkPt_zero, mkPt_one]; linarith
    · rw [chartEquiv_apply, chartEquiv_apply, e0, e1]; simp only [mkPt_zero, mkPt_one]; module

end Erdos634.LaczL25
