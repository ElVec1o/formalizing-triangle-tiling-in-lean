-- Draft/LaczFormalT5.lean -- killing two of the three unresolved models of `LaczFormalT4.similar_partial`:
-- the golden triangles (pi/5, 2pi/5, 2pi/5) and (pi/5, pi/5, 3pi/5) cannot be similar-reptiles.  Argument (new, elementary):
-- the row of the side matrix at the shortest side gives  mu = X + a*(1+sqrt 5)/2  with X, a natural; then mu^2 = N rational
-- and sqrt 5 irrational force a = 0, so mu = X rational, contradicting `Row2.mu_irrational` (N non-square).
-- UNAUDITED.  Credit: Snover-Waiveris-Williams (the theorem), Beeson (Triangle tiling I), Beeson-Rosu.
import Erdos634.Draft.LaczFormalT4

open scoped Classical
open Real Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
  Erdos634.Draft.LemmaCFinal

namespace Erdos634.Draft.LaczFormal

theorem golden_arith {N X a : ℕ} {μ : ℝ} (hNm : μ ^ 2 = N) (hμq : ¬ ∃ r : ℚ, μ = r)
    (h : μ = X + a * ((1 + Real.sqrt 5) / 2)) : False := by
  have h5 : ¬ IsSquare 5 := by
    rintro ⟨m, hm⟩
    have : m ≤ 2 := by nlinarith
    interval_cases m <;> omega
  have hirr5 : Irrational (Real.sqrt 5) := by
    have := irrational_sqrt_natCast_iff.mpr h5
    simpa using this
  have s2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  by_cases ha : a = 0
  · exact hμq ⟨X, by rw [h, ha]; simp⟩
  have hapos : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero ha
  have hc : 0 < ((X : ℝ) + a / 2) * a := by positivity
  apply hirr5
  refine ⟨((N : ℚ) - ((X : ℚ) + a / 2) ^ 2 - 5 * (a : ℚ) ^ 2 / 4) / (((X : ℚ) + a / 2) * a), ?_⟩
  push_cast
  rw [div_eq_iff hc.ne']
  have hN' : (N : ℝ) = (X + a * ((1 + Real.sqrt 5) / 2)) ^ 2 := by rw [← h, hNm]
  linear_combination hN' + (a : ℝ) ^ 2 / 4 * s2

/-- Golden acute `(π/5, 2π/5, 2π/5)` is not a similar-reptile model (N non-square). -/
theorem kill_golden_acute {N : ℕ} (D : CongruentDissection N) (μ : ℝ)
    (hside : ∀ k, D.target.oppLen k = μ * D.model.oppLen k) (hNm : μ ^ 2 = N)
    (hμq : ¬ ∃ r : ℚ, μ = r) (hT : TileAngles D (π / 5) (2 * π / 5) (2 * π / 5)) : False := by
  obtain ⟨σ, h0, h1, h2⟩ := hT
  have hpq : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
  have hpr : σ 0 ≠ σ 2 := σ.injective.ne (by decide)
  have hqr : σ 1 ≠ σ 2 := σ.injective.ne (by decide)
  have hpi := Real.pi_pos
  have sp : 0 < Real.sin (π / 5) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  have s25 : Real.sin (2 * π / 5) = Real.sin (π / 5) * ((1 + Real.sqrt 5) / 2) := by
    rw [show 2 * π / 5 = 2 * (π / 5) by ring, Real.sin_two_mul, Real.cos_pi_div_five]; ring
  set p := σ 0; set q := σ 1; set r := σ 2
  have hvp := D.model.oppLen_pos p
  have rq : D.model.oppLen q = ((1 + Real.sqrt 5) / 2) * D.model.oppLen p := by
    have h := D.model.lawSin p q
    rw [h0, h1, s25] at h
    have : Real.sin (π / 5) * D.model.oppLen q =
        Real.sin (π / 5) * (((1 + Real.sqrt 5) / 2) * D.model.oppLen p) := by linarith
    exact mul_left_cancel₀ sp.ne' this
  have rr : D.model.oppLen r = ((1 + Real.sqrt 5) / 2) * D.model.oppLen p := by
    have h := D.model.lawSin p r
    rw [h0, h2, s25] at h
    have : Real.sin (π / 5) * D.model.oppLen r =
        Real.sin (π / 5) * (((1 + Real.sqrt 5) / 2) * D.model.oppLen p) := by linarith
    exact mul_left_cancel₀ sp.ne' this
  have hrow := Row2.sideCountT_eigen D μ hside p
  rw [Fin.sum_univ_three] at hrow
  have hs3 : ∀ f : Fin 3 → ℝ, f p + f q + f r = f 0 + f 1 + f 2 := fun f =>
    sum3 f p q r hpq hpr hqr
  rw [← hs3 (fun j => (D.sideCountT p j : ℝ) * D.model.oppLen j), ] at hrow
  simp only [rq, rr] at hrow
  refine golden_arith (N := N) (X := D.sideCountT p p) (a := D.sideCountT p q + D.sideCountT p r) hNm hμq ?_
  push_cast
  have := mul_right_cancel₀ hvp.ne' (by linarith : (↑(D.sideCountT p p) + (↑(D.sideCountT p q) + ↑(D.sideCountT p r)) * ((1 + Real.sqrt 5) / 2)) * D.model.oppLen p = μ * D.model.oppLen p)
  linarith

/-- Golden obtuse `(π/5, π/5, 3π/5)` is not a similar-reptile model (N non-square). -/
theorem kill_golden_obtuse {N : ℕ} (D : CongruentDissection N) (μ : ℝ)
    (hside : ∀ k, D.target.oppLen k = μ * D.model.oppLen k) (hNm : μ ^ 2 = N)
    (hμq : ¬ ∃ r : ℚ, μ = r) (hT : TileAngles D (π / 5) (π / 5) (3 * π / 5)) : False := by
  obtain ⟨σ, h0, h1, h2⟩ := hT
  have hpq : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
  have hpr : σ 0 ≠ σ 2 := σ.injective.ne (by decide)
  have hqr : σ 1 ≠ σ 2 := σ.injective.ne (by decide)
  have hpi := Real.pi_pos
  have sp : 0 < Real.sin (π / 5) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  have s25 : Real.sin (2 * π / 5) = Real.sin (π / 5) * ((1 + Real.sqrt 5) / 2) := by
    rw [show 2 * π / 5 = 2 * (π / 5) by ring, Real.sin_two_mul, Real.cos_pi_div_five]; ring
  have s35 : Real.sin (3 * π / 5) = Real.sin (π / 5) * ((1 + Real.sqrt 5) / 2) := by
    rw [show 3 * π / 5 = π - 2 * π / 5 by ring, Real.sin_pi_sub, s25]
  set p := σ 0; set q := σ 1; set r := σ 2
  have hvp := D.model.oppLen_pos p
  have rq : D.model.oppLen q = D.model.oppLen p := by
    have h := D.model.lawSin p q
    rw [h0, h1] at h
    exact mul_left_cancel₀ sp.ne' (by linarith)
  have rr : D.model.oppLen r = ((1 + Real.sqrt 5) / 2) * D.model.oppLen p := by
    have h := D.model.lawSin p r
    rw [h0, h2, s35] at h
    have : Real.sin (π / 5) * D.model.oppLen r =
        Real.sin (π / 5) * (((1 + Real.sqrt 5) / 2) * D.model.oppLen p) := by linarith
    exact mul_left_cancel₀ sp.ne' this
  have hrow := Row2.sideCountT_eigen D μ hside p
  rw [Fin.sum_univ_three] at hrow
  have hs3 : ∀ f : Fin 3 → ℝ, f p + f q + f r = f 0 + f 1 + f 2 := fun f =>
    sum3 f p q r hpq hpr hqr
  rw [← hs3 (fun j => (D.sideCountT p j : ℝ) * D.model.oppLen j)] at hrow
  simp only [rq, rr] at hrow
  refine golden_arith (N := N) (X := D.sideCountT p p + D.sideCountT p q) (a := D.sideCountT p r) hNm hμq ?_
  push_cast
  have := mul_right_cancel₀ hvp.ne' (by linarith : ((↑(D.sideCountT p p) + ↑(D.sideCountT p q)) + ↑(D.sideCountT p r) * ((1 + Real.sqrt 5) / 2)) * D.model.oppLen p = μ * D.model.oppLen p)
  linarith

/-- **Reptile theorem, partial, second form**: only the 30-30-120 model remains unresolved. -/
theorem similar_partial2 {N : ℕ} (D : CongruentDissection N) (μ : ℝ)
    (hsim : ∀ k, D.target.angleAt k = D.model.angleAt k ∧ D.target.oppLen k = μ * D.model.oppLen k)
    (hN : ¬ IsSquare N) :
    (∃ A B : ℕ, N = A ^ 2 + B ^ 2 ∧ RightLegs D A B) ∨
    ((∃ m : ℕ, N = 3 * m ^ 2) ∧ TileAngles D (π / 6) (π / 3) (π / 2)) ∨
    ((∃ m : ℕ, N = 3 * m ^ 2) ∧ TileAngles D (π / 6) (π / 6) (2 * π / 3)) := by
  have hside : ∀ k, D.target.oppLen k = μ * D.model.oppLen k := fun k => (hsim k).2
  obtain ⟨⟨hNμ, hμq⟩, -⟩ := similar_reduction D μ hsim hN
  rcases similar_partial D μ hsim hN with h | h | h | ⟨-, hT⟩ | ⟨-, hT⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact (kill_golden_acute D μ hside hNμ.symm hμq hT).elim
  · exact (kill_golden_obtuse D μ hside hNμ.symm hμq hT).elim

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.golden_arith
#print axioms Erdos634.Draft.LaczFormal.kill_golden_acute
#print axioms Erdos634.Draft.LaczFormal.kill_golden_obtuse
#print axioms Erdos634.Draft.LaczFormal.similar_partial2
