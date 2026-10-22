-- Draft/LaczFormalT1.lean -- target T1 of the L8-general plan: a rational angle whose cosine lies in a real quadratic
-- field Q(sqrt N) (N not a perfect square) is pi/3, pi/2, 2pi/3 or belongs to one of the families
--   N = 2k^2: pi/4, 3pi/4;   N = 3k^2: pi/6, 5pi/6;   N = 5k^2: pi/5, 2pi/5, 3pi/5, 4pi/5.
-- This GENERALISES `Row2.lemmaQ` (Draft/FluxERow2Q.lean; N prime = 3 mod 4, >= 7, where only pi/3, pi/2, 2pi/3 survive):
-- the first half of that proof (algebraic integer x = 2cos theta, its conjugate x', |x|,|x'| <= 2, U = x+x', W = xx' in Z)
-- is re-run with s^2 = N; the primality step is replaced by an integer enumeration of
-- D = U^2 - 4W = (x-x')^2 in [1,16], D non-square, D = 0,1 mod 4, both roots in [-2,2].
-- Credit: Beeson (Triangle tiling I, Lemma on rational angles), Snover-Waiveris-Williams, Niven (Mathlib).  UNAUDITED.
import Erdos634.Draft.FluxERow2Q
import Erdos634.Draft.FluxERow2E

open scoped Classical
open Real Polynomial Erdos634.Geometry

namespace Erdos634.Draft.LaczFormal

/-- Core: algebraic-integer data of `x = 2 cos θ = a + b s`. -/
theorem t1_core {N : ℕ} (hN : ¬ IsSquare N) {s : ℝ} (hs : s ^ 2 = N) {θ : ℝ}
    (hθ : ∃ r : ℚ, θ = r * π) (hc : Row2.QMu s (Real.cos θ)) :
    ∃ (a b : ℚ) (U W : ℤ), 2 * Real.cos θ = (a : ℝ) + b * s ∧ (U : ℝ) = 2 * a ∧
      (W : ℝ) = a * a - b * b * N ∧ |(a : ℝ) + b * s| ≤ 2 ∧ |(a : ℝ) - b * s| ≤ 2 := by
  obtain ⟨r, hr⟩ := hθ
  obtain ⟨q₁, q₂, hq⟩ := hc
  have hsq : s ^ 2 = ((N : ℚ) : ℝ) := by rw [hs]; push_cast; ring
  have hirr : ∀ q : ℚ, s ≠ q := by
    intro q hsq'
    have habs : √(N : ℝ) = |(q : ℝ)| := by
      rw [← hsq', ← hs, Real.sqrt_sq_eq_abs]
    exact (irrational_sqrt_natCast_iff.mpr hN) ⟨|q|, by rw [habs]; push_cast; rfl⟩
  set a : ℚ := 2 * q₁ with ha
  set b : ℚ := 2 * q₂ with hb
  set x : ℝ := 2 * Real.cos θ with hx
  have hxab : x = (a : ℝ) + b * s := by rw [hx, hq, ha, hb]; push_cast; ring
  set x' : ℝ := (a : ℝ) - b * s with hx'
  have hxint : IsIntegral ℤ x := by
    rw [hx, hr]; exact Real.isIntegral_two_mul_cos_rat_mul_pi r
  have hx'int : IsIntegral ℤ x' := by
    obtain ⟨P, hPm, hP⟩ := hxint
    obtain ⟨A, B, h1, h2⟩ := Row2.poly_conj hsq a b P
    rw [hxab, h1] at hP
    have hB : B = 0 := by
      by_contra hB0
      apply hirr (-A / B)
      have hBr : (B : ℝ) ≠ 0 := by exact_mod_cast hB0
      push_cast; field_simp; linarith
    have hA : (A : ℝ) = 0 := by rw [hB] at hP; simpa using hP
    exact ⟨P, hPm, by rw [hx', h2, hA, hB]; simp⟩
  have hxle : |x| ≤ 2 := by
    rw [hx, abs_mul, abs_two]
    have := Real.abs_cos_le_one θ
    linarith
  set n : ℕ := 2 * r.den with hn
  have hnpos : 0 < n := by positivity
  have hchebx : Row2.cheb x n = 2 := by
    rw [hx, Row2.cheb_cos θ n, hr]
    have : ((n : ℕ) : ℝ) * ((r : ℝ) * π) = (r.num : ℝ) * (2 * π) := by
      rw [hn]; push_cast
      have hd : (r : ℝ) * r.den = r.num := by exact_mod_cast Rat.mul_den_eq_num r
      linear_combination (2 * π) * hd
    rw [this, Real.cos_int_mul_two_pi]; ring
  have hx'le : |x'| ≤ 2 := by
    obtain ⟨A, B, h1, h2⟩ := Row2.cheb_conj hsq a b n
    rw [← hxab, hchebx] at h1
    have hB : B = 0 := by
      by_contra hB0
      apply hirr ((2 - A) / B)
      have hBr : (B : ℝ) ≠ 0 := by exact_mod_cast hB0
      push_cast; field_simp; linarith
    have hA : (A : ℝ) = 2 := by rw [hB] at h1; simpa using h1.symm
    refine Row2.abs_le_two_of_cheb hnpos ?_
    rw [hx', h2, hA, hB]; simp
  obtain ⟨U, hU⟩ := (hxint.add hx'int).exists_int_iff_exists_rat.mp
    ⟨2 * a, by rw [hxab, hx']; push_cast; ring⟩
  obtain ⟨W, hW⟩ := (hxint.mul hx'int).exists_int_iff_exists_rat.mp
    ⟨a * a - b * b * N, by rw [hxab, hx']; push_cast; linear_combination (-(b : ℝ) ^ 2) * hs⟩
  refine ⟨a, b, U, W, hxab, ?_, ?_, ?_, ?_⟩
  · rw [← hU, hxab, hx']; ring
  · rw [← hW, hxab, hx']; linear_combination (-(b : ℝ) ^ 2) * hs
  · rw [← hxab]; exact hxle
  · exact hx'le

theorem theta_eq_of_cos {θ φ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π) (g0 : 0 ≤ φ) (g1 : φ ≤ π)
    (h : Real.cos θ = Real.cos φ) : θ = φ :=
  Real.injOn_cos ⟨h0, h1⟩ ⟨g0, g1⟩ h

theorem nat_sq_of_rat {n : ℕ} (r : ℚ) (h : (r : ℝ) ^ 2 = (n : ℝ)) : ∃ j : ℕ, n = j ^ 2 := by
  have h' : r ^ 2 = (n : ℚ) := by exact_mod_cast h
  have h1 : IsSquare (((n : ℤ) : ℤ) : ℚ) := ⟨r, by push_cast; rw [← h']; ring⟩
  rw [Rat.isSquare_intCast_iff] at h1
  obtain ⟨j, hj⟩ := Int.isSquare_natCast_iff.mp h1
  exact ⟨j, by rw [hj]; ring⟩

theorem kernel2 {N j : ℕ} (h : 8 * N = j ^ 2) : ∃ k : ℕ, N = 2 * k ^ 2 := by
  have h2 : 2 ∣ j := Nat.Prime.dvd_of_dvd_pow Nat.prime_two (⟨4 * N, by rw [← h]; ring⟩ : 2 ∣ j ^ 2)
  obtain ⟨i, rfl⟩ := h2
  have h3 : 2 * N = i ^ 2 := by nlinarith
  have h4 : 2 ∣ i := Nat.Prime.dvd_of_dvd_pow Nat.prime_two (⟨N, by rw [← h3]⟩ : 2 ∣ i ^ 2)
  obtain ⟨k, rfl⟩ := h4
  exact ⟨k, by nlinarith⟩

theorem kernel3 {N j : ℕ} (h : 12 * N = j ^ 2) : ∃ k : ℕ, N = 3 * k ^ 2 := by
  have h2 : 2 ∣ j := Nat.Prime.dvd_of_dvd_pow Nat.prime_two (⟨6 * N, by rw [← h]; ring⟩ : 2 ∣ j ^ 2)
  obtain ⟨i, rfl⟩ := h2
  have h3 : 3 * N = i ^ 2 := by nlinarith
  have h4 : 3 ∣ i := Nat.Prime.dvd_of_dvd_pow Nat.prime_three (⟨N, by rw [← h3]⟩ : 3 ∣ i ^ 2)
  obtain ⟨k, rfl⟩ := h4
  exact ⟨k, by nlinarith⟩

theorem kernel5 {N j : ℕ} (h : 5 * N = j ^ 2) : ∃ k : ℕ, N = 5 * k ^ 2 := by
  have h2 : 5 ∣ j := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) (⟨N, by rw [← h]⟩ : 5 ∣ j ^ 2)
  obtain ⟨k, rfl⟩ := h2
  exact ⟨k, by nlinarith⟩

theorem cos_two_pi_div_five : Real.cos (2 * π / 5) = (Real.sqrt 5 - 1) / 4 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [show 2 * π / 5 = 2 * (π / 5) by ring, Real.cos_two_mul, Real.cos_pi_div_five]
  nlinarith [h5]

/-- **T1 (Lemma Q, general `N`).** -/
theorem lemmaQ_general {N : ℕ} (hN : ¬ IsSquare N) {s : ℝ} (hs : s ^ 2 = N) {θ : ℝ}
    (hθ : ∃ r : ℚ, θ = r * π) (hθ0 : 0 < θ) (hθπ : θ < π) (hc : Row2.QMu s (Real.cos θ)) :
    (θ = π / 3 ∨ θ = π / 2 ∨ θ = π * (2 / 3)) ∨
    ((θ = π / 4 ∨ θ = π * (3 / 4)) ∧ ∃ k : ℕ, N = 2 * k ^ 2) ∨
    ((θ = π / 6 ∨ θ = π * (5 / 6)) ∧ ∃ k : ℕ, N = 3 * k ^ 2) ∨
    ((θ = π / 5 ∨ θ = π * (2 / 5) ∨ θ = π * (3 / 5) ∨ θ = π * (4 / 5)) ∧ ∃ k : ℕ, N = 5 * k ^ 2) := by
  have hpi := Real.pi_pos
  obtain ⟨a, b, U, W, hx, hUa, hWa, hle, hle'⟩ := t1_core hN hs hθ hc
  have hNpos : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; exact hN ⟨0, rfl⟩)
  have hirr : ∀ q : ℚ, s ≠ q := by
    intro q hsq'
    have habs : √(N : ℝ) = |(q : ℝ)| := by
      rw [← hsq', ← hs, Real.sqrt_sq_eq_abs]
    exact (irrational_sqrt_natCast_iff.mpr hN) ⟨|q|, by rw [habs]; push_cast; rfl⟩
  by_cases hb : b = 0
  · left
    have hcosq : ∃ q : ℚ, Real.cos θ = q := ⟨a / 2, by
      subst hb; push_cast at hx; push_cast; linarith⟩
    obtain ⟨r, hr⟩ := hθ
    have hmem := niven_angle_eq ⟨r, hr⟩ hcosq ⟨hθ0.le, hθπ.le⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h | h | h | h
    · exact absurd h hθ0.ne'
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd h hθπ.ne
  right
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  set x : ℝ := 2 * Real.cos θ with hxdef
  set x' : ℝ := (a : ℝ) - b * s with hx'
  have hxab : x = (a : ℝ) + b * s := hx
  have hsum : x + x' = U := by rw [hxab, hx', hUa]; ring
  have hprod : x * x' = W := by rw [hxab, hx', hWa]; linear_combination (-(b : ℝ) ^ 2) * hs
  have hdiff : x - x' = 2 * b * s := by rw [hxab, hx']; ring
  obtain ⟨D, hDdef⟩ : ∃ D : ℤ, D = U * U - 4 * W := ⟨_, rfl⟩
  have hDR : (D : ℝ) = (x - x') ^ 2 := by
    rw [hDdef]; push_cast
    have : (x - x') ^ 2 = (x + x') ^ 2 - 4 * (x * x') := by ring
    rw [this, hsum, hprod]; ring
  have hxx : |x| ≤ 2 := by rw [hxab]; exact hle
  have hxx' : |x'| ≤ 2 := hle'
  have hDpos : 0 < D := by
    have : (0 : ℝ) < (x - x') ^ 2 := by
      rw [hdiff]; have : 2 * (b : ℝ) * s ≠ 0 := by
        have hs0 : s ≠ 0 := by
          intro h0; apply hirr 0; simpa using h0
        positivity
      positivity
    exact_mod_cast hDR ▸ this
  have hDle : D ≤ 16 := by
    have h4 : |x - x'| ≤ 4 := (abs_sub _ _).trans (by linarith)
    have : (x - x') ^ 2 ≤ 16 := by
      have := sq_le_sq' (abs_le.mp h4).1 (abs_le.mp h4).2
      linarith
    have : (D : ℝ) ≤ 16 := by rw [hDR]; exact this
    exact_mod_cast this
  have hUb : -4 ≤ U ∧ U ≤ 4 := by
    have h1 := abs_le.mp hxx; have h2 := abs_le.mp hxx'
    have a1 : (U : ℝ) ≤ 4 := by rw [← hsum]; linarith
    have a2 : (-4 : ℝ) ≤ U := by rw [← hsum]; linarith
    exact ⟨by exact_mod_cast a2, by exact_mod_cast a1⟩
  have hp2 : 0 ≤ 4 - 2 * U + W := by
    have h1 := abs_le.mp hxx; have h2 := abs_le.mp hxx'
    have : (0 : ℝ) ≤ (2 - x) * (2 - x') := mul_nonneg (by linarith) (by linarith)
    have e : (2 - x) * (2 - x') = 4 - 2 * U + W := by rw [← hsum, ← hprod]; ring
    have : (0 : ℝ) ≤ 4 - 2 * U + W := by rw [← e]; exact this
    exact_mod_cast this
  have hm2 : 0 ≤ 4 + 2 * U + W := by
    have h1 := abs_le.mp hxx; have h2 := abs_le.mp hxx'
    have : (0 : ℝ) ≤ (2 + x) * (2 + x') := mul_nonneg (by linarith) (by linarith)
    have e : (2 + x) * (2 + x') = 4 + 2 * U + W := by rw [← hsum, ← hprod]; ring
    have : (0 : ℝ) ≤ 4 + 2 * U + W := by rw [← e]; exact this
    exact_mod_cast this
  have hnsq : ∀ m : ℤ, D ≠ m ^ 2 := by
    intro m hm
    have h1 : (2 * (b : ℝ) * s) ^ 2 = (m : ℝ) ^ 2 := by
      rw [← hdiff, ← hDR, hm]; push_cast; ring
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with e | e
    · apply hirr (m / (2 * b)); push_cast; field_simp; linarith
    · apply hirr (-m / (2 * b)); push_cast; field_simp; linarith
  have hn1 : D ≠ 1 := fun h => hnsq 1 (by rw [h]; norm_num)
  have hn4 : D ≠ 4 := fun h => hnsq 2 (by rw [h]; norm_num)
  have hn9 : D ≠ 9 := fun h => hnsq 3 (by rw [h]; norm_num)
  have hn16 : D ≠ 16 := fun h => hnsq 4 (by rw [h]; norm_num)
  have hW4 : 4 * W = U * U - D := by omega
  have hcases : (U = 0 ∧ D = 8) ∨ (U = 0 ∧ D = 12) ∨ (U = 1 ∧ D = 5) ∨ (U = -1 ∧ D = 5) := by
    obtain ⟨hU1, hU2⟩ := hUb
    interval_cases U <;> interval_cases D <;> omega
  -- the quantity N * D is a rational square
  have hND : ∀ d : ℕ, D = d → ∃ j : ℕ, d * N = j ^ 2 := by
    intro d hd
    refine nat_sq_of_rat (2 * b * N) ?_
    have h1 : (d : ℝ) = 4 * (b : ℝ) ^ 2 * N := by
      have : (D : ℝ) = d := by rw [hd]; simp
      rw [← this, hDR, hdiff]; linear_combination (4 * (b : ℝ) ^ 2) * hs
    push_cast
    rw [show ((2 : ℝ) * b * N) ^ 2 = (4 * (b : ℝ) ^ 2 * N) * N by ring, ← h1]
  have hxcos : Real.cos θ = x / 2 := by rw [hxdef]; ring
  rcases hcases with ⟨hU0, hD8⟩ | ⟨hU0, hD12⟩ | ⟨hU1, hD5⟩ | ⟨hU1, hD5⟩
  · -- x = ±√2
    left
    have hW : W = -2 := by rw [hU0, hD8] at hW4; omega
    have hx2 : x ^ 2 = 2 := by
      have hxx' : x' = -x := by
        have : (U : ℝ) = 0 := by rw [hU0]; simp
        linarith
      have : (W : ℝ) = -2 := by rw [hW]; simp
      rw [← hprod, hxx'] at this; linarith
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    obtain ⟨j, hj⟩ := hND 8 (by rw [hD8]; norm_num)
    refine ⟨?_, kernel2 hj⟩
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hx2.trans hs2.symm) with e | e
    · left
      refine theta_eq_of_cos hθ0.le hθπ.le (by positivity) (by linarith) ?_
      rw [hxcos, e, Real.cos_pi_div_four]
    · right
      refine theta_eq_of_cos hθ0.le hθπ.le (by positivity) (by linarith) ?_
      rw [show π * (3 / 4) = π - π / 4 by ring, Real.cos_pi_sub, Real.cos_pi_div_four, hxcos, e]; ring
  · right; left
    have hW : W = -3 := by rw [hU0, hD12] at hW4; omega
    have hx2 : x ^ 2 = 3 := by
      have hxx' : x' = -x := by
        have : (U : ℝ) = 0 := by rw [hU0]; simp
        linarith
      have : (W : ℝ) = -3 := by rw [hW]; simp
      rw [← hprod, hxx'] at this; linarith
    have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    obtain ⟨j, hj⟩ := hND 12 (by rw [hD12]; norm_num)
    refine ⟨?_, kernel3 hj⟩
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hx2.trans hs3.symm) with e | e
    · left
      refine theta_eq_of_cos hθ0.le hθπ.le (by positivity) (by linarith) ?_
      rw [hxcos, e, Real.cos_pi_div_six]
    · right
      refine theta_eq_of_cos hθ0.le hθπ.le (by positivity) (by linarith) ?_
      rw [show π * (5 / 6) = π - π / 6 by ring, Real.cos_pi_sub, Real.cos_pi_div_six, hxcos, e]; ring
  all_goals
    right; right
    have hW : W = -1 := by rw [hU1, hD5] at hW4; omega
    have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hq : x ^ 2 - U * x + W = 0 := by
      have : x' = U - x := by linarith
      rw [← hprod, this]; ring
    have hWR : (W : ℝ) = -1 := by rw [hW]; simp
    have hU2 : (U : ℝ) ^ 2 = 1 := by rw [hU1]; norm_num
    have hroot : x = (U + Real.sqrt 5) / 2 ∨ x = (U - Real.sqrt 5) / 2 := by
      have h : (x - (U + Real.sqrt 5) / 2) * (x - (U - Real.sqrt 5) / 2) = 0 := by
        linear_combination hq - hWR + (1 / 4) * hU2 - (1 / 4) * h5
      rcases mul_eq_zero.mp h with h | h
      · left; linarith
      · right; linarith
    obtain ⟨j, hj⟩ := hND 5 (by rw [hD5]; norm_num)
    refine ⟨?_, kernel5 hj⟩
    have c5 := Real.cos_pi_div_five
    have c25 := cos_two_pi_div_five
    have hr5 : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
    have hUR : (U : ℝ) = 1 ∨ (U : ℝ) = -1 := by
      have : U = 1 ∨ U = -1 := by omega
      rcases this with h | h
      · left; rw [h]; simp
      · right; rw [h]; simp
    rcases hUR with hu | hu <;> rcases hroot with e | e
    · left
      refine theta_eq_of_cos hθ0.le hθπ.le (by positivity) (by linarith) ?_
      rw [hxcos, e, hu, Real.cos_pi_div_five]; ring
    · right; right; left
      refine theta_eq_of_cos hθ0.le hθπ.le (by positivity) (by linarith) ?_
      rw [show π * (3 / 5) = π - 2 * π / 5 by ring, Real.cos_pi_sub, c25, hxcos, e, hu]; ring
    · right; left
      refine theta_eq_of_cos hθ0.le hθπ.le (by positivity) (by linarith) ?_
      rw [show π * (2 / 5) = 2 * π / 5 by ring, c25, hxcos, e, hu]; ring
    · right; right; right
      refine theta_eq_of_cos hθ0.le hθπ.le (by positivity) (by linarith) ?_
      rw [show π * (4 / 5) = π - π / 5 by ring, Real.cos_pi_sub, c5, hxcos, e, hu]; ring

/-- Non-vacuity of T1's hypotheses: `N = 5`, `θ = π/5`, `cos θ = 1/4 + (1/4)√5`; the conclusion's third family. -/
theorem lemmaQ_general_witness :
    ∃ (N : ℕ) (s θ : ℝ), ¬ IsSquare N ∧ s ^ 2 = N ∧ (∃ r : ℚ, θ = r * π) ∧ 0 < θ ∧ θ < π ∧
      Row2.QMu s (Real.cos θ) := by
  have hpi := Real.pi_pos
  have h5ns : ¬ IsSquare 5 := by
    rintro ⟨m, hm⟩
    have : m ≤ 2 := by nlinarith
    interval_cases m <;> omega
  refine ⟨5, Real.sqrt 5, π / 5, h5ns, by rw [Real.sq_sqrt (by norm_num)]; norm_num,
    ⟨1 / 5, by push_cast; ring⟩, by positivity, by linarith, 1 / 4, 1 / 4, ?_⟩
  rw [Real.cos_pi_div_five]; push_cast; ring

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.lemmaQ_general
#print axioms Erdos634.Draft.LaczFormal.lemmaQ_general_witness
