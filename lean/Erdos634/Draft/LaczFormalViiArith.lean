-- Draft/LaczFormalViiArith.lean -- exact arithmetic for case (vii) of Laczkovich 1995 Thm 5.1 (isosceles right target (pi/4,pi/4,pi/2)):
--   * Q-independence of 1, sqrt2, sqrt3, sqrt6 and of 1, sqrt2, b (b = sin(pi/8), b^2 = (2-sqrt2)/4);
--   * the three arithmetic contradictions (n = 8 (1,2,5); n = 12 (3,4,5); n = 12 (1,3,8)) from the leg word, the hypotenuse word and the area identity.
-- UNAUDITED.  Credit: Laczkovich (1995; "similar arguments" p. 94).  The obstructions were found by exact computation ((private working notes, not included)).
import Mathlib

namespace Erdos634.Draft.LaczFormal

/-- `ℚ`-independence of `1, √2`. -/
theorem r2_indep {p q : ℚ} (h : (p : ℝ) + q * Real.sqrt 2 = 0) : p = 0 ∧ q = 0 := by
  by_cases hq : q = 0
  · subst hq; simp at h; exact ⟨by exact_mod_cast h, rfl⟩
  · exfalso
    have hirr := irrational_sqrt_two
    apply hirr
    refine ⟨-p / q, ?_⟩
    have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    push_cast
    field_simp
    linarith

theorem no_rat_sq_two (y : ℚ) : y ^ 2 ≠ 2 := by
  intro h
  apply irrational_sqrt_two
  refine ⟨|y|, ?_⟩
  have : ((|y| : ℚ) : ℝ) ^ 2 = 2 := by
    rw [Rat.cast_abs, sq_abs]; exact_mod_cast h
  have h0 : (0 : ℝ) ≤ ((|y| : ℚ) : ℝ) := by exact_mod_cast abs_nonneg y
  rw [← Real.sqrt_sq h0, this]

theorem nsq3 : ¬ IsSquare (3 : ℕ) := by
  rintro ⟨k, hk⟩
  have : k ≤ 3 := by nlinarith
  interval_cases k <;> omega

theorem nsq6 : ¬ IsSquare (6 : ℕ) := by
  rintro ⟨k, hk⟩
  have : k ≤ 6 := by nlinarith
  interval_cases k <;> omega

theorem no_rat_sq_three (y : ℚ) : y ^ 2 ≠ 3 := by
  intro h
  have : Irrational (Real.sqrt 3) := by
    have := (irrational_sqrt_natCast_iff (n := 3)).mpr nsq3
    simpa using this
  apply this
  refine ⟨|y|, ?_⟩
  have h2 : ((|y| : ℚ) : ℝ) ^ 2 = 3 := by
    rw [Rat.cast_abs, sq_abs]; exact_mod_cast h
  have h0 : (0 : ℝ) ≤ ((|y| : ℚ) : ℝ) := by exact_mod_cast abs_nonneg y
  rw [← Real.sqrt_sq h0, h2]

theorem no_rat_sq_six (y : ℚ) : y ^ 2 ≠ 6 := by
  intro h
  have : Irrational (Real.sqrt 6) := by
    have := (irrational_sqrt_natCast_iff (n := 6)).mpr nsq6
    simpa using this
  apply this
  refine ⟨|y|, ?_⟩
  have h2 : ((|y| : ℚ) : ℝ) ^ 2 = 6 := by
    rw [Rat.cast_abs, sq_abs]; exact_mod_cast h
  have h0 : (0 : ℝ) ≤ ((|y| : ℚ) : ℝ) := by exact_mod_cast abs_nonneg y
  rw [← Real.sqrt_sq h0, h2]

/-- `ℚ`-independence of `1, √2, √3, √6`. -/
theorem indep4 {p q r s : ℚ}
    (h : (p : ℝ) + q * Real.sqrt 2 + r * Real.sqrt 3 + s * Real.sqrt 6 = 0) :
    p = 0 ∧ q = 0 ∧ r = 0 ∧ s = 0 := by
  have s2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have s3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have s6 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  rw [s6] at h
  -- (p + q√2) = -√3 (r + s√2)
  have hB : r = 0 ∧ s = 0 := by
    by_contra hB
    have hn : (r ^ 2 - 2 * s ^ 2 : ℚ) ≠ 0 := by
      intro hz
      by_cases hs : s = 0
      · subst hs; apply hB; refine ⟨?_, rfl⟩; nlinarith
      · apply no_rat_sq_two (r / s)
        field_simp; linarith
    -- (p+q√2)(r - s√2) = a + b√2 with a = pr - 2qs, b = qr - ps ; divide by n
    set a : ℚ := (p * r - 2 * q * s) / (r ^ 2 - 2 * s ^ 2) with ha
    set b : ℚ := (q * r - p * s) / (r ^ 2 - 2 * s ^ 2) with hb
    have e1 : a * r + 2 * b * s = p := by rw [ha, hb]; field_simp; ring
    have e2 : a * s + b * r = q := by rw [ha, hb]; field_simp; ring
    have hBne : ((r : ℝ) + s * Real.sqrt 2) ≠ 0 := by
      intro hz
      exact hB (r2_indep (p := r) (q := s) hz)
    have hu : ((p : ℝ) + q * Real.sqrt 2) = -Real.sqrt 3 * ((r : ℝ) + s * Real.sqrt 2) := by
      linear_combination h
    have key : (a : ℝ) + b * Real.sqrt 2 = -Real.sqrt 3 := by
      apply mul_right_cancel₀ hBne
      have e1' : (a : ℝ) * r + 2 * b * s = p := by exact_mod_cast e1
      have e2' : (a : ℝ) * s + b * r = q := by exact_mod_cast e2
      rw [← hu]
      linear_combination e1' + (Real.sqrt 2) * e2' + (b * s : ℝ) * s2
    have k2 : ((a : ℝ) + b * Real.sqrt 2) ^ 2 = 3 := by rw [key]; linear_combination s3
    have sq : (((a ^ 2 + 2 * b ^ 2 - 3 : ℚ)) : ℝ) + ((2 * a * b : ℚ) : ℝ) * Real.sqrt 2 = 0 := by
      push_cast
      linear_combination k2 - (b : ℝ) ^ 2 * s2
    obtain ⟨c1, c2⟩ := r2_indep sq
    have hab : a = 0 ∨ b = 0 := by
      rcases mul_eq_zero.mp (show a * b = 0 by linarith) with h | h
      · exact Or.inl h
      · exact Or.inr h
    rcases hab with h0 | h0
    · apply no_rat_sq_six (2 * b); rw [h0] at c1; nlinarith
    · apply no_rat_sq_three a; rw [h0] at c1; nlinarith
  obtain ⟨hr, hs⟩ := hB
  subst hr; subst hs
  simp at h
  obtain ⟨h1, h2⟩ := r2_indep h
  exact ⟨h1, h2, rfl, rfl⟩

/-- Case (vii), `n = 12`, tile `(3,4,5)π/12`: the hypotenuse word and the leg word of the target are incompatible (all coordinates vanish). -/
theorem vii12a_arith {ρ : ℝ} {X0 X1 X2 Z0 Z1 Z2 : ℕ} (hρ : 0 < ρ)
    (e1 : ρ * (Real.sqrt 2 / 2) = X0 * (Real.sqrt 2 / 2) + X1 * (Real.sqrt 3 / 2) +
      X2 * ((Real.sqrt 6 + Real.sqrt 2) / 4))
    (e2 : ρ = Z0 * (Real.sqrt 2 / 2) + Z1 * (Real.sqrt 3 / 2) + Z2 * ((Real.sqrt 6 + Real.sqrt 2) / 4)) :
    False := by
  have s2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have s3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have s6 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  rw [s6] at e1 e2
  have hρ1 : ρ = X0 + X2 / 2 + X2 * Real.sqrt 3 / 2 + X1 * (Real.sqrt 2 * Real.sqrt 3) / 2 := by
    linear_combination Real.sqrt 2 * e1 + (-ρ / 2 + X0 / 2 + X2 * Real.sqrt 3 / 4 + X2 / 4) * s2
  have hsum : (((X0 : ℚ) + X2 / 2 : ℚ) : ℝ) + ((-(Z0 : ℚ) / 2 - Z2 / 4 : ℚ) : ℝ) * Real.sqrt 2 +
      (((X2 : ℚ) / 2 - Z1 / 2 : ℚ) : ℝ) * Real.sqrt 3 + (((X1 : ℚ) / 2 - Z2 / 4 : ℚ) : ℝ) * Real.sqrt 6 = 0 := by
    rw [s6]; push_cast
    linear_combination e2 - hρ1
  obtain ⟨c1, c2, c3, c4⟩ := indep4 hsum
  have h0 : (0 : ℚ) ≤ X0 := Nat.cast_nonneg _
  have h1 : (0 : ℚ) ≤ X1 := Nat.cast_nonneg _
  have h2 : (0 : ℚ) ≤ X2 := Nat.cast_nonneg _
  have h3 : (0 : ℚ) ≤ Z0 := Nat.cast_nonneg _
  have h4 : (0 : ℚ) ≤ Z1 := Nat.cast_nonneg _
  have h5 : (0 : ℚ) ≤ Z2 := Nat.cast_nonneg _
  have x0 : (X0 : ℚ) = 0 := by linarith
  have x2 : (X2 : ℚ) = 0 := by linarith
  have z2 : (Z2 : ℚ) = 0 := by linarith
  have z0 : (Z0 : ℚ) = 0 := by linarith
  have z1 : (Z1 : ℚ) = 0 := by linarith
  have x1 : (X1 : ℚ) = 0 := by linarith
  have x0' : (X0 : ℝ) = 0 := by exact_mod_cast x0
  have x1' : (X1 : ℝ) = 0 := by exact_mod_cast x1
  have x2' : (X2 : ℝ) = 0 := by exact_mod_cast x2
  rw [x0', x1', x2'] at hρ1
  linarith

/-- Case (vii), `n = 12`, tile `(1,3,8)π/12`: the area identity then has a `√3`-coordinate `N/4 ≠ 0`. -/
theorem vii12b_arith {ρ : ℝ} {N X0 X1 X2 Z0 Z1 Z2 : ℕ} (hN : 0 < N) (hρ : 0 < ρ)
    (e1 : ρ * (Real.sqrt 2 / 2) = X0 * ((Real.sqrt 6 - Real.sqrt 2) / 4) + X1 * (Real.sqrt 2 / 2) +
      X2 * (Real.sqrt 3 / 2))
    (e2 : ρ = Z0 * ((Real.sqrt 6 - Real.sqrt 2) / 4) + Z1 * (Real.sqrt 2 / 2) + Z2 * (Real.sqrt 3 / 2))
    (e3 : ρ ^ 2 = 2 * N * (((Real.sqrt 6 - Real.sqrt 2) / 4) * (Real.sqrt 2 / 2) * (Real.sqrt 3 / 2))) :
    False := by
  have s2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have s3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have s6 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  rw [s6] at e1 e2 e3
  have hρ1 : ρ = -(X0 : ℝ) / 2 + X1 + X0 * Real.sqrt 3 / 2 + X2 * (Real.sqrt 2 * Real.sqrt 3) / 2 := by
    linear_combination Real.sqrt 2 * e1 + (-ρ / 2 + (X0 : ℝ) / 4 * Real.sqrt 3 - X0 / 4 + X1 / 2 +
      X2 * Real.sqrt 3 / 4 * 0) * s2
  have hsum : (((-(X0 : ℚ) / 2 + X1 : ℚ)) : ℝ) + ((((Z0 : ℚ) / 4 - Z1 / 2 : ℚ)) : ℝ) * Real.sqrt 2 +
      ((((X0 : ℚ) / 2 - Z2 / 2 : ℚ)) : ℝ) * Real.sqrt 3 + ((((X2 : ℚ) / 2 - Z0 / 4 : ℚ)) : ℝ) * Real.sqrt 6 = 0 := by
    rw [s6]; push_cast
    linear_combination e2 - hρ1
  obtain ⟨c1, c2, c3, c4⟩ := indep4 hsum
  have hX0 : (X0 : ℝ) = 2 * X1 := by
    have : (X0 : ℚ) = 2 * X1 := by linarith
    exact_mod_cast this
  have hρ2 : ρ = X1 * Real.sqrt 3 + X2 * (Real.sqrt 2 * Real.sqrt 3) / 2 := by
    rw [hρ1, hX0]; ring
  rw [hρ2] at e3
  have hsum3 : (((3 * (X1 : ℚ) ^ 2 + 3 * (X2 : ℚ) ^ 2 / 2 - 3 * (N : ℚ) / 4 : ℚ)) : ℝ) +
      (((3 * (X1 : ℚ) * X2 : ℚ)) : ℝ) * Real.sqrt 2 + ((((N : ℚ) / 4 : ℚ)) : ℝ) * Real.sqrt 3 +
      (((0 : ℚ)) : ℝ) * Real.sqrt 6 = 0 := by
    rw [s6]; push_cast
    linear_combination e3 - ((X1 : ℝ) ^ 2 + X1 * X2 * Real.sqrt 2 + X2 ^ 2 * Real.sqrt 2 ^ 2 / 4 -
      N * Real.sqrt 2 ^ 2 / 8) * s3 - (3 * (X2 : ℝ) ^ 2 / 4 - 3 * N / 8 + N * Real.sqrt 3 / 8) * s2
  obtain ⟨-, -, d3, -⟩ := indep4 hsum3
  have : (N : ℚ) = 0 := by linarith
  have : N = 0 := by exact_mod_cast this
  omega

/-- `b = sin(π/8)` (`b² = (2-√2)/4`) is not in `ℚ(√2)`. -/
theorem b_irr8 {b : ℝ} (hb2 : b ^ 2 = (2 - Real.sqrt 2) / 4) {p3 q3 p2 q2 : ℚ}
    (h : ((p3 : ℝ) + q3 * Real.sqrt 2) * b = p2 + q2 * Real.sqrt 2) : p3 = 0 ∧ q3 = 0 := by
  have s2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  by_contra hne
  have hn : (p3 ^ 2 - 2 * q3 ^ 2 : ℚ) ≠ 0 := by
    intro hz
    by_cases hq : q3 = 0
    · subst hq; apply hne; refine ⟨?_, rfl⟩; nlinarith
    · apply no_rat_sq_two (p3 / q3)
      field_simp; linarith
  set P : ℚ := (p2 * p3 - 2 * q2 * q3) / (p3 ^ 2 - 2 * q3 ^ 2) with hP
  set Q : ℚ := (q2 * p3 - p2 * q3) / (p3 ^ 2 - 2 * q3 ^ 2) with hQ
  have hn' : ((p3 : ℝ) ^ 2 - 2 * (q3 : ℝ) ^ 2) ≠ 0 := by exact_mod_cast hn
  have hPe : (P : ℝ) * ((p3 : ℝ) ^ 2 - 2 * (q3 : ℝ) ^ 2) = p2 * p3 - 2 * q2 * q3 := by
    rw [hP]; push_cast; rw [div_mul_cancel₀ _ hn']
  have hQe : (Q : ℝ) * ((p3 : ℝ) ^ 2 - 2 * (q3 : ℝ) ^ 2) = q2 * p3 - p2 * q3 := by
    rw [hQ]; push_cast; rw [div_mul_cancel₀ _ hn']
  have hb : b = P + Q * Real.sqrt 2 := by
    apply mul_left_cancel₀ hn'
    linear_combination ((p3 : ℝ) - q3 * Real.sqrt 2) * h + ((q3 : ℝ) ^ 2 * b - q3 * q2) * s2 -
      hPe - Real.sqrt 2 * hQe
  have hb2' : ((P : ℝ) + Q * Real.sqrt 2) ^ 2 = (2 - Real.sqrt 2) / 4 := by rw [← hb]; exact hb2
  have sq : (((P ^ 2 + 2 * Q ^ 2 - 1 / 2 : ℚ)) : ℝ) + (((2 * P * Q + 1 / 4 : ℚ)) : ℝ) * Real.sqrt 2 = 0 := by
    push_cast
    linear_combination hb2' - (Q : ℝ) ^ 2 * s2
  obtain ⟨c1, c2⟩ := r2_indep sq
  apply no_rat_sq_two (8 * P ^ 2 - 2)
  have : 32 * P ^ 4 - 16 * P ^ 2 + 1 = 0 := by
    linear_combination 32 * P ^ 2 * c1 - 4 * (8 * P * Q - 1) * c2
  nlinarith

/-- Case (vii), `n = 8`, tile `(1,2,5)π/8` (`b = sin(π/8)`, `sin(2π/8) = √2/2`, `sin(5π/8) = (1+√2) b`). -/
theorem vii8_arith {ρ b : ℝ} {N X0 X1 X2 Z0 Z1 Z2 : ℕ} (hN : 0 < N) (hρ : 0 < ρ) (hb : 0 < b)
    (hb2 : b ^ 2 = (2 - Real.sqrt 2) / 4)
    (e1 : ρ * (Real.sqrt 2 / 2) = X0 * b + X1 * (Real.sqrt 2 / 2) + X2 * ((1 + Real.sqrt 2) * b))
    (e2 : ρ = Z0 * b + Z1 * (Real.sqrt 2 / 2) + Z2 * ((1 + Real.sqrt 2) * b))
    (e3 : ρ ^ 2 = 2 * N * (b * (Real.sqrt 2 / 2) * ((1 + Real.sqrt 2) * b))) : False := by
  have s2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hρ1 : ρ = b * (Real.sqrt 2 * (X0 + X2) + 2 * X2) + X1 := by
    linear_combination Real.sqrt 2 * e1 + (-ρ / 2 + (X1 : ℝ) / 2 + X2 * b) * s2
  have hlin : (((2 * (X2 : ℚ) - Z0 - Z2 : ℚ)) + (((X0 : ℚ) + X2 - Z2 : ℚ)) * Real.sqrt 2 : ℝ) * b =
      (((-(X1 : ℚ)) : ℚ) : ℝ) + (((Z1 : ℚ) / 2 : ℚ) : ℝ) * Real.sqrt 2 := by
    push_cast
    linear_combination e2 - hρ1
  obtain ⟨hp3, hq3⟩ := b_irr8 hb2 (p3 := 2 * (X2 : ℚ) - Z0 - Z2) (q3 := (X0 : ℚ) + X2 - Z2)
    (p2 := -(X1 : ℚ)) (q2 := (Z1 : ℚ) / 2) (by push_cast; linear_combination e2 - hρ1)
  have hv : (((-(X1 : ℚ)) : ℚ) : ℝ) + (((Z1 : ℚ) / 2 : ℚ) : ℝ) * Real.sqrt 2 = 0 := by
    rw [← hlin]
    have : ((2 * (X2 : ℚ) - Z0 - Z2 : ℚ) : ℝ) = 0 := by rw [hp3]; simp
    have h2 : (((X0 : ℚ) + X2 - Z2 : ℚ) : ℝ) = 0 := by rw [hq3]; simp
    rw [this, h2]; simp
  obtain ⟨hx1, -⟩ := r2_indep hv
  have hX1 : (X1 : ℝ) = 0 := by
    have : (X1 : ℚ) = 0 := by linarith
    exact_mod_cast this
  rw [hX1] at hρ1
  set W : ℝ := X0 + X2 + X2 * Real.sqrt 2 with hW
  have hρW : ρ = Real.sqrt 2 * b * W := by
    rw [hρ1, hW]; linear_combination (-(X2 : ℝ) * b) * s2
  have hbsq : 0 < b ^ 2 := by positivity
  have hmain : 2 * W ^ 2 = N * (Real.sqrt 2 + 2) := by
    apply mul_left_cancel₀ hbsq.ne'
    rw [hρW] at e3
    linear_combination e3 + (-(b ^ 2) * W ^ 2 + N * b ^ 2) * s2
  -- coordinates: 2W^2 = N(√2+2) with W = p + x√2
  have hcoord : (((2 * ((X0 : ℚ) + X2) ^ 2 + 4 * (X2 : ℚ) ^ 2 - 2 * N : ℚ)) : ℝ) +
      (((4 * ((X0 : ℚ) + X2) * X2 - N : ℚ)) : ℝ) * Real.sqrt 2 = 0 := by
    push_cast
    rw [hW] at hmain
    linear_combination hmain - 2 * (X2 : ℝ) ^ 2 * s2
  obtain ⟨d1, d2⟩ := r2_indep hcoord
  by_cases hx : (X2 : ℚ) = 0
  · have : (N : ℚ) = 0 := by rw [hx] at d2; linarith
    have : N = 0 := by exact_mod_cast this
    omega
  · apply no_rat_sq_two ((((X0 : ℚ) + X2) - 2 * X2) / X2)
    field_simp
    nlinarith

end Erdos634.Draft.LaczFormal
