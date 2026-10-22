-- Draft/LaczFormalGraphArith30.lean -- exact arithmetic for the n = 30 equilateral-target tiles: Q-independence of 1, sqrt5, sqrt3, sqrt15, and the vanishing of
-- (r-p) sqrt3 e = (r+p) f + q sqrt3 for the two constants e^2 = (5 -+ sqrt5)/8, f = (sqrt5 +- 1)/4.  UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Thm 3.3 (5)).
import Erdos634.Draft.LaczFormalViiArith

namespace Erdos634.Draft.LaczFormal

theorem nsq5 : ¬ IsSquare (5 : ℕ) := by
  rintro ⟨k, hk⟩
  have : k ≤ 5 := by nlinarith
  interval_cases k <;> omega

theorem nsq15 : ¬ IsSquare (15 : ℕ) := by
  rintro ⟨k, hk⟩
  have : k ≤ 15 := by nlinarith
  interval_cases k <;> omega

theorem irr_sqrt5 : Irrational (Real.sqrt 5) := by
  have := (irrational_sqrt_natCast_iff (n := 5)).mpr nsq5
  simpa using this

theorem r5_indep {p q : ℚ} (h : (p : ℝ) + q * Real.sqrt 5 = 0) : p = 0 ∧ q = 0 := by
  by_cases hq : q = 0
  · subst hq; simp at h; exact ⟨by exact_mod_cast h, rfl⟩
  · exfalso
    apply irr_sqrt5
    refine ⟨-p / q, ?_⟩
    have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    push_cast
    field_simp
    linarith

theorem no_rat_sq_five (y : ℚ) : y ^ 2 ≠ 5 := by
  intro h
  apply irr_sqrt5
  refine ⟨|y|, ?_⟩
  have : ((|y| : ℚ) : ℝ) ^ 2 = 5 := by
    rw [Rat.cast_abs, sq_abs]; exact_mod_cast h
  have h0 : (0 : ℝ) ≤ ((|y| : ℚ) : ℝ) := by exact_mod_cast abs_nonneg y
  rw [← Real.sqrt_sq h0, this]

theorem no_rat_sq_fifteen (y : ℚ) : y ^ 2 ≠ 15 := by
  intro h
  have : Irrational (Real.sqrt 15) := by
    have := (irrational_sqrt_natCast_iff (n := 15)).mpr nsq15
    simpa using this
  apply this
  refine ⟨|y|, ?_⟩
  have h2 : ((|y| : ℚ) : ℝ) ^ 2 = 15 := by
    rw [Rat.cast_abs, sq_abs]; exact_mod_cast h
  have h0 : (0 : ℝ) ≤ ((|y| : ℚ) : ℝ) := by exact_mod_cast abs_nonneg y
  rw [← Real.sqrt_sq h0, h2]

/-- `ℚ`-independence of `1, √5, √3, √15`. -/
theorem indep_5_3 {p q r s : ℚ}
    (h : (p : ℝ) + q * Real.sqrt 5 + r * Real.sqrt 3 + s * Real.sqrt 15 = 0) :
    p = 0 ∧ q = 0 ∧ r = 0 ∧ s = 0 := by
  have s5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have s3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have s15 : Real.sqrt 15 = Real.sqrt 5 * Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  rw [s15] at h
  have hB : r = 0 ∧ s = 0 := by
    by_contra hB
    have hn : (r ^ 2 - 5 * s ^ 2 : ℚ) ≠ 0 := by
      intro hz
      by_cases hs : s = 0
      · subst hs; apply hB; refine ⟨?_, rfl⟩; nlinarith
      · apply no_rat_sq_five (r / s)
        field_simp; linarith
    set a : ℚ := (p * r - 5 * q * s) / (r ^ 2 - 5 * s ^ 2) with ha
    set b : ℚ := (q * r - p * s) / (r ^ 2 - 5 * s ^ 2) with hb
    have e1 : a * r + 5 * b * s = p := by rw [ha, hb]; field_simp; ring
    have e2 : a * s + b * r = q := by rw [ha, hb]; field_simp; ring
    have hBne : ((r : ℝ) + s * Real.sqrt 5) ≠ 0 := by
      intro hz
      exact hB (r5_indep (p := r) (q := s) hz)
    have hu : ((p : ℝ) + q * Real.sqrt 5) = -Real.sqrt 3 * ((r : ℝ) + s * Real.sqrt 5) := by
      linear_combination h
    have key : (a : ℝ) + b * Real.sqrt 5 = -Real.sqrt 3 := by
      apply mul_right_cancel₀ hBne
      have e1' : (a : ℝ) * r + 5 * b * s = p := by exact_mod_cast e1
      have e2' : (a : ℝ) * s + b * r = q := by exact_mod_cast e2
      rw [← hu]
      linear_combination e1' + (Real.sqrt 5) * e2' + (b * s : ℝ) * s5
    have k2 : ((a : ℝ) + b * Real.sqrt 5) ^ 2 = 3 := by rw [key]; linear_combination s3
    have sq : (((a ^ 2 + 5 * b ^ 2 - 3 : ℚ)) : ℝ) + ((2 * a * b : ℚ) : ℝ) * Real.sqrt 5 = 0 := by
      push_cast
      linear_combination k2 - (b : ℝ) ^ 2 * s5
    obtain ⟨c1, c2⟩ := r5_indep sq
    have hab : a = 0 ∨ b = 0 := by
      rcases mul_eq_zero.mp (show a * b = 0 by linarith) with h | h
      · exact Or.inl h
      · exact Or.inr h
    rcases hab with h0 | h0
    · apply no_rat_sq_fifteen (5 * b); rw [h0] at c1; nlinarith
    · apply no_rat_sq_three a; rw [h0] at c1; nlinarith
  obtain ⟨hr, hs⟩ := hB
  subst hr; subst hs
  simp at h
  obtain ⟨h1, h2⟩ := r5_indep h
  exact ⟨h1, h2, rfl, rfl⟩

theorem rel30_a_Q (X Y Z : ℚ) (e : ℝ) (he : e ^ 2 = (5 - Real.sqrt 5) / 8)
    (h : (X : ℝ) * (Real.sqrt 3 * e) = Y * ((1 + Real.sqrt 5) / 4) + Z * Real.sqrt 3) : X = 0 ∧ Y = 0 ∧ Z = 0 := by
  have s5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have s3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have s15 : Real.sqrt 15 = Real.sqrt 5 * Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have hsq : ((X : ℝ) * (Real.sqrt 3 * e)) ^ 2 = ((Y : ℝ) * ((1 + Real.sqrt 5) / 4) + Z * Real.sqrt 3) ^ 2 := by rw [h]
  have hind : (((15 * X ^ 2 / 8 - 3 * Y ^ 2 / 8 - 3 * Z ^ 2 : ℚ)) : ℝ) + ((-3 * X ^ 2 / 8 - Y ^ 2 / 8 : ℚ) : ℝ) * Real.sqrt 5 +
      ((-(Y * Z) / 2 : ℚ) : ℝ) * Real.sqrt 3 + ((-(Y * Z) / 2 : ℚ) : ℝ) * Real.sqrt 15 = 0 := by
    rw [s15]
    push_cast
    linear_combination hsq - ((X : ℝ) ^ 2 * e ^ 2 - (Z : ℝ) ^ 2) * s3 - 3 * (X : ℝ) ^ 2 * he + ((Y : ℝ) ^ 2 / 16) * s5
  obtain ⟨c0, c1, c2, c3⟩ := indep_5_3 hind
  have hX : X = 0 := by nlinarith [sq_nonneg X, sq_nonneg Y]
  have hY : Y = 0 := by nlinarith [sq_nonneg X, sq_nonneg Y]
  refine ⟨hX, hY, ?_⟩
  subst hX; subst hY
  nlinarith [sq_nonneg Z]

theorem rel30_b_Q (X Y Z : ℚ) (e : ℝ) (he : e ^ 2 = (5 + Real.sqrt 5) / 8)
    (h : (X : ℝ) * (Real.sqrt 3 * e) = Y * ((Real.sqrt 5 - 1) / 4) + Z * Real.sqrt 3) : X = 0 ∧ Y = 0 ∧ Z = 0 := by
  have s5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have s3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have s15 : Real.sqrt 15 = Real.sqrt 5 * Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have hsq : ((X : ℝ) * (Real.sqrt 3 * e)) ^ 2 = ((Y : ℝ) * ((Real.sqrt 5 - 1) / 4) + Z * Real.sqrt 3) ^ 2 := by rw [h]
  have hind : (((15 * X ^ 2 / 8 - 3 * Y ^ 2 / 8 - 3 * Z ^ 2 : ℚ)) : ℝ) + ((3 * X ^ 2 / 8 + Y ^ 2 / 8 : ℚ) : ℝ) * Real.sqrt 5 +
      ((Y * Z / 2 : ℚ) : ℝ) * Real.sqrt 3 + ((-(Y * Z) / 2 : ℚ) : ℝ) * Real.sqrt 15 = 0 := by
    rw [s15]
    push_cast
    linear_combination hsq - ((X : ℝ) ^ 2 * e ^ 2 - (Z : ℝ) ^ 2) * s3 - 3 * (X : ℝ) ^ 2 * he + ((Y : ℝ) ^ 2 / 16) * s5
  obtain ⟨c0, c1, c2, c3⟩ := indep_5_3 hind
  have hX : X = 0 := by nlinarith [sq_nonneg X, sq_nonneg Y]
  have hY : Y = 0 := by nlinarith [sq_nonneg X, sq_nonneg Y]
  refine ⟨hX, hY, ?_⟩
  subst hX; subst hY
  nlinarith [sq_nonneg Z]

end Erdos634.Draft.LaczFormal
