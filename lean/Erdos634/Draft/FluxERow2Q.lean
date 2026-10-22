-- Draft/FluxERow2Q.lean — ROW 2, LEMMA Q ((private working notes, not included) §5 "Lemma Q (rational
-- angles)"): for a prime `p ≡ 3 (mod 4)`, `p ≥ 7`, an angle `θ ∈ (0, π)` that is a rational multiple
-- of `π` and has `cos θ ∈ ℚ(√p)` is one of `π/3`, `π/2`, `2π/3`.  Pure number theory; NOT imported
-- into All.lean.
--
-- ROUTE (the file's, with its two algebraic steps made elementary; named):
-- * `x = 2 cos θ` is an algebraic integer: Mathlib `Real.isIntegral_two_mul_cos_rat_mul_pi` (cited).
-- * write `x = a + b s` (`s² = p`, `a, b ∈ ℚ`) and `x' = a − b s`.  The file's "both are conjugates of
--   `x`" is replaced by two explicit facts: (i) `x'` is a root of every integer polynomial `x` is a
--   root of (`Row2.poly_conj`, induction on the polynomial), so `x'` is integral; (ii) `|x'| ≤ 2`:
--   with the Chebyshev-type sequence `Row2.cheb` (`cheb k (2cos θ) = 2cos kθ`,
--   `cheb k (t + t⁻¹) = t^k + t^{-k}`), `cheb n x = 2` for `n = 2·den`, conjugation gives
--   `cheb n x' = 2`, and `|y| > 2` would give `t^n + t^{-n} = 2` with `|t| > 1`.
-- * `x + x' = 2a` and `x x' = a² − b²p` are rational algebraic integers, hence integers `U, W`
--   (Mathlib `IsIntegral.exists_int_iff_exists_rat`); `V = 2b` has `pV² = U² − 4W ∈ ℤ`, hence `V ∈ ℤ`
--   (`p` prime); `|x − x'| ≤ 4` gives `pV² ≤ 16`, so `V ∈ {0, ±1}`, and `V = ±1` would make
--   `p = U² − 4W ≡ 0, 1 (mod 4)`.  So `b = 0`, `cos θ ∈ ℚ`, and Mathlib's Niven
--   (`niven_angle_eq`, cited) finishes.  The file's "integers of ℚ(√p) are ℤ[√p]" is not used.
-- * `Row2.lemmaQ` is stated for any `s` with `s² = p` (the similarity ratio `μ` of row 2).
--
-- Witness (Draft/FluxERow2QWitness.lean): `θ = π/3`, `p = 7`, `cos θ = 1/2 + 0·√7`.
--
-- Formalization debt; not progress on the three /goal outcomes.
import Mathlib.NumberTheory.Niven
import Erdos634.Draft.FluxDRow2K

open scoped Classical

namespace Erdos634.Geometry

open Real Polynomial

/-- The Chebyshev-type sequence `C₀ = 2`, `C₁ = z`, `C_{k+2} = z C_{k+1} − C_k`. -/
def Row2.cheb {R : Type*} [CommRing R] (z : R) : ℕ → R
  | 0 => 2
  | 1 => z
  | (k + 2) => z * Row2.cheb z (k + 1) - Row2.cheb z k

/-- `C_k(2 cos θ) = 2 cos kθ`. -/
theorem Row2.cheb_cos (θ : ℝ) : ∀ k : ℕ, Row2.cheb (2 * Real.cos θ) k = 2 * Real.cos (k * θ)
  | 0 => by simp [Row2.cheb]
  | 1 => by simp [Row2.cheb]
  | (k + 2) => by
      rw [Row2.cheb, Row2.cheb_cos θ (k + 1), Row2.cheb_cos θ k]
      have key : Real.cos (((k : ℝ) + 1) * θ + θ) + Real.cos (((k : ℝ) + 1) * θ - θ)
          = 2 * Real.cos (((k : ℝ) + 1) * θ) * Real.cos θ := by
        rw [Real.cos_add, Real.cos_sub]; ring
      have e1 : ((k : ℝ) + 1) * θ + θ = ((k + 2 : ℕ) : ℝ) * θ := by push_cast; ring
      have e2 : ((k : ℝ) + 1) * θ - θ = (k : ℝ) * θ := by ring
      rw [e1, e2] at key
      push_cast at key ⊢
      linear_combination (-2 : ℝ) * key

/-- `C_k(t + t⁻¹) = t^k + t^{-k}`. -/
theorem Row2.cheb_add_inv (t : ℝ) (ht : t ≠ 0) :
    ∀ k : ℕ, Row2.cheb (t + t⁻¹) k = t ^ k + t⁻¹ ^ k
  | 0 => by simp [Row2.cheb]; norm_num
  | 1 => by simp [Row2.cheb]
  | (k + 2) => by
      rw [Row2.cheb, Row2.cheb_add_inv t ht (k + 1), Row2.cheb_add_inv t ht k]
      have h : t * t⁻¹ = 1 := mul_inv_cancel₀ ht
      linear_combination (t ^ k + t⁻¹ ^ k) * h

/-- **Conjugation commutes with `C_k`** on `ℚ + ℚ s`, `s² = p`. -/
theorem Row2.cheb_conj {s : ℝ} {p : ℚ} (hs : s ^ 2 = p) (a b : ℚ) :
    ∀ k : ℕ, ∃ A B : ℚ, Row2.cheb ((a : ℝ) + b * s) k = A + B * s ∧
      Row2.cheb ((a : ℝ) - b * s) k = A - B * s
  | 0 => ⟨2, 0, by simp [Row2.cheb], by simp [Row2.cheb]⟩
  | 1 => ⟨a, b, by simp [Row2.cheb], by simp [Row2.cheb]⟩
  | (k + 2) => by
      obtain ⟨A1, B1, h1, h1'⟩ := Row2.cheb_conj hs a b (k + 1)
      obtain ⟨A0, B0, h0, h0'⟩ := Row2.cheb_conj hs a b k
      refine ⟨a * A1 + b * B1 * p - A0, a * B1 + b * A1 - B0, ?_, ?_⟩
      · rw [Row2.cheb, h1, h0]; push_cast; linear_combination ((b : ℝ) * B1) * hs
      · rw [Row2.cheb, h1', h0']; push_cast; linear_combination ((b : ℝ) * B1) * hs

/-- **Conjugation commutes with integer polynomials** on `ℚ + ℚ s`, `s² = p`. -/
theorem Row2.poly_conj {s : ℝ} {p : ℚ} (hs : s ^ 2 = p) (a b : ℚ) (P : ℤ[X]) :
    ∃ A B : ℚ, P.eval₂ (algebraMap ℤ ℝ) ((a : ℝ) + b * s) = A + B * s ∧
      P.eval₂ (algebraMap ℤ ℝ) ((a : ℝ) - b * s) = A - B * s := by
  induction P using Polynomial.induction_on with
  | C c => exact ⟨c, 0, by rw [Polynomial.eval₂_C]; simp, by rw [Polynomial.eval₂_C]; simp⟩
  | add P Q hP hQ =>
    obtain ⟨A1, B1, h1, h1'⟩ := hP
    obtain ⟨A2, B2, h2, h2'⟩ := hQ
    refine ⟨A1 + A2, B1 + B2, ?_, ?_⟩
    · rw [Polynomial.eval₂_add, h1, h2]; push_cast; ring
    · rw [Polynomial.eval₂_add, h1', h2']; push_cast; ring
  | monomial n c h =>
    obtain ⟨A, B, h1, h1'⟩ := h
    have hstep : ∀ z : ℝ, (C c * X ^ (n + 1)).eval₂ (algebraMap ℤ ℝ) z
        = (C c * X ^ n).eval₂ (algebraMap ℤ ℝ) z * z := by
      intro z; simp [Polynomial.eval₂_mul, pow_succ, mul_assoc]
    refine ⟨A * a + B * b * p, A * b + B * a, ?_, ?_⟩
    · rw [hstep, h1]; push_cast; linear_combination ((B : ℝ) * b) * hs
    · rw [hstep, h1']; push_cast; linear_combination ((B : ℝ) * b) * hs

/-- A real `y` with `|y| > 2` is `t + t⁻¹` for some `|t| > 1`. -/
theorem Row2.exists_add_inv {y : ℝ} (hy : 2 < |y|) : ∃ t : ℝ, t ≠ 0 ∧ 1 < |t| ∧ t + t⁻¹ = y := by
  have hd : 0 ≤ y ^ 2 - 4 := by
    have : 4 < y ^ 2 := by
      have h2 : (2 : ℝ) ^ 2 < |y| ^ 2 := by
        exact pow_lt_pow_left₀ hy (by norm_num) two_ne_zero
      rw [sq_abs] at h2; linarith
    linarith
  set r := √(y ^ 2 - 4) with hr
  have hr2 : r * r = y ^ 2 - 4 := Real.mul_self_sqrt hd
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  rcases lt_abs.mp hy with h | h
  · -- `y > 2`
    refine ⟨(y + r) / 2, by positivity, ?_, ?_⟩
    · rw [abs_of_pos (by positivity)]; linarith
    · have hinv : ((y + r) / 2)⁻¹ = (y - r) / 2 :=
        inv_eq_of_mul_eq_one_right (by linear_combination (-1 / 4 : ℝ) * hr2)
      rw [hinv]; ring
  · -- `y < −2`
    have hneg : (y - r) / 2 < -1 := by linarith
    refine ⟨(y - r) / 2, by linarith, ?_, ?_⟩
    · rw [abs_of_neg (by linarith)]; linarith
    · have hne : (y - r) / 2 ≠ 0 := by linarith
      have hinv : ((y - r) / 2)⁻¹ = (y + r) / 2 :=
        inv_eq_of_mul_eq_one_right (by linear_combination (-1 / 4 : ℝ) * hr2)
      rw [hinv]; ring

/-- **Every real solution of `C_n(y) = 2` (`n ≥ 1`) has `|y| ≤ 2`.** -/
theorem Row2.abs_le_two_of_cheb {y : ℝ} {n : ℕ} (hn : 0 < n) (h : Row2.cheb y n = 2) : |y| ≤ 2 := by
  by_contra hc
  push Not at hc
  obtain ⟨t, ht0, ht1, rfl⟩ := Row2.exists_add_inv hc
  rw [Row2.cheb_add_inv t ht0 n, inv_pow] at h
  have hw0 : t ^ n ≠ 0 := pow_ne_zero n ht0
  have hw : t ^ n = 1 := by
    have h2 : (t ^ n - 1) ^ 2 = 0 := by
      have e : t ^ n * (t ^ n)⁻¹ = 1 := mul_inv_cancel₀ hw0
      linear_combination (t ^ n) * h - e
    have := pow_eq_zero_iff (n := 2) (two_ne_zero) |>.mp h2
    linarith
  have habs : |t| ^ n = 1 := by rw [← abs_pow, hw, abs_one]
  have := one_lt_pow₀ ht1 hn.ne'
  linarith

/-- An integer, as a real, is integral over `ℤ`. -/
theorem Row2.isIntegral_intCast (k : ℤ) : IsIntegral ℤ ((k : ℤ) : ℝ) := by
  simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ ℝ k))

/-- **Lemma Q (row 2).**  Let `p ≡ 3 (mod 4)` be a prime, `p ≥ 7`, and `s² = p`.  If `θ ∈ (0, π)` is a
rational multiple of `π` with `cos θ ∈ ℚ + ℚ s`, then `θ ∈ {π/3, π/2, 2π/3}`. -/
theorem Row2.lemmaQ {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3) (hp7 : 7 ≤ p) {s : ℝ}
    (hs : s ^ 2 = p) {θ : ℝ} (hθ : ∃ r : ℚ, θ = r * π) (hθ0 : 0 < θ) (hθπ : θ < π)
    (hc : Row2.QMu s (Real.cos θ)) :
    θ = π / 3 ∨ θ = π / 2 ∨ θ = π * (2 / 3) := by
  obtain ⟨r, hr⟩ := hθ
  obtain ⟨q₁, q₂, hq⟩ := hc
  have hsq : s ^ 2 = ((p : ℚ) : ℝ) := by rw [hs]; push_cast; ring
  -- `s` is irrational
  have hirr : ∀ q : ℚ, s ≠ q := by
    intro q hsq'
    have habs : √(p : ℝ) = |(q : ℝ)| := by
      rw [← hsq', ← hs, Real.sqrt_sq_eq_abs]
    exact hp.irrational_sqrt ⟨|q|, by rw [habs]; push_cast; rfl⟩
  -- `x = a + b s`, `x' = a − b s`
  set a : ℚ := 2 * q₁ with ha
  set b : ℚ := 2 * q₂ with hb
  set x : ℝ := 2 * Real.cos θ with hx
  have hxab : x = (a : ℝ) + b * s := by rw [hx, hq, ha, hb]; push_cast; ring
  set x' : ℝ := (a : ℝ) - b * s with hx'
  -- `x` is integral; so is `x'`
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
  -- `|x| ≤ 2` and `|x'| ≤ 2`
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
  -- `U = x + x' = 2a ∈ ℤ`, `W = x x' = a² − b² p ∈ ℤ`
  obtain ⟨U, hU⟩ := (hxint.add hx'int).exists_int_iff_exists_rat.mp
    ⟨2 * a, by rw [hxab, hx']; push_cast; ring⟩
  obtain ⟨W, hW⟩ := (hxint.mul hx'int).exists_int_iff_exists_rat.mp
    ⟨a * a - b * b * p, by rw [hxab, hx']; push_cast; linear_combination (-(b : ℝ) ^ 2) * hs⟩
  -- `V = 2b`, `p V² = U² − 4W`
  have hVZ : ((p : ℝ)) * ((2 * b : ℚ) : ℝ) ^ 2 = ((U ^ 2 - 4 * W : ℤ) : ℝ) := by
    have e1 : (U : ℝ) = 2 * a := by rw [← hU, hxab, hx']; ring
    have e2 : (W : ℝ) = a * a - b * b * p := by
      rw [← hW, hxab, hx']; linear_combination (-(b : ℝ) ^ 2) * hs
    push_cast; rw [e1, e2]; ring
  -- `pV ∈ ℤ`
  have hpVint : IsIntegral ℤ (((p * (2 * b) : ℚ)) : ℝ) := by
    refine IsIntegral.of_pow (n := 2) two_pos ?_
    have : (((p * (2 * b) : ℚ)) : ℝ) ^ 2 = (((p : ℤ) * (U ^ 2 - 4 * W) : ℤ) : ℝ) := by
      push_cast at hVZ ⊢; rw [← hVZ]; ring
    rw [this]; exact Row2.isIntegral_intCast _
  obtain ⟨m, hm⟩ := hpVint.exists_int_iff_exists_rat.mp ⟨_, rfl⟩
  -- `m² = p (U² − 4W)`, so `p ∣ m`
  have hm2 : m ^ 2 = (p : ℤ) * (U ^ 2 - 4 * W) := by
    have : ((m ^ 2 : ℤ) : ℝ) = (((p : ℤ) * (U ^ 2 - 4 * W) : ℤ) : ℝ) := by
      push_cast at hVZ hm ⊢; rw [← hm, ← hVZ]; ring
    exact_mod_cast this
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨m', hm'⟩ : (p : ℤ) ∣ m := hpZ.dvd_of_dvd_pow (n := 2) ⟨_, hm2⟩
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hZ : U ^ 2 - 4 * W = (p : ℤ) * m' ^ 2 := by
    rw [hm'] at hm2
    have : (p : ℤ) * ((p : ℤ) * m' ^ 2) = (p : ℤ) * (U ^ 2 - 4 * W) := by rw [← hm2]; ring
    exact (mul_left_cancel₀ hp0 this).symm
  -- `V = m'`
  have hVm : ((2 * b : ℚ) : ℝ) = m' := by
    have hp0' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have : (p : ℝ) * ((2 * b : ℚ) : ℝ) = (p : ℝ) * m' := by
      have := hm.symm; rw [hm'] at this; push_cast at this ⊢; linarith
    exact mul_left_cancel₀ hp0' this
  -- the bound `p m'² ≤ 16`
  have hbound : (p : ℝ) * (m' : ℝ) ^ 2 ≤ 16 := by
    have hdiff : x - x' = ((2 * b : ℚ) : ℝ) * s := by rw [hxab, hx']; push_cast; ring
    have h4 : |x - x'| ≤ 4 := by
      calc |x - x'| ≤ |x| + |x'| := abs_sub _ _
        _ ≤ 4 := by linarith
    rw [hdiff, hVm] at h4
    have h16 : ((m' : ℝ) * s) ^ 2 ≤ 16 := by
      have := sq_le_sq' (abs_le.mp h4).1 (abs_le.mp h4).2
      linarith
    rw [mul_pow, hs] at h16; linarith
  have hbound' : (p : ℤ) * m' ^ 2 ≤ 16 := by exact_mod_cast hbound
  have hm'0 : m' = 0 := by
    have hp7' : (7 : ℤ) ≤ p := by exact_mod_cast hp7
    have hsq1 : m' ^ 2 ≤ 2 := by nlinarith [sq_nonneg m']
    have hcases : m' ^ 2 = 0 ∨ m' ^ 2 = 1 := by
      have : m' ^ 2 < 2 ∨ m' ^ 2 = 2 := lt_or_eq_of_le hsq1
      rcases this with h | h
      · have := sq_nonneg m'; omega
      · exfalso
        -- `m'² = 2` is impossible
        have hm'le : |m'| ≤ 1 := by nlinarith [sq_abs m', abs_nonneg m']
        have : m' ^ 2 ≤ 1 := by nlinarith [sq_abs m', abs_nonneg m']
        omega
    rcases hcases with h | h
    · exact pow_eq_zero_iff (two_ne_zero) |>.mp h
    · exfalso
      rw [h, mul_one] at hZ
      -- `p = U² − 4W ≡ 0, 1 (mod 4)`
      obtain ⟨k, hk | hk⟩ := Int.even_or_odd' U
      · have e : (p : ℤ) = 4 * (k ^ 2 - W) := by rw [← hZ, hk]; ring
        generalize k ^ 2 - W = T at e
        omega
      · have e : (p : ℤ) = 4 * (k ^ 2 + k - W) + 1 := by rw [← hZ, hk]; ring
        generalize k ^ 2 + k - W = T at e
        omega
  -- so `b = 0` and `cos θ = a/2 ∈ ℚ`
  have hb0 : (b : ℝ) = 0 := by
    have := hVm; rw [hm'0] at this; push_cast at this; linarith
  have hcosq : ∃ q : ℚ, Real.cos θ = q := ⟨a / 2, by
    have : x = a := by rw [hxab, hb0]; ring
    rw [hx] at this; push_cast; linarith⟩
  have hmem := niven_angle_eq ⟨r, hr⟩ hcosq ⟨hθ0.le, hθπ.le⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h | h | h
  · exact absurd h hθ0.ne'
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact absurd h hθπ.ne

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row2.cheb_cos
#print axioms Erdos634.Geometry.Row2.cheb_add_inv
#print axioms Erdos634.Geometry.Row2.cheb_conj
#print axioms Erdos634.Geometry.Row2.poly_conj
#print axioms Erdos634.Geometry.Row2.abs_le_two_of_cheb
#print axioms Erdos634.Geometry.Row2.lemmaQ
