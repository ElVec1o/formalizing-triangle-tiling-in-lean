/-
Draft/H1bCaseAB.lean — atom H1.b of (private working notes, not included) §2 "Case AB" (`a/b ∈ ℚ`): arithmetic only.
Statement: right-tile side data `a, b, c > 0`, `c² = a² + b²`, `a = q·b` with `q ∈ ℚ`, a real `lam > 0` with
`lam² = M ∈ ℕ`, `lam ∉ ℚ`, and the side word `lam·c = u_a a + u_b b + u_c c` (`u_• ∈ ℕ`) force
`M = x² + y²` (so `N = 2M = 2(x²+y²)`).  Proof: `(lam - u_c)² (r²+s²) = (u_a r + u_b s)²` (`a/b = r/s`),
then `u_c = 0` by irrationality of `lam`, then `(r²+s²)·M = X²` and valuations at primes `≡ 3 (4)`
(`Nat.eq_sq_add_sq_iff`).
*** UNAUDITED.  Formalization debt, NOT /goal progress.  Pure Mathlib; no cited theorem; no sorry. ***
-/
import Mathlib

namespace Erdos634.Draft.H1b

/-- If `n` is a sum of two squares, `n ≠ 0`, `M ≠ 0` and `n * M` is a square, then `M` is a sum of two
squares (valuations at primes `≡ 3 (mod 4)`). -/
theorem sumsq_of_mul_sq {n M X : ℕ} (hn : ∃ x y : ℕ, n = x ^ 2 + y ^ 2) (hn0 : n ≠ 0) (hM : M ≠ 0)
    (h : n * M = X ^ 2) : ∃ x y : ℕ, M = x ^ 2 + y ^ 2 := by
  have hX : X ≠ 0 := by
    rintro rfl
    have : n * M = 0 := by simpa using h
    exact (mul_ne_zero hn0 hM) this
  rw [Nat.eq_sq_add_sq_iff] at hn ⊢
  intro q hq h4
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  haveI : Fact q.Prime := ⟨hqp⟩
  have hv := congrArg (padicValNat q) h
  rw [padicValNat.mul hn0 hM, padicValNat.pow _ hX] at hv
  have hnv : Even (padicValNat q n) := by
    by_cases hd : q ∣ n
    · exact hn q (Nat.mem_primeFactors.mpr ⟨hqp, hd, hn0⟩) h4
    · rw [padicValNat.eq_zero_of_not_dvd hd]; exact ⟨0, rfl⟩
  obtain ⟨k, hk⟩ := hnv
  exact ⟨padicValNat q X - k, by omega⟩

/-- A sum of two squares `r² + s²`, and the quantity `X₁ = u_a r + u_b s`: the squared identity of Case AB. -/
theorem caseAB_square_identity {a b c lam : ℝ} {r s ua ub uc : ℕ} (hb : 0 < b)
    (hc2 : c ^ 2 = a ^ 2 + b ^ 2) (has : a * s = b * r)
    (hw : lam * c = ua * a + ub * b + uc * c) :
    (lam - uc) ^ 2 * ((r : ℝ) ^ 2 + (s : ℝ) ^ 2) = ((ua : ℝ) * r + ub * s) ^ 2 := by
  have h1 : (lam - uc) * c * s = b * ((ua : ℝ) * r + ub * s) := by
    have : (lam - uc) * c = ua * a + ub * b := by linear_combination hw
    calc (lam - uc) * c * s = (ua * a + ub * b) * s := by rw [this]
      _ = _ := by linear_combination (ua : ℝ) * has
  have h2 : ((lam - uc) * c * s) ^ 2 = (b * ((ua : ℝ) * r + ub * s)) ^ 2 := by rw [h1]
  have h3 : c ^ 2 * (s : ℝ) ^ 2 = b ^ 2 * ((r : ℝ) ^ 2 + (s : ℝ) ^ 2) := by
    have : (a * s) ^ 2 = (b * r) ^ 2 := by rw [has]
    linear_combination (s : ℝ) ^ 2 * hc2 + this
  have hb2 : b ^ 2 ≠ 0 := by positivity
  apply mul_left_cancel₀ hb2
  calc b ^ 2 * ((lam - uc) ^ 2 * ((r : ℝ) ^ 2 + (s : ℝ) ^ 2))
      = (lam - uc) ^ 2 * (b ^ 2 * ((r : ℝ) ^ 2 + (s : ℝ) ^ 2)) := by ring
    _ = (lam - uc) ^ 2 * (c ^ 2 * (s : ℝ) ^ 2) := by rw [h3]
    _ = ((lam - uc) * c * s) ^ 2 := by ring
    _ = (b * ((ua : ℝ) * r + ub * s)) ^ 2 := h2
    _ = _ := by ring

/-- **Case AB (H1.b).**  `a/b ∈ ℚ` (as `a = q·b`), `lam ∉ ℚ`, `lam² = M`: then `M` is a sum of two squares. -/
theorem caseAB_sumsq {M : ℕ} {a b c lam : ℝ} (ha : 0 < a) (hb : 0 < b) (hc2 : c ^ 2 = a ^ 2 + b ^ 2)
    (hlam : 0 < lam) (hlam2 : lam ^ 2 = M) (hirr : Irrational lam) (hq : ∃ q : ℚ, a = q * b)
    (hword : ∃ ua ub uc : ℕ, lam * c = ua * a + ub * b + uc * c) :
    ∃ x y : ℕ, M = x ^ 2 + y ^ 2 := by
  obtain ⟨q, hq⟩ := hq
  obtain ⟨ua, ub, uc, hw⟩ := hword
  have hq0 : (0 : ℝ) < q := by
    by_contra hneg
    rw [not_lt] at hneg
    nlinarith
  have hq0' : (0 : ℚ) < q := by exact_mod_cast hq0
  have hnum : 0 < q.num := Rat.num_pos.mpr hq0'
  set r : ℕ := q.num.toNat with hr
  set s : ℕ := q.den with hs
  have hrz : (q.num : ℤ) = r := by rw [hr]; exact (Int.toNat_of_nonneg hnum.le).symm
  have hs0 : 0 < s := q.den_pos
  have hqs : (q : ℝ) * s = r := by
    have h1 : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := Rat.cast_def q
    rw [h1, hrz]
    have : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
    push_cast
    field_simp
    rw [hs]
  have has : a * s = b * r := by rw [hq, ← hqs]; ring
  have hid := caseAB_square_identity (r := r) (s := s) (ua := ua) (ub := ub) (uc := uc) hb hc2 has hw
  set n : ℕ := r ^ 2 + s ^ 2 with hn
  set X : ℕ := ua * r + ub * s with hX
  have hid' : (lam - uc) ^ 2 * (n : ℝ) = (X : ℝ) ^ 2 := by
    rw [hn, hX]; push_cast; exact hid
  have hn0 : n ≠ 0 := by
    have : 0 < n := by rw [hn]; positivity
    omega
  have huc : uc = 0 := by
    by_contra hne
    have hne' : (uc : ℝ) ≠ 0 := by exact_mod_cast hne
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
    apply hirr
    refine ⟨((n : ℚ) * (M + (uc : ℚ) ^ 2) - (X : ℚ) ^ 2) / (2 * uc * n), ?_⟩
    have key : 2 * (uc : ℝ) * n * lam = (n : ℝ) * (M + (uc : ℝ) ^ 2) - (X : ℝ) ^ 2 := by
      rw [← hid', ← hlam2]; ring
    push_cast
    rw [div_eq_iff (by positivity), ← key]
    ring
  subst huc
  have hM : (M : ℝ) * n = (X : ℝ) ^ 2 := by
    rw [← hlam2]; simp at hid'; linear_combination hid'
  have hM' : n * M = X ^ 2 := by
    have : (n : ℝ) * M = (X : ℝ) ^ 2 := by linarith
    exact_mod_cast this
  have hM0 : M ≠ 0 := by
    intro h0
    rw [h0] at hlam2
    simp at hlam2
    linarith
  exact sumsq_of_mul_sq ⟨r, s, hn⟩ hn0 hM0 hM'

end Erdos634.Draft.H1b

#print axioms Erdos634.Draft.H1b.sumsq_of_mul_sq
#print axioms Erdos634.Draft.H1b.caseAB_sumsq
