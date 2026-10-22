-- Draft/R8CompositeArg.lean — Abstract composite argument for R8 reduction.
--
-- Proves `no_prime_F4_form`: no prime N equals (x+y)·(2x+y) for x : ℕ > 0 and y : ℚ > 0.
--
-- Proof sketch:
--   Write y = num/den (lowest terms, IsCoprime num den over ℤ).
--   Then N·den² = (x·den + num)·(2·x·den + num) in ℤ.
--   The product ≡ num² (mod den), so den | num².
--   Nat.Coprime num den → den | 1 → den = 1.
--   With den=1: N = (x+num)·(2x+num), both factors ≥ 2, contradicting N prime.
--
-- ZERO sorry.  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).

import Mathlib.Tactic

open scoped Classical

namespace Erdos634.Draft.R8CompositeArg

/-! ## Key number-theory lemma over ℕ -/

/-- No prime `N` can factor as `(x*s+r)*(2*x*s+r)` when `Nat.Coprime r s` and `x,r,s ≥ 1`. -/
private lemma prime_not_split (N x r s : ℕ) (hN : N.Prime)
    (hx : 0 < x) (hr : 0 < r) (hs : 0 < s)
    (hcop : Nat.Coprime r s)
    (heq : N * s ^ 2 = (x * s + r) * (2 * x * s + r)) : False := by
  -- Step 1: s | r² (via ℤ to avoid ℕ subtraction issues)
  have hs_dvd_r2 : s ∣ r ^ 2 := by
    have hZ : (s : ℤ) ∣ (r : ℤ) ^ 2 := by
      have heqZ : (N : ℤ) * s ^ 2 = (x * s + r) * (2 * x * s + r) := by exact_mod_cast heq
      have hdvd : (s : ℤ) ∣ (↑x * ↑s + ↑r) * (2 * ↑x * ↑s + ↑r) := by
        rw [← heqZ]; exact ⟨N * s, by push_cast; ring⟩
      have heq2 : (↑x * ↑s + ↑r) * (2 * ↑x * ↑s + ↑r) =
          (r : ℤ) ^ 2 + s * (2 * x ^ 2 * s + 3 * x * r) := by push_cast; ring
      rw [heq2] at hdvd
      have h2 : (s : ℤ) ∣ (s : ℤ) * (2 * x ^ 2 * s + 3 * x * r) := dvd_mul_right _ _
      have h3 := dvd_sub hdvd h2
      rwa [show (r : ℤ) ^ 2 + (s : ℤ) * (2 * ↑x ^ 2 * ↑s + 3 * ↑x * ↑r) -
          (s : ℤ) * (2 * ↑x ^ 2 * ↑s + 3 * ↑x * ↑r) = (r : ℤ) ^ 2 from by ring] at h3
    exact_mod_cast hZ
  -- Step 2: s = 1 (from Nat.Coprime r s + s | r²)
  have hs1 : s = 1 := by
    have hcop2 : Nat.Coprime s (r ^ 2) := hcop.symm.pow_right 2
    have hs_dvd1 : s ∣ 1 := by
      have h := Nat.dvd_gcd (dvd_refl s) hs_dvd_r2
      rwa [hcop2] at h
    exact Nat.le_antisymm (Nat.le_of_dvd one_pos hs_dvd1) hs
  -- Step 3: N = (x+r)*(2x+r) with both factors ≥ 2, contradicting N prime
  subst hs1
  simp at heq
  have hA : 2 ≤ x + r := by omega
  have hAdvd : x + r ∣ N := ⟨2 * x + r, heq⟩
  rcases hN.eq_one_or_self_of_dvd (x + r) hAdvd with h1 | hNeq
  · omega
  · have hB : 3 ≤ 2 * x + r := by omega
    have : N * (2 * x + r) = N * 1 :=
      calc N * (2 * x + r) = (x + r) * (2 * x + r) := by rw [← hNeq]
        _ = N * 1 := by linarith [heq]
    have := Nat.eq_of_mul_eq_mul_left hN.pos this
    omega

/-! ## Main theorem -/

/-- No prime `N` equals `(↑x + y) * (2 * ↑x + y)` for `x : ℕ > 0` and `y : ℚ > 0`. -/
theorem no_prime_F4_form (N : ℕ) (hN : N.Prime) (x : ℕ) (hx : 0 < x) (y : ℚ) (hy : 0 < y) :
    (N : ℚ) ≠ (↑x + y) * (2 * ↑x + y) := by
  intro heq
  have hnum_pos : 0 < y.num := Rat.num_pos.mpr hy
  have hden_pos : 0 < y.den := y.pos
  -- Derive the ℤ identity N·den² = (x·den+num)·(2x·den+num)
  have hZ : (N : ℤ) * y.den ^ 2 = (↑x * ↑y.den + y.num) * (2 * ↑x * ↑y.den + y.num) := by
    have hd_ne : (y.den : ℚ) ≠ 0 := by exact_mod_cast hden_pos.ne'
    have hyd : y * (y.den : ℚ) = y.num := by exact_mod_cast Rat.mul_den_eq_num y
    have hQ : (N : ℚ) * y.den ^ 2 = (↑x * ↑y.den + y.num) * (2 * ↑x * ↑y.den + y.num) := by
      calc (N : ℚ) * y.den ^ 2
          = ((↑x + y) * (2 * ↑x + y)) * y.den ^ 2 := by rw [← heq]
        _ = (↑x * ↑y.den + y * ↑y.den) * (2 * ↑x * ↑y.den + y * ↑y.den) := by ring
        _ = (↑x * ↑y.den + ↑y.num) * (2 * ↑x * ↑y.den + ↑y.num) := by rw [hyd]
    exact_mod_cast hQ
  -- Lift to ℕ identity using natAbs (since y.num > 0)
  have hnn : (y.num.natAbs : ℤ) = y.num := Int.natAbs_of_nonneg (le_of_lt hnum_pos)
  have hNeq_nat : N * y.den ^ 2 = (x * y.den + y.num.natAbs) * (2 * x * y.den + y.num.natAbs) := by
    have hZ' : (N : ℤ) * y.den ^ 2 =
        (↑x * ↑y.den + ↑y.num.natAbs) * (2 * ↑x * ↑y.den + ↑y.num.natAbs) := by
      rw [hnn]; exact hZ
    exact_mod_cast hZ'
  -- Apply the ℕ core lemma
  exact prime_not_split N x y.num.natAbs y.den hN hx
    (by simp [Nat.pos_iff_ne_zero, ne_of_gt hnum_pos])
    hden_pos y.reduced hNeq_nat

#check @no_prime_F4_form
#print axioms no_prime_F4_form

end Erdos634.Draft.R8CompositeArg
