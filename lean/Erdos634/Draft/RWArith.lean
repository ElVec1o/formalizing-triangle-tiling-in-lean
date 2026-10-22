-- Draft/RWArith.lean — arithmetic core of Theorem R-W (S4): `N e² = S² (2f² − e²)` with `N` prime
-- and `gcd(e,f) = 1` forces `N = 2f² − e²`, `S = e` (the paper's `k = 1`).
-- Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Mathlib

namespace Erdos634.Draft.RWArith

theorem w_arith {N : ℕ} {e f S : ℤ} (hN : N.Prime) (hN5 : 5 ≤ N)
    (he : 0 < e) (hef : e < f) (hcop : IsCoprime e f) (hS : 0 < S)
    (hEq : (N : ℤ) * e ^ 2 = S ^ 2 * (2 * f ^ 2 - e ^ 2)) :
    (N : ℤ) = 2 * f ^ 2 - e ^ 2 ∧ S = e := by
  have hNp : Prime (N : ℤ) := Nat.prime_iff_prime_int.mp hN
  have hN0 : (0 : ℤ) < N := by exact_mod_cast hN.pos
  have hN5' : (5 : ℤ) ≤ N := by exact_mod_cast hN5
  set g : ℤ := 2 * f ^ 2 - e ^ 2 with hg
  have hgpos : e ^ 2 < g := by nlinarith
  have hdvd : (N : ℤ) ∣ S ^ 2 * g := ⟨e ^ 2, hEq.symm⟩
  rcases hNp.dvd_or_dvd hdvd with h | h
  · exfalso
    obtain ⟨S', hS'⟩ := hNp.dvd_of_dvd_pow h
    have hS'pos : 0 < S' := by
      by_contra hle; push Not at hle; nlinarith
    have h1 : e ^ 2 = N * S' ^ 2 * g := by
      have : (N : ℤ) * e ^ 2 = N * (N * S' ^ 2 * g) := by rw [hEq, hS']; ring
      exact mul_left_cancel₀ hN0.ne' this
    nlinarith [sq_nonneg S', mul_pos hN0 (pow_pos hS'pos 2), mul_pos (mul_pos hN0 (pow_pos hS'pos 2)) (lt_of_le_of_lt (sq_nonneg e) hgpos)]
  · obtain ⟨g', hg'⟩ := h
    have h1 : e ^ 2 = S ^ 2 * g' := by
      have : (N : ℤ) * e ^ 2 = N * (S ^ 2 * g') := by rw [hEq, hg']; ring
      exact mul_left_cancel₀ hN0.ne' this
    have hSe : S ∣ e := by
      have : S ^ 2 ∣ e ^ 2 := ⟨g', h1⟩
      exact (Int.pow_dvd_pow_iff (by norm_num)).mp this
    obtain ⟨t, ht⟩ := hSe
    have ht0 : 0 < t := by
      by_contra hle; push Not at hle; nlinarith
    have hgt : g' = t ^ 2 := by
      have : S ^ 2 * g' = S ^ 2 * t ^ 2 := by rw [← h1, ht]; ring
      exact mul_left_cancel₀ (pow_pos hS 2).ne' this
    have h2f : 2 * f ^ 2 = t ^ 2 * (N + S ^ 2) := by
      have : 2 * f ^ 2 = g + e ^ 2 := by rw [hg]; ring
      rw [this, hg', hgt, ht]; ring
    have hcopt : IsCoprime t f := hcop.of_isCoprime_of_dvd_left ⟨S, by rw [ht]; ring⟩
    have hcopt2 : IsCoprime (t ^ 2) (f ^ 2) := hcopt.pow
    have hdiv : t ^ 2 ∣ 2 * f ^ 2 := ⟨N + S ^ 2, h2f⟩
    have hdiv2 : t ^ 2 ∣ 2 := hcopt2.dvd_of_dvd_mul_right hdiv
    have ht1 : t = 1 := by
      have : t ^ 2 ≤ 2 := Int.le_of_dvd (by norm_num) hdiv2
      nlinarith
    subst ht1
    refine ⟨?_, by rw [ht]; ring⟩
    rw [hg', hgt]; ring

end Erdos634.Draft.RWArith

#print axioms Erdos634.Draft.RWArith.w_arith
