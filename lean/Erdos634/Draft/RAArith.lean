-- Draft/RAArith.lean — arithmetic core of Theorem R-A (S5): `N (f+e) = K² (f−e)` with `N` prime
-- gives `f² − e² = N σ²` and `(f−e) K = N σ` (the paper's `k = pσ`, `f²−e² = pσ²`).
-- Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Mathlib

namespace Erdos634.Draft.RAArith

theorem ra_arith {N : ℕ} {e f K : ℤ} (hN : N.Prime) (he : 0 < e) (hef : e < f) (hK : 0 < K)
    (hEq : (N : ℤ) * (f + e) = K ^ 2 * (f - e)) :
    ∃ σ : ℤ, 0 < σ ∧ f ^ 2 - e ^ 2 = N * σ ^ 2 ∧ (f - e) * K = N * σ := by
  have hNp : Prime (N : ℤ) := Nat.prime_iff_prime_int.mp hN
  have hN0 : (0 : ℤ) < N := by exact_mod_cast hN.pos
  have hk2 : ((f - e) * K) ^ 2 = N * (f ^ 2 - e ^ 2) := by
    have : ((f - e) * K) ^ 2 = (f - e) * (K ^ 2 * (f - e)) := by ring
    rw [this, ← hEq]; ring
  have hdvd : (N : ℤ) ∣ ((f - e) * K) ^ 2 := ⟨f ^ 2 - e ^ 2, hk2⟩
  obtain ⟨σ, hσ⟩ := hNp.dvd_of_dvd_pow hdvd
  have hkpos : 0 < (f - e) * K := mul_pos (by linarith) hK
  have hσpos : 0 < σ := by
    by_contra hle; push Not at hle; nlinarith
  refine ⟨σ, hσpos, ?_, hσ⟩
  have : (N : ℤ) * ((N : ℤ) * σ ^ 2) = N * (f ^ 2 - e ^ 2) := by
    rw [← hk2, hσ]; ring
  exact (mul_left_cancel₀ hN0.ne' this).symm

end Erdos634.Draft.RAArith

#print axioms Erdos634.Draft.RAArith.ra_arith
