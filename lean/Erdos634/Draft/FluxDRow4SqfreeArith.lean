-- Draft/FluxDRow4SqfreeArith.lean — atom A1 of the squarefree γ=2α route ((private working notes, not included)):
-- the leg-word arithmetic for N = M·M' with gcd(M,M') = 1 (squarefree N), generalising `Row4.L7`.
-- Pure ℕ arithmetic.  Atoms A2 (real-number layer), A3 (β-pigeonhole on a b-free leg), A4 (assembly)
-- are NOT done.  UNAUDITED.  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Mathlib

namespace Erdos634.Draft.FluxDRow4SqfreeArith

/-- `k = (M'−M)/2`, `m = (M'+M)/2`, `N = M M'`, `gcd(M,M') = 1`, `M'>3M`, `M,M'` odd.
A leg word `p·a + q·b + r·c` of length `X = N a/k` (tile `a = k², b = N, c = k m`) is either
`b^k` (`q = k`, `p = r = 0`) or has no `b` (`q = 0`, `p k + r m = N`). -/
theorem leg_words_gen (M M' k m : ℕ) (hM : 0 < M) (hcop : Nat.Coprime M M') (hlt : 3 * M < M')
    (hk : 2 * k + M = M') (hm : 2 * m = M' + M) (p q r : ℕ)
    (h : (M * M') * k = p * k ^ 2 + q * (M * M') + r * k * m) :
    (q = k ∧ p = 0 ∧ r = 0) ∨ (q = 0 ∧ p * k + r * m = M * M') := by
  have hk2 : 2 ≤ k := by omega
  have hkM : Nat.Coprime k M := by
    have h1 : Nat.gcd k M ∣ k := Nat.gcd_dvd_left _ _
    have h2 : Nat.gcd k M ∣ M := Nat.gcd_dvd_right _ _
    have h3 : Nat.gcd k M ∣ M' := by
      rw [← hk]; exact dvd_add (dvd_mul_of_dvd_right h1 2) h2
    exact Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd h2 h3)
  have hkM' : Nat.Coprime k M' := by
    have h1 : Nat.gcd k M' ∣ k := Nat.gcd_dvd_left _ _
    have h2 : Nat.gcd k M' ∣ M' := Nat.gcd_dvd_right _ _
    have h3 : Nat.gcd k M' ∣ M := by
      have : Nat.gcd k M' ∣ 2 * k + M := hk ▸ h2
      exact (Nat.dvd_add_right (dvd_mul_of_dvd_right h1 2)).mp this
    exact Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd h3 h2)
  have hkN : Nat.Coprime k (M * M') := Nat.Coprime.mul_right hkM hkM'
  have hN0 : 0 < M * M' := Nat.mul_pos hM (by omega)
  -- q ≤ k
  have hqk : q ≤ k := by
    by_contra hlt'
    push Not at hlt'
    have : (M * M') * k < q * (M * M') := by nlinarith
    omega
  -- k ∣ q * N
  have hdvd : k ∣ q * (M * M') := by
    have h' : q * (M * M') = k * ((M * M') - p * k - r * m) ∨ True := Or.inr trivial
    have hle : p * k + r * m ≤ M * M' := by
      by_contra hcon
      push Not at hcon
      have : k * (p * k + r * m) > k * (M * M') := Nat.mul_lt_mul_of_pos_left hcon (by omega)
      nlinarith
    refine ⟨(M * M') - (p * k + r * m), ?_⟩
    have e1 : k * ((M * M') - (p * k + r * m)) = k * (M * M') - k * (p * k + r * m) := by
      rw [Nat.mul_sub]
    rw [e1]
    have : k * (M * M') = k * (p * k + r * m) + q * (M * M') := by nlinarith
    omega
  have hkq : k ∣ q := hkN.dvd_of_dvd_mul_right hdvd
  obtain ⟨t, ht⟩ := hkq
  have ht1 : t ≤ 1 := by
    by_contra hcon
    push Not at hcon
    have : q ≥ 2 * k := by rw [ht]; nlinarith
    omega
  interval_cases t
  · right
    refine ⟨by omega, ?_⟩
    have hq0 : q = 0 := by omega
    subst hq0
    have : k * (p * k + r * m) = k * (M * M') := by nlinarith
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  · left
    have hq : q = k := by omega
    subst hq
    have h0 : p * q ^ 2 + r * q * m = 0 := by linarith [h, mul_comm (M * M') q]
    have hpq : p * q ^ 2 = 0 := by omega
    have hrq : r * q * m = 0 := by omega
    have hm0 : 0 < m := by omega
    refine ⟨rfl, ?_, ?_⟩
    · rcases Nat.mul_eq_zero.mp hpq with h1 | h1
      · exact h1
      · exact absurd h1 (by positivity)
    · rcases Nat.mul_eq_zero.mp hrq with h1 | h1
      · rcases Nat.mul_eq_zero.mp h1 with h2 | h2
        · exact h2
        · omega
      · omega

end Erdos634.Draft.FluxDRow4SqfreeArith

#print axioms Erdos634.Draft.FluxDRow4SqfreeArith.leg_words_gen
