/-
Draft/CompositeIsoB.lean — `IsoH9b N` (ThmIsoH9b) by bounded check, for N = 22, 46, 66, 78 (squarefree, N ≡ 2 mod 4),
the four N at which `IsoH9 N` is FALSE (a proper divisor e = a+2b of N carries a primitive integer 120° triple:
22 ⊃ 11 = 5+2·3 (5,3,7);  46 ⊃ 23 = 7+2·8 (7,8,13);  66 ⊃ 11, 22 = 8+2·7 (8,7,13);  78 ⊃ 13 = 3+2·5 (3,5,7), 26 = 16+2·5 (16,5,19)).
Mechanism (all four): area identity `b N = k² e` (k = μ) plus `k(c−a−b) = M_α b` plus `M_α ≡ N (mod 2)`.
  22, 66, 78 : `b·(N/e)` is not a perfect square (k does not exist);
  46         : (7,8,13), e = 23, `b·(N/e) = 8·2 = 16 = 4²` DOES exist (k = 4), `M_α = k(c−a−b)/b = −1`, odd, but N is even:
               killed only by the parity clause `M_α ≡ N (mod 2)` of `Paper.cor_int_at`.
Negative controls: `IsoH9 N` fails at these N (`not_isoH9_*`), and `IsoH9b` itself FAILS at N = 33
(k = 3, (5,3,7), M_α = −1, N odd) so the hypothesis is not trivially true (`not_isoH9b_33`).
UNAUDITED.  Formalization debt, NOT /goal progress.  No sorry, no native_decide (`decide +kernel` on closed Nat/Int checks).
-/
import Erdos634.Draft.ThmIsoH9b


set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.CompositeIsoB

open Erdos634.Geometry

theorem isoH9b_of_check (N : ℕ) (hN : 0 < N)
    (hchk : ∀ a : ℕ, a < N → ∀ b : ℕ, b < N → 0 < a → 0 < b → a + 2 * b < N → 3 ≤ a + 2 * b →
      a + 2 * b ∣ N → Nat.gcd b (a + 2 * b) = 1 →
      Nat.sqrt (a ^ 2 + a * b + b ^ 2) * Nat.sqrt (a ^ 2 + a * b + b ^ 2) = a ^ 2 + a * b + b ^ 2 →
      Nat.sqrt (b * (N / (a + 2 * b))) * Nat.sqrt (b * (N / (a + 2 * b))) = b * (N / (a + 2 * b)) →
      ((Nat.sqrt (b * (N / (a + 2 * b))) : ℤ) * ((Nat.sqrt (a ^ 2 + a * b + b ^ 2) : ℤ) - a - b)) % b = 0 →
      ((((Nat.sqrt (b * (N / (a + 2 * b))) : ℤ) * ((Nat.sqrt (a ^ 2 + a * b + b ^ 2) : ℤ) - a - b)) / b - N) % 2
        = 0) → False) :
    IsoH9b N := by
  intro a b c k nA ha hb hc hk hcc h3 hcop hdvd hne harea hkc hpar
  have hle : a + 2 * b ≤ (N : ℤ) := Int.le_of_dvd (by exact_mod_cast hN) hdvd
  have hlt : a + 2 * b < (N : ℤ) := lt_of_le_of_ne hle hne
  lift a to ℕ using ha.le
  lift b to ℕ using hb.le
  lift c to ℕ using hc.le
  lift k to ℕ using hk.le
  have hdvd' : a + 2 * b ∣ N := by exact_mod_cast hdvd
  have hcc' : c ^ 2 = a ^ 2 + a * b + b ^ 2 := by exact_mod_cast hcc
  have hcop' : Nat.gcd b (a + 2 * b) = 1 := by
    have : IsCoprime ((b : ℕ) : ℤ) (((a + 2 * b : ℕ)) : ℤ) := by exact_mod_cast hcop
    exact Nat.isCoprime_iff_coprime.mp this
  obtain ⟨n', hn'⟩ := hdvd'
  have hepos : 0 < a + 2 * b := by omega
  have hdiv : N / (a + 2 * b) = n' := by rw [hn']; exact Nat.mul_div_cancel_left _ hepos
  have hkq : k ^ 2 = b * n' := by
    have h1 : (b : ℤ) * (N : ℤ) = (k : ℤ) ^ 2 * (a + 2 * b) := by exact_mod_cast harea
    have h2 : b * N = k ^ 2 * (a + 2 * b) := by exact_mod_cast h1
    rw [hn'] at h2
    have h3' : (a + 2 * b) * (b * n') = (a + 2 * b) * k ^ 2 := by linarith [h2]
    exact (Nat.eq_of_mul_eq_mul_left hepos h3').symm
  have hsc : Nat.sqrt (a ^ 2 + a * b + b ^ 2) = c := by rw [← hcc']; exact Nat.sqrt_eq' c
  have hsk : Nat.sqrt (b * (N / (a + 2 * b))) = k := by rw [hdiv, ← hkq]; exact Nat.sqrt_eq' k
  have hnA : ((k : ℤ) * ((c : ℤ) - a - b)) / b = nA := by
    have hb0 : (b : ℤ) ≠ 0 := by exact_mod_cast hb.ne'
    rw [hkc]; exact Int.mul_ediv_cancel nA hb0
  have hmod : ((k : ℤ) * ((c : ℤ) - a - b)) % b = 0 := Int.emod_eq_zero_of_dvd ⟨nA, by rw [hkc]; ring⟩
  have hpar' : ((nA - (N : ℤ)) % 2 = 0) := Int.emod_eq_zero_of_dvd hpar
  refine hchk a (by omega) b (by omega) (by exact_mod_cast ha) (by exact_mod_cast hb) (by omega) (by omega)
    ⟨n', hn'⟩ hcop' ?_ ?_ ?_ ?_
  · rw [hsc]; nlinarith [hcc']
  · rw [hsk, hdiv, ← hkq]; ring
  · rw [hsk, hsc]; exact hmod
  · rw [hsk, hsc, hnA]; exact hpar'

theorem isoH9b_22 : IsoH9b 22 := isoH9b_of_check 22 (by norm_num) (by decide +kernel)
theorem isoH9b_46 : IsoH9b 46 := isoH9b_of_check 46 (by norm_num) (by decide +kernel)
theorem isoH9b_66 : IsoH9b 66 := isoH9b_of_check 66 (by norm_num) (by decide +kernel)
theorem isoH9b_78 : IsoH9b 78 := isoH9b_of_check 78 (by norm_num) (by decide +kernel)

/-- Negative controls: `IsoH9 N` (the original hypothesis of `ThmIsoH9.thmIso_H9`) is FALSE at these N. -/
theorem not_isoH9_22 : ¬ IsoH9 22 := fun h => by
  have := h 5 3 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num); omega
theorem not_isoH9_46 : ¬ IsoH9 46 := fun h => by
  have := h 7 8 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num); omega
theorem not_isoH9_66 : ¬ IsoH9 66 := fun h => by
  have := h 5 3 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num); omega
theorem not_isoH9_78 : ¬ IsoH9 78 := fun h => by
  have := h 3 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num); omega

/-- `IsoH9b` is not trivially true: it FAILS at N = 33 (tile (5,3,7), e = 11, k = 3, `M_α = −1` odd, N odd). -/
theorem not_isoH9b_33 : ¬ IsoH9b 33 := fun h =>
  h 5 3 7 3 (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [Int.isCoprime_iff_gcd_eq_one]; decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

end Erdos634.Draft.CompositeIsoB

#print axioms Erdos634.Draft.CompositeIsoB.isoH9b_22
#print axioms Erdos634.Draft.CompositeIsoB.isoH9b_46
#print axioms Erdos634.Draft.CompositeIsoB.isoH9b_66
#print axioms Erdos634.Draft.CompositeIsoB.isoH9b_78
#print axioms Erdos634.Draft.CompositeIsoB.not_isoH9b_33
