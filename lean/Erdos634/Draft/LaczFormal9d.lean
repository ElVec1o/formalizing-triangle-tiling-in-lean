import Erdos634.Draft.LaczFormal9c

/-!
# Laczkovich, Discrete Math. 140 (1995), Theorem 3.4

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) Thm 3.3, Thm 3.4), Beeson, Beeson-Zhang.
Formalization debt, not progress on the /goal outcomes.

Printed Theorem 3.4: let `P` be any finite set of primes.  Then there is an `n` such that the equilateral triangle can be dissected
into `n` congruent triangles and every `p in P` has an odd exponent in the prime factorization of `n`.
Printed proof: `q` = product of the odd elements of `P`, `x = 4 q`, `y = 1`, Theorem 3.3 gives `n = 4q (4q+2)(1+8q) k^2`.
`dm140_thm34` is that statement, from `dm140_thm33` (and so `N = 8 q (2q+1)(8q+1) k^2`).
-/

open scoped Classical
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional

namespace Erdos634.Laczkovich9

theorem pv_prod (p : ℕ) [Fact p.Prime] (a b c d k : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (hk : k ≠ 0) :
    padicValNat p (a * b * c * d * k ^ 2) =
      padicValNat p a + padicValNat p b + padicValNat p c + padicValNat p d + 2 * padicValNat p k := by
  rw [padicValNat.mul (mul_ne_zero (mul_ne_zero (mul_ne_zero ha hb) hc) hd) (pow_ne_zero 2 hk),
    padicValNat.mul (mul_ne_zero (mul_ne_zero ha hb) hc) hd, padicValNat.mul (mul_ne_zero ha hb) hc,
    padicValNat.mul ha hb, padicValNat.pow 2 hk]

/-- **Laczkovich DM 140 (1995), Theorem 3.4.** -/
theorem dm140_thm34 (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∃ (N : ℕ) (D : CongruentDissection N), Equilateral D ∧ ∀ p ∈ S, Odd (padicValNat p N) := by
  set T : Finset ℕ := S.filter (fun p => p ≠ 2) with hT
  have hTp : ∀ p ∈ T, p.Prime := fun p hp => hS p (Finset.mem_filter.mp hp).1
  have hT2 : ∀ p ∈ T, p ≠ 2 := fun p hp => (Finset.mem_filter.mp hp).2
  set q : ℕ := ∏ p ∈ T, p with hq
  have hq0 : q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun p hp => (hTp p hp).ne_zero)
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
  have hq2 : ¬ 2 ∣ q := by
    intro hd
    rcases (Prime.dvd_finsetProd_iff Nat.prime_two.prime _).mp hd with ⟨r, hr, h2r⟩
    exact hT2 r hr ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (hTp r hr)).mp h2r).symm
  -- Theorem 3.3 with x = 4 q, y = 1
  have hx : ((4 * q : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (by omega : 4 * q ≠ 0)
  obtain ⟨k, N, hk, hN, D, hEq, -⟩ := dm140_thm33 ((4 * q : ℕ) : ℤ) 1 hx one_ne_zero
    (by push_cast; omega) (by push_cast; omega)
  have hval : (((4 * q : ℕ) : ℤ) * 1 * (((4 * q : ℕ) : ℤ) + 2 * 1) * (1 + 2 * ((4 * q : ℕ) : ℤ))).natAbs
      = 4 * q * (4 * q + 2) * (8 * q + 1) := by
    have : (((4 * q : ℕ) : ℤ) * 1 * (((4 * q : ℕ) : ℤ) + 2 * 1) * (1 + 2 * ((4 * q : ℕ) : ℤ)))
        = ((4 * q * (4 * q + 2) * (8 * q + 1) : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.natAbs_natCast]
  rw [hval] at hN
  have hN' : N = 8 * q * (2 * q + 1) * (8 * q + 1) * k ^ 2 := by rw [hN]; ring
  refine ⟨N, D, hEq, ?_⟩
  intro p hp
  have hpp : p.Prime := hS p hp
  haveI : Fact p.Prime := ⟨hpp⟩
  have hk0 : k ≠ 0 := hk.ne'
  have hsplit : padicValNat p N = padicValNat p 8 + padicValNat p q + padicValNat p (2 * q + 1) +
      padicValNat p (8 * q + 1) + 2 * padicValNat p k := by
    rw [hN']
    exact pv_prod p 8 q (2 * q + 1) (8 * q + 1) k (by norm_num) hq0 (by omega) (by omega) hk0
  rw [hsplit]
  by_cases hp2 : p = 2
  · subst hp2
    have v8 : padicValNat 2 8 = 3 := by
      have : (8 : ℕ) = 2 ^ 3 := by norm_num
      rw [this, padicValNat.prime_pow]
    have vq : padicValNat 2 q = 0 := padicValNat.eq_zero_of_not_dvd hq2
    have v2 : padicValNat 2 (2 * q + 1) = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
    have v3 : padicValNat 2 (8 * q + 1) = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
    rw [v8, vq, v2, v3]
    exact ⟨1 + padicValNat 2 k, by omega⟩
  · have hpT : p ∈ T := Finset.mem_filter.mpr ⟨hp, hp2⟩
    have hpq : p ∣ q := Finset.dvd_prod_of_mem _ hpT
    have v8 : padicValNat p 8 = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      intro hd
      have h8 : p ∣ 2 ^ 3 := by norm_num; exact hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow h8))
    have vq : padicValNat p q = 1 := by
      have hsp : p * ∏ r ∈ T.erase p, r = q := Finset.mul_prod_erase T (fun x => x) hpT
      have hnd : ¬ p ∣ ∏ r ∈ T.erase p, r := by
        intro hd
        rcases (Prime.dvd_finsetProd_iff hpp.prime _).mp hd with ⟨r, hr, hpr⟩
        have hrp : r.Prime := hTp r (Finset.mem_of_mem_erase hr)
        exact (Finset.ne_of_mem_erase hr) ((Nat.prime_dvd_prime_iff_eq hpp hrp).mp hpr).symm
      have hne : ∏ r ∈ T.erase p, r ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun r hr => (hTp r (Finset.mem_of_mem_erase hr)).ne_zero)
      rw [← hsp, padicValNat.mul hpp.ne_zero hne, padicValNat.self hpp.one_lt,
        padicValNat.eq_zero_of_not_dvd hnd]
    have v2 : padicValNat p (2 * q + 1) = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      intro hd
      have : p ∣ 1 := (Nat.dvd_add_right (dvd_mul_of_dvd_right hpq 2)).mp hd
      exact hpp.one_lt.ne' (Nat.dvd_one.mp this)
    have v3 : padicValNat p (8 * q + 1) = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      intro hd
      have : p ∣ 1 := (Nat.dvd_add_right (dvd_mul_of_dvd_right hpq 8)).mp hd
      exact hpp.one_lt.ne' (Nat.dvd_one.mp this)
    rw [v8, vq, v2, v3]
    exact ⟨padicValNat p k, by omega⟩

end Erdos634.Laczkovich9

#print axioms Erdos634.Laczkovich9.dm140_thm34
