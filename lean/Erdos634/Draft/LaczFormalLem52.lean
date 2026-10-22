-- Draft/LaczFormalLem52.lean -- Laczkovich, "Tilings of triangles", Discrete Math. 140 (1995) 79-94, Lemma 5.2 (p. 90).
-- Statement (our reading): let 0 < a < n be integers such that for every integer k prime to 2n the fractional part
-- {k a / n} is <= 1/3 or >= 2/3.  Then n = d * n1 with d = gcd(a, n) and n1 in {3, 4, 6, 10}.
-- Proof in the paper: reduce to a1 = a/d, n1 = n/d by a Chinese-remainder style lift (k = r + i n1 prime to 2n), then
-- Bertrand's postulate gives a prime q in (n1/3, 2 n1/3), forcing n1 = 2q and q = 5.  Re-proved here in my own words.
-- Role: step of Laczkovich's Thm 5.1 (the classification of rational-angle tilings of a triangle); see PLAN_L9_L7.md.
-- Satisfiable: a = 1, n = 6 (fractions 1/6, 5/6, 1/6, 5/6 for k = 1, 5, 7, 11).  UNAUDITED.
import Mathlib

open scoped Classical

namespace Erdos634.Draft.LaczFormal

/-- Arithmetic form of "{m/n1} <= 1/3 or >= 2/3". -/
def Far (n1 m : ℕ) : Prop := 3 * (m % n1) ≤ n1 ∨ 2 * n1 ≤ 3 * (m % n1)

theorem lem52_n1 {n1 : ℕ} (h2 : 2 ≤ n1) (h : ∀ m : ℕ, Nat.Coprime m n1 → Far n1 m) :
    n1 = 3 ∨ n1 = 4 ∨ n1 = 6 ∨ n1 = 10 := by
  by_cases hle : n1 ≤ 6
  · interval_cases n1
    · have := h 1 (by norm_num); unfold Far at this; omega
    · simp
    · simp
    · have := h 2 (by norm_num); unfold Far at this; omega
    · simp
  · push Not at hle
    obtain ⟨q, hq, hq1, hq2⟩ := Nat.exists_prime_lt_and_le_two_mul (n1 / 3) (by omega)
    have hlo : n1 < 3 * q := by omega
    have hhi : 3 * q < 2 * n1 := by
      have : 3 * q ≤ 6 * (n1 / 3) := by omega
      have h6 : 6 * (n1 / 3) ≤ 2 * n1 := by omega
      by_contra hc
      have h3 : 3 * q = 2 * n1 := by omega
      have : 3 ∣ 2 * n1 := ⟨q, h3.symm⟩
      have h3n : 3 ∣ n1 := by omega
      obtain ⟨t, rfl⟩ := h3n
      have : q = 2 * t := by omega
      subst this
      have hp2 : (2 * t).Prime := hq
      have := (Nat.prime_mul_iff.mp hp2)
      rcases this with ⟨_, h1⟩ | ⟨_, h1⟩
      · omega
      · omega
    have hqlt : q < n1 := by omega
    by_cases hd : q ∣ n1
    · obtain ⟨s, hs⟩ := hd
      have hs2 : s = 2 := by
        have : s < 3 := by
          by_contra hc; push Not at hc; nlinarith
        have : 1 < s := by
          by_contra hc; push Not at hc
          interval_cases s <;> omega
        omega
      subst hs2
      subst hs
      have hq5 : 5 ≤ q := by
        by_contra hc; push Not at hc
        have h4 : q = 4 := by omega
        subst h4
        exact absurd hq (by norm_num)
      have hodd : q % 2 = 1 := by
        by_contra hc
        have h2d : 2 ∣ q := by omega
        rcases hq.eq_one_or_self_of_dvd 2 h2d with h' | h' <;> omega
      have hc1 : Nat.Coprime (q - 2) q := by
        apply Nat.Coprime.symm
        exact (Nat.Prime.coprime_iff_not_dvd hq).mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
      have hc2 : Nat.Coprime (q - 2) 2 := by
        apply Nat.Coprime.symm
        exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
      have hcop : Nat.Coprime (q - 2) (q * 2) := Nat.Coprime.mul_right hc1 hc2
      have := h (q - 2) hcop
      unfold Far at this
      rw [Nat.mod_eq_of_lt (by omega)] at this
      omega
    · exfalso
      have hc : Nat.Coprime q n1 := (Nat.Prime.coprime_iff_not_dvd hq).mpr hd
      have := h q hc
      unfold Far at this
      rw [Nat.mod_eq_of_lt hqlt] at this
      omega

/-- **Laczkovich 1995, Lemma 5.2** (arithmetic form: `{k a/n} <= 1/3` is `3 * ((k a) % n) <= n`,
`{k a/n} >= 2/3` is `2 n <= 3 * ((k a) % n)`). -/
theorem lacz_lemma_5_2 {a n : ℕ} (h0 : 0 < a) (han : a < n)
    (h : ∀ k : ℕ, Nat.Coprime k (2 * n) →
      3 * ((k * a) % n) ≤ n ∨ 2 * n ≤ 3 * ((k * a) % n)) :
    ∃ n1 : ℕ, n = Nat.gcd a n * n1 ∧ (n1 = 3 ∨ n1 = 4 ∨ n1 = 6 ∨ n1 = 10) := by
  set d := Nat.gcd a n with hd
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left _ h0
  obtain ⟨a1, ha1⟩ : d ∣ a := Nat.gcd_dvd_left a n
  obtain ⟨n1, hn1⟩ : d ∣ n := Nat.gcd_dvd_right a n
  have hcop : Nat.Coprime a1 n1 := by
    have e1 : a / d = a1 := Nat.div_eq_of_eq_mul_right hdpos ha1
    have e2 : n / d = n1 := Nat.div_eq_of_eq_mul_right hdpos hn1
    have := Nat.coprime_div_gcd_div_gcd (m := a) (n := n) hdpos
    rwa [← hd, e1, e2] at this
  have ha1pos : 0 < a1 := by
    rcases Nat.eq_zero_or_pos a1 with h' | h'
    · rw [h'] at ha1; omega
    · exact h'
  have hlt : a1 < n1 := by
    by_contra hc; push Not at hc
    have : d * n1 ≤ d * a1 := Nat.mul_le_mul_left d hc
    omega
  have hn12 : 2 ≤ n1 := by omega
  refine ⟨n1, by rw [← hn1], lem52_n1 hn12 ?_⟩
  intro m hm
  -- lift m to r with r a1 = m (mod n1), r prime to n1
  have hφ : 0 < Nat.totient n1 := Nat.totient_pos.mpr (by omega)
  set r := m * a1 ^ (Nat.totient n1 - 1) with hr
  have hrcop : Nat.Coprime r n1 :=
    Nat.Coprime.mul_left hm (Nat.Coprime.pow_left _ hcop)
  have hrm : r * a1 ≡ m [MOD n1] := by
    have : r * a1 = m * a1 ^ Nat.totient n1 := by
      rw [hr, mul_assoc, ← pow_succ, Nat.sub_add_cancel hφ]
    rw [this]
    have h1 := Nat.ModEq.pow_totient hcop
    simpa using (Nat.ModEq.refl m).mul h1
  -- i = product of the primes of 2n not dividing r
  set i := ∏ p ∈ (2 * n).primeFactors.filter (fun p => ¬ p ∣ r), p with hi
  have hkcop : Nat.Coprime (r + i * n1) (2 * n) := by
    apply Nat.coprime_of_dvd
    intro p hp hpk hp2n
    by_cases hpr : p ∣ r
    · have hin : p ∣ i * n1 := (Nat.dvd_add_right hpr).mp hpk
      have hpn1 : ¬ p ∣ n1 := fun hh =>
        hp.one_lt.ne' (Nat.eq_one_of_dvd_one (hrcop ▸ Nat.dvd_gcd hpr hh))
      have hpi : ¬ p ∣ i := by
        intro hpi
        obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hpi
        have hqm := Finset.mem_filter.mp hq
        have : p = q := (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors hqm.1)).mp hpq
        exact hqm.2 (this ▸ hpr)
      rcases (Nat.Prime.dvd_mul hp).mp hin with h' | h'
      · exact hpi h'
      · exact hpn1 h'
    · have hpmem : p ∈ (2 * n).primeFactors.filter (fun p => ¬ p ∣ r) :=
        Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hp2n, by omega⟩, hpr⟩
      have hpi : p ∣ i := Finset.dvd_prod_of_mem _ hpmem
      have : p ∣ r := (Nat.dvd_add_left (dvd_mul_of_dvd_left hpi n1)).mp hpk
      exact hpr this
  have key := h _ hkcop
  have hmod : ((r + i * n1) * a) % n = d * (m % n1) := by
    have h1 : (r + i * n1) * a = d * ((r + i * n1) * a1) := by rw [ha1]; ring
    rw [h1, hn1, Nat.mul_mod_mul_left]
    congr 1
    have h2 : (r + i * n1) * a1 = r * a1 + (i * a1) * n1 := by ring
    rw [h2, Nat.add_mul_mod_self_right]
    exact hrm
  rw [hmod, hn1] at key
  unfold Far
  rcases key with k1 | k1
  · left; nlinarith
  · right; nlinarith


/-- **Corollary used at the start of Thm 5.1's case analysis (p. 91):** with `a/n <= 1/3` (`3 a <= n`) the hypothesis of Lemma 5.2 leaves only
`a/n ∈ {1/3, 1/4, 1/6, 1/10, 3/10}`. -/
theorem lacz_lemma_5_2_values {a n : ℕ} (h0 : 0 < a) (han : a < n) (h3 : 3 * a ≤ n)
    (h : ∀ k : ℕ, Nat.Coprime k (2 * n) →
      3 * ((k * a) % n) ≤ n ∨ 2 * n ≤ 3 * ((k * a) % n)) :
    n = 3 * a ∨ n = 4 * a ∨ n = 6 * a ∨ n = 10 * a ∨ 10 * a = 3 * n := by
  obtain ⟨n1, hn1, hcases⟩ := lacz_lemma_5_2 h0 han h
  set d := Nat.gcd a n with hd
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left _ h0
  obtain ⟨a1, ha1⟩ : d ∣ a := Nat.gcd_dvd_left a n
  have hcop : Nat.Coprime a1 n1 := by
    have e1 : a / d = a1 := Nat.div_eq_of_eq_mul_right hdpos ha1
    have e2 : n / d = n1 := Nat.div_eq_of_eq_mul_right hdpos hn1
    have := Nat.coprime_div_gcd_div_gcd (m := a) (n := n) hdpos
    rwa [← hd, e1, e2] at this
  have ha1pos : 0 < a1 := by
    rcases Nat.eq_zero_or_pos a1 with h' | h'
    · rw [h'] at ha1; omega
    · exact h'
  have h3' : 3 * a1 ≤ n1 := by
    have e : 3 * a = d * (3 * a1) := by rw [ha1]; ring
    have : d * (3 * a1) ≤ d * n1 := by rw [← e, ← hn1]; exact h3
    exact Nat.le_of_mul_le_mul_left this hdpos
  rcases hcases with rfl | rfl | rfl | rfl
  · left
    have : a1 = 1 := by omega
    subst this; omega
  · right; left
    have : a1 = 1 := by omega
    subst this; omega
  · right; right; left
    have : a1 = 1 := by
      have hlt : a1 ≤ 2 := by omega
      interval_cases a1
      · rfl
      · exfalso; revert hcop; norm_num
    subst this; omega
  · have : a1 = 1 ∨ a1 = 3 := by
      have hlt : a1 ≤ 3 := by omega
      interval_cases a1
      · exact Or.inl rfl
      · exfalso; revert hcop; norm_num
      · exact Or.inr rfl
    rcases this with rfl | rfl
    · right; right; right; left; omega
    · right; right; right; right; omega

/-- The same with fractional parts (the form printed in the paper). -/
theorem lacz_lemma_5_2_fract {a n : ℕ} (h0 : 0 < a) (han : a < n)
    (h : ∀ k : ℕ, Nat.Coprime k (2 * n) →
      Int.fract (((k * a : ℕ) : ℚ) / n) ≤ 1 / 3 ∨ 2 / 3 ≤ Int.fract (((k * a : ℕ) : ℚ) / n)) :
    ∃ n1 : ℕ, n = Nat.gcd a n * n1 ∧ (n1 = 3 ∨ n1 = 4 ∨ n1 = 6 ∨ n1 = 10) := by
  have hn : (0 : ℚ) < n := by exact_mod_cast (by omega : 0 < n)
  refine lacz_lemma_5_2 h0 han (fun k hk => ?_)
  have := h k hk
  rw [Int.fract_div_natCast_eq_div_natCast_mod] at this
  rcases this with h1 | h1
  · left
    rw [div_le_iff₀ hn] at h1
    have : (3 * (((k * a) % n : ℕ) : ℚ)) ≤ n := by linarith
    exact_mod_cast this
  · right
    rw [le_div_iff₀ hn] at h1
    have : (2 * n : ℚ) ≤ 3 * (((k * a) % n : ℕ) : ℚ) := by linarith
    exact_mod_cast this

/-- Non-vacuity: `a = 1`, `n = 6` satisfies the hypothesis (fractions `1/6`, `5/6`), and `n = gcd * 6`. -/
theorem lacz_lemma_5_2_witness :
    (∀ k : ℕ, Nat.Coprime k (2 * 6) → 3 * ((k * 1) % 6) ≤ 6 ∨ 2 * 6 ≤ 3 * ((k * 1) % 6)) := by
  intro k hk
  have h2 : ¬ 2 ∣ k := fun hh => by
    have := Nat.Coprime.coprime_dvd_right (by norm_num : 2 ∣ 2 * 6) hk
    have := Nat.Coprime.eq_one_of_dvd this.symm hh
    omega
  have h3 : ¬ 3 ∣ k := fun hh => by
    have := Nat.Coprime.coprime_dvd_right (by norm_num : 3 ∣ 2 * 6) hk
    have := Nat.Coprime.eq_one_of_dvd this.symm hh
    omega
  omega

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.lacz_lemma_5_2
#print axioms Erdos634.Draft.LaczFormal.lacz_lemma_5_2_values
