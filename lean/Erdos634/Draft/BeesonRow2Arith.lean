import Mathlib

/-!
# Beeson (arXiv 1206.2229 v4), Theorem 7 (algebra), Corollary 1 (arithmetic), Corollary 3, Lemmas 46, 47, 50 (arithmetic)

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4), Beeson-Zhang, Laczkovich (DCG 48 (2012)).
Formalization debt, not progress on the /goal outcomes.  Pure arithmetic; no H1, no tiling hypotheses.
Map rows T-T7 (algebra half), T-C1, T-C3, T-L46, T-L47 (printed form), T-L50 (arithmetic half).

PRINT NOTES (found while formalizing):
* Printed Lemma 46 says "N prime ==> N = +-1 (mod 8)".  The proof only uses that `N = 2k^2 - m^2` is odd (then `m` odd,
  `m^2 = 1 mod 8`, `N = 2k^2 - 1`), so neither primality beyond oddness nor `gcd(m,k) = 1` is needed; "N prime"
  must exclude N = 2 (arithmetic alone allows N = 2 with (m,k) = (4,3), but that violates m < k, which is used here).
* Printed Lemma 47 hypothesis "N prime" is used only through `j^2 | N`.
-/

namespace Erdos634.BeesonRow2

/-- Printed Theorem 7, algebra: `N s^2 = M^2 (2 - s^2)`, `0 < s < 1`, `M != 0` give `s^2 (N + M^2) = 2 M^2`,
`s^2 = 2M^2/(N+M^2)` and `M^2 < N`. -/
theorem thm7_alg (s M N : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hM : M ≠ 0) (h : N * s ^ 2 = M ^ 2 * (2 - s ^ 2)) :
    s ^ 2 * (N + M ^ 2) = 2 * M ^ 2 ∧ s ^ 2 = 2 * M ^ 2 / (N + M ^ 2) ∧ M ^ 2 < N := by
  have e : s ^ 2 * (N + M ^ 2) = 2 * M ^ 2 := by linarith
  have hM2 : 0 < M ^ 2 := by positivity
  have hs2 : 0 < s ^ 2 := by positivity
  have hpos : 0 < N + M ^ 2 := by
    by_contra hh; push_neg at hh; nlinarith
  refine ⟨e, ?_, ?_⟩
  · rw [eq_div_iff hpos.ne']; exact e
  · have : s ^ 2 < 1 := by nlinarith
    nlinarith

/-- Printed Corollary 1 (arithmetic): `m^2 N = M^2 (2k^2 - m^2)` with `gcd(m,k) = 1`, `m > 0` forces `m | M`, and with
`j = M/m`: `N = j^2 (2k^2 - m^2)`. -/
theorem cor1_arith (m k M N : ℤ) (hm : 0 < m) (hmk : IsCoprime m k) (h : m ^ 2 * N = M ^ 2 * (2 * k ^ 2 - m ^ 2)) :
    ∃ j : ℤ, M = j * m ∧ N = j ^ 2 * (2 * k ^ 2 - m ^ 2) := by
  have key : m ∣ M := by
    by_cases hM : M = 0
    · exact ⟨0, by simp [hM]⟩
    have hgp : 0 < Int.gcd m M := Int.gcd_pos_of_ne_zero_left _ hm.ne'
    obtain ⟨g, m', M', hg0, hg1, hm', hM'⟩ := Int.exists_gcd_one' hgp
    have hg0' : (0 : ℤ) < g := by exact_mod_cast hg0
    have hcop : IsCoprime m' M' := Int.isCoprime_iff_gcd_eq_one.mpr hg1
    have h2 : m' ^ 2 * N = M' ^ 2 * (2 * k ^ 2 - m ^ 2) := by
      have hg2 : (g : ℤ) ^ 2 ≠ 0 := by positivity
      apply mul_left_cancel₀ hg2
      rw [hm', hM'] at h
      rw [hm']
      linear_combination h
    have hd1 : m' ^ 2 ∣ 2 * k ^ 2 - m ^ 2 := by
      have : m' ^ 2 ∣ M' ^ 2 * (2 * k ^ 2 - m ^ 2) := ⟨N, by rw [← h2]; try ring⟩
      exact (hcop.pow (m := 2) (n := 2)).dvd_of_dvd_mul_left this
    have hd2 : m' ^ 2 ∣ 2 * k ^ 2 := by
      have hm2 : m' ^ 2 ∣ m ^ 2 := ⟨(g : ℤ) ^ 2, by rw [hm']; try ring⟩
      have := dvd_add hd1 hm2
      simpa using this
    have hck : IsCoprime m' k := IsCoprime.of_mul_left_left (show IsCoprime (m' * g) k by rw [← hm']; exact hmk)
    have hd3 : m' ^ 2 ∣ 2 := (hck.pow (m := 2) (n := 2)).dvd_of_dvd_mul_right hd2
    have hm'0 : m' ≠ 0 := by rintro rfl; simp at hm'; omega
    have hle : m' ^ 2 ≤ 2 := Int.le_of_dvd (by norm_num) hd3
    have hm'1 : m' = 1 ∨ m' = -1 := by
      have : m' ^ 2 = 1 := by
        have : 0 < m' ^ 2 := by positivity
        have : m' ^ 2 ≠ 2 := by
          intro h2'
          have : m' ≤ 1 := by nlinarith
          have : -1 ≤ m' := by nlinarith
          have : m' = 1 ∨ m' = 0 ∨ m' = -1 := by omega
          rcases this with h | h | h
          · rw [h] at h2'; norm_num at h2'
          · exact hm'0 h
          · rw [h] at h2'; norm_num at h2'
        omega
      have : m' * m' = 1 := by nlinarith
      exact Int.eq_one_or_neg_one_of_mul_eq_one this
    rcases hm'1 with h1 | h1
    · exact ⟨M', by rw [hM', hm', h1]; try ring⟩
    · exact ⟨-M', by rw [hM', hm', h1]; try ring⟩
  obtain ⟨j, hj⟩ := key
  refine ⟨j, by rw [hj]; ring, ?_⟩
  subst hj
  have : m ^ 2 * (N - j ^ 2 * (2 * k ^ 2 - m ^ 2)) = 0 := by nlinarith [h]
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd h0 (by positivity)
  · linarith


/-- Printed Lemma 47: `(M,K) = j (m,k)`, `N = 2K^2 - M^2 > 0` prime, then `j = 1` (`j > 0`). -/
theorem lemma47 (j m k N : ℕ) (hj : 0 < j) (hN : N.Prime) (h : (N : ℤ) = 2 * ((j * k : ℕ) : ℤ) ^ 2 - ((j * m : ℕ) : ℤ) ^ 2) :
    j = 1 := by
  have hD : ∃ D : ℤ, (N : ℤ) = (j : ℤ) ^ 2 * D := ⟨2 * (k : ℤ) ^ 2 - (m : ℤ) ^ 2, by rw [h]; push_cast; ring⟩
  obtain ⟨D, hD⟩ := hD
  have hdv : j ∣ N := by
    have : (j : ℤ) ∣ (N : ℤ) := ⟨(j : ℤ) * D, by rw [hD]; ring⟩
    exact_mod_cast this
  rcases (Nat.dvd_prime hN).mp hdv with h1 | h1
  · exact h1
  · exfalso
    -- j = N, so N^2 | N
    have h2 : (j : ℤ) ^ 2 ∣ (N : ℤ) := ⟨D, hD⟩
    have h3 : j ^ 2 ∣ N := by exact_mod_cast h2
    rw [h1] at h3
    have := Nat.le_of_dvd hN.pos h3
    have := hN.two_le
    nlinarith

/-- Printed Lemma 46 (arithmetic): `N + m^2 = 2 k^2`, `0 < m < k`, `N` prime: `m` odd, and either
`N = 1 (mod 8)` with `k` odd, or `N = 7 (mod 8)` with `k` even.  See the print note in the header. -/
theorem lemma46 (N m k : ℕ) (hN : N.Prime) (hm : 0 < m) (hmk : m < k) (h : N + m ^ 2 = 2 * k ^ 2) :
    m % 2 = 1 ∧ ((N % 8 = 1 ∧ k % 2 = 1) ∨ (N % 8 = 7 ∧ k % 2 = 0)) := by
  have hN2 : N ≠ 2 := by
    rintro rfl
    have : 2 ≤ k := by omega
    nlinarith
  have hodd : N % 2 = 1 := (hN.eq_one_or_self_of_dvd 2 |>.mt (by
    intro hh; exact hN2 (by rcases hh with h | h <;> omega))) |> fun _ => by
      rcases hN.eq_two_or_odd with h | h
      · exact absurd h hN2
      · exact h
  have hmodd : m % 2 = 1 := by
    by_contra hh
    have hm0 : m % 2 = 0 := by omega
    obtain ⟨t, rfl⟩ : 2 ∣ m := by omega
    have : N = 2 * (k ^ 2 - 2 * t ^ 2) := by
      have h' : N + 4 * t ^ 2 = 2 * k ^ 2 := by nlinarith [h]
      omega
    omega
  refine ⟨hmodd, ?_⟩
  have hm8 : m ^ 2 % 8 = 1 := by
    have : m % 8 = 1 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 7 := by omega
    rcases this with h | h | h | h <;> simp [Nat.pow_mod, h]
  have hk8 : k ^ 2 % 8 = 0 ∨ k ^ 2 % 8 = 1 ∨ k ^ 2 % 8 = 4 := by
    have : k % 8 < 8 := Nat.mod_lt _ (by norm_num)
    have : k % 8 = 0 ∨ k % 8 = 1 ∨ k % 8 = 2 ∨ k % 8 = 3 ∨ k % 8 = 4 ∨ k % 8 = 5 ∨ k % 8 = 6 ∨ k % 8 = 7 := by omega
    rcases this with h | h | h | h | h | h | h | h <;> simp [Nat.pow_mod, h]
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · right
    have : k ^ 2 % 8 = 0 ∨ k ^ 2 % 8 = 4 := by
      rcases hk8 with h | h | h
      · left; exact h
      · exfalso
        have : k % 8 = 1 ∨ k % 8 = 3 ∨ k % 8 = 5 ∨ k % 8 = 7 → False := by
          intro hh; omega
        have hk' : k % 8 = 0 ∨ k % 8 = 2 ∨ k % 8 = 4 ∨ k % 8 = 6 := by omega
        rcases hk' with h' | h' | h' | h' <;> simp [Nat.pow_mod, h'] at h
      · right; exact h
    refine ⟨by omega, hk⟩
  · left
    have hk1 : k ^ 2 % 8 = 1 := by
      have hk' : k % 8 = 1 ∨ k % 8 = 3 ∨ k % 8 = 5 ∨ k % 8 = 7 := by omega
      rcases hk' with h' | h' | h' | h' <;> simp [Nat.pow_mod, h']
    exact ⟨by omega, hk⟩

/-- Printed Corollary 3: `n = k t`, `n < K = j k`, `k > 0` give `t < j`; if `j = 1` then `n = 0`. -/
theorem cor3 (n k t j : ℕ) (hk : 0 < k) (hn : n = k * t) (hlt : n < j * k) : t < j ∧ (j = 1 → n = 0) := by
  have ht : t < j := by
    by_contra hh; push_neg at hh
    have : j * k ≤ t * k := Nat.mul_le_mul_right k hh
    nlinarith
  refine ⟨ht, fun hj => ?_⟩
  subst hj
  have : t = 0 := by omega
  simp [hn, this]

/-- Printed Lemma 50 (integrality half): from `s = a/c` with integers `a < c`, the scaled tile `(ac, c^2 - a^2, c^2)`
has integer sides, satisfies `A^2 + C B = C^2` (Lemma 3's relation) and has the same ratio `A/C = a/c`. -/
theorem lemma50_int (a c : ℕ) (hc : 0 < c) (hac : a < c) :
    ∃ A B C : ℕ, A = a * c ∧ B = c ^ 2 - a ^ 2 ∧ C = c ^ 2 ∧ A ^ 2 + C * B = C ^ 2 ∧
      (A : ℚ) / C = (a : ℚ) / c := by
  refine ⟨a * c, c ^ 2 - a ^ 2, c ^ 2, rfl, rfl, rfl, ?_, ?_⟩
  · have : a ^ 2 ≤ c ^ 2 := Nat.pow_le_pow_left hac.le 2
    zify [this]; ring
  · have : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
    push_cast; field_simp

/-! Witnesses (non-vacuity of the hypotheses). -/
example : (2 : ℕ) ^ 2 = 2 * 2 := rfl
theorem wit_lemma46 : (1 % 2 = 1) ∧ (((7 : ℕ) % 8 = 1 ∧ 2 % 2 = 1) ∨ ((7 : ℕ) % 8 = 7 ∧ 2 % 2 = 0)) :=
  lemma46 7 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
theorem wit_lemma46' : (1 % 2 = 1) ∧ (((17 : ℕ) % 8 = 1 ∧ 3 % 2 = 1) ∨ ((17 : ℕ) % 8 = 7 ∧ 3 % 2 = 0)) :=
  lemma46 17 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
/-- Cor 1 witness: `j = 3, m = 1, k = 2`: `N = 9*7 = 63`, `M = 3`: `1 * 63 = 9 * 7`. -/
theorem wit_cor1 : ∃ j : ℤ, (3 : ℤ) = j * 1 ∧ (63 : ℤ) = j ^ 2 * (2 * 2 ^ 2 - 1 ^ 2) :=
  cor1_arith 1 2 3 63 (by norm_num) (by norm_num [Int.isCoprime_iff_gcd_eq_one]) (by norm_num)
theorem wit_lemma47 : (1 : ℕ) = 1 := lemma47 1 1 2 7 (by norm_num) (by norm_num) (by norm_num)

end Erdos634.BeesonRow2
