-- Draft/LaczFormalUnifA.lean -- number-theoretic helpers for the UNIFORM treatment of the 5-smooth residue of Laczkovich's Thm 5.1
-- (case `F = (p,0,0)`, `p in {3,4,6,10}`, tile angle `a_i = n/p`): (i) `pick_i`: a small `i0 <= 19` with `p | b + i0` and `gcd(i0,a) = 1`
-- (decidable case check over the residue of `b` mod `p` and the primes 2,3,5 dividing `a`); (ii) `Q_core`: a unit `k = p t - 1` with `k b = i0 + p a w`.
-- Replaces Laczkovich's interior-vertex argument ((4) and conjugates k = 5,7,11,13 on p. 92 of Discrete Math 140 (1995)) by the corner equation `F . x'(k) = 1`
-- at one explicit unit.  UNAUDITED (NOTE).  Credit: Laczkovich (Discrete Math 140 (1995) Thm 5.1; DCG 48 (2012)), Beeson-Rosu, Beeson.
import Mathlib

namespace Erdos634.Draft.LaczFormal

/-- Bool test: `i` is a valid pick for residue `r` mod `p` and flags `d2,d3,d5` (0/1: does the prime divide `a`). -/
def pickOk (p r d2 d3 d5 i : ℕ) : Bool :=
  (decide (1 ≤ i)) && ((r + i) % p == 0) && (d2 == 0 || i % 2 != 0) && (d3 == 0 || i % 3 != 0) && (d5 == 0 || i % 5 != 0)

/-- Bool test: the flags are compatible with `gcd(a,b) = 1` for `r = b mod p`. -/
def feasB (p r d2 d3 d5 : ℕ) : Bool :=
  (d2 == 0 || p % 2 != 0 || r % 2 != 0) && (d3 == 0 || p % 3 != 0 || r % 3 != 0) && (d5 == 0 || p % 5 != 0 || r % 5 != 0)

/-- All checks, as one Boolean (kernel-evaluated). -/
def allChk : Bool :=
  (List.range 11).all fun p => !(p == 3 || p == 4 || p == 6 || p == 10) ||
    (List.range p).all fun r => (List.range 2).all fun d2 => (List.range 2).all fun d3 => (List.range 2).all fun d5 =>
      !feasB p r d2 d3 d5 || (List.range 20).any (pickOk p r d2 d3 d5)

theorem allChk_true : allChk = true := by decide +kernel

/-- Decidable core of `pick_i`: for `p in {3,4,6,10}`, residue `r = b mod p`, and flags, some `i < 20` is a valid pick. -/
theorem pick_i_decide {p r d2 d3 d5 : ℕ} (hp11 : p < 11) (hp : p = 3 ∨ p = 4 ∨ p = 6 ∨ p = 10) (hr : r < p)
    (h2 : d2 < 2) (h3 : d3 < 2) (h5 : d5 < 2) (hf : feasB p r d2 d3 d5 = true) :
    (List.range 20).any (pickOk p r d2 d3 d5) = true := by
  have h := allChk_true
  unfold allChk at h
  rw [List.all_eq_true] at h
  have h1 := h p (List.mem_range.mpr hp11)
  have hp' : (p == 3 || p == 4 || p == 6 || p == 10) = true := by
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  rw [hp'] at h1
  simp only [Bool.not_true, Bool.false_or, List.all_eq_true, List.mem_range] at h1
  have h6 := h1 r hr d2 h2 d3 h3 d5 h5
  rw [hf] at h6
  simpa using h6

theorem pick_i {p a b : ℕ} (hp : p = 3 ∨ p = 4 ∨ p = 6 ∨ p = 10)
    (hsm : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ a → ℓ ≤ 5) (hcop : Nat.Coprime a b) :
    ∃ i, 1 ≤ i ∧ i ≤ 19 ∧ p ∣ b + i ∧ Nat.Coprime i a := by
  have hpos : 0 < p := by rcases hp with rfl | rfl | rfl | rfl <;> norm_num
  have hp11 : p < 11 := by rcases hp with rfl | rfl | rfl | rfl <;> norm_num
  have hl : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ a → ℓ ∣ p → (b % p) % ℓ ≠ 0 := by
    intro ℓ hℓ hla hlp h0
    have h1 : ℓ ∣ b % p := Nat.dvd_of_mod_eq_zero h0
    have h2 : ℓ ∣ b := by
      have := Nat.mod_add_div b p
      rw [← this]
      exact dvd_add h1 (Dvd.dvd.mul_right hlp _)
    have h3 : ℓ ∣ Nat.gcd a b := Nat.dvd_gcd hla h2
    rw [hcop] at h3
    exact hℓ.one_lt.ne' (Nat.dvd_one.mp h3)
  have hfe : feasB p (b % p) (if 2 ∣ a then 1 else 0) (if 3 ∣ a then 1 else 0) (if 5 ∣ a then 1 else 0) = true := by
    unfold feasB
    have e2 := hl 2 Nat.prime_two
    have e3 := hl 3 Nat.prime_three
    have e5 := hl 5 Nat.prime_five
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · by_cases h : 2 ∣ a
      · by_cases hq : 2 ∣ p
        · right; exact e2 h hq
        · left; right; intro h0; exact hq (Nat.dvd_of_mod_eq_zero h0)
      · left; left; simp [h]
    · by_cases h : 3 ∣ a
      · by_cases hq : 3 ∣ p
        · right; exact e3 h hq
        · left; right; intro h0; exact hq (Nat.dvd_of_mod_eq_zero h0)
      · left; left; simp [h]
    · by_cases h : 5 ∣ a
      · by_cases hq : 5 ∣ p
        · right; exact e5 h hq
        · left; right; intro h0; exact hq (Nat.dvd_of_mod_eq_zero h0)
      · left; left; simp [h]
  have hany := pick_i_decide hp11 hp (Nat.mod_lt b hpos) (by split_ifs <;> norm_num) (by split_ifs <;> norm_num)
    (by split_ifs <;> norm_num) hfe
  rw [List.any_eq_true] at hany
  obtain ⟨i, hi, hok⟩ := hany
  rw [List.mem_range] at hi
  simp only [pickOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true, bne_iff_ne, ne_eq] at hok
  obtain ⟨⟨⟨⟨hi1, h1⟩, h2⟩, h3⟩, h4⟩ := hok
  refine ⟨i, hi1, by omega, ?_, ?_⟩
  · have hm : (b % p + i) ≡ b + i [MOD p] := (Nat.mod_modEq b p).add_right i
    have hd : p ∣ b % p + i := Nat.dvd_of_mod_eq_zero h1
    exact (hm.dvd_iff (dvd_refl p)).mp hd
  · apply Nat.coprime_of_dvd
    intro ℓ hℓ hli hla
    have h5 := hsm ℓ hℓ hla
    have hl2 : ℓ = 2 ∨ ℓ = 3 ∨ ℓ = 5 := by
      have h2' : 2 ≤ ℓ := hℓ.two_le
      interval_cases ℓ
      · simp
      · simp
      · exact absurd hℓ (by norm_num)
      · simp
    rcases hl2 with rfl | rfl | rfl
    · rcases h2 with h2 | h2
      · simp [hla] at h2
      · exact h2 (Nat.mod_eq_zero_of_dvd hli)
    · rcases h3 with h3 | h3
      · simp [hla] at h3
      · exact h3 (Nat.mod_eq_zero_of_dvd hli)
    · rcases h4 with h4 | h4
      · simp [hla] at h4
      · exact h4 (Nat.mod_eq_zero_of_dvd hli)

/-- Explicit unit: `k = p t - 1`, `k b = i + p a w`, `k` prime to `p a`. -/
theorem Q_core {p a b i : ℕ} (hp : 0 < p) (ha : 0 < a) (hab : Nat.Coprime a b) (hdiv : p ∣ b + i)
    (hi : Nat.Coprime i a) :
    ∃ (k t w : ℤ), k = p * t - 1 ∧ k * b = i + ((p * a : ℕ) : ℤ) * w ∧ IsCoprime k ((p * a : ℕ) : ℤ) := by
  obtain ⟨s, hs⟩ := hdiv
  have hab' : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hab
  obtain ⟨u, v, huv⟩ := hab'
  -- u a + v b = 1, so v b = 1 - u a
  refine ⟨p * (s * v) - 1, s * v, -(s * u), rfl, ?_, ?_⟩
  · have hs' : (b : ℤ) + i = p * s := by exact_mod_cast hs
    push_cast
    linear_combination ((p:ℤ) * s) * huv - hs'
  · have hk1 : IsCoprime ((p:ℤ) * (s * v) - 1) (p : ℤ) := ⟨-1, s * v, by ring⟩
    have hia : IsCoprime (i : ℤ) (a : ℤ) := Nat.isCoprime_iff_coprime.mpr hi
    have hs' : (b : ℤ) + i = p * s := by exact_mod_cast hs
    have heq : ((p:ℤ) * (s * v) - 1) * b = i + a * (p * -(s * u)) := by
      linear_combination ((p:ℤ) * s) * huv - hs'
    have hkb : IsCoprime (((p:ℤ) * (s * v) - 1) * b) (a : ℤ) := by
      rw [heq]; exact hia.add_mul_left_left _
    have hk2 : IsCoprime ((p:ℤ) * (s * v) - 1) (a : ℤ) := hkb.of_mul_left_left
    push_cast
    exact hk1.mul_right hk2

/-- Primes in `[7, 200]`. -/
def primes7 : List ℕ := [7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199]

theorem primes7_prime : ∀ ℓ ∈ primes7, ℓ.Prime := by
  intro ℓ hℓ
  simp only [primes7, List.mem_cons, List.not_mem_nil, or_false] at hℓ
  rcases hℓ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- The 5-smooth integers in `[3, 200]`. -/
def smoothList : List ℕ := [3, 4, 5, 6, 8, 9, 10, 12, 15, 16, 18, 20, 24, 25, 27, 30, 32, 36, 40, 45, 48, 50, 54, 60, 64, 72, 75, 80, 81, 90, 96, 100, 108, 120, 125, 128, 135, 144, 150, 160, 162, 180, 192, 200]

def smoothChk : Bool :=
  (List.range 201).all fun n => decide (n < 3) || primes7.any (fun ℓ => n % ℓ == 0) || smoothList.contains n

theorem smoothChk_true : smoothChk = true := by decide +kernel

theorem smooth_le200 {n : ℕ} (hn : n < 201) (h3 : 3 ≤ n) (h : ∀ ℓ ∈ primes7, ¬ ℓ ∣ n) : n ∈ smoothList := by
  have h1 := smoothChk_true
  unfold smoothChk at h1
  rw [List.all_eq_true] at h1
  have h2 := h1 n (List.mem_range.mpr hn)
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq, List.contains_iff_mem] at h2
  rcases h2 with (h2 | ⟨ℓ, hℓ, hd⟩) | h2
  · omega
  · exact absurd (Nat.dvd_of_mod_eq_zero hd) (h ℓ hℓ)
  · exact h2

end Erdos634.Draft.LaczFormal
