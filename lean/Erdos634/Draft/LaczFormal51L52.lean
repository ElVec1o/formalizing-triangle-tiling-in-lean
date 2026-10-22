import Mathlib

/-!
# Laczkovich Thm 5.1, Lemma 5.2 (Bertrand-type argument)

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Lemma 5.2), Beeson, Beeson-Zhang.
Formalization debt, not progress on the /goal outcomes.

Printed statement (the OCR reads "{ka/n} <= 1/3 or {ka/n} >= 2/3"): let `0 < a < n` be integers such that for every `k` prime to
`2n`, `{ka/n} <= 1/3` or `>= 2/3`.  Then `n = d n1` with `d = gcd(a, n)` and `n1 in {3,4,6,10}`.
Integer form of `{ka/n}`: `((k*a) % n) / n`.  Proof follows the printed one (lift a unit mod `n1` to a unit mod `2n`, then
Bertrand: a prime `q` with `n1/3 < q < 2 n1/3`).  No extra hypothesis was needed.
-/

namespace Erdos634.Lacz51

/-- (Mathlib `ZMod.unitsMap_surjective`, unfolded) every `x` prime to `n1` lifts to `x + t*n1` prime to `M`. -/
theorem coprime_lift {M : ℕ} (hM : M ≠ 0) {n1 x : ℕ} (hx : x.Coprime n1) :
    ∃ t : ℕ, (x + t * n1).Coprime M := by
  let ps : Finset ℕ := {p ∈ M.primeFactors | ¬p ∣ x}
  refine ⟨ps.prod id, ?_⟩
  apply Nat.coprime_of_dvd
  intro p pp hp hpn
  by_cases hpx : p ∣ x
  · have h := Nat.dvd_sub hp hpx
    rw [add_comm, Nat.add_sub_cancel] at h
    rcases pp.dvd_mul.mp h with h | h
    · have ⟨q, hq, hq'⟩ := (pp.prime.dvd_finsetProd_iff id).mp h
      rw [Finset.mem_filter, Nat.mem_primeFactors,
        ← (Nat.prime_dvd_prime_iff_eq pp hq.1.1).mp hq'] at hq
      exact hq.2 hpx
    · exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, pp, hpx, h⟩ hx
  · have pps : p ∈ ps := Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨pp, hpn, hM⟩, hpx⟩
    have h := Nat.dvd_sub hp ((Finset.dvd_prod_of_mem id pps).mul_right n1)
    rw [Nat.add_sub_cancel] at h
    contradiction

/-- The condition "`{m/n1} <= 1/3` or `>= 2/3`" in integer form. -/
def Good (n1 m : ℕ) : Prop := 3 * (m % n1) ≤ n1 ∨ 2 * n1 ≤ 3 * (m % n1)

/-- Second half of Lemma 5.2: `Good n1 m` for all `m` prime to `n1` (with `n1 >= 2`) forces `n1 in {3,4,6,10}`. -/
theorem core (n1 : ℕ) (hn1 : 2 ≤ n1) (P : ∀ m, Nat.Coprime m n1 → Good n1 m) :
    n1 = 3 ∨ n1 = 4 ∨ n1 = 6 ∨ n1 = 10 := by
  by_cases hle : n1 ≤ 6
  · interval_cases n1
    · exact absurd (P 1 (by decide)) (by unfold Good; decide)
    · simp
    · simp
    · exact absurd (P 2 (by decide)) (by unfold Good; decide)
    · simp
  · rw [not_le] at hle
    set t := n1 / 3 with ht
    have ht2 : 2 ≤ t := by omega
    obtain ⟨q, hq, hqt, hq2⟩ := Nat.exists_prime_lt_and_le_two_mul t (by omega)
    have hq3 : n1 < 3 * q := by omega
    have hq4 : 3 * q < 2 * n1 := by
      have : q ≠ 2 * t := by
        intro h
        have h2 : 2 ∣ q := ⟨t, h⟩
        rcases (Nat.dvd_prime hq).mp h2 with h3 | h3 <;> omega
      omega
    have hdvd : q ∣ n1 := by
      by_contra hnd
      have hc : Nat.Coprime q n1 := (Nat.Prime.coprime_iff_not_dvd hq).mpr hnd
      have := P q hc
      unfold Good at this
      rw [Nat.mod_eq_of_lt (by omega)] at this
      omega
    obtain ⟨s, hs⟩ := hdvd
    have hs2 : s = 2 := by
      rcases s with _ | _ | _ | s
      · omega
      · nlinarith
      · rfl
      · nlinarith
    subst hs2
    have hq5 : 5 ≤ q := by
      have := hq.two_le
      by_contra h
      interval_cases q <;> first | omega | exact absurd hq (by decide)
    have hodd : q % 2 = 1 := by
      rcases hq.eq_two_or_odd with h | h
      · omega
      · exact h
    have hc : Nat.Coprime (q - 2) n1 := by
      rw [hs]
      apply Nat.Coprime.mul_right
      · exact ((Nat.Prime.coprime_iff_not_dvd hq).mpr (by
          intro h; have := Nat.le_of_dvd (by omega) h; omega)).symm
      · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]; omega
    have := P (q - 2) hc
    unfold Good at this
    rw [hs, Nat.mod_eq_of_lt (by omega)] at this
    omega


/-- **Laczkovich Lemma 5.2** (integer form).  If `0 < a < n` and for every `k` prime to `2n` the fractional part `{ka/n}` is
`<= 1/3` or `>= 2/3`, then `n / gcd(a,n) in {3,4,6,10}`. -/
theorem lemma52 (a n : ℕ) (ha : 0 < a) (han : a < n)
    (H : ∀ k, Nat.Coprime k (2 * n) → 3 * ((k * a) % n) ≤ n ∨ 2 * n ≤ 3 * ((k * a) % n)) :
    n / Nat.gcd a n = 3 ∨ n / Nat.gcd a n = 4 ∨ n / Nat.gcd a n = 6 ∨ n / Nat.gcd a n = 10 := by
  set d := Nat.gcd a n with hd
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left _ ha
  obtain ⟨a1, ha1⟩ := Nat.gcd_dvd_left a n
  obtain ⟨n1, hn1⟩ := Nat.gcd_dvd_right a n
  rw [← hd] at ha1 hn1
  have hcop : Nat.Coprime a1 n1 := by
    have := Nat.coprime_div_gcd_div_gcd (m := a) (n := n) hdpos
    rw [← hd] at this
    rwa [ha1, hn1, Nat.mul_div_cancel_left _ hdpos, Nat.mul_div_cancel_left _ hdpos] at this
  have hnd : n / d = n1 := by rw [hn1, Nat.mul_div_cancel_left _ hdpos]
  rw [hnd]
  have hn1ge : 2 ≤ n1 := by
    by_contra h
    have : n1 = 0 ∨ n1 = 1 := by omega
    rcases this with h | h
    · subst h; simp at hn1; omega
    · subst h
      have : 1 ≤ a1 := by
        rcases Nat.eq_zero_or_pos a1 with h0 | h0
        · subst h0; simp at ha1; omega
        · exact h0
      nlinarith
  apply core n1 hn1ge
  intro m hm
  obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by omega)
  have hsc : Nat.Coprime s n1 := by
    have hg : Nat.gcd s n1 ∣ (a1 * s) % n1 := by
      rw [Nat.dvd_mod_iff (Nat.gcd_dvd_right s n1)]
      exact Dvd.dvd.mul_left (Nat.gcd_dvd_left s n1) _
    rw [hs] at hg
    exact Nat.eq_one_of_dvd_one hg
  have hrc : Nat.Coprime (m * s) n1 := Nat.Coprime.mul hm hsc
  obtain ⟨t, ht⟩ := coprime_lift (M := 2 * n) (by omega) hrc
  have hk := H _ ht
  have key : ((m * s + t * n1) * a) % n = d * (m % n1) := by
    have : (m * s + t * n1) * a = d * ((m * s + t * n1) * a1) := by rw [ha1]; ring
    rw [this, hn1, Nat.mul_mod_mul_left]
    congr 1
    have e : (m * s + t * n1) * a1 = m * (a1 * s) + n1 * (t * a1) := by ring
    rw [e, Nat.add_mul_mod_self_left, Nat.mul_mod, hs]
    simp
  rw [key, hn1] at hk
  unfold Good
  rcases hk with h | h
  · left; apply Nat.le_of_mul_le_mul_left _ hdpos; nlinarith
  · right; apply Nat.le_of_mul_le_mul_left _ hdpos; nlinarith

end Erdos634.Lacz51

#print axioms Erdos634.Lacz51.lemma52
