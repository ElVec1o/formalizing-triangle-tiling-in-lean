-- Draft/CaseALemmaVCore.lean — CASE A, node A2 (Lemma V), the ALGEBRAIC core, no dissection.
-- Source: (private working notes, not included) §3.2 steps 4–6.
--   * `reduced`:  in 𝓞 K, K = ℚ(ζ_m), a prime ℓ ∤ m satisfies ℓ ∣ x² → ℓ ∣ x
--     (ℓ unramified: Mathlib's `ramificationIdx_eq_of_not_dvd` ⇒ span{ℓ} squarefree).
--   * `one_sub_dvd`: 1 − ω ∣ m for every m-th root of unity ω ≠ 1 (so every S(jπ/n) is an
--     ℓ-unit for ℓ ∤ 4n, step 4).
--   * `even_of_eq`: N·A = Y²·B with A, B dividing integers prime to ℓ ⇒ v_ℓ(N) even (step 6).
-- This avoids the ℓ-adic valuation on 𝓞 K: induction on v_ℓ(N) plus reducedness of 𝓞 K/ℓ.
-- Mathlib only.  Formalization debt; NOT /goal progress.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
-- Hazard H59: no parameter pair (e, f) is evaluated here.
import Mathlib

namespace Erdos634.Geometry.CaseA.LemmaV

open Ideal NumberField UniqueFactorizationMonoid

variable {K : Type*} [Field K] [NumberField K] {m : ℕ} [NeZero m]
  [IsCyclotomicExtension {m} ℚ K]

/-- span{ℓ} in 𝓞 ℚ(ζ_m) is squarefree when ℓ ∤ m (ℓ unramified). -/
theorem span_squarefree {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (hm : ¬ ℓ ∣ m) :
    Squarefree (span {((ℓ : ℤ) : 𝓞 K)}) := by
  have hmap : map (algebraMap ℤ (𝓞 K)) (span {(ℓ : ℤ)}) = span {((ℓ : ℤ) : 𝓞 K)} := by
    rw [map_span, Set.image_singleton]; simp
  have hne : span {((ℓ : ℤ) : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, span_singleton_eq_bot]
    exact_mod_cast hℓ.out.ne_zero
  rw [squarefree_iff_nodup_normalizedFactors hne, Multiset.nodup_iff_count_le_one]
  intro P
  by_cases hP : P ∈ normalizedFactors (span {((ℓ : ℤ) : 𝓞 K)})
  · have hPp : Prime P := prime_of_normalized_factor P hP
    have hP0 : P ≠ ⊥ := hPp.ne_zero
    haveI hPi : P.IsPrime := isPrime_of_prime hPp
    have hle : span {((ℓ : ℤ) : 𝓞 K)} ≤ P := le_of_dvd (dvd_of_mem_normalizedFactors hP)
    haveI : P.LiesOver (span {(ℓ : ℤ)}) := by
      constructor
      have hmax : (span {(ℓ : ℤ)}).IsMaximal :=
        PrincipalIdealRing.isMaximal_of_irreducible
          (Int.prime_iff_natAbs_prime.mpr (by simpa using hℓ.out)).irreducible
      refine hmax.eq_of_le (IsPrime.ne_top inferInstance) ?_
      rw [← map_le_iff_le_comap, hmap]; exact hle
    have h1 := IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd ℓ K P hm
    rw [IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count (by rw [hmap]; exact hne)
      hPi hP0, hmap] at h1
    omega
  · rw [Multiset.count_eq_zero_of_notMem hP]; omega

/-- **Reducedness.** ℓ ∤ m, ℓ ∣ x² in 𝓞 ℚ(ζ_m) ⇒ ℓ ∣ x. -/
theorem reduced {ℓ : ℕ} [Fact ℓ.Prime] (hm : ¬ ℓ ∣ m) {x : 𝓞 K}
    (h : ((ℓ : ℤ) : 𝓞 K) ∣ x ^ 2) : ((ℓ : ℤ) : 𝓞 K) ∣ x := by
  have hs := span_squarefree (K := K) hm
  rw [← mem_span_singleton, ← dvd_span_singleton] at h ⊢
  rw [← span_singleton_pow] at h
  exact (hs.dvd_pow_iff_dvd two_ne_zero).mp h

/-- ℓ is not a unit of 𝓞 K (any number field). -/
theorem not_unit {ℓ : ℕ} (hℓ : ℓ.Prime) : ¬ IsUnit ((ℓ : ℤ) : 𝓞 K) := by
  intro h
  have hu := h.map (Algebra.norm ℤ (S := 𝓞 K))
  rw [show ((ℓ : ℤ) : 𝓞 K) = algebraMap ℤ (𝓞 K) (ℓ : ℤ) by simp, Algebra.norm_algebraMap] at hu
  have hd : Module.finrank ℤ (𝓞 K) ≠ 0 := by
    rw [RingOfIntegers.rank]; exact Module.finrank_pos.ne'
  rw [isUnit_pow_iff hd, Int.isUnit_iff] at hu
  rcases hu with hu | hu <;> have := hℓ.two_le <;> omega

/-- An integer prime to ℓ that ℓ divides in 𝓞 K: impossible. -/
theorem not_dvd_int {ℓ : ℕ} (hℓ : ℓ.Prime) {c : ℤ} (hc : ¬ (ℓ : ℤ) ∣ c)
    (h : ((ℓ : ℤ) : 𝓞 K) ∣ (c : 𝓞 K)) : False := by
  have hcop : IsCoprime (ℓ : ℤ) c :=
    (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hℓ).irreducible).mpr hc
  obtain ⟨u, v, huv⟩ := hcop
  apply not_unit (K := K) hℓ
  rw [isUnit_iff_dvd_one]
  have : ((u * ℓ + v * c : ℤ) : 𝓞 K) = 1 := by rw [huv]; simp
  rw [← this, Int.cast_add, Int.cast_mul, Int.cast_mul]
  exact dvd_add (dvd_mul_left _ _) (dvd_mul_of_dvd_right h _)

/-- `A` is an **ℓ-unit**: it divides an integer prime to ℓ. -/
def LUnit (ℓ : ℕ) {R : Type*} [CommRing R] (A : R) : Prop :=
  ∃ t : R, ∃ c : ℤ, ¬ (ℓ : ℤ) ∣ c ∧ A * t = c

theorem LUnit.mul {ℓ : ℕ} (hℓ : ℓ.Prime) {R : Type*} [CommRing R] {A B : R}
    (hA : LUnit ℓ A) (hB : LUnit ℓ B) : LUnit ℓ (A * B) := by
  obtain ⟨t, c, hc, h⟩ := hA
  obtain ⟨t', c', hc', h'⟩ := hB
  refine ⟨t * t', c * c', ?_, ?_⟩
  · exact fun hd => ((Nat.prime_iff_prime_int.mp hℓ).dvd_or_dvd hd).elim hc hc'
  · rw [Int.cast_mul, ← h, ← h']; ring

theorem LUnit.of_isUnit {ℓ : ℕ} (hℓ : ℓ.Prime) {R : Type*} [CommRing R] {A : R}
    (hA : IsUnit A) : LUnit ℓ A := by
  obtain ⟨u, rfl⟩ := hA
  refine ⟨(u⁻¹ : Rˣ), 1, ?_, by simp⟩
  exact fun hd => hℓ.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) hd)

theorem LUnit.int {ℓ : ℕ} {R : Type*} [CommRing R] {c : ℤ} (hc : ¬ (ℓ : ℤ) ∣ c) :
    LUnit ℓ (c : R) := ⟨1, c, hc, by simp⟩

/-- **Step 4 (integrality).** For an `m`-th root of unity `ω ≠ 1` in a domain, `1 − ω ∣ m`. -/
theorem one_sub_dvd {R : Type*} [CommRing R] [IsDomain R] {ω : R} {m : ℕ}
    (hω : ω ^ m = 1) (h1 : ω ≠ 1) : (1 - ω) ∣ (m : R) := by
  have hs : ∑ i ∈ Finset.range m, ω ^ i = 0 := by
    have := geom_sum_mul ω m
    rw [hω, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr h1)
  have : (m : R) = ∑ i ∈ Finset.range m, (1 - ω ^ i) := by
    rw [Finset.sum_sub_distrib, hs]; simp
  rw [this]
  exact Finset.dvd_sum fun i _ => by simpa using one_sub_dvd_one_sub_pow ω i

/-- Hence `1 − ω` is an ℓ-unit for every prime ℓ ∤ m. -/
theorem LUnit.one_sub {ℓ : ℕ} {R : Type*} [CommRing R] [IsDomain R] {ω : R} {m : ℕ}
    (hω : ω ^ m = 1) (h1 : ω ≠ 1) (hm : ¬ ℓ ∣ m) : LUnit ℓ (1 - ω) := by
  obtain ⟨t, ht⟩ := one_sub_dvd hω h1
  exact ⟨t, m, by exact_mod_cast hm, by rw [← ht]; simp⟩

/-- ℓ ∣ Y·B with B an ℓ-unit ⇒ ℓ ∣ Y. -/
theorem dvd_of_dvd_mul_lunit {ℓ : ℕ} (hℓ : ℓ.Prime) {R : Type*} [CommRing R] {Y B : R}
    (hB : LUnit ℓ B) (h : ((ℓ : ℤ) : R) ∣ Y * B) : ((ℓ : ℤ) : R) ∣ Y := by
  obtain ⟨t, c, hc, hBt⟩ := hB
  obtain ⟨u, v, huv⟩ :=
    (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hℓ).irreducible).mpr hc
  have hY : Y = ((u : ℤ) : R) * ((ℓ : ℤ) : R) * Y + ((v : ℤ) : R) * (Y * B * t) := by
    rw [mul_assoc Y B t, hBt]
    have : ((u * ℓ + v * c : ℤ) : R) = 1 := by rw [huv]; simp
    rw [Int.cast_add, Int.cast_mul, Int.cast_mul] at this
    linear_combination (-Y) * this
  rw [hY]
  exact dvd_add (dvd_mul_of_dvd_left (dvd_mul_left _ _) _)
    (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left h _) _)

/-- **Step 6 (parity), exponent form.** ℓ^a·A = Y²·B, A and B ℓ-units ⇒ a even. -/
theorem even_exp {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (hm : ¬ ℓ ∣ m) :
    ∀ a : ℕ, ∀ A Y B : 𝓞 K, LUnit ℓ A → LUnit ℓ B →
      ((ℓ : ℤ) : 𝓞 K) ^ a * A = Y ^ 2 * B → Even a := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro A Y B hA hB h
  rcases Nat.lt_or_ge a 1 with ha | ha
  · interval_cases a; exact ⟨0, rfl⟩
  have hl0 : ((ℓ : ℤ) : 𝓞 K) ≠ 0 := by exact_mod_cast hℓ.out.ne_zero
  have hdY : ((ℓ : ℤ) : 𝓞 K) ∣ Y := by
    apply reduced (K := K) hm
    apply dvd_of_dvd_mul_lunit hℓ.out hB
    rw [← h]; exact dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) _
  obtain ⟨Y', rfl⟩ := hdY
  rcases Nat.lt_or_ge a 2 with ha2 | ha2
  · -- a = 1: A = ℓ·Y'²·B, so ℓ divides the integer attached to A
    obtain rfl : a = 1 := by omega
    have hA' : A = ((ℓ : ℤ) : 𝓞 K) * (Y' ^ 2 * B) := by
      apply mul_left_cancel₀ hl0
      rw [← pow_one ((ℓ : ℤ) : 𝓞 K), h]; ring
    obtain ⟨t, c, hc, hAt⟩ := hA
    refine (not_dvd_int (K := K) hℓ.out hc ?_).elim
    rw [← hAt, hA']
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  · obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
    have h' : ((ℓ : ℤ) : 𝓞 K) ^ b * A = Y' ^ 2 * B := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hl0)
      linear_combination h
    have := ih b (by omega) A Y' B hA hB h'
    exact this.add even_two

/-- **Lemma V, algebraic core.**  In `𝓞 ℚ(ζ_m)`, if `N·A = Y²·B` with `A, B` ℓ-units and
`ℓ ∤ m` prime, then `v_ℓ(N)` is even. -/
theorem even_padicValNat {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (hm : ¬ ℓ ∣ m) {N : ℕ} (hN : N ≠ 0)
    {A Y B : 𝓞 K} (hA : LUnit ℓ A) (hB : LUnit ℓ B)
    (h : ((N : ℤ) : 𝓞 K) * A = Y ^ 2 * B) : Even (padicValNat ℓ N) := by
  set a := padicValNat ℓ N
  obtain ⟨M, hM⟩ : ℓ ^ a ∣ N := pow_padicValNat_dvd
  have hMl : ¬ ℓ ∣ M := by
    intro hd
    have : ℓ ^ (a + 1) ∣ N := by rw [hM, pow_succ]; exact mul_dvd_mul_left _ hd
    exact pow_succ_padicValNat_not_dvd hN this
  apply even_exp (K := K) hm a (((M : ℤ) : 𝓞 K) * A) Y B
    ((LUnit.int (by exact_mod_cast hMl)).mul hℓ.out hA) hB
  rw [← h, hM]; push_cast; ring

/-! ### Witnesses (non-vacuity) -/

section Witness

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
instance : NeZero ((4 : ℕ) : ℚ) := ⟨by norm_num⟩
instance cyc4 : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
  CyclotomicField.isCyclotomicExtension 4 ℚ

/-- All hypotheses of `even_padicValNat` are satisfiable: ℚ(ζ₄), ℓ = 3 ∤ 4, N = 9, A = B = 1,
Y = 3 (a genuine instance with v₃(N) = 2). -/
example : Even (padicValNat 3 9) :=
  even_padicValNat (K := CyclotomicField 4 ℚ) (m := 4) (ℓ := 3) (by norm_num) (by norm_num)
    (A := 1) (B := 1) (Y := 3) (LUnit.of_isUnit (by norm_num) isUnit_one)
    (LUnit.of_isUnit (by norm_num) isUnit_one) (by push_cast; ring)

/-- The core has teeth: 3 is not `Y²·(ℓ-unit)/(ℓ-unit)` in 𝓞 ℚ(ζ₄); e.g. 3 ≠ Y². -/
theorem three_ne_sq (Y : 𝓞 (CyclotomicField 4 ℚ)) : ((3 : ℕ) : ℤ) * (1 : 𝓞 (CyclotomicField 4 ℚ)) ≠
    Y ^ 2 * 1 := by
  intro h
  have := even_padicValNat (K := CyclotomicField 4 ℚ) (m := 4) (ℓ := 3) (N := 3) (by norm_num)
    (by norm_num) (LUnit.of_isUnit (by norm_num) isUnit_one)
    (LUnit.of_isUnit (by norm_num) isUnit_one) (by exact_mod_cast h)
  rw [padicValNat_self] at this
  exact (Nat.not_even_one) this

/-- `one_sub_dvd` fires on a genuine root of unity: `1 − i ∣ 4` in ℂ. -/
example : (1 - Complex.I) ∣ ((4 : ℕ) : ℂ) :=
  one_sub_dvd (by rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul]; simp) (by
    intro h; have := congrArg Complex.im h; simp at this)

end Witness

end Erdos634.Geometry.CaseA.LemmaV

#print axioms Erdos634.Geometry.CaseA.LemmaV.even_padicValNat
#print axioms Erdos634.Geometry.CaseA.LemmaV.three_ne_sq
#print axioms Erdos634.Geometry.CaseA.LemmaV.LUnit.one_sub
