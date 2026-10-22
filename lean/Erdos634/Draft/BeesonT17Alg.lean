import Mathlib

/-!
# Beeson (arXiv 1206.2229v4) Lemma 49 and the algorithm of Theorem 17 (second tiling equation), pure arithmetic

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Lemma 49, Thm 17), Laczkovich (DCG 48 (2012)), Beeson-Zhang.
Formalization debt, not progress on the /goal outcomes.  No tiling hypothesis and no H1 are used: this is the arithmetic half
(the geometric half is `second_tiling_eq` in `BeesonT17Eq`).

Second tiling equation: `N (1-s)^2 (2+s)^2 = M^2 (2-s^2)(3-s^2)`.
* `lemma49`: for `0 < s < 1`, `(1-s)^2 (2+s)^2 < (2-s^2)(3-s^2)`; hence a solution with `N > 0` has `M^2 < N`.
* `thm17_den_dvd`, `thm17_num_dvd`: for a rational root `s = e/f` in lowest terms, `f | N - M^2` and `e | 4N - 6M^2`.
* `thm17Sol N`: a finite, computable set of triples `(M, e, f)` (the printed algorithm); `thm17_alg_sound`, `thm17_alg_complete`:
  it contains exactly the solutions `(M, s = e/f)` with `M > 0`, `0 < s < 1`.
-/

namespace Erdos634.BeesonColoring

theorem lemma49 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s : K} (h0 : 0 < s) (h1 : s < 1) :
    (1 - s) ^ 2 * (2 + s) ^ 2 < (2 - s ^ 2) * (3 - s ^ 2) := by
  nlinarith [mul_pos h0 h0, mul_pos (mul_pos h0 h0) h0, mul_pos h0 (sub_pos.2 h1), sq_nonneg s,
    mul_pos (sub_pos.2 h1) (add_pos one_pos h0), mul_pos (mul_pos h0 (sub_pos.2 h1)) (add_pos one_pos h0)]

theorem lemma49_M_lt {s N M : ℚ} (hN : 0 < N) (h0 : 0 < s) (h1 : s < 1) (hM : 0 < M)
    (h : N * ((1 - s) ^ 2 * (2 + s) ^ 2) = M ^ 2 * ((2 - s ^ 2) * (3 - s ^ 2))) : M ^ 2 < N := by
  have hl := lemma49 h0 h1
  have hp : 0 < (1 - s) ^ 2 * (2 + s) ^ 2 := by
    have : 0 < 1 - s := by linarith
    positivity
  by_contra hh
  push_neg at hh
  nlinarith [mul_le_mul_of_nonneg_right hh hp.le, mul_lt_mul_of_pos_left hl (pow_pos hM 2)]

/-- clearing denominators: `s = e/f` -/
theorem poly_clear {N M e f : ℤ} (hf : f ≠ 0)
    (h : (N : ℚ) * ((1 - (e : ℚ) / f) ^ 2 * (2 + (e : ℚ) / f) ^ 2)
        = (M : ℚ) ^ 2 * ((2 - ((e : ℚ) / f) ^ 2) * (3 - ((e : ℚ) / f) ^ 2))) :
    (N - M ^ 2) * e ^ 4 + 2 * N * e ^ 3 * f + (5 * M ^ 2 - 3 * N) * e ^ 2 * f ^ 2 - 4 * N * e * f ^ 3
      + (4 * N - 6 * M ^ 2) * f ^ 4 = 0 := by
  have hf' : (f : ℚ) ≠ 0 := by exact_mod_cast hf
  have : ((N - M ^ 2) * e ^ 4 + 2 * N * e ^ 3 * f + (5 * M ^ 2 - 3 * N) * e ^ 2 * f ^ 2 - 4 * N * e * f ^ 3
      + (4 * N - 6 * M ^ 2) * f ^ 4 : ℤ) = (0 : ℚ) := by
    push_cast
    field_simp at h
    linear_combination h
  exact_mod_cast this

theorem thm17_den_dvd {N M : ℤ} {q : ℚ}
    (h : (N : ℚ) * ((1 - q) ^ 2 * (2 + q) ^ 2) = (M : ℚ) ^ 2 * ((2 - q ^ 2) * (3 - q ^ 2))) :
    (q.den : ℤ) ∣ N - M ^ 2 := by
  have hq : q = (q.num : ℚ) / (q.den : ℤ) := by simp [Rat.num_div_den]
  have hf : (q.den : ℤ) ≠ 0 := by exact_mod_cast q.den_nz
  rw [hq] at h
  have P := poly_clear hf h
  have cop : IsCoprime (q.den : ℤ) (q.num ^ 4) := by
    apply IsCoprime.pow_right
    have := q.reduced
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd_comm] using this
  have hd : (q.den : ℤ) ∣ (N - M ^ 2) * q.num ^ 4 := by
    have : (N - M ^ 2) * q.num ^ 4 = -(2 * N * q.num ^ 3 * q.den + (5 * M ^ 2 - 3 * N) * q.num ^ 2 * q.den ^ 2
        - 4 * N * q.num * q.den ^ 3 + (4 * N - 6 * M ^ 2) * q.den ^ 4) := by linarith
    rw [this]
    refine Dvd.dvd.neg_right ?_
    refine ⟨2 * N * q.num ^ 3 + (5 * M ^ 2 - 3 * N) * q.num ^ 2 * q.den - 4 * N * q.num * q.den ^ 2
      + (4 * N - 6 * M ^ 2) * q.den ^ 3, by ring⟩
  exact cop.dvd_of_dvd_mul_right hd

theorem thm17_num_dvd {N M : ℤ} {q : ℚ}
    (h : (N : ℚ) * ((1 - q) ^ 2 * (2 + q) ^ 2) = (M : ℚ) ^ 2 * ((2 - q ^ 2) * (3 - q ^ 2))) :
    q.num ∣ 4 * N - 6 * M ^ 2 := by
  have hq : q = (q.num : ℚ) / (q.den : ℤ) := by simp [Rat.num_div_den]
  have hf : (q.den : ℤ) ≠ 0 := by exact_mod_cast q.den_nz
  rw [hq] at h
  have P := poly_clear hf h
  have cop : IsCoprime q.num ((q.den : ℤ) ^ 4) := by
    apply IsCoprime.pow_right
    have := q.reduced
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa using this
  have hd : q.num ∣ (4 * N - 6 * M ^ 2) * (q.den : ℤ) ^ 4 := by
    have : (4 * N - 6 * M ^ 2) * (q.den : ℤ) ^ 4 = -((N - M ^ 2) * q.num ^ 4 + 2 * N * q.num ^ 3 * q.den
        + (5 * M ^ 2 - 3 * N) * q.num ^ 2 * q.den ^ 2 - 4 * N * q.num * q.den ^ 3) := by linarith
    rw [this]
    refine Dvd.dvd.neg_right ?_
    refine ⟨(N - M ^ 2) * q.num ^ 3 + 2 * N * q.num ^ 2 * q.den + (5 * M ^ 2 - 3 * N) * q.num * q.den ^ 2
      - 4 * N * q.den ^ 3, by ring⟩
  exact cop.dvd_of_dvd_mul_right hd

/-- the printed algorithm: finitely many `M` (`M^2 < N`), `f | N - M^2`, `0 < e < f`, each candidate tested exactly. -/
def thm17Sol (N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range N) ×ˢ (Finset.range N) ×ˢ (Finset.range N)).filter fun t =>
    0 < t.1 ∧ t.1 ^ 2 < N ∧ t.2.2 ∣ N - t.1 ^ 2 ∧ 0 < t.2.1 ∧ t.2.1 < t.2.2 ∧ Nat.Coprime t.2.1 t.2.2 ∧
    (N : ℚ) * ((1 - (t.2.1 : ℚ) / t.2.2) ^ 2 * (2 + (t.2.1 : ℚ) / t.2.2) ^ 2)
      = (t.1 : ℚ) ^ 2 * ((2 - ((t.2.1 : ℚ) / t.2.2) ^ 2) * (3 - ((t.2.1 : ℚ) / t.2.2) ^ 2))

theorem thm17_alg_sound {N M e f : ℕ} (h : (M, e, f) ∈ thm17Sol N) :
    0 < M ∧ 0 < (e : ℚ) / f ∧ (e : ℚ) / f < 1 ∧
      (N : ℚ) * ((1 - (e : ℚ) / f) ^ 2 * (2 + (e : ℚ) / f) ^ 2)
        = (M : ℚ) ^ 2 * ((2 - ((e : ℚ) / f) ^ 2) * (3 - ((e : ℚ) / f) ^ 2)) := by
  simp only [thm17Sol, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h
  obtain ⟨-, hM, -, -, he0, hef, -, heq⟩ := h
  have hf : (0 : ℚ) < f := by exact_mod_cast (he0.trans hef)
  refine ⟨hM, div_pos (by exact_mod_cast he0) hf, (div_lt_one hf).2 (by exact_mod_cast hef), heq⟩

theorem thm17_alg_complete {N M : ℕ} {q : ℚ} (hM : 0 < M) (h0 : 0 < q) (h1 : q < 1) (hN : 0 < N)
    (h : (N : ℚ) * ((1 - q) ^ 2 * (2 + q) ^ 2) = (M : ℚ) ^ 2 * ((2 - q ^ 2) * (3 - q ^ 2))) :
    (M, q.num.toNat, q.den) ∈ thm17Sol N := by
  have hlt : (M : ℚ) ^ 2 < N :=
    lemma49_M_lt (by exact_mod_cast hN) h0 h1 (by exact_mod_cast hM) h
  have hlt' : M ^ 2 < N := by exact_mod_cast hlt
  have hnum : 0 < q.num := Rat.num_pos.2 h0
  have hnum' : (q.num.toNat : ℤ) = q.num := Int.toNat_of_nonneg hnum.le
  have hlt1 : q.num < q.den := by
    have h2 : (q.num : ℚ) / (q.den : ℚ) < 1 := by rw [Rat.num_div_den]; exact h1
    have h3 := (div_lt_one (by exact_mod_cast q.den_pos : (0 : ℚ) < q.den)).1 h2
    exact_mod_cast h3
  have hd := thm17_den_dvd (N := (N : ℤ)) (M := (M : ℤ)) (by exact_mod_cast h)
  have hd' : q.den ∣ N - M ^ 2 := by
    have : ((q.den : ℕ) : ℤ) ∣ ((N - M ^ 2 : ℕ) : ℤ) := by
      rw [Nat.cast_sub hlt'.le]; push_cast; exact hd
    exact_mod_cast this
  have hq : q = (q.num.toNat : ℚ) / (q.den : ℚ) := by
    have : ((q.num.toNat : ℕ) : ℚ) = (q.num : ℚ) := by exact_mod_cast hnum'
    rw [this]; simp [Rat.num_div_den]
  have hcop : Nat.Coprime q.num.toNat q.den := by
    have := q.reduced
    have e : q.num.toNat = q.num.natAbs := by omega
    rw [e]; exact this
  have hdpos : 0 < q.den := q.den_pos
  simp only [thm17Sol, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  have hnum2 : 0 < q.num.toNat := by omega
  have hnum3 : q.num.toNat < q.den := by omega
  have hNM : 0 < N - M ^ 2 := by omega
  have hden_le : q.den ≤ N - M ^ 2 := Nat.le_of_dvd hNM hd'
  have hMle : M ≤ M ^ 2 := by nlinarith
  refine ⟨⟨by omega, by omega, by omega⟩, hM, hlt', hd', hnum2, hnum3, hcop, ?_⟩
  rw [← hq]; exact h

end Erdos634.BeesonColoring

#print axioms Erdos634.BeesonColoring.lemma49
#print axioms Erdos634.BeesonColoring.thm17_den_dvd
#print axioms Erdos634.BeesonColoring.thm17_num_dvd
#print axioms Erdos634.BeesonColoring.thm17_alg_complete
