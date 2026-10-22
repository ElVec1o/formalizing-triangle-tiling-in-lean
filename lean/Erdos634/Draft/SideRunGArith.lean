/-
Draft/SideRunGArith.lean -- written 14 October 2026.  UNAUDITED.  In `AllThreshold`.

Paper: Theorem `thm:siderunall`, Corollaries `cor:ebelow` and `cor:thickw`: the ARITHMETIC of the proofs, for every coprime
`1 ≤ e < f`, with the tile `(a, b, c) = (e f, f^2 - e^2, f^2)`.  Pure arithmetic, no geometry.  A representation of `n` is a
triple `(x, y, z)` of natural numbers with `x a + y b + z c = n`; the hypotheses are stated over `ℕ` (natural subtraction is
exact because `e < f`).

(R0)   `r0_residues`, `r0_inv`, `r0`, `r0_inv_form`: `a ≡ c ≡ 0` and `b ≡ -e^2 (mod f)`; `e` is invertible mod `f`; and the
       consequence `y ≡ -n e^{-2} (mod f)` for every representation of `n`.
(A1)   `A1`: `j b`, `1 ≤ j ≤ f - 1`, is represented only as `b^j`.
(A5)   `A5`: a representation of `j c`, `1 ≤ j ≤ f - 1`, contains no `b`.  The proof is the paper's (divide by `f`, `e (x - m e) =
       f (j - m f - z)`, `f ∣ w`, `e t = m f + z - j`, `t ≤ m - 1`); the argument of the `e = 1` file (`y b ≤ j c < f b`) is not used,
       it fails for `(2, 3)` (`f b = 15 < 2 c = 18`).
(Aa)   `Aa`: `j a`, `1 ≤ j ≤ f - 1`, is represented only as `a^j`.
(C-QB) `C_QB`: a representation of `M e (2 f^2 - e^2)` has `y ≡ M e (mod f)`; if `M e < f`, also `M e ≤ y` and `z ≤ M e`.
(C-base) `C_base`: the same for `M e (3 f^2 - e^2)`, with `z ≤ 2 M e`.
(C-AQ) `C_AQ`: a representation of `M f b` has `f ∣ y`; if `M (f - e) ≤ e`, then `z ≤ M (f - e)`.

The count with no edge `b` used in `C_AQ` is `WStripArith.count_no_b_int`.  No sorry, no native_decide.  `#print axioms` at the foot.
Examples at `(e, f) = (2, 3)` and `(2, 5)` at the end: every hypothesis is satisfied by an explicit representation, and the
bounds `j ≤ f - 1`, `M (f - e) ≤ e` are shown necessary by explicit representations just outside them.
-/
import Erdos634.Draft.WStripArith

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.SideRunGArith
open Erdos634.Draft.WStripArith

/-! ## Helpers -/

/-- `2 f^2 - e^2` as a natural number with its integer value (`e < f`) -/
theorem exists_b2 {e f : ℕ} (hef : e < f) :
    ∃ b : ℕ, 2 * f ^ 2 - e ^ 2 = b ∧ (b : ℤ) = 2 * (f : ℤ) ^ 2 - (e : ℤ) ^ 2 := by
  have h : e ^ 2 ≤ 2 * f ^ 2 := by
    have := Nat.pow_le_pow_left hef.le 2
    omega
  refine ⟨2 * f ^ 2 - e ^ 2, rfl, ?_⟩
  rw [Nat.cast_sub h]
  push_cast
  try ring

/-- `3 f^2 - e^2` as a natural number with its integer value (`e < f`) -/
theorem exists_b3 {e f : ℕ} (hef : e < f) :
    ∃ b : ℕ, 3 * f ^ 2 - e ^ 2 = b ∧ (b : ℤ) = 3 * (f : ℤ) ^ 2 - (e : ℤ) ^ 2 := by
  have h : e ^ 2 ≤ 3 * f ^ 2 := by
    have := Nat.pow_le_pow_left hef.le 2
    omega
  refine ⟨3 * f ^ 2 - e ^ 2, rfl, ?_⟩
  rw [Nat.cast_sub h]
  push_cast
  try ring

/-- `b = f^2 - e^2 > 0` -/
theorem sq_sub_pos {e f : ℕ} (he : 1 ≤ e) (hef : e < f) : (0 : ℤ) < (f : ℤ) ^ 2 - (e : ℤ) ^ 2 := by
  have h : (0 : ℤ) < ((f : ℤ) - e) * ((f : ℤ) + e) := mul_pos (by omega) (by omega)
  nlinarith

/-- `y = f m` with `y ≥ 0` and `f > 0` gives `m ≥ 0` -/
theorem nonneg_of_eq_mul {f m y : ℤ} (hf : 0 < f) (hy : 0 ≤ y) (hm : y = f * m) : 0 ≤ m := by
  by_contra hc
  push_neg at hc
  have := mul_neg_of_pos_of_neg hf hc
  linarith

/-! ## (R0) -/

/-- **(R0)** `a ≡ c ≡ 0` and `b ≡ -e^2 (mod f)`: `f ∣ a`, `f ∣ c`, `f ∣ b + e^2`. -/
theorem r0_residues (e f : ℕ) (hef : e < f) :
    f ∣ e * f ∧ f ∣ f ^ 2 ∧ f ∣ (f ^ 2 - e ^ 2) + e ^ 2 := by
  refine ⟨dvd_mul_left f e, dvd_pow_self f (by norm_num), ?_⟩
  rw [Nat.sub_add_cancel (Nat.pow_le_pow_left hef.le 2)]
  exact dvd_pow_self f (by norm_num)

/-- **(R0)** `e` is invertible modulo `f` -/
theorem r0_inv (e f : ℕ) (hef : e < f) (he : 1 ≤ e) (hco : Nat.Coprime e f) :
    ∃ e' : ℕ, e * e' % f = 1 := by
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hco (by omega : 1 < f)
  exact ⟨m, hm⟩

/-- **(R0)**, congruence form: for a representation of `n`, `f ∣ y e^2 + n` -/
theorem r0 {e f x y z n : ℕ} (hef : e < f)
    (h : x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = n) :
    (f : ℤ) ∣ (y : ℤ) * (e : ℤ) ^ 2 + n := by
  obtain ⟨b, hbN, hbZ⟩ := exists_b hef
  rw [hbN] at h
  have hZ : (x : ℤ) * (e * f) + y * (b : ℤ) + z * (f : ℤ) ^ 2 = n := by exact_mod_cast h
  rw [hbZ] at hZ
  exact ⟨(x : ℤ) * e + y * f + z * f, by linear_combination (-1 : ℤ) * hZ⟩

/-- **(R0)**, inverse form: `y ≡ -n e^{-2} (mod f)`, i.e. `f ∣ y + n e'^2` where `e e' ≡ 1 (mod f)` -/
theorem r0_inv_form {e f : ℕ} (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) :
    ∃ e' : ℕ, e * e' % f = 1 ∧ ∀ x y z n : ℕ,
      x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = n → (f : ℤ) ∣ (y : ℤ) + (n : ℤ) * (e' : ℤ) ^ 2 := by
  obtain ⟨e', he'⟩ := r0_inv e f hef he hco
  refine ⟨e', he', fun x y z n h => ?_⟩
  obtain ⟨m, hm⟩ := r0 hef h
  have hmod : e * e' ≡ 1 [MOD f] := by
    have h1 : 1 % f = 1 := Nat.mod_eq_of_lt (by omega)
    show e * e' % f = 1 % f
    rw [h1]
    exact he'
  obtain ⟨k, hk⟩ := Nat.modEq_iff_dvd.mp hmod
  push_cast at hk
  exact ⟨(e' : ℤ) ^ 2 * m + y * k * (e * e' + 1),
    by linear_combination (e' : ℤ) ^ 2 * hm + ((y : ℤ) * (e * e' + 1)) * hk⟩

/-! ## (A1) -/

/-- **(A1)** For `1 ≤ j ≤ f - 1`: `x a + y b + z c = j b` implies `x = 0`, `y = j`, `z = 0`. -/
theorem A1 {e f j x y z : ℕ} (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    (hj1 : 1 ≤ j) (hj : j ≤ f - 1)
    (h : x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = j * (f ^ 2 - e ^ 2)) :
    x = 0 ∧ y = j ∧ z = 0 := by
  obtain ⟨b, hbN, hbZ⟩ := exists_b hef
  rw [hbN] at h
  have hZ : (x : ℤ) * (e * f) + y * (b : ℤ) + z * (f : ℤ) ^ 2 = j * (b : ℤ) := by exact_mod_cast h
  rw [hbZ] at hZ
  have hF : (0 : ℤ) < f := by omega
  have he0 : (0 : ℤ) < e := by omega
  have hb0 := sq_sub_pos he hef
  have hx0 : (0 : ℤ) ≤ (x : ℤ) * (e * f) := by positivity
  have hz0 : (0 : ℤ) ≤ (z : ℤ) * (f : ℤ) ^ 2 := by positivity
  have hjf : (j : ℤ) ≤ f - 1 := by omega
  have hyj : (y : ℤ) ≤ j := by
    have h1 : (y : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) ≤ j * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) := by linarith
    exact le_of_mul_le_mul_right h1 hb0
  have hd : (f : ℤ) ∣ (e : ℤ) ^ 2 * ((y : ℤ) - j) :=
    ⟨((y : ℤ) - j) * f + x * e + z * f, by linear_combination (-1 : ℤ) * hZ⟩
  have hd2 : (f : ℤ) ∣ (y : ℤ) - j := dvd_of_coprime_mul_sq hco hd
  have hy0 : (0 : ℤ) ≤ y := by positivity
  have hyj0 : (y : ℤ) - j = 0 := dvd_eq_zero_of_lt hF hd2 (by linarith) (by linarith)
  have hyjeq : (y : ℤ) = j := by linarith
  have hrest : (x : ℤ) * (e * f) + z * (f : ℤ) ^ 2 = 0 := by
    rw [hyjeq] at hZ
    linarith
  have hx1 : (x : ℤ) * (e * f) = 0 := by linarith
  have hz1 : (z : ℤ) * (f : ℤ) ^ 2 = 0 := by linarith
  have hef0 : ((e : ℤ) * f) ≠ 0 := (mul_pos he0 hF).ne'
  have hf20 : ((f : ℤ) ^ 2) ≠ 0 := (pow_pos hF 2).ne'
  have hx2 : (x : ℤ) = 0 := (mul_eq_zero.mp hx1).resolve_right hef0
  have hz2 : (z : ℤ) = 0 := (mul_eq_zero.mp hz1).resolve_right hf20
  exact ⟨by exact_mod_cast hx2, by exact_mod_cast hyjeq, by exact_mod_cast hz2⟩

/-! ## (A5) -/

/-- **(A5)** For `1 ≤ j ≤ f - 1`: `x a + y b + z c = j c` implies `y = 0`.  (The paper's argument: `y = m f`, `m ≥ 1` gives
`e (m e - x) = f (m f + z - j)`, hence `m e - x = t f`, `e t = m f + z - j`, `t ≤ m - 1`, and `e t ≤ f (m - 1) < e t`.) -/
theorem A5 {e f j x y z : ℕ} (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    (hj1 : 1 ≤ j) (hj : j ≤ f - 1)
    (h : x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = j * f ^ 2) : y = 0 := by
  obtain ⟨b, hbN, hbZ⟩ := exists_b hef
  rw [hbN] at h
  have hZ : (x : ℤ) * (e * f) + y * (b : ℤ) + z * (f : ℤ) ^ 2 = j * (f : ℤ) ^ 2 := by exact_mod_cast h
  rw [hbZ] at hZ
  have hF : (0 : ℤ) < f := by omega
  have he0 : (0 : ℤ) < e := by omega
  have hef' : (e : ℤ) < f := by omega
  have hx0 : (0 : ℤ) ≤ x := by positivity
  have hy0 : (0 : ℤ) ≤ y := by positivity
  have hz0 : (0 : ℤ) ≤ z := by positivity
  have hjf : (j : ℤ) ≤ f - 1 := by omega
  have hd : (f : ℤ) ∣ (e : ℤ) ^ 2 * (y : ℤ) :=
    ⟨(y : ℤ) * f - j * f + x * e + z * f, by linear_combination (-1 : ℤ) * hZ⟩
  obtain ⟨m, hm⟩ := dvd_of_coprime_mul_sq hco hd
  have hm0 : 0 ≤ m := nonneg_of_eq_mul hF hy0 hm
  by_contra hy
  have hyne : (y : ℤ) ≠ 0 := by exact_mod_cast hy
  have hm1 : 1 ≤ m := by
    rcases (show m = 0 ∨ 1 ≤ m by omega) with h0 | h1
    · exfalso
      apply hyne
      rw [hm, h0, mul_zero]
    · exact h1
  have h2 : (f : ℤ) * ((x : ℤ) * e + m * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + z * f) = (f : ℤ) * (j * f) := by
    linear_combination hZ - ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) * hm
  have h3 : (x : ℤ) * e + m * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + z * f = j * f :=
    mul_left_cancel₀ hF.ne' h2
  have h4 : (e : ℤ) * (m * (e : ℤ) - x) = f * (m * f + z - j) := by
    linear_combination (-1 : ℤ) * h3
  have hmf : (1 : ℤ) * f ≤ m * f := mul_le_mul_of_nonneg_right hm1 hF.le
  have hpos : (0 : ℤ) < m * f + z - j := by linarith
  have hW : 0 < m * (e : ℤ) - x := by
    by_contra hc
    push_neg at hc
    have a1 := mul_nonneg he0.le (show (0 : ℤ) ≤ -(m * (e : ℤ) - x) by linarith)
    have a2 := mul_pos hF hpos
    linarith
  obtain ⟨t, ht⟩ : (f : ℤ) ∣ m * (e : ℤ) - x := by
    apply dvd_of_coprime_mul hco
    exact ⟨m * f + z - j, h4⟩
  have ht1 : 0 < t := by
    by_contra hc
    push_neg at hc
    have a1 := mul_nonneg hF.le (show (0 : ℤ) ≤ -t by linarith)
    linarith
  have h5 : (e : ℤ) * t = m * f + z - j := by
    apply mul_left_cancel₀ hF.ne'
    linear_combination h4 - (e : ℤ) * ht
  have h6 : t < m := by
    by_contra hc
    push_neg at hc
    have a1 := mul_le_mul_of_nonneg_left hc hF.le
    have a2 : m * (e : ℤ) < m * f := mul_lt_mul_of_pos_left hef' (by omega)
    linarith
  have h7 : t ≤ m - 1 := by omega
  have a3 : (e : ℤ) * t ≤ e * (m - 1) := mul_le_mul_of_nonneg_left h7 he0.le
  have a4 : (e : ℤ) * (m - 1) ≤ f * (m - 1) := mul_le_mul_of_nonneg_right hef'.le (by omega)
  linarith

/-! ## (Aa) -/

/-- **(Aa)** For `1 ≤ j ≤ f - 1`: `x a + y b + z c = j a` implies `x = j`, `y = 0`, `z = 0`. -/
theorem Aa {e f j x y z : ℕ} (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    (hj1 : 1 ≤ j) (hj : j ≤ f - 1)
    (h : x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = j * (e * f)) :
    x = j ∧ y = 0 ∧ z = 0 := by
  obtain ⟨b, hbN, hbZ⟩ := exists_b hef
  rw [hbN] at h
  have hZ : (x : ℤ) * (e * f) + y * (b : ℤ) + z * (f : ℤ) ^ 2 = j * (e * f) := by exact_mod_cast h
  rw [hbZ] at hZ
  have hF : (0 : ℤ) < f := by omega
  have he0 : (0 : ℤ) < e := by omega
  have hef' : (e : ℤ) < f := by omega
  have hx0 : (0 : ℤ) ≤ x := by positivity
  have hy0 : (0 : ℤ) ≤ y := by positivity
  have hz0 : (0 : ℤ) ≤ z := by positivity
  have hjf : (j : ℤ) ≤ f - 1 := by omega
  have hd : (f : ℤ) ∣ (e : ℤ) ^ 2 * (y : ℤ) :=
    ⟨(y : ℤ) * f - j * e + x * e + z * f, by linear_combination (-1 : ℤ) * hZ⟩
  obtain ⟨m, hm⟩ := dvd_of_coprime_mul_sq hco hd
  have hm0 : 0 ≤ m := nonneg_of_eq_mul hF hy0 hm
  have h2 : (f : ℤ) * ((x : ℤ) * e + m * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + z * f) = (f : ℤ) * (j * e) := by
    linear_combination hZ - ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) * hm
  have h3 : (x : ℤ) * e + m * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + z * f = j * e :=
    mul_left_cancel₀ hF.ne' h2
  have h4 : (e : ℤ) * ((j : ℤ) - x + m * e) = f * (m * f + z) := by
    linear_combination (-1 : ℤ) * h3
  obtain ⟨t, ht⟩ : (f : ℤ) ∣ (j : ℤ) - x + m * e := by
    apply dvd_of_coprime_mul hco
    exact ⟨m * f + z, h4⟩
  have h5 : (e : ℤ) * t = m * f + z := by
    apply mul_left_cancel₀ hF.ne'
    linear_combination h4 - (e : ℤ) * ht
  rcases (show m = 0 ∨ 1 ≤ m by omega) with h0 | h1
  · subst h0
    have ht_nn : 0 ≤ t := by
      by_contra hc
      push_neg at hc
      have a1 := mul_pos he0 (neg_pos.mpr hc)
      linarith
    have ht_lt : t < 1 := by
      by_contra hc
      push_neg at hc
      have a1 := mul_le_mul_of_nonneg_left hc hF.le
      linarith
    have ht0 : t = 0 := by omega
    rw [ht0] at ht h5
    have hxj : (x : ℤ) = j := by linarith
    have hy' : (y : ℤ) = 0 := by linarith
    have hz' : (z : ℤ) = 0 := by linarith
    exact ⟨by exact_mod_cast hxj, by exact_mod_cast hy', by exact_mod_cast hz'⟩
  · exfalso
    have a2 : m * (e : ℤ) < m * f := mul_lt_mul_of_pos_left hef' (by omega)
    have ht_gt : m < t := by
      by_contra hc
      push_neg at hc
      have a1 := mul_le_mul_of_nonneg_left hc he0.le
      linarith
    have a3 := mul_le_mul_of_nonneg_left (show m + 1 ≤ t by omega) hF.le
    linarith

/-! ## (C-QB), (C-base), (C-AQ) -/

/-- **(C-QB)** A representation of `M e (2 f^2 - e^2)` (the length of the side `QB` of `W_M(e, f)`) has `y ≡ M e (mod f)`;
if `M e < f`, then `M e ≤ y` and `z ≤ M e`. -/
theorem C_QB {e f M x y z : ℕ} (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    (h : x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = M * e * (2 * f ^ 2 - e ^ 2)) :
    y ≡ M * e [MOD f] ∧ (M * e < f → M * e ≤ y ∧ z ≤ M * e) := by
  obtain ⟨b, hbN, hbZ⟩ := exists_b hef
  obtain ⟨b2, hb2N, hb2Z⟩ := exists_b2 hef
  rw [hbN, hb2N] at h
  have hZ : (x : ℤ) * (e * f) + y * (b : ℤ) + z * (f : ℤ) ^ 2 = M * e * (b2 : ℤ) := by
    exact_mod_cast h
  rw [hbZ, hb2Z] at hZ
  have hF : (0 : ℤ) < f := by omega
  have hb0 := sq_sub_pos he hef
  have hy0 : (0 : ℤ) ≤ y := by positivity
  have hd : (f : ℤ) ∣ (e : ℤ) ^ 2 * ((M : ℤ) * e - y) :=
    ⟨-((y : ℤ) * f + x * e + z * f - 2 * M * e * f), by linear_combination hZ⟩
  have hd2 : (f : ℤ) ∣ (M : ℤ) * e - y := dvd_of_coprime_mul_sq hco hd
  have hmod : y ≡ M * e [MOD f] := by
    apply Nat.modEq_iff_dvd.mpr
    push_cast
    exact hd2
  refine ⟨hmod, fun hMe => ?_⟩
  have hMe' : (M : ℤ) * e < f := by exact_mod_cast hMe
  have hyM : (M : ℤ) * e ≤ y := by
    by_contra hc
    push_neg at hc
    have h0 : (M : ℤ) * e - y = 0 := dvd_eq_zero_of_lt hF hd2 (by linarith) (by linarith)
    linarith
  have a1 := mul_le_mul_of_nonneg_right hyM hb0.le
  have hxef : (0 : ℤ) ≤ (x : ℤ) * (e * f) := by positivity
  have hzM : (z : ℤ) * (f : ℤ) ^ 2 ≤ ((M : ℤ) * e) * (f : ℤ) ^ 2 := by nlinarith
  have hf2 : (0 : ℤ) < (f : ℤ) ^ 2 := pow_pos hF 2
  have hz := le_of_mul_le_mul_right hzM hf2
  exact ⟨by exact_mod_cast hyM, by exact_mod_cast hz⟩

/-- **(C-base)** A representation of `M e (3 f^2 - e^2)` (the base of `T_M(e, f)`) has `y ≡ M e (mod f)`; if `M e < f`, then
`M e ≤ y` and `z ≤ 2 M e`. -/
theorem C_base {e f M x y z : ℕ} (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    (h : x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = M * e * (3 * f ^ 2 - e ^ 2)) :
    y ≡ M * e [MOD f] ∧ (M * e < f → M * e ≤ y ∧ z ≤ 2 * (M * e)) := by
  obtain ⟨b, hbN, hbZ⟩ := exists_b hef
  obtain ⟨b3, hb3N, hb3Z⟩ := exists_b3 hef
  rw [hbN, hb3N] at h
  have hZ : (x : ℤ) * (e * f) + y * (b : ℤ) + z * (f : ℤ) ^ 2 = M * e * (b3 : ℤ) := by
    exact_mod_cast h
  rw [hbZ, hb3Z] at hZ
  have hF : (0 : ℤ) < f := by omega
  have hb0 := sq_sub_pos he hef
  have hy0 : (0 : ℤ) ≤ y := by positivity
  have hd : (f : ℤ) ∣ (e : ℤ) ^ 2 * ((M : ℤ) * e - y) :=
    ⟨-((y : ℤ) * f + x * e + z * f - 3 * M * e * f), by linear_combination hZ⟩
  have hd2 : (f : ℤ) ∣ (M : ℤ) * e - y := dvd_of_coprime_mul_sq hco hd
  have hmod : y ≡ M * e [MOD f] := by
    apply Nat.modEq_iff_dvd.mpr
    push_cast
    exact hd2
  refine ⟨hmod, fun hMe => ?_⟩
  have hMe' : (M : ℤ) * e < f := by exact_mod_cast hMe
  have hyM : (M : ℤ) * e ≤ y := by
    by_contra hc
    push_neg at hc
    have h0 : (M : ℤ) * e - y = 0 := dvd_eq_zero_of_lt hF hd2 (by linarith) (by linarith)
    linarith
  have a1 := mul_le_mul_of_nonneg_right hyM hb0.le
  have hxef : (0 : ℤ) ≤ (x : ℤ) * (e * f) := by positivity
  have hzM : (z : ℤ) * (f : ℤ) ^ 2 ≤ (2 * ((M : ℤ) * e)) * (f : ℤ) ^ 2 := by nlinarith
  have hf2 : (0 : ℤ) < (f : ℤ) ^ 2 := pow_pos hF 2
  have hz := le_of_mul_le_mul_right hzM hf2
  exact ⟨by exact_mod_cast hyM, by exact_mod_cast hz⟩

/-- **(C-AQ)** A representation of `M f b` (the length of the side `AQ` of `W_M(e, f)`) has `f ∣ y`; if `M (f - e) ≤ e`,
then `z ≤ M (f - e)`.  (Remove the `y / f` copies of `f b`; what is left is a representation of `M' f b` with no edge `b`,
`M' = M - y / f`, to which `count_no_b_int` applies.) -/
theorem C_AQ {e f M x y z : ℕ} (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    (h : x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = M * f * (f ^ 2 - e ^ 2)) :
    f ∣ y ∧ (M * (f - e) ≤ e → z ≤ M * (f - e)) := by
  obtain ⟨b, hbN, hbZ⟩ := exists_b hef
  rw [hbN] at h
  have hZ : (x : ℤ) * (e * f) + y * (b : ℤ) + z * (f : ℤ) ^ 2 = M * f * (b : ℤ) := by exact_mod_cast h
  rw [hbZ] at hZ
  have hF : (0 : ℤ) < f := by omega
  have hef' : (e : ℤ) < f := by omega
  have hy0 : (0 : ℤ) ≤ y := by positivity
  have hd : (f : ℤ) ∣ (e : ℤ) ^ 2 * (y : ℤ) :=
    ⟨(y : ℤ) * f - M * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + x * e + z * f, by
      linear_combination (-1 : ℤ) * hZ⟩
  have hdy : (f : ℤ) ∣ (y : ℤ) := dvd_of_coprime_mul_sq hco hd
  refine ⟨by exact_mod_cast hdy, fun hMe => ?_⟩
  obtain ⟨m, hm⟩ := hdy
  have hm0 : 0 ≤ m := nonneg_of_eq_mul hF hy0 hm
  have h2 : (f : ℤ) * ((x : ℤ) * e + z * f) = (f : ℤ) * (((M : ℤ) - m) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2)) := by
    linear_combination hZ - ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) * hm
  have h3 : (x : ℤ) * e + z * f = ((M : ℤ) - m) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) :=
    mul_left_cancel₀ hF.ne' h2
  have hcast : ((M * (f - e) : ℕ) : ℤ) = (M : ℤ) * ((f : ℤ) - e) := by
    rw [Nat.cast_mul, Nat.cast_sub hef.le]
  have hMe' : (M : ℤ) * ((f : ℤ) - e) ≤ e := by
    rw [← hcast]
    exact_mod_cast hMe
  have hmfe : (0 : ℤ) ≤ m * ((f : ℤ) - e) := mul_nonneg hm0 (by omega)
  have hN : ((M : ℤ) - m) * ((f : ℤ) - e) < f := by nlinarith
  obtain ⟨-, hz1⟩ := count_no_b_int (N := (M : ℤ) - m) (X := (x : ℤ)) (Z := (z : ℤ)) hef hco
    (by positivity) hN h3
  have hzle : (z : ℤ) ≤ M * ((f : ℤ) - e) := by nlinarith
  rw [← hcast] at hzle
  exact_mod_cast hzle

/-! ## Examples: every hypothesis is satisfied at `(e, f) = (2, 3)` and `(2, 5)`

`(2, 3)`: `(a, b, c) = (6, 5, 9)`.  `(2, 5)`: `(a, b, c) = (10, 21, 25)`. -/

example : (2 : ℕ) * 3 = 6 ∧ 3 ^ 2 - 2 ^ 2 = 5 ∧ 3 ^ 2 = 9 := by norm_num
example : (2 : ℕ) * 5 = 10 ∧ 5 ^ 2 - 2 ^ 2 = 21 ∧ 5 ^ 2 = 25 := by norm_num

-- (R0)
example : 3 ∣ 2 * 3 ∧ 3 ∣ 3 ^ 2 ∧ 3 ∣ (3 ^ 2 - 2 ^ 2) + 2 ^ 2 := r0_residues 2 3 (by norm_num)
example : 5 ∣ 2 * 5 ∧ 5 ∣ 5 ^ 2 ∧ 5 ∣ (5 ^ 2 - 2 ^ 2) + 2 ^ 2 := r0_residues 2 5 (by norm_num)
example : ∃ e' : ℕ, 2 * e' % 3 = 1 :=
  r0_inv 2 3 (by norm_num) (by norm_num) (by first | decide | norm_num)
example : ∃ e' : ℕ, 2 * e' % 5 = 1 :=
  r0_inv 2 5 (by norm_num) (by norm_num) (by first | decide | norm_num)
-- the representation (3, 2, 0) of 28 = 2 (2 * 9 - 4): 3 ∣ y e^2 + n = 8 + 28 = 36
example := r0 (e := 2) (f := 3) (x := 3) (y := 2) (z := 0) (n := 28) (by norm_num) (by norm_num)
-- the representation (5, 2, 0) of 92: 5 ∣ 8 + 92 = 100
example := r0 (e := 2) (f := 5) (x := 5) (y := 2) (z := 0) (n := 92) (by norm_num) (by norm_num)
example := r0_inv_form (e := 2) (f := 3) (by norm_num) (by norm_num) (by first | decide | norm_num)
example := r0_inv_form (e := 2) (f := 5) (by norm_num) (by norm_num) (by first | decide | norm_num)

-- (A1): `2 b = b^2` at (2, 3); `3 b = b^3` at (2, 5); control at j = f: `f b = (f - e) (a + c)`, here 15 = 6 + 9
example := A1 (e := 2) (f := 3) (j := 2) (x := 0) (y := 2) (z := 0) (by norm_num) (by norm_num)
  (by first | decide | norm_num) (by norm_num) (by norm_num) (by norm_num)
example := A1 (e := 2) (f := 5) (j := 3) (x := 0) (y := 3) (z := 0) (by norm_num) (by norm_num)
  (by first | decide | norm_num) (by norm_num) (by norm_num) (by norm_num)
example : 1 * (2 * 3) + 0 * (3 ^ 2 - 2 ^ 2) + 1 * 3 ^ 2 = 3 * (3 ^ 2 - 2 ^ 2) ∧ ¬ (1 = 0 ∧ 0 = 3 ∧ 1 = 0) := by
  norm_num
example : 3 * (2 * 5) + 0 * (5 ^ 2 - 2 ^ 2) + 3 * 5 ^ 2 = 5 * (5 ^ 2 - 2 ^ 2) ∧ ¬ (3 = 0 ∧ 0 = 5 ∧ 3 = 0) := by
  norm_num

-- (A5): `2 c = 3 a` at (2, 3) (no `b`); `2 c = 5 a` at (2, 5); control at j = f: `f c` has a representation with `b`
example := A5 (e := 2) (f := 3) (j := 2) (x := 3) (y := 0) (z := 0) (by norm_num) (by norm_num)
  (by first | decide | norm_num) (by norm_num) (by norm_num) (by norm_num)
example := A5 (e := 2) (f := 5) (j := 2) (x := 5) (y := 0) (z := 0) (by norm_num) (by norm_num)
  (by first | decide | norm_num) (by norm_num) (by norm_num) (by norm_num)
example : 2 * (2 * 3) + 3 * (3 ^ 2 - 2 ^ 2) + 0 * 3 ^ 2 = 3 * 3 ^ 2 ∧ 3 ≠ 0 := by norm_num

-- (Aa): `2 a = a^2` at (2, 3); `4 a = a^4` at (2, 5); control at j = f: `f a = e c`, here 18 = 2 * 9
example := Aa (e := 2) (f := 3) (j := 2) (x := 2) (y := 0) (z := 0) (by norm_num) (by norm_num)
  (by first | decide | norm_num) (by norm_num) (by norm_num) (by norm_num)
example := Aa (e := 2) (f := 5) (j := 4) (x := 4) (y := 0) (z := 0) (by norm_num) (by norm_num)
  (by first | decide | norm_num) (by norm_num) (by norm_num) (by norm_num)
example : 0 * (2 * 3) + 0 * (3 ^ 2 - 2 ^ 2) + 2 * 3 ^ 2 = 3 * (2 * 3) ∧ ¬ (0 = 3) := by norm_num

-- (C-QB): the side QB of W_1: length 28 at (2, 3), 92 at (2, 5), with M e = 2 < f
example := C_QB (e := 2) (f := 3) (M := 1) (x := 3) (y := 2) (z := 0) (by norm_num) (by norm_num)
  (by first | decide | norm_num) (by norm_num)
example := C_QB (e := 2) (f := 5) (M := 1) (x := 5) (y := 2) (z := 0) (by norm_num) (by norm_num)
  (by first | decide | norm_num) (by norm_num)

-- (C-base): the base of T_1: length 46 at (2, 3), 142 at (2, 5)
example := C_base (e := 2) (f := 3) (M := 1) (x := 6) (y := 2) (z := 0) (by norm_num) (by norm_num)
  (by first | decide | norm_num) (by norm_num)
example := C_base (e := 2) (f := 5) (M := 1) (x := 10) (y := 2) (z := 0) (by norm_num) (by norm_num)
  (by first | decide | norm_num) (by norm_num)

-- (C-AQ): the side AQ of W_M: M f b = 30 at (2, 3), M = 2, with M (f - e) = 2 <= e = 2: the representation (2, 0, 2) has z = 2
example := C_AQ (e := 2) (f := 3) (M := 2) (x := 2) (y := 0) (z := 2) (by norm_num) (by norm_num)
  (by first | decide | norm_num) (by norm_num)
-- at (2, 5) the condition M (f - e) = 3 M <= 2 never holds; `f ∣ y` for the representation (8, 0, 1) of 105
example := C_AQ (e := 2) (f := 5) (M := 1) (x := 8) (y := 0) (z := 1) (by norm_num) (by norm_num)
  (by first | decide | norm_num) (by norm_num)
-- the member (3, 5), M = 1: M (f - e) = 2 <= 3, M f b = 80, (2, 0, 2): z = 2 <= 2
example := C_AQ (e := 3) (f := 5) (M := 1) (x := 2) (y := 0) (z := 2) (by norm_num) (by norm_num)
  (by first | decide | norm_num) (by norm_num)
-- control: M (f - e) = e + 1 at (2, 3), M = 3: M f b = 45 = 5 c, z = 5 > 3
example : 0 * (2 * 3) + 0 * (3 ^ 2 - 2 ^ 2) + 5 * 3 ^ 2 = 3 * 3 * (3 ^ 2 - 2 ^ 2) ∧ ¬ (5 ≤ 3 * (3 - 2)) := by
  norm_num

end Erdos634.Draft.SideRunGArith

#print axioms Erdos634.Draft.SideRunGArith.r0_residues
#print axioms Erdos634.Draft.SideRunGArith.r0_inv
#print axioms Erdos634.Draft.SideRunGArith.r0
#print axioms Erdos634.Draft.SideRunGArith.r0_inv_form
#print axioms Erdos634.Draft.SideRunGArith.A1
#print axioms Erdos634.Draft.SideRunGArith.A5
#print axioms Erdos634.Draft.SideRunGArith.Aa
#print axioms Erdos634.Draft.SideRunGArith.C_QB
#print axioms Erdos634.Draft.SideRunGArith.C_base
#print axioms Erdos634.Draft.SideRunGArith.C_AQ
