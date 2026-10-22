import Mathlib

/-!
# Beeson Theorem 14 (arXiv 1206.2229v4): the counting identity, general parameters

Tile `(a,b,c)` with `3 alpha + 2 beta = pi`, i.e. `a^2 + c*b = c^2` (`c | a^2`, `b = c - a^2/c`),
`l = lcm(a,c) = j*c`, `k = l*b/a`.  Fig. 17 pattern: three quadratic tilings of scale `l`, one of scale `j*a`,
one of scale `j*b`, and a parallelogram of `(k - j*a) x (j*a)` cells of two tiles each.
`thm14_count` : total `= j^2 (b+c)(b+2c)` (Beeson's `N`); `thm14_rows` : `k - j*a > 0 <-> c < 2b`.
The geometric statement is formalized per instance, `BeesonT14_a_b_c.lean` and `BeesonFig17.lean`.
Credit Beeson (arXiv 1206.2229), Laczkovich.  UNAUDITED.
-/

namespace Erdos634.BeesonT14Count

theorem thm14_count (a b c j r : ℕ) (h : a * a + c * b = c * c)
    (hk : (j * a + r) * a = j * c * b) :
    3 * (j * c) ^ 2 + (j * b) ^ 2 + (j * a) ^ 2 + 2 * r * (j * a) = j ^ 2 * (b + c) * (b + 2 * c) := by
  have h' : ((a : ℤ) * a + c * b = c * c) := by exact_mod_cast h
  have hk' : (((j : ℤ) * a + r) * a = j * c * b) := by exact_mod_cast hk
  have : (3 * ((j : ℤ) * c) ^ 2 + (j * b) ^ 2 + (j * a) ^ 2 + 2 * r * (j * a)) =
      j ^ 2 * (b + c) * (b + 2 * c) := by
    linear_combination (2 * (j : ℤ)) * hk' - (j : ℤ) ^ 2 * h'
  exact_mod_cast this

theorem thm14_rows (a b c j k : ℕ) (ha : 0 < a) (hj : 0 < j) (hc : 0 < c) (h : a * a + c * b = c * c)
    (hk : k * a = j * c * b) : j * a < k ↔ c < 2 * b := by
  constructor
  · intro hlt
    have h1 : (j * a) * a < k * a := Nat.mul_lt_mul_of_pos_right hlt ha
    have h2 : j * (a * a) < j * (c * b) := by nlinarith
    have h3 : a * a < c * b := Nat.lt_of_mul_lt_mul_left h2
    have h4 : c * c < c * (2 * b) := by nlinarith
    exact Nat.lt_of_mul_lt_mul_left h4
  · intro hlt
    have h4 : c * c < c * (2 * b) := Nat.mul_lt_mul_of_pos_left hlt hc
    have h3 : a * a < c * b := by nlinarith
    have h2 : j * (a * a) < j * (c * b) := Nat.mul_lt_mul_of_pos_left h3 hj
    have h1 : (j * a) * a < k * a := by nlinarith
    exact Nat.lt_of_mul_lt_mul_right h1

/-- Fig. 17: `(a,b,c) = (6,5,9)`, `j = 2`, `k = 15`, `r = 3`: `N = 1288`. -/
theorem count_6_5_9 : 3 * (2 * 9) ^ 2 + (2 * 5) ^ 2 + (2 * 6) ^ 2 + 2 * 3 * (2 * 6) = 1288 := by norm_num
theorem hyp_6_5_9 : 6 * 6 + 9 * 5 = 9 * 9 ∧ (2 * 6 + 3) * 6 = 2 * 9 * 5 := by norm_num
theorem count_family_6_5_9 : 3 * (2 * 9) ^ 2 + (2 * 5) ^ 2 + (2 * 6) ^ 2 + 2 * 3 * (2 * 6)
    = 2 ^ 2 * (5 + 9) * (5 + 2 * 9) :=
  thm14_count 6 5 9 2 3 (by norm_num) (by norm_num)

end Erdos634.BeesonT14Count
