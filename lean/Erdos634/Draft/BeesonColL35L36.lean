import Mathlib
import Erdos634.Draft.BeesonRowL30

/-!
# Beeson-Rosu (arXiv 2607.23453 v2) Lemma 35 (isosceles-beta side lengths) and Lemma 36 (no b-edges on the equal sides)

NOTE, UNAUDITED.  Credit: Michael Beeson and Rosu (arXiv 2607.23453 v2, Lemmas 35, 36), Beeson (arXiv 1206.2229 v4, Theorem 19
for equation (6)), Laczkovich (DCG 48 (2012)), Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.

Lemma 35.  Tile `(a, b, c) = (km, k^2-m^2, k^2)`, `0 < m < k`.  ABC isosceles `(beta, beta, 3 alpha)`, equal sides `X`, base `Y`.
Named hypotheses (nothing else):
  * `hY`   : `Y = 2 X cos beta`  (the printed perpendicular-from-B argument; geometry of an isosceles triangle),
  * `hcos` : `cos beta = (a^2+c^2-b^2)/(2ac)`  (law of cosines in the tile),
  * `harea`: `X Y = N a c`  (area of ABC equals N tile areas, the common factor `sin beta / 2` cancelled),
  * `h6`   : `N = j^2 (3k^2 - m^2)`  (printed equation (6), cited to Beeson [3, Theorem 19]; NOT proved here).
Conclusions as printed: `X = j k c`, `Y = j m (b+2c)`, `Y/X = a(b+2c)/c^2`, `Y < 2X`.  Witnessed at `(k,m,j) = (3,1,1)`.

Lemma 36.  `X = k c = p a + q b + r c` in naturals with `r >= 1` (the named hypothesis is the conclusion of the printed Lemma 31,
"every side has a c edge", NOT proved here; Lemma 31 needs alpha/pi irrational, Lemma 27): then `q = 0`.  Uses `lemma30_C`.
-/

namespace Erdos634.BeesonColL35L36

theorem lemma35 {k m j N X Y β : ℝ} (hm : 0 < m) (hmk : m < k) (hj : 0 < j) (hX : 0 < X)
    (hY : Y = 2 * X * Real.cos β)
    (hcos : Real.cos β = ((k * m) ^ 2 + (k ^ 2) ^ 2 - (k ^ 2 - m ^ 2) ^ 2) / (2 * (k * m) * k ^ 2))
    (harea : X * Y = N * (k * m) * k ^ 2)
    (h6 : N = j ^ 2 * (3 * k ^ 2 - m ^ 2)) :
    X = j * k * k ^ 2 ∧ Y = j * m * ((k ^ 2 - m ^ 2) + 2 * k ^ 2) ∧
    Y / X = (k * m) * ((k ^ 2 - m ^ 2) + 2 * k ^ 2) / (k ^ 2) ^ 2 ∧ Y < 2 * X := by
  have hk : 0 < k := by linarith
  have hk3 : 0 < k ^ 3 := by positivity
  have hq : Real.cos β = m * (3 * k ^ 2 - m ^ 2) / (2 * k ^ 3) := by
    rw [hcos]; field_simp; ring
  have hYX : Y = X * (m * (3 * k ^ 2 - m ^ 2) / k ^ 3) := by
    rw [hY, hq]; field_simp
  have h3 : 0 < 3 * k ^ 2 - m ^ 2 := by nlinarith
  have hXsq : X ^ 2 = (j * k ^ 3) ^ 2 := by
    have e0 : X * (X * (m * (3 * k ^ 2 - m ^ 2) / k ^ 3)) = N * (k * m) * k ^ 2 := by rw [← hYX]; exact harea
    have l : X ^ 2 * (m * (3 * k ^ 2 - m ^ 2)) = X * (X * (m * (3 * k ^ 2 - m ^ 2) / k ^ 3)) * k ^ 3 := by
      field_simp
    have e1 : X ^ 2 * (m * (3 * k ^ 2 - m ^ 2)) = (j * k ^ 3) ^ 2 * (m * (3 * k ^ 2 - m ^ 2)) := by
      rw [l, e0, h6]; ring
    exact mul_right_cancel₀ (mul_pos hm h3).ne' e1
  have hXe : X = j * k * k ^ 2 := by
    have hp : 0 < j * k ^ 3 := by positivity
    have := (sq_eq_sq₀ hX.le hp.le).mp hXsq
    rw [this]; ring
  refine ⟨hXe, ?_, ?_, ?_⟩
  · rw [hYX, hXe]; field_simp; ring
  · rw [hYX]; field_simp; ring
  · rw [hYX]
    have : m * (3 * k ^ 2 - m ^ 2) / k ^ 3 < 2 := by
      rw [div_lt_iff₀ hk3]
      nlinarith [mul_pos (mul_pos (sub_pos.mpr hmk) (sub_pos.mpr hmk)) (by linarith : (0 : ℝ) < 2 * k + m)]
    nlinarith

/-- witness: all hypotheses of `lemma35` hold at `(k,m,j) = (3,1,1)`, `N = 26`, `X = 27`, `Y = 26`, `beta = arccos (13/27)`. -/
theorem lemma35_wit : ∃ (k m j N X Y β : ℝ), 0 < m ∧ m < k ∧ 0 < j ∧ 0 < X ∧ Y = 2 * X * Real.cos β ∧
    Real.cos β = ((k * m) ^ 2 + (k ^ 2) ^ 2 - (k ^ 2 - m ^ 2) ^ 2) / (2 * (k * m) * k ^ 2) ∧
    X * Y = N * (k * m) * k ^ 2 ∧ N = j ^ 2 * (3 * k ^ 2 - m ^ 2) := by
  refine ⟨3, 1, 1, 26, 27, 26, Real.arccos (13 / 27), by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_, by norm_num, by norm_num⟩
  · rw [Real.cos_arccos (by norm_num) (by norm_num)]; norm_num
  · rw [Real.cos_arccos (by norm_num) (by norm_num)]; norm_num

/-- Lemma 36 arithmetic: with `j = 1` (`X = k c`) and at least one c edge (`r >= 1`), no b edges: `q = 0`. -/
theorem lemma36 {k m : ℤ} (hm : 0 < m) (hmk : m < k) (hcop : IsCoprime m k) {p q r : ℤ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr1 : 1 ≤ r)
    (h : p * (k * m) + q * (k ^ 2 - m ^ 2) + r * k ^ 2 = k * k ^ 2) : q = 0 := by
  have hk : 0 < k := by linarith
  have hb : 0 < k ^ 2 - m ^ 2 := by nlinarith
  have ha : 0 < k * m := by positivity
  have hrk : r ≤ k := by
    by_contra hc; push Not at hc
    nlinarith [mul_nonneg hp ha.le, mul_nonneg hq hb.le, mul_pos (by linarith : (0:ℤ) < r - k) (by positivity : (0:ℤ) < k ^ 2)]
  rcases hrk.eq_or_lt with hrk | hrk
  · have h' := h
    rw [hrk] at h'
    have : q * (k ^ 2 - m ^ 2) = 0 := by nlinarith [mul_nonneg hp ha.le, mul_nonneg hq hb.le]
    exact (mul_eq_zero.mp this).resolve_right hb.ne'
  · exact BeesonRowL30.lemma30_C hm hmk hcop (n := k - r) (p := p) (q := q) (r := 0) (by linarith) (by linarith) hp hq le_rfl
      (by linear_combination h)

/-- witness for the hypotheses of `lemma36` at `(m,k) = (1,3)`: `p=0,q=0,r=3`. -/
theorem lemma36_wit : ∃ (k m p q r : ℤ), 0 < m ∧ m < k ∧ IsCoprime m k ∧ 0 ≤ p ∧ 0 ≤ q ∧ 1 ≤ r ∧
    p * (k * m) + q * (k ^ 2 - m ^ 2) + r * k ^ 2 = k * k ^ 2 :=
  ⟨3, 1, 0, 0, 3, by norm_num, by norm_num, isCoprime_one_left, le_rfl, le_rfl, by norm_num, by norm_num⟩

end Erdos634.BeesonColL35L36
