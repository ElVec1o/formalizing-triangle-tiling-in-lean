-- Draft/LaczFormalIVcRatB7a.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch), BLUEPRINT Part B, item B7 (row of rhombi), stage a: the WEDGE ALGEBRA.
--   Frame coordinates: a vector e = a p + beta q with |p| = |q| = b, p.q = b^2/2 has |e|^2 = b^2 (a^2 + a beta + beta^2) and e.e' = b^2 (a a' + beta beta' + (a beta' + a' beta)/2).
--   `wedge_extremes`: two unit vectors (in the form Q = 1) at the angle pi/3 (B = 1/2) lying in the closed quadrant a, beta >= 0 are the two basis vectors (1,0), (0,1) in some order.
--   `wedge_in_quadrant`: two such unit vectors with beta >= 0 whose wedge {s e1 + t e2} (s,t >= 0, s+t <= 1) avoids the open box (-1,0) x (0,1) lie in the quadrant a >= 0.
--   `frame_norm`: |a p + beta q|^2 = b^2 Q(a,beta).
--   Used by the step lemma of B7 (a cell with a vertex U on the supporting line along XY must be the triangle U, U+p, U+q).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Beeson, Beeson-Zhang.
import Mathlib

namespace Erdos634.Draft.LaczFormal.RG

/-- Gram identity of the frame (determinant of the Gram matrix of the basis p, q is 3/4). -/
theorem gram_identity (a1 b1 a2 b2 : ℝ) :
    (a1 ^ 2 + a1 * b1 + b1 ^ 2) * (a2 ^ 2 + a2 * b2 + b2 ^ 2) - (a1 * a2 + b1 * b2 + (a1 * b2 + a2 * b1) / 2) ^ 2
      = 3 / 4 * (a1 * b2 - a2 * b1) ^ 2 := by ring

/-- Unit vectors at angle pi/3 in the closed quadrant are the two basis vectors. -/
theorem wedge_extremes {a1 b1 a2 b2 : ℝ} (hQ1 : a1 ^ 2 + a1 * b1 + b1 ^ 2 = 1) (hQ2 : a2 ^ 2 + a2 * b2 + b2 ^ 2 = 1)
    (hB : a1 * a2 + b1 * b2 + (a1 * b2 + a2 * b1) / 2 = 1 / 2)
    (h1 : 0 ≤ a1) (h2 : 0 ≤ b1) (h3 : 0 ≤ a2) (h4 : 0 ≤ b2) :
    (a1 = 1 ∧ b1 = 0 ∧ a2 = 0 ∧ b2 = 1) ∨ (a1 = 0 ∧ b1 = 1 ∧ a2 = 1 ∧ b2 = 0) := by
  have hg := gram_identity a1 b1 a2 b2
  rw [hQ1, hQ2, hB] at hg
  have hD : (a1 * b2 - a2 * b1) ^ 2 = 1 := by nlinarith
  have ha1 : a1 ≤ 1 := by nlinarith [mul_nonneg h1 h2, sq_nonneg b1]
  have hb1 : b1 ≤ 1 := by nlinarith [mul_nonneg h1 h2, sq_nonneg a1]
  have ha2 : a2 ≤ 1 := by nlinarith [mul_nonneg h3 h4, sq_nonneg b2]
  have hb2 : b2 ≤ 1 := by nlinarith [mul_nonneg h3 h4, sq_nonneg a2]
  have hcase : a1 * b2 - a2 * b1 = 1 ∨ a1 * b2 - a2 * b1 = -1 := by
    have : (a1 * b2 - a2 * b1 - 1) * (a1 * b2 - a2 * b1 + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  rcases hcase with h | h
  · left
    have hp : 0 ≤ a2 * b1 := mul_nonneg h3 h2
    have hle : a1 * b2 ≤ 1 * 1 := mul_le_mul ha1 hb2 h4 (by norm_num)
    have h11 : a1 * b2 = 1 := by linarith
    have ha : a1 = 1 := by nlinarith [mul_le_mul_of_nonneg_left hb2 h1]
    have hb : b2 = 1 := by nlinarith [mul_le_mul_of_nonneg_left ha1 h4]
    subst ha hb
    have hb1' : b1 = 0 := by nlinarith
    subst hb1'
    have ha2' : a2 = 0 := by nlinarith
    exact ⟨rfl, rfl, ha2', rfl⟩
  · right
    have hp : 0 ≤ a1 * b2 := mul_nonneg h1 h4
    have hle : a2 * b1 ≤ 1 * 1 := mul_le_mul ha2 hb1 h2 (by norm_num)
    have h11 : a2 * b1 = 1 := by linarith
    have ha : a2 = 1 := by nlinarith [mul_le_mul_of_nonneg_left hb1 h3]
    have hb : b1 = 1 := by nlinarith [mul_le_mul_of_nonneg_left ha2 h2]
    subst ha hb
    have hb2' : b2 = 0 := by nlinarith
    subst hb2'
    have ha1' : a1 = 0 := by nlinarith
    exact ⟨ha1', rfl, rfl, rfl⟩

/-- A unit vector with `b >= 0` has `a >= -2` and `b < 2`. -/
theorem unit_bounds {a b : ℝ} (hQ : a ^ 2 + a * b + b ^ 2 = 1) (hb : 0 ≤ b) : -2 < a ∧ b < 2 := by
  have hb2 : b < 2 := by nlinarith [sq_nonneg (a + b / 2)]
  refine ⟨?_, hb2⟩
  nlinarith [sq_nonneg (a + b / 2)]

/-- One direction: a unit vector with `b >= 0` and `a < 0` meeting the open box along its own ray is impossible. -/
theorem no_neg_a_first {a1 b1 a2 b2 : ℝ} (hQ1 : a1 ^ 2 + a1 * b1 + b1 ^ 2 = 1) (hQ2 : a2 ^ 2 + a2 * b2 + b2 ^ 2 = 1)
    (hB : a1 * a2 + b1 * b2 + (a1 * b2 + a2 * b1) / 2 = 1 / 2) (h2 : 0 ≤ b1) (h4 : 0 ≤ b2)
    (hO : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → s + t ≤ 1 →
      ¬ (-1 < s * a1 + t * a2 ∧ s * a1 + t * a2 < 0 ∧ 0 < s * b1 + t * b2 ∧ s * b1 + t * b2 < 1)) :
    0 ≤ a1 := by
  by_contra hneg
  push Not at hneg
  obtain ⟨hl1, hu1⟩ := unit_bounds hQ1 h2
  obtain ⟨hl2, hu2⟩ := unit_bounds hQ2 h4
  rcases h2.lt_or_eq with hb1 | hb1
  · exact hO (1 / 4) 0 (by norm_num) le_rfl (by norm_num) ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · -- b1 = 0, so a1 = -1
    have hb1' : b1 = 0 := hb1.symm
    subst hb1'
    have ha1 : a1 = -1 := by nlinarith
    subst ha1
    have hb2 : 0 < b2 := by
      rcases h4.lt_or_eq with h | h
      · exact h
      · exfalso
        have h' : b2 = 0 := h.symm
        subst h'
        nlinarith
    have ha2 : a2 = -1 / 2 - b2 / 2 := by nlinarith
    exact hO (1 / 2) (1 / 8) (by norm_num) (by norm_num) (by norm_num)
      ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- Both vectors of the wedge lie in the half plane `a >= 0`. -/
theorem wedge_in_quadrant {a1 b1 a2 b2 : ℝ} (hQ1 : a1 ^ 2 + a1 * b1 + b1 ^ 2 = 1) (hQ2 : a2 ^ 2 + a2 * b2 + b2 ^ 2 = 1)
    (hB : a1 * a2 + b1 * b2 + (a1 * b2 + a2 * b1) / 2 = 1 / 2) (h2 : 0 ≤ b1) (h4 : 0 ≤ b2)
    (hO : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → s + t ≤ 1 →
      ¬ (-1 < s * a1 + t * a2 ∧ s * a1 + t * a2 < 0 ∧ 0 < s * b1 + t * b2 ∧ s * b1 + t * b2 < 1)) :
    0 ≤ a1 ∧ 0 ≤ a2 := by
  refine ⟨no_neg_a_first hQ1 hQ2 hB h2 h4 hO, ?_⟩
  refine no_neg_a_first hQ2 hQ1 (by linarith) h4 h2 ?_
  intro s t hs ht hst
  have := hO t s ht hs (by linarith)
  intro ⟨c1, c2, c3, c4⟩
  exact this ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Combined wedge lemma: unit vectors at angle pi/3, `b >= 0`, avoiding the box: the basis vectors. -/
theorem wedge_basis {a1 b1 a2 b2 : ℝ} (hQ1 : a1 ^ 2 + a1 * b1 + b1 ^ 2 = 1) (hQ2 : a2 ^ 2 + a2 * b2 + b2 ^ 2 = 1)
    (hB : a1 * a2 + b1 * b2 + (a1 * b2 + a2 * b1) / 2 = 1 / 2) (h2 : 0 ≤ b1) (h4 : 0 ≤ b2)
    (hO : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → s + t ≤ 1 →
      ¬ (-1 < s * a1 + t * a2 ∧ s * a1 + t * a2 < 0 ∧ 0 < s * b1 + t * b2 ∧ s * b1 + t * b2 < 1)) :
    (a1 = 1 ∧ b1 = 0 ∧ a2 = 0 ∧ b2 = 1) ∨ (a1 = 0 ∧ b1 = 1 ∧ a2 = 1 ∧ b2 = 0) := by
  obtain ⟨h1, h3⟩ := wedge_in_quadrant hQ1 hQ2 hB h2 h4 hO
  exact wedge_extremes hQ1 hQ2 hB h1 h2 h3 h4

/-- Norm and inner product in the frame (vectors `a p + b q`). -/
theorem frame_norm {p0 p1 q0 q1 b : ℝ} (hp : p0 ^ 2 + p1 ^ 2 = b ^ 2) (hq : q0 ^ 2 + q1 ^ 2 = b ^ 2)
    (hpq : p0 * q0 + p1 * q1 = b ^ 2 / 2) (a1 b1 a2 b2 : ℝ) :
    (a1 * p0 + b1 * q0) * (a2 * p0 + b2 * q0) + (a1 * p1 + b1 * q1) * (a2 * p1 + b2 * q1)
      = b ^ 2 * (a1 * a2 + b1 * b2 + (a1 * b2 + a2 * b1) / 2) := by
  have : (a1 * p0 + b1 * q0) * (a2 * p0 + b2 * q0) + (a1 * p1 + b1 * q1) * (a2 * p1 + b2 * q1)
      = a1 * a2 * (p0 ^ 2 + p1 ^ 2) + b1 * b2 * (q0 ^ 2 + q1 ^ 2) + (a1 * b2 + a2 * b1) * (p0 * q0 + p1 * q1) := by ring
  rw [this, hp, hq, hpq]; ring

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.wedge_extremes
#print axioms Erdos634.Draft.LaczFormal.RG.wedge_basis
