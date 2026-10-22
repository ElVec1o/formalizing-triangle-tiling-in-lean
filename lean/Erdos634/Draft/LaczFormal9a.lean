import Erdos634.Draft.LaczFormalThm33if5

/-!
# Laczkovich, Discrete Math. 140 (1995) 79-94, Lemma 3.2 (and a witness for Theorem 3.1)

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) Lemma 3.2, Thm 3.1), Beeson, Beeson-Zhang.
Formalization debt, not progress on the /goal outcomes.

Printed Lemma 3.2: let `x, y` be non-zero rationals with `x + 2y != 0 != y + 2x`.  Then
`a = |x(x+2y)|`, `b = |y(y+2x)|`, `c = x^2 + xy + y^2` are the sides of a rational triangle with angle `gamma = pi/3` or `2pi/3`.

* `lemma32_dm140`: exactly that: a rational tile `R : RTri` with `R.a = a`, `R.b = b`, `R.c = c`, and the angle opposite `c`
  (`vang R.Δ 2`) equal to `pi/3` or `2pi/3`.  Also the sign statement: `pi/3` iff `x y (x+2y)(y+2x) > 0`.
* `thm31_witness_357`: witness for the hypotheses of Theorem 3.1 (`thm33_if_rtri_2pi3`): the rational triangle `(3,5,7)`
  has `gamma = 2pi/3`, and so an equilateral `CongruentDissection` by it exists (`Thm33If` at its angles).
-/

open scoped Classical
open EuclideanGeometry Erdos634.Geometry Erdos634.RegionDissection Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
  Erdos634.Draft.LaczFormal Erdos634.LaczL35 Erdos634.LaczL22 Erdos634.CertCoord Erdos634.LaczThm33If

namespace Erdos634.Laczkovich9

theorem tri_ineq (a b c s : ℚ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hs : s = 1 ∨ s = -1)
    (h : c ^ 2 = a ^ 2 + b ^ 2 - s * a * b) : a < b + c ∧ b < a + c ∧ c < a + b := by
  have hab : 0 < a * b := mul_pos ha hb
  rcases hs with rfl | rfl
  · refine ⟨?_, ?_, ?_⟩
    · by_contra hh; push_neg at hh
      nlinarith [mul_pos hb hc, mul_pos ha hb, mul_pos ha hc, sq_nonneg (a - b - c)]
    · by_contra hh; push_neg at hh
      nlinarith [mul_pos ha hc, mul_pos ha hb, mul_pos hb hc, sq_nonneg (b - a - c)]
    · by_contra hh; push_neg at hh
      nlinarith [mul_pos ha hb]
  · refine ⟨?_, ?_, ?_⟩
    · by_contra hh; push_neg at hh
      nlinarith [mul_pos hb hc, mul_pos ha hb, mul_pos ha hc]
    · by_contra hh; push_neg at hh
      nlinarith [mul_pos ha hc, mul_pos ha hb, mul_pos hb hc]
    · by_contra hh; push_neg at hh
      nlinarith [mul_pos ha hb]

/-- **Laczkovich DM 140 (1995), Lemma 3.2.** -/
theorem lemma32_dm140 (x y : ℚ) (hx : x ≠ 0) (hy : y ≠ 0) (h1 : x + 2 * y ≠ 0) (h2 : y + 2 * x ≠ 0) :
    ∃ R : RTri, R.a = |x * (x + 2 * y)| ∧ R.b = |y * (y + 2 * x)| ∧ R.c = x ^ 2 + x * y + y ^ 2 ∧
      ((vang R.Δ 2 = Real.pi / 3 ∧ 0 < x * y * (x + 2 * y) * (y + 2 * x)) ∨
        (vang R.Δ 2 = 2 * Real.pi / 3 ∧ x * y * (x + 2 * y) * (y + 2 * x) < 0)) := by
  set P : ℚ := x * (x + 2 * y) with hP
  set Q : ℚ := y * (y + 2 * x) with hQ
  have hP0 : P ≠ 0 := mul_ne_zero hx h1
  have hQ0 : Q ≠ 0 := mul_ne_zero hy h2
  have ha : 0 < |P| := abs_pos.mpr hP0
  have hb : 0 < |Q| := abs_pos.mpr hQ0
  have hcpos : 0 < x ^ 2 + x * y + y ^ 2 := by
    rcases eq_or_ne x 0 with h | h
    · exact absurd h hx
    · nlinarith [sq_nonneg (x + 2 * y), sq_pos_of_ne_zero h, sq_pos_of_ne_zero hy]
  have hid : (x ^ 2 + x * y + y ^ 2) ^ 2 = P ^ 2 + Q ^ 2 - P * Q := by rw [hP, hQ]; ring
  have hprod : x * y * (x + 2 * y) * (y + 2 * x) = P * Q := by rw [hP, hQ]; ring
  have hpq : 0 < P * Q ∨ P * Q < 0 := (lt_or_gt_of_ne (mul_ne_zero hP0 hQ0)).symm
  have habs : |P| * |Q| = |P * Q| := (abs_mul P Q).symm
  have hsq : |P| ^ 2 = P ^ 2 := sq_abs P
  have hsq' : |Q| ^ 2 = Q ^ 2 := sq_abs Q
  -- the cosine rule data
  have key : ∀ s : ℚ, (s = 1 ∧ 0 < P * Q) ∨ (s = -1 ∧ P * Q < 0) →
      (x ^ 2 + x * y + y ^ 2) ^ 2 = |P| ^ 2 + |Q| ^ 2 - s * |P| * |Q| := by
    intro s hs
    have e : s * |P| * |Q| = s * |P * Q| := by rw [← habs]; ring
    rw [e]
    rcases hs with ⟨rfl, hpos⟩ | ⟨rfl, hneg⟩
    · rw [abs_of_pos hpos, hsq, hsq', hid]; ring
    · rw [abs_of_neg hneg, hsq, hsq', hid]; ring
  have hcosR : ∀ R : RTri, R.a = |P| → R.b = |Q| → R.c = x ^ 2 + x * y + y ^ 2 → ∀ s : ℚ,
      (x ^ 2 + x * y + y ^ 2) ^ 2 = |P| ^ 2 + |Q| ^ 2 - s * |P| * |Q| →
      Real.cos (vang R.Δ 2) = s / 2 := by
    intro R ra rb rc s hs
    rw [cos_vang2 R, ra, rb, rc]
    have hsR : ((x ^ 2 + x * y + y ^ 2 : ℚ) : ℝ) ^ 2 = ((|P| : ℚ) : ℝ) ^ 2 + ((|Q| : ℚ) : ℝ) ^ 2 - (s : ℝ) * (|P| : ℚ) * (|Q| : ℚ) := by
      exact_mod_cast hs
    have haR : ((|P| : ℚ) : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
    have hbR : ((|Q| : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
    rw [hsR]
    field_simp
    ring
  have hcos : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
  have hcos2 : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num
  have hpi := Real.pi_pos
  rcases hpq with hpos | hneg
  · have hk := key 1 (Or.inl ⟨rfl, hpos⟩)
    obtain ⟨hi1, hi2, hi3⟩ := tri_ineq _ _ _ 1 ha hb hcpos (Or.inl rfl) hk
    obtain ⟨R, ra, rb, rc⟩ := exists_RTri_rat _ _ _ ha hb hcpos hi1 hi2 hi3
    refine ⟨R, ra, rb, rc, Or.inl ⟨?_, by rw [hprod]; exact hpos⟩⟩
    have hc := hcosR R ra rb rc 1 hk
    refine angle_eq_of_cos (angle_nonneg _ _ _) (angle_le_pi _ _ _) (by positivity) (by linarith) ?_
    rw [hc, hcos] <;> norm_num
  · have hk := key (-1) (Or.inr ⟨rfl, hneg⟩)
    obtain ⟨hi1, hi2, hi3⟩ := tri_ineq _ _ _ (-1) ha hb hcpos (Or.inr rfl) hk
    obtain ⟨R, ra, rb, rc⟩ := exists_RTri_rat _ _ _ ha hb hcpos hi1 hi2 hi3
    refine ⟨R, ra, rb, rc, Or.inr ⟨?_, by rw [hprod]; exact hneg⟩⟩
    have hc := hcosR R ra rb rc (-1) hk
    refine angle_eq_of_cos (angle_nonneg _ _ _) (angle_le_pi _ _ _) (by positivity) (by linarith) ?_
    rw [hc, hcos2] <;> norm_num

/-- Witness for the hypotheses of Lemma 3.2: `x = -1, y = 4` (the printed example, the triangle `(7, 8, 13)` with `gamma = 2pi/3`
is `x = -1, y = 4` up to the absolute values; here we check the sign condition and the conclusion). -/
theorem lemma32_dm140_witness : ∃ R : RTri, R.a = 7 ∧ R.b = 8 ∧ R.c = 13 ∧ vang R.Δ 2 = 2 * Real.pi / 3 := by
  obtain ⟨R, ra, rb, rc, h⟩ := lemma32_dm140 (-1) 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨R, by rw [ra]; norm_num, by rw [rb]; norm_num, by rw [rc]; norm_num, ?_⟩
  rcases h with ⟨_, hpos⟩ | ⟨h2, _⟩
  · exfalso; norm_num at hpos
  · exact h2

/-- Witness for the hypothesis of Theorem 3.1 (rational triangle with an angle `2pi/3`): the triangle `(3,5,7)`. -/
theorem thm31_witness_357 : ∃ R : RTri, R.a = 3 ∧ R.b = 5 ∧ R.c = 7 ∧
    ∃ (N : ℕ) (D : CongruentDissection N), Equilateral D ∧
      TileAngles D (vang R.Δ 0) (vang R.Δ 1) (vang R.Δ 2) := by
  obtain ⟨R, ra, rb, rc⟩ := exists_RTri_rat 3 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨R, ra, rb, rc, ?_⟩
  have hk : Real.cos (vang R.Δ 2) = -1 / 2 := by
    rw [cos_vang2 R, ra, rb, rc]; norm_num
  have hcos2 : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num
  have hpi := Real.pi_pos
  have hz : vang R.Δ 2 = 2 * Real.pi / 3 :=
    angle_eq_of_cos (angle_nonneg _ _ _) (angle_le_pi _ _ _) (by positivity) (by linarith) (by rw [hk, hcos2])
  exact thm33_if_rtri_2pi3 R hz

end Erdos634.Laczkovich9

#print axioms Erdos634.Laczkovich9.lemma32_dm140
#print axioms Erdos634.Laczkovich9.lemma32_dm140_witness
#print axioms Erdos634.Laczkovich9.thm31_witness_357
