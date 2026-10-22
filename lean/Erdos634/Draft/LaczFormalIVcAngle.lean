-- Draft/LaczFormalIVcAngle.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, gamma = pi/3, alpha + beta = 2pi/3), the display
--   b/a = sin beta / sin alpha = sin(2pi/3 - alpha)/sin alpha = (sqrt 3 / 2) cot alpha + 1/2:  if a, b are commensurable and alpha/pi is rational then alpha in {pi/6, pi/3, pi/2}.
--   `ivc_alpha_classify` : 0 < alpha < 2pi/3, sin(2pi/3 - alpha) = q sin alpha (q rational), alpha = s pi (s rational)  ==>  alpha = pi/6 or pi/3 or pi/2.
--   The printed text then discards alpha = pi/3 (a = b = c contradicts 'c/a irrational') and uses the symmetry alpha <-> beta to reduce pi/6 to pi/2 (a = 2b); not formalized here.
--   `ivc_alpha_witness` (all three values satisfy the hypotheses, ratios 2, 1, 1/2), `ivc_alpha_pi4_control` (pi/4 does not: sqrt 3 irrational).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Beeson, Beeson-Zhang, Niven (Mathlib `Real.niven_angle_eq`).
import Mathlib.NumberTheory.Niven
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Erdos634.Draft.LaczFormal.Thm21

open Real

theorem ivc_rel (α q : ℝ) (h : sin (2 * π / 3 - α) = q * sin α) : Real.sqrt 3 * cos α = (2 * q - 1) * sin α := by
  have e : 2 * π / 3 - α = π - (π / 3 + α) := by ring
  rw [e, sin_pi_sub, sin_add, sin_pi_div_three, cos_pi_div_three] at h
  linarith

theorem ivc_alpha_classify (α : ℝ) (q s : ℚ) (h0 : 0 < α) (h1 : α < 2 * π / 3) (hq : sin (2 * π / 3 - α) = (q : ℝ) * sin α)
    (hs : α = (s : ℝ) * π) : α = π / 6 ∨ α = π / 3 ∨ α = π / 2 := by
  have hrel := ivc_rel α q hq
  have hpi := Real.pi_pos
  have hsin : 0 < sin α := sin_pos_of_pos_of_lt_pi h0 (by linarith)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsq : sin α ^ 2 * (3 + ((2 * (q : ℝ) - 1)) ^ 2) = 3 := by
    have e : (Real.sqrt 3 * cos α) ^ 2 = ((2 * (q : ℝ) - 1) * sin α) ^ 2 := by rw [hrel]
    have hc : cos α ^ 2 = 1 - sin α ^ 2 := by nlinarith [sin_sq_add_cos_sq α]
    have : 3 * (1 - sin α ^ 2) = (2 * (q : ℝ) - 1) ^ 2 * sin α ^ 2 := by
      calc 3 * (1 - sin α ^ 2) = Real.sqrt 3 ^ 2 * cos α ^ 2 := by rw [h3, hc]
        _ = (Real.sqrt 3 * cos α) ^ 2 := by ring
        _ = _ := by rw [e]; ring
    nlinarith
  have hcos2 : ∃ r : ℚ, cos (2 * α) = r := by
    refine ⟨1 - 2 * (3 / (3 + (2 * q - 1) ^ 2)), ?_⟩
    have hpos : (0 : ℝ) < 3 + (2 * (q : ℝ) - 1) ^ 2 := by positivity
    have : sin α ^ 2 = 3 / (3 + (2 * (q : ℝ) - 1) ^ 2) := by
      field_simp; linarith
    rw [cos_two_mul, cos_sq', this]
    push_cast; ring
  -- 2 alpha in {pi/3, pi/2, 2pi/3, pi}
  have hmem : 2 * α = π / 3 ∨ 2 * α = π / 2 ∨ 2 * α = π * (2 / 3) ∨ 2 * α = π := by
    by_cases hle : 2 * α ≤ π
    · have hrat : ∃ r : ℚ, 2 * α = r * π := ⟨2 * s, by rw [hs]; push_cast; ring⟩
      have := niven_angle_eq hrat hcos2 ⟨by linarith, hle⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
      rcases this with h | h | h | h | h
      · exfalso; linarith
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    · exfalso
      push Not at hle
      have hrat : ∃ r : ℚ, 2 * π - 2 * α = r * π := ⟨2 - 2 * s, by rw [hs]; push_cast; ring⟩
      have hc : ∃ r : ℚ, cos (2 * π - 2 * α) = r := by
        obtain ⟨r, hr⟩ := hcos2
        exact ⟨r, by rw [cos_two_pi_sub]; exact hr⟩
      have := niven_angle_eq hrat hc ⟨by linarith, by linarith⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
      rcases this with h | h | h | h | h <;> linarith
  rcases hmem with h | h | h | h
  · exact Or.inl (by linarith)
  · exfalso
    have hα4 : α = π / 4 := by linarith
    have hc : cos α = Real.sqrt 2 / 2 := by rw [hα4]; exact cos_pi_div_four
    have hs4 : sin α = Real.sqrt 2 / 2 := by rw [hα4]; exact sin_pi_div_four
    rw [hc, hs4] at hrel
    have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
    have : Real.sqrt 3 = 2 * (q : ℝ) - 1 := by
      have : Real.sqrt 2 * (Real.sqrt 3 - (2 * (q : ℝ) - 1)) = 0 := by linarith
      rcases mul_eq_zero.mp this with h' | h'
      · linarith
      · linarith
    have hirr : Irrational (Real.sqrt 3) := Nat.prime_three.irrational_sqrt
    exact hirr ⟨2 * q - 1, by rw [this]; push_cast; ring⟩
  · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (by linarith))

/-- Witness: all three values satisfy the hypotheses (ratios `2`, `1`, `1/2`), so the classification is not vacuous. -/
theorem ivc_alpha_witness :
    (∃ q s : ℚ, sin (2 * π / 3 - π / 6) = (q : ℝ) * sin (π / 6) ∧ π / 6 = (s : ℝ) * π) ∧
    (∃ q s : ℚ, sin (2 * π / 3 - π / 3) = (q : ℝ) * sin (π / 3) ∧ π / 3 = (s : ℝ) * π) ∧
    (∃ q s : ℚ, sin (2 * π / 3 - π / 2) = (q : ℝ) * sin (π / 2) ∧ π / 2 = (s : ℝ) * π) := by
  refine ⟨⟨2, 1 / 6, ?_, by push_cast; ring⟩, ⟨1, 1 / 3, ?_, by push_cast; ring⟩, ⟨1 / 2, 1 / 2, ?_, by push_cast; ring⟩⟩
  · rw [show 2 * π / 3 - π / 6 = π / 2 by ring, sin_pi_div_two, sin_pi_div_six]; push_cast; ring
  · rw [show 2 * π / 3 - π / 3 = π / 3 by ring]; push_cast; ring
  · rw [show 2 * π / 3 - π / 2 = π / 6 by ring, sin_pi_div_two, sin_pi_div_six]; push_cast; ring

/-- Negative control: `alpha = pi/4` does not satisfy the commensurability hypothesis. -/
theorem ivc_alpha_pi4_control (q : ℚ) : sin (2 * π / 3 - π / 4) ≠ (q : ℝ) * sin (π / 4) := by
  intro h
  have := ivc_alpha_classify (π / 4) q (1 / 4) (by positivity) (by linarith [Real.pi_pos]) h (by push_cast; ring)
  have hpi := Real.pi_pos
  rcases this with h | h | h <;> linarith

end Erdos634.Draft.LaczFormal.Thm21

#print axioms Erdos634.Draft.LaczFormal.Thm21.ivc_alpha_classify
#print axioms Erdos634.Draft.LaczFormal.Thm21.ivc_alpha_witness
#print axioms Erdos634.Draft.LaczFormal.Thm21.ivc_alpha_pi4_control
