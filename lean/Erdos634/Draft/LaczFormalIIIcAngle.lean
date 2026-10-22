-- Draft/LaczFormalIIIcAngle.lean -- Laczkovich DCG 48 (2012), Sect. 7.3 (Subcase IIIc), first display: if `a, b` are commensurable (`b/a = sin beta / sin alpha` rational, `beta = pi/3 - alpha`)
-- and `alpha` is a rational multiple of `pi`, then `alpha = pi/6`.  Pure real statement; Niven's theorem from Mathlib.
--   `iiic_alpha_pi6`    : 0 < alpha < pi/3, sin(pi/3 - alpha) = q * sin alpha (q rational), alpha = s * pi (s rational)  ==>  alpha = pi/6.
--   `iiic_alpha_witness`: the hypotheses are satisfied (alpha = pi/6, q = 1, s = 1/6), so the theorem is not vacuous.
--   `iiic_alpha_pi4_control`: negative control: alpha = pi/4 does NOT satisfy the hypotheses (the ratio sin(pi/12)/sin(pi/4) is not rational; the proof uses sqrt 3 irrational).
-- Used for: IIIc (M >= 4, not a parallelogram): either (viii) (alpha = pi/6) or alpha/pi irrational, which is what the chi / Phi argument (Lemma 7.2, `lemma72_*`) needs.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 7.3), Beeson, Beeson-Zhang, Niven (Mathlib `Real.niven_angle_eq`).
import Mathlib.NumberTheory.Niven
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Erdos634.Draft.LaczFormal.Thm21

open Real

/-- `sqrt 3 * cos alpha = (2q+1) * sin alpha` from `sin (pi/3 - alpha) = q sin alpha`. -/
theorem iiic_rel (α q : ℝ) (h : sin (π / 3 - α) = q * sin α) : Real.sqrt 3 * cos α = (2 * q + 1) * sin α := by
  rw [sin_sub, sin_pi_div_three, cos_pi_div_three] at h
  linarith

/-- **Subcase IIIc, first display**: commensurable `a, b` and `alpha` a rational multiple of `pi` force `alpha = pi/6`. -/
theorem iiic_alpha_pi6 (α : ℝ) (q s : ℚ) (h0 : 0 < α) (h1 : α < π / 3) (hq : sin (π / 3 - α) = (q : ℝ) * sin α)
    (hs : α = (s : ℝ) * π) : α = π / 6 := by
  have hrel := iiic_rel α q hq
  have hpi := Real.pi_pos
  have hsin : 0 < sin α := sin_pos_of_pos_of_lt_pi h0 (by linarith)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  -- sin^2 alpha = 3 / (3 + (2q+1)^2)
  have hsq : sin α ^ 2 * (3 + ((2 * (q : ℝ) + 1)) ^ 2) = 3 := by
    have e : (Real.sqrt 3 * cos α) ^ 2 = ((2 * (q : ℝ) + 1) * sin α) ^ 2 := by rw [hrel]
    have hc : cos α ^ 2 = 1 - sin α ^ 2 := by nlinarith [sin_sq_add_cos_sq α]
    have : 3 * (1 - sin α ^ 2) = (2 * (q : ℝ) + 1) ^ 2 * sin α ^ 2 := by
      calc 3 * (1 - sin α ^ 2) = Real.sqrt 3 ^ 2 * cos α ^ 2 := by rw [h3, hc]
        _ = (Real.sqrt 3 * cos α) ^ 2 := by ring
        _ = _ := by rw [e]; ring
    nlinarith
  have hcos2 : ∃ r : ℚ, cos (2 * α) = r := by
    refine ⟨1 - 2 * (3 / (3 + (2 * q + 1) ^ 2)), ?_⟩
    have hpos : (0 : ℝ) < 3 + (2 * (q : ℝ) + 1) ^ 2 := by positivity
    have : sin α ^ 2 = 3 / (3 + (2 * (q : ℝ) + 1) ^ 2) := by
      field_simp; linarith
    rw [cos_two_mul, cos_sq', this]
    push_cast; ring
  have hrat : ∃ r : ℚ, 2 * α = r * π := ⟨2 * s, by rw [hs]; push_cast; ring⟩
  have hmem := niven_angle_eq hrat hcos2 ⟨by linarith, by linarith⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h | h | h
  · linarith
  · linarith
  · exfalso
    have hα4 : α = π / 4 := by linarith
    have hc : cos α = Real.sqrt 2 / 2 := by rw [hα4]; exact cos_pi_div_four
    have hs4 : sin α = Real.sqrt 2 / 2 := by rw [hα4]; exact sin_pi_div_four
    rw [hc, hs4] at hrel
    have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
    have : Real.sqrt 3 = 2 * (q : ℝ) + 1 := by
      have : Real.sqrt 2 * (Real.sqrt 3 - (2 * (q : ℝ) + 1)) = 0 := by linarith
      rcases mul_eq_zero.mp this with h' | h'
      · linarith
      · linarith
    have hirr : Irrational (Real.sqrt 3) := Nat.prime_three.irrational_sqrt
    exact hirr ⟨2 * q + 1, by rw [this]; push_cast; ring⟩
  · linarith
  · linarith

/-- Witness: the hypotheses of `iiic_alpha_pi6` are satisfiable (alpha = pi/6, q = 1, s = 1/6), so the theorem is not vacuous. -/
theorem iiic_alpha_witness : ∃ α : ℝ, ∃ q s : ℚ, 0 < α ∧ α < π / 3 ∧ sin (π / 3 - α) = (q : ℝ) * sin α ∧ α = (s : ℝ) * π := by
  refine ⟨π / 6, 1, 1 / 6, by positivity, by linarith [Real.pi_pos], ?_, by push_cast; ring⟩
  have : π / 3 - π / 6 = π / 6 := by ring
  rw [this]; push_cast; ring

/-- Negative control: `alpha = pi/4` (a rational multiple of `pi`, different from `pi/6`) does not satisfy the commensurability hypothesis. -/
theorem iiic_alpha_pi4_control (q : ℚ) : sin (π / 3 - π / 4) ≠ (q : ℝ) * sin (π / 4) := by
  intro h
  have := iiic_alpha_pi6 (π / 4) q (1 / 4) (by positivity) (by linarith [Real.pi_pos]) h (by push_cast; ring)
  linarith [Real.pi_pos]

end Erdos634.Draft.LaczFormal.Thm21

#print axioms Erdos634.Draft.LaczFormal.Thm21.iiic_alpha_pi6
#print axioms Erdos634.Draft.LaczFormal.Thm21.iiic_alpha_witness
#print axioms Erdos634.Draft.LaczFormal.Thm21.iiic_alpha_pi4_control
