-- Draft/LaczFormalIVcRat.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc), rational branch, tile-data step.
--   Printed: alpha/pi rational => alpha in {pi/6, pi/2} (alpha = pi/3 gives a = b = c, contradicting 'c/a irrational'); by the
--   symmetry alpha <-> beta take alpha = pi/2, beta = pi/6, then a = 2b (c = sqrt 3 * b).  This file proves exactly that arithmetic.
--   Hypotheses: law of sines for (alpha, 2pi/3 - alpha, pi/3) with opposite sides (a, b, c); a > 0; c not a rational multiple of a.
--   `ivc_rat_tile`      : alpha in {pi/6, pi/3, pi/2}, law of sines, c not a rational multiple of a  ==>  (alpha = pi/2, a = 2b, c = sqrt 3 b) or (alpha = pi/6, b = 2a, c = sqrt 3 a).
--   `ivc_rat_witness`   : the (alpha = pi/2) hypotheses are satisfied by (a, b, c) = (2, 1, sqrt 3)  (c/a = sqrt3/2 irrational); non-vacuous.
--   `ivc_rat_pi3_control`: alpha = pi/3 is excluded (a = b = c would make c = 1 * a).
-- NOT formalized (named, hand proof in (private working notes, not included) 2026-10-22): the printed gap at 'U1 cannot be the vertex of a triangle Q1 ... V(Q1) or W(Q1) would be a point of XY'.
--   Hand proof: R1 has angle pi/3 at X, so 2pi/3 at U1 (adjacent angles of a parallelogram along XU1); the remaining angle at U1 is pi/3, and a regular
--   triangle Q1 at U1 fills it, so one side U1U1' of Q1 lies along XY, with U1' in XY (convexity). If U1 = V(Q1) it is on bd A (V is interior); else U1 lies on
--   the side opposite V; either that side lies on XY (W in XY) or V is U1' in XY. Both contradict V, W interior.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcAngle

namespace Erdos634.Draft.LaczFormal.Thm21

open Real

private theorem s3 : (0 : ℝ) < Real.sqrt 3 := by positivity

theorem ivc_rat_tile (α a b c : ℝ) (ha : 0 < a) (hα : α = π / 6 ∨ α = π / 3 ∨ α = π / 2)
    (hb : a * sin (2 * π / 3 - α) = b * sin α) (hc : a * sin (π / 3) = c * sin α)
    (hirr : ¬ ∃ r : ℚ, c = (r : ℝ) * a) :
    (α = π / 2 ∧ a = 2 * b ∧ c = Real.sqrt 3 * b) ∨ (α = π / 6 ∧ b = 2 * a ∧ c = Real.sqrt 3 * a) := by
  rcases hα with h | h | h
  · right
    refine ⟨h, ?_, ?_⟩
    · rw [h, show 2 * π / 3 - π / 6 = π / 2 by ring, sin_pi_div_two, sin_pi_div_six] at hb; linarith
    · rw [h, sin_pi_div_three, sin_pi_div_six] at hc; linarith
  · exfalso
    apply hirr
    rw [h, show 2 * π / 3 - π / 3 = π / 3 by ring] at hb
    rw [h] at hc
    have hs : 0 < sin (π / 3) := by rw [sin_pi_div_three]; positivity
    refine ⟨1, ?_⟩
    push_cast
    have : (c - a) * sin (π / 3) = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · linarith
    · linarith
  · left
    refine ⟨h, ?_, ?_⟩
    · rw [h, show 2 * π / 3 - π / 2 = π / 6 by ring, sin_pi_div_two, sin_pi_div_six] at hb; linarith
    · rw [h, sin_pi_div_three, sin_pi_div_two] at hc
      have : a = 2 * b := by
        rw [h, show 2 * π / 3 - π / 2 = π / 6 by ring, sin_pi_div_two, sin_pi_div_six] at hb; linarith
      rw [this] at hc; linarith

theorem ivc_rat_witness :
    (π / 2 = π / 6 ∨ π / 2 = π / 3 ∨ π / 2 = π / 2) ∧ (2 : ℝ) * sin (2 * π / 3 - π / 2) = 1 * sin (π / 2) ∧
    (2 : ℝ) * sin (π / 3) = Real.sqrt 3 * sin (π / 2) ∧ ¬ ∃ r : ℚ, Real.sqrt 3 = (r : ℝ) * 2 := by
  refine ⟨Or.inr (Or.inr rfl), ?_, ?_, ?_⟩
  · rw [show 2 * π / 3 - π / 2 = π / 6 by ring, sin_pi_div_two, sin_pi_div_six]; ring
  · rw [sin_pi_div_three, sin_pi_div_two]; ring
  · rintro ⟨r, hr⟩
    exact Nat.prime_three.irrational_sqrt ⟨r * 2, by push_cast; linarith⟩

/-- Negative control: with alpha = pi/3 the hypothesis 'c not a rational multiple of a' is contradictory. -/
theorem ivc_rat_pi3_control (a b c : ℝ) (ha : 0 < a)
    (hb : a * sin (2 * π / 3 - π / 3) = b * sin (π / 3)) (hc : a * sin (π / 3) = c * sin (π / 3)) :
    ∃ r : ℚ, c = (r : ℝ) * a := by
  by_contra hn
  have hpi := Real.pi_pos
  rcases ivc_rat_tile (π / 3) a b c ha (Or.inr (Or.inl rfl)) hb hc hn with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith

end Erdos634.Draft.LaczFormal.Thm21

#print axioms Erdos634.Draft.LaczFormal.Thm21.ivc_rat_tile
#print axioms Erdos634.Draft.LaczFormal.Thm21.ivc_rat_witness
#print axioms Erdos634.Draft.LaczFormal.Thm21.ivc_rat_pi3_control
