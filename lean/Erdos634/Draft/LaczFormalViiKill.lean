-- Draft/LaczFormalViiKill.lean -- the three cases (vii) of Laczkovich 1995 Thm 5.1 for CONGRUENT tiles (Thm 5.3, "similar arguments", p. 94):
-- no congruent dissection of the isosceles right triangle has tiles with angles  (1,2,5)π/8,  (3,4,5)π/12  or  (1,3,8)π/12.
-- Method (as in tails (iv),(v) and case (vi)): leg word, hypotenuse word and area identity of `iso_right_extract`, then exact arithmetic
-- (`LaczFormalViiArith`).  UNAUDITED.  Credit: Laczkovich (1995).
import Erdos634.Draft.LaczFormalVii
import Erdos634.Draft.LaczFormalViiArith

open scoped Classical

namespace Erdos634.Draft.LaczFormal

open Real Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional

theorem TileAngles.of_eq {N : ℕ} {D : CongruentDissection N} {x y z x' y' z' : ℝ}
    (h : TileAngles D x y z) (hx : x = x') (hy : y = y') (hz : z = z') : TileAngles D x' y' z' := by
  subst hx hy hz; exact h

theorem tgt_of_eq {N : ℕ} {D : CongruentDissection N} {x y z x' y' z' : ℝ}
    (h : TgtAngles D x y z) (hx : x = x') (hy : y = y') (hz : z = z') : TgtAngles D x' y' z' := by
  subst hx hy hz; exact h

/-- **Case (vii), `n = 8`.**  No congruent dissection of a `(2,2,4)π/8` triangle has tile angles `(1,2,5)π/8`. -/
theorem case_vii_8 {N : ℕ} (D : CongruentDissection N)
    (hM : TileAngles D (1 * π / 8) (2 * π / 8) (5 * π / 8))
    (hT : TgtAngles D (2 * π / 8) (2 * π / 8) (4 * π / 8)) : False := by
  have hpi := Real.pi_pos
  have s2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hb : 0 < Real.sin (π / 8) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  have hb2 : Real.sin (π / 8) ^ 2 = (2 - Real.sqrt 2) / 4 := by
    have h1 := Real.sin_sq_add_cos_sq (π / 8)
    have h2 : Real.cos (π / 8) ^ 2 = 1 / 2 + Real.cos (2 * (π / 8)) / 2 := Real.cos_sq _
    rw [show 2 * (π / 8) = π / 4 by ring, Real.cos_pi_div_four] at h2
    nlinarith
  have hsy : Real.sin (2 * π / 8) = Real.sqrt 2 / 2 := by
    rw [show 2 * π / 8 = π / 4 by ring]; exact Real.sin_pi_div_four
  have hsz : Real.sin (5 * π / 8) = (1 + Real.sqrt 2) * Real.sin (π / 8) := by
    have hc : Real.sin (5 * π / 8) = Real.cos (π / 8) := by
      rw [show 5 * π / 8 = π / 8 + π / 2 by ring, Real.sin_add_pi_div_two]
    have h3 : Real.sin (2 * (π / 8)) = 2 * Real.sin (π / 8) * Real.cos (π / 8) := Real.sin_two_mul _
    rw [show 2 * (π / 8) = π / 4 by ring, Real.sin_pi_div_four] at h3
    rw [hc]
    apply mul_left_cancel₀ hb.ne'
    nlinarith
  have hM' : TileAngles D (π / 8) (2 * π / 8) (5 * π / 8) := hM.of_eq (by ring) rfl rfl
  have hT' : TgtAngles D (π / 4) (π / 4) (π / 2) := tgt_of_eq hT (by ring) (by ring) (by ring)
  obtain ⟨ρ, X, Z, hρ, hN, e1, e2, e3⟩ := iso_right_extract D hM' hT' (by simpa using hb)
  rw [hsy, hsz] at e1 e2 e3
  exact vii8_arith (ρ := ρ) (b := Real.sin (π / 8)) hN hρ hb hb2 e1 e2 e3

/-- **Case (vii), `n = 12`, `(3,4,5)`.** -/
theorem case_vii_12_345 {N : ℕ} (D : CongruentDissection N)
    (hM : TileAngles D (3 * π / 12) (4 * π / 12) (5 * π / 12))
    (hT : TgtAngles D (3 * π / 12) (3 * π / 12) (6 * π / 12)) : False := by
  have hpi := Real.pi_pos
  have hs6 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have hx : Real.sin (3 * π / 12) = Real.sqrt 2 / 2 := by
    rw [show 3 * π / 12 = π / 4 by ring]; exact Real.sin_pi_div_four
  have hy : Real.sin (4 * π / 12) = Real.sqrt 3 / 2 := by
    rw [show 4 * π / 12 = π / 3 by ring]; exact Real.sin_pi_div_three
  have hz : Real.sin (5 * π / 12) = (Real.sqrt 6 + Real.sqrt 2) / 4 := by
    rw [show 5 * π / 12 = π / 4 + π / 6 by ring, Real.sin_add, Real.sin_pi_div_four, Real.cos_pi_div_four,
      Real.cos_pi_div_six, Real.sin_pi_div_six, hs6]
    ring
  have hM' : TileAngles D (3 * π / 12) (4 * π / 12) (5 * π / 12) := hM
  have hT' : TgtAngles D (π / 4) (π / 4) (π / 2) := tgt_of_eq hT (by ring) (by ring) (by ring)
  have hsx : 0 < Real.sin (3 * π / 12) := by rw [hx]; positivity
  obtain ⟨ρ, X, Z, hρ, hN, e1, e2, e3⟩ := iso_right_extract D hM' hT' hsx
  rw [hx, hy, hz] at e1 e2
  exact vii12a_arith hρ e1 e2

/-- **Case (vii), `n = 12`, `(1,3,8)`.** -/
theorem case_vii_12_138 {N : ℕ} (D : CongruentDissection N)
    (hM : TileAngles D (1 * π / 12) (3 * π / 12) (8 * π / 12))
    (hT : TgtAngles D (3 * π / 12) (3 * π / 12) (6 * π / 12)) : False := by
  have hpi := Real.pi_pos
  have hs6 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have hx : Real.sin (1 * π / 12) = (Real.sqrt 6 - Real.sqrt 2) / 4 := by
    rw [show 1 * π / 12 = π / 3 - π / 4 by ring, Real.sin_sub, Real.sin_pi_div_three, Real.cos_pi_div_four,
      Real.cos_pi_div_three, Real.sin_pi_div_four, hs6]
    ring
  have hy : Real.sin (3 * π / 12) = Real.sqrt 2 / 2 := by
    rw [show 3 * π / 12 = π / 4 by ring]; exact Real.sin_pi_div_four
  have hz : Real.sin (8 * π / 12) = Real.sqrt 3 / 2 := by
    rw [show 8 * π / 12 = π - π / 3 by ring, Real.sin_pi_sub]; exact Real.sin_pi_div_three
  have hT' : TgtAngles D (π / 4) (π / 4) (π / 2) := tgt_of_eq hT (by ring) (by ring) (by ring)
  have hsx : 0 < Real.sin (1 * π / 12) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  obtain ⟨ρ, X, Z, hρ, hN, e1, e2, e3⟩ := iso_right_extract D hM hT' hsx
  rw [hx, hy, hz] at e1 e2 e3
  exact vii12b_arith (N := N) hN hρ e1 e2 e3

/-- Each hypothesis of the three (vii) theorems is satisfiable on its own: the isosceles right triangle is dissected by its own ladder (`N = 4`),
and each of the three tile shapes dissects a similar triangle (ladder).  The (vii) theorems say the hypotheses are incompatible. -/
theorem case_vii_hyps_individually :
    (∃ (N : ℕ) (D : CongruentDissection N), TgtAngles D (2 * π / 8) (2 * π / 8) (4 * π / 8) ∧
        TileAngles D (2 * π / 8) (2 * π / 8) (4 * π / 8)) ∧
    (∃ (N : ℕ) (D : CongruentDissection N), TileAngles D (1 * π / 8) (2 * π / 8) (5 * π / 8)) ∧
    (∃ (N : ℕ) (D : CongruentDissection N), TileAngles D (3 * π / 12) (4 * π / 12) (5 * π / 12)) ∧
    (∃ (N : ℕ) (D : CongruentDissection N), TileAngles D (1 * π / 12) (3 * π / 12) (8 * π / 12)) := by
  have hpi := Real.pi_pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨N, D, hm, ht⟩ := ladder_with_angles (α := 2 * π / 8) (β := 2 * π / 8) (by positivity) (by positivity) (by linarith)
    exact ⟨N, D, tgt_of_eq ht rfl rfl (by ring), hm.of_eq rfl rfl (by ring)⟩
  · obtain ⟨N, D, hm, -⟩ := ladder_with_angles (α := 1 * π / 8) (β := 2 * π / 8) (by positivity) (by positivity) (by linarith)
    exact ⟨N, D, hm.of_eq rfl rfl (by ring)⟩
  · obtain ⟨N, D, hm, -⟩ := ladder_with_angles (α := 3 * π / 12) (β := 4 * π / 12) (by positivity) (by positivity) (by linarith)
    exact ⟨N, D, hm.of_eq rfl rfl (by ring)⟩
  · obtain ⟨N, D, hm, -⟩ := ladder_with_angles (α := 1 * π / 12) (β := 3 * π / 12) (by positivity) (by positivity) (by linarith)
    exact ⟨N, D, hm.of_eq rfl rfl (by ring)⟩

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.case_vii_8
#print axioms Erdos634.Draft.LaczFormal.case_vii_12_345
#print axioms Erdos634.Draft.LaczFormal.case_vii_12_138
