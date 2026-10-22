-- Draft/ISUMain.lean (task ISU, 2026-10-03).  NEW file.  Standard axioms; no sorry/native_decide.
-- thm:iso without the `N % 4 = 3`, `N > 3` and `IsoTP` restrictions of `ThmIsoFull.thmIso`:
-- any prime N, target any triangle with two equal sides (resp. angles) that is not equilateral,
-- tile with an angle 2pi/3 and the other angles alpha, pi/3-alpha, alpha not in Q*pi.
import Erdos634.Draft.ISUCore
import Erdos634.Draft.ISUReduce
import Erdos634.Draft.G3CIsoControl

open scoped Classical

namespace Erdos634.Draft.ISUMain

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.ISUReduce
  Erdos634.Draft.ISUCore Erdos634.Draft.LemmaCFinal

/-! ## Sides vs angles (isosceles by sides) -/

theorem sin_inj_aux (A B : ℝ) (hA : 0 < A) (hAB : A + B < Real.pi) (hlt : A < B)
    (h : Real.sin A = Real.sin B) : False := by
  by_cases hB : B ≤ Real.pi / 2
  · exact absurd h (Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) hB hlt).ne
  · push Not at hB
    have h1 : A < Real.pi - B := by linarith
    have h2 : Real.pi - B ≤ Real.pi / 2 := by linarith
    have := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) h2 h1
    rw [Real.sin_pi_sub] at this
    exact absurd h this.ne

theorem sin_inj (A B : ℝ) (hA : 0 < A) (hB : 0 < B) (hAB : A + B < Real.pi)
    (h : Real.sin A = Real.sin B) : A = B := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact sin_inj_aux A B hA hAB hlt h
  · exact sin_inj_aux B A hB (by linarith) hgt h.symm

/-- Equal opposite sides give equal angles. -/
theorem angleAt_eq_of_oppLen_eq (T : Tri) (i j : Fin 3) (hij : i ≠ j)
    (h : T.oppLen i = T.oppLen j) : T.angleAt i = T.angleAt j := by
  have hL : 0 < T.oppLen i := T.oppLen_pos i
  have hs := T.lawSin i j
  rw [← h] at hs
  have hsin : Real.sin (T.angleAt i) = Real.sin (T.angleAt j) :=
    mul_right_cancel₀ hL.ne' hs
  have h3 : ∀ i j : Fin 3, i ≠ j → ∃ k, k ≠ i ∧ k ≠ j := by decide
  obtain ⟨k, hki, hkj⟩ := h3 i j hij
  have hsum := sum3 (fun m => T.angleAt m) i j k hij (Ne.symm hki) (Ne.symm hkj)
  simp only at hsum
  rw [T.angleAt_sum] at hsum
  exact sin_inj _ _ (T.angleAt_pos' i) (T.angleAt_pos' j)
    (by linarith [T.angleAt_pos' k]) hsin

/-- Equilateral (all angles `pi/3`) gives all sides equal. -/
theorem oppLen_eq_of_equilateral {N : ℕ} (D : CongruentDissection N) (hE : Equilateral D) :
    ∀ i j : Fin 3, D.target.oppLen i = D.target.oppLen j := by
  intro i j
  have hs := D.target.lawSin i j
  have hi : D.target.angleAt i = Real.pi / 3 := hE i
  have hj : D.target.angleAt j = Real.pi / 3 := hE j
  rw [hi, hj] at hs
  have : 0 < Real.sin (Real.pi / 3) := by rw [Real.sin_pi_div_three]; positivity
  exact (mul_left_cancel₀ this.ne' hs).symm

/-! ## The theorem -/

/-- **thm:iso, unrestricted form (angle-isosceles).**  Any `N` that is prime; target with two equal
corner angles, not equilateral; tile `(alpha, pi/3-alpha, 2pi/3)`, `alpha` not in `Q*pi`.
No hypothesis `N % 4 = 3`, `N > 3`, and no `IsoTP` shape assumption. -/
theorem thmIso_unrestricted_angles {N : ℕ} (D : CongruentDissection N) (hN : N.Prime)
    {α a b c : ℝ} (hα : IrrPi α) (hm : D.model.TwoPiThreeData α a b c)
    (hiso : ∃ i j : Fin 3, i ≠ j ∧ D.target.angleAt i = D.target.angleAt j)
    (hne : ¬ Equilateral D) : False := by
  obtain ⟨α', a', b', c', hα', hm', hshape⟩ := iso_to_isoTP D hα hm hiso hne
  exact thmIsoCore N D hN α' a' b' c' hα' hm' hshape

/-- **thm:iso, unrestricted form (side-isosceles).**  Target has two equal sides and is not
equilateral (not all three sides equal). -/
theorem thmIso_unrestricted {N : ℕ} (D : CongruentDissection N) (hN : N.Prime)
    {α a b c : ℝ} (hα : IrrPi α) (hm : D.model.TwoPiThreeData α a b c)
    (hiso : ∃ i j : Fin 3, i ≠ j ∧ D.target.oppLen i = D.target.oppLen j)
    (hne : ¬ ∀ i j : Fin 3, D.target.oppLen i = D.target.oppLen j) : False := by
  obtain ⟨i, j, hij, h⟩ := hiso
  exact thmIso_unrestricted_angles D hN hα hm ⟨i, j, hij, angleAt_eq_of_oppLen_eq _ i j hij h⟩
    (fun hE => hne (oppLen_eq_of_equilateral D hE))

/-- Reformulated over all primes, with the tile phrased through `IrrPi`. -/
theorem thmIso_unrestricted_statement :
    ∀ (N : ℕ) (D : CongruentDissection N), N.Prime →
      ∀ α a b c : ℝ, IrrPi α → D.model.TwoPiThreeData α a b c →
        (∃ i j : Fin 3, i ≠ j ∧ D.target.oppLen i = D.target.oppLen j) →
        (¬ ∀ i j : Fin 3, D.target.oppLen i = D.target.oppLen j) → False :=
  fun _ D hN _ _ _ _ hα hm hiso hne => thmIso_unrestricted D hN hα hm hiso hne

/-! ## Controls: every non-primality hypothesis is satisfied by a real tiling; primality is needed -/

open Erdos634.Draft.G3CIsoControl in
/-- Witness for the geometric hypotheses (tile, `alpha` irrational, isosceles, non-equilateral)
on the certified 2673-tile tiling of the (21,21,33)*1890*9... isosceles triangle.
Everything except `N.Prime` holds; `2673 = 3^5 * 11`. -/
theorem control_hypotheses :
    IrrPi α ∧ D.model.TwoPiThreeData α (1890 * 3) (1890 * 5) (1890 * 7) ∧
    (∃ i j : Fin 3, i ≠ j ∧ D.target.oppLen i = D.target.oppLen j) ∧
    (¬ ∀ i j : Fin 3, D.target.oppLen i = D.target.oppLen j) := by
  refine ⟨α_irr, data, ⟨0, 1, by decide, by rw [t_opp0, t_opp1]⟩, ?_⟩
  intro h
  have := h 0 2
  rw [t_opp0, t_opp2] at this
  norm_num at this

open Erdos634.Draft.G3CIsoControl in
/-- Negative control: dropping primality refutes the statement. -/
theorem thmIso_unrestricted_primeFree_refuted :
    ¬ (∀ (N : ℕ) (D : CongruentDissection N) (α a b c : ℝ), IrrPi α →
        D.model.TwoPiThreeData α a b c →
        (∃ i j : Fin 3, i ≠ j ∧ D.target.oppLen i = D.target.oppLen j) →
        (¬ ∀ i j : Fin 3, D.target.oppLen i = D.target.oppLen j) → False) := by
  intro h
  obtain ⟨h1, h2, h3, h4⟩ := control_hypotheses
  exact h _ D α _ _ _ h1 h2 h3 h4

theorem control_N_not_prime : ¬ Nat.Prime 2673 := by norm_num

end Erdos634.Draft.ISUMain

#print axioms Erdos634.Draft.ISUMain.thmIso_unrestricted
#print axioms Erdos634.Draft.ISUMain.thmIso_unrestricted_angles
#print axioms Erdos634.Draft.ISUMain.thmIso_unrestricted_statement
#print axioms Erdos634.Draft.ISUMain.thmIso_unrestricted_primeFree_refuted
#print axioms Erdos634.Draft.ISUMain.angleAt_eq_of_oppLen_eq
