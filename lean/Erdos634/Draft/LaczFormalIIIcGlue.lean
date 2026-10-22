-- Draft/LaczFormalIIIcGlue.lean -- Laczkovich DCG 48 (2012), Thm 2.1, Case III (gamma = 2pi/3), subcase IIIc glued into the case split.
--   `caseIIIc_concl`   : regular PolyTiling, gamma = 2pi/3, a,b commensurable, c not commensurable with a  ==>  Thm21Concl  (no further hypothesis).
--      alpha/pi irrational: `iiic_final` (Concl1 or Concl6);  alpha/pi rational: Niven (`iiic_alpha_pi6`) gives alpha = beta = pi/6, hence Concl8 (angles from `polygon_angle_2pi3`, M <= 6 by angle sum).
--   `caseIII_reduce'`  : Case III reduced to the two subcases IIIa/IIIb ONLY (NotComb disjuncts; the printed Lemma 7.1 is not valid there, `LaczFormalRG3Gap`): the IIIc disjunct of `caseIII_reduce` is removed.
-- The model angles (alpha, pi/3 - alpha, 2pi/3) at vertices (0,1,2) are NOT a relabelling: they are `angleAt 0`, `angleAt 1 = pi/3 - angleAt 0` (angle sum, gamma = 2pi/3), `angleAt 2` (hypothesis).
-- NOTE, UNAUDITED.  Non-vacuity: the three hypotheses hold for the irrational-alpha parallelogram (named in `LaczFormalIIIcFinal`) and, with alpha = pi/6, for the (30,30,120) triangle tiling (a = b, c = sqrt 3 a).
-- Credit: Laczkovich (DCG 48 (2012), Sect. 7.3), Beeson, Beeson-Zhang, Niven (Mathlib).
import Erdos634.Draft.LaczFormalIIIcFinal
import Erdos634.Draft.LaczFormalIIIcAngle

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.Draft.LaczFormal.RG

namespace Erdos634.Draft.LaczFormal.IIIc

set_option maxHeartbeats 6400000 in
theorem caseIIIc_concl {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) (hγ : angleAt T.C.model 2 = 2 * Real.pi / 3)
    (hab : Comm (slen T.C 0) (slen T.C 1)) (hac : ¬ Comm (slen T.C 0) (slen T.C 2)) : Thm21Concl T.C T.P := by
  classical
  have hs : angleAt T.C.model 0 + angleAt T.C.model 1 + angleAt T.C.model 2 = Real.pi := Erdos634.Draft.LaczFormal.angleAt_sum T.C.model
  have hm1 : angleAt T.C.model 1 = Real.pi / 3 - angleAt T.C.model 0 := by rw [hγ] at hs; linarith
  by_cases hα : ∃ r : ℚ, angleAt T.C.model 0 = (r : ℝ) * Real.pi
  · -- rational alpha: Niven forces alpha = pi/6
    right; right; right; right; right; right; right; left
    obtain ⟨s, hs'⟩ := hα
    have hpi := Real.pi_pos
    have h0 : 0 < angleAt T.C.model 0 := T.C.model.angleAt_pos' 0
    have h1' : 0 < angleAt T.C.model 1 := T.C.model.angleAt_pos' 1
    have hqq : ∃ q : ℚ, Real.sin (angleAt T.C.model 1) = (q : ℝ) * Real.sin (angleAt T.C.model 0) := by
      obtain ⟨p, q, hp, hq, e⟩ := hab
      have hsr : Real.sin (angleAt T.C.model 0) / Real.sin (angleAt T.C.model 1) = slen T.C 0 / slen T.C 1 := sin_ratio_eq T.C
      have hsa : 0 < Real.sin (angleAt T.C.model 0) := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)
      have hsb : 0 < Real.sin (angleAt T.C.model 1) := Real.sin_pos_of_pos_of_lt_pi h1' (by linarith)
      have hb := RG.slen_pos T.C 1
      have hp' : (p : ℝ) ≠ 0 := by positivity
      have hq' : (q : ℝ) ≠ 0 := by
        have : (q : ℝ) * slen T.C 1 = (p : ℝ) * slen T.C 0 := by linarith
        have ha := RG.slen_pos T.C 0
        intro h0'; rw [h0'] at this; nlinarith [mul_pos (by positivity : (0:ℝ) < p) ha]
      have ha := RG.slen_pos T.C 0
      rw [div_eq_div_iff hsb.ne' hb.ne'] at hsr
      refine ⟨(p : ℚ) / (q : ℚ), ?_⟩
      push_cast
      rw [div_mul_eq_mul_div, eq_div_iff hq']
      apply mul_left_cancel₀ ha.ne'
      linear_combination (-(q : ℝ)) * hsr - (Real.sin (angleAt T.C.model 0)) * e
    obtain ⟨q, hq⟩ := hqq
    have h6 : angleAt T.C.model 0 = Real.pi / 6 := by
      apply iiic_alpha_pi6 _ q s h0 (by rw [hm1] at h1'; linarith) _ hs'
      rw [← hm1]; exact hq
    have h6' : angleAt T.C.model 1 = Real.pi / 6 := by rw [hm1, h6]; ring
    have hRat := polytiling_rational T hreg hab hac
    obtain ⟨idx, hA, hcnt⟩ := hreg
    haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
    have hαβ : T.C.model.angleAt 0 + T.C.model.angleAt 1 = Real.pi / 3 := by
      have h6a : T.C.model.angleAt 0 = Real.pi / 6 := h6
      have h6b : T.C.model.angleAt 1 = Real.pi / 6 := h6'
      rw [h6a, h6b]; ring
    have hall : ∀ i : Fin M, T.P.angle i = Real.pi / 3 ∨ T.P.angle i = 2 * Real.pi / 3 := by
      intro i
      have := polygon_angle_2pi3 T.C T.P T.region_eq idx hA hγ hαβ (fun X => hcnt X) (i - 1)
      rwa [sub_add_cancel] at this
    have hsum := poly_angle_sum T.P
    have hM3 : 3 ≤ M := T.P.three_le
    have hM6 : M ≤ 6 := by
      have hle1 : ∀ i, T.P.angle i ≤ 2 * Real.pi / 3 := fun i => by rcases hall i with h | h <;> rw [h] <;> linarith
      have hle : ∑ i, T.P.angle i ≤ ∑ _i : Fin M, 2 * Real.pi / 3 := Finset.sum_le_sum (fun i _ => hle1 i)
      rw [hsum] at hle
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
      rw [Nat.cast_sub (by omega)] at hle
      have : (M : ℝ) ≤ 6 := by
        by_contra hc
        push Not at hc
        push_cast at hle
        nlinarith
      exact_mod_cast this
    exact ⟨hRat, hM6, hall, h6, h6', hγ⟩
  · rcases iiic_final T hreg hα rfl hm1 hγ hab hac with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

/-- **Case III reduced to IIIa/IIIb.**  Either Theorem 2.1's conclusion holds, or `a` (resp. `b`) is not a nonnegative rational combination of the other two sides (the printed Lemma 7.1 is not valid
there: `LaczFormalRG3Gap`; these two subcases remain OPEN in Lean). -/
theorem caseIII_reduce' {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) (hγ : angleAt T.C.model 2 = 2 * Real.pi / 3) :
    Thm21Concl T.C T.P ∨ NotComb (slen T.C 0) (slen T.C 1) (slen T.C 2) ∨ NotComb (slen T.C 1) (slen T.C 0) (slen T.C 2) := by
  rcases caseIII_reduce T hreg hγ with h | h | h | ⟨hab, hac⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact Or.inl (caseIIIc_concl T hreg hγ hab hac)

end Erdos634.Draft.LaczFormal.IIIc

#print axioms Erdos634.Draft.LaczFormal.IIIc.caseIIIc_concl
#print axioms Erdos634.Draft.LaczFormal.IIIc.caseIII_reduce'
