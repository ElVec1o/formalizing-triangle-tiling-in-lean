-- Draft/LaczFormalThm21Partial3.lean -- **Laczkovich (DCG 48 (2012)) Theorem 2.1: PARTIAL assembly, version 3.**  NOT `Theorem21`.
-- Glue of the IVc irrational branch (`IIIc.ivc_final_ge5`, M >= 5) into the case split:
--   `caseIVc_concl`      : gamma = pi/3, a,b commensurable, c not commensurable with a, M >= 5, alpha/pi irrational  ==>  Thm21Concl (Concl6).
--   `ivc_rat_alpha`      : same data with alpha/pi rational  ==>  alpha = pi/6 or alpha = pi/2  (alpha = pi/3 excluded: it gives c = a).  (a = 2b or b = 2a by `Thm21.ivc_rat_tile`.)
--   `Thm21Excluded3`     : what is left = IIc  or  IVc-rational (gamma = pi/3, Comm a b, not Comm a c, M >= 5, alpha/pi rational).
--   `thm21_partial3`, `theorem21_of_cases3`.
-- NOTE, UNAUDITED.  `Theorem21` is NOT claimed.  Non-vacuity: the hypotheses of `ivc_rat_alpha` are satisfiable for M <= 4 only by examples we have (30-60-90 parallelogram,
-- `caseIVc_small_witness`); no tiling with M >= 5 and these data is exhibited (printed (vi): hexagon possible, not constructed here), so for M >= 5 the branch is named-vacuous-or-open, not witnessed.
-- `Thm21Excluded3` satisfiable-by-hypothesis only (arithmetic witness `ivc_rat_witness`).
-- Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Zhang, Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalThm21Partial2
import Erdos634.Draft.LaczFormalIVcFinal
import Erdos634.Draft.LaczFormalIVcRat

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.Draft.LaczFormal.RG

namespace Erdos634.Draft.LaczFormal.RG

theorem caseIVc_concl {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) (hγ : angleAt T.C.model 2 = Real.pi / 3)
    (hab : Comm (slen T.C 0) (slen T.C 1)) (hac : ¬ Comm (slen T.C 0) (slen T.C 2)) (hM5 : 5 ≤ M)
    (hα : ¬ ∃ r : ℚ, angleAt T.C.model 0 = (r : ℝ) * Real.pi) : Thm21Concl T.C T.P := by
  have hsum : angleAt T.C.model 0 + angleAt T.C.model 1 + angleAt T.C.model 2 = Real.pi := Erdos634.Draft.LaczFormal.angleAt_sum T.C.model
  have hm1 : angleAt T.C.model 1 = 2 * Real.pi / 3 - angleAt T.C.model 0 := by
    linarith
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    (Erdos634.Draft.LaczFormal.IIIc.ivc_final_ge5 T hreg hα rfl hm1 hγ hab hac hM5))))))

theorem ivc_rat_alpha {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hγ : angleAt T.C.model 2 = Real.pi / 3)
    (hab : Comm (slen T.C 0) (slen T.C 1)) (hac : ¬ Comm (slen T.C 0) (slen T.C 2))
    (hα : ∃ s : ℚ, angleAt T.C.model 0 = (s : ℝ) * Real.pi) :
    angleAt T.C.model 0 = Real.pi / 6 ∨ angleAt T.C.model 0 = Real.pi / 2 := by
  obtain ⟨s, hs⟩ := hα
  have hpi := Real.pi_pos
  have hsum : angleAt T.C.model 0 + angleAt T.C.model 1 + angleAt T.C.model 2 = Real.pi := Erdos634.Draft.LaczFormal.angleAt_sum T.C.model
  have hγ' := hγ
  have p0 : 0 < angleAt T.C.model 0 := model_angle_pos' T.C 0
  have p1 : 0 < angleAt T.C.model 1 := model_angle_pos' T.C 1
  obtain ⟨h1, h2⟩ := slen_sin_rel' T.C
  have h1 : Real.sin (angleAt T.C.model 1) * slen T.C 0 = Real.sin (angleAt T.C.model 0) * slen T.C 1 := h1
  have h2 : Real.sin (angleAt T.C.model 0) * slen T.C 2 = Real.sin (angleAt T.C.model 2) * slen T.C 0 := h2
  have ha := slen_pos T.C 0
  have hb := slen_pos T.C 1
  obtain ⟨p, q, hp, hq, e⟩ := hab
  have hm1 : angleAt T.C.model 1 = 2 * Real.pi / 3 - angleAt T.C.model 0 := by
    linarith
  have hq' : Real.sin (2 * Real.pi / 3 - angleAt T.C.model 0) = (((p : ℚ) / (q : ℚ) : ℚ) : ℝ) * Real.sin (angleAt T.C.model 0) := by
    rw [← hm1]
    have hq0 : (q : ℝ) ≠ 0 := by positivity
    push_cast
    have h1' := h1
    have hb' : slen T.C 1 = (p : ℝ) / q * slen T.C 0 := by field_simp; linarith
    rw [hb'] at h1'
    have : (Real.sin (angleAt T.C.model 1) - (p : ℝ) / q * Real.sin (angleAt T.C.model 0)) * slen T.C 0 = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  have hcl := ivc_alpha_classify (angleAt T.C.model 0) _ s p0 (by linarith) hq' hs
  rcases hcl with h | h | h
  · exact Or.inl h
  · exfalso
    apply hac
    have h2' := h2
    rw [h, hγ'] at h2'
    have hs3 : 0 < Real.sin (Real.pi / 3) := by rw [Real.sin_pi_div_three]; positivity
    refine ⟨1, 1, one_pos, one_pos, ?_⟩
    simp only [Nat.cast_one]
    have : Real.sin (Real.pi / 3) * (slen T.C 2 - slen T.C 0) = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · linarith
    · linarith
  · exact Or.inr h

/-- What remains of Theorem 2.1 after IIIa, IIIb and the IVc irrational branch: IIc, and IVc with `alpha/pi` rational and `M >= 5`. -/
def Thm21Excluded3 {N M : ℕ} [NeZero M] (T : PolyTiling N M) : Prop :=
  (angleAt T.C.model 2 < Real.pi / 2 ∧ angleAt T.C.model 2 ≠ Real.pi / 3 ∧ Comm (slen T.C 0) (slen T.C 1) ∧ ¬ Comm (slen T.C 0) (slen T.C 2)) ∨
  (angleAt T.C.model 2 = Real.pi / 3 ∧ Comm (slen T.C 0) (slen T.C 1) ∧ ¬ Comm (slen T.C 0) (slen T.C 2) ∧ 5 ≤ M ∧
    ∃ s : ℚ, angleAt T.C.model 0 = (s : ℝ) * Real.pi)

theorem thm21_partial3 {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) (hex : ¬ Thm21Excluded3 T) : Thm21Concl T.C T.P := by
  by_cases h : Thm21Excluded2 T
  · rcases h with h | ⟨hγ, hab, hac, hM⟩
    · exact absurd (Or.inl h) hex
    · by_cases hs : ∃ s : ℚ, angleAt T.C.model 0 = (s : ℝ) * Real.pi
      · exact absurd (Or.inr ⟨hγ, hab, hac, hM, hs⟩) hex
      · exact caseIVc_concl T hreg hγ hab hac hM hs
  · exact thm21_partial2 T hreg h

theorem theorem21_of_cases3
    (h : ∀ (N M : ℕ) [NeZero M] (T : PolyTiling N M), RegularPQ T.C → Thm21Excluded3 T → Thm21Concl T.C T.P) : Theorem21 :=
  fun N M _ T hreg => by
    by_cases hx : Thm21Excluded3 T
    · exact h N M T hreg hx
    · exact thm21_partial3 T hreg hx

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.caseIVc_concl
#print axioms Erdos634.Draft.LaczFormal.RG.ivc_rat_alpha
#print axioms Erdos634.Draft.LaczFormal.RG.thm21_partial3
#print axioms Erdos634.Draft.LaczFormal.RG.theorem21_of_cases3
