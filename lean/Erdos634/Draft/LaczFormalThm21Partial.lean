-- Draft/LaczFormalThm21Partial.lean -- **Laczkovich (DCG 48 (2012)) Theorem 2.1: the PARTIAL assembly.**  NOT `Theorem21`.
-- `Thm21Excluded T` names the four classes of regular polygon tilings whose case is not yet in Lean:
--   IIc  (gamma < pi/2, != pi/3; a,b commensurable, a,c not),      IIIa (gamma = 2pi/3, a not a combination of b,c),
--   IIIb (gamma = 2pi/3, b not a combination of a,c),               IVc5 (gamma = pi/3; a,b commensurable, a,c not; M >= 5).
-- `thm21_partial`: for every regular tiling outside these classes, one of (i)-(ix) holds (unconditional on the rest).
-- `theorem21_of_cases`: the conditional form: the four missing case statements (as explicit hypotheses) imply `Theorem21`.
-- NOTE, UNAUDITED.  The printed Lemma 7.1(i) used for IIIa/IIIb is FALSE at 3a+3b=pi (`printed_L71_330_false`), so hIIIa/hIIIb are not known provable by the printed route.
-- Credit: Laczkovich (DCG 48 (2012)), Zhang, Beeson, Beeson-Zhang.
import Erdos634.Draft.AllLaczThm21
import Erdos634.Draft.LaczFormalRG11IIb

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

/-- The four classes still missing from the Lean proof of Theorem 2.1. -/
def Thm21Excluded {N M : ℕ} [NeZero M] (T : PolyTiling N M) : Prop :=
  (angleAt T.C.model 2 < Real.pi / 2 ∧ angleAt T.C.model 2 ≠ Real.pi / 3 ∧ Comm (slen T.C 0) (slen T.C 1) ∧ ¬ Comm (slen T.C 0) (slen T.C 2)) ∨
  (angleAt T.C.model 2 = 2 * Real.pi / 3 ∧ NotComb (slen T.C 0) (slen T.C 1) (slen T.C 2)) ∨
  (angleAt T.C.model 2 = 2 * Real.pi / 3 ∧ NotComb (slen T.C 1) (slen T.C 0) (slen T.C 2)) ∨
  (angleAt T.C.model 2 = Real.pi / 3 ∧ Comm (slen T.C 0) (slen T.C 1) ∧ ¬ Comm (slen T.C 0) (slen T.C 2) ∧ 5 ≤ M)

/-- **Theorem 2.1 outside the excluded classes** (UNAUDITED; NOT the full theorem). -/
theorem thm21_partial {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) (hex : ¬ Thm21Excluded T) : Thm21Concl T.C T.P := by
  classical
  unfold Thm21Excluded at hex
  push Not at hex
  obtain ⟨e1, e2, e3, e4⟩ := hex
  have hγ0 := model_angle_pos' T.C 2
  have hγπ := model_gamma_lt_pi T.C
  rcases lt_trichotomy (angleAt T.C.model 2) (Real.pi / 2) with hlt | heq | hgt
  · -- Case II
    by_cases h3 : angleAt T.C.model 2 = Real.pi / 3
    · -- Case IV
      rcases caseIV_reduce T hreg h3 with h | ⟨hab, hac⟩
      · exact h
      · by_cases hM : M ≤ 4
        · exact Or.inl (caseIVc_small T hreg h3 hab hac hM)
        · have := e4 h3 hab hac; omega
    · by_cases hA : NotComb (slen T.C 0) (slen T.C 1) (slen T.C 2)
      · exact Or.inl (caseII_a T hreg hlt h3 hA)
      by_cases hB : NotComb (slen T.C 1) (slen T.C 0) (slen T.C 2)
      · exact Or.inl (caseII_b_small T hreg hlt h3 hB)
      unfold NotComb at hA hB
      push Not at hA hB
      obtain ⟨r, p, q, hr, f1⟩ := hA
      obtain ⟨r', p', q', hr', f2⟩ := hB
      have hcomm : Comm (slen T.C 0) (slen T.C 1) := comm_of_two_combs (slen_pos T.C 0) (slen_pos T.C 1) hr f1 hr' f2
      by_cases hc : Comm (slen T.C 0) (slen T.C 2)
      · exact Or.inr (Or.inr (Or.inl (caseII_b T hreg hlt h3 hcomm hc)))
      · exact absurd (e1 hlt h3 hcomm) hc
  · exact Or.inl (thm21_V N M T hreg heq)
  · by_cases h3 : angleAt T.C.model 2 = 2 * Real.pi / 3
    · rcases IIIc.caseIII_reduce' T hreg h3 with h | h | h
      · exact h
      · exact absurd h (e2 h3)
      · exact absurd h (e3 h3)
    · exact thm21_I T hreg hgt h3

/-- **The conditional form**: the single hypothesis "Theorem 2.1 holds on the four excluded classes" (one explicit input for IIc, IIIa, IIIb, IVc5) gives `Theorem21`.  (`hIIIa`/`hIIIb` are the paper's
statements, not known to follow from the printed route; the hypotheses are propositions about all tilings of the class, not witnessed here.) -/
theorem theorem21_of_cases
    (hIIc : ∀ (N M : ℕ) [NeZero M] (T : PolyTiling N M), RegularPQ T.C → Thm21Excluded T → Thm21Concl T.C T.P) : Theorem21 :=
  fun N M _ T hreg => by
    by_cases h : Thm21Excluded T
    · exact hIIc N M T hreg h
    · exact thm21_partial T hreg h

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.thm21_partial
#print axioms Erdos634.Draft.LaczFormal.RG.theorem21_of_cases
