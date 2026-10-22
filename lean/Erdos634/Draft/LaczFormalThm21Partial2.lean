-- Draft/LaczFormalThm21Partial2.lean -- **Laczkovich (DCG 48 (2012)) Theorem 2.1: PARTIAL assembly, version 2.**  NOT `Theorem21`.
-- Cases IIIa and IIIb (gamma = 2pi/3, NotComb) are now covered by the repaired counting (`caseIIIa_repaired`, `caseIIIb_repaired`, LaczFormalBZBridge: BZ defect inequality + corner-side closure).
-- `Thm21Excluded2` keeps ONLY the two remaining classes:  IIc (gamma < pi/2, != pi/3; a,b commensurable, a,c not)  and  IVc5 (gamma = pi/3; a,b commensurable, a,c not; M >= 5).
-- (The IVc rational branch of the task brief is the `M <= 4` side of IVc, closed by `caseIVc_small` in `thm21_partial`; what stays excluded is IVc5 and IIc.)
-- `thm21_partial2`: outside these two classes one of (i)-(ix) holds.  `theorem21_of_cases2`: the conditional form with a single hypothesis on the two classes.  Old names in LaczFormalThm21Partial are kept.
-- NOTE, UNAUDITED.  `Theorem21` is NOT claimed.  The IIIa/IIIb input is the AI assistant repair (audit (private working notes, not included)), not the printed Lemma 7.1; no tiling with NotComb data and M >= 4
-- is known to exist (consistent with `caseIIIa_repaired` concluding Concl1, a parallelogram with a gamma-angle), so those two lemmas are witnessed only through their hypotheses' satisfiability, not by an example.
-- Credit: Laczkovich (DCG 48 (2012)), Zhang, Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalThm21Partial
import Erdos634.Draft.LaczFormalBZBridge

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

/-- The two classes still missing from the Lean proof of Theorem 2.1 (IIIa, IIIb removed). -/
def Thm21Excluded2 {N M : ℕ} [NeZero M] (T : PolyTiling N M) : Prop :=
  (angleAt T.C.model 2 < Real.pi / 2 ∧ angleAt T.C.model 2 ≠ Real.pi / 3 ∧ Comm (slen T.C 0) (slen T.C 1) ∧ ¬ Comm (slen T.C 0) (slen T.C 2)) ∨
  (angleAt T.C.model 2 = Real.pi / 3 ∧ Comm (slen T.C 0) (slen T.C 1) ∧ ¬ Comm (slen T.C 0) (slen T.C 2) ∧ 5 ≤ M)

theorem thm21_partial2 {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) (hex : ¬ Thm21Excluded2 T) : Thm21Concl T.C T.P := by
  by_cases h : Thm21Excluded T
  · unfold Thm21Excluded at h
    rcases h with h | ⟨hγ, hnc⟩ | ⟨hγ, hnc⟩ | h
    · exact absurd (Or.inl h) hex
    · exact Or.inl (caseIIIa_repaired T hreg hγ hnc)
    · exact Or.inl (caseIIIb_repaired T hreg hγ hnc)
    · exact absurd (Or.inr h) hex
  · exact thm21_partial T hreg h

theorem theorem21_of_cases2
    (h : ∀ (N M : ℕ) [NeZero M] (T : PolyTiling N M), RegularPQ T.C → Thm21Excluded2 T → Thm21Concl T.C T.P) : Theorem21 :=
  fun N M _ T hreg => by
    by_cases hx : Thm21Excluded2 T
    · exact h N M T hreg hx
    · exact thm21_partial2 T hreg hx

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.thm21_partial2
#print axioms Erdos634.Draft.LaczFormal.RG.theorem21_of_cases2
