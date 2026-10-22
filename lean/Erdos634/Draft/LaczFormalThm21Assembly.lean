-- Draft/LaczFormalThm21Assembly.lean -- **Laczkovich (DCG 48 (2012)) Theorem 2.1: ASSEMBLY modulo the single named hypothesis `IIcClaim`.**  NOT `Theorem21`.
-- Case split on a regular polygon tiling T (gamma = model angle at vertex 2):
--   gamma = pi/2 (V) -> thm21_V ; gamma > pi/2: != 2pi/3 (I) -> thm21_I ; = 2pi/3 (III) -> caseIII_reduce' / caseIIIa_repaired / caseIIIb_repaired ;
--   gamma < pi/2: = pi/3 (IV) -> caseIV_reduce, caseIVc_small (M <= 4), caseIVc_concl (M >= 5, alpha/pi irrational), ivc_rat_final (M >= 5, alpha/pi rational) ;
--   gamma < pi/2, != pi/3 (II) -> caseII_a, caseII_b_small, caseII_b, and the class IIc (a,b commensurable, a,c not) = `Thm21Excluded4`.
-- `IIcClaim` is the ONLY open input: "Theorem 2.1 holds on the class IIc" (Lemma 6.2(ii), ring step, Lemma 6.3 of the paper).  Conclusion (v) (the printed inequality
-- `a_k >= q^(k-1) a_1`, `Concl5`) is produced ONLY by Lemma 6.3 inside IIc; no other case outputs Concl5, and it is not provable separately from the data
-- of IIc, so it is NOT a separate hypothesis: it is part of what `IIcClaim` asserts (Thm21Concl includes Concl5 verbatim as printed).
-- Results: `thm21_partial4` (unconditional outside IIc), `theorem21_of_IIc : IIcClaim -> Theorem21`.
-- NOTE, UNAUDITED.  Theorem21 is NOT claimed.  Non-vacuity of the assembled statement: Draft/LaczFormalThm21AssemblyWit.lean.
-- Credit: Laczkovich (DCG 48 (2012)), Zhang, Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalThm21Partial3
import Erdos634.Draft.LaczFormalIVcRatBr8a

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

/-- The class IIc: gamma < pi/2, gamma != pi/3, a,b commensurable, a,c not commensurable. The only class not in Lean. -/
def Thm21Excluded4 {N M : ℕ} [NeZero M] (T : PolyTiling N M) : Prop :=
  angleAt T.C.model 2 < Real.pi / 2 ∧ angleAt T.C.model 2 ≠ Real.pi / 3 ∧ Comm (slen T.C 0) (slen T.C 1) ∧ ¬ Comm (slen T.C 0) (slen T.C 2)

/-- The single open input: Theorem 2.1's conclusion for every regular polygon tiling of class IIc. -/
def IIcClaim : Prop :=
  ∀ (N M : ℕ) [NeZero M] (T : PolyTiling N M), RegularPQ T.C → Thm21Excluded4 T → Thm21Concl T.C T.P

/-- Outside IIc, one of (i)-(ix) holds (unconditional; uses `ivc_rat_final` for the rational IVc branch). -/
theorem thm21_partial4 {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) (hex : ¬ Thm21Excluded4 T) : Thm21Concl T.C T.P := by
  by_cases h : Thm21Excluded3 T
  · rcases h with h | ⟨hγ, hab, hac, hM, hs⟩
    · exact absurd h hex
    · exact ivc_rat_final T hreg hγ hab hac hM hs
  · exact thm21_partial3 T hreg h

/-- **Theorem 2.1 modulo `IIcClaim`.** -/
theorem theorem21_of_IIc (h_IIc : IIcClaim) : Theorem21 :=
  fun N M _ T hreg => by
    by_cases hx : Thm21Excluded4 T
    · exact h_IIc N M T hreg hx
    · exact thm21_partial4 T hreg hx

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.thm21_partial4
#print axioms Erdos634.Draft.LaczFormal.RG.theorem21_of_IIc
