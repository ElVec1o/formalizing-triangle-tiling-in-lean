-- Draft/LaczFormalThm21Final.lean -- Laczkovich (DCG 48 (2012)), Theorem 2.1: UNCONDITIONAL in Lean.
-- `theorem21_unconditional : Theorem21` = theorem21_of_noKites iicNoKites_proved.  `Theorem21` is `forall N M T, RegularPQ T.C -> Thm21Concl T.C T.P`; no residual hypothesis.
-- NOTE, UNAUDITED (internal; not audited outside the project).  Known deviations from the printed statement: see (private working notes, not included)
-- Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN127
import Erdos634.Draft.LaczFormalIIcIsoK
import Erdos634.Draft.LaczFormalThm21AssemblyWit

namespace Erdos634.Draft.LaczFormal.RG

theorem theorem21_unconditional : Erdos634.Draft.LaczFormal.Thm21.Theorem21 :=
  theorem21_of_noKites iicNoKites_proved

/-- `IIcClaim` (the single former input of `theorem21_of_IIc`) is now a theorem. -/
theorem iic_claim_unconditional : IIcClaim := iic_claim_of_parts iicNoKites_proved iic_iso_claim

/-- Unconditional restatement of `assembly_witness'`. -/
theorem assembly_witness_unc : Erdos634.Draft.LaczFormal.Thm21.Thm21Concl rTilingSqrt3.C rTilingSqrt3.P :=
  assembly_witness' iic_claim_unconditional

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.theorem21_unconditional
#print axioms Erdos634.Draft.LaczFormal.RG.iic_claim_unconditional
#print axioms Erdos634.Draft.LaczFormal.RG.assembly_witness_unc
