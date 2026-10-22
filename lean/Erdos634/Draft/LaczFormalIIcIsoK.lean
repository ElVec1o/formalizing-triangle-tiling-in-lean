-- Draft/LaczFormalIIcIsoK.lean -- Laczkovich (DCG 48 (2012)), Thm 2.1, Case IIc with alpha = beta: THE NAMED BLOCKER `IIcIsoCore` (Lemma 6.3 on the corner-count branch) IS PROVED, hence `IIcIsoClaim`.
--  `iic_iso_core  : IIcIsoCore`    (via `lemma63_full_iso`, `kiteB_empty_iso`, `AngGen'` derived inside IIc: `angGen'_of_IIc`, `corner_angles_gamma`),
--  `iic_iso_claim : IIcIsoClaim`   (`iic_iso_claim_of_core`),
--  `theorem21_of_noKites : IIcNoKites -> Theorem21` (the isosceles half of Case IIc is no longer an input; only Lemma 6.2 for generic angles `IIcNoKites` remains, plus the WITNESS of the IIc hypothesis block).
-- Route: for alpha = beta no Gamma_kite vertex of type (B) exists (an interior (2,2,2) vertex always carries a straight line: IsoF), every end of a Gamma_except edge is exceptional (IsoG), and the generic
-- Lemma 6.3 machinery (Sharp5/7, L8*, G11*) is rerun on that, unchanged, in the iso copies IsoH/I/J.
-- STATUS UPDATE: the Case IIc hypothesis block is witnessed by the octagon (IsoWitA..M, commit 8883acc3), so the "no witness constructed" wording of the earlier header is stale.
-- NOTE, UNAUDITED.  CONDITIONAL on nothing beyond the Case IIc hypothesis block of `IIcIsoCore`, which the octagon witness supplies. Credit: Laczkovich (DCG 48 (2012), Sect. 6.2-6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcIsoJ
import Erdos634.Draft.LaczFormalIIcIsoC

open scoped Classical Fin.NatCast
open EuclideanGeometry Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

set_option maxHeartbeats 12800000 in
/-- **`IIcIsoCore`: Lemma 6.3 for the isosceles model, corner-count branch.** -/
theorem iic_iso_core : IIcIsoCore := by
  intro N M _ D _ P hreg idx hC hab hac h1 h3 h01 hcor W hW
  have hMγ := (corner_angles_gamma D P hreg idx hC h1 h3 hcor).2
  have G : AngGenI (fun l => D.model.angleAt l) := ⟨angGen'_of_IIc D hMγ h1 h3 hab hac, h01⟩
  exact lemma63_full_iso D P hreg idx hC hab hac h1 h3 G hcor (kiteB_empty_iso D P hreg idx hC h1 h3 G) W hW

/-- **`IIcIsoClaim` proved.** -/
theorem iic_iso_claim : IIcIsoClaim := iic_iso_claim_of_core iic_iso_core

/-- **Theorem 2.1 modulo `IIcNoKites` ONLY** (the isosceles sub-case of Case IIc is proved). -/
theorem theorem21_of_noKites (hNK : IIcNoKites) : Theorem21 := theorem21_of_noKites_iso hNK iic_iso_claim

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.iic_iso_core
#print axioms Erdos634.Draft.LaczFormal.RG.iic_iso_claim
#print axioms Erdos634.Draft.LaczFormal.RG.theorem21_of_noKites
