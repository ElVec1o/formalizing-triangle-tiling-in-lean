-- Draft/LaczFormalIIcG11i.lean -- Laczkovich (DCG 48 (2012)), Thm 2.1: the class IIc reduced to TWO named inputs.
--   `IIcNoKites`  : Lemma 6.2 for generic angles (kiteB = empty) -- NOT proved;
--   `IIcIsoClaim` : Theorem 2.1's conclusion on the class IIc when alpha = beta (isosceles model, a = b) -- NOT proved (the only non-`AngGen` sub-case that is not vacuous, see G11h).
-- `iic_claim_of_parts : IIcNoKites -> IIcIsoClaim -> IIcClaim`, and `theorem21_of_noKites_iso : IIcNoKites -> IIcIsoClaim -> Theorem21`.
-- For alpha != beta, `AngGen` is derived (G11h: ne02, ne12 and the right angles are vacuous in IIc) and the printed inequality (v) is proved (G11e-g), so nothing else is assumed.
-- NOTE, UNAUDITED.  CONDITIONAL on the two named hypotheses and on the Case IIc hypothesis block (witnessed by GenWitK (204-tile octagon, genTiling_thm21) and IsoWitM).  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcG11g
import Erdos634.Draft.LaczFormalIIcG11h

open scoped Classical Fin.NatCast
open EuclideanGeometry Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

/-- NAMED BLOCKER: Theorem 2.1's conclusion for regular tilings of class IIc with `alpha = beta` (isosceles model). -/
def IIcIsoClaim : Prop :=
  ∀ (N M : ℕ) [NeZero M] (T : PolyTiling N M), RegularPQ T.C → Thm21Excluded4 T → angleAt T.C.model 0 = angleAt T.C.model 1 → Thm21Concl T.C T.P

set_option maxHeartbeats 12800000 in
/-- **`IIcClaim` from `IIcNoKites` and `IIcIsoClaim`.** -/
theorem iic_claim_of_parts (hNK : IIcNoKites) (hIso : IIcIsoClaim) : IIcClaim := by
  intro N M _ T hreg hex
  classical
  by_cases h01 : angleAt T.C.model 0 = angleAt T.C.model 1
  · exact hIso N M T hreg hex h01
  obtain ⟨h1, h3, hab, hac⟩ := hex
  rcases lemma61 T hreg h1 h3 hab hac with hc1 | hangs
  · exact Or.inl hc1
  · obtain ⟨idx, hA, hcnt⟩ := hreg
    haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
    have hC : CaseC T.C idx := ⟨idx_dist_of_angle T.C idx hA, hA, fun X => hcnt X, notComb_c_of_comm (slen_pos T.C 2) hab hac⟩
    rcases lemma61_core T.C T.P T.region_eq idx hC h1 h3 with hP | ⟨-, a, ha1, -, -⟩
    · have hcor := corners_of_cntP0 T.C T.P T.region_eq idx hC h1 hP
      have hMγ := (corner_angles_gamma T.C T.P T.region_eq idx hC h1 h3 hcor).2
      have hAng : AngGen (fun l => T.C.model.angleAt l) := (angGen'_of_IIc T.C hMγ h1 h3 hab hac).toAngGen h01
      have hW : ∀ j : Fin M, ∃ W, GExc T.C idx (T.P.v j) W := fun j => gexc_start_of_corner T.C T.P T.region_eq idx hC h1 h3 hcor j
      choose W hW using hW
      have hNK' := hNK N M T idx hC h1 h3 hab hac hAng hcor
      rcases lemma63_full T.C T.P T.region_eq idx hC hab hac h1 h3 hAng hcor hNK' W hW with h7 | h5
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
    · exfalso
      have := hangs (a + 1)
      have ha1' : T.P.angle (a + 1) = angleAt T.C.model 2 := ha1
      rw [ha1'] at this
      linarith

/-- **Theorem 2.1 modulo `IIcNoKites` and `IIcIsoClaim`.** -/
theorem theorem21_of_noKites_iso (hNK : IIcNoKites) (hIso : IIcIsoClaim) : Theorem21 :=
  theorem21_of_IIc (iic_claim_of_parts hNK hIso)

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.iic_claim_of_parts
#print axioms Erdos634.Draft.LaczFormal.RG.theorem21_of_noKites_iso
