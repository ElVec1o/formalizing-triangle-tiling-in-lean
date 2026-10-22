-- Draft/LaczFormalIIcIsoC.lean -- Laczkovich (DCG 48 (2012)), Thm 2.1, Case IIc with alpha = beta: reduction of `IIcIsoClaim` to its geometric core.
-- `IIcIsoCore` is Lemma 6.3 for the isosceles model, stated on the corner-count branch ONLY (every corner of P carries labels (1,1,0), a Gamma_except edge starts at every vertex):
--   conclusion `Concl7 D P \/ Concl5 D P` (regular M-gon, or the centrally symmetric 2k-gon with q = 1).  The dispatch of `lemma61`/`lemma61_core` (conclusion (i), or the corner-count branch,
--   or contradiction) does not use `AngGen` and is reused verbatim.   `iic_iso_claim_of_core : IIcIsoCore -> IIcIsoClaim`.
-- What `IIcIsoCore` still needs (NOT proved): the Fig. 5 / Gamma_except analysis for omega 0 = omega 1 (the label-distinctness consumers of `straight_run_labels` in RG12GExc*, IIcSharp5/7), see PROGRESS_IIcIso.md.
-- STATUS UPDATE: `IIcIsoCore` is now PROVED (`LaczFormalIIcIsoK.iic_iso_core`) and the Case IIc hypothesis block is witnessed by the octagon (IsoWitA..M, commit 8883acc3); the "NOT proved" note above is stale.
-- NOTE, UNAUDITED.  This file is the conditional reduction `IIcIsoCore -> IIcIsoClaim`, kept as stated. Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcG11i
import Erdos634.Draft.LaczFormalIIcIsoB

open scoped Classical Fin.NatCast
open EuclideanGeometry Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

/-- NAMED BLOCKER (core of `IIcIsoClaim`): Lemma 6.3 for the isosceles model on the corner-count branch. -/
def IIcIsoCore : Prop :=
  ∀ (N M : ℕ) [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (_ : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (_ : CaseC D idx) (_ : Comm (slen D 0) (slen D 1)) (_ : ¬ Comm (slen D 0) (slen D 2))
    (_ : D.model.angleAt 2 < Real.pi / 2) (_ : D.model.angleAt 2 ≠ Real.pi / 3) (_ : angleAt D.model 0 = angleAt D.model 1)
    (_ : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0)
    (W : Fin M → Plane) (_ : ∀ j, GExc D idx (P.v j) (W j)), Concl7 D P ∨ Concl5 D P

set_option maxHeartbeats 12800000 in
/-- **`IIcIsoClaim` from `IIcIsoCore`.** -/
theorem iic_iso_claim_of_core (hCore : IIcIsoCore) : IIcIsoClaim := by
  intro N M _ T hreg hex h01
  classical
  obtain ⟨h1, h3, hab, hac⟩ := hex
  rcases lemma61 T hreg h1 h3 hab hac with hc1 | hangs
  · exact Or.inl hc1
  · obtain ⟨idx, hA, hcnt⟩ := hreg
    haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
    have hC : CaseC T.C idx := ⟨idx_dist_of_angle T.C idx hA, hA, fun X => hcnt X, notComb_c_of_comm (slen_pos T.C 2) hab hac⟩
    rcases lemma61_core T.C T.P T.region_eq idx hC h1 h3 with hP | ⟨-, a, ha1, -, -⟩
    · have hcor := corners_of_cntP0 T.C T.P T.region_eq idx hC h1 hP
      have hW : ∀ j : Fin M, ∃ W, GExc T.C idx (T.P.v j) W := fun j => gexc_start_of_corner T.C T.P T.region_eq idx hC h1 h3 hcor j
      choose W hW using hW
      rcases hCore N M T.C T.P T.region_eq idx hC hab hac h1 h3 h01 hcor W hW with h7 | h5
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
    · exfalso
      have := hangs (a + 1)
      have ha1' : T.P.angle (a + 1) = angleAt T.C.model 2 := ha1
      rw [ha1'] at this
      linarith

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.iic_iso_claim_of_core
