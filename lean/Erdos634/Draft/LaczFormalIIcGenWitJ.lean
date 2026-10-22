-- Draft/LaczFormalIIcGenWitJ.lean -- WITNESS of the GENERIC Case IIc block (alpha != beta), step J: the hypothesis block of `lemma63_full` / `iic_ang_g11` is satisfied by the 204-tile octagon, EXCEPT `kiteB genDiss idx = empty` (Lemma 6.2),
-- which is NOT discharged here.  What is proved: `RegularPQ`, `Thm21Excluded4`, `AngGen` (alpha != beta), `CaseC`, `hcor`, `HasFansC`, the exceptional-point starts `GExc`; and that `lemma63_full` / `iic_ang_g11` APPLY to it
-- given their hypothesis `hNK` (the conclusion cannot be `Concl7`, since alpha != beta, so it is `Concl5`).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcGenWitI
import Erdos634.Draft.LaczFormalIIcG11g
import Erdos634.Draft.LaczFormalRG12GExcCorner

namespace Erdos634.Draft.LaczFormal.GenWit

open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Thm21 Erdos634.Draft.LaczFormal.RG Erdos634.Draft.LaczFormal.Graph Z2

theorem genTiling_regular : RegularPQ genTiling.C := ⟨idx, genDiss_hidxA, genDiss_hregR⟩

theorem genTiling_excluded4 : Thm21Excluded4 genTiling :=
  ⟨genDiss_angle2_lt, genDiss_angle2_ne, genDiss_comm, genDiss_notComm⟩

theorem genTiling_angGen : AngGen (fun l => genTiling.C.model.angleAt l) := genDiss_angGen

theorem genDiss_alpha_ne_beta : genDiss.model.angleAt 0 ≠ genDiss.model.angleAt 1 := genDiss_angGen.ne01

/-- the exceptional-point starts at the eight corners exist (`gexc_start_of_corner`). -/
theorem genDiss_gexc_starts : ∀ j : Fin 8, ∃ W, GExc genDiss idx (octP.v j) W := by
  haveI : HasFansC genDiss.toRegionDissection := hasFansC_poly _ octP rfl
  intro j
  exact gexc_start_of_corner genDiss octP rfl idx genDiss_caseC genDiss_angle2_lt genDiss_angle2_ne genDiss_hcor j

/-- **`lemma63_full` applies to the 204-tile octagon** (given `kiteB = empty`, the one hypothesis of the block NOT discharged). -/
theorem genBlock_lemma63 (hNK : kiteB genDiss idx = ∅) : Concl7 genDiss octP ∨ Concl5 genDiss octP := by
  haveI : HasFansC genDiss.toRegionDissection := hasFansC_poly _ octP rfl
  obtain ⟨W, hW⟩ : ∃ W : Fin 8 → Plane, ∀ j, GExc genDiss idx (octP.v j) (W j) := by
    choose W hW using genDiss_gexc_starts
    exact ⟨W, hW⟩
  exact lemma63_full genDiss octP rfl idx genDiss_caseC genDiss_comm genDiss_notComm genDiss_angle2_lt genDiss_angle2_ne genDiss_angGen genDiss_hcor hNK W hW

theorem genDiss_not_concl7 : ¬ Concl7 genDiss octP := fun h => genDiss_alpha_ne_beta h.2.2.1

theorem genBlock_concl5 (hNK : kiteB genDiss idx = ∅) : Concl5 genDiss octP :=
  (genBlock_lemma63 hNK).resolve_left genDiss_not_concl7

/-- **`iic_ang_g11` applies** (given the global `IIcNoKites`). -/
theorem genBlock_iic (hNK : IIcNoKites) : Thm21Concl genTiling.C genTiling.P :=
  iic_ang_g11 hNK genTiling genTiling_regular genTiling_excluded4 genDiss_angGen

/-- **The generic Case IIc hypothesis block is satisfiable** (all hypotheses of `iic_ang_g11` other than `IIcNoKites`; `N = 204`, `M = 8`). -/
theorem genBlock_exists : ∃ (T : PolyTiling 204 8) (idx : Fin 204 → Equiv.Perm (Fin 3)), RegularPQ T.C ∧ Thm21Excluded4 T ∧
    AngGen (fun l => T.C.model.angleAt l) ∧ CaseC T.C idx ∧
    (∀ j : Fin 8, RG.cnt T.C idx (T.P.v j) 0 = 1 ∧ RG.cnt T.C idx (T.P.v j) 1 = 1 ∧ RG.cnt T.C idx (T.P.v j) 2 = 0) :=
  ⟨genTiling, idx, genTiling_regular, genTiling_excluded4, genDiss_angGen, genDiss_caseC, genDiss_hcor⟩

end Erdos634.Draft.LaczFormal.GenWit

#print axioms Erdos634.Draft.LaczFormal.GenWit.genBlock_exists
#print axioms Erdos634.Draft.LaczFormal.GenWit.genBlock_lemma63
#print axioms Erdos634.Draft.LaczFormal.GenWit.genBlock_concl5
#print axioms Erdos634.Draft.LaczFormal.GenWit.genBlock_iic
