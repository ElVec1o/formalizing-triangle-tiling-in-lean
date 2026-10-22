-- Draft/LaczFormalThm21AssemblyWit.lean -- NON-VACUITY of the assembly (LaczFormalThm21Assembly): on the real regular tiling `rTilingSqrt3` (30-60-90 rectangle, PolyTiling 2 4,
-- RegularPQ, gamma = pi/2) the hypotheses of `thm21_partial4` hold (it is not in IIc, as gamma = pi/2 is not < pi/2) and Thm21Concl is obtained through the assembly,
-- also via `theorem21_of_IIc`'s case split (the branch taken is `thm21_partial4`).  This witnesses the unconditional branch only; the hypothesis `IIcClaim` is NOT witnessed
-- (its class IIc has no known instance: see WITNESS_IIC_2026-10-22.md).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalThm21Assembly
import Erdos634.Draft.LaczFormalRGCaseVWit

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

theorem rTilingSqrt3_not_IIc : ¬ Thm21Excluded4 rTilingSqrt3 := by
  intro h
  have g := rDiss_gamma (one_pos : (0:ℝ) < 1) (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 3))
  have := h.1
  have e : angleAt rTilingSqrt3.C.model 2 = Real.pi / 2 := g
  linarith

theorem assembly_witness : Thm21Concl rTilingSqrt3.C rTilingSqrt3.P :=
  thm21_partial4 rTilingSqrt3 (rDiss_regular one_pos (Real.sqrt_pos.mpr (by norm_num))) rTilingSqrt3_not_IIc

/-- The assembled theorem applied to the witness (the IIc hypothesis is only used in the IIc branch, not taken here). -/
theorem assembly_witness' (h : IIcClaim) : Thm21Concl rTilingSqrt3.C rTilingSqrt3.P :=
  theorem21_of_IIc h 2 4 rTilingSqrt3 (rDiss_regular one_pos (Real.sqrt_pos.mpr (by norm_num)))

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.assembly_witness
