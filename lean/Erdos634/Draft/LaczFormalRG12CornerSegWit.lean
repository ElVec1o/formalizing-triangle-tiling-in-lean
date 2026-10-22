-- Draft/LaczFormalRG12CornerSegWit.lean -- NON-VACUITY of `corner_segment_exists` (Laczkovich Sect. 6.2, Gamma_except start): the two-triangle rhombus `w61Tiling` (gamma = pi/4), polygon vertex `v_1 = (1,0)`,
-- where both tiles meet (the diagonal's endpoint); every hypothesis of `corner_segment_exists` holds and a maximal segment (the diagonal) is obtained.
-- Caveat: a two-tile example (the chain has n = 2, one inner ray); it does not exercise longer chains.  NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12CornerSeg
import Erdos634.Draft.LaczFormalRG12L61Wit

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

theorem corner_segment_witness :
    haveI : HasFansC w61Tiling.C.toRegionDissection := hasFansC_poly _ w61Tiling.P w61Tiling.region_eq
    ∃ (pT qT d : V2), Par pT (toV2 (w61Tiling.P.e (0 + 1))) ∧ Par qT (toV2 (w61Tiling.P.v 0 - w61Tiling.P.v (0 + 1))) ∧ 0 < crs pT qT ∧
      inCone pT qT d ∧ MaxSegAlong w61Tiling.C.toRegionDissection d (w61Tiling.P.v (0 + 1)) := by
  haveI : HasFansC w61Tiling.C.toRegionDissection := hasFansC_poly _ w61Tiling.P w61Tiling.region_eq
  have hv : w61Tiling.P.v (0 + 1) = mkPt 1 0 := rfl
  have m0 : w61Tiling.P.v (0 + 1) ∈ (w61Tiling.C.tile 0).carrier :=
    hv ▸ (show mkPt 1 0 = (w61Tiling.C.tile 0).pts 0 from rfl) ▸ subset_convexHull ℝ _ ⟨0, rfl⟩
  have m1 : w61Tiling.P.v (0 + 1) ∈ (w61Tiling.C.tile 1).carrier :=
    hv ▸ (show mkPt 1 0 = (w61Tiling.C.tile 1).pts 1 from rfl) ▸ subset_convexHull ℝ _ ⟨1, rfl⟩
  refine corner_segment_exists w61Tiling.C.toRegionDissection w61Tiling.P w61Tiling.region_eq 0 ⟨0, 0, hv ▸ rfl⟩
    ⟨⟨0, m0⟩, ⟨1, m1⟩, ?_⟩
  intro h
  have := congrArg Subtype.val h
  exact absurd this (show (0 : Fin 2) ≠ 1 by decide)

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.corner_segment_witness
#print axioms Erdos634.Draft.LaczFormal.RG.corner_segment_exists
