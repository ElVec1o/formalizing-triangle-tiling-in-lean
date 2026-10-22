-- Draft/LaczFormalFluxPolyWit.lean -- WITNESS for the polygon flux cancellation (LaczFormalFluxPolyFin): the unit square cut along a diagonal into two triangles
-- (`sqTiling`, a genuine `PolyTiling 2 4`, one interior edge shared by the two tiles) satisfies the hypotheses `R.region = P.carrier`; the odd weight `f d = d` (E = Plane) is
-- odd.  So `ConvPoly.flux_cancel` is instantiated and its conclusion is inhabited.  Also the axiom audit of the whole chain.
-- NOTE / UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 7.3/8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalFluxPolyFin
import Erdos634.Draft.LaczFormalThm21AreaWit

open Erdos634.Geometry Erdos634.RegionDissection

namespace Erdos634.Draft.LaczFormal.Thm21

/-- `f d = d` (the underlying vector) is an odd direction weight. -/
theorem id_odd (d : Dir) : (fun d : Dir => (d.1 : Plane)) (Dir.neg d) = -(fun d : Dir => (d.1 : Plane)) d := rfl

/-- The polygon flux cancellation instantiated on the unit-square tiling. -/
theorem flux_cancel_square :
    ∑ i, (sqTiling.C.toRegionDissection.tile i).flux (fun d : Dir => (d.1 : Plane)) =
      sqTiling.P.flux (fun d : Dir => (d.1 : Plane)) :=
  sqTiling.P.flux_cancel sqTiling.C.toRegionDissection sqTiling.region_eq _ id_odd

end Erdos634.Draft.LaczFormal.Thm21

#print axioms Erdos634.Draft.LaczFormal.Thm21.flux_cancel_square
#print axioms Erdos634.Draft.LaczFormal.Thm21.ConvPoly.flux_cancel
