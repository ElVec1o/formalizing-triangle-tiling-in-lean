-- Draft/LaczFormalIIcWN127.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2: `iicNoKites_proved : IIcNoKites`, with NO residual supply.
-- `IIcSupply7` (WN118) was the single hypothesis `ExcInsideAll`; WN119-126 prove it (nesting of disjoint polygons, convex-vertex chords, counting with capacities, induction on the Gamma_kite vertices inside).
-- What remains is the hypothesis block of `IIcNoKites` itself (Case IIc: `CaseC`, `angleAt 2 < pi/2`, `angleAt 2 != pi/3`, `Comm`, `AngGen`, the corner counts); it is satisfiable (octagon iso and generic witnesses, per (private working notes, not included)).
-- The conclusion `kiteB = empty` is the statement that a counterexample hypothesis block has no Gamma_kite vertex (Lemma 6.2: no closed Gamma_kite chain exists).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN126

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

theorem iicSupply7_proved : IIcSupply7 := by
  intro N M _ T idx hC h1 h3 hab hac hAng hcor _
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  exact excInsideAll_proved T.C T.P T.region_eq idx hC hab hac h1 h3 hAng hcor

/-- **Laczkovich, Lemma 6.2: `IIcNoKites`**, unconditional in Lean (modulo the hypothesis block of the statement). -/
theorem iicNoKites_proved : IIcNoKites := iicNoKites_of_supply7 iicSupply7_proved

#print axioms iicNoKites_proved

end Erdos634.Draft.LaczFormal.RG
