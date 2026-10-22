-- Draft/Chain15X.lean — GapF1c4a discharged (F1c4aSide); chain_fifteen6 needs only GapA2 and GapE120.  UNAUDITED.
import Erdos634.Draft.Chain15H
import Erdos634.Draft.F1c4aSide

namespace Erdos634.Draft.Chain15
open Erdos634.Geometry Erdos634.CaseA.R0c15

theorem chain_fifteen6 (A2 : GapA2) (gE120 : GapE120 15) (D : CongruentDissection 15) : False :=
  chain_fifteen5 A2 gE120 Erdos634.Draft.F1c4aSide.gapF1c4a_holds D
#print axioms chain_fifteen6
end Erdos634.Draft.Chain15
