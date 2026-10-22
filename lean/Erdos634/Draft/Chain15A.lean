-- Draft/Chain15A.lean — N = 15 modulo: LemmaH15 (half-isosceles exit, port in progress), GapA2 (5-smooth Case A, OPEN),
-- GapE120 (2π/3 equilateral certificate, needs override), GapF1c4a (F1 (3,5) branch, OPEN).  UNAUDITED.
import Erdos634.Draft.CaseAN15

namespace Erdos634.Draft.Chain15

open Erdos634.Geometry Erdos634.CaseA.R0c15

theorem chain_fifteen4 (hH : LemmaH15) (A2 : GapA2) (gE120 : GapE120 15) (g : GapF1c4a)
    (D : CongruentDissection 15) : False :=
  chain_fifteen3 (gapA_fifteen_of_A2 hH A2) gE120 g D

end Erdos634.Draft.Chain15

#print axioms Erdos634.Draft.Chain15.chain_fifteen4
