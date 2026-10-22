-- Draft/Chain15H.lean — LemmaH15 discharged (lemmaH_15); chain_fifteen5 needs only GapA2, GapE120, GapF1c4a.  UNAUDITED.
import Erdos634.Draft.Chain15A
import Erdos634.Draft.CaseALemmaH15Exc

namespace Erdos634.Draft.Chain15
open Erdos634.Geometry Erdos634.CaseA.R0c15

theorem lemmaH15_holds : LemmaH15 := by
  intro D θ hq h0 h2 p q hpq hp hq' i j hij hi hj
  exact Erdos634.Geometry.CaseA.LemmaH.lemmaH_15 D hq h0 h2 hpq hp hq' hij hi hj rfl

theorem chain_fifteen5 (A2 : GapA2) (gE120 : GapE120 15) (g : GapF1c4a) (D : CongruentDissection 15) : False :=
  chain_fifteen4 lemmaH15_holds A2 gE120 g D
#print axioms chain_fifteen5
end Erdos634.Draft.Chain15
