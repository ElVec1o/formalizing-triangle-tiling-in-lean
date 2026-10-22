-- Draft/Chain15Gaps.lean — discharge of Chain15's gap leaves as they are proved; `chain_fifteen'` has the remaining ones.
import Erdos634.Draft.Chain15
import Erdos634.Draft.FluxCRow5N15

open scoped Classical

namespace Erdos634.Draft.Chain15

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional

/-- π/3 tile, equilateral target, N = 15: discharged (FluxCRow5N15). -/
theorem gapE60_fifteen : GapE60 15 :=
  fun D α a b c hα hd hE => Row5.theoremE_sixty_full15 D hα hd hE rfl

/-- N = 15 modulo the four remaining gap leaves. -/
theorem chain_fifteen' (gA : GapA 15) (gE120 : GapE120 15) (gF1 : GapF1 15) (gR8 : GapR8 15)
    (D : CongruentDissection 15) : False :=
  chain_fifteen gA gapE60_fifteen gE120 gF1 gR8 D

end Erdos634.Draft.Chain15

#print axioms Erdos634.Draft.Chain15.chain_fifteen'
