-- Draft/Chain15R8.lean — GapR8 at N = 15 DISCHARGED: the five R8 shapes (F2, F3, F3', F4, F4') via the N=15
-- ports R8N15F2 / F3 / F3Prime / F4 / F4Prime, dispatched exactly as R8F2to4Bridge.r8_reduction_statement.  UNAUDITED.
import Erdos634.Draft.Chain15Gaps
import Erdos634.Draft.R8F2to4Bridge
import Erdos634.Draft.R8N15F2
import Erdos634.Draft.R8N15F3
import Erdos634.Draft.R8N15F3Prime
import Erdos634.Draft.R8N15F4
import Erdos634.Draft.R8N15F4Prime

open scoped Classical

namespace Erdos634.Draft.Chain15

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.R8F2to4Bridge

theorem gapR8_fifteen : GapR8 15 := by
  intro D α a b c hirr hm hshape
  obtain ⟨_, _, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  rcases hshape with hF2 | hF3 | hF3' | hF4 | hF4'
  · obtain ⟨ν, hνpos, hd⟩ := f2_data_of_shape D hm hF2
    exact Erdos634.Draft.R8N15F2.f2_prime_contradiction D hirr hm hd ha0 hb0 hνpos rfl
  · obtain ⟨ν, hνpos, hd⟩ := f3_data_of_shape D hm hF3
    exact Erdos634.Draft.R8N15F3.f3_prime_contradiction D hirr hm hd ha0 hb0 hνpos rfl
  · obtain ⟨ν, hνpos, hd⟩ := f3prime_data_of_shape D hm hF3'
    exact Erdos634.Draft.R8N15F3Prime.f3prime_contradiction D hirr hm hd ha0 hb0 hνpos rfl
  · obtain ⟨ν, hνpos, hd⟩ := f4_data_of_shape D hm hF4
    exact Erdos634.Draft.R8N15F4.f4_prime_contradiction D hirr hm hd ha0 hb0 hνpos rfl
  · obtain ⟨ν, hνpos, hd⟩ := f4prime_data_of_shape D hm hF4'
    exact Erdos634.Draft.R8N15F4Prime.f4prime_prime_contradiction D hirr hm hd ha0 hb0 hνpos rfl

/-- N = 15 modulo the three remaining gap leaves (Case A, 2π/3 equilateral, F1). -/
theorem chain_fifteen'' (gA : GapA 15) (gE120 : GapE120 15) (gF1 : GapF1 15)
    (D : CongruentDissection 15) : False :=
  chain_fifteen' gA gE120 gF1 gapR8_fifteen D

end Erdos634.Draft.Chain15

#print axioms Erdos634.Draft.Chain15.chain_fifteen''
