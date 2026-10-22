-- Draft/Chain15F1.lean — GapF1 at N = 15 NARROWED to the (3,5) branch `c = 4a` (open): the (1,15) branch is
-- discharged by `f1_free_Ma1` + `f1_pin_mu_or_c4a_15`.  UNAUDITED.
import Erdos634.Draft.Chain15R8
import Erdos634.Draft.F1FreeProofM
import Erdos634.Draft.F1N15

open scoped Classical

namespace Erdos634.Draft.Chain15

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional

/-- The open (3,5) branch of the F1 leaf at N = 15: `Ma = 3`, `Mb = 5`, `c = 4a`, `b/a = (−1+√61)/2`. -/
def GapF1c4a : Prop :=
  ∀ (D : CongruentDissection 15) (α a b c μ : ℝ), IrrPi α → D.model.TwoPiThreeData α a b c →
    D.target.F1Data α a b c μ → 0 < μ → c = 4 * a → False

theorem gapF1_fifteen_of_c4a (g : GapF1c4a) : GapF1 15 := by
  intro D α a b c hirr hm hshape
  refine Erdos634.Draft.F1FreeProofM.f1_free_Ma1 D (by norm_num) hirr hm hshape ?_ ?_
  · intro μ hμ hF1
    rcases Erdos634.Draft.F1AlgebraPin.f1_pin_mu_or_c4a_15 D hirr hm hF1 hμ rfl with h | h
    · exact h
    · exact (g D α a b c μ hirr hm hF1 hμ h).elim
  · intro μ hμ hF1'
    have hirr' : IrrPi (Real.pi / 3 - α) := by
      intro ⟨q, hq⟩; apply hirr; exact ⟨1/3 - q, by push_cast; linarith⟩
    have hm' : D.model.TwoPiThreeData (Real.pi / 3 - α) b a c :=
      Erdos634.Geometry.twoPiThreeData_swap D.model hm
    rcases Erdos634.Draft.F1AlgebraPin.f1_pin_mu_or_c4a_15 D hirr' hm' hF1' hμ rfl with h | h
    · exact h
    · exact (g D _ b a c μ hirr' hm' hF1' hμ h).elim

/-- N = 15 modulo Case A, the 2π/3 equilateral certificate, and the (3,5) F1 branch. -/
theorem chain_fifteen3 (gA : GapA 15) (gE120 : GapE120 15) (g : GapF1c4a)
    (D : CongruentDissection 15) : False :=
  chain_fifteen'' gA gE120 (gapF1_fifteen_of_c4a g) D

end Erdos634.Draft.Chain15

#print axioms Erdos634.Draft.Chain15.chain_fifteen3
