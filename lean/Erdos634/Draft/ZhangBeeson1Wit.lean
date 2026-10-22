import Erdos634.Draft.ZhangBeeson1
import Erdos634.Draft.FluxCRow12Witness

/-! Witness for `ZhangBeeson1.zhang_thm1_beeson3`: the certified 44-tiling (`Tiling44Bridge.dissection`, tile `(16,24,32)`, base-beta target) satisfies every hypothesis.
NOTE, UNAUDITED.  Credit Zhang, Beeson, Beeson-Zhang. -/

namespace Erdos634.Draft.ZhangBeeson1
open Erdos634.Draft.TheoremPConditional Erdos634.Draft.LaczFormal.Thm21

theorem beeson3_wit : Comm (16 : ℝ) 24 ∧ Comm (16 : ℝ) 32 :=
  zhang_thm1_beeson3 Erdos634.Tiling44Bridge.dissection Erdos634.Draft.FluxGridWitness.α44_irr
    Erdos634.Draft.FluxGridWitness.three_α_two_β Erdos634.Draft.FluxRow11Witness.data44
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, Erdos634.Draft.FluxGridWitness.t_angle0,
      Erdos634.Draft.FluxGridWitness.t_angle1, Erdos634.Draft.FluxGridWitness.t_angle2⟩))))

end Erdos634.Draft.ZhangBeeson1
#print axioms Erdos634.Draft.ZhangBeeson1.beeson3_wit
