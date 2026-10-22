import Erdos634.Draft.ZhangRat8Eq
import Erdos634.Draft.G3CSixtyControl

/-! Witness for `ZhangRat8Eq.zhang_thm1_equilateral_pi3`: the certified equilateral dissection by the `pi/3` tile (`G3CSixtyControl`)
satisfies all hypotheses, so the theorem is not vacuous.  NOTE, UNAUDITED.  Credit Zhang, Beeson-Zhang, Laczkovich. -/

namespace Erdos634.Draft.ZhangRat8Eq
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional

theorem eq_pi3_wit : ∃ (N : ℕ) (D : CongruentDissection N) (a b c : ℝ), Comm a b ∧ Comm a c := by
  obtain ⟨N, D, α, a, b, c, hα, h, -, hE⟩ := Erdos634.Draft.G3CSixtyControl.lemmaP_premises_satisfied
  exact ⟨N, D, a, b, c, zhang_thm1_equilateral_pi3 D hE hα h⟩

end Erdos634.Draft.ZhangRat8Eq
#print axioms Erdos634.Draft.ZhangRat8Eq.eq_pi3_wit
