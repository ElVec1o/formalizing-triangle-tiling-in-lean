import Erdos634.Draft.ZhangRat10Thm9
import Erdos634.Draft.ZhangBeeson1Wit

/-! Non-vacuity of `ZhangRat10Thm9.beeson_thm9`: the certified 44-tiling (tile `(16,24,32)`, target angles `(beta, beta, 3 alpha)`) meets every hypothesis,
including the AAA non-similarity of the target to the tile.  NOTE, UNAUDITED.  Credit Beeson (arXiv 1206.2229v4, Thm 9), Zhang, Laczkovich. -/

namespace Erdos634.Draft.ZhangRat10Thm9
open Erdos634.Draft.TheoremPConditional Erdos634.Draft.LaczFormal.Thm21 Erdos634.Geometry Erdos634.BeesonColoring
open Erdos634.Draft.FluxGridWitness

theorem aux_not_triple3 {α β x y z : ℝ} (hα : α ≠ 0) (hne : α ≠ β) (hx : x = β) (hy : y = β) :
    ¬ Triple3 x y z α β (2 * α + β) := by
  subst hx hy
  rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
  all_goals first | exact hne h1.symm | exact hne h2.symm | exact hα (by linarith)

theorem w_hne : α44 ≠ β44 := by
  intro e
  apply α44_irr ⟨1 / 5, ?_⟩
  have := three_α_two_β
  push_cast; linarith

theorem w_hne0 : α44 ≠ 0 := fun e => α44_irr ⟨0, by rw [e]; simp⟩

theorem w_e0 : Erdos634.Tiling44Bridge.dissection.target.angleAt 0 = β44 := t_angle0

theorem w_e1 : Erdos634.Tiling44Bridge.dissection.target.angleAt 1 = β44 := t_angle1

theorem w_ns : ¬ Triple3 (Erdos634.Tiling44Bridge.dissection.target.angleAt 0)
    (Erdos634.Tiling44Bridge.dissection.target.angleAt 1) (Erdos634.Tiling44Bridge.dissection.target.angleAt 2)
    α44 β44 (2 * α44 + β44) := aux_not_triple3 w_hne0 w_hne w_e0 w_e1

theorem beeson_thm9_wit : ∃ (N : ℕ) (D : CongruentDissection N) (α β a b c : ℝ), 3 * α + 2 * β = Real.pi ∧
    D.model.ThreeAlphaData α β a b c ∧
    ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β) ∧ Comm a b ∧ Comm a c :=
  ⟨Tiling44.tiles.length, Erdos634.Tiling44Bridge.dissection, α44, β44, 16, 24, 32, three_α_two_β,
    Erdos634.Draft.FluxRow11Witness.data44, w_ns,
    beeson_thm9 Erdos634.Tiling44Bridge.dissection three_α_two_β Erdos634.Draft.FluxRow11Witness.data44 w_ns⟩

end Erdos634.Draft.ZhangRat10Thm9
#print axioms Erdos634.Draft.ZhangRat10Thm9.beeson_thm9_wit
