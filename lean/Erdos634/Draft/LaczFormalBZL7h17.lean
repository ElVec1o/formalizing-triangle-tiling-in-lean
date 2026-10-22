-- Draft/LaczFormalBZL7h17.lean -- NON-VACUITY of `beeson_thm107_proved` (BZL7h16): the certified 1125-tiling of the isosceles (150,150,225)*16 triangle by the tile (4,5,6)*16 (Herdt/Zhang; `G3GControl.D`)
-- meets EVERY hypothesis (angles (alpha, pi-3 alpha, 2 alpha) after relabelling, alpha not in Q pi, polygon corner angles alpha / pi - 2 alpha, a corner of each kind), so the theorem applies to it
-- (its conclusion, rational sides, holds there: (4,5,6) is rational).  NOTE, UNAUDITED.
-- Credit: Beeson (arXiv 1206.1974v7), Herdt, Zhang (the 1125-tiling), Beeson-Zhang, Laczkovich.
import Erdos634.Draft.LaczFormalBZL7h16
import Erdos634.Draft.LaczFormalBZL7f3

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

open Erdos634.Draft.G3GControl

theorem witness_1125_thm107 : ∃ (N : ℕ) (C : CongruentRegionDissection N), ∃ r s : ℚ, slen C 0 = (r : ℝ) * slen C 1 ∧ slen C 2 = (s : ℝ) * slen C 0 := by
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := data
  set C := relabel D.toRegion σ with hC
  have hA : C.model.angleAt 0 = α := (relabel_angleAt D.toRegion σ 0).trans h0
  have hB : C.model.angleAt 1 = Real.pi - 3 * C.model.angleAt 0 := by rw [hA]; exact (relabel_angleAt D.toRegion σ 1).trans h1
  have hG : C.model.angleAt 2 = 2 * C.model.angleAt 0 := by rw [hA]; exact (relabel_angleAt D.toRegion σ 2).trans h2
  have hirr : ¬ ∃ r : ℚ, C.model.angleAt 0 = (r : ℝ) * Real.pi := by rw [hA]; exact α_irr
  obtain ⟨P, hPc, τ, hPa, -⟩ := exists_convpoly_of_tri' D.target
  have hreg : C.region = P.carrier := hPc.symm
  have hsum := Erdos634.Draft.LaczFormal.angleAt_sum D.target
  have t2 : D.target.angleAt 2 = Real.pi - 2 * α := by linarith [t_ang0, t_ang1, hsum]
  have hang : ∀ j : Fin 3, D.target.angleAt j = α ∨ D.target.angleAt j = Real.pi - 2 * α := by
    intro j; fin_cases j
    · exact Or.inl t_ang0
    · exact Or.inl t_ang1
    · exact Or.inr t2
  obtain ⟨k0, hk0⟩ := τ.surjective 2
  obtain ⟨kA, hkA⟩ := τ.surjective 0
  refine ⟨_, C, beeson_thm107_proved C P hreg hB hG hirr ?_ (k0 - 1) ?_ (kA - 1) ?_⟩
  · intro k
    rw [hPa, hA]; exact hang _
  · rw [hPa]; simp only [sub_add_cancel]; rw [hk0, hA]; exact t2
  · rw [hPa]; simp only [sub_add_cancel]; rw [hkA, hA]; exact t_ang0

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.witness_1125_thm107
