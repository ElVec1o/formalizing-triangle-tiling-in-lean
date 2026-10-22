-- Draft/LaczFormalBZL7f3.lean -- NON-VACUITY WITNESS for `exists_center_a2` (Beeson arXiv 1206.1974v7 Lemma 10.2): the certified 1125-tiling of the isosceles (150,150,225)*16 triangle by the tile
-- (4,5,6)*16 (Herdt/Zhang; `G3GControl.D`) satisfies every hypothesis (model relabelled to angles (alpha, pi-3 alpha, 2 alpha), target as a ConvPoly with corner angles alpha or pi - 2 alpha,
-- alpha not in Q pi, fans from the polygon), and `exists_center_a2` yields a tiling vertex with corner counts (0,2,3).
-- NOTE, UNAUDITED.  Credit: Beeson (arXiv 1206.1974v7), Herdt, Zhang (the 1125-tiling), Beeson-Zhang, Laczkovich.
import Erdos634.Draft.LaczFormalBZL7e1
import Erdos634.Draft.LaczFormalBZL7d5b
import Erdos634.Draft.G3GControl

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

open Erdos634.Draft.G3GControl

theorem witness_1125_center : ∃ (N : ℕ) (C : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)),
    ∃ v ∈ vtxSet C.toRegionDissection, cnt C idx v 0 = 0 ∧ cnt C idx v 1 = 2 ∧ cnt C idx v 2 = 3 := by
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := data
  set C := relabel D.toRegion σ with hC
  have hA : C.model.angleAt 0 = α := (relabel_angleAt D.toRegion σ 0).trans h0
  have hB : C.model.angleAt 1 = Real.pi - 3 * C.model.angleAt 0 := by rw [hA]; exact (relabel_angleAt D.toRegion σ 1).trans h1
  have hG : C.model.angleAt 2 = 2 * C.model.angleAt 0 := by rw [hA]; exact (relabel_angleAt D.toRegion σ 2).trans h2
  have hirr : ¬ ∃ r : ℚ, C.model.angleAt 0 = (r : ℝ) * Real.pi := by rw [hA]; exact α_irr
  obtain ⟨P, hPc, τ, hPa, -⟩ := exists_convpoly_of_tri' D.target
  have hreg : C.region = P.carrier := hPc.symm
  haveI : HasFansC C.toRegionDissection := hasFansC_poly _ P hreg
  obtain ⟨idx, -, hidxA⟩ := exists_idx_both C
  have hsum := Erdos634.Draft.LaczFormal.angleAt_sum D.target
  have t2 : D.target.angleAt 2 = Real.pi - 2 * α := by linarith [t_ang0, t_ang1, hsum]
  have hang : ∀ j : Fin 3, D.target.angleAt j = α ∨ D.target.angleAt j = Real.pi - 2 * α := by
    intro j; fin_cases j
    · exact Or.inl t_ang0
    · exact Or.inl t_ang1
    · exact Or.inr t2
  obtain ⟨k0, hk0⟩ := τ.surjective 2
  refine ⟨_, C, idx, exists_center_a2 C P hreg idx hidxA hB hG hirr ?_ (k0 - 1) ?_⟩
  · intro k
    rw [hPa, hA]; exact hang _
  · rw [hPa]; simp only [sub_add_cancel]; rw [hk0, hA]; exact t2
end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.witness_1125_center
