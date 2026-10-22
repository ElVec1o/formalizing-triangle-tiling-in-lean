-- Draft/LaczFormalL10.lean -- atom L10, the pieces that do not need the commensurable classification (L9):
-- (1) Table 3 line 2 (right tile with an irrational angle, isosceles target (beta,beta,2alpha)): N is even
--     (Beeson "Seven" / Beeson-Rosu Table 3 line 2 + Remark), assembled from `Row3.RP.row3_RP_even_any_label`;
-- (2) the equilateral-target N formulas are `LaczFormalL6Rat.equilateral_tile_i/ii/iii` (with witnesses).
-- UNAUDITED.  Credit: Beeson, Beeson-Rosu.
import Erdos634.Draft.LaczFormalL5
import Erdos634.Draft.FluxGRow3RPAnyLabel
import Erdos634.Draft.FluxGRow3RPWitness

open scoped Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
  Erdos634.Draft.LemmaCFinal

namespace Erdos634.Draft.LaczFormal

theorem irrational_of_irrPi {α : ℝ} (h : IrrPi α) : Irrational (α / Real.pi) := by
  rintro ⟨q, hq⟩
  exact h ⟨q, (div_eq_iff Real.pi_pos.ne').mp hq.symm⟩

/-- **Right tile, isosceles target (Table 3 line 2): `N` is even.** Tile angles `(α, β, π/2)` with
`α ∉ ℚπ`, target angles `(β, β, 2α)`. -/
theorem right_tile_even {N : ℕ} (D : CongruentDissection N) {α β : ℝ} (hα : IrrPi α)
    (hT : TileAngles D α β (Real.pi / 2)) (hB : TgtAngles D β β (2 * α)) : Even N := by
  obtain ⟨σ, h0, h1, h2⟩ := hT
  obtain ⟨σ', g0, g1, -⟩ := hB
  have d01 : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
  have d02 : σ 0 ≠ σ 2 := σ.injective.ne (by decide)
  have d12 : σ 1 ≠ σ 2 := σ.injective.ne (by decide)
  have h3 : D.model.angleAt (σ 0) + D.model.angleAt (σ 1) + D.model.angleAt (σ 2)
      = D.model.angleAt 0 + D.model.angleAt 1 + D.model.angleAt 2 :=
    sum3 (fun m => D.model.angleAt m) _ _ _ d01 d02 d12
  have hs := angleAt_sum D.model
  have hpa : 0 < α := h0 ▸ Erdos634.MarchFlank.cornerAngle_pos D.model (σ 0)
  have hpb : 0 < β := h1 ▸ Erdos634.MarchFlank.cornerAngle_pos D.model (σ 1)
  rw [h0, h1, h2] at h3
  have hβ : β = Real.pi / 2 - α := by linarith
  exact Erdos634.Geometry.Row3.RP.row3_RP_even_any_label D hpa (by linarith)
    (irrational_of_irrPi hα) d02 h0 h2 (Or.inr hβ) (σ'.injective.ne (by decide : (0 : Fin 3) ≠ 1)) g0 g1

open Erdos634.Draft.FluxGRow3RPWitness Erdos634.Draft.FluxGRow3AngleWitnessDissection
  Erdos634.Draft.FluxGRow3WitnessBridge Erdos634.Draft.FluxGRow3SharedGrid
  Erdos634.Draft.FluxGRow3Step3N2Final Erdos634.Geometry.Row3 in
/-- **Non-vacuity of `right_tile_even`**: all its hypotheses hold jointly on the real
`CongruentDissection 2` of `FluxGRow3RPWitness` (right isosceles-base tile, `cos α = 3/4`), and the
theorem fires (`Even 2`). -/
theorem right_tile_even_witness : Even 2 := by
  have hirr : IrrPi Erdos634.Draft.FluxRow4Witness.α456 := irrPi_of_irrational α456_div_pi_irr
  have hT := (tile_of_two dissection' 0 2 (by decide) _ (Real.pi / 2) model'_angleAt0
    tile0'_angleAt2).swap23.swap
  have hB := tgt_of_two dissection' 0 1 (by decide) _ target_angleAt0 target_angleAt1
  have hr : IrrPi (Real.pi - Erdos634.Draft.FluxRow4Witness.α456 - Real.pi / 2) :=
    irr_transfer _ _ (-1) (1 / 2) (by push_cast; ring) hirr
  exact right_tile_even dissection' hr hT (tgt_congr3 hB (by ring))

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.right_tile_even
#print axioms Erdos634.Draft.LaczFormal.right_tile_even_witness
