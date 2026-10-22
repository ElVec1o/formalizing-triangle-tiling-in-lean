import Erdos634.Draft.ZhangRat3Prop11
import Erdos634.Draft.LaczFormalThm21Area

/-!
# The tile count of a region is determined (area count), for Zhang Prop 11

`tiledis_count_unique`: if a set `S` is tiled by `n` and by `n'` copies of the same tile `R`, then
`n = n'` (area additivity `volume_region_eq`: `volume S = n * volume R.Δ`, and `0 < volume R.Δ < ∞`).
Consequence (`tiledis_count_formula`): in Zhang's Prop 11 the hypothesis count `n0` is not a free
parameter; any `n0` with `TileDis R S n0` equals any other tile count of `S`.  UNAUDITED.
Credit Zhang (arXiv 2512.22696v4), Beeson, Beeson-Zhang, Laczkovich.
-/

namespace Erdos634.ZhangRat4

open MeasureTheory Erdos634.Geometry Erdos634.RegionDissection Erdos634.ZhangRat3 Erdos634.LaczL22
open scoped ENNReal

theorem tileDis_volume (R : RTri) {S : Set Plane} {n : ℕ} (h : TileDis R S n) :
    volume S = (n : ℝ≥0∞) * volume R.Δ.carrier := by
  obtain ⟨C, hr, hm⟩ := h
  rw [← hr, Erdos634.Draft.LaczFormal.Thm21.volume_region_eq C.toRegionDissection]
  have : ∀ i, volume (C.tile i).carrier = volume R.Δ.carrier := fun i =>
    (Erdos634.CongruentArea.volume_congruent (C.tiles_congruent i)).trans
      (Erdos634.CongruentArea.volume_congruent hm)
  simp [this]

theorem tiledis_count_unique (R : RTri) {S : Set Plane} {n n' : ℕ} (h : TileDis R S n)
    (h' : TileDis R S n') : n = n' := by
  have e := (tileDis_volume R h).symm.trans (tileDis_volume R h')
  have hpos : volume R.Δ.carrier ≠ 0 := R.Δ.volume_pos.ne'
  have hfin : volume R.Δ.carrier ≠ ⊤ := by
    rw [Erdos634.Draft.LaczFormal.Thm21.volume_tri_eq]; exact ENNReal.ofReal_ne_top
  have := (ENNReal.mul_left_inj hpos hfin).mp e
  exact_mod_cast this

end Erdos634.ZhangRat4

#print axioms Erdos634.ZhangRat4.tiledis_count_unique
