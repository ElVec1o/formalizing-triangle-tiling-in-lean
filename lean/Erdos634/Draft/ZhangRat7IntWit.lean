import Erdos634.Draft.ZhangRat7Int
import Erdos634.Draft.EqSemigroup

/-!
# Witness for `ZhangRat7Int.lemma3_geom`: the 240-tile dissection of the equilateral triangle of side 60 by
`(3, 5, 7)` (`EqSemigroup.eqD_60`) satisfies every hypothesis (model sides `(3,5,7)` in the `RTri` order, target
equilateral).  UNAUDITED.  Credit Zhang (arXiv 2512.22696v4), Beeson, Beeson-Zhang.
-/

set_option maxHeartbeats 3200000

open Erdos634.Geometry Erdos634.CertCoord
namespace Erdos634.ZhangRat7IntWit
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.S2G Erdos634.Draft.S2AllTheta
open Erdos634.TilePlacement
open Erdos634.Draft.EqSemigroup (Mod357 Mod_12 Mod_20 Mod_01 dPhi1 EqD eqTri eqD_60)

theorem sideOpp_eqTri (L : ℕ) (hL : 0 < L) (j : Fin 3) : sideOpp (eqTri L hL) j = L := by
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  fin_cases j
  · show dist ((eqTri L hL).pts 1) ((eqTri L hL).pts 2) = L
    simp only [eqTri, triC_pts]
    exact dPhi1 _ _ _ hL0 (by ring)
  · show dist ((eqTri L hL).pts 2) ((eqTri L hL).pts 0) = L
    simp only [eqTri, triC_pts]
    exact dPhi1 _ _ _ hL0 (by ring)
  · show dist ((eqTri L hL).pts 0) ((eqTri L hL).pts 1) = L
    simp only [eqTri, triC_pts]
    exact dPhi1 _ _ _ hL0 (by ring)

theorem lemma3_wit : ∃ m : ℕ, ((60 : ℕ) : ℝ) = (m * (3 * 5) : ℕ) := by
  obtain ⟨-, hL, D, hM, hT⟩ := eqD_60
  refine Erdos634.ZhangRat7Int.zhang_lemma3_geom 3 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    Nat.prime_three.squarefree Nat.prime_five.squarefree D (by norm_num) ?_ ?_ ?_ ((60 : ℕ) : ℝ) ?_
  · rw [hM]; exact_mod_cast Mod_12
  · rw [hM]; exact_mod_cast Mod_20
  · rw [hM]; exact_mod_cast Mod_01
  · intro j; rw [hT]; exact sideOpp_eqTri 60 hL j

end Erdos634.ZhangRat7IntWit

#print axioms Erdos634.ZhangRat7IntWit.lemma3_wit
