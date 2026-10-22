-- Draft/SixTiles.lean — CongruentDissection 6 (equilateral triangle -> 3 tiles (30,30,120) ->
-- each cut by its altitude into 2 tiles (30,60,90)), the cevian-split lemma applied via
-- RefineTiles, and 6k² for all k ≥ 1.  UNAUDITED.
-- Imported via AllNew8.lean:394 → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Draft.RefineTiles
import Erdos634.Draft.Equilateral3
import Erdos634.Draft.RAAssemble

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.RWGlue Erdos634.Draft.RWPieces
  Erdos634.Draft.RAAssemble Erdos634.Draft.SumTwoSquares
open Erdos634.RouteOneCrossing (selfDissection)

namespace Erdos634.Draft.SixTiles

/-- The (30,30,120) tile cut by its altitude: `CongruentDissection 2` of `mkTri 3 r 0 0 6 0`
(same triangle as `mkTri 0 0 6 0 3 r`, vertices rotated), model the (30,60,90) half. -/
theorem altitude_split (r : ℝ) (hr0 : 0 < r) (hr2 : r ^ 2 = 3)
    (dT : det3 3 r 0 0 6 0 ≠ 0) :
    ∃ E : CongruentDissection 2, E.target = mkTri 3 r 0 0 6 0 dT := by
  have d1 : det3 3 r 0 0 3 0 ≠ 0 := by unfold det3; nlinarith
  have d2 : det3 3 r 3 0 6 0 ≠ 0 := by unfold det3; nlinarith
  set T : Tri := mkTri 3 r 0 0 6 0 dT
  set T1 : Tri := mkTri 3 r 0 0 3 0 d1
  set T2 : Tri := mkTri 3 r 3 0 6 0 d2
  have hc : T2.Congruent T1 := by
    refine (T2.congruent_relabel (Equiv.swap (1 : Fin 3) 2)).trans ?_
    refine SssCongruent.congruent_of_dist_three ?_ ?_ ?_
    · show dist (mkPt (3 : ℝ) r) (mkPt 6 0) = dist (mkPt (3 : ℝ) r) (mkPt 0 0)
      exact eqsq dist_nonneg dist_nonneg (by rw [dist_sq_mkPt, dist_sq_mkPt]; nlinarith)
    · show dist (mkPt (6 : ℝ) 0) (mkPt 3 0) = dist (mkPt (0 : ℝ) 0) (mkPt 3 0)
      exact eqsq dist_nonneg dist_nonneg (by rw [dist_sq_mkPt, dist_sq_mkPt]; nlinarith)
    · show dist (mkPt (3 : ℝ) 0) (mkPt 3 r) = dist (mkPt (3 : ℝ) 0) (mkPt 3 r)
      rfl
  set D1 : CongruentDissection 1 :=
    { toDissection := selfDissection T1, model := T1, tiles_congruent := fun _ => Tri.Congruent.refl T1 }
  set D2 : CongruentDissection 1 :=
    { toDissection := selfDissection T2, model := T1, tiles_congruent := fun _ => hc }
  have hlm : AffineMap.lineMap (mkPt (0 : ℝ) 0) (mkPt 6 0) (1 / 2 : ℝ) = mkPt 3 0 := by
    rw [lm]; congr 1 <;> norm_num
  obtain ⟨D, hD, -⟩ := glue_two T T1 T2 (1 / 2) (by norm_num) (by norm_num)
    (by show mkPt (3 : ℝ) r = mkPt 3 r; rfl) (by show mkPt (0 : ℝ) 0 = mkPt 0 0; rfl)
    (by show mkPt (3 : ℝ) 0 = AffineMap.lineMap (mkPt (0 : ℝ) 0) (mkPt 6 0) (1 / 2); rw [hlm])
    (by show mkPt (3 : ℝ) r = mkPt 3 r; rfl)
    (by show mkPt (3 : ℝ) 0 = AffineMap.lineMap (mkPt (0 : ℝ) 0) (mkPt 6 0) (1 / 2); rw [hlm])
    (by show mkPt (6 : ℝ) 0 = mkPt 6 0; rfl)
    D1 D2 (Tri.Congruent.refl _) (Tri.Congruent.refl _) (Tri.Congruent.refl _)
  exact ⟨D, hD⟩

/-- **Six tiles.** -/
theorem exists_dissection_6 : Nonempty (CongruentDissection 6) := by
  obtain ⟨D, hd0, hDm⟩ := Erdos634.Draft.Equilateral3.exists_dissection_3_model
  set r : ℝ := Real.sqrt 3 with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by norm_num)
  have hr2 : r ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have dT : det3 3 r 0 0 6 0 ≠ 0 := by unfold det3; nlinarith
  obtain ⟨E, hE⟩ := altitude_split r hr0 hr2 dT
  have hcong : D.model.Congruent E.target := by
    rw [hDm, hE]
    refine ⟨IsometryEquiv.refl _, finRotate 3, fun k => ?_⟩
    fin_cases k <;> rfl
  obtain ⟨F, -⟩ := Erdos634.Draft.RefineTiles.refine_congruent D E hcong
  exact ⟨F⟩

end Erdos634.Draft.SixTiles

#print axioms Erdos634.Draft.SixTiles.exists_dissection_6
