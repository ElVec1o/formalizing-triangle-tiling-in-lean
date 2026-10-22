-- Draft/LaczFormalRG12ShapeTileWit.lean -- NON-VACUITY of `pair_shape_tiles`: on the two-tile parallelogram of the 30-60-90 tile `(2, 1, sqrt 3)` all hypotheses hold (shared diagonal `c = sqrt 3` between tile 0 and tile 1,
-- `slen 0 = 2 != sqrt 3`, `slen 1 = 1 != sqrt 3`), and the conclusion (kite or parallelogram) is obtained.  2-tile caveat.  NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Lemma 4.8), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12ShapeTile
import Erdos634.Draft.LaczFormalRG10Lemma48Wit

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

theorem pair_shape_witness : ∃ (i j : Fin 2) (d : V2) (U V : Plane), TriStep (vTiling.C.tile i) d U V ∧ TriStep (vTiling.C.tile j) (neg2 d) V U ∧ dist U V = slen vTiling.C 2 := by
  have hv := vT_pos
  have hS : TriStep (vTiling.C.tile 0) (0, vT) (mkPt 1 0) (mkPt 1 vT) := by
    refine ⟨0, 1, 2, rfl, rfl, by decide, by decide, by decide, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · simp [crs, toV2, mkPt]
      · simp [dt, toV2, mkPt]; positivity
    · show 0 < crs (0, vT) (toV2 (mkPt 0 0 - mkPt 1 0))
      simp [crs, toV2, mkPt]; exact hv
  have hc : dist (mkPt 1 0) (mkPt 1 vT) = slen vTiling.C 2 := by
    rw [vDiss_slen2]
    rw [EuclideanSpace.dist_eq]
    simp [Fin.sum_univ_two, mkPt, vT]
  obtain ⟨j, -, hj⟩ := lemma48_witness
  exact ⟨0, j, _, _, _, hS, hj, hc⟩

theorem pair_shape_witness_concl : ∃ kk f g kk' f' g' : Fin 3, True := by
  obtain ⟨i, j, d, U, V, h1, h2, h3⟩ := pair_shape_witness
  obtain ⟨idx, hidx⟩ := exists_idx_len vTiling.C
  have h0 : slen vTiling.C 0 ≠ slen vTiling.C 2 := by
    have := vTiling_notComm; intro h; apply this; rw [h]; exact ⟨1, 1, by norm_num, by norm_num, by simp⟩
  have h1' : slen vTiling.C 1 ≠ slen vTiling.C 2 := by
    rw [vDiss_slen1, vDiss_slen2]
    intro h
    have : (1 : ℝ) = Real.sqrt 3 := h
    have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    rw [← this] at h3; norm_num at h3
  obtain ⟨kk, f, g, kk', f', g', -⟩ := pair_shape_tiles vTiling.C idx hidx h0 h1' h1 h2 h3
  exact ⟨kk, f, g, kk', f', g', trivial⟩

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.pair_shape_witness_concl
