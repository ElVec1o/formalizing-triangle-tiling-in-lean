-- Draft/LaczFormalRG10Lemma48Wit.lean -- NON-VACUITY of Lemma 4.8 (`polytiling_lemma48`): on the two-triangle parallelogram of the 30-60-90 tile `(2, 1, sqrt 3)` (regular, `a, b` commensurable, `c` not commensurable with `a`)
-- the shared diagonal has length `c = sqrt 3` and its midpoint is interior; the hypotheses hold and the conclusion (the second tile on the other side with the same side) is obtained.
-- Caveat: a 2-tile tiling, so the maximal-segment and fan steps are not exercised nontrivially.  UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Lemma 4.8), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG10Lemma48
import Erdos634.Draft.LaczFormalRG6IVcWit

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

theorem vTiling_mid_interior : mkPt 1 (vT / 2) ∈ interior vTiling.C.region := by
  have c0 : Continuous (fun x : Plane => x 0) := (EuclideanSpace.proj (0 : Fin 2)).continuous
  have c1 : Continuous (fun x : Plane => x 1) := (EuclideanSpace.proj (1 : Fin 2)).continuous
  have hO : IsOpen {x : Plane | 0 < x 1 ∧ x 1 < vT ∧ 0 < vT * x 0 - 1 * x 1 ∧ 0 < vT * (1 - x 0) + 1 * x 1} := by
    refine (isOpen_lt continuous_const c1).inter ((isOpen_lt c1 continuous_const).inter
      ((isOpen_lt continuous_const ((continuous_const.mul c0).sub (continuous_const.mul c1))).inter
        (isOpen_lt continuous_const ((continuous_const.mul (continuous_const.sub c0)).add (continuous_const.mul c1)))))
  have hsub : {x : Plane | 0 < x 1 ∧ x 1 < vT ∧ 0 < vT * x 0 - 1 * x 1 ∧ 0 < vT * (1 - x 0) + 1 * x 1} ⊆ vTiling.C.region := by
    intro x hx
    show x ∈ (parPoly 1 1 vT one_pos vT_pos).carrier
    rw [parPoly_carrier one_pos vT_pos]
    obtain ⟨h1, h2, h3, h4⟩ := hx
    exact ⟨h1.le, h2.le, h3.le, h4.le⟩
  apply interior_maximal hsub hO
  have := vT_pos
  have h1 : (mkPt 1 (vT / 2)) 0 = 1 := by simp [mkPt]
  have h2 : (mkPt 1 (vT / 2)) 1 = vT / 2 := by simp [mkPt]
  simp only [Set.mem_setOf_eq]
  rw [h1, h2]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem lemma48_witness : ∃ j : Fin 2, j ≠ 0 ∧ TriStep (vTiling.C.tile j) (neg2 (0, vT)) (mkPt 1 vT) (mkPt 1 0) := by
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
  have hm : mkPt 1 (vT / 2) ∈ openSegment ℝ (mkPt 1 0) (mkPt 1 vT) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext j; fin_cases j <;> simp [mkPt] <;> ring
  exact polytiling_lemma48 vTiling (pDiss_regular one_pos vT_pos) vTiling_comm vTiling_notComm hS hc hm vTiling_mid_interior

end Erdos634.Draft.LaczFormal.RG
