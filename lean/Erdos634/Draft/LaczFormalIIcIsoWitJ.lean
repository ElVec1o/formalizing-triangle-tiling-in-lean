-- Draft/LaczFormalIIcIsoWitJ.lean -- NON-VACUITY witness for `IIcIsoCore`, step J: the four tile steps along the diameter through each vertex.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcIsoWitI

open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Thm21 Erdos634.Draft.LaczFormal.RG Erdos634.Draft.LaczFormal.Graph

namespace Erdos634.Draft.LaczFormal.IsoWit

theorem tp0 (i : Fin 8) : (tile i).pts 0 = oct.v i := rfl
theorem tp1 (i : Fin 8) : (tile i).pts 1 = oct.v (i + 1) := rfl
theorem tp2 (i : Fin 8) : (tile i).pts 2 = mkPt 0 0 := rfl
theorem O0 : (mkPt 0 0 : Plane) 0 = 0 := mkPt_zero _ _
theorem O1 : (mkPt 0 0 : Plane) 1 = 0 := mkPt_one _ _

theorem par_rad (j : Fin 8) (a b : ℝ) (ha : a = - cx j) (hb : b = - cy j) : Par (a, b) (dvec j) := by
  have := cxy_sq j
  subst ha hb
  constructor
  · unfold crs dvec; simp; ring
  · unfold dt dvec; simp; nlinarith

theorem stepA (j : Fin 8) : TriStep (tile (j - 1)) (dvec j) (oct.v j) (mkPt 0 0) := by
  refine ⟨1, 2, 0, ?_, tp2 _, by decide, by decide, by decide, ?_, ?_⟩
  · rw [tp1, sub_add_cancel]
  · show Par ((mkPt 0 0 : Plane) 0 - (oct.v j) 0, (mkPt 0 0 : Plane) 1 - (oct.v j) 1) _
    rw [O0, O1, oct_v0, oct_v1]
    exact par_rad j _ _ (by ring) (by ring)
  · show 0 < crs (dvec j) ((((tile (j - 1)).pts 0) 0 - (oct.v j) 0), (((tile (j - 1)).pts 0) 1 - (oct.v j) 1))
    simp only [tp0, oct_v0, oct_v1]
    have h := cr_1 (j - 1)
    rw [sub_add_cancel] at h
    unfold cr at h
    unfold crs dvec
    simp only
    nlinarith [hh_pos]

theorem stepB (j : Fin 8) : TriStep (tile (j + 4)) (dvec j) (mkPt 0 0) (oct.v (j + 4)) := by
  refine ⟨2, 0, 1, tp2 _, tp0 _, by decide, by decide, by decide, ?_, ?_⟩
  · show Par ((oct.v (j + 4)) 0 - (mkPt 0 0 : Plane) 0, (oct.v (j + 4)) 1 - (mkPt 0 0 : Plane) 1) _
    rw [O0, O1, oct_v0, oct_v1, cx_add4, cy_add4]
    exact par_rad j _ _ (by ring) (by ring)
  · show 0 < crs (dvec j) ((((tile (j + 4)).pts 1) 0 - (mkPt 0 0 : Plane) 0), (((tile (j + 4)).pts 1) 1 - (mkPt 0 0 : Plane) 1))
    rw [tp1, O0, O1, oct_v0, oct_v1]
    have h := cr_5 j
    have e : j + 4 + 1 = j + 5 := (by decide : ∀ a : Fin 8, a + 4 + 1 = a + 5) j
    rw [e]
    unfold cr at h
    unfold crs dvec
    simp only
    nlinarith [hh_pos]

theorem stepC (j : Fin 8) : TriStep (tile j) (neg2 (dvec j)) (mkPt 0 0) (oct.v j) := by
  refine ⟨2, 0, 1, tp2 _, tp0 _, by decide, by decide, by decide, ?_, ?_⟩
  · show Par ((oct.v j) 0 - (mkPt 0 0 : Plane) 0, (oct.v j) 1 - (mkPt 0 0 : Plane) 1) _
    rw [O0, O1, oct_v0, oct_v1]
    have := cxy_sq j
    constructor
    · unfold crs neg2 dvec; simp; ring
    · unfold dt neg2 dvec; simp; nlinarith
  · show 0 < crs (neg2 (dvec j)) ((((tile j).pts 1) 0 - (mkPt 0 0 : Plane) 0), (((tile j).pts 1) 1 - (mkPt 0 0 : Plane) 1))
    rw [tp1, O0, O1, oct_v0, oct_v1]
    have h := cr_1 j
    unfold cr at h
    unfold crs neg2 dvec
    simp only
    nlinarith [hh_pos]

theorem stepD (j : Fin 8) : TriStep (tile (j + 3)) (neg2 (dvec j)) (oct.v (j + 4)) (mkPt 0 0) := by
  refine ⟨1, 2, 0, ?_, tp2 _, by decide, by decide, by decide, ?_, ?_⟩
  · rw [tp1]; congr 1; exact (by decide : ∀ a : Fin 8, a + 3 + 1 = a + 4) j
  · show Par ((mkPt 0 0 : Plane) 0 - (oct.v (j + 4)) 0, (mkPt 0 0 : Plane) 1 - (oct.v (j + 4)) 1) _
    rw [O0, O1, oct_v0, oct_v1, cx_add4, cy_add4]
    have := cxy_sq j
    constructor
    · unfold crs neg2 dvec; simp; ring
    · unfold dt neg2 dvec; simp; nlinarith
  · show 0 < crs (neg2 (dvec j)) ((((tile (j + 3)).pts 0) 0 - (oct.v (j + 4)) 0), (((tile (j + 3)).pts 0) 1 - (oct.v (j + 4)) 1))
    rw [tp0, oct_v0, oct_v1, oct_v0, oct_v1, cx_add4, cy_add4]
    have h := cr_3 j
    unfold cr at h
    unfold crs neg2 dvec
    simp only
    nlinarith [hh_pos]

end Erdos634.Draft.LaczFormal.IsoWit
