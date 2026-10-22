-- Draft/LaczFormalIIcIsoWitB.lean -- NON-VACUITY witness for `IIcIsoCore`, step B: the octagon `ConvPoly 8`, the eight tiles, covering, disjointness, congruence, `CongruentRegionDissection 8`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcIsoWitA
import Erdos634.CertGeom
import Erdos634.SssCongruent
import Erdos634.RegionDissection

open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Thm21

namespace Erdos634.Draft.LaczFormal.IsoWit

theorem hdet (i : Fin 8) : det3 (cx i) (cy i) (cx (i + 1)) (cy (i + 1)) 0 0 ≠ 0 := by
  have h := cr_1 i
  have : det3 (cx i) (cy i) (cx (i + 1)) (cy (i + 1)) 0 0 = hh := by
    rw [← h]; unfold det3 cr; ring
  rw [this]; exact hh_pos.ne'

/-- tile `i`: apex `O` (pts 2), base vertices `V i` (pts 0), `V (i+1)` (pts 1). -/
noncomputable def tile (i : Fin 8) : Tri := mkTri (cx i) (cy i) (cx (i + 1)) (cy (i + 1)) 0 0 (hdet i)

theorem tile_pts (i : Fin 8) : (tile i).pts = ![mkPt (cx i) (cy i), mkPt (cx (i + 1)) (cy (i + 1)), mkPt 0 0] := rfl

/-- the regular octagon -/
noncomputable def oct : ConvPoly 8 where
  v := fun k => mkPt (cx k) (cy k)
  three_le := by norm_num
  left := by
    intro i j hji hji1
    have := hh_pos; have := hh_sq
    fin_cases i <;> fin_cases j <;> first | (exfalso; revert hji hji1; decide) | (simp [cross2, mkPt, cx, cy] <;> nlinarith)

theorem mem_oct (x : Plane) : x ∈ oct.carrier ↔ ∀ k : Fin 8, 0 ≤ (cx (k + 1) - cx k) * (x 1 - cy k) - (x 0 - cx k) * (cy (k + 1) - cy k) := by
  unfold ConvPoly.carrier
  simp only [Set.mem_setOf_eq]
  refine forall_congr' fun k => ?_
  simp [oct, cross2, mkPt]
  constructor <;> intro h <;> linarith

/-- the edge functional of the octagon at the vertices of the tiles -/
noncomputable def E (k : Fin 8) (a b : ℝ) : ℝ := (cx (k + 1) - cx k) * (b - cy k) - (a - cx k) * (cy (k + 1) - cy k)

theorem E_V (k i : Fin 8) : 0 ≤ E k (cx i) (cy i) := by
  have := hh_pos; have := hh_sq
  unfold E
  fin_cases k <;> fin_cases i <;> simp [cx, cy] <;> nlinarith
theorem E_O (k : Fin 8) : 0 ≤ E k 0 0 := by
  have := hh_pos; have := hh_sq
  unfold E
  fin_cases k <;> simp [cx, cy] <;> nlinarith

theorem tile_sub (i : Fin 8) : (tile i).carrier ⊆ oct.carrier := by
  intro x hx
  rw [mem_oct]
  intro k
  have key := Erdos634.CertGeom.le_of_forall_pts_le (Erdos634.CertGeom.lineFun (cx (k + 1)) (cy (k + 1)) (cx k) (cy k)) (c := 0) (t := tile i) ?_ x hx
  · simp only [Erdos634.CertGeom.lineFun_apply] at key
    nlinarith [key]
  · intro m
    have h0 := E_V k i
    have h1 := E_V k (i + 1)
    have h2 := E_O k
    unfold E at h0 h1 h2
    fin_cases m
    · simp [tile_pts, Erdos634.CertGeom.lineFun_apply]; nlinarith
    · simp [tile_pts, Erdos634.CertGeom.lineFun_apply]; nlinarith
    · simp [tile_pts, Erdos634.CertGeom.lineFun_apply]; nlinarith

end Erdos634.Draft.LaczFormal.IsoWit
