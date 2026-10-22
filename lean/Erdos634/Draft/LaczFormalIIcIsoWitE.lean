-- Draft/LaczFormalIIcIsoWitE.lean -- NON-VACUITY witness for `IIcIsoCore`, step E: the labelling `idx = id`, `CaseC` data (hidx, hidxA, hregc), corner counts (1,1,0) at the polygon vertices.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcIsoWitD
import Erdos634.Draft.LaczFormalIIcIsoK

open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Thm21 Erdos634.Draft.LaczFormal.RG

namespace Erdos634.Draft.LaczFormal.IsoWit

theorem tile_dist (i : Fin 8) (m n : Fin 3) : dist ((tile i).pts m) ((tile i).pts n) = dist ((tile 0).pts m) ((tile 0).pts n) := by
  obtain ⟨f, σ, hf⟩ := tile_cong i
  have := hh_sq; have := hh_pos
  apply Erdos634.SssCongruent.dist_of_sq
  fin_cases i <;> fin_cases m <;> fin_cases n <;> simp [tile_pts, dist_sq_mkPt, cx, cy] <;> nlinarith

theorem cornerAngle_of_dists {p q r p' q' r' : Plane} (h1 : dist p q = dist p' q') (h2 : dist r q = dist r' q')
    (h3 : dist p r = dist p' r') (ha : 0 < dist p q) (hb : 0 < dist r q) : cornerAngle p q r = cornerAngle p' q' r' := by
  have l1 := EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle p q r
  have l2 := EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle p' q' r'
  rw [← h1, ← h2, ← h3] at l2
  have hc : Real.cos (EuclideanGeometry.angle (V := Plane) p q r) = Real.cos (EuclideanGeometry.angle (V := Plane) p' q' r') := by
    have hab : 0 < dist p q * dist r q := mul_pos ha hb
    have : 2 * (dist p q * dist r q) * (Real.cos (EuclideanGeometry.angle (V := Plane) p q r) - Real.cos (EuclideanGeometry.angle (V := Plane) p' q' r')) = 0 := by
      nlinarith
    have h0 : (2 * (dist p q * dist r q)) ≠ 0 := by positivity
    have := (mul_eq_zero.mp this).resolve_left h0
    linarith
  exact Real.injOn_cos ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩ hc

theorem pts_dist_pos (T : Tri) {a b : Fin 3} (h : a ≠ b) : 0 < dist (T.pts a) (T.pts b) :=
  dist_pos.mpr (fun e => h (T.indep.injective e))

/-- the labelling: identity on every tile -/
def idx : Fin 8 → Equiv.Perm (Fin 3) := fun _ => 1

theorem octDiss_hidx : ∀ i k k', dist ((octDiss.tile i).pts k) ((octDiss.tile i).pts k') = dist (octDiss.model.pts (idx i k)) (octDiss.model.pts (idx i k')) := by
  intro i k k'
  show dist ((tile i).pts k) ((tile i).pts k') = dist ((tile 0).pts (idx i k)) ((tile 0).pts (idx i k'))
  simp only [idx, Equiv.Perm.coe_one, id_eq]
  exact tile_dist i k k'

theorem octDiss_hidxA : ∀ i v, octDiss.model.angleAt (idx i v) = (octDiss.tile i).angleAt v := by
  intro i v
  show Erdos634.TilePlacement.angleAt (tile 0) (idx i v) = Erdos634.TilePlacement.angleAt (tile i) v
  simp only [idx, Equiv.Perm.coe_one, id_eq]
  unfold Erdos634.TilePlacement.angleAt
  symm
  apply cornerAngle_of_dists (tile_dist i _ _) (tile_dist i _ _) (tile_dist i _ _)
  · exact pts_dist_pos _ (by revert v; decide)
  · exact pts_dist_pos _ (by revert v; decide)

end Erdos634.Draft.LaczFormal.IsoWit
