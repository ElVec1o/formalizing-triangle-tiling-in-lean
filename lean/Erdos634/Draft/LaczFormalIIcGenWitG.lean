-- Draft/LaczFormalIIcGenWitG.lean -- WITNESS of the GENERIC Case IIc block (alpha != beta), step G: `genDiss : CongruentRegionDissection 204`, `genTiling : PolyTiling 204 8`, labelling `idx = id`,
-- `hidx`, `hidxA`.  NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcGenWitF
import Erdos634.RegionDissection
import Erdos634.Draft.LaczFormalRGTypes
import Erdos634.Draft.LaczFormalRG5GammaC

namespace Erdos634.Draft.LaczFormal.GenWit

open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Thm21 Erdos634.Draft.LaczFormal.RG Z2

/-- **The 204-tile dissection of the octagon.** -/
noncomputable def genDiss : CongruentRegionDissection 204 where
  region := octP.carrier
  tile := fun i => triZ (TT i)
  covers := tiles_cover
  interiors_disjoint := tile_disjoint
  model := triZ modelTZ
  tiles_congruent := fun i => triZ_cong (TT_props i).1 (TT_props i).2.1

/-- **The tiling as a `PolyTiling 204 8`.** -/
noncomputable def genTiling : PolyTiling 204 8 where
  C := genDiss
  P := octP
  region_eq := rfl

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

/-- the labelling: identity on every tile (tile vertex `k` is the model vertex `k`) -/
def idx : Fin 204 → Equiv.Perm (Fin 3) := fun _ => 1

theorem genDiss_dist (i : Fin 204) (m n : Fin 3) :
    dist ((genDiss.tile i).pts m) ((genDiss.tile i).pts n) = dist (genDiss.model.pts m) (genDiss.model.pts n) :=
  triZ_dist (TT_props i).1 (TT_props i).2.1 m n

theorem genDiss_hidx : ∀ i k k', dist ((genDiss.tile i).pts k) ((genDiss.tile i).pts k') = dist (genDiss.model.pts (idx i k)) (genDiss.model.pts (idx i k')) := by
  intro i k k'
  simp only [idx, Equiv.Perm.coe_one, id_eq]
  exact genDiss_dist i k k'

theorem genDiss_hidxA : ∀ i v, genDiss.model.angleAt (idx i v) = (genDiss.tile i).angleAt v := by
  intro i v
  show Erdos634.TilePlacement.angleAt genDiss.model (idx i v) = Erdos634.TilePlacement.angleAt (genDiss.tile i) v
  simp only [idx, Equiv.Perm.coe_one, id_eq]
  unfold Erdos634.TilePlacement.angleAt
  symm
  apply cornerAngle_of_dists (genDiss_dist i _ _) (genDiss_dist i _ _) (genDiss_dist i _ _)
  · exact pts_dist_pos _ (by revert v; decide)
  · exact pts_dist_pos _ (by revert v; decide)

end Erdos634.Draft.LaczFormal.GenWit
