-- Draft/LaczFormalIIcIsoWitH.lean -- NON-VACUITY witness for `IIcIsoCore`, step H: model angles (3pi/8, 3pi/8, pi/4); `CaseC octDiss idx`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcIsoWitG

open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Thm21 Erdos634.Draft.LaczFormal.RG

namespace Erdos634.Draft.LaczFormal.IsoWit

theorem octDiss_angle2 : octDiss.model.angleAt 2 = Real.pi / 4 := by
  show Erdos634.TilePlacement.angleAt (tile 0) 2 = _
  unfold Erdos634.TilePlacement.angleAt
  have hp : (tile 0).pts = ![mkPt 1 0, mkPt hh hh, mkPt 0 0] := model_pts
  have e1 : (2 : Fin 3) + 1 = 0 := by decide
  have e2 : (2 : Fin 3) + 2 = 1 := by decide
  rw [e1, e2, hp]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  have hlaw := EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle (V := Plane) (mkPt 1 0) (mkPt 0 0) (mkPt hh hh)
  have ha : dist (mkPt 1 0) (mkPt 0 0) = 1 := dist_V0O
  have hb : dist (mkPt hh hh) (mkPt 0 0) = 1 := dist_V1O
  have hd := dist_V01
  rw [ha, hb] at hlaw
  have hcos : Real.cos (EuclideanGeometry.angle (V := Plane) (mkPt 1 0) (mkPt 0 0) (mkPt hh hh)) = Real.cos (Real.pi / 4) := by
    rw [Real.cos_pi_div_four, ← hh_two] 
    nlinarith [hlaw, hd]
  exact Real.injOn_cos ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
    ⟨by positivity, by linarith [Real.pi_pos]⟩ hcos

theorem octDiss_angle2_lt : octDiss.model.angleAt 2 < Real.pi / 2 := by
  rw [octDiss_angle2]; linarith [Real.pi_pos]

theorem octDiss_angle2_ne : octDiss.model.angleAt 2 ≠ Real.pi / 3 := by
  rw [octDiss_angle2]; intro h; linarith [Real.pi_pos]

theorem octDiss_angle01 : Erdos634.TilePlacement.angleAt octDiss.model 0 = Erdos634.TilePlacement.angleAt octDiss.model 1 := by
  show Erdos634.TilePlacement.angleAt (tile 0) 0 = Erdos634.TilePlacement.angleAt (tile 0) 1
  unfold Erdos634.TilePlacement.angleAt
  have hp : (tile 0).pts = ![mkPt 1 0, mkPt hh hh, mkPt 0 0] := model_pts
  have e1 : (0 : Fin 3) + 1 = 1 := by decide
  have e2 : (0 : Fin 3) + 2 = 2 := by decide
  have e3 : (1 : Fin 3) + 1 = 2 := by decide
  have e4 : (1 : Fin 3) + 2 = 0 := by decide
  rw [e1, e2, e3, e4, hp]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  have ha := dist_V0O
  have hb := dist_V1O
  have hc : dist (mkPt 1 0) (mkPt hh hh) = dist (mkPt hh hh) (mkPt 1 0) := dist_comm _ _
  have hu : 0 < dist (mkPt 1 0) (mkPt hh hh) := by
    apply dist_pos.mpr; intro h
    obtain ⟨h1, _⟩ := mkPt_inj h
    nlinarith [hh_sq, hh_pos]
  -- ∠(V1,V0,O) = ∠(O,V1,V0) = ∠(V0,V1,O)
  rw [cornerAngle, cornerAngle, EuclideanGeometry.angle_comm (mkPt 0 0) (mkPt hh hh) (mkPt 1 0)]
  exact cornerAngle_of_dists (p := mkPt hh hh) (q := mkPt 1 0) (r := mkPt 0 0) (p' := mkPt 1 0) (q' := mkPt hh hh) (r' := mkPt 0 0)
    hc.symm (by rw [dist_comm (mkPt 0 0) (mkPt 1 0), ha, dist_comm (mkPt 0 0) (mkPt hh hh), hb]) (by rw [hb, ha]) (by rw [← hc]; exact hu) (by rw [dist_comm (mkPt 0 0) (mkPt 1 0), ha]; norm_num)

theorem octDiss_caseC : CaseC octDiss idx where
  hidx := octDiss_hidx
  hidxA := octDiss_hidxA
  hregc := octDiss_hregc
  hnc := octDiss_notComb

end Erdos634.Draft.LaczFormal.IsoWit
