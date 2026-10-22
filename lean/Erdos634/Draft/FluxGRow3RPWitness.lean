-- Draft/FluxGRow3RPWitness.lean — non-vacuity of `RP.row3_RP_even` (FluxGRow3RP.lean): every
-- hypothesis discharged JOINTLY on the real `CongruentDissection 2` `dissection'`
-- (FluxGRow3WitnessBridge.lean: target (−3,0),(3,0),(0,√7) cut along its altitude into two copies of
-- the 3-√7-4 right tile, α = α456 with cos α456 = 3/4, α456/π irrational). Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- Hazard H59: `(e, f) = (3, 4)` is never evaluated or mentioned as a parameter pair; every `3`, `4`,
-- `√7` below is the 3-√7-4 right-triangle side data of row 3's witness (same disclaimer as every
-- other file in this chain).
--
-- Formalization debt, not /goal progress.
import Erdos634.Draft.FluxGRow3RP
import Erdos634.Draft.FluxGRow3Step3N2Final

open scoped Classical

namespace Erdos634.Draft.FluxGRow3RPWitness

open Erdos634.Geometry Erdos634.CertCoord Erdos634.AngleThreshold
open Erdos634.Draft.FluxGRow3AngleWitnessDissection Erdos634.Draft.FluxGRow3WitnessBridge
open Erdos634.Draft.FluxGRow3SharedGrid Erdos634.Draft.FluxGRow3Step3N2Final
open Erdos634.Draft.FluxRow4Witness Erdos634.Geometry.Row3

theorem dist_BC : dist (mkPt (3:ℝ) 0) (mkPt (-3) 0) = 6 := by
  apply dist_eq_of_sq (by norm_num)
  rw [dist_sq_mkPt]; norm_num

theorem arccos_three_quarters : Real.arccos (3 / 4 : ℝ) = α456 := by
  rw [← cos_α456]
  exact Real.arccos_cos α456_pos.le (by linarith [α456_lt_pi_div_two, Real.pi_pos])

theorem target_angleAt0 : target.angleAt 0 = α456 := by
  show cornerAngle (target.pts 1) (target.pts 0) (target.pts 2) = α456
  rw [target_pts]
  show cornerAngle (mkPt 3 0) (mkPt (-3) 0) (mkPt 0 sq7) = α456
  have h7 := sq7_sq
  have hPQ : dist (mkPt (3:ℝ) 0) (mkPt (-3) 0) = 6 := dist_BC
  have hRQ : dist (mkPt (0:ℝ) sq7) (mkPt (-3) 0) = 4 := by rw [dist_comm]; exact model'_dBA
  have hPR : dist (mkPt (3:ℝ) 0) (mkPt 0 sq7) = 4 := tile1'_dist_CA
  have hcos : Real.cos (cornerAngle (mkPt 3 0) (mkPt (-3) 0) (mkPt 0 sq7)) = 3 / 4 := by
    rw [cos_of_sides _ _ _ (by rw [hPQ]; norm_num) (by rw [hRQ]; norm_num), hPQ, hRQ, hPR]
    norm_num
  have hmem : cornerAngle (mkPt 3 0) (mkPt (-3) 0) (mkPt (0:ℝ) sq7) ∈ Set.Icc 0 Real.pi :=
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
  have hres := Real.arccos_cos hmem.1 hmem.2
  rw [hcos, arccos_three_quarters] at hres
  exact hres.symm

theorem target_angleAt1 : target.angleAt 1 = α456 := by
  show cornerAngle (target.pts 2) (target.pts 1) (target.pts 0) = α456
  rw [target_pts]
  show cornerAngle (mkPt 0 sq7) (mkPt 3 0) (mkPt (-3) 0) = α456
  have h7 := sq7_sq
  have hPQ : dist (mkPt (0:ℝ) sq7) (mkPt 3 0) = 4 := by rw [dist_comm]; exact tile1'_dist_CA
  have hRQ : dist (mkPt (-3:ℝ) 0) (mkPt 3 0) = 6 := by rw [dist_comm]; exact dist_BC
  have hPR : dist (mkPt (0:ℝ) sq7) (mkPt (-3) 0) = 4 := by rw [dist_comm]; exact model'_dBA
  have hcos : Real.cos (cornerAngle (mkPt 0 sq7) (mkPt 3 0) (mkPt (-3) 0)) = 3 / 4 := by
    rw [cos_of_sides _ _ _ (by rw [hPQ]; norm_num) (by rw [hRQ]; norm_num), hPQ, hRQ, hPR]
    norm_num
  have hmem : cornerAngle (mkPt 0 sq7) (mkPt 3 0) (mkPt (-3:ℝ) 0) ∈ Set.Icc 0 Real.pi :=
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
  have hres := Real.arccos_cos hmem.1 hmem.2
  rw [hcos, arccos_three_quarters] at hres
  exact hres.symm

/-- **Joint witness**: all nine hypotheses of `RP.row3_RP_even` hold together on `dissection'`,
and the theorem fires (conclusion `Even 2`). -/
theorem row3_RP_even_witness : Even 2 :=
  RP.row3_RP_even dissection' α456_pos α456_lt_pi_div_two α456_div_pi_irr
    model'_angleAt0 tile0'_angleAt2 target_angleAt0 target_angleAt1 target_det_pos

end Erdos634.Draft.FluxGRow3RPWitness

#print axioms Erdos634.Draft.FluxGRow3RPWitness.row3_RP_even_witness
