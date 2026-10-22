-- Draft/G3CS3Control.lean — G3C (room FINISH, seat HILBERT). UNAUDITED. No sorry/native_decide.
-- Premise-satisfiability + negative control for leaf S3Closed (`CompositeGen2.S3Closed`): the certified 84-tiling
-- (`R84TilingBridge.dissection`, tile (2,3,4)*8 = (16,24,32), target (192,192,336) with angles (alpha, alpha, alpha+2beta)).
-- Shows `not (S3Closed 84)` and `not (S3Chk 84)` (the leaf's decidable arithmetic check fails at the real N, (e,d)=(1,1)).
import Erdos634.R84TilingBridge
import Erdos634.Draft.FluxGridWitness
import Erdos634.Draft.TheoremPConditional
import Erdos634.Draft.CompositeGen2
import Erdos634.Draft.AllNExclusionArith

open scoped Classical

namespace Erdos634.Draft.G3CS3Control

open Erdos634.Geometry Erdos634.Z15Real Erdos634.Draft.TheoremPConditional Erdos634.Draft.CompositeGen2
open Erdos634.R84TilingBridge (pieceTri headI_mem_tiles vertexOf targetTri toZPt dist2_eq_zdist2)
open Erdos634.Draft.FluxGridWitness (α44 β44 α44_irr three_α_two_β cos_α44 cos_β44 cos_cornerAngle
  cornerAngle_mem ne_of_dist α44_le)

noncomputable abbrev D := Erdos634.R84TilingBridge.dissection

theorem d_model : D.model = pieceTri headI_mem_tiles := rfl
theorem d_target : D.target = targetTri := rfl

theorem m_d01 : dist (D.model.pts 0) (D.model.pts 1) = 24 := by
  have e : R84Tiling.dist2 (vertexOf R84Tiling.tiles.headI 0) (vertexOf R84Tiling.tiles.headI 1)
      = ((576:ℤ),(0:ℤ)) := by decide
  exact Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num)
    (by rw [d_model, Erdos634.R84TilingBridge.pieceTri_dist_sq _ _ 0 1, e]; simp [toR]; norm_num)

theorem m_d12 : dist (D.model.pts 1) (D.model.pts 2) = 16 := by
  have e : R84Tiling.dist2 (vertexOf R84Tiling.tiles.headI 1) (vertexOf R84Tiling.tiles.headI 2)
      = ((256:ℤ),(0:ℤ)) := by decide
  exact Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num)
    (by rw [d_model, Erdos634.R84TilingBridge.pieceTri_dist_sq _ _ 1 2, e]; simp [toR]; norm_num)

theorem m_d20 : dist (D.model.pts 2) (D.model.pts 0) = 32 := by
  have e : R84Tiling.dist2 (vertexOf R84Tiling.tiles.headI 2) (vertexOf R84Tiling.tiles.headI 0)
      = ((1024:ℤ),(0:ℤ)) := by decide
  exact Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num)
    (by rw [d_model, Erdos634.R84TilingBridge.pieceTri_dist_sq _ _ 2 0, e]; simp [toR]; norm_num)

theorem t_d01 : dist (D.target.pts 0) (D.target.pts 1) = 336 := by
  have h := Erdos634.R84TilingBridge.targetTri_sides.1
  exact Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num) (by rw [d_target, h]; norm_num)

theorem t_d12 : dist (D.target.pts 1) (D.target.pts 2) = 192 := by
  have h := Erdos634.R84TilingBridge.targetTri_sides.2.1
  exact Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num) (by rw [d_target, h]; norm_num)

theorem t_d20 : dist (D.target.pts 2) (D.target.pts 0) = 192 := by
  have h := Erdos634.R84TilingBridge.targetTri_sides.2.2
  exact Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num) (by rw [d_target, h]; norm_num)

theorem t_d10 : dist (D.target.pts 1) (D.target.pts 0) = 336 := by rw [dist_comm]; exact t_d01
theorem t_d21 : dist (D.target.pts 2) (D.target.pts 1) = 192 := by rw [dist_comm]; exact t_d12
theorem t_d02 : dist (D.target.pts 0) (D.target.pts 2) = 192 := by rw [dist_comm]; exact t_d20

theorem model_angle0 : D.model.angleAt 0 = α44 := by
  have hcos : Real.cos (D.model.angleAt 0) = 7 / 8 := by
    unfold Tri.angleAt
    simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl]
    rw [cos_cornerAngle (ne_of_dist m_d01 (by norm_num)).symm (ne_of_dist m_d20 (by norm_num)),
      dist_comm (D.model.pts 1) (D.model.pts 0), m_d01, m_d20, m_d12]
    norm_num
  exact Real.injOn_cos (cornerAngle_mem _ _ _) (cornerAngle_mem _ _ _) (hcos.trans cos_α44.symm)

theorem model_angle2 : D.model.angleAt 2 = β44 := by
  have hcos : Real.cos (D.model.angleAt 2) = 11 / 16 := by
    unfold Tri.angleAt
    simp only [show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
    rw [cos_cornerAngle (ne_of_dist m_d20 (by norm_num)).symm (ne_of_dist m_d12 (by norm_num)),
      dist_comm (D.model.pts 0) (D.model.pts 2), m_d20, m_d12, m_d01]
    norm_num
  exact Real.injOn_cos (cornerAngle_mem _ _ _) (cornerAngle_mem _ _ _) (hcos.trans cos_β44.symm)

theorem target_angle0 : D.target.angleAt 0 = α44 := by
  have hcos : Real.cos (D.target.angleAt 0) = 7 / 8 := by
    unfold Tri.angleAt
    simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl]
    rw [cos_cornerAngle (ne_of_dist t_d10 (by norm_num)) (ne_of_dist t_d20 (by norm_num))]
    simp only [t_d10, t_d20, t_d12]
    norm_num
  exact Real.injOn_cos (cornerAngle_mem _ _ _) (cornerAngle_mem _ _ _) (hcos.trans cos_α44.symm)

theorem target_angle1 : D.target.angleAt 1 = α44 := by
  have hcos : Real.cos (D.target.angleAt 1) = 7 / 8 := by
    unfold Tri.angleAt
    simp only [show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl]
    rw [cos_cornerAngle (ne_of_dist t_d21 (by norm_num)) (ne_of_dist t_d01 (by norm_num))]
    simp only [t_d21, t_d01, t_d20]
    norm_num
  exact Real.injOn_cos (cornerAngle_mem _ _ _) (cornerAngle_mem _ _ _) (hcos.trans cos_α44.symm)

theorem model_opp : D.model.oppLen 0 = 16 ∧ D.model.oppLen 1 = 32 ∧ D.model.oppLen 2 = 24 := by
  unfold Tri.oppLen
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl,
    show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl,
    show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
  exact ⟨m_d12, m_d20, m_d01⟩

theorem data : D.model.ThreeAlphaData α44 β44 16 24 32 :=
  threeAlpha_of_02 _ three_α_two_β model_angle0 model_angle2 model_opp.1 model_opp.2.2 model_opp.2.1

/-- All non-arithmetic premises of `S3Closed` hold on the real 84-tiling (two target angles alpha at vertices 0, 1). -/
theorem s3_premises :
    IrrPi α44 ∧ 3 * α44 + 2 * β44 = Real.pi ∧ D.model.ThreeAlphaData α44 β44 16 24 32 ∧
      D.target.angleAt 0 = α44 ∧ D.target.angleAt 1 = α44 :=
  ⟨α44_irr, three_α_two_β, data, target_angle0, target_angle1⟩

theorem len84 : R84Tiling.tiles.length = 84 := by decide

/-- The leaf `S3Closed` is FALSE at the real tiling's N = 84. -/
theorem not_s3Closed_84 : ¬ S3Closed 84 := by
  intro g
  rw [← len84] at g
  exact g D α44 β44 16 24 32 α44_irr three_α_two_β data 0 1 (by decide) target_angle0 target_angle1

/-- Negative control: the decidable arithmetic check `S3Chk` fails at N = 84 (witness `(e,d) = (1,1)`, `m = 2`). -/
theorem not_s3Chk_84 : ¬ Erdos634.Draft.AllNExclusion.S3Chk 84 := by decide +kernel

end Erdos634.Draft.G3CS3Control

#print axioms Erdos634.Draft.G3CS3Control.not_s3Closed_84
#print axioms Erdos634.Draft.G3CS3Control.not_s3Chk_84
