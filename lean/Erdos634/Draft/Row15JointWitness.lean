-- Draft/Row15JointWitness.lean — a JOINT Lean witness for `Row15.rational_any_label`
-- (Draft/FluxFRow15AnyLabel.lean) on the REAL certified 77-tiling, via the new bridge
-- `Draft/Tiling77Bridge.lean` (`Tiling77Bridge.dissection`).  Model = head tile (48,32,64) = 16·(3,2,4):
-- α at 0, β at 2, γ at 1.  Target (0,0),(528,0),(136,56√15): sides d01=528, d12=448, d20=256,
-- angles 2α at 0 (cos 17/32), α at 1 (cos 7/8).  α := α44, β := β44 from `FluxGridWitness`
-- (irrationality and 3α+2β = π pre-existing).  Instantiated: r = 1/2, 1 − r² = 3/4.
-- Formalization debt (non-vacuity of a VERIFIED row), not /goal progress.
import Erdos634.Draft.Tiling77Bridge
import Erdos634.Draft.FluxGridWitness
import Erdos634.Draft.FluxFRow15AnyLabel

open scoped Classical

namespace Erdos634.Draft.Row15JointWitness

open Erdos634.Geometry Erdos634.Z15Real
open Erdos634.Tiling77Bridge (pieceTri headI_mem_tiles vertexOf targetTri toZPt target dist2_eq_zdist2)
open Erdos634.Draft.FluxGridWitness (α44 β44 α44_irr three_α_two_β cos_α44 cos_β44 cos_cornerAngle
  cornerAngle_mem ne_of_dist α44_le)

noncomputable abbrev D := Erdos634.Tiling77Bridge.dissection

theorem d_model : D.model = pieceTri headI_mem_tiles := rfl
theorem d_target : D.target = targetTri := rfl

theorem targetTri_dist_sq (i j : Fin 3) :
    dist (targetTri.pts i) (targetTri.pts j) ^ 2
      = toR (Tiling77.dist2 (vertexOf target i) (vertexOf target j)) := by
  have hp : ∀ k, targetTri.pts k = Erdos634.CertCoord.mkPt (toR (zx (toZPt (vertexOf target k))))
      (toR (zy (toZPt (vertexOf target k)))) := by intro k; fin_cases k <;> rfl
  rw [hp i, hp j, Erdos634.CertCoord.dist_sq_mkPt, dist2_eq_zdist2]
  exact toR_zdist2 _ _

theorem m_d01 : dist (D.model.pts 0) (D.model.pts 1) = 48 := by
  have e : Tiling77.dist2 (vertexOf Tiling77.tiles.headI 0) (vertexOf Tiling77.tiles.headI 1)
      = ((2304:ℤ),(0:ℤ)) := by decide
  exact Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num)
    (by rw [d_model, Erdos634.Tiling77Bridge.pieceTri_dist_sq _ _ 0 1, e]; simp [toR]; norm_num)

theorem m_d12 : dist (D.model.pts 1) (D.model.pts 2) = 32 := by
  have e : Tiling77.dist2 (vertexOf Tiling77.tiles.headI 1) (vertexOf Tiling77.tiles.headI 2)
      = ((1024:ℤ),(0:ℤ)) := by decide
  exact Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num)
    (by rw [d_model, Erdos634.Tiling77Bridge.pieceTri_dist_sq _ _ 1 2, e]; simp [toR]; norm_num)

theorem m_d20 : dist (D.model.pts 2) (D.model.pts 0) = 64 := by
  have e : Tiling77.dist2 (vertexOf Tiling77.tiles.headI 2) (vertexOf Tiling77.tiles.headI 0)
      = ((4096:ℤ),(0:ℤ)) := by decide
  exact Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num)
    (by rw [d_model, Erdos634.Tiling77Bridge.pieceTri_dist_sq _ _ 2 0, e]; simp [toR]; norm_num)

theorem t_d01 : dist (D.target.pts 0) (D.target.pts 1) = 528 := by
  have e : Tiling77.dist2 (vertexOf target 0) (vertexOf target 1) = ((278784:ℤ),(0:ℤ)) := by decide
  exact Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num)
    (by rw [d_target, targetTri_dist_sq 0 1, e]; simp [toR]; norm_num)

theorem t_d12 : dist (D.target.pts 1) (D.target.pts 2) = 448 := by
  have e : Tiling77.dist2 (vertexOf target 1) (vertexOf target 2) = ((200704:ℤ),(0:ℤ)) := by decide
  exact Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num)
    (by rw [d_target, targetTri_dist_sq 1 2, e]; simp [toR]; norm_num)

theorem t_d20 : dist (D.target.pts 2) (D.target.pts 0) = 256 := by
  have e : Tiling77.dist2 (vertexOf target 2) (vertexOf target 0) = ((65536:ℤ),(0:ℤ)) := by decide
  exact Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num)
    (by rw [d_target, targetTri_dist_sq 2 0, e]; simp [toR]; norm_num)

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

theorem t_d10 : dist (D.target.pts 1) (D.target.pts 0) = 528 := by rw [dist_comm]; exact t_d01
theorem t_d21 : dist (D.target.pts 2) (D.target.pts 1) = 448 := by rw [dist_comm]; exact t_d12
theorem t_d02 : dist (D.target.pts 0) (D.target.pts 2) = 256 := by rw [dist_comm]; exact t_d20

theorem target_angle1 : D.target.angleAt 1 = α44 := by
  have hcos : Real.cos (D.target.angleAt 1) = 7 / 8 := by
    unfold Tri.angleAt
    simp only [show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl]
    rw [cos_cornerAngle (ne_of_dist t_d21 (by norm_num)) (ne_of_dist t_d01 (by norm_num))]
    simp only [t_d21, t_d01, t_d20]
    norm_num
  exact Real.injOn_cos (cornerAngle_mem _ _ _) (cornerAngle_mem _ _ _) (hcos.trans cos_α44.symm)

theorem target_angle0 : D.target.angleAt 0 = 2 * α44 := by
  have hcos : Real.cos (D.target.angleAt 0) = 17 / 32 := by
    unfold Tri.angleAt
    simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl]
    rw [cos_cornerAngle (ne_of_dist t_d10 (by norm_num)) (ne_of_dist t_d20 (by norm_num))]
    simp only [t_d10, t_d20, t_d12]
    norm_num
  have hc2 : Real.cos (2 * α44) = 17 / 32 := by rw [Real.cos_two_mul, cos_α44]; norm_num
  have hα0 : 0 ≤ α44 := (cornerAngle_mem _ _ _).1
  have hle := α44_le
  exact Real.injOn_cos (cornerAngle_mem _ _ _)
    ⟨by linarith, by linarith [Real.pi_pos]⟩ (hcos.trans hc2.symm)

theorem model_opp : D.model.oppLen 0 = 32 ∧ D.model.oppLen 1 = 64 ∧ D.model.oppLen 2 = 48 := by
  unfold Tri.oppLen
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl,
    show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl,
    show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
  exact ⟨m_d12, m_d20, m_d01⟩

/-- **Joint witness**: every hypothesis of `Row15.rational_any_label` holds at once on the real
certified 77-tiling (m = (0,2,1), t = (0,1)); the theorem fires. -/
theorem row15_fires :
    ∃ r : ℚ, D.model.oppLen 0 = (r : ℝ) * D.model.oppLen 1 ∧
      D.model.oppLen 2 = (1 - (r : ℝ) ^ 2) * D.model.oppLen 1 :=
  Row15.rational_any_label D α44 β44 α44_irr three_α_two_β
    (m₀ := 0) (m₁ := 2) (m₂ := 1) (by decide) (by decide) (by decide)
    model_angle0 model_angle2 (t₀ := 0) (t₁ := 1) (by decide) target_angle0 target_angle1

/-- The rational it produces is exactly `1/2` (and `1 − r² = 3/4`: 48 = (3/4)·64). -/
theorem row15_r_eq_half :
    ∃ r : ℚ, D.model.oppLen 0 = (r : ℝ) * D.model.oppLen 1 ∧
      D.model.oppLen 2 = (1 - (r : ℝ) ^ 2) * D.model.oppLen 1 ∧ r = 1 / 2 := by
  obtain ⟨r, hr, hr2⟩ := row15_fires
  refine ⟨r, hr, hr2, ?_⟩
  rw [model_opp.1, model_opp.2.1] at hr
  have h : (r : ℝ) = ((1 / 2 : ℚ) : ℝ) := by push_cast; linarith
  exact Rat.cast_injective h

/-- Sanity: the number of pieces is 77. -/
theorem pieces_eq_77 : Tiling77.tiles.length = 77 := by decide

end Erdos634.Draft.Row15JointWitness

#print axioms Erdos634.Draft.Row15JointWitness.row15_fires
#print axioms Erdos634.Draft.Row15JointWitness.row15_r_eq_half
#print axioms Erdos634.Tiling77Bridge.dissection
