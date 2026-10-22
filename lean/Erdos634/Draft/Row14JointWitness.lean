-- Draft/Row14JointWitness.lean — a JOINT Lean witness for `Row14.rational_any_label`
-- (Draft/FluxFRow14AnyLabel.lean) on a REAL certified tiling: `CevianTiling63Bridge.dissection`
-- (63 copies of the (2,3,4)·8 tile in the target (6,7,8)·24, pre-existing bridge — reused, not rebuilt).
-- Every hypothesis is discharged on that one dissection with α := α44 (cos 7/8), β := β44 (cos 11/16)
-- from `FluxGridWitness` (irrationality `α44_irr`, `3α+2β = π` `three_α_two_β`, both pre-existing).
-- Model (24,16,32): α at 0, β at 2, γ at 1.  Target d01=168, d12=192, d20=144: 2α at 2, β at 1.
-- The theorem's output is then instantiated: r = 1/2 (oppLen 0 = 16, oppLen 1 = 32).
-- Formalization debt (non-vacuity of a VERIFIED row), not /goal progress.
import Erdos634.CevianTiling63Bridge
import Erdos634.Draft.FluxGridWitness
import Erdos634.Draft.FluxFRow14AnyLabel

open scoped Classical

namespace Erdos634.Draft.Row14JointWitness

open Erdos634.Geometry Erdos634.Z15Real
open Erdos634.Draft.FluxGridWitness (α44 β44 α44_irr three_α_two_β cos_α44 cos_β44 cos_cornerAngle
  cornerAngle_mem ne_of_dist α44_le)

noncomputable abbrev D := Erdos634.CevianTiling63Bridge.dissection

theorem d_model : D.model = Erdos634.CevianTiling63Bridge.pieceTri
    Erdos634.CevianTiling63Bridge.headI_mem_tiles := rfl
theorem d_target : D.target = Erdos634.CevianTiling63Bridge.targetTri := rfl

theorem m_d01 : dist (D.model.pts 0) (D.model.pts 1) = 24 := by
  have e : CevianTiling63.dist2 (Erdos634.CevianTiling63Bridge.vertexOf CevianTiling63.tiles.headI 0)
      (Erdos634.CevianTiling63Bridge.vertexOf CevianTiling63.tiles.headI 1) = ((576:ℤ),(0:ℤ)) := by decide
  exact Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num)
    (by rw [d_model, Erdos634.CevianTiling63Bridge.pieceTri_dist_sq _ _ 0 1, e]; simp [toR]; norm_num)

theorem m_d12 : dist (D.model.pts 1) (D.model.pts 2) = 16 := by
  have e : CevianTiling63.dist2 (Erdos634.CevianTiling63Bridge.vertexOf CevianTiling63.tiles.headI 1)
      (Erdos634.CevianTiling63Bridge.vertexOf CevianTiling63.tiles.headI 2) = ((256:ℤ),(0:ℤ)) := by decide
  exact Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num)
    (by rw [d_model, Erdos634.CevianTiling63Bridge.pieceTri_dist_sq _ _ 1 2, e]; simp [toR]; norm_num)

theorem m_d20 : dist (D.model.pts 2) (D.model.pts 0) = 32 := by
  have e : CevianTiling63.dist2 (Erdos634.CevianTiling63Bridge.vertexOf CevianTiling63.tiles.headI 2)
      (Erdos634.CevianTiling63Bridge.vertexOf CevianTiling63.tiles.headI 0) = ((1024:ℤ),(0:ℤ)) := by decide
  exact Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num)
    (by rw [d_model, Erdos634.CevianTiling63Bridge.pieceTri_dist_sq _ _ 2 0, e]; simp [toR]; norm_num)

theorem t_d01 : dist (D.target.pts 0) (D.target.pts 1) = 168 :=
  Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num)
    (by rw [d_target, Erdos634.CevianTiling63Bridge.targetTri_sides.1]; norm_num)
theorem t_d12 : dist (D.target.pts 1) (D.target.pts 2) = 192 :=
  Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num)
    (by rw [d_target, Erdos634.CevianTiling63Bridge.targetTri_sides.2.1]; norm_num)
theorem t_d20 : dist (D.target.pts 2) (D.target.pts 0) = 144 :=
  Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num)
    (by rw [d_target, Erdos634.CevianTiling63Bridge.targetTri_sides.2.2]; norm_num)

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

theorem target_angle1 : D.target.angleAt 1 = β44 := by
  have hcos : Real.cos (D.target.angleAt 1) = 11 / 16 := by
    unfold Tri.angleAt
    simp only [show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl]
    have e1 : dist (D.target.pts 2) (D.target.pts 1) = 192 := by rw [dist_comm]; exact t_d12
    have e2 : dist (D.target.pts 0) (D.target.pts 1) = 168 := t_d01
    have e3 : dist (D.target.pts 2) (D.target.pts 0) = 144 := t_d20
    rw [cos_cornerAngle (ne_of_dist e1 (by norm_num)) (ne_of_dist e2 (by norm_num))]
    simp only [e1, e2, e3]
    norm_num
  exact Real.injOn_cos (cornerAngle_mem _ _ _) (cornerAngle_mem _ _ _) (hcos.trans cos_β44.symm)

theorem target_angle2 : D.target.angleAt 2 = 2 * α44 := by
  have hcos : Real.cos (D.target.angleAt 2) = 17 / 32 := by
    unfold Tri.angleAt
    simp only [show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
    rw [cos_cornerAngle (ne_of_dist t_d20 (by norm_num)).symm (ne_of_dist t_d12 (by norm_num)),
      dist_comm (D.target.pts 0) (D.target.pts 2), t_d20, t_d12, t_d01]
    norm_num
  have hc2 : Real.cos (2 * α44) = 17 / 32 := by rw [Real.cos_two_mul, cos_α44]; norm_num
  have hα0 : 0 ≤ α44 := (cornerAngle_mem _ _ _).1
  have hle := α44_le
  exact Real.injOn_cos (cornerAngle_mem _ _ _)
    ⟨by linarith, by linarith [Real.pi_pos]⟩ (hcos.trans hc2.symm)

theorem model_opp : D.model.oppLen 0 = 16 ∧ D.model.oppLen 1 = 32 := by
  unfold Tri.oppLen
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl,
    show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl]
  exact ⟨m_d12, m_d20⟩

/-- **Joint witness**: every hypothesis of `Row14.rational_any_label` holds at once on the real
certified 63-tiling (m = (0,2,1), t = (2,1)); the theorem fires. -/
theorem row14_fires :
    ∃ r : ℚ, D.model.oppLen 0 = (r : ℝ) * D.model.oppLen 1 :=
  Row14.rational_any_label D α44 β44 α44_irr three_α_two_β
    (m₀ := 0) (m₁ := 2) (m₂ := 1) (by decide) (by decide) (by decide)
    model_angle0 model_angle2 (t₀ := 2) (t₁ := 1) (by decide) target_angle2 target_angle1

/-- The rational it produces is exactly `1/2`. -/
theorem row14_r_eq_half :
    ∃ r : ℚ, D.model.oppLen 0 = (r : ℝ) * D.model.oppLen 1 ∧ r = 1 / 2 := by
  obtain ⟨r, hr⟩ := row14_fires
  refine ⟨r, hr, ?_⟩
  rw [model_opp.1, model_opp.2] at hr
  have h : (r : ℝ) = ((1 / 2 : ℚ) : ℝ) := by push_cast; linarith
  exact Rat.cast_injective h

end Erdos634.Draft.Row14JointWitness

#print axioms Erdos634.Draft.Row14JointWitness.row14_fires
#print axioms Erdos634.Draft.Row14JointWitness.row14_r_eq_half
