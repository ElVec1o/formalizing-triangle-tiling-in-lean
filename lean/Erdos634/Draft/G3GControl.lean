-- Draft/G3GControl.lean — G3G. UNAUDITED. No sorry/native_decide.
-- REAL control for the leaf `CaseGClosed`: the certified 1125-tiling (Herdt/Beeson Fig. 23) of the isosceles triangle
-- (150,150,225)*16 by the tile (4,5,6)*16 (gamma = 2alpha, cos alpha = 3/4) is a `CongruentDissection 1125`
-- meeting every structural premise of `CaseGClosed`, hence `¬ CaseGClosed 1125`.
-- Not progress on the /goal: premise-satisfiability (formalization debt, gate G3).
import Erdos634.Draft.G3GTiling1125
import Erdos634.Draft.G3CAng
import Erdos634.Draft.ChainComposite

open scoped Classical

namespace Erdos634.Draft.G3GControl

open Erdos634.Geometry Erdos634.Draft.G3GCert Erdos634.Draft.TheoremPConditional Erdos634.Draft.ChainComposite
open Erdos634.Draft.G3GTiling1125 (cert cert_ok cert_len)
open Erdos634.Draft.G3CAng (cos_angleAt_opp cos_s0 cos_s1 cos_s2 angle_eq_of_cos irrPi_of_cos sum_perm)
open Erdos634.Draft.FluxPaperWitness (cornerAngle_mem')

theorem dist_toPt_nat (p q : LP) (s : ℕ) (h : d2 p q = (s : ℤ) ^ 2) :
    dist (toPt p) (toPt q) = (s : ℝ) := by
  have h1 := dist_sq_toPt p q
  rw [h] at h1
  push_cast at h1
  exact (pow_left_inj₀ dist_nonneg (Nat.cast_nonneg s) two_ne_zero).mp h1

theorem oppLen_triOf (t : LT) (h : 0 < cross t.1 t.2.1 t.2.2) (k : Fin 3) :
    (triOf t h).oppLen k = dist (toPt (vtx t (k + 1))) (toPt (vtx t (k + 2))) := by
  unfold Tri.oppLen
  rw [triOf_pts, triOf_pts]

noncomputable abbrev D := cd cert cert_ok

theorem m_opp0 : D.model.oppLen 0 = 64 := by
  rw [show D.model = _ from cd_model cert cert_ok, oppLen_triOf]
  have := dist_toPt_nat (vtx cert.model (0 + 1)) (vtx cert.model (0 + 2)) 64 (by decide)
  rw [this]; norm_num
theorem m_opp1 : D.model.oppLen 1 = 80 := by
  rw [show D.model = _ from cd_model cert cert_ok, oppLen_triOf]
  have := dist_toPt_nat (vtx cert.model (1 + 1)) (vtx cert.model (1 + 2)) 80 (by decide)
  rw [this]; norm_num
theorem m_opp2 : D.model.oppLen 2 = 96 := by
  rw [show D.model = _ from cd_model cert cert_ok, oppLen_triOf]
  have := dist_toPt_nat (vtx cert.model (2 + 1)) (vtx cert.model (2 + 2)) 96 (by decide)
  rw [this]; norm_num
theorem t_opp0 : D.target.oppLen 0 = 2400 := by
  rw [show D.target = _ from cd_target cert cert_ok, oppLen_triOf]
  have := dist_toPt_nat (vtx cert.target (0 + 1)) (vtx cert.target (0 + 2)) 2400 (by decide)
  rw [this]; norm_num
theorem t_opp1 : D.target.oppLen 1 = 2400 := by
  rw [show D.target = _ from cd_target cert cert_ok, oppLen_triOf]
  have := dist_toPt_nat (vtx cert.target (1 + 1)) (vtx cert.target (1 + 2)) 2400 (by decide)
  rw [this]; norm_num
theorem t_opp2 : D.target.oppLen 2 = 3600 := by
  rw [show D.target = _ from cd_target cert cert_ok, oppLen_triOf]
  have := dist_toPt_nat (vtx cert.target (2 + 1)) (vtx cert.target (2 + 2)) 3600 (by decide)
  rw [this]; norm_num

noncomputable def α : ℝ := D.model.angleAt 0

theorem cos_α : Real.cos α = 3 / 4 := by
  have := cos_s0 D.model 1 (by simp [m_opp1]) (by simp [m_opp2])
  simp only [Equiv.Perm.coe_one, id_eq] at this
  unfold α
  rw [this, m_opp0, m_opp1, m_opp2]; norm_num

theorem cos_β : Real.cos (D.model.angleAt 1) = 9 / 16 := by
  have := cos_s1 D.model 1 (by simp [m_opp0]) (by simp [m_opp2])
  simp only [Equiv.Perm.coe_one, id_eq] at this
  rw [this, m_opp0, m_opp1, m_opp2]; norm_num

theorem cos_γ : Real.cos (D.model.angleAt 2) = 1 / 8 := by
  have := cos_s2 D.model 1 (by simp [m_opp0]) (by simp [m_opp1])
  simp only [Equiv.Perm.coe_one, id_eq] at this
  rw [this, m_opp0, m_opp1, m_opp2]; norm_num

theorem α_irr : IrrPi α :=
  irrPi_of_cos α (3 / 4) (by rw [cos_α]; norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem α_lt : α < Real.pi / 2 := by
  by_contra h
  push Not at h
  have h2 : D.model.angleAt 0 ≤ Real.pi := (cornerAngle_mem' _ _ _).2
  have := Real.cos_nonpos_of_pi_div_two_le_of_le (x := α) h (by unfold α; linarith [h2, Real.pi_pos])
  rw [cos_α] at this; norm_num at this

theorem γ_eq : D.model.angleAt 2 = 2 * α := by
  have hpi := Real.pi_pos
  have hα0 : 0 ≤ α := (cornerAngle_mem' _ _ _ : 0 ≤ D.model.angleAt 0 ∧ _).1
  have hc : Real.cos (2 * α) = 1 / 8 := by rw [Real.cos_two_mul, cos_α]; norm_num
  exact Real.injOn_cos (cornerAngle_mem' _ _ _) ⟨by positivity, by linarith [α_lt]⟩ (cos_γ.trans hc.symm)

theorem β_eq : D.model.angleAt 1 = Real.pi - 3 * α := by
  have hs := sum_perm D.model 1
  simp only [Equiv.Perm.coe_one, id_eq] at hs
  have := γ_eq
  unfold α at *
  linarith

theorem data : D.model.TwoAlphaData α 64 80 96 :=
  ⟨1, rfl, m_opp0, β_eq, m_opp1, γ_eq, m_opp2⟩

theorem t_cos0 : Real.cos (D.target.angleAt 0) = 3 / 4 := by
  have := cos_s0 D.target 1 (by simp [t_opp1]) (by simp [t_opp2])
  simp only [Equiv.Perm.coe_one, id_eq] at this
  rw [this, t_opp0, t_opp1, t_opp2]; norm_num

theorem t_cos1 : Real.cos (D.target.angleAt 1) = 3 / 4 := by
  have := cos_s1 D.target 1 (by simp [t_opp0]) (by simp [t_opp2])
  simp only [Equiv.Perm.coe_one, id_eq] at this
  rw [this, t_opp0, t_opp1, t_opp2]; norm_num

theorem t_ang0 : D.target.angleAt 0 = α := angle_eq_of_cos 0 0 (t_cos0.trans cos_α.symm)
theorem t_ang1 : D.target.angleAt 1 = α := angle_eq_of_cos 1 0 (t_cos1.trans cos_α.symm)

/-- every non-arithmetic premise of `CaseGClosed` holds on the real 1125-tiling -/
theorem premises :
    IrrPi α ∧ D.model.TwoAlphaData α 64 80 96 ∧ (0 : Fin 3) ≠ 1 ∧
      D.target.angleAt 0 = α ∧ D.target.angleAt 1 = α :=
  ⟨α_irr, data, by decide, t_ang0, t_ang1⟩

theorem not_caseGClosed_1125 : ¬ CaseGClosed 1125 := by
  intro g
  have h : cert.leaves.length = 1125 := cert_len
  rw [← h] at g
  exact g D α _ _ _ α_irr data 0 1 (by decide) t_ang0 t_ang1

end Erdos634.Draft.G3GControl

#print axioms Erdos634.Draft.G3GControl.not_caseGClosed_1125
