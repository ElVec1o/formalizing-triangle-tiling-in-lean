-- Draft/G3CIsoControl.lean — G3C (room FINISH, seat HILBERT). UNAUDITED. No sorry/native_decide/axioms.
-- REAL control for node C10 (`ThmIsoStatement`, thm:iso): the certified 2673-tiling (Zhang/Herdt family
-- N = m^2 a(b+2a), (a,b,c)=(3,5,7), m=9) of the isosceles triangle (21,21,33)*9 by the 2pi/3 tile (3,5,7).
import Erdos634.Draft.G3CIso2673
import Erdos634.Draft.G3CAng

open scoped Classical

namespace Erdos634.Draft.G3CIsoControl

open Erdos634.Geometry Erdos634.Draft.G3CCert Erdos634.Draft.G3CAng Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.G3CIso2673 (cert cert_ok cert_len)

noncomputable abbrev D := cd cert cert_ok

theorem m_opp0 : D.model.oppLen 0 = 1890 * 3 := by
  rw [show D.model = _ from cd_model cert cert_ok, oppLen_triOf]
  have := dist_toPt_nat (vtx cert.model (0 + 1)) (vtx cert.model (0 + 2)) 5670 (by decide)
  rw [this]; norm_num
theorem m_opp1 : D.model.oppLen 1 = 1890 * 7 := by
  rw [show D.model = _ from cd_model cert cert_ok, oppLen_triOf]
  have := dist_toPt_nat (vtx cert.model (1 + 1)) (vtx cert.model (1 + 2)) 13230 (by decide)
  rw [this]; norm_num
theorem m_opp2 : D.model.oppLen 2 = 1890 * 5 := by
  rw [show D.model = _ from cd_model cert cert_ok, oppLen_triOf]
  have := dist_toPt_nat (vtx cert.model (2 + 1)) (vtx cert.model (2 + 2)) 9450 (by decide)
  rw [this]; norm_num

theorem t_opp0 : D.target.oppLen 0 = 1890 * 189 := by
  rw [show D.target = _ from cd_target cert cert_ok, oppLen_triOf]
  have := dist_toPt_nat (vtx cert.target (0 + 1)) (vtx cert.target (0 + 2)) 357210 (by decide)
  rw [this]; norm_num
theorem t_opp1 : D.target.oppLen 1 = 1890 * 189 := by
  rw [show D.target = _ from cd_target cert cert_ok, oppLen_triOf]
  have := dist_toPt_nat (vtx cert.target (1 + 1)) (vtx cert.target (1 + 2)) 357210 (by decide)
  rw [this]; norm_num
theorem t_opp2 : D.target.oppLen 2 = 1890 * 297 := by
  rw [show D.target = _ from cd_target cert cert_ok, oppLen_triOf]
  have := dist_toPt_nat (vtx cert.target (2 + 1)) (vtx cert.target (2 + 2)) 561330 (by decide)
  rw [this]; norm_num

/-- model: sigma sends (opp 3, opp 5, opp 7) to vertices (0, 2, 1) -/
noncomputable def σm : Equiv.Perm (Fin 3) := Equiv.swap 1 2
theorem σm0 : σm 0 = 0 := by decide
theorem σm1 : σm 1 = 2 := by decide
theorem σm2 : σm 2 = 1 := by decide

noncomputable def α : ℝ := D.model.angleAt (σm 0)
noncomputable def β : ℝ := D.model.angleAt (σm 1)

theorem o0 : D.model.oppLen (σm 0) = 1890 * 3 := by rw [σm0]; exact m_opp0
theorem o1 : D.model.oppLen (σm 1) = 1890 * 5 := by rw [σm1]; exact m_opp2
theorem o2 : D.model.oppLen (σm 2) = 1890 * 7 := by rw [σm2]; exact m_opp1

theorem data : D.model.TwoPiThreeData α (1890 * 3) (1890 * 5) (1890 * 7) :=
  tp_data D.model σm 1890 3 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) o0 o1 o2

theorem hβ : β = Real.pi / 3 - α :=
  (tp_angles D.model σm 1890 3 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) o0 o1 o2).2

theorem cos_α : Real.cos α = 13 / 14 := by
  unfold α
  rw [cos_s0 D.model σm (by rw [o1]; norm_num) (by rw [o2]; norm_num), o0, o1, o2]; norm_num

theorem cos_β : Real.cos β = 11 / 14 := by
  unfold β
  rw [cos_s1 D.model σm (by rw [o0]; norm_num) (by rw [o2]; norm_num), o0, o1, o2]; norm_num

theorem α_irr : IrrPi α :=
  irrPi_of_cos α (13 / 14) (by rw [cos_α]; norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem t_cos0 : Real.cos (D.target.angleAt 0) = 11 / 14 := by
  have := cos_s0 D.target 1 (by simp [t_opp1]) (by simp [t_opp2])
  simp only [Equiv.Perm.coe_one, id_eq] at this
  rw [this, t_opp0, t_opp1, t_opp2]; norm_num

theorem t_cos1 : Real.cos (D.target.angleAt 1) = 11 / 14 := by
  have := cos_s1 D.target 1 (by simp [t_opp0]) (by simp [t_opp2])
  simp only [Equiv.Perm.coe_one, id_eq] at this
  rw [this, t_opp0, t_opp1, t_opp2]; norm_num

theorem iso_shape : IsoTP D α := by
  refine Or.inr ⟨1, ?_, ?_, ?_⟩
  · simp only [Equiv.Perm.coe_one, id_eq]
    rw [← hβ]; exact angle_eq_of_cos 0 (σm 1) (t_cos0.trans cos_β.symm)
  · simp only [Equiv.Perm.coe_one, id_eq]
    rw [← hβ]; exact angle_eq_of_cos 1 (σm 1) (t_cos1.trans cos_β.symm)
  · simp only [Equiv.Perm.coe_one, id_eq]
    have h0 : D.target.angleAt 0 = β := angle_eq_of_cos 0 (σm 1) (t_cos0.trans cos_β.symm)
    have h1 : D.target.angleAt 1 = β := angle_eq_of_cos 1 (σm 1) (t_cos1.trans cos_β.symm)
    have hs := D.target.angleAt_sum
    rw [hβ] at h0 h1
    linarith

/-- **C10 control**: every non-arithmetic premise of `ThmIsoStatement` holds on the real 2673-tiling. -/
theorem thmIso_premises :
    IrrPi α ∧ D.model.TwoPiThreeData α (1890 * 3) (1890 * 5) (1890 * 7) ∧ IsoTP D α :=
  ⟨α_irr, data, iso_shape⟩

/-- The prime-free variant of C10 is REFUTED by the real 2673-tiling (N = 2673 = 33*81 = m^2 a(b+2a)). -/
theorem thmIso_primeFree_refuted :
    ¬ (∀ (N : ℕ) (D : CongruentDissection N) (α a b c : ℝ), IrrPi α →
        D.model.TwoPiThreeData α a b c → IsoTP D α → False) := by
  intro h
  exact h _ D α _ _ _ α_irr data iso_shape

end Erdos634.Draft.G3CIsoControl

#print axioms Erdos634.Draft.G3CIsoControl.thmIso_primeFree_refuted
