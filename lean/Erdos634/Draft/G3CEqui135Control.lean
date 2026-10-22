-- Draft/G3CEqui135Control.lean — G3C (room FINISH, seat HILBERT). UNAUDITED. No sorry/native_decide/axioms.
-- Premise-satisfiability + negative control for leaf GapE120 (`Chain15.GapE120`): the certified 1215-tiling
-- (Zhang/Herdt, m = 9) of the EQUILATERAL triangle of side 135*1890 by the 2pi/3 tile (3,5,7)*1890.
-- Shows `not (GapE120 1215)` and `not (Pairs120Chk 1215)` (the leaf's arithmetic check fails at the real N).
import Erdos634.Draft.G3CEqui135
import Erdos634.Draft.G3CAng
import Erdos634.Draft.AllNExclusionArith2

open scoped Classical

namespace Erdos634.Draft.G3CEqui135Control

open Erdos634.Geometry Erdos634.Draft.G3CCert Erdos634.Draft.G3CAng Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.Chain15 Erdos634.Draft.AllNExclusion
open Erdos634.Draft.G3CEqui135 (cert cert_ok cert_len)

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
theorem t_opp0 : D.target.oppLen 0 = 1890 * 135 := by
  rw [show D.target = _ from cd_target cert cert_ok, oppLen_triOf]
  have := dist_toPt_nat (vtx cert.target (0 + 1)) (vtx cert.target (0 + 2)) 255150 (by decide)
  rw [this]; norm_num
theorem t_opp1 : D.target.oppLen 1 = 1890 * 135 := by
  rw [show D.target = _ from cd_target cert cert_ok, oppLen_triOf]
  have := dist_toPt_nat (vtx cert.target (1 + 1)) (vtx cert.target (1 + 2)) 255150 (by decide)
  rw [this]; norm_num
theorem t_opp2 : D.target.oppLen 2 = 1890 * 135 := by
  rw [show D.target = _ from cd_target cert cert_ok, oppLen_triOf]
  have := dist_toPt_nat (vtx cert.target (2 + 1)) (vtx cert.target (2 + 2)) 255150 (by decide)
  rw [this]; norm_num

noncomputable def σm : Equiv.Perm (Fin 3) := Equiv.swap 1 2
theorem σm0 : σm 0 = 0 := by decide
theorem σm1 : σm 1 = 2 := by decide
theorem σm2 : σm 2 = 1 := by decide

noncomputable def α : ℝ := D.model.angleAt (σm 0)

theorem o0 : D.model.oppLen (σm 0) = 1890 * 3 := by rw [σm0]; exact m_opp0
theorem o1 : D.model.oppLen (σm 1) = 1890 * 5 := by rw [σm1]; exact m_opp2
theorem o2 : D.model.oppLen (σm 2) = 1890 * 7 := by rw [σm2]; exact m_opp1

theorem data : D.model.TwoPiThreeData α (1890 * 3) (1890 * 5) (1890 * 7) :=
  tp_data D.model σm 1890 3 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) o0 o1 o2

theorem cos_α : Real.cos α = 13 / 14 := by
  unfold α
  rw [cos_s0 D.model σm (by rw [o1]; norm_num) (by rw [o2]; norm_num), o0, o1, o2]; norm_num

theorem α_irr : IrrPi α :=
  irrPi_of_cos α (13 / 14) (by rw [cos_α]; norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem t_angle (k : Fin 3) : D.target.angleAt k = Real.pi / 3 := by
  have hpi := Real.pi_pos
  have key : Real.cos (D.target.angleAt k) = 1 / 2 := by
    fin_cases k
    · have := cos_s0 D.target 1 (by simp [t_opp1]) (by simp [t_opp2])
      simp only [Equiv.Perm.coe_one, id_eq] at this
      rw [show ((⟨0, by omega⟩ : Fin 3)) = 0 from rfl, this, t_opp0, t_opp1, t_opp2]; norm_num
    · have := cos_s1 D.target 1 (by simp [t_opp0]) (by simp [t_opp2])
      simp only [Equiv.Perm.coe_one, id_eq] at this
      rw [show ((⟨1, by omega⟩ : Fin 3)) = 1 from rfl, this, t_opp0, t_opp1, t_opp2]; norm_num
    · have := cos_s2 D.target 1 (by simp [t_opp0]) (by simp [t_opp1])
      simp only [Equiv.Perm.coe_one, id_eq] at this
      rw [show ((⟨2, by omega⟩ : Fin 3)) = 2 from rfl, this, t_opp0, t_opp1, t_opp2]; norm_num
  exact Real.injOn_cos (Erdos634.Draft.FluxPaperWitness.cornerAngle_mem' _ _ _)
    ⟨by positivity, by linarith⟩ (key.trans Real.cos_pi_div_three.symm)

theorem equilateral : Equilateral D := t_angle


theorem premises :
    IrrPi α ∧ D.model.TwoPiThreeData α (1890 * 3) (1890 * 5) (1890 * 7) ∧ Equilateral D :=
  ⟨α_irr, data, equilateral⟩

/-- The leaf `GapE120` is FALSE at the real tiling's N = 1215. -/
theorem not_gapE120_1215 : ¬ GapE120 1215 := by
  have h := cert_len
  intro g
  rw [← h] at g
  exact g D α _ _ _ α_irr data equilateral

/-- Negative control: the leaf's decidable arithmetic check fails at N = 1215, with the tiling's own data
`(s,t) = (27,135)`, `s+t = 162 ∣ 2N`. -/
theorem not_pairs120Chk_1215 : ¬ Pairs120Chk 1215 := fun h =>
  not_gapE120_1215 (gapE120_of_chk (by norm_num) h)

theorem not_pairs120Chk_1215_direct : ¬ Pairs120Chk 1215 := by decide +kernel

end Erdos634.Draft.G3CEqui135Control

#print axioms Erdos634.Draft.G3CEqui135Control.not_gapE120_1215
#print axioms Erdos634.Draft.G3CEqui135Control.not_pairs120Chk_1215
#print axioms Erdos634.Draft.G3CEqui135Control.not_pairs120Chk_1215_direct
