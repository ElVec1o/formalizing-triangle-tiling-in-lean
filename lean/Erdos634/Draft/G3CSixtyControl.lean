-- Draft/G3CSixtyControl.lean — G3C (room FINISH, seat HILBERT). UNAUDITED. No sorry/native_decide/axioms.
-- Premise-satisfiability control for node C3 (`LemmaPStatement`, lemma P / `lemmaP_general`): the certified
-- 1440-tiling (Zhang Thm 5 / Herdt, m = 6) of the EQUILATERAL triangle of side 240 by the irrational pi/3-angle
-- tile (5,8,7) (7 opposite pi/3).  Lemma P is true prime-free, so no refutation exists; this shows its premises
-- (IrrPi, SixtyData, not similar) are jointly satisfied by a real dissection.
import Erdos634.Draft.G3CEqui60n1440
import Erdos634.Draft.G3CAng

open scoped Classical

namespace Erdos634.Draft.G3CSixtyControl

open Erdos634.Geometry Erdos634.Draft.G3CCert Erdos634.Draft.G3CAng Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.G3CEqui60n1440 (cert cert_ok cert_len)

noncomputable abbrev D := cd cert cert_ok

theorem m_opp0 : D.model.oppLen 0 = 3360 * 7 := by
  rw [show D.model = _ from cd_model cert cert_ok, oppLen_triOf]
  have := dist_toPt_nat (vtx cert.model (0 + 1)) (vtx cert.model (0 + 2)) 23520 (by decide)
  rw [this]; norm_num
theorem m_opp1 : D.model.oppLen 1 = 3360 * 5 := by
  rw [show D.model = _ from cd_model cert cert_ok, oppLen_triOf]
  have := dist_toPt_nat (vtx cert.model (1 + 1)) (vtx cert.model (1 + 2)) 16800 (by decide)
  rw [this]; norm_num
theorem m_opp2 : D.model.oppLen 2 = 3360 * 8 := by
  rw [show D.model = _ from cd_model cert cert_ok, oppLen_triOf]
  have := dist_toPt_nat (vtx cert.model (2 + 1)) (vtx cert.model (2 + 2)) 26880 (by decide)
  rw [this]; norm_num
theorem t_opp0 : D.target.oppLen 0 = 806400 := by
  rw [show D.target = _ from cd_target cert cert_ok, oppLen_triOf]
  have := dist_toPt_nat (vtx cert.target (0 + 1)) (vtx cert.target (0 + 2)) 806400 (by decide)
  rw [this]; norm_num
theorem t_opp1 : D.target.oppLen 1 = 806400 := by
  rw [show D.target = _ from cd_target cert cert_ok, oppLen_triOf]
  have := dist_toPt_nat (vtx cert.target (1 + 1)) (vtx cert.target (1 + 2)) 806400 (by decide)
  rw [this]; norm_num
theorem t_opp2 : D.target.oppLen 2 = 806400 := by
  rw [show D.target = _ from cd_target cert cert_ok, oppLen_triOf]
  have := dist_toPt_nat (vtx cert.target (2 + 1)) (vtx cert.target (2 + 2)) 806400 (by decide)
  rw [this]; norm_num

/-- sigma sends (opp 5, opp 8, opp 7) to vertices (1, 2, 0) -/
noncomputable def σm : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
theorem σm0 : σm 0 = 1 := by decide
theorem σm1 : σm 1 = 2 := by decide
theorem σm2 : σm 2 = 0 := by decide

noncomputable def α : ℝ := D.model.angleAt (σm 0)

theorem o0 : D.model.oppLen (σm 0) = 3360 * 5 := by rw [σm0]; exact m_opp1
theorem o1 : D.model.oppLen (σm 1) = 3360 * 8 := by rw [σm1]; exact m_opp2
theorem o2 : D.model.oppLen (σm 2) = 3360 * 7 := by rw [σm2]; exact m_opp0

theorem data : D.model.SixtyData α (3360 * 5) (3360 * 8) (3360 * 7) :=
  sixty_data D.model σm 3360 5 8 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) o0 o1 o2

theorem cos_α : Real.cos α = 11 / 14 := by
  unfold α
  rw [cos_s0 D.model σm (by rw [o1]; norm_num) (by rw [o2]; norm_num), o0, o1, o2]; norm_num

theorem α_irr : IrrPi α :=
  irrPi_of_cos α (11 / 14) (by rw [cos_α]; norm_num) (by norm_num) (by norm_num) (by norm_num)
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

theorem not_similar : ¬ SimilarTM D := by
  rintro ⟨μ, τ, hs⟩
  obtain ⟨k, hk⟩ := τ.surjective (σm 0)
  have h := (hs k).1
  rw [hk, t_angle k] at h
  apply α_irr
  exact ⟨1 / 3, by rw [show D.model.angleAt (σm 0) = α from rfl] at h; rw [← h]; push_cast; ring⟩

/-- **C3 control**: the premises of `LemmaPStatement` are jointly satisfied by a real dissection
(N = 1440 = 36*40, equilateral side 240, tile (5,8,7), 7 opposite pi/3). -/
theorem lemmaP_premises_satisfied :
    ∃ (N : ℕ) (D : CongruentDissection N) (α a b c : ℝ),
      IrrPi α ∧ D.model.SixtyData α a b c ∧ ¬ SimilarTM D ∧ Equilateral D :=
  ⟨_, D, α, _, _, _, α_irr, data, not_similar, equilateral⟩

end Erdos634.Draft.G3CSixtyControl

#print axioms Erdos634.Draft.G3CSixtyControl.lemmaP_premises_satisfied
