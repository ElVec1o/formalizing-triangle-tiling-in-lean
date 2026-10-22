import Erdos634.Draft.G3CCert
import Erdos634.Draft.G3CAng
import Erdos634.Draft.LaczFormalBZL7i1

-- Draft/LaczFormalBZL7j4.lean -- COUNTEREXAMPLE showing that "alpha not in Q pi" cannot be dropped from Beeson-Zhang Thm 1.1 (and from `bz_thm11`):
-- three copies of the (30,30,120) triangle (sides 2, 2, 2 sqrt 3; Eisenstein-lattice certificate, `G3CCert`) tile an equilateral triangle by rotation about its centre.
--   `witness_30_30_120` : a genuine `CongruentDissection 3` with `TwoPiThreeData (pi/6) 2 2 (2 sqrt 3)`, alpha = pi/6 in Q pi, target NOT similar to the tile (`NotSim`), and the sides 2, 2 sqrt 3 NOT commensurable.
-- This is exactly Laczkovich's (1995) Thm 5.1 case for the tile (pi/6, pi/6, 2pi/3); it is the branch `alpha = pi/6, equilateral` of `bz_rational_classify` (BZL7j3).  NOTE, UNAUDITED.
-- Credit: Laczkovich (Discrete Math. 140 (1995) Thm 5.1), Beeson-Zhang (arXiv 2604.01314, hypothesis alpha not in Q pi), Herdt.

open scoped Classical
open Erdos634.Draft.LaczFormal.Thm21 Erdos634.Geometry Erdos634.Draft.G3CCert Erdos634.Draft.G3CAng Erdos634.Draft.TheoremPConditional Erdos634.Draft.LaczFormal.RG
  Erdos634.Draft.LaczFormal.BZL7Wit Erdos634.Draft.LaczFormal.BZL7i

namespace Erdos634.Draft.LaczFormal.BZL7W30

def cert : Cert := {
  target := ((2, 0), (-1, 1), (-1, -1)),
  model := ((0, 0), (2, 0), (-1, 1)),
  clusters := [.leaf ((0, 0), (2, 0), (-1, 1)), .leaf ((0, 0), (-1, 1), (-1, -1)), .leaf ((0, 0), (-1, -1), (2, 0))],
  seps := [((-1, 1), (0, 0)), ((0, 0), (2, 0)), ((-1, -1), (0, 0))] }

theorem cert_ok : cert.ok = true := by decide +kernel
theorem cert_len : cert.leaves.length = 3 := by decide +kernel

noncomputable abbrev D := cd cert cert_ok

theorem sqrt12 : Real.sqrt 12 = 2 * Real.sqrt 3 := by
  rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

theorem dist12 (p q : LP) (h : d2 p q = 12) : dist (toPt p) (toPt q) = 2 * Real.sqrt 3 := by
  have h1 := dist_sq_toPt p q
  rw [h] at h1
  have h2 : (2 * Real.sqrt 3) ^ 2 = 12 := by nlinarith [s3sq]
  exact (pow_left_inj₀ dist_nonneg (by positivity) two_ne_zero).mp (by rw [h1, h2]; norm_num)

theorem m_opp0 : D.model.oppLen 0 = 2 * Real.sqrt 3 := by
  rw [show D.model = _ from cd_model cert cert_ok, oppLen_triOf]
  exact dist12 _ _ (by decide)
theorem m_opp1 : D.model.oppLen 1 = 2 := by
  rw [show D.model = _ from cd_model cert cert_ok, oppLen_triOf]
  exact dist_toPt_nat _ _ 2 (by decide) |>.trans (by norm_num)
theorem m_opp2 : D.model.oppLen 2 = 2 := by
  rw [show D.model = _ from cd_model cert cert_ok, oppLen_triOf]
  exact dist_toPt_nat _ _ 2 (by decide) |>.trans (by norm_num)
theorem t_opp0 : D.target.oppLen 0 = 2 * Real.sqrt 3 := by
  rw [show D.target = _ from cd_target cert cert_ok, oppLen_triOf]
  exact dist12 _ _ (by decide)
theorem t_opp1 : D.target.oppLen 1 = 2 * Real.sqrt 3 := by
  rw [show D.target = _ from cd_target cert cert_ok, oppLen_triOf]
  exact dist12 _ _ (by decide)
theorem t_opp2 : D.target.oppLen 2 = 2 * Real.sqrt 3 := by
  rw [show D.target = _ from cd_target cert cert_ok, oppLen_triOf]
  exact dist12 _ _ (by decide)

noncomputable def σ : Equiv.Perm (Fin 3) := Equiv.addRight (1 : Fin 3)
theorem σ0 : σ 0 = 1 := by decide
theorem σ1 : σ 1 = 2 := by decide
theorem σ2 : σ 2 = 0 := by decide

theorem data : D.model.TwoPiThreeData (D.model.angleAt (σ 0)) (2 * 1) (2 * 1) (2 * Real.sqrt 3) := by
  have s3 := s3sq
  refine tp_data D.model σ 2 1 1 (Real.sqrt 3) (by norm_num) (by norm_num) (by norm_num) (by nlinarith) ?_ ?_ ?_
  · rw [σ0, m_opp1]; norm_num
  · rw [σ1, m_opp2]; norm_num
  · rw [σ2, m_opp0]

theorem cos_α : Real.cos (D.model.angleAt (σ 0)) = Real.sqrt 3 / 2 := by
  have hs3 := s3pos
  rw [cos_s0 D.model σ (by rw [σ1, m_opp2]; norm_num) (by rw [σ2, m_opp0]; positivity), σ0, σ1, σ2, m_opp1, m_opp2, m_opp0]
  have s3 := s3sq
  field_simp
  nlinarith [s3]

theorem α_eq : D.model.angleAt (σ 0) = Real.pi / 6 := by
  have hpi := Real.pi_pos
  have h1 := data.alpha_range
  exact Real.injOn_cos (Erdos634.Draft.FluxPaperWitness.cornerAngle_mem' _ _ _)
    ⟨by positivity, by linarith⟩ (cos_α.trans Real.cos_pi_div_six.symm)

theorem t_angle (k : Fin 3) : D.target.angleAt k = Real.pi / 3 := by
  have hpi := Real.pi_pos
  have hs3 := s3pos
  obtain ⟨k0, k1, k2⟩ := tri_cos D.target (2 * Real.sqrt 3) (2 * Real.sqrt 3) (2 * Real.sqrt 3) (by positivity) (by positivity)
    (by positivity) t_opp0 t_opp1 t_opp2
  have e : ∀ j, Real.cos (D.target.angleAt j) = Real.cos (Real.pi / 3) → D.target.angleAt j = Real.pi / 3 := fun j hj =>
    Real.injOn_cos (Erdos634.Draft.FluxPaperWitness.cornerAngle_mem' _ _ _) ⟨by positivity, by linarith⟩ hj
  fin_cases k
  · exact e 0 (by rw [Real.cos_pi_div_three, k0]; field_simp; ring)
  · exact e 1 (by rw [Real.cos_pi_div_three, k1]; field_simp; ring)
  · exact e 2 (by rw [Real.cos_pi_div_three, k2]; field_simp; ring)

theorem not_comm : ¬ Comm (2 * 1 : ℝ) (2 * Real.sqrt 3) := by
  rintro ⟨p, q, hp, hq, e⟩
  have hirr : Irrational (Real.sqrt 3) := Nat.Prime.irrational_sqrt (by norm_num)
  apply hirr
  refine ⟨(p : ℚ) / q, ?_⟩
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  push_cast
  field_simp
  linarith

theorem witness_30_30_120 : ∃ (N : ℕ) (D : CongruentDissection N) (α a b c : ℝ), D.model.TwoPiThreeData α a b c ∧
    α = Real.pi / 6 ∧ (∃ r : ℚ, α = (r : ℝ) * Real.pi) ∧ NotSim D ∧ ¬ Comm a c ∧ N = 3 := by
  have hpi := Real.pi_pos
  have hs3 := s3pos
  have hNS : NotSim D := by
    refine notSim_of_no_match D data 0 ?_ ?_ ?_
    · rw [t_angle, α_eq]; intro e; linarith
    · rw [t_angle, α_eq]; intro e; linarith
    · rw [t_angle]; intro e; linarith
  exact ⟨_, D, _, _, _, _, data, α_eq, ⟨1 / 6, by rw [α_eq]; push_cast; ring⟩, hNS, not_comm, cert_len⟩

end Erdos634.Draft.LaczFormal.BZL7W30

#print axioms Erdos634.Draft.LaczFormal.BZL7W30.α_eq
#print axioms Erdos634.Draft.LaczFormal.BZL7W30.t_angle
#print axioms Erdos634.Draft.LaczFormal.BZL7W30.not_comm
#print axioms Erdos634.Draft.LaczFormal.BZL7W30.witness_30_30_120
