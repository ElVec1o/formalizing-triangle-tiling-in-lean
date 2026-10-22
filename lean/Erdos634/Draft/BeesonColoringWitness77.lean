import Erdos634.Draft.BeesonColoringThm15
import Erdos634.Draft.BeesonT14_2_3_4
import Erdos634.Draft.FluxGridWitness
import Erdos634.Draft.FluxDRow4AnyLabel
import Erdos634.Draft.FluxFRow14AnyLabel

/-!
# Non-vacuity of `Beeson.thm13` / `Beeson.thm15_only_if`: Beeson's 77-tiling of `(2 alpha, alpha, 2 beta)`

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Fig. 15, Thm 13, Thm 15), Beeson-Zhang, Laczkovich.
The 77-tiling is `BeesonT14_2_3_4.beeson_t14_2_3_4` (the triangle `A = (0,0)`, `C = (16,0)`,
`B = (561/32, (231/32) sqrt 15)` tiled by 77 copies of the tile `(2,3,4)`).  It is turned into a
`CongruentDissection 77` with target angles `(2 alpha, alpha, 2 beta)` at vertices `(0, 1, 2)` (relabelling of the
vertices `(A, C, B)` by the swap `1 <-> 2`) and the tile angles `alpha, beta` are the project's `alpha44, beta44`
(`cos = 7/8, 11/16`, `alpha44 not in Q pi` proved in `FluxGridWitness`).  Consequence: every hypothesis of
`thm13`, `thm15_only_if` is witnessed jointly, and the conclusion yields Beeson's `M = 5`, `s = 1/2`.
-/

open scoped Classical

namespace Erdos634.BeesonColoring.W77

open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.ZhangSporadic
  Erdos634.BeesonT14.I_2_3_4 Erdos634.Draft.FluxGridWitness

/-! ## the tile `T0 = (2,3,4)` -/

theorem m_d01 : dist (T0.pts 0) (T0.pts 1) = 4 :=
  Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num) (by
    show dist (mkPt 0 0) (mkPt 4 0) ^ 2 = _
    rw [dist_sq_mkPt]; norm_num)

theorem m_d02 : dist (T0.pts 0) (T0.pts 2) = 3 :=
  Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num) (by
    show dist (mkPt 0 0) (mkPt (21 / 8) ((3 / 8) * rt)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination (9 / 64 : ℝ) * rt_sq)

theorem m_d12 : dist (T0.pts 1) (T0.pts 2) = 2 :=
  Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num) (by
    show dist (mkPt 4 0) (mkPt (21 / 8) ((3 / 8) * rt)) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination (9 / 64 : ℝ) * rt_sq)

theorem m_opp : T0.oppLen 0 = 2 ∧ T0.oppLen 1 = 3 ∧ T0.oppLen 2 = 4 := by
  unfold Tri.oppLen
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl,
    show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl,
    show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
  refine ⟨m_d12, ?_, ?_⟩
  · rw [dist_comm]; exact m_d02
  · exact m_d01

theorem m_angle0 : T0.angleAt 0 = α44 := by
  have hcos : Real.cos (T0.angleAt 0) = 7 / 8 := by
    unfold Tri.angleAt
    simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl]
    rw [cos_cornerAngle (ne_of_dist m_d01 (by norm_num)).symm (ne_of_dist m_d02 (by norm_num)).symm,
      dist_comm (T0.pts 1) (T0.pts 0), dist_comm (T0.pts 2) (T0.pts 0), m_d01, m_d02, m_d12]
    norm_num
  exact Real.injOn_cos (cornerAngle_mem _ _ _) (cornerAngle_mem _ _ _) (hcos.trans cos_α44.symm)

theorem m_angle1 : T0.angleAt 1 = β44 := by
  have hcos : Real.cos (T0.angleAt 1) = 11 / 16 := by
    unfold Tri.angleAt
    simp only [show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl]
    rw [cos_cornerAngle (ne_of_dist m_d12 (by norm_num)).symm (ne_of_dist m_d01 (by norm_num)),
      dist_comm (T0.pts 2) (T0.pts 1), m_d12, m_d01, dist_comm (T0.pts 2) (T0.pts 0), m_d02]
    norm_num
  exact Real.injOn_cos (cornerAngle_mem _ _ _) (cornerAngle_mem _ _ _) (hcos.trans cos_β44.symm)

theorem m_angle2 : T0.angleAt 2 = 2 * α44 + β44 := by
  have hs := T0.angleAt_sum
  rw [m_angle0, m_angle1] at hs
  have h := three_α_two_β
  linarith

theorem data77 : T0.ThreeAlphaData α44 β44 2 3 4 :=
  ⟨1, m_angle0, m_opp.1, m_angle1, m_opp.2.1, m_angle2, m_opp.2.2⟩

/-! ## the target `(A, C, B)` -/

theorem hdetP : 0 < det3 0 (rt * 0) 16 (rt * 0) (561 / 32) (rt * (231 / 32)) := by
  have := rt_pos
  unfold det3; nlinarith

noncomputable def TP : Tri := mkTri 0 (rt * 0) 16 (rt * 0) (561 / 32) (rt * (231 / 32)) hdetP.ne'

theorem t_d01 : dist (TP.pts 0) (TP.pts 1) = 16 :=
  Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num) (by
    show dist (mkPt 0 (rt * 0)) (mkPt 16 (rt * 0)) ^ 2 = _
    rw [dist_sq_mkPt]; norm_num)

theorem t_d02 : dist (TP.pts 0) (TP.pts 2) = 33 :=
  Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num) (by
    show dist (mkPt 0 (rt * 0)) (mkPt (561 / 32) (rt * (231 / 32))) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((231 / 32 : ℝ) ^ 2) * rt_sq)

theorem t_d12 : dist (TP.pts 1) (TP.pts 2) = 28 :=
  Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num) (by
    show dist (mkPt 16 (rt * 0)) (mkPt (561 / 32) (rt * (231 / 32))) ^ 2 = _
    rw [dist_sq_mkPt]; linear_combination ((231 / 32 : ℝ) ^ 2) * rt_sq)

theorem t_angle0 : TP.angleAt 0 = 2 * α44 := by
  have hcos : Real.cos (TP.angleAt 0) = 17 / 32 := by
    unfold Tri.angleAt
    simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl]
    rw [cos_cornerAngle (ne_of_dist t_d01 (by norm_num)).symm (ne_of_dist t_d02 (by norm_num)).symm,
      dist_comm (TP.pts 1) (TP.pts 0), dist_comm (TP.pts 2) (TP.pts 0), t_d01, t_d02, t_d12]
    norm_num
  have hc2 : Real.cos (2 * α44) = 17 / 32 := by rw [Real.cos_two_mul, cos_α44]; norm_num
  have hα0 : 0 ≤ α44 := (cornerAngle_mem _ _ _).1
  have hαle := α44_le
  have hπ := Real.pi_pos
  exact Real.injOn_cos (cornerAngle_mem _ _ _) ⟨by linarith, by linarith⟩ (hcos.trans hc2.symm)

theorem t_angle1 : TP.angleAt 1 = 2 * β44 := by
  have hcos : Real.cos (TP.angleAt 1) = -7 / 128 := by
    unfold Tri.angleAt
    simp only [show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl]
    rw [cos_cornerAngle (ne_of_dist t_d12 (by norm_num)).symm (ne_of_dist t_d01 (by norm_num)),
      dist_comm (TP.pts 2) (TP.pts 1), t_d12, t_d01, dist_comm (TP.pts 2) (TP.pts 0), t_d02]
    norm_num
  have h2β : 2 * β44 = Real.pi - 3 * α44 := by linarith [three_α_two_β]
  have hc2 : Real.cos (2 * β44) = -7 / 128 := by
    rw [h2β, Real.cos_pi_sub, Real.cos_three_mul, cos_α44]; norm_num
  have hα0 : 0 ≤ α44 := (cornerAngle_mem _ _ _).1
  have hαle := α44_le
  exact Real.injOn_cos (cornerAngle_mem _ _ _) ⟨by linarith, by linarith⟩ (hcos.trans hc2.symm)

theorem t_angle2 : TP.angleAt 2 = α44 := by
  have hcos : Real.cos (TP.angleAt 2) = 7 / 8 := by
    unfold Tri.angleAt
    simp only [show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
    rw [cos_cornerAngle (ne_of_dist t_d02 (by norm_num)) (ne_of_dist t_d12 (by norm_num)),
      t_d02, t_d12, t_d01]
    norm_num
  exact Real.injOn_cos (cornerAngle_mem _ _ _) (cornerAngle_mem _ _ _) (hcos.trans cos_α44.symm)

/-- The swap `1 <-> 2` of target vertices. -/
def swp : Equiv.Perm (Fin 3) := Equiv.swap 1 2

theorem swp0 : swp 0 = 0 := by decide
theorem swp1 : swp 1 = 2 := by decide
theorem swp2 : swp 2 = 1 := by decide

/-- **A genuine `CongruentDissection 77`** with target angles `(2 alpha, alpha, 2 beta)` and a `3 alpha + 2 beta = pi`
tile `(2,3,4)` (angles `alpha44, beta44`). -/
theorem exists_D77 : ∃ D : CongruentDissection 77,
    D.model.ThreeAlphaData α44 β44 2 3 4 ∧ D.target.angleAt 0 = 2 * α44 ∧
      D.target.angleAt 1 = α44 ∧ D.target.angleAt 2 = 2 * β44 := by
  obtain ⟨C, hreg, hm⟩ := beeson_t14_2_3_4
  set D0 : CongruentDissection 77 :=
    C.toCongruentDissection TP (hreg.trans (TriSet_eq_carrier hdetP)) with hD0
  have hmod : D0.model = T0 := hm
  have hTt : D0.target = TP := rfl
  set D := D0.relabelTarget' swp with hD
  have hT : ∀ k, D.target.pts k = D0.target.pts (swp k) := fun k => rfl
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · show D0.model.ThreeAlphaData α44 β44 2 3 4
    rw [hmod]; exact data77
  · rw [Row14AnyLabel.angleAt_of_pts swp hT, swp0, hTt]; exact t_angle0
  · rw [Row14AnyLabel.angleAt_of_pts swp hT, swp1, hTt]; exact t_angle2
  · rw [Row14AnyLabel.angleAt_of_pts swp hT, swp2, hTt]; exact t_angle1

/-- **Non-vacuity of `Beeson.thm13`**: the 77-tiling gives Beeson's `N = 77`, `M = 5`, `s = 1/2`. -/
theorem thm13_at_77 : ∃ D : CongruentDissection 77, ∃ (M : ℤ) (s : ℚ), D.model.ThreeAlphaData α44 β44 2 3 4 ∧
    M = 5 ∧ s = 1 / 2 ∧ (77 : ℚ) / (M : ℚ) ^ 2 = (2 - s ^ 2) * (3 - s ^ 2) / ((1 - s) ^ 2 * (2 + s) ^ 2) := by
  obtain ⟨D, h, e0, e1, e2⟩ := exists_D77
  obtain ⟨M, s, hM, hsac, -, -, -, -, heq, hdiv⟩ :=
    Erdos634.BeesonColoring.thm13 D α44_irr three_α_two_β h e0 e1 e2
  have hs : s = 1 / 2 := by
    have : ((s : ℚ) : ℝ) = (((1 / 2 : ℚ)) : ℝ) := by rw [hsac]; norm_num
    exact Rat.cast_injective this
  subst hs
  have hM2 : (M : ℚ) ^ 2 = 25 := by
    norm_num at heq
    linarith
  have hMz : M = 5 := by
    have h1 : M ^ 2 = 25 := by exact_mod_cast hM2
    nlinarith
  refine ⟨D, M, 1 / 2, h, hMz, rfl, ?_⟩
  simpa using hdiv

/-- **Non-vacuity of `Beeson.thm15_only_if`** at the 77-tiling with integers `(a, b, c) = (2, 3, 4)`, `k = 1`. -/
theorem thm15_at_77 : ∃ D : CongruentDissection 77, ∃ M : ℤ, 0 < M ∧
    (77 : ℤ) * (3 + 4 - 2) ^ 2 = (3 + 4) * (3 + 2 * 4) * M ^ 2 ∧ M = 5 := by
  obtain ⟨D, h, e0, e1, e2⟩ := exists_D77
  have h' : D.model.ThreeAlphaData α44 β44 (1 * ((2 : ℤ) : ℝ)) (1 * ((3 : ℤ) : ℝ)) (1 * ((4 : ℤ) : ℝ)) := by
    simpa using h
  obtain ⟨-, -, -, -, M, hM, heq⟩ :=
    Erdos634.BeesonColoring.thm15_only_if D 2 3 4 one_pos α44_irr three_α_two_β h' e0 e1 e2
  refine ⟨D, M, hM, by simpa using heq, ?_⟩
  have h1 : M ^ 2 = 25 := by norm_num at heq; nlinarith
  nlinarith

end Erdos634.BeesonColoring.W77

#print axioms Erdos634.BeesonColoring.W77.exists_D77
#print axioms Erdos634.BeesonColoring.W77.thm13_at_77
#print axioms Erdos634.BeesonColoring.W77.thm15_at_77
