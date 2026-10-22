-- Draft/G3CAtomControl.lean — G3C (room FINISH, seat HILBERT). UNAUDITED. No sorry/native_decide/axioms.
-- REAL control for node S5 (`RAStatement`, R-A) and Row 13 joint witness: the certified 48-tiling of the
-- isosceles ATOM A_4 at (e,f) = (1,2): target (legs 24, base 12; angles (alpha+beta, alpha+beta, alpha)) by the
-- 3alpha+2beta tile (2,3,4) (cos alpha = 7/8, cos beta = 11/16).  N = 48 = b m^2 (b=3, m=4); not prime, so
-- the prime-free variant of R-A (conclusion BaseBetaTiled, which is false in Lean) is REFUTED here.
import Erdos634.Draft.G3CAtomTilingBridge
import Erdos634.Draft.G3CAng
import Erdos634.Draft.FluxGridWitness

open scoped Classical

namespace Erdos634.Draft.G3CAtomControl

open Erdos634.Geometry Erdos634.Z15Real Erdos634.Draft.G3CAng Erdos634.Draft.TheoremPConditional
open Erdos634.G3CAtomTilingBridge (pieceTri headI_mem_tiles vertexOf targetTri toZPt dist2_eq_zdist2)
open Erdos634.Draft.FluxGridWitness (α44 β44 α44_irr three_α_two_β cos_α44 cos_β44)
open Erdos634.Draft.FluxPaperWitness (cornerAngle_mem')

noncomputable abbrev D := Erdos634.G3CAtomTilingBridge.dissection

theorem d_model : D.model = pieceTri headI_mem_tiles := rfl
theorem d_target : D.target = targetTri := rfl

theorem m_opp0 : D.model.oppLen 0 = 16 := by
  have e : G3CAtomTiling.dist2 (vertexOf G3CAtomTiling.tiles.headI 1) (vertexOf G3CAtomTiling.tiles.headI 2)
      = ((256:ℤ),(0:ℤ)) := by decide
  unfold Tri.oppLen
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl]
  exact Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num)
    (by rw [d_model, Erdos634.G3CAtomTilingBridge.pieceTri_dist_sq _ _ 1 2, e]; simp [toR]; norm_num)

theorem m_opp1 : D.model.oppLen 1 = 24 := by
  have e : G3CAtomTiling.dist2 (vertexOf G3CAtomTiling.tiles.headI 2) (vertexOf G3CAtomTiling.tiles.headI 0)
      = ((576:ℤ),(0:ℤ)) := by decide
  unfold Tri.oppLen
  simp only [show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl]
  exact Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num)
    (by rw [d_model, Erdos634.G3CAtomTilingBridge.pieceTri_dist_sq _ _ 2 0, e]; simp [toR]; norm_num)

theorem m_opp2 : D.model.oppLen 2 = 32 := by
  have e : G3CAtomTiling.dist2 (vertexOf G3CAtomTiling.tiles.headI 0) (vertexOf G3CAtomTiling.tiles.headI 1)
      = ((1024:ℤ),(0:ℤ)) := by decide
  unfold Tri.oppLen
  simp only [show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
  exact Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num)
    (by rw [d_model, Erdos634.G3CAtomTilingBridge.pieceTri_dist_sq _ _ 0 1, e]; simp [toR]; norm_num)

theorem t_opp0 : D.target.oppLen 0 = 192 := by
  unfold Tri.oppLen
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl]
  exact Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num)
    (by rw [d_target, (Erdos634.G3CAtomTilingBridge.targetTri_sides).2.1]; norm_num)
theorem t_opp1 : D.target.oppLen 1 = 192 := by
  unfold Tri.oppLen
  simp only [show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl]
  exact Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num)
    (by rw [d_target, (Erdos634.G3CAtomTilingBridge.targetTri_sides).2.2]; norm_num)
theorem t_opp2 : D.target.oppLen 2 = 96 := by
  unfold Tri.oppLen
  simp only [show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
  exact Erdos634.Draft.FluxWitness.dist_of_sq' (by norm_num)
    (by rw [d_target, (Erdos634.G3CAtomTilingBridge.targetTri_sides).1]; norm_num)

theorem model_angle0 : D.model.angleAt 0 = α44 := by
  have := cos_s0 D.model 1 (by simp [m_opp1]) (by simp [m_opp2])
  simp only [Equiv.Perm.coe_one, id_eq] at this
  have hcos : Real.cos (D.model.angleAt 0) = 7 / 8 := by
    rw [this, m_opp0, m_opp1, m_opp2]; norm_num
  exact Real.injOn_cos (cornerAngle_mem' _ _ _) (cornerAngle_mem' _ _ _) (hcos.trans cos_α44.symm)

theorem model_angle1 : D.model.angleAt 1 = β44 := by
  have := cos_s1 D.model 1 (by simp [m_opp0]) (by simp [m_opp2])
  simp only [Equiv.Perm.coe_one, id_eq] at this
  have hcos : Real.cos (D.model.angleAt 1) = 11 / 16 := by
    rw [this, m_opp0, m_opp1, m_opp2]; norm_num
  exact Real.injOn_cos (cornerAngle_mem' _ _ _) (cornerAngle_mem' _ _ _) (hcos.trans cos_β44.symm)

theorem threeAlpha : D.model.ThreeAlphaData α44 β44 16 24 32 := by
  refine ⟨1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using model_angle0
  · simpa using m_opp0
  · simpa using model_angle1
  · simpa using m_opp1
  · simp only [Equiv.Perm.coe_one, id_eq]
    have hs := D.model.angleAt_sum
    rw [model_angle0, model_angle1] at hs
    linarith [three_α_two_β]
  · simpa using m_opp2

theorem t_angle2 : D.target.angleAt 2 = α44 := by
  have := cos_s2 D.target 1 (by simp [t_opp0]) (by simp [t_opp1])
  simp only [Equiv.Perm.coe_one, id_eq] at this
  have hcos : Real.cos (D.target.angleAt 2) = 7 / 8 := by
    rw [this, t_opp0, t_opp1, t_opp2]; norm_num
  exact Real.injOn_cos (cornerAngle_mem' _ _ _) (cornerAngle_mem' _ _ _) (hcos.trans cos_α44.symm)

theorem t_angle01 : D.target.angleAt 0 = D.target.angleAt 1 := by
  have h0 := cos_s0 D.target 1 (by simp [t_opp1]) (by simp [t_opp2])
  have h1 := cos_s1 D.target 1 (by simp [t_opp0]) (by simp [t_opp2])
  simp only [Equiv.Perm.coe_one, id_eq] at h0 h1
  exact angle_eq_of_cos 0 1 (by rw [h0, h1, t_opp0, t_opp1, t_opp2])

theorem t_angle0 : D.target.angleAt 0 = α44 + β44 := by
  have hs := D.target.angleAt_sum
  rw [← t_angle01, t_angle2] at hs
  linarith [three_α_two_β]

theorem t_angle1 : D.target.angleAt 1 = α44 + β44 := by rw [← t_angle01]; exact t_angle0

theorem tgt_atom : TgtAngles D (α44 + β44) (α44 + β44) α44 :=
  ⟨1, by simpa using t_angle0, by simpa using t_angle1, by simpa using t_angle2⟩

/-- **S5 control**: every non-arithmetic premise of `RAStatement` holds on the real 48-tiling of the atom A_4
(r = 1/2: 16 = (1/2)*32, 24 = (1 - 1/4)*32). -/
theorem rA_premises :
    IrrPi α44 ∧ 3 * α44 + 2 * β44 = Real.pi ∧ D.model.ThreeAlphaData α44 β44 16 24 32 ∧
      (16 : ℝ) = ((1 / 2 : ℚ) : ℝ) * 32 ∧ (24 : ℝ) = (1 - ((1 / 2 : ℚ) : ℝ) ^ 2) * 32 ∧
      TgtAngles D (α44 + β44) (α44 + β44) α44 :=
  ⟨α44_irr, three_α_two_β, threeAlpha, by norm_num, by norm_num, tgt_atom⟩

/-- The prime-free variant of R-A (S5) is REFUTED by the real 48-tiling of A_4: S5 rests on primality. -/
theorem rA_primeFree_refuted :
    ¬ (∀ (N : ℕ) (D : CongruentDissection N) (α β a b c : ℝ) (r : ℚ), IrrPi α →
        3 * α + 2 * β = Real.pi → D.model.ThreeAlphaData α β a b c → a = (r : ℝ) * c →
        b = (1 - (r : ℝ) ^ 2) * c → TgtAngles D (α + β) (α + β) α → BaseBetaTiled) := by
  intro h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := rA_premises
  exact not_baseBetaTiled (h _ D α44 β44 16 24 32 (1 / 2) h1 h2 h3 h4 h5 h6)

end Erdos634.Draft.G3CAtomControl

#print axioms Erdos634.Draft.G3CAtomControl.rA_primeFree_refuted
