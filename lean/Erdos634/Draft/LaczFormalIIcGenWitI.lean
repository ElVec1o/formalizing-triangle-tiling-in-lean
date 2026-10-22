-- Draft/LaczFormalIIcGenWitI.lean -- WITNESS of the GENERIC Case IIc block (alpha != beta), step I: the model tile.  Sides (a, b, c) = (1, 2, sqrt(5 - 2 sqrt 2)) opposite the model vertices (0, 1, 2); cosines by the law of cosines;
-- gamma = pi/4; AngGen (alpha != beta, no right angle); Comm a b; not Comm a c; NotComb.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcGenWitH
import Erdos634.Draft.LaczFormalRG12Fan222
import Erdos634.Draft.LaczFormalRG4Arith
import Erdos634.Draft.LaczFormalBase
import Erdos634.Draft.LaczFormalRGSideStep

namespace Erdos634.Draft.LaczFormal.GenWit

open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Thm21 Erdos634.Draft.LaczFormal.RG Erdos634.Draft.LaczFormal.Graph Z2

theorem M0_pts (k : Fin 3) : genDiss.model.pts k = ptR (modelTZ.pt k) := triZ_pts valid_model k

theorem dsq (k l : Fin 3) (z : Z2) (h : d2 (modelTZ.pt k) (modelTZ.pt l) = z) :
    dist (genDiss.model.pts k) (genDiss.model.pts l) ^ 2 = z.val / 4 := by
  rw [M0_pts, M0_pts, dist_sq_ptR, h]

theorem slen0_eq : RG.slen genDiss 0 = 1 := by
  have h : dist (genDiss.model.pts 1) (genDiss.model.pts 2) ^ 2 = 1 := by
    rw [dsq 1 2 ⟨4, 0⟩ (by decide)]; unfold Z2.val; norm_num
  have hn : 0 ≤ dist (genDiss.model.pts 1) (genDiss.model.pts 2) := dist_nonneg
  show dist (genDiss.model.pts 1) (genDiss.model.pts 2) = 1
  nlinarith

theorem slen1_eq : RG.slen genDiss 1 = 2 := by
  have h : dist (genDiss.model.pts 2) (genDiss.model.pts 0) ^ 2 = 4 := by
    rw [dsq 2 0 ⟨16, 0⟩ (by decide)]; unfold Z2.val; norm_num
  have hn : 0 ≤ dist (genDiss.model.pts 2) (genDiss.model.pts 0) := dist_nonneg
  show dist (genDiss.model.pts 2) (genDiss.model.pts 0) = 2
  nlinarith

/-- `c = slen 2`, `c^2 = 5 - 2 sqrt 2` -/
theorem slen2_sq : RG.slen genDiss 2 ^ 2 = 5 - 2 * Real.sqrt 2 := by
  have h : dist (genDiss.model.pts 0) (genDiss.model.pts 1) ^ 2 = (⟨20, -8⟩ : Z2).val / 4 := dsq 0 1 ⟨20, -8⟩ (by decide)
  have e : (⟨20, -8⟩ : Z2).val / 4 = 5 - 2 * Real.sqrt 2 := by unfold Z2.val; push_cast; ring
  rw [e] at h
  exact h

theorem slen2_pos : 0 < RG.slen genDiss 2 := RG.slen_pos genDiss 2

theorem sqrt2_lt_two : Real.sqrt 2 < 2 := by
  have := Z2.hs; have := Z2.hspos; nlinarith
theorem one_lt_sqrt2 : 1 < Real.sqrt 2 := by
  have := Z2.hs; have := Z2.hspos; nlinarith

/-! ## Cosine laws for the model -/

theorem cos_laws (T : Tri) :
    2 * dist (T.pts 2) (T.pts 0) * dist (T.pts 0) (T.pts 1) * Real.cos (T.angleAt 0) = dist (T.pts 2) (T.pts 0) ^ 2 + dist (T.pts 0) (T.pts 1) ^ 2 - dist (T.pts 1) (T.pts 2) ^ 2 ∧
    2 * dist (T.pts 0) (T.pts 1) * dist (T.pts 1) (T.pts 2) * Real.cos (T.angleAt 1) = dist (T.pts 0) (T.pts 1) ^ 2 + dist (T.pts 1) (T.pts 2) ^ 2 - dist (T.pts 2) (T.pts 0) ^ 2 ∧
    2 * dist (T.pts 1) (T.pts 2) * dist (T.pts 2) (T.pts 0) * Real.cos (T.angleAt 2) = dist (T.pts 1) (T.pts 2) ^ 2 + dist (T.pts 2) (T.pts 0) ^ 2 - dist (T.pts 0) (T.pts 1) ^ 2 := by
  have a0 : T.angleAt 0 = EuclideanGeometry.angle (V := Plane) (T.pts 1) (T.pts 0) (T.pts 2) := rfl
  have a1 : T.angleAt 1 = EuclideanGeometry.angle (V := Plane) (T.pts 2) (T.pts 1) (T.pts 0) := rfl
  have a2 : T.angleAt 2 = EuclideanGeometry.angle (V := Plane) (T.pts 0) (T.pts 2) (T.pts 1) := rfl
  have l0 := EuclideanGeometry.law_cos (V := Plane) (T.pts 1) (T.pts 0) (T.pts 2)
  have l1 := EuclideanGeometry.law_cos (V := Plane) (T.pts 2) (T.pts 1) (T.pts 0)
  have l2 := EuclideanGeometry.law_cos (V := Plane) (T.pts 0) (T.pts 2) (T.pts 1)
  rw [dist_comm (T.pts 1) (T.pts 0)] at l0
  rw [dist_comm (T.pts 2) (T.pts 1)] at l1
  rw [dist_comm (T.pts 0) (T.pts 2)] at l2
  rw [a0, a1, a2]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith [l0, l1, l2]

theorem cos_laws_model :
    2 * RG.slen genDiss 1 * RG.slen genDiss 2 * Real.cos (genDiss.model.angleAt 0) = RG.slen genDiss 1 ^ 2 + RG.slen genDiss 2 ^ 2 - RG.slen genDiss 0 ^ 2 ∧
    2 * RG.slen genDiss 2 * RG.slen genDiss 0 * Real.cos (genDiss.model.angleAt 1) = RG.slen genDiss 2 ^ 2 + RG.slen genDiss 0 ^ 2 - RG.slen genDiss 1 ^ 2 ∧
    2 * RG.slen genDiss 0 * RG.slen genDiss 1 * Real.cos (genDiss.model.angleAt 2) = RG.slen genDiss 0 ^ 2 + RG.slen genDiss 1 ^ 2 - RG.slen genDiss 2 ^ 2 :=
  cos_laws genDiss.model

theorem cos0_pos : 0 < Real.cos (genDiss.model.angleAt 0) := by
  obtain ⟨e0, -, -⟩ := cos_laws_model
  rw [slen0_eq, slen1_eq] at e0
  have hc := slen2_pos; have hc2 := slen2_sq; have := sqrt2_lt_two
  by_contra h; push_neg at h
  nlinarith [mul_nonneg hc.le (neg_nonneg.mpr h)]

theorem cos1_neg : Real.cos (genDiss.model.angleAt 1) < 0 := by
  obtain ⟨-, e1, -⟩ := cos_laws_model
  rw [slen0_eq, slen1_eq] at e1
  have hc := slen2_pos; have hc2 := slen2_sq; have := one_lt_sqrt2
  by_contra h; push_neg at h
  nlinarith [mul_nonneg hc.le h]

theorem cos2_eq : Real.cos (genDiss.model.angleAt 2) = Real.sqrt 2 / 2 := by
  obtain ⟨-, -, e2⟩ := cos_laws_model
  rw [slen0_eq, slen1_eq] at e2
  have hc2 := slen2_sq
  linarith

theorem angle2_eq : genDiss.model.angleAt 2 = Real.pi / 4 := by
  have hpi := Real.pi_pos
  refine Real.injOn_cos ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
    ⟨by positivity, by linarith⟩ ?_
  show Real.cos (genDiss.model.angleAt 2) = Real.cos (Real.pi / 4)
  rw [cos2_eq, Real.cos_pi_div_four]

theorem genDiss_angle2_lt : genDiss.model.angleAt 2 < Real.pi / 2 := by
  rw [angle2_eq]; have := Real.pi_pos; linarith

theorem genDiss_angle2_ne : genDiss.model.angleAt 2 ≠ Real.pi / 3 := by
  rw [angle2_eq]; have := Real.pi_pos; intro h; linarith

theorem genDiss_angGen : AngGen (fun l => genDiss.model.angleAt l) := by
  have hpos := model_angle_pos' genDiss
  have hs := angleAt_sum genDiss.model
  have c0 := cos0_pos
  have c1 := cos1_neg
  have c2 := cos2_eq
  have hs2 := Z2.hs
  have hs2p := Z2.hspos
  have hcc := slen2_sq
  have hcp := slen2_pos
  refine ⟨hpos, hs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; have := congrArg Real.cos h; simp only at this; linarith
  · intro h
    have h' := congrArg Real.cos h
    simp only at h'
    obtain ⟨e0, -, -⟩ := cos_laws_model
    rw [slen0_eq, slen1_eq] at e0
    rw [h', c2] at e0
    have h3 : RG.slen genDiss 2 * Real.sqrt 2 = 4 - Real.sqrt 2 := by nlinarith
    have h4 : (RG.slen genDiss 2 * Real.sqrt 2) ^ 2 = (4 - Real.sqrt 2) ^ 2 := by rw [h3]
    have h5 : (RG.slen genDiss 2 * Real.sqrt 2) ^ 2 = RG.slen genDiss 2 ^ 2 * (Real.sqrt 2 * Real.sqrt 2) := by ring
    rw [h5, hcc, hs2] at h4
    have : Real.sqrt 2 = 2 := by nlinarith
    nlinarith
  · intro h; have := congrArg Real.cos h; simp only at this; rw [c2] at this; linarith
  · intro h; have := congrArg Real.cos h; simp only at this; rw [Real.cos_pi_div_two] at this; linarith
  · intro h; have := congrArg Real.cos h; simp only at this; rw [Real.cos_pi_div_two] at this; linarith
  · intro h; have := congrArg Real.cos h; simp only at this; rw [Real.cos_pi_div_two, c2] at this; linarith

/-! ## Commensurability -/

theorem slen2_not_rat (p q : ℕ) (hq : 0 < q) : (p : ℝ) ≠ q * RG.slen genDiss 2 := by
  intro h
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have hcc := slen2_sq
  have key : (q : ℝ) ^ 2 * (5 - 2 * Real.sqrt 2) = (p : ℝ) ^ 2 := by
    rw [← hcc, h]; ring
  apply irrational_sqrt_two
  refine ⟨((5 : ℚ) - (p : ℚ) ^ 2 / (q : ℚ) ^ 2) / 2, ?_⟩
  have hq2 : (q : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hq'
  push_cast
  field_simp
  linarith

theorem genDiss_comm : Comm (RG.slen genDiss 0) (RG.slen genDiss 1) :=
  ⟨2, 1, by norm_num, by norm_num, by rw [slen0_eq, slen1_eq]; norm_num⟩

theorem genDiss_notComm : ¬ Comm (RG.slen genDiss 0) (RG.slen genDiss 2) := by
  rintro ⟨p, q, hp, hq, h⟩
  rw [slen0_eq] at h
  exact slen2_not_rat p q hq (by simpa using h)

theorem genDiss_notComb : NotComb (RG.slen genDiss 2) (RG.slen genDiss 1) (RG.slen genDiss 0) := by
  intro r p q hr
  rw [slen0_eq, slen1_eq]
  intro h
  have := slen2_not_rat (2 * p + q) r hr
  apply this
  push_cast
  linarith

theorem genDiss_caseC : CaseC genDiss idx where
  hidx := genDiss_hidx
  hidxA := genDiss_hidxA
  hregc := genDiss_hregc
  hnc := genDiss_notComb

end Erdos634.Draft.LaczFormal.GenWit
