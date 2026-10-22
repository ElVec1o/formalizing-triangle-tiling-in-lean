-- Draft/FluxGRow3RP.lean — row 3 (AUDIT_ROWS), Proposition RP for GENERAL N, on a real
-- CongruentDissection. Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- Formalization debt on an already paper-level-PROVED result (row3 PROOF.md, Prop RP; two hostile
-- reviews HOLD). Not /goal progress; no target of (private working notes, not included) moves.
--
-- `row3_RP_even`: a real `CongruentDissection N` whose model is a right tile in normal form
-- (angle `α` at vertex 0, `π/2` at vertex 2, `α/π ∉ ℚ`, `0 < α < π/2`) and whose target has angles
-- `α, α` at vertices 0, 1 and is positively oriented, has `N` even. Any scale of tile, any
-- position/orientation of the tiles, any placement of the target (only its vertex labelling and
-- orientation are normalised; `det > 0` with apex at vertex 2 is always reachable by relabelling).
--
-- Assembly: Step 1 (area, `abs_det_eq` + `CongruentArea`), Step 3 (`gaussWeight_flux_cancel`, general
-- `Dissection`), Step 4 (`FluxGRow3Relabel.rightTile_flux_value`, rescaled here; off-grid tiles give
-- 0), Step 5 (`target_flux_general`: the boundary value for an arbitrary placed target, from its
-- angles and side lengths, no coordinates), Step 6 (`Step6.step6_quadratic`: coefficientwise
-- division by c·z⁻¹(z − e^{iα})), Step 7 (`Row3.step7_even`).
import Erdos634.Draft.FluxGRow3Relabel
import Erdos634.AreaDet
import Erdos634.CongruentArea
import Erdos634.TriLawSin
import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle

open scoped Classical

namespace Erdos634.Geometry.Row3.RP

open Real Erdos634.Geometry Erdos634.Geometry.Row3

/-! ## Triangle facts: area, right-triangle sides, isosceles sides -/

theorem oppLen_pos (T : Tri) (k : Fin 3) : 0 < T.oppLen k := by
  unfold Tri.oppLen
  apply dist_pos.mpr
  intro h
  have := T.indep.injective h
  revert this; fin_cases k <;> decide

/-- `|det| = (side opp 1)(side opp 2) sin(angle at 0)`. -/
theorem abs_det_eq (T : Tri) :
    |T.det| = T.oppLen 1 * T.oppLen 2 * Real.sin (T.angleAt 0) := by
  have hang : T.angleAt 0
      = InnerProductGeometry.angle (T.pts 1 - T.pts 0) (T.pts 2 - T.pts 0) := rfl
  have h1 : T.oppLen 1 = ‖T.pts 2 - T.pts 0‖ := by
    show dist (T.pts 2) (T.pts 0) = _; rw [dist_eq_norm]
  have h2 : T.oppLen 2 = ‖T.pts 1 - T.pts 0‖ := by
    show dist (T.pts 0) (T.pts 1) = _; rw [dist_comm, dist_eq_norm]
  have hsin := InnerProductGeometry.sin_angle_mul_norm_mul_norm (T.pts 1 - T.pts 0)
    (T.pts 2 - T.pts 0)
  have hid : inner ℝ (T.pts 1 - T.pts 0) (T.pts 1 - T.pts 0)
        * inner ℝ (T.pts 2 - T.pts 0) (T.pts 2 - T.pts 0)
      - inner ℝ (T.pts 1 - T.pts 0) (T.pts 2 - T.pts 0)
        * inner ℝ (T.pts 1 - T.pts 0) (T.pts 2 - T.pts 0) = T.det ^ 2 := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two]
    unfold Tri.det; ring
  rw [← Real.sqrt_sq_eq_abs, ← hid, ← hsin, hang, h1, h2]
  ring

/-- Right angle at vertex 2: the legs are `c cos(angle 0)` and `c sin(angle 0)`, `c = oppLen 2`. -/
theorem right_sides (T : Tri) (h2 : T.angleAt 2 = Real.pi / 2) :
    T.oppLen 1 = T.oppLen 2 * Real.cos (T.angleAt 0)
      ∧ T.oppLen 0 = T.oppLen 2 * Real.sin (T.angleAt 0) := by
  have h : EuclideanGeometry.angle (T.pts 1) (T.pts 2) (T.pts 0) = Real.pi / 2 := by
    rw [EuclideanGeometry.angle_comm]; exact h2
  have hc := EuclideanGeometry.cos_angle_mul_dist_of_angle_eq_pi_div_two h
  have hs := EuclideanGeometry.sin_angle_mul_dist_of_angle_eq_pi_div_two h
  have ha : T.angleAt 0 = EuclideanGeometry.angle (T.pts 2) (T.pts 0) (T.pts 1) := by
    show EuclideanGeometry.angle (T.pts 1) (T.pts 0) (T.pts 2) = _
    exact EuclideanGeometry.angle_comm _ _ _
  have e2 : T.oppLen 2 = dist (T.pts 1) (T.pts 0) := by
    show dist (T.pts 0) (T.pts 1) = _; exact dist_comm _ _
  have e1 : T.oppLen 1 = dist (T.pts 0) (T.pts 2) := by
    show dist (T.pts 2) (T.pts 0) = _; exact dist_comm _ _
  have e0 : T.oppLen 0 = dist (T.pts 1) (T.pts 2) := rfl
  rw [ha, e2, e1, e0]
  exact ⟨by rw [← hc]; ring, by rw [← hs]; ring⟩

/-- Base angles `α, α` at vertices 0, 1: legs equal, base `= 2·leg·cos α`. -/
theorem iso_sides (T : Tri) {α : ℝ} (hα : 0 < α) (hα2 : α < Real.pi / 2)
    (h0 : T.angleAt 0 = α) (h1 : T.angleAt 1 = α) :
    T.oppLen 0 = T.oppLen 1 ∧ T.oppLen 2 = 2 * T.oppLen 1 * Real.cos α := by
  have hsum := T.angleAt_sum
  have h2 : T.angleAt 2 = Real.pi - 2 * α := by linarith
  have l0 : Real.sin (T.angleAt 1) * T.oppLen 0 = Real.sin (T.angleAt 0) * T.oppLen 1 :=
    Erdos634.TriLawSin.sin_angleAt_mul_sideOpp T 0
  have l2 : Real.sin (T.angleAt 0) * T.oppLen 2 = Real.sin (T.angleAt 2) * T.oppLen 0 :=
    Erdos634.TriLawSin.sin_angleAt_mul_sideOpp T 2
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα (by linarith [Real.pi_pos])
  rw [h0, h1] at l0
  have e0 : T.oppLen 0 = T.oppLen 1 := mul_left_cancel₀ hs.ne' l0
  refine ⟨e0, ?_⟩
  rw [h0, h2, Real.sin_pi_sub, Real.sin_two_mul, e0] at l2
  have : Real.sin α * (T.oppLen 2 - 2 * T.oppLen 1 * Real.cos α) = 0 := by linarith
  have := (mul_eq_zero.mp this).resolve_left hs.ne'
  linarith

/-- **Step 1, general**: `|det target| = N · |det model|`. -/
theorem abs_det_target {N : ℕ} (D : CongruentDissection N) :
    |D.target.det| = N * |D.model.det| := by
  have hdt : ∀ T : Tri, Erdos634.AreaDet.detTri T = T.det := fun T => by
    rw [Erdos634.AreaDet.detTri_eq]; unfold Tri.det; ring
  have hv := Erdos634.CongruentArea.congruentDissection_volume_target D
  rw [Erdos634.AreaDet.volume_eq_det_mul, Erdos634.AreaDet.volume_eq_det_mul, hdt, hdt] at hv
  set S := MeasureTheory.volume Erdos634.AreaDet.stdCarrier
  have hB : ENNReal.ofReal |D.model.det| ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact abs_pos.mpr D.model.det_ne_zero
  have hS0 : S ≠ 0 := by
    have hp := D.model.volume_pos
    rw [Erdos634.AreaDet.volume_eq_det_mul, hdt] at hp
    change 0 < ENNReal.ofReal |D.model.det| * S at hp
    intro h; rw [h, mul_zero] at hp; exact lt_irrefl _ hp
  have hST : S ≠ ⊤ := by
    have hf := D.model.volume_ne_top
    rw [Erdos634.AreaDet.volume_eq_det_mul, hdt] at hf
    change ENNReal.ofReal |D.model.det| * S ≠ ⊤ at hf
    intro h; apply hf; rw [h]; exact ENNReal.mul_top hB
  have hpos : 0 < S.toReal := ENNReal.toReal_pos hS0 hST
  have hr := congrArg ENNReal.toReal hv
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_natCast] at hr
  have : (|D.target.det| - N * |D.model.det|) * S.toReal = 0 := by linear_combination hr
  have := (mul_eq_zero.mp this).resolve_right hpos.ne'
  linarith

/-! ## Step 4, rescaled: one tile of hypotenuse `c` -/

theorem rightTile_flux_value_c {α θ₀ c : ℝ} (hα : Irrational (α / Real.pi)) (T : Tri)
    (hβ : T.angleAt 1 = Real.pi / 2 - α) (hγ : T.angleAt 2 = Real.pi / 2)
    (ha : T.oppLen 0 = c * Real.sin α) (hb : T.oppLen 1 = c * Real.cos α) (hc : T.oppLen 2 = c)
    (X : ℤ) :
    T.flux (gaussWeight α θ₀ X)
      = (c : ℂ) * Step6.tileVal α (IsGridA α θ₀ (T.leftUnit 0).angle) (T.det < 0)
          (gridK α θ₀ (T.leftUnit 0).angle) (gridJ α θ₀ (T.leftUnit 0).angle) X := by
  unfold Step6.tileVal
  by_cases hg : IsGridA α θ₀ (T.leftUnit 0).angle
  · rw [if_pos hg]
    rcases lt_or_gt_of_ne T.det_ne_zero with hneg | hpos
    · rw [if_pos hneg, Tri.flux_gauss_reflected T hα hneg hβ hγ hg X, ha, hb, hc]
      unfold Step6.vv; push_cast; split_ifs <;> ring
    · rw [if_neg (by linarith), Tri.flux_gauss_direct T hα hpos hβ hγ hg X, ha, hb, hc]
      unfold Step6.uu; push_cast; split_ifs <;> ring
  · rw [if_neg hg, mul_zero]
    obtain ⟨g1, g2⟩ := legs_offGrid T hβ hγ hg
    unfold Tri.flux
    rw [Fin.sum_univ_three, gaussWeight_offGrid X _ hg, gaussWeight_offGrid X _ g1,
      gaussWeight_offGrid X _ g2]
    simp

/-! ## Step 5, general placement: the target's value from its angles and sides alone -/

theorem target_flux_general {α c lam : ℝ} (hα : Irrational (α / Real.pi)) (T : Tri)
    (hdet : 0 < T.det) (h1 : T.angleAt 1 = α) (h2 : T.angleAt 2 = Real.pi - 2 * α)
    (hs0 : T.oppLen 0 = lam * c) (hs1 : T.oppLen 1 = lam * c)
    (hs2 : T.oppLen 2 = 2 * lam * c * Real.cos α) (X : ℤ) :
    T.flux (gaussWeight α (T.leftUnit 0).angle.toReal X) = (c : ℂ) * Step6.bdryVal α lam X := by
  set θ₀ := (T.leftUnit 0).angle.toReal with hθ₀
  have hspec : (T.leftUnit 0).angle
      = ((θ₀ + ((0 : ℤ) : ℝ) * α + ((0 : ℤ) : ℝ) * (Real.pi / 2) : ℝ) : Real.Angle) := by
    rw [show θ₀ + ((0 : ℤ) : ℝ) * α + ((0 : ℤ) : ℝ) * (Real.pi / 2) = θ₀ by push_cast; ring,
      hθ₀, Real.Angle.coe_toReal]
  have hg0 : IsGridA α θ₀ (T.leftUnit 0).angle := ⟨0, 0, hspec⟩
  have hk0 : gridK α θ₀ (T.leftUnit 0).angle = 0 := gridK_eq_of_spec hα hspec
  have hj0 : (Complex.I : ℂ) ^ gridJ α θ₀ (T.leftUnit 0).angle = 1 := by
    rw [Erdos634.Geometry.Row3.Complex.I_zpow_eq_of_mod4 (gridJ_eq_of_spec hα hspec)]; simp
  have hw0 : ∀ Y, gaussWeightA α θ₀ Y (T.leftUnit 0).angle = if (0 : ℤ) = Y then 1 else 0 := by
    intro Y; unfold gaussWeightA; rw [dif_pos hg0, hk0, hj0]
  have hI2 : (Complex.I : ℂ) ^ (2 : ℤ) = -1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, Complex.I_sq]
  have t0 := T.leftUnit_turn_of_pos hdet 0
  have t1 := T.leftUnit_turn_of_pos hdet 1
  simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (1 : Fin 3) + 1 = 2 from rfl] at t0 t1
  have t0' : (T.leftUnit 1).angle = (T.leftUnit 0).angle
      + ((((-1 : ℤ) : ℝ) * α + ((2 : ℤ) : ℝ) * (Real.pi / 2) : ℝ) : Real.Angle) := by
    rw [t0, h1]; congr 2; push_cast; ring
  have t1' : (T.leftUnit 2).angle = (T.leftUnit 0).angle
      + ((((1 : ℤ) : ℝ) * α + ((2 : ℤ) : ℝ) * (Real.pi / 2) : ℝ) : Real.Angle) := by
    rw [t1, h2, t0, h1, add_assoc, ← Real.Angle.coe_add]; congr 2; push_cast; ring
  have hw1 : gaussWeight α θ₀ X (T.leftUnit 1) = -(if (0 : ℤ) = X + 1 then 1 else 0) := by
    unfold gaussWeight
    rw [t0', gaussWeightA_shift hα hg0 (-1) 2 X, hw0, hI2, show X - -1 = X + 1 by ring]; ring
  have hw2 : gaussWeight α θ₀ X (T.leftUnit 2) = -(if (0 : ℤ) = X - 1 then 1 else 0) := by
    unfold gaussWeight
    rw [t1', gaussWeightA_shift hα hg0 1 2 X, hw0, hI2]; ring
  have hw0' : gaussWeight α θ₀ X (T.leftUnit 0) = if (0 : ℤ) = X then 1 else 0 := hw0 X
  unfold Tri.flux
  rw [Fin.sum_univ_three]
  show dist (T.pts 0) (T.pts 1) • gaussWeight α θ₀ X (T.leftUnit 0)
      + dist (T.pts 1) (T.pts 2) • gaussWeight α θ₀ X (T.leftUnit 1)
      + dist (T.pts 2) (T.pts 0) • gaussWeight α θ₀ X (T.leftUnit 2) = _
  have d2 : dist (T.pts 0) (T.pts 1) = T.oppLen 2 := rfl
  have d0 : dist (T.pts 1) (T.pts 2) = T.oppLen 0 := rfl
  have d1 : dist (T.pts 2) (T.pts 0) = T.oppLen 1 := rfl
  rw [d2, d0, d1, hs0, hs1, hs2, hw0', hw1, hw2, Complex.real_smul, Complex.real_smul,
    Complex.real_smul]
  unfold Step6.bdryVal
  split_ifs <;> first | omega | (push_cast; ring)

/-! ## Proposition RP, general `N` -/

/-- **Proposition RP (row 3), general N, on a real `CongruentDissection`.** -/
theorem row3_RP_even {N : ℕ} (D : CongruentDissection N) {α : ℝ} (hα0 : 0 < α)
    (hα2 : α < Real.pi / 2) (hirr : Irrational (α / Real.pi))
    (hm0 : D.model.angleAt 0 = α) (hm2 : D.model.angleAt 2 = Real.pi / 2)
    (ht0 : D.target.angleAt 0 = α) (ht1 : D.target.angleAt 1 = α) (htdet : 0 < D.target.det) :
    Even N := by
  -- the model
  set c := D.model.oppLen 2 with hc
  have hc0 : 0 < c := oppLen_pos _ _
  have hm1 : D.model.angleAt 1 = Real.pi / 2 - α := by
    have := D.model.angleAt_sum; linarith
  obtain ⟨hmb, hma⟩ := right_sides D.model hm2
  rw [hm0] at hmb hma
  -- the target
  obtain ⟨te0, te2⟩ := iso_sides D.target hα0 hα2 ht0 ht1
  have ht2 : D.target.angleAt 2 = Real.pi - 2 * α := by
    have := D.target.angleAt_sum; linarith
  set L := D.target.oppLen 1 with hL
  set lam := L / c with hlam
  have hLc : L = lam * c := by rw [hlam]; field_simp
  -- Step 1
  have hN : (N : ℝ) = 2 * lam ^ 2 := by
    have h := abs_det_target D
    rw [abs_det_eq, abs_det_eq, ht0, hm0, te2, hmb, ← hL, ← hc] at h
    have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith [Real.pi_pos])
    have hco : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, hα2⟩
    have hk : (2 * lam ^ 2 - N) * (c ^ 2 * Real.cos α * Real.sin α) = 0 := by
      rw [hLc] at h; linear_combination h
    have := (mul_eq_zero.mp hk).resolve_right (by positivity)
    linarith
  -- normal forms of the tiles
  choose τ hτ using fun i => Tri.Congruent.exists_normal (D.tiles_congruent i)
  set T' : Fin N → Tri := fun i => (D.tile i).relabel (τ i) with hT'
  set θ₀ := (D.target.leftUnit 0).angle.toReal with hθ₀
  have hsum : ∀ X, ∑ i, Step6.tileVal α (IsGridA α θ₀ ((T' i).leftUnit 0).angle)
      ((T' i).det < 0) (gridK α θ₀ ((T' i).leftUnit 0).angle)
      (gridJ α θ₀ ((T' i).leftUnit 0).angle) X = Step6.bdryVal α lam X := by
    intro X
    have hcancel := gaussWeight_flux_cancel (θ₀ := θ₀) hirr X D.toDissection
    have htgt : D.toDissection.target.flux (gaussWeight α θ₀ X) = (c : ℂ) * Step6.bdryVal α lam X :=
      target_flux_general hirr D.target htdet ht1 ht2 (by rw [te0, hLc]) hLc
        (by rw [te2, hLc]; ring) X
    have htile : ∀ i, (D.toDissection.tile i).flux (gaussWeight α θ₀ X)
        = (c : ℂ) * Step6.tileVal α (IsGridA α θ₀ ((T' i).leftUnit 0).angle)
          ((T' i).det < 0) (gridK α θ₀ ((T' i).leftUnit 0).angle)
          (gridJ α θ₀ ((T' i).leftUnit 0).angle) X := by
      intro i
      show (D.tile i).flux _ = _
      rw [← Tri.flux_relabel (D.tile i) (τ i)]
      exact rightTile_flux_value_c hirr (T' i) ((hτ i 1).1.trans hm1) ((hτ i 2).1.trans hm2)
        ((hτ i 0).2.trans hma) ((hτ i 1).2.trans hmb) ((hτ i 2).2) X
    rw [Finset.sum_congr rfl (fun i _ => htile i), ← Finset.mul_sum, htgt] at hcancel
    exact mul_left_cancel₀ (by exact_mod_cast hc0.ne') hcancel
  exact Step6.step6_even N α lam _ _ _ _ hN hsum

end Erdos634.Geometry.Row3.RP

#print axioms Erdos634.Geometry.Row3.RP.abs_det_eq
#print axioms Erdos634.Geometry.Row3.RP.abs_det_target
#print axioms Erdos634.Geometry.Row3.RP.target_flux_general
#print axioms Erdos634.Geometry.Row3.RP.row3_RP_even
