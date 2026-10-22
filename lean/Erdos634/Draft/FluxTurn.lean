-- Draft/FluxTurn.lean — layer 2, part 1: edge-direction angles and the TURN LEMMA
-- (consecutive left-hand edge directions of a tile differ by `π − interior angle` in `ℝ/2πℤ`).
-- Imported into All.lean (All.lean:502; header corrected 2026-10-03); on the theoremP_6 closure (UNAUDITED).  Design: (private working notes, not included) §3.6 (`FluxTurn.lean`).
--
-- Formalization debt (the blocker of `lem:value`); not progress on the three /goal outcomes.
--
-- Reuse (cited): `Tri.det_cyclic`, `Tri.leftDir(_ne_zero)`, `Tri.det_ne_zero`, `cornerAngle(_sum)`,
-- `cross_sub_right` (EdgeChain); Mathlib `Complex.angle_eq_abs_arg`, `Complex.arg_div_coe_angle`,
-- `Complex.arg_neg_coe_angle`, `Complex.arg_real_mul`, `LinearIsometry.angle_map`,
-- `InnerProductGeometry.angle_neg_left`.
import Erdos634.Draft.FluxCore
import Mathlib.Analysis.Complex.Angle

open scoped Classical

namespace Erdos634.Geometry

/-- The plane read as `ℂ`: `v ↦ v₀ + v₁ i`. -/
noncomputable def toC : Plane ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm

theorem toC_apply (v : Plane) : toC v = (v 0 : ℂ) + (v 1 : ℂ) * Complex.I :=
  Complex.orthonormalBasisOneI_repr_symm_apply v

theorem toC_re (v : Plane) : (toC v).re = v 0 := by simp [toC_apply]

theorem toC_im (v : Plane) : (toC v).im = v 1 := by simp [toC_apply]

theorem toC_ne_zero {v : Plane} (hv : v ≠ 0) : toC v ≠ 0 := by
  intro h
  apply hv
  exact toC.injective (h.trans (map_zero toC).symm)

/-- `Im (v / u) = cross u v / |u|²`. -/
theorem toC_div_im (u v : Plane) :
    (toC v / toC u).im = cross u v / Complex.normSq (toC u) := by
  rw [Complex.div_im, toC_re, toC_re, toC_im, toC_im]
  unfold cross
  ring

/-- **The turn, in vectors.**  If `v` is to the left of `u` (`cross u v > 0`), then
`arg v = arg u + ∠(u, v)` in `ℝ/2πℤ`. -/
theorem arg_turn {u v : Plane} (hu : u ≠ 0) (hv : v ≠ 0) (hc : 0 < cross u v) :
    ((Complex.arg (toC v) : ℝ) : Real.Angle)
      = (Complex.arg (toC u) : Real.Angle)
        + ((InnerProductGeometry.angle u v : ℝ) : Real.Angle) := by
  have hu' := toC_ne_zero hu
  have hv' := toC_ne_zero hv
  have him : 0 ≤ (toC v / toC u).im := by
    rw [toC_div_im]
    exact div_nonneg hc.le (Complex.normSq_nonneg _)
  have h1 : InnerProductGeometry.angle (toC u) (toC v) = InnerProductGeometry.angle u v :=
    toC.toLinearIsometry.angle_map u v
  have hang : InnerProductGeometry.angle u v = Complex.arg (toC v / toC u) := by
    rw [← h1, InnerProductGeometry.angle_comm, Complex.angle_eq_abs_arg hv' hu',
      abs_of_nonneg (Complex.arg_nonneg_iff.mpr him)]
  rw [hang, Complex.arg_div_coe_angle hv' hu']
  abel

/-- The angle of a direction, in `ℝ/2πℤ`. -/
noncomputable def Dir.angle (d : Dir) : Real.Angle := (Complex.arg (toC d.1) : Real.Angle)

theorem Dir.ne_zero (d : Dir) : d.1 ≠ 0 := by
  intro h
  have h2 := d.2
  rw [h, norm_zero] at h2
  norm_num at h2

/-- Reversal adds `π`. -/
theorem Dir.angle_neg (d : Dir) :
    (Dir.neg d).angle = d.angle + ((Real.pi : ℝ) : Real.Angle) := by
  unfold Dir.angle
  have h : toC (Dir.neg d).1 = - toC d.1 := map_neg toC d.1
  rw [h, Complex.arg_neg_coe_angle (toC_ne_zero d.ne_zero)]

/-- The angle of a left-hand unit is the argument of the unnormalised left-hand direction. -/
theorem Tri.leftUnit_angle (T : Tri) (k : Fin 3) :
    (T.leftUnit k).angle = (Complex.arg (toC (T.leftDir k)) : Real.Angle) := by
  unfold Dir.angle
  show ((Complex.arg (toC (‖T.leftDir k‖⁻¹ • T.leftDir k)) : ℝ) : Real.Angle) = _
  rw [map_smul, Complex.real_smul,
    Complex.arg_real_mul _ (inv_pos.mpr (norm_pos_iff.mpr (T.leftDir_ne_zero k)))]

/-- The interior angle of `T` at vertex `k`. -/
noncomputable def Tri.angleAt (T : Tri) (k : Fin 3) : ℝ :=
  cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2))

/-- The side opposite vertex `k`. -/
noncomputable def Tri.oppLen (T : Tri) (k : Fin 3) : ℝ := dist (T.pts (k + 1)) (T.pts (k + 2))

theorem Tri.angleAt_sum (T : Tri) : T.angleAt 0 + T.angleAt 1 + T.angleAt 2 = Real.pi := by
  have h := cornerAngle_sum T
  unfold Tri.angleAt
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl,
    show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl,
    show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
  exact h

/-- The exterior angle at vertex `k+1` is the unoriented angle between the two edge vectors
`u = pts (k+1) − pts k` and `v = pts (k+2) − pts (k+1)`. -/
theorem Tri.pi_sub_angleAt (T : Tri) (k : Fin 3) :
    Real.pi - T.angleAt (k + 1)
      = InnerProductGeometry.angle (T.pts (k + 1) - T.pts k) (T.pts (k + 2) - T.pts (k + 1)) := by
  have h1 : k + 1 + 1 = k + 2 := by fin_cases k <;> rfl
  have h2 : k + 1 + 2 = k := by fin_cases k <;> rfl
  unfold Tri.angleAt cornerAngle EuclideanGeometry.angle
  rw [h1, h2]
  simp only [vsub_eq_sub]
  rw [InnerProductGeometry.angle_comm,
    show T.pts k - T.pts (k + 1) = -(T.pts (k + 1) - T.pts k) by abel,
    InnerProductGeometry.angle_neg_left]
  ring

/-- `cross (pts (k+1) − pts k) (pts (k+2) − pts (k+1)) = det`. -/
theorem Tri.cross_consecutive (T : Tri) (k : Fin 3) :
    cross (T.pts (k + 1) - T.pts k) (T.pts (k + 2) - T.pts (k + 1)) = T.det := by
  have h := T.det_cyclic k
  have e : T.pts (k + 2) - T.pts (k + 1) = (T.pts (k + 2) - T.pts k) - (T.pts (k + 1) - T.pts k) := by
    abel
  rw [e, cross_sub_right, h, cross_self, sub_zero]

/-- **The turn lemma, ccw tile.**  Leaving vertex `k+1` the left-hand direction turns left by the
exterior angle `π − (angle at k+1)`. -/
theorem Tri.leftUnit_turn_of_pos (T : Tri) (hT : 0 < T.det) (k : Fin 3) :
    (T.leftUnit (k + 1)).angle
      = (T.leftUnit k).angle + ((Real.pi - T.angleAt (k + 1) : ℝ) : Real.Angle) := by
  have h1 : k + 1 + 1 = k + 2 := by fin_cases k <;> rfl
  have hk : T.leftDir k = T.pts (k + 1) - T.pts k := by unfold Tri.leftDir; rw [if_pos hT]
  have hk1 : T.leftDir (k + 1) = T.pts (k + 2) - T.pts (k + 1) := by
    unfold Tri.leftDir; rw [if_pos hT, h1]
  rw [Tri.leftUnit_angle, Tri.leftUnit_angle, T.pi_sub_angleAt k, hk, hk1]
  refine arg_turn ?_ ?_ ?_
  · rw [← hk]; exact T.leftDir_ne_zero k
  · rw [← hk1]; exact T.leftDir_ne_zero (k + 1)
  · rw [T.cross_consecutive k]; exact hT

/-- **The turn lemma, cw tile.**  The ccw traversal runs `k+1 → k`, so the roles swap. -/
theorem Tri.leftUnit_turn_of_neg (T : Tri) (hT : T.det < 0) (k : Fin 3) :
    (T.leftUnit k).angle
      = (T.leftUnit (k + 1)).angle + ((Real.pi - T.angleAt (k + 1) : ℝ) : Real.Angle) := by
  have h1 : k + 1 + 1 = k + 2 := by fin_cases k <;> rfl
  have hn : ¬ 0 < T.det := not_lt.mpr hT.le
  have hk : T.leftDir k = -(T.pts (k + 1) - T.pts k) := by
    unfold Tri.leftDir; rw [if_neg hn]; abel
  have hk1 : T.leftDir (k + 1) = -(T.pts (k + 2) - T.pts (k + 1)) := by
    unfold Tri.leftDir; rw [if_neg hn, h1]; abel
  have hang : InnerProductGeometry.angle (T.pts (k + 1) - T.pts k) (T.pts (k + 2) - T.pts (k + 1))
      = InnerProductGeometry.angle (-(T.pts (k + 2) - T.pts (k + 1))) (-(T.pts (k + 1) - T.pts k)) := by
    rw [InnerProductGeometry.angle_neg_neg, InnerProductGeometry.angle_comm]
  rw [Tri.leftUnit_angle, Tri.leftUnit_angle, T.pi_sub_angleAt k, hk, hk1, hang]
  refine arg_turn ?_ ?_ ?_
  · rw [← hk1]; exact T.leftDir_ne_zero (k + 1)
  · rw [← hk]; exact T.leftDir_ne_zero k
  · have hc := T.cross_consecutive k
    simp only [cross, PiLp.neg_apply] at hc ⊢
    linarith

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Tri.leftUnit_turn_of_pos
#print axioms Erdos634.Geometry.Tri.leftUnit_turn_of_neg
#print axioms Erdos634.Geometry.Dir.angle_neg
