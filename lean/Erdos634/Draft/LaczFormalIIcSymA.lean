-- Draft/LaczFormalIIcSymA.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3, two-exceptional-point case, central symmetry: PURE PLANE GEOMETRY ingredients (no tiling).
--  `sine_ratio_step`: two consecutive triangles A B E, B C E with angles alpha at the first base vertex and beta at the second give |BC| sin beta = sin alpha |AB| (law of sines twice; this is (18), `q = sin alpha / sin beta`).
--  `turn_step`: at a corner of unoriented angle pi - gamma with a left turn, the next side vector is (|next|/|prev|) * e^{i gamma} * (previous side vector), in complex coordinates (the exterior angle is gamma).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3, (18) and the central symmetry argument), Beeson, Beeson-Zhang.
import Mathlib
import Erdos634.Draft.LaczFormalThm21Area

open Erdos634.Geometry EuclideanGeometry
open scoped RealInnerProductSpace

namespace Erdos634.Draft.LaczFormal.Thm21

/-- Plane vectors as complex numbers. -/
noncomputable def cv (x : Plane) : ℂ := ⟨x 0, x 1⟩

theorem sine_ratio_step {A B C E : Plane} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hαβ : α + β < Real.pi) (hAB : A ≠ B) (hBC : B ≠ C)
    (h1 : ∠ B A E = α) (h2 : ∠ A B E = β) (h3 : ∠ C B E = α) (h4 : ∠ B C E = β) :
    dist B C * Real.sin β = Real.sin α * dist A B := by
  have sα : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα (by linarith)
  have hpi := Real.pi_pos
  have a1 := EuclideanGeometry.law_sin A B E
  have b1 := EuclideanGeometry.law_sin E A B
  have a2 := EuclideanGeometry.law_sin B C E
  have b2 := EuclideanGeometry.law_sin E B C
  have s1 := EuclideanGeometry.angle_add_angle_add_angle_eq_pi (p₁ := A) (p₂ := B) E hAB.symm
  have s2 := EuclideanGeometry.angle_add_angle_add_angle_eq_pi (p₁ := B) (p₂ := C) E hBC.symm
  rw [EuclideanGeometry.angle_comm E A B, h1] at b1
  rw [EuclideanGeometry.angle_comm E A B, h1] at a1
  rw [h2] at a1
  rw [EuclideanGeometry.angle_comm E B C, h3] at b2 a2
  rw [h4] at a2
  have e1 : ∠ B E A = Real.pi - β - α := by
    have := s1; rw [h2, EuclideanGeometry.angle_comm E A B, h1] at this; linarith
  have e2 : ∠ C E B = Real.pi - β - α := by
    have := s2; rw [h4, EuclideanGeometry.angle_comm E B C, h3] at this; linarith
  rw [e1] at b1
  rw [e2] at b2
  rw [dist_comm E A] at a1
  rw [dist_comm E B] at a2
  apply mul_left_cancel₀ sα.ne'
  linear_combination (Real.sin β) * b2 + (Real.sin (Real.pi - β - α)) * a2 - (Real.sin α) * b1

theorem turn_step {A B C : Plane} {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < Real.pi) (hAB : A ≠ B) (hBC : B ≠ C)
    (hcr : 0 < cross2 (B - A) (C - B)) (hang : ∠ A B C = Real.pi - γ) :
    cv (C - B) * ((‖B - A‖ : ℝ) : ℂ) = ((‖C - B‖ : ℝ) : ℂ) * ⟨Real.cos γ, Real.sin γ⟩ * cv (B - A) := by
  have hu : ‖B - A‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hAB.symm)
  have hw : ‖C - B‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hBC.symm)
  have hup : 0 < ‖B - A‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hu)
  have hwp : 0 < ‖C - B‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw)
  have hn : ‖B - A‖ ^ 2 = (B - A) 0 ^ 2 + (B - A) 1 ^ 2 := Erdos634.Geometry.norm_sq_coords _
  have hn' : ‖C - B‖ ^ 2 = (C - B) 0 ^ 2 + (C - B) 1 ^ 2 := Erdos634.Geometry.norm_sq_coords _
  have hdot : (B - A) 0 * (C - B) 0 + (B - A) 1 * (C - B) 1 = ‖B - A‖ * ‖C - B‖ * Real.cos γ := by
    have h := InnerProductGeometry.cos_angle (A - B) (C - B)
    have hang' : InnerProductGeometry.angle (A - B) (C - B) = Real.pi - γ := hang
    rw [hang', Real.cos_pi_sub, norm_sub_rev A B, eq_div_iff (mul_ne_zero hu hw)] at h
    rw [Erdos634.Geometry.inner_coords] at h
    simp only [PiLp.sub_apply] at h ⊢
    linarith
  have hsin : 0 < Real.sin γ := Real.sin_pos_of_pos_of_lt_pi hγ0 hγ
  have hcross : cross2 (B - A) (C - B) = ‖B - A‖ * ‖C - B‖ * Real.sin γ := by
    have hsq : cross2 (B - A) (C - B) ^ 2 = (‖B - A‖ * ‖C - B‖ * Real.sin γ) ^ 2 := by
      have hs2 : Real.sin γ ^ 2 = 1 - Real.cos γ ^ 2 := by nlinarith [Real.sin_sq_add_cos_sq γ]
      unfold cross2
      have : ((B - A) 0 * (C - B) 1 - (B - A) 1 * (C - B) 0) ^ 2 = ‖B - A‖ ^ 2 * ‖C - B‖ ^ 2 - ((B - A) 0 * (C - B) 0 + (B - A) 1 * (C - B) 1) ^ 2 := by
        rw [hn, hn']; ring
      rw [this, hdot]
      linear_combination (-(‖B - A‖ ^ 2 * ‖C - B‖ ^ 2)) * Real.sin_sq_add_cos_sq γ
    exact (pow_left_inj₀ hcr.le (by positivity) two_ne_zero).mp hsq
  apply Complex.ext
  · simp only [cv, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    apply mul_left_cancel₀ hu
    unfold cross2 at hcross
    linear_combination ((C - B) 0) * hn + ((B - A) 0) * hdot - ((B - A) 1) * hcross
  · simp only [cv, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    apply mul_left_cancel₀ hu
    unfold cross2 at hcross
    linear_combination ((C - B) 1) * hn + ((B - A) 0) * hcross + ((B - A) 1) * hdot

end Erdos634.Draft.LaczFormal.Thm21
