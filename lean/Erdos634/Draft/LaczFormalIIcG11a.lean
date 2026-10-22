-- Draft/LaczFormalIIcG11a.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.3 / Thm 2.1 (v), the printed inequality G11: PURE PLANE GEOMETRY, part a.
--  `rot_step`: vectors X, Y with positive cross product and unoriented angle theta satisfy cv Y * |X| = |Y| * e^{i theta} * cv X (the general form of `turn_step`).
--  `rho_tri`: a triangle A B E with E strictly left of A -> B, angle alpha at A and beta at B: cv (E - A) = (sin beta / sin (alpha+beta)) e^{i alpha} cv (B - A).
--  `rho_alg`: with rho the complex number of `rho_tri` and gamma = pi - alpha - beta:  rho - 1 = rho * (r e^{i gamma}), r = sin alpha / sin beta  (the log-spiral multiplier of the spoke fan).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3, (18)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcSymB

open Erdos634.Geometry EuclideanGeometry
open scoped RealInnerProductSpace

namespace Erdos634.Draft.LaczFormal.Thm21

set_option maxHeartbeats 3200000 in
theorem rot_step {X Y : Plane} {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < Real.pi) (hX : X ≠ 0) (hY : Y ≠ 0)
    (hcr : 0 < cross2 X Y) (hang : InnerProductGeometry.angle X Y = θ) :
    cv Y * ((‖X‖ : ℝ) : ℂ) = ((‖Y‖ : ℝ) : ℂ) * ⟨Real.cos θ, Real.sin θ⟩ * cv X := by
  have hu : ‖X‖ ≠ 0 := norm_ne_zero_iff.mpr hX
  have hw : ‖Y‖ ≠ 0 := norm_ne_zero_iff.mpr hY
  have hup : 0 < ‖X‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hu)
  have hwp : 0 < ‖Y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw)
  have hn : ‖X‖ ^ 2 = X 0 ^ 2 + X 1 ^ 2 := Erdos634.Geometry.norm_sq_coords _
  have hn' : ‖Y‖ ^ 2 = Y 0 ^ 2 + Y 1 ^ 2 := Erdos634.Geometry.norm_sq_coords _
  have hdot : X 0 * Y 0 + X 1 * Y 1 = ‖X‖ * ‖Y‖ * Real.cos θ := by
    have h := InnerProductGeometry.cos_angle X Y
    rw [hang, eq_div_iff (mul_ne_zero hu hw)] at h
    rw [Erdos634.Geometry.inner_coords] at h
    linarith
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθ
  have hcross : cross2 X Y = ‖X‖ * ‖Y‖ * Real.sin θ := by
    have hsq : cross2 X Y ^ 2 = (‖X‖ * ‖Y‖ * Real.sin θ) ^ 2 := by
      unfold cross2
      have : (X 0 * Y 1 - X 1 * Y 0) ^ 2 = ‖X‖ ^ 2 * ‖Y‖ ^ 2 - (X 0 * Y 0 + X 1 * Y 1) ^ 2 := by
        rw [hn, hn']; ring
      rw [this, hdot]
      linear_combination (-(‖X‖ ^ 2 * ‖Y‖ ^ 2)) * Real.sin_sq_add_cos_sq θ
    exact (pow_left_inj₀ hcr.le (by positivity) two_ne_zero).mp hsq
  apply Complex.ext
  · simp only [cv, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    apply mul_left_cancel₀ hu
    unfold cross2 at hcross
    linear_combination (Y 0) * hn + (X 0) * hdot - (X 1) * hcross
  · simp only [cv, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    apply mul_left_cancel₀ hu
    unfold cross2 at hcross
    linear_combination (Y 1) * hn + (X 0) * hcross + (X 1) * hdot

set_option maxHeartbeats 3200000 in
theorem rho_tri {A B E : Plane} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hαβ : α + β < Real.pi) (hAB : A ≠ B)
    (hcr : 0 < cross2 (B - A) (E - A)) (h1 : ∠ B A E = α) (h2 : ∠ A B E = β) :
    cv (E - A) = (((Real.sin β / Real.sin (α + β) : ℝ)) : ℂ) * ⟨Real.cos α, Real.sin α⟩ * cv (B - A) := by
  have hX : B - A ≠ 0 := sub_ne_zero.mpr hAB.symm
  have hEA : E ≠ A := by
    intro h
    rw [h] at hcr
    simp [cross2] at hcr
  have hY : E - A ≠ 0 := sub_ne_zero.mpr hEA
  have hα' : α < Real.pi := by linarith
  have hrot := rot_step hα hα' hX hY hcr (by simpa [EuclideanGeometry.angle] using h1)
  have hsαβ : 0 < Real.sin (α + β) := Real.sin_pos_of_pos_of_lt_pi (by linarith) hαβ
  -- law of sines
  have hls := EuclideanGeometry.law_sin B E A
  have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi (p₁ := A) (p₂ := B) E hAB.symm
  rw [h2, EuclideanGeometry.angle_comm E A B, h1] at hsum
  have hε : ∠ B E A = Real.pi - β - α := by linarith
  rw [hε, h2] at hls
  have hsε : Real.sin (Real.pi - β - α) = Real.sin (α + β) := by
    have : Real.pi - β - α = Real.pi - (α + β) := by ring
    rw [this, Real.sin_pi_sub]
  rw [hsε] at hls
  -- hls : sin (α+β) * dist E A = sin (∠ A B E) * dist A B   (after rewriting)
  have hnY : ‖E - A‖ = dist E A := (dist_eq_norm E A).symm
  have hnX : ‖B - A‖ = dist A B := by rw [dist_comm, dist_eq_norm]
  have hmag : ‖E - A‖ = Real.sin β / Real.sin (α + β) * ‖B - A‖ := by
    rw [hnY, hnX]
    have : Real.sin (α + β) * dist E A = Real.sin β * dist A B := hls
    field_simp
    linarith
  have hu : ‖B - A‖ ≠ 0 := norm_ne_zero_iff.mpr hX
  have huc : ((‖B - A‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu
  apply mul_right_cancel₀ huc
  rw [hrot, hmag]
  push_cast
  ring

end Erdos634.Draft.LaczFormal.Thm21
