-- Draft/LaczFormalFluxPolyPhi2.lean -- coordinates of the side directions of a convex polygon: unit vectors u_j = (c_j, s_j), the rotation rule
-- u_{j+1} = rot(pi - angle_{j+1}) u_j, and closure  sum_j d_j u_j = 0  (d_j = side length).  Used for Lemma 7.2 (Laczkovich DCG 48 (2012)).
-- NOTE / UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 7.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalFluxPolyPhi

open scoped Classical
open Erdos634.Geometry

namespace Erdos634.Draft.LaczFormal.Thm21

variable {M : ℕ} [NeZero M]

theorem Dir.cos_angle (d : Dir) : Real.Angle.cos d.angle = d.1 0 := by
  unfold Dir.angle
  rw [Real.Angle.cos_coe, Complex.cos_arg (toC_ne_zero d.ne_zero)]
  have h1 : ‖toC d.1‖ = 1 := by rw [LinearIsometryEquiv.norm_map]; exact d.2
  rw [h1, div_one, toC_re]

theorem Dir.sin_angle (d : Dir) : Real.Angle.sin d.angle = d.1 1 := by
  unfold Dir.angle
  rw [Real.Angle.sin_coe, Complex.sin_arg]
  have h1 : ‖toC d.1‖ = 1 := by rw [LinearIsometryEquiv.norm_map]; exact d.2
  rw [h1, div_one, toC_im]

namespace ConvPoly
variable (P : ConvPoly M)

/-- x-coordinate of the unit direction of side `j`. -/
noncomputable def cx (j : Fin M) : ℝ := (P.sideDir j).1 0
/-- y-coordinate of the unit direction of side `j`. -/
noncomputable def sy (j : Fin M) : ℝ := (P.sideDir j).1 1

theorem unit_sq (j : Fin M) : P.cx j ^ 2 + P.sy j ^ 2 = 1 := by
  have h := (P.sideDir j).2
  have h2 : ‖(P.sideDir j).1‖ ^ 2 = 1 := by rw [h]; norm_num
  rw [norm_sq_plane] at h2
  exact h2

theorem rot_cos (j : Fin M) :
    P.cx (j + 1) = P.cx j * Real.cos (Real.pi - P.angle (j + 1)) - P.sy j * Real.sin (Real.pi - P.angle (j + 1)) := by
  have h := congrArg Real.Angle.cos (P.sideDir_turn j)
  rw [Real.Angle.cos_add, Real.Angle.cos_coe, Real.Angle.sin_coe, Dir.cos_angle, Dir.sin_angle, Dir.cos_angle] at h
  exact h

theorem rot_sin (j : Fin M) :
    P.sy (j + 1) = P.sy j * Real.cos (Real.pi - P.angle (j + 1)) + P.cx j * Real.sin (Real.pi - P.angle (j + 1)) := by
  have h := congrArg Real.Angle.sin (P.sideDir_turn j)
  rw [Real.Angle.sin_add, Real.Angle.cos_coe, Real.Angle.sin_coe, Dir.cos_angle, Dir.sin_angle, Dir.sin_angle] at h
  exact h

theorem e_eq (j : Fin M) (i : Fin 2) : P.e j i = P.side j * (P.sideDir j).1 i := by
  have hne := P.e_ne_zero P.three_le j
  have hs : P.side j = ‖P.e j‖ := by
    unfold side e
    rw [dist_comm, dist_eq_norm]
  have : P.e j = ‖P.e j‖ • (P.sideDir j).1 := by
    show P.e j = ‖P.e j‖ • (‖P.e j‖⁻¹ • P.e j)
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hne), one_smul]
  rw [hs]
  conv_lhs => rw [this]
  simp

theorem sum_e (i : Fin 2) : ∑ j : Fin M, P.e j i = 0 := by
  unfold e
  simp only [PiLp.sub_apply]
  rw [Finset.sum_sub_distrib]
  have := Equiv.sum_comp (Equiv.addRight (1 : Fin M)) (fun j => P.v j i)
  simp only [Equiv.coe_addRight] at this
  rw [this]; ring

/-- **Closure of the polygon**: `sum_j d_j c_j = 0` and `sum_j d_j s_j = 0`. -/
theorem closure_x : ∑ j : Fin M, P.side j * P.cx j = 0 := by
  have := P.sum_e 0
  simpa [P.e_eq, cx] using this

theorem closure_y : ∑ j : Fin M, P.side j * P.sy j = 0 := by
  have := P.sum_e 1
  simpa [P.e_eq, sy] using this

end ConvPoly

end Erdos634.Draft.LaczFormal.Thm21
