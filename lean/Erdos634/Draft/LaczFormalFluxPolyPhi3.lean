-- Draft/LaczFormalFluxPolyPhi3.lean -- Laczkovich DCG 48 (2012), Lemma 7.2 (Sect. 7.3): the values of the functional Phi (G = <pi/3, alpha>, chi((n pi/3) + m alpha) = (-1)^n)
-- on the polygon A of Case IIIc, for N = 3, 4, 5, 6 sides, together with the side relations they use.
--   (0-indexed sides d_j = |v_j v_{j+1}|; Laczkovich's d_i = my side (i-1).)  G is anchored at the direction of side 0 (the side on the x-axis).
--   N = 3 (all angles pi/3):                    Phi = d_0 + d_1 + d_2 = 3 d_0, d_0 = d_1 = d_2;
--   N = 4 (angles pi/3, 2pi/3, 2pi/3 at v_1, v_2, v_3): Phi = d_0 + d_1 - d_2 + d_3 = 3 d_3  (d_1 = d_3, d_0 = d_2 + d_3);
--   N = 5 (angle pi/3 at v_1, 2pi/3 at v_2, v_3, v_4):  Phi = d_0 + d_1 - d_2 + d_3 - d_4 = 3 d_3  (d_1 = d_3 + d_4, d_0 = d_2 + d_3);
--   N = 6 (all angles 2pi/3):                   Phi = d_0 - d_1 + d_2 - d_3 + d_4 - d_5,  d_0 + d_1 = d_3 + d_4, d_1 + d_2 = d_4 + d_5.
-- Phi(P) := P.flux (G.weight) = sum_j d_j * weight(direction of side j) (LaczFormalFluxPolyFin); additivity of Phi over a dissection is `ConvPoly.flux_cancel`.
-- NOTE / UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Lemma 7.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalFluxPolyPhi2

open scoped Classical
open Erdos634.Geometry

namespace Erdos634.Draft.LaczFormal.Thm21

section Alg
theorem alg3 (c0 s0 c1 s1 c2 s2 r d0 d1 d2 : ℝ) (hr : r^2 = 3) (hu : c0^2 + s0^2 = 1)
    (hc1 : c1 = c0 * (-1/2) - s0 * (r/2)) (hs1 : s1 = s0 * (-1/2) + c0 * (r/2)) (hc2 : c2 = c1 * (-1/2) - s1 * (r/2)) (hs2 : s2 = s1 * (-1/2) + c1 * (r/2))
    (hX : d0 * c0 + d1 * c1 + d2 * c2 = 0) (hY : d0 * s0 + d1 * s1 + d2 * s2 = 0) :
    (1) * d0 + (-1/2) * d1 + (-1/2) * d2 = 0 ∧ r * ((0) * d0 + (1) * d1 + (-1) * d2) = 0 := by
  constructor
  · linear_combination (-c0*d1 + c0*d2/2 - d2*r*s0/2) * hc1 + (c0*d2*r/2 - d1*s0 + d2*s0/2) * hs1 + (-c0*d2) * hc2 + (-d2*s0) * hs2 + (-d0 + d1/2 + d2*r^2/4 - d2/4) * hu + (d2/4) * hr + c0 * hX + s0 * hY
  · linear_combination 2 * ((-c0*d2*r/2 + d1*s0 - d2*s0/2) * hc1 + (-c0*d1 + c0*d2/2 - d2*r*s0/2) * hs1 + (d2*s0) * hc2 + (-c0*d2) * hs2 + (-d1*r/2 + d2*r/2) * hu + c0 * hY + (-s0) * hX)

theorem alg4 (c0 s0 c1 s1 c2 s2 c3 s3 r d0 d1 d2 d3 : ℝ) (hr : r^2 = 3) (hu : c0^2 + s0^2 = 1)
    (hc1 : c1 = c0 * (-1/2) - s0 * (r/2)) (hs1 : s1 = s0 * (-1/2) + c0 * (r/2)) (hc2 : c2 = c1 * (1/2) - s1 * (r/2)) (hs2 : s2 = s1 * (1/2) + c1 * (r/2)) (hc3 : c3 = c2 * (1/2) - s2 * (r/2)) (hs3 : s3 = s2 * (1/2) + c2 * (r/2))
    (hX : d0 * c0 + d1 * c1 + d2 * c2 + d3 * c3 = 0) (hY : d0 * s0 + d1 * s1 + d2 * s2 + d3 * s3 = 0) :
    (1) * d0 + (-1/2) * d1 + (-1) * d2 + (-1/2) * d3 = 0 ∧ r * ((0) * d0 + (1) * d1 + (0) * d2 + (-1) * d3) = 0 := by
  constructor
  · linear_combination (-c0*d1 - c0*d2/2 + c0*d3*r^2/4 - c0*d3/4 - d2*r*s0/2 - d3*r*s0/2) * hc1 + (c0*d2*r/2 + c0*d3*r/2 - d1*s0 - d2*s0/2 + d3*r^2*s0/4 - d3*s0/4) * hs1 + (-c0*d2 - c0*d3/2 - d3*r*s0/2) * hc2 + (c0*d3*r/2 - d2*s0 - d3*s0/2) * hs2 + (-c0*d3) * hc3 + (-d3*s0) * hs3 + (-d0 + d1/2 + d2*r^2/4 + d2/4 + d3*r^2/8 + d3/8) * hu + (d2/4 + d3/8) * hr + c0 * hX + s0 * hY
  · linear_combination 2 * ((-c0*d2*r/2 - c0*d3*r/2 + d1*s0 + d2*s0/2 - d3*r^2*s0/4 + d3*s0/4) * hc1 + (-c0*d1 - c0*d2/2 + c0*d3*r^2/4 - c0*d3/4 - d2*r*s0/2 - d3*r*s0/2) * hs1 + (-c0*d3*r/2 + d2*s0 + d3*s0/2) * hc2 + (-c0*d2 - c0*d3/2 - d3*r*s0/2) * hs2 + (d3*s0) * hc3 + (-c0*d3) * hs3 + (-d1*r/2 + d3*r^3/8 + d3*r/8) * hu + (d3*r/8) * hr + c0 * hY + (-s0) * hX)

theorem alg5 (c0 s0 c1 s1 c2 s2 c3 s3 c4 s4 r d0 d1 d2 d3 d4 : ℝ) (hr : r^2 = 3) (hu : c0^2 + s0^2 = 1)
    (hc1 : c1 = c0 * (-1/2) - s0 * (r/2)) (hs1 : s1 = s0 * (-1/2) + c0 * (r/2)) (hc2 : c2 = c1 * (1/2) - s1 * (r/2)) (hs2 : s2 = s1 * (1/2) + c1 * (r/2)) (hc3 : c3 = c2 * (1/2) - s2 * (r/2)) (hs3 : s3 = s2 * (1/2) + c2 * (r/2)) (hc4 : c4 = c3 * (1/2) - s3 * (r/2)) (hs4 : s4 = s3 * (1/2) + c3 * (r/2))
    (hX : d0 * c0 + d1 * c1 + d2 * c2 + d3 * c3 + d4 * c4 = 0) (hY : d0 * s0 + d1 * s1 + d2 * s2 + d3 * s3 + d4 * s4 = 0) :
    (1) * d0 + (-1/2) * d1 + (-1) * d2 + (-1/2) * d3 + (1/2) * d4 = 0 ∧ r * ((0) * d0 + (1) * d1 + (0) * d2 + (-1) * d3 + (-1) * d4) = 0 := by
  constructor
  · linear_combination (-c0*d1 - c0*d2/2 + c0*d3*r^2/4 - c0*d3/4 + 3*c0*d4*r^2/8 - c0*d4/8 - d2*r*s0/2 - d3*r*s0/2 + d4*r^3*s0/8 - 3*d4*r*s0/8) * hc1 + (c0*d2*r/2 + c0*d3*r/2 - c0*d4*r^3/8 + 3*c0*d4*r/8 - d1*s0 - d2*s0/2 + d3*r^2*s0/4 - d3*s0/4 + 3*d4*r^2*s0/8 - d4*s0/8) * hs1 + (-c0*d2 - c0*d3/2 + c0*d4*r^2/4 - c0*d4/4 - d3*r*s0/2 - d4*r*s0/2) * hc2 + (c0*d3*r/2 + c0*d4*r/2 - d2*s0 - d3*s0/2 + d4*r^2*s0/4 - d4*s0/4) * hs2 + (-c0*d3 - c0*d4/2 - d4*r*s0/2) * hc3 + (c0*d4*r/2 - d3*s0 - d4*s0/2) * hs3 + (-c0*d4) * hc4 + (-d4*s0) * hs4 + (-d0 + d1/2 + d2*r^2/4 + d2/4 + d3*r^2/8 + d3/8 - d4*r^4/16 + d4/16) * hu + (d2/4 + d3/8 - d4*r^2/16 - 3*d4/16) * hr + c0 * hX + s0 * hY
  · linear_combination 2 * ((-c0*d2*r/2 - c0*d3*r/2 + c0*d4*r^3/8 - 3*c0*d4*r/8 + d1*s0 + d2*s0/2 - d3*r^2*s0/4 + d3*s0/4 - 3*d4*r^2*s0/8 + d4*s0/8) * hc1 + (-c0*d1 - c0*d2/2 + c0*d3*r^2/4 - c0*d3/4 + 3*c0*d4*r^2/8 - c0*d4/8 - d2*r*s0/2 - d3*r*s0/2 + d4*r^3*s0/8 - 3*d4*r*s0/8) * hs1 + (-c0*d3*r/2 - c0*d4*r/2 + d2*s0 + d3*s0/2 - d4*r^2*s0/4 + d4*s0/4) * hc2 + (-c0*d2 - c0*d3/2 + c0*d4*r^2/4 - c0*d4/4 - d3*r*s0/2 - d4*r*s0/2) * hs2 + (-c0*d4*r/2 + d3*s0 + d4*s0/2) * hc3 + (-c0*d3 - c0*d4/2 - d4*r*s0/2) * hs3 + (d4*s0) * hc4 + (-c0*d4) * hs4 + (-d1*r/2 + d3*r^3/8 + d3*r/8 + d4*r^3/8 + d4*r/8) * hu + (d3*r/8 + d4*r/8) * hr + c0 * hY + (-s0) * hX)

theorem alg6 (c0 s0 c1 s1 c2 s2 c3 s3 c4 s4 c5 s5 r d0 d1 d2 d3 d4 d5 : ℝ) (hr : r^2 = 3) (hu : c0^2 + s0^2 = 1)
    (hc1 : c1 = c0 * (1/2) - s0 * (r/2)) (hs1 : s1 = s0 * (1/2) + c0 * (r/2)) (hc2 : c2 = c1 * (1/2) - s1 * (r/2)) (hs2 : s2 = s1 * (1/2) + c1 * (r/2)) (hc3 : c3 = c2 * (1/2) - s2 * (r/2)) (hs3 : s3 = s2 * (1/2) + c2 * (r/2)) (hc4 : c4 = c3 * (1/2) - s3 * (r/2)) (hs4 : s4 = s3 * (1/2) + c3 * (r/2)) (hc5 : c5 = c4 * (1/2) - s4 * (r/2)) (hs5 : s5 = s4 * (1/2) + c4 * (r/2))
    (hX : d0 * c0 + d1 * c1 + d2 * c2 + d3 * c3 + d4 * c4 + d5 * c5 = 0) (hY : d0 * s0 + d1 * s1 + d2 * s2 + d3 * s3 + d4 * s4 + d5 * s5 = 0) :
    (1) * d0 + (1/2) * d1 + (-1/2) * d2 + (-1) * d3 + (-1/2) * d4 + (1/2) * d5 = 0 ∧ r * ((0) * d0 + (1) * d1 + (1) * d2 + (0) * d3 + (-1) * d4 + (-1) * d5) = 0 := by
  constructor
  · linear_combination (-c0*d1 - c0*d2/2 + c0*d3*r^2/4 - c0*d3/4 + 3*c0*d4*r^2/8 - c0*d4/8 - c0*d5*r^4/16 + 3*c0*d5*r^2/8 - c0*d5/16 - d2*r*s0/2 - d3*r*s0/2 + d4*r^3*s0/8 - 3*d4*r*s0/8 + d5*r^3*s0/4 - d5*r*s0/4) * hc1 + (c0*d2*r/2 + c0*d3*r/2 - c0*d4*r^3/8 + 3*c0*d4*r/8 - c0*d5*r^3/4 + c0*d5*r/4 - d1*s0 - d2*s0/2 + d3*r^2*s0/4 - d3*s0/4 + 3*d4*r^2*s0/8 - d4*s0/8 - d5*r^4*s0/16 + 3*d5*r^2*s0/8 - d5*s0/16) * hs1 + (-c0*d2 - c0*d3/2 + c0*d4*r^2/4 - c0*d4/4 + 3*c0*d5*r^2/8 - c0*d5/8 - d3*r*s0/2 - d4*r*s0/2 + d5*r^3*s0/8 - 3*d5*r*s0/8) * hc2 + (c0*d3*r/2 + c0*d4*r/2 - c0*d5*r^3/8 + 3*c0*d5*r/8 - d2*s0 - d3*s0/2 + d4*r^2*s0/4 - d4*s0/4 + 3*d5*r^2*s0/8 - d5*s0/8) * hs2 + (-c0*d3 - c0*d4/2 + c0*d5*r^2/4 - c0*d5/4 - d4*r*s0/2 - d5*r*s0/2) * hc3 + (c0*d4*r/2 + c0*d5*r/2 - d3*s0 - d4*s0/2 + d5*r^2*s0/4 - d5*s0/4) * hs3 + (-c0*d4 - c0*d5/2 - d5*r*s0/2) * hc4 + (c0*d5*r/2 - d4*s0 - d5*s0/2) * hs4 + (-c0*d5) * hc5 + (-d5*s0) * hs5 + (-d0 - d1/2 + d2*r^2/4 - d2/4 + 3*d3*r^2/8 - d3/8 - d4*r^4/16 + 3*d4*r^2/8 - d4/16 - 5*d5*r^4/32 + 5*d5*r^2/16 - d5/32) * hu + (d2/4 + 3*d3/8 - d4*r^2/16 + 3*d4/16 - 5*d5*r^2/32 - 5*d5/32) * hr + c0 * hX + s0 * hY
  · linear_combination 2 * ((-c0*d2*r/2 - c0*d3*r/2 + c0*d4*r^3/8 - 3*c0*d4*r/8 + c0*d5*r^3/4 - c0*d5*r/4 + d1*s0 + d2*s0/2 - d3*r^2*s0/4 + d3*s0/4 - 3*d4*r^2*s0/8 + d4*s0/8 + d5*r^4*s0/16 - 3*d5*r^2*s0/8 + d5*s0/16) * hc1 + (-c0*d1 - c0*d2/2 + c0*d3*r^2/4 - c0*d3/4 + 3*c0*d4*r^2/8 - c0*d4/8 - c0*d5*r^4/16 + 3*c0*d5*r^2/8 - c0*d5/16 - d2*r*s0/2 - d3*r*s0/2 + d4*r^3*s0/8 - 3*d4*r*s0/8 + d5*r^3*s0/4 - d5*r*s0/4) * hs1 + (-c0*d3*r/2 - c0*d4*r/2 + c0*d5*r^3/8 - 3*c0*d5*r/8 + d2*s0 + d3*s0/2 - d4*r^2*s0/4 + d4*s0/4 - 3*d5*r^2*s0/8 + d5*s0/8) * hc2 + (-c0*d2 - c0*d3/2 + c0*d4*r^2/4 - c0*d4/4 + 3*c0*d5*r^2/8 - c0*d5/8 - d3*r*s0/2 - d4*r*s0/2 + d5*r^3*s0/8 - 3*d5*r*s0/8) * hs2 + (-c0*d4*r/2 - c0*d5*r/2 + d3*s0 + d4*s0/2 - d5*r^2*s0/4 + d5*s0/4) * hc3 + (-c0*d3 - c0*d4/2 + c0*d5*r^2/4 - c0*d5/4 - d4*r*s0/2 - d5*r*s0/2) * hs3 + (-c0*d5*r/2 + d4*s0 + d5*s0/2) * hc4 + (-c0*d4 - c0*d5/2 - d5*r*s0/2) * hs4 + (d5*s0) * hc5 + (-c0*d5) * hs5 + (-d1*r/2 - d2*r/2 + d3*r^3/8 - 3*d3*r/8 + d4*r^3/4 - d4*r/4 - d5*r^5/32 + 5*d5*r^3/16 - 5*d5*r/32) * hu + (d3*r/8 + d4*r/4 - d5*r^3/32 + 7*d5*r/32) * hr + c0 * hY + (-s0) * hX)


end Alg

variable {M : ℕ} [NeZero M]

theorem sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

section Chi
variable (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (θ₀ : Real.Angle)

theorem chi_third (k : ℤ) :
    (fAlphaAt α hα θ₀).chi (((k : ℝ) * (Real.pi / 3) : ℝ) : Real.Angle) = if (k : ZMod 2) = 0 then 1 else -1 := by
  have := GridChar.rankn_chi 3 (by norm_num) (by decide) α hα 0 θ₀ k 0
  simpa [fAlphaAt] using this

theorem third_mem (k : ℤ) : (((k : ℝ) * (Real.pi / 3) : ℝ) : Real.Angle) ∈ (fAlphaAt α hα θ₀).L := by
  have := GridChar.rankn_mem 3 (by norm_num) (by decide) α hα 0 θ₀ k 0
  simpa [fAlphaAt] using this

theorem weight_anchor (d : Dir) (hd : d.angle = θ₀) : (fAlphaAt α hα θ₀).weight d = 1 := by
  unfold GridChar.weight
  rw [hd]
  exact GridChar.val_anchor _

end Chi

namespace ConvPoly
variable (P : ConvPoly M)

theorem turn_a (j k : Fin M) (hjk : j + 1 = k) (h : P.angle k = Real.pi / 3) :
    P.cx k = P.cx j * (-1 / 2) - P.sy j * (Real.sqrt 3 / 2) ∧ P.sy k = P.sy j * (-1 / 2) + P.cx j * (Real.sqrt 3 / 2) := by
  subst hjk
  rw [P.rot_cos, P.rot_sin, h, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  constructor <;> ring

theorem turn_b (j k : Fin M) (hjk : j + 1 = k) (h : P.angle k = 2 * Real.pi / 3) :
    P.cx k = P.cx j * (1 / 2) - P.sy j * (Real.sqrt 3 / 2) ∧ P.sy k = P.sy j * (1 / 2) + P.cx j * (Real.sqrt 3 / 2) := by
  subst hjk
  rw [P.rot_cos, P.rot_sin, h, show Real.pi - 2 * Real.pi / 3 = Real.pi / 3 by ring, Real.cos_pi_div_three, Real.sin_pi_div_three]
  constructor <;> ring

variable (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (θ₀ : Real.Angle)

theorem weight_step_a (j k : Fin M) (hjk : j + 1 = k) (h : P.angle k = Real.pi / 3) :
    (fAlphaAt α hα θ₀).weight (P.sideDir k) = (fAlphaAt α hα θ₀).weight (P.sideDir j) := by
  subst hjk
  have hm : ((Real.pi - P.angle (j + 1) : ℝ) : Real.Angle) ∈ (fAlphaAt α hα θ₀).L := by
    rw [h, show Real.pi - Real.pi / 3 = ((2 : ℤ) : ℝ) * (Real.pi / 3) by push_cast; ring]
    exact third_mem α hα θ₀ 2
  rw [P.weight_next _ j hm, h, show Real.pi - Real.pi / 3 = ((2 : ℤ) : ℝ) * (Real.pi / 3) by push_cast; ring,
    chi_third α hα θ₀ 2]
  have h2 : ((2 : ℤ) : ZMod 2) = 0 := by decide
  rw [if_pos h2, one_mul]

theorem weight_step_b (j k : Fin M) (hjk : j + 1 = k) (h : P.angle k = 2 * Real.pi / 3) :
    (fAlphaAt α hα θ₀).weight (P.sideDir k) = -(fAlphaAt α hα θ₀).weight (P.sideDir j) := by
  subst hjk
  have e : Real.pi - 2 * Real.pi / 3 = ((1 : ℤ) : ℝ) * (Real.pi / 3) := by push_cast; ring
  have hm : ((Real.pi - P.angle (j + 1) : ℝ) : Real.Angle) ∈ (fAlphaAt α hα θ₀).L := by
    rw [h, e]
    exact third_mem α hα θ₀ 1
  rw [P.weight_next _ j hm, h, e, chi_third α hα θ₀ 1]
  simp

end ConvPoly

namespace ConvPoly

/-- **The functional `Phi` of Laczkovich** (DCG 48 (2012), p. 351, formula (14)) for `G = <pi/3, alpha>` and `chi(n pi/3 + m alpha) = (-1)^n`, in the frame in which side `0`
lies on the `x`-axis: `Phi(P) = sum_j d_j * chi(direction of side j)`; `P.flux_cancel` is its additivity over a dissection. -/
noncomputable def Phi {M : ℕ} [NeZero M] (P : ConvPoly M) (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) : ℝ :=
  P.flux (fAlphaAt α hα (P.sideDir 0).angle).weight

end ConvPoly

section L72
variable (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)

private theorem sqrt3_ne : Real.sqrt 3 ≠ 0 := by positivity

/-- **Lemma 7.2, `N = 3`** (all angles `pi/3`): the sides are equal and `Phi(A) = 3 d_0`. -/
theorem lemma72_three (P : ConvPoly 3) (hA : ∀ i, P.angle i = Real.pi / 3) :
    P.side 0 = P.side 1 ∧ P.side 1 = P.side 2 ∧ P.Phi α hα = 3 * P.side 0 := by
  have hX := P.closure_x
  have hY := P.closure_y
  rw [Fin.sum_univ_three] at hX hY
  obtain ⟨c1, s1⟩ := P.turn_a 0 1 (by decide) (hA 1)
  obtain ⟨c2, s2⟩ := P.turn_a 1 2 (by decide) (hA 2)
  obtain ⟨hRe, hIm⟩ := alg3 (P.cx 0) (P.sy 0) (P.cx 1) (P.sy 1) (P.cx 2) (P.sy 2) (Real.sqrt 3)
    (P.side 0) (P.side 1) (P.side 2) sqrt3_sq (P.unit_sq 0) c1 s1 c2 s2 hX hY
  have hIm' := (mul_eq_zero.mp hIm).resolve_left sqrt3_ne
  have w0 : (fAlphaAt α hα (P.sideDir 0).angle).weight (P.sideDir 0) = 1 := weight_anchor α hα _ _ rfl
  have w1 := P.weight_step_a α hα (P.sideDir 0).angle 0 1 (by decide) (hA 1)
  have w2 := P.weight_step_a α hα (P.sideDir 0).angle 1 2 (by decide) (hA 2)
  have hP : P.Phi α hα = P.side 0 + P.side 1 + P.side 2 := by
    unfold ConvPoly.Phi ConvPoly.flux
    rw [Fin.sum_univ_three]; simp only [smul_eq_mul]
    rw [w2, w1, w0]; ring
  refine ⟨by linarith, by linarith, by rw [hP]; linarith⟩

/-- **Lemma 7.2, `N = 4`** (angles `pi/3, 2pi/3, 2pi/3` at `v_1, v_2, v_3`; trapezoid): `d_1 = d_3`, `d_0 = d_2 + d_3`, `Phi(A) = d_0 + d_1 - d_2 + d_3 = 3 d_3`. -/
theorem lemma72_four (P : ConvPoly 4) (h1 : P.angle 1 = Real.pi / 3) (h2 : P.angle 2 = 2 * Real.pi / 3)
    (h3 : P.angle 3 = 2 * Real.pi / 3) :
    P.side 1 = P.side 3 ∧ P.side 0 = P.side 2 + P.side 3 ∧ P.Phi α hα = 3 * P.side 3 := by
  have hX := P.closure_x
  have hY := P.closure_y
  rw [Fin.sum_univ_four] at hX hY
  obtain ⟨c1, s1⟩ := P.turn_a 0 1 (by decide) h1
  obtain ⟨c2, s2⟩ := P.turn_b 1 2 (by decide) h2
  obtain ⟨c3, s3⟩ := P.turn_b 2 3 (by decide) h3
  obtain ⟨hRe, hIm⟩ := alg4 (P.cx 0) (P.sy 0) (P.cx 1) (P.sy 1) (P.cx 2) (P.sy 2) (P.cx 3) (P.sy 3) (Real.sqrt 3)
    (P.side 0) (P.side 1) (P.side 2) (P.side 3) sqrt3_sq (P.unit_sq 0) c1 s1 c2 s2 c3 s3 hX hY
  have hIm' := (mul_eq_zero.mp hIm).resolve_left sqrt3_ne
  have w0 : (fAlphaAt α hα (P.sideDir 0).angle).weight (P.sideDir 0) = 1 := weight_anchor α hα _ _ rfl
  have w1 := P.weight_step_a α hα (P.sideDir 0).angle 0 1 (by decide) h1
  have w2 := P.weight_step_b α hα (P.sideDir 0).angle 1 2 (by decide) h2
  have w3 := P.weight_step_b α hα (P.sideDir 0).angle 2 3 (by decide) h3
  have hP : P.Phi α hα = P.side 0 + P.side 1 - P.side 2 + P.side 3 := by
    unfold ConvPoly.Phi ConvPoly.flux
    rw [Fin.sum_univ_four]; simp only [smul_eq_mul]
    rw [w3, w2, w1, w0]; ring
  refine ⟨by linarith, by linarith, by rw [hP]; linarith⟩

/-- **Lemma 7.2, `N = 5`** (angle `pi/3` at `v_1`, `2pi/3` at `v_2, v_3, v_4`; pentagon): `d_1 = d_3 + d_4`, `d_0 = d_2 + d_3`, `Phi(A) = d_0 + d_1 - d_2 + d_3 - d_4 = 3 d_3`. -/
theorem lemma72_five (P : ConvPoly 5) (h1 : P.angle 1 = Real.pi / 3) (h2 : P.angle 2 = 2 * Real.pi / 3)
    (h3 : P.angle 3 = 2 * Real.pi / 3) (h4 : P.angle 4 = 2 * Real.pi / 3) :
    P.side 1 = P.side 3 + P.side 4 ∧ P.side 0 = P.side 2 + P.side 3 ∧ P.Phi α hα = 3 * P.side 3 := by
  have hX := P.closure_x
  have hY := P.closure_y
  rw [Fin.sum_univ_five] at hX hY
  obtain ⟨c1, s1⟩ := P.turn_a 0 1 (by decide) h1
  obtain ⟨c2, s2⟩ := P.turn_b 1 2 (by decide) h2
  obtain ⟨c3, s3⟩ := P.turn_b 2 3 (by decide) h3
  obtain ⟨c4, s4⟩ := P.turn_b 3 4 (by decide) h4
  obtain ⟨hRe, hIm⟩ := alg5 (P.cx 0) (P.sy 0) (P.cx 1) (P.sy 1) (P.cx 2) (P.sy 2) (P.cx 3) (P.sy 3) (P.cx 4) (P.sy 4)
    (Real.sqrt 3) (P.side 0) (P.side 1) (P.side 2) (P.side 3) (P.side 4) sqrt3_sq (P.unit_sq 0) c1 s1 c2 s2 c3 s3 c4 s4 hX hY
  have hIm' := (mul_eq_zero.mp hIm).resolve_left sqrt3_ne
  have w0 : (fAlphaAt α hα (P.sideDir 0).angle).weight (P.sideDir 0) = 1 := weight_anchor α hα _ _ rfl
  have w1 := P.weight_step_a α hα (P.sideDir 0).angle 0 1 (by decide) h1
  have w2 := P.weight_step_b α hα (P.sideDir 0).angle 1 2 (by decide) h2
  have w3 := P.weight_step_b α hα (P.sideDir 0).angle 2 3 (by decide) h3
  have w4 := P.weight_step_b α hα (P.sideDir 0).angle 3 4 (by decide) h4
  have hP : P.Phi α hα = P.side 0 + P.side 1 - P.side 2 + P.side 3 - P.side 4 := by
    unfold ConvPoly.Phi ConvPoly.flux
    rw [Fin.sum_univ_five]; simp only [smul_eq_mul]
    rw [w4, w3, w2, w1, w0]; ring
  refine ⟨by linarith, by linarith, by rw [hP]; linarith⟩

/-- **Lemma 7.2, `N = 6`** (all angles `2pi/3`): `Phi(A) = d_0 - d_1 + d_2 - d_3 + d_4 - d_5`, with `d_0 + d_1 = d_3 + d_4` and `d_1 + d_2 = d_4 + d_5`. -/
theorem lemma72_six (P : ConvPoly 6) (hA : ∀ i, P.angle i = 2 * Real.pi / 3) :
    P.side 0 + P.side 1 = P.side 3 + P.side 4 ∧ P.side 1 + P.side 2 = P.side 4 + P.side 5 ∧
      P.Phi α hα = P.side 0 - P.side 1 + P.side 2 - P.side 3 + P.side 4 - P.side 5 := by
  have hX := P.closure_x
  have hY := P.closure_y
  rw [Fin.sum_univ_six] at hX hY
  obtain ⟨c1, s1⟩ := P.turn_b 0 1 (by decide) (hA 1)
  obtain ⟨c2, s2⟩ := P.turn_b 1 2 (by decide) (hA 2)
  obtain ⟨c3, s3⟩ := P.turn_b 2 3 (by decide) (hA 3)
  obtain ⟨c4, s4⟩ := P.turn_b 3 4 (by decide) (hA 4)
  obtain ⟨c5, s5⟩ := P.turn_b 4 5 (by decide) (hA 5)
  obtain ⟨hRe, hIm⟩ := alg6 (P.cx 0) (P.sy 0) (P.cx 1) (P.sy 1) (P.cx 2) (P.sy 2) (P.cx 3) (P.sy 3) (P.cx 4) (P.sy 4)
    (P.cx 5) (P.sy 5) (Real.sqrt 3) (P.side 0) (P.side 1) (P.side 2) (P.side 3) (P.side 4) (P.side 5) sqrt3_sq (P.unit_sq 0)
    c1 s1 c2 s2 c3 s3 c4 s4 c5 s5 hX hY
  have hIm' := (mul_eq_zero.mp hIm).resolve_left sqrt3_ne
  have w0 : (fAlphaAt α hα (P.sideDir 0).angle).weight (P.sideDir 0) = 1 := weight_anchor α hα _ _ rfl
  have w1 := P.weight_step_b α hα (P.sideDir 0).angle 0 1 (by decide) (hA 1)
  have w2 := P.weight_step_b α hα (P.sideDir 0).angle 1 2 (by decide) (hA 2)
  have w3 := P.weight_step_b α hα (P.sideDir 0).angle 2 3 (by decide) (hA 3)
  have w4 := P.weight_step_b α hα (P.sideDir 0).angle 3 4 (by decide) (hA 4)
  have w5 := P.weight_step_b α hα (P.sideDir 0).angle 4 5 (by decide) (hA 5)
  have hP : P.Phi α hα = P.side 0 - P.side 1 + P.side 2 - P.side 3 + P.side 4 - P.side 5 := by
    unfold ConvPoly.Phi ConvPoly.flux
    rw [Fin.sum_univ_six]; simp only [smul_eq_mul]
    rw [w5, w4, w3, w2, w1, w0]; ring
  exact ⟨by linarith, by linarith, hP⟩

end L72

namespace ConvPoly

/-- **Additivity of `Phi`** (Laczkovich, p. 351): for a dissection `R` of the convex polygon `P` into triangles, `Phi(P) = sum of the tile fluxes` of the same weight
(`G = <pi/3, alpha>` anchored at side 0 of `P`).  This is `flux_cancel` at the odd weight `G.weight`. -/
theorem Phi_additive {M N : ℕ} [NeZero M] (P : ConvPoly M) (R : Erdos634.RegionDissection.RegionDissection N) (hR : R.region = P.carrier) (α : ℝ)
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) :
    ∑ i, (R.tile i).flux (fAlphaAt α hα (P.sideDir 0).angle).weight = P.Phi α hα :=
  P.flux_cancel R hR _ (fAlphaAt α hα (P.sideDir 0).angle).weight_odd

end ConvPoly

end Erdos634.Draft.LaczFormal.Thm21

#print axioms Erdos634.Draft.LaczFormal.Thm21.lemma72_three
#print axioms Erdos634.Draft.LaczFormal.Thm21.lemma72_four
#print axioms Erdos634.Draft.LaczFormal.Thm21.lemma72_five
#print axioms Erdos634.Draft.LaczFormal.Thm21.lemma72_six
#print axioms Erdos634.Draft.LaczFormal.Thm21.ConvPoly.Phi_additive
