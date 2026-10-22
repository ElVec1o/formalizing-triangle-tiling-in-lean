-- Draft/LaczFormalRG9Geo.lean -- geometry for Case I of Laczkovich's Theorem 2.1: (1) the interior angles of a strictly convex polygon lie in `(0, pi)`;
-- (2) a convex quadrilateral with consecutive angles `theta, pi - theta, theta` is a parallelogram (general `theta`; the `theta = 2pi/3` instance is `quad_parallelogram`).  UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 5), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG4CaseIV

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {M : ℕ} [NeZero M]

/-- The interior angles of a strictly convex polygon lie in `(0, π)`. -/
theorem polyAngle_bounds (P : ConvPoly M) (i : Fin M) : 0 < P.angle i ∧ P.angle i < Real.pi := by
  have hturn := (turn_of_angle P i).1
  have hn1 : 0 < ‖P.e (i - 1)‖ := norm_pos_iff.mpr (P.e_ne_zero P.three_le (i - 1))
  have hn2 : 0 < ‖P.e i‖ := norm_pos_iff.mpr (P.e_ne_zero P.three_le i)
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := ConvPoly.fin_facts P.three_le i
  have hpos : 0 < cross2 (P.e (i - 1)) (P.e i) := by
    have := P.left (i - 1) (i + 1) (by intro h; exact f4 h) (by rw [f5]; exact f1)
    have e1 : P.v (i - 1 + 1) - P.v (i - 1) = P.e (i - 1) := rfl
    have e2 : P.v (i + 1) - P.v (i - 1) = P.e (i - 1) + P.e i := by
      unfold ConvPoly.e; rw [f5]; abel
    rw [e1, e2, cross2_add_right, cross2_self] at this
    simpa using this
  have hsin : 0 < Real.sin (P.angle i) := by
    by_contra hle
    push Not at hle
    have : ‖P.e (i - 1)‖ * ‖P.e i‖ * Real.sin (P.angle i) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hle
    linarith
  have hge : 0 ≤ P.angle i := by
    unfold ConvPoly.angle cornerAngle EuclideanGeometry.angle; exact InnerProductGeometry.angle_nonneg _ _
  have hle : P.angle i ≤ Real.pi := by
    unfold ConvPoly.angle cornerAngle EuclideanGeometry.angle; exact InnerProductGeometry.angle_le_pi _ _
  refine ⟨?_, ?_⟩
  · rcases hge.lt_or_eq with h | h
    · exact h
    · rw [← h] at hsin; simp at hsin
  · rcases hle.lt_or_eq with h | h
    · exact h
    · rw [h] at hsin; simp at hsin

/-- **Algebra of the `θ, π-θ, θ, π-θ` quadrilateral** (`u = -cos θ`, `s = sin θ`). -/
theorem quad_alg_gen (u s : ℝ) (hs : 0 < s) (hus : u ^ 2 + s ^ 2 = 1)
    (p0 p1 q0 q1 r0 r1 s0 s1 np nq nr ns : ℝ) (hnp : 0 < np) (hnq : 0 < nq) (hnr : 0 < nr) (hns : 0 < ns)
    (hp : np ^ 2 = p0 ^ 2 + p1 ^ 2)
    (hq : nq ^ 2 = q0 ^ 2 + q1 ^ 2) (hr : nr ^ 2 = r0 ^ 2 + r1 ^ 2)
    (c1 : p0 * q0 + p1 * q1 = np * nq * u) (d1 : p0 * q1 - p1 * q0 = s * np * nq)
    (c2 : q0 * r0 + q1 * r1 = -(nq * nr * u)) (d2 : q0 * r1 - q1 * r0 = s * nq * nr)
    (c3 : r0 * s0 + r1 * s1 = nr * ns * u) (d3 : r0 * s1 - r1 * s0 = s * nr * ns)
    (hz0 : p0 + q0 + r0 + s0 = 0) (hz1 : p1 + q1 + r1 + s1 = 0) : p0 + r0 = 0 ∧ p1 + r1 = 0 := by
  have Q0 : np * q0 = nq * (u * p0 - s * p1) := by
    have : np * (np * q0 - nq * (u * p0 - s * p1)) = 0 := by
      linear_combination q0 * hp + p0 * c1 - p1 * d1
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hnp.ne'
    · linarith
  have Q1 : np * q1 = nq * (u * p1 + s * p0) := by
    have : np * (np * q1 - nq * (u * p1 + s * p0)) = 0 := by
      linear_combination q1 * hp + p1 * c1 + p0 * d1
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hnp.ne'
    · linarith
  have R0 : nq * r0 = nr * (-u * q0 - s * q1) := by
    have : nq * (nq * r0 - nr * (-u * q0 - s * q1)) = 0 := by
      linear_combination r0 * hq + q0 * c2 - q1 * d2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hnq.ne'
    · linarith
  have R1 : nq * r1 = nr * (-u * q1 + s * q0) := by
    have : nq * (nq * r1 - nr * (-u * q1 + s * q0)) = 0 := by
      linear_combination r1 * hq + q1 * c2 + q0 * d2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hnq.ne'
    · linarith
  have S0 : nr * s0 = ns * (u * r0 - s * r1) := by
    have : nr * (nr * s0 - ns * (u * r0 - s * r1)) = 0 := by
      linear_combination s0 * hr + r0 * c3 - r1 * d3
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hnr.ne'
    · linarith
  have S1 : nr * s1 = ns * (u * r1 + s * r0) := by
    have : nr * (nr * s1 - ns * (u * r1 + s * r0)) = 0 := by
      linear_combination s1 * hr + r1 * c3 + r0 * d3
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hnr.ne'
    · linarith
  have Rp0 : np * r0 = - nr * p0 := by
    have : nq * (np * r0 + nr * p0) = 0 := by
      linear_combination np * R0 + (-(nr * u)) * Q0 + (-(nr * s)) * Q1 + (-(nq * nr * p0)) * hus
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hnq.ne'
    · linarith
  have Rp1 : np * r1 = - nr * p1 := by
    have : nq * (np * r1 + nr * p1) = 0 := by
      linear_combination np * R1 + (-(nr * u)) * Q1 + (nr * s) * Q0 + (-(nq * nr * p1)) * hus
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hnq.ne'
    · linarith
  have Sp0 : np * s0 = ns * (-u * p0 + s * p1) := by
    have : nr * (np * s0 - ns * (-u * p0 + s * p1)) = 0 := by
      linear_combination np * S0 + (ns * u) * Rp0 + (-(ns * s)) * Rp1
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hnr.ne'
    · linarith
  have Sp1 : np * s1 = ns * (-u * p1 - s * p0) := by
    have : nr * (np * s1 - ns * (-u * p1 - s * p0)) = 0 := by
      linear_combination np * S1 + (ns * u) * Rp1 + (ns * s) * Rp0
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hnr.ne'
    · linarith
  have E0 : (np - nr) * p0 + (nq - ns) * (u * p0 - s * p1) = 0 := by
    linear_combination np * hz0 - Q0 - Rp0 - Sp0
  have E1 : (np - nr) * p1 + (nq - ns) * (u * p1 + s * p0) = 0 := by
    linear_combination np * hz1 - Q1 - Rp1 - Sp1
  have hY : (nq - ns) * (s * np ^ 2) = 0 := by
    linear_combination (-1 : ℝ) * (p1 * E0 - p0 * E1) + (nq - ns) * s * hp
  have hY' : nq = ns := by
    rcases mul_eq_zero.mp hY with h | h
    · linarith
    · exfalso
      have : 0 < s * np ^ 2 := by positivity
      linarith
  have hX0 : (np - nr) * p0 = 0 := by rw [hY'] at E0; linarith
  have hX1 : (np - nr) * p1 = 0 := by rw [hY'] at E1; linarith
  have hX : (np - nr) * np ^ 2 = 0 := by rw [hp]; linear_combination p0 * hX0 + p1 * hX1
  have hX' : np = nr := by
    rcases mul_eq_zero.mp hX with h | h
    · linarith
    · exfalso; have : 0 < np ^ 2 := by positivity
      linarith
  subst hX'
  constructor
  · have : np * (r0 + p0) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hnp.ne'
    · linarith
  · have : np * (r1 + p1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hnp.ne'
    · linarith

/-- **A convex quadrilateral with consecutive angles `θ, π - θ, θ` at `v_{a+1}, v_{a+2}, v_{a+3}` is a parallelogram.** -/
theorem quad_parallelogram_gen (P : ConvPoly 4) (a : Fin 4) (θ : ℝ) (h1 : P.angle (a + 1) = θ) (h2 : P.angle (a + 2) = Real.pi - θ)
    (h3 : P.angle (a + 3) = θ) : P.v a + P.v (a + 2) = P.v (a + 1) + P.v (a + 3) := by
  have t1 := turn_of_angle P (a + 1)
  have t2 := turn_of_angle P (a + 2)
  have t3 := turn_of_angle P (a + 3)
  have e1 : a + 1 - 1 = a := by simp
  have e2 : a + 2 - 1 = a + 1 := by
    have : ∀ a : Fin 4, a + 2 - 1 = a + 1 := by decide
    exact this a
  have e3 : a + 3 - 1 = a + 2 := by
    have : ∀ a : Fin 4, a + 3 - 1 = a + 2 := by decide
    exact this a
  rw [e1, h1] at t1
  rw [e2, h2] at t2
  rw [e3, h3] at t3
  rw [Real.sin_pi_sub, Real.cos_pi_sub] at t2
  have hb := polyAngle_bounds P (a + 1)
  rw [h1] at hb
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hb.1 hb.2
  have hp0 := P.e_ne_zero P.three_le a
  have hq0 := P.e_ne_zero P.three_le (a + 1)
  have hr0 := P.e_ne_zero P.three_le (a + 2)
  have hs0 := P.e_ne_zero P.three_le (a + 3)
  have hnp : 0 < ‖P.e a‖ := norm_pos_iff.mpr hp0
  have hnq : 0 < ‖P.e (a + 1)‖ := norm_pos_iff.mpr hq0
  have hnr : 0 < ‖P.e (a + 2)‖ := norm_pos_iff.mpr hr0
  have hns : 0 < ‖P.e (a + 3)‖ := norm_pos_iff.mpr hs0
  have hclos : P.e a + P.e (a + 1) + P.e (a + 2) + P.e (a + 3) = 0 := by
    have h4 : a + 3 + 1 = a := by
      have : ∀ a : Fin 4, a + 3 + 1 = a := by decide
      exact this a
    have h12 : a + 1 + 1 = a + 2 := by
      have : ∀ a : Fin 4, a + 1 + 1 = a + 2 := by decide
      exact this a
    have h23 : a + 2 + 1 = a + 3 := by
      have : ∀ a : Fin 4, a + 2 + 1 = a + 3 := by decide
      exact this a
    unfold ConvPoly.e
    rw [h12, h23, h4]; abel
  have hz0 : P.e a 0 + P.e (a + 1) 0 + P.e (a + 2) 0 + P.e (a + 3) 0 = 0 := by
    have := congrArg (fun v : Plane => v 0) hclos; simpa using this
  have hz1 : P.e a 1 + P.e (a + 1) 1 + P.e (a + 2) 1 + P.e (a + 3) 1 = 0 := by
    have := congrArg (fun v : Plane => v 1) hclos; simpa using this
  obtain ⟨d1, c1⟩ := t1
  obtain ⟨d2, c2⟩ := t2
  obtain ⟨d3, c3⟩ := t3
  rw [inner_plane] at c1 c2 c3
  unfold cross2 at d1 d2 d3
  have hus : (-Real.cos θ) ^ 2 + Real.sin θ ^ 2 = 1 := by nlinarith [Real.sin_sq_add_cos_sq θ]
  have := quad_alg_gen (-Real.cos θ) (Real.sin θ) hs hus (P.e a 0) (P.e a 1) (P.e (a + 1) 0) (P.e (a + 1) 1) (P.e (a + 2) 0) (P.e (a + 2) 1) (P.e (a + 3) 0) (P.e (a + 3) 1)
    ‖P.e a‖ ‖P.e (a + 1)‖ ‖P.e (a + 2)‖ ‖P.e (a + 3)‖ hnp hnq hnr hns (norm_sq_plane _) (norm_sq_plane _) (norm_sq_plane _)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hz0 hz1
  obtain ⟨r0, r1⟩ := this
  have h23 : a + 2 + 1 = a + 3 := by
    have : ∀ a : Fin 4, a + 2 + 1 = a + 3 := by decide
    exact this a
  have hpr0 : (P.v (a + 1) - P.v a) 0 + (P.v (a + 3) - P.v (a + 2)) 0 = 0 := by
    have : P.e a 0 + P.e (a + 2) 0 = 0 := r0
    unfold ConvPoly.e at this
    rw [h23] at this; exact this
  have hpr1 : (P.v (a + 1) - P.v a) 1 + (P.v (a + 3) - P.v (a + 2)) 1 = 0 := by
    have : P.e a 1 + P.e (a + 2) 1 = 0 := r1
    unfold ConvPoly.e at this
    rw [h23] at this; exact this
  ext j
  fin_cases j
  · simp at hpr0 ⊢; linarith
  · simp at hpr1 ⊢; linarith

end Erdos634.Draft.LaczFormal.RG
