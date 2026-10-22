-- Draft/LaczFormalRG4Geo.lean -- Case IV: plane geometry of the polygon.  (i) for a strictly convex polygon, the cross and the inner product of consecutive edges at the vertex `v_i` are
-- `|e||e'| sin(angle)` and `-|e||e'| cos(angle)`; (ii) a convex quadrilateral with angles `pi/3, 2pi/3, pi/3, 2pi/3` (cyclically) is a parallelogram; (iii) rotation of the polygon indexing.
-- UNAUDITED.  Credit: classical plane geometry; the project's `abs_cross2` (Thm21Area).
import Erdos634.Draft.LaczFormalRG4AngleSum
import Erdos634.Draft.LaczFormalThm21Loc

open scoped Classical
open Erdos634.Geometry Erdos634.Draft.LaczFormal.Thm21

namespace Erdos634.Draft.LaczFormal.RG

variable {M : ℕ} [NeZero M]

/-- **Cross and inner product of consecutive edges** (strictly convex polygon): at the vertex `v_i`, `cross(e_{i-1}, e_i) = |e_{i-1}||e_i| sin(angle_i)` and `<e_{i-1}, e_i> = -|e_{i-1}||e_i| cos(angle_i)`. -/
theorem turn_of_angle (P : ConvPoly M) (i : Fin M) :
    cross2 (P.e (i - 1)) (P.e i) = ‖P.e (i - 1)‖ * ‖P.e i‖ * Real.sin (P.angle i) ∧
    inner ℝ (P.e (i - 1)) (P.e i) = - (‖P.e (i - 1)‖ * ‖P.e i‖ * Real.cos (P.angle i)) := by
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := ConvPoly.fin_facts P.three_le i
  have hpos : 0 < cross2 (P.e (i - 1)) (P.e i) := by
    have := P.left (i - 1) (i + 1) (by intro h; exact f4 h) (by rw [f5]; exact f1)
    have e1 : P.v (i - 1 + 1) - P.v (i - 1) = P.e (i - 1) := rfl
    have e2 : P.v (i + 1) - P.v (i - 1) = P.e (i - 1) + P.e i := by
      unfold ConvPoly.e; rw [f5]; abel
    rw [e1, e2, cross2_add_right, cross2_self] at this
    simpa using this
  have ha : P.v (i - 1) - P.v i = - P.e (i - 1) := by
    unfold ConvPoly.e; rw [f5]; abel
  have hc : P.v (i + 1) - P.v i = P.e i := rfl
  unfold ConvPoly.angle cornerAngle EuclideanGeometry.angle
  simp only [vsub_eq_sub]
  rw [ha, hc]
  have h1 := abs_cross2 (- P.e (i - 1)) (P.e i)
  have h2 := InnerProductGeometry.cos_angle_mul_norm_mul_norm (- P.e (i - 1)) (P.e i)
  rw [norm_neg] at h1 h2
  have hcr : cross2 (- P.e (i - 1)) (P.e i) = - cross2 (P.e (i - 1)) (P.e i) := by
    have := cross2_smul_left (-1 : ℝ) (P.e (i - 1)) (P.e i)
    simp only [neg_smul, one_smul] at this
    rw [this]; ring
  rw [hcr, abs_neg, abs_of_pos hpos] at h1
  refine ⟨h1, ?_⟩
  have hin : inner ℝ (- P.e (i - 1)) (P.e i) = - inner ℝ (P.e (i - 1)) (P.e i) := by simp
  rw [hin] at h2
  linarith

/-- **Algebra of the `60°, 120°, 60°, 120°` quadrilateral**: four vectors summing to zero whose consecutive pairs have (inner, cross) equal to
`(n n'/2, (√3/2) n n')`, `(-n n'/2, (√3/2) n n')`, `(n n'/2, (√3/2) n n')`, `(-n n'/2, (√3/2) n n')` satisfy `p + r = 0` (and hence `q + s = 0`). -/
theorem quad_alg (p0 p1 q0 q1 r0 r1 s0 s1 np nq nr ns : ℝ) (hnp : 0 < np) (hnq : 0 < nq) (hnr : 0 < nr) (hns : 0 < ns)
    (hp : np ^ 2 = p0 ^ 2 + p1 ^ 2)
    (hq : nq ^ 2 = q0 ^ 2 + q1 ^ 2) (hr : nr ^ 2 = r0 ^ 2 + r1 ^ 2)
    (c1 : p0 * q0 + p1 * q1 = np * nq / 2) (d1 : p0 * q1 - p1 * q0 = (Real.sqrt 3 / 2) * np * nq)
    (c2 : q0 * r0 + q1 * r1 = -(nq * nr / 2)) (d2 : q0 * r1 - q1 * r0 = (Real.sqrt 3 / 2) * nq * nr)
    (c3 : r0 * s0 + r1 * s1 = nr * ns / 2) (d3 : r0 * s1 - r1 * s0 = (Real.sqrt 3 / 2) * nr * ns)
    (hz0 : p0 + q0 + r0 + s0 = 0) (hz1 : p1 + q1 + r1 + s1 = 0) : p0 + r0 = 0 ∧ p1 + r1 = 0 := by
  set k := Real.sqrt 3 with hk
  have hk2 : k ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hkpos : 0 < k := Real.sqrt_pos.mpr (by norm_num)
  have Q0 : np * q0 = nq * (p0 / 2 - k / 2 * p1) := by
    have : np * (np * q0 - nq * (p0 / 2 - k / 2 * p1)) = 0 := by
      linear_combination q0 * hp + p0 * c1 - p1 * d1
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hnp.ne'
    · linarith
  have Q1 : np * q1 = nq * (p1 / 2 + k / 2 * p0) := by
    have : np * (np * q1 - nq * (p1 / 2 + k / 2 * p0)) = 0 := by
      linear_combination q1 * hp + p1 * c1 + p0 * d1
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hnp.ne'
    · linarith
  have R0 : nq * r0 = nr * (-q0 / 2 - k / 2 * q1) := by
    have : nq * (nq * r0 - nr * (-q0 / 2 - k / 2 * q1)) = 0 := by
      linear_combination r0 * hq + q0 * c2 - q1 * d2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hnq.ne'
    · linarith
  have R1 : nq * r1 = nr * (-q1 / 2 + k / 2 * q0) := by
    have : nq * (nq * r1 - nr * (-q1 / 2 + k / 2 * q0)) = 0 := by
      linear_combination r1 * hq + q1 * c2 + q0 * d2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hnq.ne'
    · linarith
  have S0 : nr * s0 = ns * (r0 / 2 - k / 2 * r1) := by
    have : nr * (nr * s0 - ns * (r0 / 2 - k / 2 * r1)) = 0 := by
      linear_combination s0 * hr + r0 * c3 - r1 * d3
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hnr.ne'
    · linarith
  have S1 : nr * s1 = ns * (r1 / 2 + k / 2 * r0) := by
    have : nr * (nr * s1 - ns * (r1 / 2 + k / 2 * r0)) = 0 := by
      linear_combination s1 * hr + r1 * c3 + r0 * d3
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hnr.ne'
    · linarith
  -- r in terms of p
  have Rp0 : np * r0 = - nr * p0 := by
    have : nq * (np * r0 + nr * p0) = 0 := by
      linear_combination np * R0 + (-(nr) / 2) * Q0 + (-(nr * k) / 2) * Q1 + (-(nq * nr * p0) / 4) * hk2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hnq.ne'
    · linarith
  have Rp1 : np * r1 = - nr * p1 := by
    have : nq * (np * r1 + nr * p1) = 0 := by
      linear_combination np * R1 + (-(nr) / 2) * Q1 + (nr * k / 2) * Q0 + (-(nq * nr * p1) / 4) * hk2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hnq.ne'
    · linarith
  have Sp0 : np * s0 = ns * (-p0 / 2 + k / 2 * p1) := by
    have : nr * (np * s0 - ns * (-p0 / 2 + k / 2 * p1)) = 0 := by
      linear_combination np * S0 + (ns / 2) * Rp0 + (-(ns * k) / 2) * Rp1
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hnr.ne'
    · linarith
  have Sp1 : np * s1 = ns * (-p1 / 2 - k / 2 * p0) := by
    have : nr * (np * s1 - ns * (-p1 / 2 - k / 2 * p0)) = 0 := by
      linear_combination np * S1 + (ns / 2) * Rp1 + (ns * k / 2) * Rp0
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hnr.ne'
    · linarith
  have E0 : (np - nr) * p0 + (nq - ns) * (p0 / 2 - k / 2 * p1) = 0 := by
    linear_combination np * hz0 - Q0 - Rp0 - Sp0
  have E1 : (np - nr) * p1 + (nq - ns) * (p1 / 2 + k / 2 * p0) = 0 := by
    linear_combination np * hz1 - Q1 - Rp1 - Sp1
  have hY : (nq - ns) * (k / 2 * np ^ 2) = 0 := by
    linear_combination (-1 : ℝ) * (p1 * E0 - p0 * E1) + (nq - ns) * (k / 2) * hp * 1 - (nq - ns) * (k / 2) * (np ^ 2 - (p0 ^ 2 + p1 ^ 2)) * 0
  have hY' : nq = ns := by
    rcases mul_eq_zero.mp hY with h | h
    · linarith
    · exfalso
      have : 0 < k / 2 * np ^ 2 := by positivity
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

theorem sin_two_pi_div_three : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]

theorem cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]

/-- **A convex quadrilateral with consecutive angles `2π/3, π/3, 2π/3` at `v_{a+1}, v_{a+2}, v_{a+3}` is a parallelogram.** -/
theorem quad_parallelogram (P : ConvPoly 4) (a : Fin 4) (h1 : P.angle (a + 1) = 2 * Real.pi / 3) (h2 : P.angle (a + 2) = Real.pi / 3)
    (h3 : P.angle (a + 3) = 2 * Real.pi / 3) : P.v a + P.v (a + 2) = P.v (a + 1) + P.v (a + 3) := by
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
  rw [sin_two_pi_div_three, cos_two_pi_div_three] at t1 t3
  rw [Real.sin_pi_div_three, Real.cos_pi_div_three] at t2
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
  have := quad_alg (P.e a 0) (P.e a 1) (P.e (a + 1) 0) (P.e (a + 1) 1) (P.e (a + 2) 0) (P.e (a + 2) 1) (P.e (a + 3) 0) (P.e (a + 3) 1)
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

/-! ## Rotating the indexing of a polygon -/

/-- The polygon with the vertex labels shifted by `s`: `v'_i = v_{i+s}`. -/
def polyRot (P : ConvPoly M) (s : Fin M) : ConvPoly M where
  v := fun i => P.v (i + s)
  three_le := P.three_le
  left := by
    intro i j hj1 hj2
    have h1 : j + s ≠ i + s := fun h => hj1 (add_right_cancel h)
    have h2 : j + s ≠ (i + s) + 1 := by
      intro h
      apply hj2
      have : j + s = (i + 1) + s := by rw [h]; abel
      exact add_right_cancel this
    have := P.left (i + s) (j + s) h1 h2
    have e : i + 1 + s = i + s + 1 := by abel
    simpa only [e] using this

theorem polyRot_carrier (P : ConvPoly M) (s : Fin M) : (polyRot P s).carrier = P.carrier := by
  ext x
  simp only [ConvPoly.carrier, Set.mem_setOf_eq]
  constructor
  · intro h i
    have := h (i - s)
    have e1 : i - s + 1 + s = i + 1 := by abel
    have e2 : i - s + s = i := by abel
    simpa [polyRot, e1, e2] using this
  · intro h i
    have := h (i + s)
    have e : i + 1 + s = i + s + 1 := by abel
    simpa [polyRot, e] using this

theorem polyRot_angle (P : ConvPoly M) (s i : Fin M) : (polyRot P s).angle i = P.angle (i + s) := by
  unfold ConvPoly.angle
  have e : i - 1 + s = i + s - 1 := by abel
  have e2 : i + 1 + s = i + s + 1 := by abel
  simp only [polyRot, e, e2]

theorem polyRot_side (P : ConvPoly M) (s i : Fin M) : (polyRot P s).side i = P.side (i + s) := by
  unfold ConvPoly.side
  have e2 : i + 1 + s = i + s + 1 := by abel
  simp only [polyRot, e2]


end Erdos634.Draft.LaczFormal.RG
