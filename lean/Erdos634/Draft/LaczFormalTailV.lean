-- Draft/LaczFormalTailV.lean -- Laczkovich 1995, proof of Thm 5.3, case (v) (pp. 93-94), ALGEBRAIC CORE.
-- Case (v): tile angles (pi/10, 3pi/10, 6pi/10), target (3pi/10, 3pi/10, 4pi/10).  With a = sin(pi/10) = (sqrt5-1)/4, b = sin(3pi/10) =
-- (sqrt5+1)/4, c = sin(6pi/10) (c^2 = (5+sqrt5)/8, c NOT in Q(sqrt5)), the area identity and the side words of the target give,
-- for a scale rho > 0 and natural numbers N > 0, x,y,z,u,v,w:
--     rho^2 b = N a,    rho b = x a + y b + z c,    rho c = u a + v b + w c.
-- The paper derives a contradiction in Q(sqrt5); here is that contradiction as a theorem (`tail_v_arith`).  Its ROLE: the hypotheses are
-- exactly what a hypothetical congruent dissection of case (v) would supply (the geometric glue -- relabelling, law of sines, area
-- identity `abs_det_target`, side counts `sideCountT_sum` -- is NOT in this file; see PLAN_L9_L7.md); individually the hypotheses
-- are satisfiable (e.g. rho b = x a + y b needs only numbers).  Proof in my own words; credit Laczkovich (1995).  UNAUDITED.
import Mathlib

open scoped Classical

namespace Erdos634.Draft.LaczFormal

theorem not_sq_five : ¬ IsSquare (5 : ℚ) := by
  rintro ⟨r, hr⟩
  have h1 : IsSquare ((5 : ℤ) : ℚ) := ⟨r, by simpa using hr⟩
  rw [Rat.isSquare_intCast_iff] at h1
  obtain ⟨m, hm⟩ := h1
  have : m ≤ 3 := by nlinarith
  have : -3 ≤ m := by nlinarith
  interval_cases m <;> omega

theorem sqrt5_irr : Irrational (Real.sqrt 5) := by
  have h5 : ¬ IsSquare 5 := by
    rintro ⟨m, hm⟩
    have : m ≤ 2 := by nlinarith
    interval_cases m <;> omega
  have := irrational_sqrt_natCast_iff.mpr h5
  simpa using this

/-- `u + v √5 = 0` with `u, v` rational forces `u = v = 0`. -/
theorem sqrt5_indep {u v : ℝ} (hu : ∃ r : ℚ, u = r) (hv : ∃ r : ℚ, v = r) (h : u + v * Real.sqrt 5 = 0) :
    u = 0 ∧ v = 0 := by
  obtain ⟨ru, rfl⟩ := hu
  obtain ⟨rv, rfl⟩ := hv
  by_cases hv0 : rv = 0
  · subst hv0; simp at h; simp [h]
  · exfalso
    apply sqrt5_irr
    refine ⟨-ru / rv, ?_⟩
    have : (rv : ℝ) ≠ 0 := by exact_mod_cast hv0
    push_cast
    field_simp
    linarith

theorem c_not_in_Q5 {c : ℝ} (hc2 : c ^ 2 = (5 + Real.sqrt 5) / 8) (p q : ℚ) :
    c ≠ p + q * Real.sqrt 5 := by
  intro hc
  have s2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h : ((p : ℝ) ^ 2 + 5 * q ^ 2 - 5 / 8) + (2 * p * q - 1 / 8) * Real.sqrt 5 = 0 := by
    have := hc2; rw [hc] at this
    nlinarith [s2]
  obtain ⟨h1, h2⟩ := sqrt5_indep ⟨p ^ 2 + 5 * q ^ 2 - 5 / 8, by push_cast; ring⟩
    ⟨2 * p * q - 1 / 8, by push_cast; ring⟩ h
  have e1 : (p : ℚ) ^ 2 + 5 * q ^ 2 = 5 / 8 := by
    have : ((p ^ 2 + 5 * q ^ 2 : ℚ) : ℝ) = ((5 / 8 : ℚ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have e2 : (p : ℚ) * q = 1 / 16 := by
    have : ((p * q : ℚ) : ℝ) = ((1 / 16 : ℚ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  apply not_sq_five
  refine ⟨4 * (p ^ 2 - 5 * q ^ 2), ?_⟩
  have : (p ^ 2 - 5 * q ^ 2) ^ 2 = (p ^ 2 + 5 * q ^ 2) ^ 2 - 20 * (p * q) ^ 2 := by ring
  rw [e1, e2] at this
  nlinarith [this]

/-- If `(p3 + q3 √5) c = p2 + q2 √5` (rationals) and `c ∉ ℚ(√5)` then `p3 = q3 = 0`. -/
theorem lin_c {c : ℝ} (hc2 : c ^ 2 = (5 + Real.sqrt 5) / 8) {p2 q2 p3 q3 : ℚ}
    (h : ((p3 : ℝ) + q3 * Real.sqrt 5) * c = p2 + q2 * Real.sqrt 5) : p3 = 0 ∧ q3 = 0 := by
  have s2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  by_contra hne
  have hnorm : p3 ^ 2 - 5 * q3 ^ 2 ≠ 0 := by
    intro h0
    apply hne
    by_cases hq : q3 = 0
    · subst hq
      have : p3 ^ 2 = 0 := by linarith
      exact ⟨pow_eq_zero_iff (two_ne_zero) |>.mp this, rfl⟩
    · exfalso
      apply sqrt5_irr
      -- √5 = |p3 / q3|
      have hq' : (q3 : ℝ) ≠ 0 := by exact_mod_cast hq
      have h5 : (p3 / q3 : ℝ) ^ 2 = 5 := by
        have : ((p3 ^ 2 - 5 * q3 ^ 2 : ℚ) : ℝ) = 0 := by rw [h0]; simp
        push_cast at this
        field_simp; linarith
      have hs : Real.sqrt 5 = |(p3 : ℝ) / q3| := by
        rw [← h5, Real.sqrt_sq_eq_abs]
      exact ⟨|p3 / q3|, by rw [hs]; push_cast; rfl⟩
  apply c_not_in_Q5 hc2 ((p2 * p3 - 5 * q2 * q3) / (p3 ^ 2 - 5 * q3 ^ 2))
    ((q2 * p3 - p2 * q3) / (p3 ^ 2 - 5 * q3 ^ 2))
  have hne3 : ((p3 : ℝ) ^ 2 - 5 * q3 ^ 2) ≠ 0 := by exact_mod_cast hnorm
  have hcexp : c * ((p3 : ℝ) ^ 2 - 5 * q3 ^ 2) = ((p2 : ℝ) * p3 - 5 * q2 * q3) + ((q2 : ℝ) * p3 - p2 * q3) * Real.sqrt 5 := by
    have key : ((p3 : ℝ) ^ 2 - 5 * q3 ^ 2) * c
        = ((p3 : ℝ) - q3 * Real.sqrt 5) * (((p3 : ℝ) + q3 * Real.sqrt 5) * c) := by
      linear_combination ((q3 : ℝ) ^ 2 * c) * s2
    rw [mul_comm, key, h]
    linear_combination (-(q2 : ℝ) * q3) * s2
  push_cast
  field_simp
  linear_combination hcexp

set_option maxHeartbeats 1600000 in
/-- **Tail (v), algebraic core.** -/
theorem tail_v_arith {N x y z u v w : ℕ} {ρ c : ℝ} (hN : 0 < N) (hρ : 0 < ρ) (hc : 0 < c)
    (hc2 : c ^ 2 = (5 + Real.sqrt 5) / 8)
    (h0 : ρ ^ 2 * ((Real.sqrt 5 + 1) / 4) = N * ((Real.sqrt 5 - 1) / 4))
    (h1 : ρ * ((Real.sqrt 5 + 1) / 4) = x * ((Real.sqrt 5 - 1) / 4) + y * ((Real.sqrt 5 + 1) / 4) + z * c)
    (h2 : ρ * c = u * ((Real.sqrt 5 - 1) / 4) + v * ((Real.sqrt 5 + 1) / 4) + w * c) : False := by
  have s2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  set s := Real.sqrt 5 with hsd
  set p1 : ℚ := ((y : ℚ) - x) / 4 with hp1
  set q1 : ℚ := ((x : ℚ) + y) / 4 with hq1
  have hP : (x : ℝ) * ((s - 1) / 4) + y * ((s + 1) / 4) = p1 + q1 * s := by
    rw [hp1, hq1]; push_cast; ring
  have hsq : (p1 + q1 * s) ^ 2 + 2 * (p1 + q1 * s) * z * c + (z : ℝ) ^ 2 * c ^ 2 = N / 4 := by
    have e : (ρ * ((s + 1) / 4)) ^ 2 = ((p1 + q1 * s) + z * c) ^ 2 := by
      rw [h1, show (x : ℝ) * ((s - 1) / 4) + y * ((s + 1) / 4) + z * c = ((p1 + q1 * s) + z * c) by
        rw [← hP]]
    have e2 : (ρ * ((s + 1) / 4)) ^ 2 = N / 4 := by
      have : (ρ * ((s + 1) / 4)) ^ 2 = ρ ^ 2 * ((s + 1) / 4) * ((s + 1) / 4) := by ring
      rw [this, h0]; linear_combination ((N : ℝ) / 16) * s2
    have := e.symm.trans e2
    linear_combination this
  -- (2 z p1 + 2 z q1 s) c = rational + rational s
  have hlin : (((2 * z * p1 : ℚ) : ℝ) + ((2 * z * q1 : ℚ) : ℝ) * s) * c =
      (((N : ℚ) / 4 - p1 ^ 2 - 5 * q1 ^ 2 - 5 * z ^ 2 / 8 : ℚ) : ℝ) +
        (((-(2 * p1 * q1) - z ^ 2 / 8 : ℚ)) : ℝ) * s := by
    push_cast
    have := hsq; rw [hc2] at this
    linear_combination this + (-(q1 : ℝ) ^ 2) * s2 * 1
  obtain ⟨hA, hB⟩ := lin_c hc2 hlin
  have hxy : (z : ℚ) = 0 ∨ (p1 = 0 ∧ q1 = 0) := by
    by_cases hz : (z : ℚ) = 0
    · left; exact hz
    · right
      constructor
      · have : (2 * z : ℚ) * p1 = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · exfalso; apply hz; linarith
        · exact h
      · have : (2 * z : ℚ) * q1 = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · exfalso; apply hz; linarith
        · exact h
  rcases hxy with hz | ⟨hp0, hq0⟩
  · -- z = 0
    have hz' : (z : ℝ) = 0 := by exact_mod_cast hz
    rw [hz'] at hsq
    -- (p1 + q1 s)^2 = N/4  =>  p1 q1 = 0
    have hsq2 : ((p1 ^ 2 + 5 * q1 ^ 2 - N / 4 : ℚ) : ℝ) + ((2 * p1 * q1 : ℚ) : ℝ) * s = 0 := by
      push_cast; linear_combination hsq - (q1 : ℝ) ^ 2 * s2
    obtain ⟨-, hpq⟩ := sqrt5_indep ⟨_, rfl⟩ ⟨_, rfl⟩ hsq2
    have hpq' : p1 * q1 = 0 := by
      have : ((2 * p1 * q1 : ℚ) : ℝ) = 0 := hpq
      have : (2 * p1 * q1 : ℚ) = 0 := by exact_mod_cast this
      linarith
    have hx0 : (x : ℚ) + y ≠ 0 := by
      intro h
      have hx : x = 0 := by have : (x : ℚ) = 0 := by have := (Nat.cast_nonneg (α := ℚ) x); have := (Nat.cast_nonneg (α := ℚ) y); linarith
                            exact_mod_cast this
      have hy : y = 0 := by have : (y : ℚ) = 0 := by have := (Nat.cast_nonneg (α := ℚ) x); have := (Nat.cast_nonneg (α := ℚ) y); linarith
                            exact_mod_cast this
      subst hx; subst hy
      -- then z = 0 gives N/4 = 0
      have : (N : ℝ) / 4 = 0 := by rw [← hsq]; simp [hp1, hq1]
      have : (0 : ℝ) < N := by exact_mod_cast hN
      linarith
    have hq1ne : q1 ≠ 0 := by rw [hq1]; intro h; apply hx0; linarith
    have hp10 : p1 = 0 := by
      rcases mul_eq_zero.mp hpq' with h | h
      · exact h
      · exact absurd h hq1ne
    have hxy : (x : ℚ) = y := by rw [hp1] at hp10; linarith
    -- ρ = P / b with P = x s / 2
    have hρ' : ρ * ((s + 1) / 4) = (x : ℝ) * s / 2 := by
      have hp1r : (p1 : ℝ) = 0 := by exact_mod_cast hp10
      have hq1r : (q1 : ℝ) = x / 2 := by
        rw [hq1]; push_cast; have : (y : ℝ) = x := by exact_mod_cast hxy.symm
        rw [this]; ring
      have hPx : (x : ℝ) * ((s - 1) / 4) + y * ((s + 1) / 4) = (x : ℝ) * s / 2 := by
        rw [hP, hp1r, hq1r]; ring
      rw [h1, hz', zero_mul, add_zero]; exact hPx
    have hρx : ρ = (x : ℝ) * (5 - s) / 2 := by
      have hb : (s + 1) / 4 ≠ 0 := by positivity
      have : ρ = (x : ℝ) * s / 2 / ((s + 1) / 4) := by rw [← hρ']; field_simp
      rw [this]
      field_simp
      nlinarith [s2]
    -- eq2: (ρ - w) c = u a + v b
    have hlin2 : ((( (5 * (x : ℚ) / 2 - w : ℚ) : ℝ)) + (((-(x : ℚ) / 2 : ℚ)) : ℝ) * s) * c =
        (((-(u : ℚ) / 4 + v / 4 : ℚ)) : ℝ) + (((u : ℚ) / 4 + v / 4 : ℚ) : ℝ) * s := by
      push_cast
      have := h2; rw [hρx] at this
      linear_combination this
    obtain ⟨-, hxq⟩ := lin_c hc2 hlin2
    have hx00 : (x : ℚ) = 0 := by linarith
    have : (x : ℚ) + y = 0 := by rw [← hxy]; linarith
    exact hx0 this
  · -- p1 = q1 = 0 : x = y = 0, then z^2 c^2 = N/4
    have hsq0 : (z : ℝ) ^ 2 * c ^ 2 = N / 4 := by
      have hp0' : (p1 : ℝ) = 0 := by exact_mod_cast hp0
      have hq0' : (q1 : ℝ) = 0 := by exact_mod_cast hq0
      rw [hp0', hq0'] at hsq; linarith
    rw [hc2] at hsq0
    have hz2 : ((((5 : ℚ) * z ^ 2 / 8 - N / 4 : ℚ)) : ℝ) + (((z : ℚ) ^ 2 / 8 : ℚ) : ℝ) * s = 0 := by
      push_cast; linarith
    obtain ⟨-, hzz⟩ := sqrt5_indep ⟨_, rfl⟩ ⟨_, rfl⟩ hz2
    have : (z : ℝ) ^ 2 = 0 := by
      have : (((z : ℚ) ^ 2 / 8 : ℚ) : ℝ) = 0 := hzz
      push_cast at this; linarith
    have hz0 : (z : ℝ) = 0 := by exact pow_eq_zero_iff (two_ne_zero) |>.mp this
    rw [hz0] at hsq0
    have : (0 : ℝ) < N := by exact_mod_cast hN
    linarith

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.tail_v_arith
