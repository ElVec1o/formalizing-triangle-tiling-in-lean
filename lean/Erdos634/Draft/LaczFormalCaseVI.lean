-- Draft/LaczFormalCaseVI.lean -- ALGEBRAIC CORE of case (vi) of Laczkovich 1995 Thm 5.1/5.3 (p. 92, "similar arguments" in the paper):
-- congruent tiles with angles (pi/10, 2pi/10, 7pi/10) cannot dissect a triangle with angles (pi/10, pi/10, 8pi/10).
-- With A = sin(pi/10) = (sqrt5-1)/4, C = sin(7pi/10) = (sqrt5+1)/4, b = sin(2pi/10) (b^2 = (5-sqrt5)/8, b not in Q(sqrt5)), the area identity and
-- the side words of the target give, for rho > 0 and naturals N > 0, x, y, z, u, v, w:
--     rho^2 A = N C,   rho A = x A + y b + z C,   rho b = u A + v b + w C.
-- `vi_arith` shows these are inconsistent (my own argument: the only way out is irrational N or a rational b^2).  UNAUDITED.  Credit: Laczkovich (1995).
import Erdos634.Draft.LaczFormalTailV
import Erdos634.Draft.LaczFormalTailIV
import Erdos634.Draft.LaczFormalL9Wit

open scoped Classical

namespace Erdos634.Draft.LaczFormal

/-- `b = sin(π/5)` is not in `ℚ(√5)`: a rational-linear relation `(p3+q3√5) b = p2+q2√5` forces `p3 = q3 = 0`. -/
theorem lin_b {b : ℝ} (hb2 : b ^ 2 = (5 - Real.sqrt 5) / 8) (hb : 0 < b) {p2 q2 p3 q3 : ℚ}
    (h : ((p3 : ℝ) + q3 * Real.sqrt 5) * b = p2 + q2 * Real.sqrt 5) : p3 = 0 ∧ q3 = 0 := by
  have s2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  set s := Real.sqrt 5 with hs
  set c := (1 + s) / 2 * b with hc
  have hc2 : c ^ 2 = (5 + s) / 8 := by
    rw [hc, mul_pow, hb2]; nlinarith [s2]
  refine lin_c (c := c) hc2 (p2 := (p2 + 5 * q2) / 2) (q2 := (p2 + q2) / 2) (p3 := p3) (q3 := q3) ?_
  rw [hc]
  push_cast
  linear_combination ((1 + s) / 2) * h + (((q2 : ℝ)) / 2) * s2


/-- Elements of `ℚ(√5)` inside `ℝ`. -/
def InQ5 (r : ℝ) : Prop := ∃ p q : ℚ, r = p + q * Real.sqrt 5

theorem inq5_add {a b : ℝ} (ha : InQ5 a) (hb : InQ5 b) : InQ5 (a + b) := by
  obtain ⟨p, q, rfl⟩ := ha; obtain ⟨p', q', rfl⟩ := hb
  exact ⟨p + p', q + q', by push_cast; ring⟩

theorem inq5_sub {a b : ℝ} (ha : InQ5 a) (hb : InQ5 b) : InQ5 (a - b) := by
  obtain ⟨p, q, rfl⟩ := ha; obtain ⟨p', q', rfl⟩ := hb
  exact ⟨p - p', q - q', by push_cast; ring⟩

theorem inq5_mul {a b : ℝ} (ha : InQ5 a) (hb : InQ5 b) : InQ5 (a * b) := by
  obtain ⟨p, q, rfl⟩ := ha; obtain ⟨p', q', rfl⟩ := hb
  have s2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  exact ⟨p * p' + 5 * q * q', p * q' + q * p', by push_cast; linear_combination (q * q' : ℝ) * s2⟩

theorem inq5_nat (n : ℕ) : InQ5 (n : ℝ) := ⟨n, 0, by simp⟩
theorem inq5_s : InQ5 (Real.sqrt 5) := ⟨0, 1, by simp⟩
theorem inq5_rat (r : ℚ) : InQ5 (r : ℝ) := ⟨r, 0, by simp⟩

theorem inq5_div {a d : ℝ} (ha : InQ5 a) (hd : InQ5 d) (hne : d ≠ 0) : InQ5 (a / d) := by
  obtain ⟨p, q, rfl⟩ := ha; obtain ⟨p', q', hd'⟩ := hd
  have s2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hnorm : (p' ^ 2 - 5 * q' ^ 2 : ℚ) ≠ 0 := by
    intro h0
    apply hne
    by_cases hq : q' = 0
    · subst hq; have : p' ^ 2 = 0 := by linarith
      have : p' = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp this
      rw [hd', this]; simp
    · exfalso; apply sqrt5_irr
      have hq' : (q' : ℝ) ≠ 0 := by exact_mod_cast hq
      have h5 : (p' / q' : ℝ) ^ 2 = 5 := by
        have : ((p' ^ 2 - 5 * q' ^ 2 : ℚ) : ℝ) = 0 := by rw [h0]; simp
        push_cast at this; field_simp; linarith
      have hs : Real.sqrt 5 = |(p' : ℝ) / q'| := by rw [← h5, Real.sqrt_sq_eq_abs]
      exact ⟨|p' / q'|, by rw [hs]; push_cast; rfl⟩
  have hn' : ((p' : ℝ) ^ 2 - 5 * q' ^ 2) ≠ 0 := by exact_mod_cast hnorm
  refine ⟨(p * p' - 5 * q * q') / (p' ^ 2 - 5 * q' ^ 2), (q * p' - p * q') / (p' ^ 2 - 5 * q' ^ 2), ?_⟩
  have hden : (p' : ℝ) + q' * Real.sqrt 5 ≠ 0 := by rw [← hd']; exact hne
  rw [hd', div_eq_iff hden]
  push_cast
  field_simp
  linear_combination ((p : ℝ) * q' ^ 2 - (q : ℝ) * p' * q') * s2

end Erdos634.Draft.LaczFormal

namespace Erdos634.Draft.LaczFormal

set_option maxHeartbeats 3200000 in
/-- **Case (vi), algebraic core.** -/
theorem vi_arith {N x y z u v w : ℕ} {ρ b : ℝ} (hN : 0 < N) (hρ : 0 < ρ) (hb : 0 < b)
    (hb2 : b ^ 2 = (5 - Real.sqrt 5) / 8)
    (h0 : ρ ^ 2 * ((Real.sqrt 5 - 1) / 4) = N * ((Real.sqrt 5 + 1) / 4))
    (h1 : ρ * ((Real.sqrt 5 - 1) / 4) =
      x * ((Real.sqrt 5 - 1) / 4) + y * b + z * ((Real.sqrt 5 + 1) / 4))
    (h2 : ρ * b = u * ((Real.sqrt 5 - 1) / 4) + v * b + w * ((Real.sqrt 5 + 1) / 4)) : False := by
  have s2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs2 : 2 < Real.sqrt 5 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  set s := Real.sqrt 5 with hs
  have hA : 0 < (s - 1) / 4 := by linarith
  have hC : 0 < (s + 1) / 4 := by linarith
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hy : y = 0
  · -- y = 0 : ρ = x + z (3 + s)/2
    have hy' : (y : ℝ) = 0 := by exact_mod_cast hy
    rw [hy', zero_mul, add_zero] at h1
    have hρe : ρ = x + z * ((3 + s) / 2) := by
      apply mul_left_cancel₀ hA.ne'
      linear_combination h1 - ((z : ℝ) / 8) * s2
    have hlin : (((x : ℚ) - v + 3 * z / 2 : ℚ) + (((z : ℚ) / 2 : ℚ) : ℝ) * s) * b =
        (((w : ℚ) - u) / 4 : ℚ) + ((((u : ℚ) + w) / 4 : ℚ) : ℝ) * s := by
      push_cast
      rw [hρe] at h2
      linear_combination h2
    obtain ⟨hp3, hq3⟩ := lin_b hb2 hb hlin
    have hz0 : (z : ℚ) = 0 := by linarith
    have hxv : (x : ℚ) = v := by rw [hz0] at hp3; linarith
    have hzR : (z : ℝ) = 0 := by exact_mod_cast hz0
    have hρx : ρ = x := by rw [hρe, hzR]; ring
    have hx2 : (x : ℝ) ^ 2 * ((s - 1) / 4) = N * ((s + 1) / 4) := by rw [← hρx]; exact h0
    have h5 : ((((-(x : ℚ) ^ 2 - N) / 4 : ℚ)) : ℝ) + ((((x : ℚ) ^ 2 - N) / 4 : ℚ) : ℝ) * s = 0 := by
      push_cast; linear_combination hx2
    obtain ⟨h5a, -⟩ := sqrt5_indep ⟨_, rfl⟩ ⟨_, rfl⟩ h5
    have : (((-(x : ℚ) ^ 2 - N) / 4 : ℚ) : ℝ) = 0 := h5a
    have h6 : (-(x : ℚ) ^ 2 - N) / 4 = 0 := by exact_mod_cast this
    have : (0 : ℚ) < N := by exact_mod_cast hN
    nlinarith [sq_nonneg (x : ℚ)]
  · have hyR : (0 : ℝ) < y := by exact_mod_cast Nat.pos_of_ne_zero hy
    have hQ5A : InQ5 ((s - 1) / 4) := ⟨-1 / 4, 1 / 4, by push_cast; ring⟩
    have hQ5C : InQ5 ((s + 1) / 4) := ⟨1 / 4, 1 / 4, by push_cast; ring⟩
    set Q : ℝ := x * ((s - 1) / 4) + z * ((s + 1) / 4) with hQ
    set R : ℝ := u * ((s - 1) / 4) + w * ((s + 1) / 4) with hR
    have hkey : (Q + v * ((s - 1) / 4)) * ρ = N * ((s + 1) / 4) + v * Q - y * R := by
      linear_combination (-(ρ - v)) * h1 - (y : ℝ) * h2 + h0
    by_cases hall : x = 0 ∧ z = 0 ∧ v = 0
    · obtain ⟨hx, hz, hv⟩ := hall
      have hx' : (x : ℝ) = 0 := by exact_mod_cast hx
      have hz' : (z : ℝ) = 0 := by exact_mod_cast hz
      have hv' : (v : ℝ) = 0 := by exact_mod_cast hv
      have hQ0 : Q = 0 := by rw [hQ, hx', hz']; ring
      have hyb : (y : ℝ) * b = ρ * ((s - 1) / 4) := by
        rw [hx', hz'] at h1; linear_combination -h1
      -- y R = N C
      have hyR2 : (y : ℝ) * R = N * ((s + 1) / 4) := by
        have e2 : ρ * b = R := by rw [hv'] at h2; linear_combination h2
        calc (y : ℝ) * R = ρ * ((y : ℝ) * b) := by rw [← e2]; ring
          _ = ρ * (ρ * ((s - 1) / 4)) := by rw [hyb]
          _ = N * ((s + 1) / 4) := by linear_combination h0
      have h7 : ((((-(y : ℚ) * u + y * w - N) / 4 : ℚ)) : ℝ) +
          ((((y : ℚ) * u + y * w - N) / 4 : ℚ) : ℝ) * s = 0 := by
        push_cast; rw [hR] at hyR2; linear_combination hyR2
      obtain ⟨h7a, h7b⟩ := sqrt5_indep ⟨_, rfl⟩ ⟨_, rfl⟩ h7
      have e7a : (((-(y : ℚ) * u + y * w - N) / 4 : ℚ) : ℝ) = 0 := h7a
      have e7b : ((((y : ℚ) * u + y * w - N) / 4 : ℚ) : ℝ) = 0 := h7b
      have q7a : (-(y : ℚ) * u + y * w - N) / 4 = 0 := by exact_mod_cast e7a
      have q7b : ((y : ℚ) * u + y * w - N) / 4 = 0 := by exact_mod_cast e7b
      -- b^2 = ρ^2 A^2 / y^2 = N/(4 y^2)  (u = 0 not needed): b^2 rational
      have hb2' : b ^ 2 = (N : ℝ) / (4 * (y : ℝ) ^ 2) := by
        have : ((y : ℝ) * b) ^ 2 = (ρ * ((s - 1) / 4)) ^ 2 := by rw [hyb]
        have hh : (ρ * ((s - 1) / 4)) ^ 2 = (N : ℝ) / 4 := by
          have : (ρ * ((s - 1) / 4)) ^ 2 = ρ ^ 2 * ((s - 1) / 4) * ((s - 1) / 4) := by ring
          rw [this, h0]; linear_combination ((N : ℝ) / 16) * s2
        field_simp
        nlinarith [this, hh]
      have h8 : ((((5 : ℚ) - 2 * N / (y : ℚ) ^ 2) : ℚ) : ℝ) = Real.sqrt 5 := by
        push_cast
        have : (5 - s) / 8 = (N : ℝ) / (4 * (y : ℝ) ^ 2) := by rw [← hb2, hb2']
        field_simp at this ⊢
        linarith
      exact sqrt5_irr ⟨_, h8⟩
    · -- (Q + v A) > 0, so ρ ∈ ℚ(√5), hence b ∈ ℚ(√5)
      have hD : 0 < Q + v * ((s - 1) / 4) := by
        by_contra hle
        push Not at hle
        have t1 : (0 : ℝ) ≤ x * ((s - 1) / 4) := by positivity
        have t2 : (0 : ℝ) ≤ z * ((s + 1) / 4) := by positivity
        have t3 : (0 : ℝ) ≤ v * ((s - 1) / 4) := by positivity
        have e1 : (x : ℝ) * ((s - 1) / 4) = 0 := by rw [hQ] at hle; linarith
        have e2 : (z : ℝ) * ((s + 1) / 4) = 0 := by rw [hQ] at hle; linarith
        have e3 : (v : ℝ) * ((s - 1) / 4) = 0 := by rw [hQ] at hle; linarith
        apply hall
        refine ⟨?_, ?_, ?_⟩
        · have := (mul_eq_zero.mp e1).resolve_right hA.ne'; exact_mod_cast this
        · have := (mul_eq_zero.mp e2).resolve_right hC.ne'; exact_mod_cast this
        · have := (mul_eq_zero.mp e3).resolve_right hA.ne'; exact_mod_cast this
      have hQ5 : InQ5 Q := inq5_add (inq5_mul (inq5_nat x) hQ5A) (inq5_mul (inq5_nat z) hQ5C)
      have hR5 : InQ5 R := inq5_add (inq5_mul (inq5_nat u) hQ5A) (inq5_mul (inq5_nat w) hQ5C)
      have hD5 : InQ5 (Q + v * ((s - 1) / 4)) := inq5_add hQ5 (inq5_mul (inq5_nat v) hQ5A)
      have hnum5 : InQ5 (N * ((s + 1) / 4) + v * Q - y * R) :=
        inq5_sub (inq5_add (inq5_mul (inq5_nat N) hQ5C) (inq5_mul (inq5_nat v) hQ5)) (inq5_mul (inq5_nat y) hR5)
      have hρ5 : InQ5 ρ := by
        have : ρ = (N * ((s + 1) / 4) + v * Q - y * R) / (Q + v * ((s - 1) / 4)) := by
          rw [eq_div_iff hD.ne']; linarith [hkey]
        rw [this]; exact inq5_div hnum5 hD5 hD.ne'
      have hyb5 : InQ5 ((y : ℝ) * b) := by
        have : (y : ℝ) * b = ρ * ((s - 1) / 4) - Q := by rw [hQ]; linarith [h1]
        rw [this]; exact inq5_sub (inq5_mul hρ5 hQ5A) hQ5
      obtain ⟨p, q, hpq⟩ := hyb5
      have hlin : (((y : ℚ) : ℝ) + (((0 : ℚ)) : ℝ) * s) * b = (p : ℝ) + q * s := by
        push_cast; linarith [hpq]
      obtain ⟨hy0, -⟩ := lin_b hb2 hb hlin
      exact hy (by exact_mod_cast hy0)

end Erdos634.Draft.LaczFormal

namespace Erdos634.Draft.LaczFormal

open Real Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional

set_option maxHeartbeats 3200000 in
/-- **Case (vi).**  No congruent dissection has a tile with angles `(π/10, 2π/10, 7π/10)` and a target with angles `(π/10, π/10, 8π/10)`. -/
theorem case_vi {N : ℕ} (D : CongruentDissection N)
    (hM : TileAngles D (π / 10) (2 * π / 10) (7 * π / 10))
    (hT : TgtAngles D (π / 10) (π / 10) (8 * π / 10)) : False := by
  obtain ⟨σm, m0, m1, m2⟩ := hM
  obtain ⟨σt, t0, t1, t2⟩ := hT
  let D' : CongruentDissection N :=
    { toDissection := Erdos634.NormalPosition.relabelTarget D.toDissection σt
      model := D.model.relabel σm
      tiles_congruent := fun i => (D.tiles_congruent i).relabel σm }
  have hTa := Row2.angleAt_comp D.target D'.target σt (fun k => rfl)
  have hMa := Row2.angleAt_comp D.model D'.model σm (fun k => rfl)
  have a0 : D'.model.angleAt 0 = π / 10 := by rw [(hMa 0).1]; exact m0
  have a1 : D'.model.angleAt 1 = 2 * π / 10 := by rw [(hMa 1).1]; exact m1
  have a2 : D'.model.angleAt 2 = 7 * π / 10 := by rw [(hMa 2).1]; exact m2
  have b0 : D'.target.angleAt 0 = π / 10 := by rw [(hTa 0).1]; exact t0
  have b1 : D'.target.angleAt 1 = π / 10 := by rw [(hTa 1).1]; exact t1
  have b2 : D'.target.angleAt 2 = 8 * π / 10 := by rw [(hTa 2).1]; exact t2
  have hpi := Real.pi_pos
  have s5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs5 : 2 < Real.sqrt 5 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have sa : Real.sin (π / 10) = (Real.sqrt 5 - 1) / 4 := by
    rw [← Real.cos_pi_div_two_sub, show π / 2 - π / 10 = 2 * π / 5 by ring]; exact cos_two_pi_div_five
  have sC : Real.sin (7 * π / 10) = (Real.sqrt 5 + 1) / 4 := by
    rw [show 7 * π / 10 = π - 3 * π / 10 by ring, Real.sin_pi_sub,
      ← Real.cos_pi_div_two_sub, show π / 2 - 3 * π / 10 = π / 5 by ring, Real.cos_pi_div_five]; ring
  set bb := Real.sin (2 * π / 10) with hbb
  have s8 : Real.sin (8 * π / 10) = bb := by
    rw [hbb, show 8 * π / 10 = π - 2 * π / 10 by ring, Real.sin_pi_sub]
  have hbpos : 0 < bb := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  have hb2 : bb ^ 2 = (5 - Real.sqrt 5) / 8 := by
    have h1 := Real.sin_sq_add_cos_sq (2 * π / 10)
    have h2 : Real.cos (2 * π / 10) = (1 + Real.sqrt 5) / 4 := by
      rw [show 2 * π / 10 = π / 5 by ring]; exact Real.cos_pi_div_five
    rw [h2] at h1; rw [hbb]; nlinarith [s5]
  have hapos : 0 < (Real.sqrt 5 - 1) / 4 := by linarith
  have hCpos : 0 < (Real.sqrt 5 + 1) / 4 := by linarith
  set A := (Real.sqrt 5 - 1) / 4 with hA
  set C := (Real.sqrt 5 + 1) / 4 with hC
  have hv0 := D'.model.oppLen_pos 0
  have hw0 := D'.target.oppLen_pos 0
  set t := D'.model.oppLen 0 / A with ht
  have htpos : 0 < t := div_pos hv0 hapos
  have v0e : D'.model.oppLen 0 = t * A := by rw [ht]; field_simp
  have v1e : D'.model.oppLen 1 = t * bb := by
    have h := D'.model.lawSin 0 1
    rw [a0, a1, sa, v0e] at h
    apply mul_left_cancel₀ hapos.ne'
    linarith
  have v2e : D'.model.oppLen 2 = t * C := by
    have h := D'.model.lawSin 0 2
    rw [a0, a2, sa, sC, v0e] at h
    apply mul_left_cancel₀ hapos.ne'
    linarith
  set s := D'.target.oppLen 0 / A with hs
  have hspos : 0 < s := div_pos hw0 hapos
  have w0e : D'.target.oppLen 0 = s * A := by rw [hs]; field_simp
  have w1e : D'.target.oppLen 1 = s * A := by
    have h := D'.target.lawSin 0 1
    rw [b0, b1] at h
    have hsin : 0 < Real.sin (π / 10) := by rw [sa]; exact hapos
    have := mul_left_cancel₀ hsin.ne' (by linarith : Real.sin (π / 10) * D'.target.oppLen 1 =
      Real.sin (π / 10) * D'.target.oppLen 0)
    rw [this, w0e]
  have w2e : D'.target.oppLen 2 = s * bb := by
    have h := D'.target.lawSin 0 2
    rw [b0, b2, sa, s8] at h
    apply mul_left_cancel₀ hapos.ne'
    rw [w0e] at h
    linarith
  have harea := Row3.RP.abs_det_target D'
  rw [Row3.RP.abs_det_eq, Row3.RP.abs_det_eq, b0, a0, sa, w1e, w2e, v1e, v2e] at harea
  set ρ := s / t with hρ
  have hρpos : 0 < ρ := div_pos hspos htpos
  have hN0 : 0 < N := D'.pos
  have h0 : ρ ^ 2 * A = N * C := by
    have key : s ^ 2 * A = N * t ^ 2 * C := by
      have hAb : 0 < A * bb := mul_pos hapos hbpos
      apply mul_left_cancel₀ hAb.ne'
      linear_combination harea
    rw [hρ]; field_simp; linear_combination key
  have r0 := D'.sideCountT_sum 0
  have r2 := D'.sideCountT_sum 2
  rw [Fin.sum_univ_three, v0e, v1e, v2e, w0e] at r0
  rw [Fin.sum_univ_three, v0e, v1e, v2e, w2e] at r2
  have et : t * ρ = s := by rw [hρ]; field_simp
  have h1 : ρ * A = (D'.sideCountT 0 0 : ℝ) * A + (D'.sideCountT 0 1 : ℝ) * bb + (D'.sideCountT 0 2 : ℝ) * C := by
    have : t * (ρ * A) = t * ((D'.sideCountT 0 0 : ℝ) * A + (D'.sideCountT 0 1 : ℝ) * bb + (D'.sideCountT 0 2 : ℝ) * C) := by
      linear_combination A * et + (-1 : ℝ) * r0
    exact mul_left_cancel₀ htpos.ne' this
  have h2 : ρ * bb = (D'.sideCountT 2 0 : ℝ) * A + (D'.sideCountT 2 1 : ℝ) * bb + (D'.sideCountT 2 2 : ℝ) * C := by
    have : t * (ρ * bb) = t * ((D'.sideCountT 2 0 : ℝ) * A + (D'.sideCountT 2 1 : ℝ) * bb + (D'.sideCountT 2 2 : ℝ) * C) := by
      linear_combination bb * et + (-1 : ℝ) * r2
    exact mul_left_cancel₀ htpos.ne' this
  exact vi_arith hN0 hρpos hbpos hb2 h0 h1 h2

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.vi_arith
#print axioms Erdos634.Draft.LaczFormal.case_vi

namespace Erdos634.Draft.LaczFormal

open Real Erdos634.Geometry Erdos634.TilePlacement Erdos634.Subdivision Erdos634.Draft.TheoremPConditional

/-- Ladder (scale 2) dissection of any triangle with prescribed angles `α, β` : the model has angles `(α, β, π-α-β)`, and so has the target. -/
theorem ladder_with_angles {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hs : α + β < π) :
    ∃ (N : ℕ) (D : CongruentDissection N), TileAngles D α β (π - α - β) ∧
      TgtAngles D α β (π - α - β) := by
  obtain ⟨T, h0, h1⟩ := exists_tri_angles hα hβ hs
  have h2 : T.angleAt 2 = π - α - β := by
    have := angleAt_sum T; rw [h0, h1] at this; linarith
  have hpts : (![T.pts 0, T.pts 1, T.pts 2] : Fin 3 → Plane) = T.pts := by
    funext i; fin_cases i <;> rfl
  have hind : AffineIndependent ℝ ![T.pts 0, T.pts 1, T.pts 2] := by rw [hpts]; exact T.indep
  set Tm : Tri := ⟨![T.pts 0, T.pts 1, T.pts 2], hind⟩ with hTm
  have hang : ∀ k, Tm.angleAt k = T.angleAt k := by
    intro k
    have : Tm.pts = T.pts := hpts
    simp only [Tri.angleAt, this]
  let D : CongruentDissection (2 * 2) :=
    { toDissection := ladderDissection (T.pts 0) (T.pts 1) (T.pts 2) hind 2 (by norm_num)
      model := Tm
      tiles_congruent := fun n =>
        (ladderDissection_congruent (T.pts 0) (T.pts 1) (T.pts 2) hind 2 (by norm_num) n).symm }
  refine ⟨_, D, ⟨1, ?_, ?_, ?_⟩, ⟨1, ?_, ?_, ?_⟩⟩
  · show Tm.angleAt 0 = _; rw [hang]; exact h0
  · show Tm.angleAt 1 = _; rw [hang]; exact h1
  · show Tm.angleAt 2 = _; rw [hang]; exact h2
  · show (bigTri (T.pts 0) (T.pts 1) (T.pts 2) hind 2 (by norm_num)).angleAt 0 = _
    rw [bigTri_angleAt]; exact h0
  · show (bigTri (T.pts 0) (T.pts 1) (T.pts 2) hind 2 (by norm_num)).angleAt 1 = _
    rw [bigTri_angleAt]; exact h1
  · show (bigTri (T.pts 0) (T.pts 1) (T.pts 2) hind 2 (by norm_num)).angleAt 2 = _
    rw [bigTri_angleAt]; exact h2

/-- Each hypothesis of `case_vi` is satisfiable on its own (a tile with these angles dissects a similar triangle; the isosceles
`(π/10, π/10, 8π/10)` triangle is dissected by its own ladder); `case_vi` says they are incompatible. -/
theorem case_vi_hyps_individually :
    (∃ (N : ℕ) (D : CongruentDissection N), TileAngles D (π / 10) (2 * π / 10) (7 * π / 10)) ∧
    (∃ (N : ℕ) (D : CongruentDissection N), TgtAngles D (π / 10) (π / 10) (8 * π / 10)) := by
  have hpi := Real.pi_pos
  refine ⟨?_, ?_⟩
  · obtain ⟨N, D, h, -⟩ := ladder_with_angles (α := π / 10) (β := 2 * π / 10) (by positivity)
      (by positivity) (by linarith)
    exact ⟨N, D, by simpa [show π - π / 10 - 2 * π / 10 = 7 * π / 10 by ring] using h⟩
  · obtain ⟨N, D, -, h⟩ := ladder_with_angles (α := π / 10) (β := π / 10) (by positivity)
      (by positivity) (by linarith)
    exact ⟨N, D, by simpa [show π - π / 10 - π / 10 = 8 * π / 10 by ring] using h⟩

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.case_vi_hyps_individually
