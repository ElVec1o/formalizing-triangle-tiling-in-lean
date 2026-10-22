-- Draft/LaczFormalGraphArc.lean -- D5 (part 2): partial angle sums of a chain of sectors.
-- `chain_rot`: if `u_{j+1} ~ v_j` (positive multiples), then `u_m = r * exp(i * sum_{j<m} wd(u_j,v_j)) * u_0` (complex numbers) with `r > 0`.
-- `opp_sum`: if moreover `u_m` is a negative multiple of `u_0` and `0 < sum < 2 pi`, the sum equals `pi` (an opposite ray is exactly `pi` away).  UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Lemma 8.1 proof: "the angle between h_i and h_j equals pi").
import Erdos634.Draft.LaczFormalGraphFan

open scoped Classical

namespace Erdos634.Draft.LaczFormal.Graph

def cx (u : V2) : ℂ := ⟨u.1, u.2⟩

theorem cx_ne_zero {u : V2} (h : u ≠ 0) : cx u ≠ 0 := by
  intro h0
  apply h
  have h1 := congrArg Complex.re h0
  have h2 := congrArg Complex.im h0
  simp [cx] at h1 h2
  exact Prod.ext h1 h2

theorem chain_rot (u v : ℕ → V2) (hu : ∀ j, u j ≠ 0) (hpar : ∀ j, Par (u (j + 1)) (v j)) (m : ℕ) :
    ∃ r : ℝ, 0 < r ∧ cx (u m) = (r : ℂ) * Complex.exp (((∑ j ∈ Finset.range m, wd (u j) (v j) : ℝ) : ℂ) * Complex.I) * cx (u 0) := by
  induction m with
  | zero => exact ⟨1, one_pos, by simp⟩
  | succ m ih =>
    obtain ⟨r, hr, hrm⟩ := ih
    obtain ⟨c, hc, hcv⟩ := (hpar m).smul
    set W : ℂ := ⟨dt (u m) (v m), crs (u m) (v m)⟩ with hW
    have hUm := cx_ne_zero (hu m)
    have hnm : ‖cx (u m)‖ ^ 2 = (u m).1 ^ 2 + (u m).2 ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp [cx]; ring
    have hnpos : 0 < ‖cx (u m)‖ ^ 2 := pow_pos (norm_pos_iff.mpr hUm) 2
    obtain ⟨Nm, hNm⟩ : ∃ Nm : ℝ, Nm = ‖cx (u m)‖ ^ 2 := ⟨_, rfl⟩
    rw [← hNm] at hnpos hnm
    -- U(m+1) * Nm = c * W * U m
    have hstep : cx (u (m + 1)) * (Nm : ℂ) = (c : ℂ) * W * cx (u m) := by
      have h1 := congrArg Prod.fst hcv
      have h2 := congrArg Prod.snd hcv
      simp only at h1 h2
      apply Complex.ext
      · simp [Complex.mul_re, Complex.mul_im, cx, hW, dt, crs]
        rw [hnm]; first | ring1 | linear_combination ((u m).1 ^ 2 + (u m).2 ^ 2) * h1
      · simp [Complex.mul_re, Complex.mul_im, cx, hW, dt, crs]
        rw [hnm]; first | ring1 | linear_combination ((u m).1 ^ 2 + (u m).2 ^ 2) * h2
    have hWne : W ≠ 0 := by
      intro h0
      have h1 := congrArg Complex.re h0
      have h2 := congrArg Complex.im h0
      simp [hW] at h1 h2
      exact hu m (eq_zero_of_crs_dt (hpar m).ne_right h2 h1)
    have hWpos' : 0 < ‖W‖ := norm_pos_iff.mpr hWne
    obtain ⟨nW, hnW⟩ : ∃ x : ℝ, x = ‖W‖ := ⟨_, rfl⟩
    have hWpos : 0 < nW := by rw [hnW]; exact hWpos'
    have hWexp : W = (nW : ℂ) * Complex.exp ((wd (u m) (v m) : ℂ) * Complex.I) := by
      rw [hnW]
      have := Complex.norm_mul_exp_arg_mul_I W
      exact this.symm
    refine ⟨c * nW * r / Nm, by positivity, ?_⟩
    have hNc : (Nm : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
    have e1 : cx (u (m + 1)) = (c : ℂ) * W * cx (u m) / (Nm : ℂ) := by
      rw [← hstep]; field_simp
    rw [e1, hWexp, hrm, Finset.sum_range_succ]
    push_cast
    rw [add_mul, Complex.exp_add]
    field_simp

theorem opp_sum (u v : ℕ → V2) (hu : ∀ j, u j ≠ 0) (hpar : ∀ j, Par (u (j + 1)) (v j)) (m : ℕ)
    (hopp : ∃ t : ℝ, 0 < t ∧ u m = (-(t * (u 0).1), -(t * (u 0).2)))
    (hpos : 0 < ∑ j ∈ Finset.range m, wd (u j) (v j)) (hlt : ∑ j ∈ Finset.range m, wd (u j) (v j) < 2 * Real.pi) :
    ∑ j ∈ Finset.range m, wd (u j) (v j) = Real.pi := by
  obtain ⟨r, hr, hrm⟩ := chain_rot u v hu hpar m
  obtain ⟨t, ht, hut⟩ := hopp
  set S := ∑ j ∈ Finset.range m, wd (u j) (v j) with hS
  have hU0 := cx_ne_zero (hu 0)
  have h1 : (r : ℂ) * Complex.exp ((S : ℂ) * Complex.I) * cx (u 0) = (-(t : ℂ)) * cx (u 0) := by
    rw [← hrm]
    apply Complex.ext <;> simp [cx, hut]
  have h2 : (r : ℂ) * Complex.exp ((S : ℂ) * Complex.I) = -(t : ℂ) := mul_right_cancel₀ hU0 h1
  have hre := congrArg Complex.re h2
  have him := congrArg Complex.im h2
  rw [Complex.exp_mul_I] at hre him
  simp [← Complex.ofReal_cos, ← Complex.ofReal_sin] at hre him
  have hsin : Real.sin S = 0 := by
    have : r * Real.sin S = 0 := by simpa using him
    exact (mul_eq_zero.mp this).resolve_left hr.ne'
  have hcos : Real.cos S = -1 := by
    have h3 := Real.sin_sq_add_cos_sq S
    rw [hsin] at h3
    have hc2 : Real.cos S ^ 2 = 1 := by linarith
    have hneg : Real.cos S ≤ 0 := by
      have : r * Real.cos S = -t := by simpa using hre
      by_contra hpos'
      push_neg at hpos'
      nlinarith [mul_pos hr hpos']
    nlinarith [sq_nonneg (Real.cos S + 1)]
  -- cos S = -1 with 0 < S < 2 pi gives S = pi
  by_cases hle : S ≤ Real.pi
  · have hm1 : S ∈ Set.Icc 0 Real.pi := ⟨hpos.le, hle⟩
    have hm2 : Real.pi ∈ Set.Icc 0 Real.pi := ⟨Real.pi_pos.le, le_rfl⟩
    exact Real.injOn_cos hm1 hm2 (by rw [hcos, Real.cos_pi])
  · push_neg at hle
    have hc : Real.cos (2 * Real.pi - S) = -1 := by rw [Real.cos_two_pi_sub]; exact hcos
    have hm1 : 2 * Real.pi - S ∈ Set.Icc 0 Real.pi := ⟨by linarith, by linarith⟩
    have hm2 : Real.pi ∈ Set.Icc 0 Real.pi := ⟨Real.pi_pos.le, le_rfl⟩
    have := Real.injOn_cos hm1 hm2 (by rw [hc, Real.cos_pi])
    linarith

end Erdos634.Draft.LaczFormal.Graph
