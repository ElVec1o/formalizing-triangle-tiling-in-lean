-- Draft/R8F3PrimeContradiction.lean — No prime N > 3 admits a CongruentDissection with 2π/3 model
-- and F3PrimeData target (angles β, 2β, 3α; sides νc², νc(2a+b), 3νa(a+b)).
-- This is the a↔b mirror of R8F3Contradiction.
--
-- ZERO sorry.  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).

import Erdos634.Draft.FluxPaper
import Erdos634.Draft.FluxE2Pi3Row8Mirrors
import Erdos634.Draft.FluxE2Pi3Row8Arith
import Erdos634.Draft.R8F3PrimeAreaFormula
import Erdos634.Draft.ThmIsoShBridge

open scoped Classical

namespace Erdos634.Draft.R8F3PrimeContradiction

open Erdos634.Geometry
open Erdos634.Row8Arith
open Erdos634.Draft.R8F3PrimeAreaFormula (F3prime_area_formula)

/-! ## Auxiliary -/

private lemma c_sq (T : Tri) {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
  obtain ⟨σ, -, ha, -, hb, hγ, hc⟩ := h
  have hl := T.lawCos_perm σ
  rw [ha, hb, hc, hγ,
      show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three] at hl
  linarith

-- F3′ factor identities (a↔b of F3)
private lemma F3prime_factor_alpha (ν : ℝ) {a b c : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ν * (c ^ 2 - c * (2 * a + b) - 3 * a * (a + b)) = -(ν * (c + a + 2 * b) * (c + a - b)) := by
  linear_combination 2 * ν * hc2

private lemma F3prime_factor_beta (ν : ℝ) {a b c : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ν * (-(c ^ 2) - c * (2 * a + b) + 3 * a * (a + b)) = ν * (c - a - 2 * b) * (c + b - a) := by
  linear_combination -2 * ν * hc2

/-! ## Core: given integers s = ν(a+2b) > 0 and z = νc > 0, derive False -/

private lemma f3prime_core
    {N : ℕ} (hN : N.Prime) (hN3 : 3 < N)
    {a b c ν : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν) (hcpos : 0 < c)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hNreal : (N : ℝ) = 3 * ν ^ 2 * (a + b) * (2 * a + b))
    (s : ℤ) (hs_pos : 0 < s) (hs_R : (s : ℝ) = ν * (a + 2 * b))
    (z : ℤ) (hz_pos : 0 < z) (hz_R : (z : ℝ) = ν * c) : False := by
  have hA_R : (N : ℝ) + 3 * (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2 =
      6 * ν ^ 2 * (a + b) * (a + 2 * b) := by
    rw [hs_R, hz_R, hNreal]; linear_combination -3 * ν ^ 2 * hc2
  have hB_R : (N : ℝ) + (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2 =
      2 * ν ^ 2 * (2 * a + b) * (a + 2 * b) := by
    rw [hs_R, hz_R, hNreal]; linear_combination -3 * ν ^ 2 * hc2
  have hR_eq : (N : ℝ) * 4 * (s : ℝ) ^ 2 =
      ((N : ℝ) + 3 * (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2) *
      ((N : ℝ) + (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2) := by
    rw [hA_R, hB_R, hNreal, hs_R]; ring
  have hZ_eq : (N : ℤ) * 4 * s ^ 2 =
      ((N : ℤ) + 3 * s ^ 2 - 3 * z ^ 2) * ((N : ℤ) + s ^ 2 - 3 * z ^ 2) := by
    have hRZ : ((N : ℤ) : ℝ) * 4 * (s : ℝ) ^ 2 =
        (((N : ℤ) : ℝ) + 3 * (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2) *
        (((N : ℤ) : ℝ) + (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2) := by
      push_cast; exact hR_eq
    exact_mod_cast hRZ
  set M : ℤ := (N : ℤ) + 2 * s ^ 2 - 3 * z ^ 2 with hM_def
  have hM_sq : M ^ 2 = s ^ 2 * (s ^ 2 + 4 * (N : ℤ)) := by linear_combination -hZ_eq
  have hs_dvd : s ∣ M := by
    have hsq_dvd : s ^ 2 ∣ M ^ 2 := ⟨s ^ 2 + 4 * (N : ℤ), by linarith [hM_sq]⟩
    exact (IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).mp hsq_dvd
  obtain ⟨m, hm⟩ := hs_dvd
  have hm_sq : m ^ 2 = s ^ 2 + 4 * (N : ℤ) := by
    have : s ^ 2 * m ^ 2 = s ^ 2 * (s ^ 2 + 4 * (N : ℤ)) :=
      calc s ^ 2 * m ^ 2 = (s * m) ^ 2 := by ring
        _ = M ^ 2 := by rw [← hm]
        _ = s ^ 2 * (s ^ 2 + 4 * (N : ℤ)) := hM_sq
    exact Int.eq_of_mul_eq_mul_left (pow_ne_zero _ hs_pos.ne') this
  set k : ℤ := m - 2 * s
  have hks : k * s = (N : ℤ) - 3 * z ^ 2 := by
    have h1 : s * m = M := hm.symm ▸ rfl
    have h2 : M = (N : ℤ) + 2 * s ^ 2 - 3 * z ^ 2 := hM_def
    have h3 : m * s = (N : ℤ) + 2 * s ^ 2 - 3 * z ^ 2 := by linarith [mul_comm s m, h1, h2]
    nlinarith [h3]
  have hm_s : m * s = (N : ℤ) - 3 * z ^ 2 + 2 * s ^ 2 := by nlinarith [hks]
  have hk_sq : k ^ 2 = 3 * (4 * z ^ 2 - s ^ 2) := by nlinarith [hm_sq, hm_s]
  have h4z2s2_nn : 0 ≤ 4 * z ^ 2 - s ^ 2 := by
    have hineq : (s : ℝ) ^ 2 < 4 * (z : ℝ) ^ 2 := by
      rw [hs_R, hz_R]
      have : (a + 2 * b) ^ 2 < 4 * c ^ 2 := by nlinarith [hc2, sq_pos_of_pos ha]
      nlinarith [sq_pos_of_pos hν]
    have hZ : (s : ℤ) ^ 2 < 4 * z ^ 2 := by exact_mod_cast hineq
    linarith
  have h3_dvd_k_sq : (3 : ℤ) ∣ k ^ 2 := ⟨4 * z ^ 2 - s ^ 2, by linarith [hk_sq]⟩
  have h3_dvd_k : (3 : ℤ) ∣ k :=
    (by norm_num : Prime (3 : ℤ)).dvd_of_dvd_pow h3_dvd_k_sq
  obtain ⟨j, hj⟩ := h3_dvd_k
  have h3_dvd_N : (3 : ℤ) ∣ (N : ℤ) := by
    use j * s + z ^ 2
    nlinarith [hks, hj]
  have hN3_eq : N = 3 := by
    rcases hN.eq_one_or_self_of_dvd 3 (by exact_mod_cast h3_dvd_N) with h1 | h2
    · norm_num at h1
    · exact h2.symm
  omega

/-! ## Main theorem -/

/-- No prime `N > 3` admits a `CongruentDissection` with a 2π/3 model and an F3PrimeData target. -/
theorem f3prime_contradiction {N : ℕ} (D : CongruentDissection N)
    {α a b c ν : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : D.target.F3PrimeData α a b c ν)
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (hN : N.Prime) (hN3 : 3 < N) : False := by
  obtain ⟨-, hc0, -, -⟩ := cos_alpha_of_TwoPiThree D.model hm
  have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := c_sq D.model hm
  have hcpos : 0 < c := hc0
  have hNreal : (N : ℝ) = 3 * ν ^ 2 * (a + b) * (2 * a + b) :=
    F3prime_area_formula D hm ht ha hb hν
  obtain ⟨Mα, Mβ, hpar_α, hpar_β, hflux_α, hflux_β⟩ := Paper.cor_int D hα hm
  have hW_α := Row8.lemmaW_F3prime_alpha D.target hα ht
  have hW_β := Row8.lemmaW_F3prime_beta D.target hα ht
  have hfact_α := F3prime_factor_alpha ν hc2
  have hfact_β := F3prime_factor_beta ν hc2
  -- Divisors: α-divisor = (c+a-b), β-divisor = (c+b-a)
  have hdiv_α : 0 < c + a - b := divisor_alpha_pos hc2 ha hb hcpos
  have hdiv_β : 0 < c + b - a := divisor_beta_pos hc2 ha hb hcpos
  have hN_odd : ¬ (2 : ℤ) ∣ (N : ℤ) := fun hdvd => by
    have : N = 2 := (hN.eq_one_or_self_of_dvd 2 (by exact_mod_cast hdvd)).resolve_left
      (by omega) |>.symm
    omega
  have hMα_odd : ¬ (2 : ℤ) ∣ Mα := fun h => hN_odd (by
    have := Int.dvd_sub hpar_α h; simp at this; exact this)
  have hMβ_odd : ¬ (2 : ℤ) ∣ Mβ := fun h => hN_odd (by
    have := Int.dvd_sub hpar_β h; simp at this; exact this)
  have hsum_even : (2 : ℤ) ∣ Mα + Mβ := by omega
  have hdiff_even : (2 : ℤ) ∣ Mβ - Mα := by omega
  rcases hW_α with hα_pos | hα_neg <;> rcases hW_β with hβ_pos | hβ_neg
  · -- (++): Mα = -(ν*(c+a+2b)), Mβ = ν*(c-a-2b)
    have hMα_R : (Mα : ℝ) * (c + a - b) = ν * (c ^ 2 - c * (2 * a + b) - 3 * a * (a + b)) :=
      hflux_α.symm.trans hα_pos
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = ν * (-(c ^ 2) - c * (2 * a + b) + 3 * a * (a + b)) :=
      hflux_β.symm.trans hβ_pos
    have hMα_val : (Mα : ℝ) = -(ν * (c + a + 2 * b)) :=
      mul_right_cancel₀ hdiv_α.ne' (by linear_combination hMα_R.trans hfact_α)
    have hMβ_val : (Mβ : ℝ) = ν * (c - a - 2 * b) :=
      mul_right_cancel₀ hdiv_β.ne' (hMβ_R.trans hfact_β)
    -- 2ν(a+2b) = -(Mα+Mβ); 2νc = Mβ-Mα
    have h2s : 2 * (ν * (a + 2 * b)) = -((Mα : ℝ) + Mβ) := by rw [hMα_val, hMβ_val]; ring
    have h2z : 2 * (ν * c) = (Mβ : ℝ) - Mα := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨p, hp⟩ := hsum_even
    obtain ⟨q, hq⟩ := hdiff_even
    have hs_R : (-p : ℝ) = ν * (a + 2 * b) := by
      have : (Mα + Mβ : ℝ) = 2 * p := by exact_mod_cast hp
      linarith [h2s]
    have hz_R : (q : ℝ) = ν * c := by
      have : (Mβ - Mα : ℝ) = 2 * q := by exact_mod_cast hq
      linarith [h2z]
    have hs_pos : 0 < -p := by
      exact_mod_cast (show (0 : ℝ) < -p by rw [hs_R]; exact mul_pos hν (by linarith))
    have hz_pos : 0 < q := by
      exact_mod_cast (show (0 : ℝ) < q by rw [hz_R]; exact mul_pos hν hcpos)
    exact f3prime_core hN hN3 ha hb hν hcpos hc2 hNreal (-p) hs_pos (by exact_mod_cast hs_R)
      q hz_pos (by exact_mod_cast hz_R)
  · -- (+-): Mα = -(ν*(c+a+2b)), Mβ = -(ν*(c-a-2b))
    have hMα_R : (Mα : ℝ) * (c + a - b) = ν * (c ^ 2 - c * (2 * a + b) - 3 * a * (a + b)) :=
      hflux_α.symm.trans hα_pos
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = -(ν * (-(c ^ 2) - c * (2 * a + b) + 3 * a * (a + b))) :=
      hflux_β.symm.trans hβ_neg
    have hMα_val : (Mα : ℝ) = -(ν * (c + a + 2 * b)) :=
      mul_right_cancel₀ hdiv_α.ne' (by linear_combination hMα_R.trans hfact_α)
    have hMβ_val : (Mβ : ℝ) = -(ν * (c - a - 2 * b)) :=
      mul_right_cancel₀ hdiv_β.ne' (hMβ_R.trans (by linear_combination -hfact_β))
    -- 2ν(a+2b) = Mβ-Mα; 2νc = -(Mα+Mβ)
    have h2s : 2 * (ν * (a + 2 * b)) = (Mβ : ℝ) - Mα := by rw [hMα_val, hMβ_val]; ring
    have h2z : 2 * (ν * c) = -((Mα : ℝ) + Mβ) := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨q, hq⟩ := hdiff_even
    obtain ⟨p, hp⟩ := hsum_even
    have hs_R : (q : ℝ) = ν * (a + 2 * b) := by
      have : (Mβ - Mα : ℝ) = 2 * q := by exact_mod_cast hq
      linarith [h2s]
    have hz_R : (-p : ℝ) = ν * c := by
      have : (Mα + Mβ : ℝ) = 2 * p := by exact_mod_cast hp
      linarith [h2z]
    have hs_pos : 0 < q := by
      exact_mod_cast (show (0 : ℝ) < q by rw [hs_R]; exact mul_pos hν (by linarith))
    have hz_pos : 0 < -p := by
      exact_mod_cast (show (0 : ℝ) < -p by rw [hz_R]; exact mul_pos hν hcpos)
    exact f3prime_core hN hN3 ha hb hν hcpos hc2 hNreal q hs_pos (by exact_mod_cast hs_R)
      (-p) hz_pos (by exact_mod_cast hz_R)
  · -- (-+): Mα = ν*(c+a+2b), Mβ = ν*(c-a-2b)
    have hMα_R : (Mα : ℝ) * (c + a - b) = -(ν * (c ^ 2 - c * (2 * a + b) - 3 * a * (a + b))) :=
      hflux_α.symm.trans hα_neg
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = ν * (-(c ^ 2) - c * (2 * a + b) + 3 * a * (a + b)) :=
      hflux_β.symm.trans hβ_pos
    have hMα_val : (Mα : ℝ) = ν * (c + a + 2 * b) :=
      mul_right_cancel₀ hdiv_α.ne' (hMα_R.trans (by linear_combination -hfact_α))
    have hMβ_val : (Mβ : ℝ) = ν * (c - a - 2 * b) :=
      mul_right_cancel₀ hdiv_β.ne' (hMβ_R.trans hfact_β)
    -- 2ν(a+2b) = -(Mβ-Mα); 2νc = Mα+Mβ
    have h2s : 2 * (ν * (a + 2 * b)) = -((Mβ : ℝ) - Mα) := by rw [hMα_val, hMβ_val]; ring
    have h2z : 2 * (ν * c) = (Mα : ℝ) + Mβ := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨q, hq⟩ := hdiff_even
    obtain ⟨p, hp⟩ := hsum_even
    have hs_R : (-q : ℝ) = ν * (a + 2 * b) := by
      have : (Mβ - Mα : ℝ) = 2 * q := by exact_mod_cast hq
      linarith [h2s]
    have hz_R : (p : ℝ) = ν * c := by
      have : (Mα + Mβ : ℝ) = 2 * p := by exact_mod_cast hp
      linarith [h2z]
    have hs_pos : 0 < -q := by
      exact_mod_cast (show (0 : ℝ) < -q by rw [hs_R]; exact mul_pos hν (by linarith))
    have hz_pos : 0 < p := by
      exact_mod_cast (show (0 : ℝ) < p by rw [hz_R]; exact mul_pos hν hcpos)
    exact f3prime_core hN hN3 ha hb hν hcpos hc2 hNreal (-q) hs_pos (by exact_mod_cast hs_R)
      p hz_pos (by exact_mod_cast hz_R)
  · -- (--): Mα = ν*(c+a+2b), Mβ = -(ν*(c-a-2b))
    have hMα_R : (Mα : ℝ) * (c + a - b) = -(ν * (c ^ 2 - c * (2 * a + b) - 3 * a * (a + b))) :=
      hflux_α.symm.trans hα_neg
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = -(ν * (-(c ^ 2) - c * (2 * a + b) + 3 * a * (a + b))) :=
      hflux_β.symm.trans hβ_neg
    have hMα_val : (Mα : ℝ) = ν * (c + a + 2 * b) :=
      mul_right_cancel₀ hdiv_α.ne' (hMα_R.trans (by linear_combination -hfact_α))
    have hMβ_val : (Mβ : ℝ) = -(ν * (c - a - 2 * b)) :=
      mul_right_cancel₀ hdiv_β.ne' (hMβ_R.trans (by linear_combination -hfact_β))
    -- 2ν(a+2b) = Mα+Mβ; 2νc = -(Mβ-Mα)
    have h2s : 2 * (ν * (a + 2 * b)) = (Mα : ℝ) + Mβ := by rw [hMα_val, hMβ_val]; ring
    have h2z : 2 * (ν * c) = -((Mβ : ℝ) - Mα) := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨p, hp⟩ := hsum_even
    obtain ⟨q, hq⟩ := hdiff_even
    have hs_R : (p : ℝ) = ν * (a + 2 * b) := by
      have : (Mα + Mβ : ℝ) = 2 * p := by exact_mod_cast hp
      linarith [h2s]
    have hz_R : (-q : ℝ) = ν * c := by
      have : (Mβ - Mα : ℝ) = 2 * q := by exact_mod_cast hq
      linarith [h2z]
    have hs_pos : 0 < p := by
      exact_mod_cast (show (0 : ℝ) < p by rw [hs_R]; exact mul_pos hν (by linarith))
    have hz_pos : 0 < -q := by
      exact_mod_cast (show (0 : ℝ) < -q by rw [hz_R]; exact mul_pos hν hcpos)
    exact f3prime_core hN hN3 ha hb hν hcpos hc2 hNreal p hs_pos (by exact_mod_cast hs_R)
      (-q) hz_pos (by exact_mod_cast hz_R)

/-! ## N=3 case: algebraic contradiction without N>3 -/

/-- For N=3, F3PrimeData forces ν²·a·(a+2b) = 1−z², but the left side is positive while z≥1
    makes the right side ≤ 0. -/
private lemma f3prime_core_n3
    {a b c ν : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν) (hcpos : 0 < c)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hNreal : (3 : ℝ) = 3 * ν ^ 2 * (a + b) * (2 * a + b))
    (z : ℤ) (hz_pos : 0 < z) (hz_R : (z : ℝ) = ν * c) : False := by
  -- ν²*(a+b)*(2a+b) = 1
  have h1 : ν ^ 2 * (a + b) * (2 * a + b) = 1 := by linarith
  -- ν²*a*(a+2b) = 1 − z²   [since (a+b)(2a+b) − c² = a(a+2b) by hc2]
  have h_key : ν ^ 2 * a * (a + 2 * b) = 1 - (z : ℝ) ^ 2 := by
    have hzc : (z : ℝ) ^ 2 = ν ^ 2 * c ^ 2 := by rw [hz_R]; ring
    rw [hzc, hc2]; nlinarith [h1]
  -- Left side positive
  have h_pos : 0 < ν ^ 2 * a * (a + 2 * b) := by positivity
  -- Right side ≤ 0: z ≥ 1 so z² ≥ 1
  have hz1 : (1 : ℝ) ≤ (z : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz_pos
    nlinarith [sq_nonneg ((z : ℝ) - 1)]
  linarith

/-- Version of `f3prime_core` that works for ALL primes (including N=3). -/
private lemma f3prime_core_any
    {N : ℕ} (hN : N.Prime) (hN2 : N ≠ 2)
    {a b c ν : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν) (hcpos : 0 < c)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hNreal : (N : ℝ) = 3 * ν ^ 2 * (a + b) * (2 * a + b))
    (s : ℤ) (hs_pos : 0 < s) (hs_R : (s : ℝ) = ν * (a + 2 * b))
    (z : ℤ) (hz_pos : 0 < z) (hz_R : (z : ℝ) = ν * c) : False := by
  by_cases hN3 : 3 < N
  · exact f3prime_core hN hN3 ha hb hν hcpos hc2 hNreal s hs_pos hs_R z hz_pos hz_R
  · -- N is prime, N ≠ 2, ¬ 3 < N, so N = 3
    have hN3_eq : N = 3 := by
      have := hN.two_le; have : N ≤ 3 := Nat.not_lt.mp hN3; omega
    subst hN3_eq
    -- hNreal : (3 : ℕ) cast to ℝ = 3*ν²*(a+b)*(2a+b)
    have hNreal3 : (3 : ℝ) = 3 * ν ^ 2 * (a + b) * (2 * a + b) := by exact_mod_cast hNreal
    exact f3prime_core_n3 ha hb hν hcpos hc2 hNreal3 z hz_pos hz_R

/-! ## All-prime contradiction (including N=3) -/

/-- No prime N ≠ 2 admits a CongruentDissection with a 2π/3 model and F3PrimeData target. -/
theorem f3prime_any_prime_contradiction {N : ℕ} (D : CongruentDissection N)
    {α a b c ν : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : D.target.F3PrimeData α a b c ν)
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (hN : N.Prime) (hN2 : N ≠ 2) : False := by
  obtain ⟨-, hc0, -, -⟩ := cos_alpha_of_TwoPiThree D.model hm
  have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := c_sq D.model hm
  have hcpos : 0 < c := hc0
  have hNreal : (N : ℝ) = 3 * ν ^ 2 * (a + b) * (2 * a + b) :=
    F3prime_area_formula D hm ht ha hb hν
  obtain ⟨Mα, Mβ, hpar_α, hpar_β, hflux_α, hflux_β⟩ := Paper.cor_int D hα hm
  have hW_α := Row8.lemmaW_F3prime_alpha D.target hα ht
  have hW_β := Row8.lemmaW_F3prime_beta D.target hα ht
  have hfact_α := F3prime_factor_alpha ν hc2
  have hfact_β := F3prime_factor_beta ν hc2
  have hdiv_α : 0 < c + a - b := divisor_alpha_pos hc2 ha hb hcpos
  have hdiv_β : 0 < c + b - a := divisor_beta_pos hc2 ha hb hcpos
  have hN_odd : ¬ (2 : ℤ) ∣ (N : ℤ) := fun hdvd => by
    have : N = 2 := (hN.eq_one_or_self_of_dvd 2 (by exact_mod_cast hdvd)).resolve_left
      (by omega) |>.symm
    exact hN2 this
  have hMα_odd : ¬ (2 : ℤ) ∣ Mα := fun h => hN_odd (by
    have := Int.dvd_sub hpar_α h; simp at this; exact this)
  have hMβ_odd : ¬ (2 : ℤ) ∣ Mβ := fun h => hN_odd (by
    have := Int.dvd_sub hpar_β h; simp at this; exact this)
  have hsum_even : (2 : ℤ) ∣ Mα + Mβ := by omega
  have hdiff_even : (2 : ℤ) ∣ Mβ - Mα := by omega
  rcases hW_α with hα_pos | hα_neg <;> rcases hW_β with hβ_pos | hβ_neg
  · -- (++): Mα = -(ν*(c+a+2b)), Mβ = ν*(c-a-2b)
    have hMα_R : (Mα : ℝ) * (c + a - b) = ν * (c ^ 2 - c * (2 * a + b) - 3 * a * (a + b)) :=
      hflux_α.symm.trans hα_pos
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = ν * (-(c ^ 2) - c * (2 * a + b) + 3 * a * (a + b)) :=
      hflux_β.symm.trans hβ_pos
    have hMα_val : (Mα : ℝ) = -(ν * (c + a + 2 * b)) :=
      mul_right_cancel₀ hdiv_α.ne' (by linear_combination hMα_R.trans hfact_α)
    have hMβ_val : (Mβ : ℝ) = ν * (c - a - 2 * b) :=
      mul_right_cancel₀ hdiv_β.ne' (hMβ_R.trans hfact_β)
    have h2s : 2 * (ν * (a + 2 * b)) = -((Mα : ℝ) + Mβ) := by rw [hMα_val, hMβ_val]; ring
    have h2z : 2 * (ν * c) = (Mβ : ℝ) - Mα := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨p, hp⟩ := hsum_even
    obtain ⟨q, hq⟩ := hdiff_even
    have hs_R : (-p : ℝ) = ν * (a + 2 * b) := by
      have : (Mα + Mβ : ℝ) = 2 * p := by exact_mod_cast hp
      linarith [h2s]
    have hz_R : (q : ℝ) = ν * c := by
      have : (Mβ - Mα : ℝ) = 2 * q := by exact_mod_cast hq
      linarith [h2z]
    have hs_pos : 0 < -p := by
      exact_mod_cast (show (0 : ℝ) < -p by rw [hs_R]; exact mul_pos hν (by linarith))
    have hz_pos : 0 < q := by
      exact_mod_cast (show (0 : ℝ) < q by rw [hz_R]; exact mul_pos hν hcpos)
    exact f3prime_core_any hN hN2 ha hb hν hcpos hc2 hNreal (-p) hs_pos
      (by exact_mod_cast hs_R) q hz_pos (by exact_mod_cast hz_R)
  · -- (+-): Mα = -(ν*(c+a+2b)), Mβ = -(ν*(c-a-2b))
    have hMα_R : (Mα : ℝ) * (c + a - b) = ν * (c ^ 2 - c * (2 * a + b) - 3 * a * (a + b)) :=
      hflux_α.symm.trans hα_pos
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = -(ν * (-(c ^ 2) - c * (2 * a + b) + 3 * a * (a + b))) :=
      hflux_β.symm.trans hβ_neg
    have hMα_val : (Mα : ℝ) = -(ν * (c + a + 2 * b)) :=
      mul_right_cancel₀ hdiv_α.ne' (by linear_combination hMα_R.trans hfact_α)
    have hMβ_val : (Mβ : ℝ) = -(ν * (c - a - 2 * b)) :=
      mul_right_cancel₀ hdiv_β.ne' (hMβ_R.trans (by linear_combination -hfact_β))
    have h2s : 2 * (ν * (a + 2 * b)) = (Mβ : ℝ) - Mα := by rw [hMα_val, hMβ_val]; ring
    have h2z : 2 * (ν * c) = -((Mα : ℝ) + Mβ) := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨q, hq⟩ := hdiff_even
    obtain ⟨p, hp⟩ := hsum_even
    have hs_R : (q : ℝ) = ν * (a + 2 * b) := by
      have : (Mβ - Mα : ℝ) = 2 * q := by exact_mod_cast hq
      linarith [h2s]
    have hz_R : (-p : ℝ) = ν * c := by
      have : (Mα + Mβ : ℝ) = 2 * p := by exact_mod_cast hp
      linarith [h2z]
    have hs_pos : 0 < q := by
      exact_mod_cast (show (0 : ℝ) < q by rw [hs_R]; exact mul_pos hν (by linarith))
    have hz_pos : 0 < -p := by
      exact_mod_cast (show (0 : ℝ) < -p by rw [hz_R]; exact mul_pos hν hcpos)
    exact f3prime_core_any hN hN2 ha hb hν hcpos hc2 hNreal q hs_pos
      (by exact_mod_cast hs_R) (-p) hz_pos (by exact_mod_cast hz_R)
  · -- (-+): Mα = ν*(c+a+2b), Mβ = ν*(c-a-2b)
    have hMα_R : (Mα : ℝ) * (c + a - b) = -(ν * (c ^ 2 - c * (2 * a + b) - 3 * a * (a + b))) :=
      hflux_α.symm.trans hα_neg
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = ν * (-(c ^ 2) - c * (2 * a + b) + 3 * a * (a + b)) :=
      hflux_β.symm.trans hβ_pos
    have hMα_val : (Mα : ℝ) = ν * (c + a + 2 * b) :=
      mul_right_cancel₀ hdiv_α.ne' (hMα_R.trans (by linear_combination -hfact_α))
    have hMβ_val : (Mβ : ℝ) = ν * (c - a - 2 * b) :=
      mul_right_cancel₀ hdiv_β.ne' (hMβ_R.trans hfact_β)
    have h2s : 2 * (ν * (a + 2 * b)) = -((Mβ : ℝ) - Mα) := by rw [hMα_val, hMβ_val]; ring
    have h2z : 2 * (ν * c) = (Mα : ℝ) + Mβ := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨q, hq⟩ := hdiff_even
    obtain ⟨p, hp⟩ := hsum_even
    have hs_R : (-q : ℝ) = ν * (a + 2 * b) := by
      have : (Mβ - Mα : ℝ) = 2 * q := by exact_mod_cast hq
      linarith [h2s]
    have hz_R : (p : ℝ) = ν * c := by
      have : (Mα + Mβ : ℝ) = 2 * p := by exact_mod_cast hp
      linarith [h2z]
    have hs_pos : 0 < -q := by
      exact_mod_cast (show (0 : ℝ) < -q by rw [hs_R]; exact mul_pos hν (by linarith))
    have hz_pos : 0 < p := by
      exact_mod_cast (show (0 : ℝ) < p by rw [hz_R]; exact mul_pos hν hcpos)
    exact f3prime_core_any hN hN2 ha hb hν hcpos hc2 hNreal (-q) hs_pos
      (by exact_mod_cast hs_R) p hz_pos (by exact_mod_cast hz_R)
  · -- (--): Mα = ν*(c+a+2b), Mβ = -(ν*(c-a-2b))
    have hMα_R : (Mα : ℝ) * (c + a - b) = -(ν * (c ^ 2 - c * (2 * a + b) - 3 * a * (a + b))) :=
      hflux_α.symm.trans hα_neg
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = -(ν * (-(c ^ 2) - c * (2 * a + b) + 3 * a * (a + b))) :=
      hflux_β.symm.trans hβ_neg
    have hMα_val : (Mα : ℝ) = ν * (c + a + 2 * b) :=
      mul_right_cancel₀ hdiv_α.ne' (hMα_R.trans (by linear_combination -hfact_α))
    have hMβ_val : (Mβ : ℝ) = -(ν * (c - a - 2 * b)) :=
      mul_right_cancel₀ hdiv_β.ne' (hMβ_R.trans (by linear_combination -hfact_β))
    have h2s : 2 * (ν * (a + 2 * b)) = (Mα : ℝ) + Mβ := by rw [hMα_val, hMβ_val]; ring
    have h2z : 2 * (ν * c) = -((Mβ : ℝ) - Mα) := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨p, hp⟩ := hsum_even
    obtain ⟨q, hq⟩ := hdiff_even
    have hs_R : (p : ℝ) = ν * (a + 2 * b) := by
      have : (Mα + Mβ : ℝ) = 2 * p := by exact_mod_cast hp
      linarith [h2s]
    have hz_R : (-q : ℝ) = ν * c := by
      have : (Mβ - Mα : ℝ) = 2 * q := by exact_mod_cast hq
      linarith [h2z]
    have hs_pos : 0 < p := by
      exact_mod_cast (show (0 : ℝ) < p by rw [hs_R]; exact mul_pos hν (by linarith))
    have hz_pos : 0 < -q := by
      exact_mod_cast (show (0 : ℝ) < -q by rw [hz_R]; exact mul_pos hν hcpos)
    exact f3prime_core_any hN hN2 ha hb hν hcpos hc2 hNreal p hs_pos
      (by exact_mod_cast hs_R) (-q) hz_pos (by exact_mod_cast hz_R)

#check @f3prime_contradiction
#check @f3prime_any_prime_contradiction

end Erdos634.Draft.R8F3PrimeContradiction
