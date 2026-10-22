-- Draft/R8F3Contradiction.lean — No prime N > 3 admits a CongruentDissection with 2π/3 model
-- and F3Data target (angles α, 2α, 3β; sides νc², νc(a+2b), 3νb(a+b)).
--
-- Proof route (PROOF_row8.md §3, F3 case):
--   1. cor_int  →  Mα, Mβ ∈ ℤ with Mα ≡ Mβ ≡ N (mod 2)
--   2. lemmaW_F3_alpha/beta + F3_factor_alpha/beta (under hc2)
--      →  Mα = ±ν(c−2a−b),  Mβ = ∓ν(c+2a+b)
--   3. Parity: N prime > 3 → N odd → Mα, Mβ odd → in all 4 sign cases,
--      s := ν(2a+b) ∈ ℤ > 0;  z := νc ∈ ℤ > 0
--   4. F3_area_formula  →  (N:ℝ) = 3·ν²·(a+b)·(a+2b)
--   5. Integer identity  →  N·4s² = (N+3s²−3z²)·(N+s²−3z²)  (under c²=a²+ab+b²)
--   6. M := N+2s²−3z²; M² = s²(s²+4N); s | M; m := M/s;
--      k := m−2s; k² = 3(4z²−s²) → 3|k → 3|N → N=3, contradicts N>3.
--
-- ZERO sorry.  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).

import Erdos634.Draft.FluxPaper
import Erdos634.Draft.FluxE2Pi3Row8F3
import Erdos634.Draft.FluxE2Pi3Row8Arith
import Erdos634.Draft.R8F3AreaFormula
import Erdos634.Draft.ThmIsoShBridge

open scoped Classical

namespace Erdos634.Draft.R8N15F3

open Erdos634.Geometry
open Erdos634.Row8Arith
open Erdos634.Draft.R8F3AreaFormula (F3_area_formula)

/-! ## Auxiliary -/

private lemma c_sq (T : Tri) {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
  obtain ⟨σ, -, ha, -, hb, hγ, hc⟩ := h
  have hl := T.lawCos_perm σ
  rw [ha, hb, hc, hγ,
      show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three] at hl
  linarith

-- F3 factor identities
private lemma F3_factor_alpha (ν : ℝ) {a b c : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ν * (-(c ^ 2) - c * (a + 2 * b) + 3 * b * (a + b)) = ν * (c - 2 * a - b) * (c + a - b) := by
  linear_combination -2 * ν * hc2

private lemma F3_factor_beta (ν : ℝ) {a b c : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ν * (c ^ 2 - c * (a + 2 * b) - 3 * b * (a + b)) = -(ν * (c + 2 * a + b) * (c + b - a)) := by
  linear_combination 2 * ν * hc2

/-! ## Core: given integers s = ν(2a+b) > 0 and z = νc > 0, derive False -/

private lemma f3_core
    {N : ℕ} (hN15 : N = 15)
    {a b c ν : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hNreal : (N : ℝ) = 3 * ν ^ 2 * (a + b) * (a + 2 * b))
    (s : ℤ) (hs_pos : 0 < s) (hs_R : (s : ℝ) = ν * (2 * a + b))
    (z : ℤ) (hz_pos : 0 < z) (hz_R : (z : ℝ) = ν * c) : False := by
  -- Establish the key ℝ identities for the two factors
  have hA_R : (N : ℝ) + 3 * (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2 =
      6 * ν ^ 2 * (a + b) * (2 * a + b) := by
    rw [hs_R, hz_R, hNreal]; linear_combination -3 * ν ^ 2 * hc2
  have hB_R : (N : ℝ) + (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2 =
      2 * ν ^ 2 * (2 * a + b) * (a + 2 * b) := by
    rw [hs_R, hz_R, hNreal]; linear_combination -3 * ν ^ 2 * hc2
  -- The ℝ identity: N·4s² = (N+3s²−3z²)·(N+s²−3z²)
  have hR_eq : (N : ℝ) * 4 * (s : ℝ) ^ 2 =
      ((N : ℝ) + 3 * (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2) *
      ((N : ℝ) + (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2) := by
    rw [hA_R, hB_R, hNreal, hs_R]; ring
  -- Cast to ℤ
  have hZ_eq : (N : ℤ) * 4 * s ^ 2 =
      ((N : ℤ) + 3 * s ^ 2 - 3 * z ^ 2) * ((N : ℤ) + s ^ 2 - 3 * z ^ 2) := by
    have hRZ : ((N : ℤ) : ℝ) * 4 * (s : ℝ) ^ 2 =
        (((N : ℤ) : ℝ) + 3 * (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2) *
        (((N : ℤ) : ℝ) + (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2) := by
      push_cast; exact hR_eq
    exact_mod_cast hRZ
  -- Define M = N+2s²−3z², show M² = s²(s²+4N)
  set M : ℤ := (N : ℤ) + 2 * s ^ 2 - 3 * z ^ 2 with hM_def
  have hM_sq : M ^ 2 = s ^ 2 * (s ^ 2 + 4 * (N : ℤ)) := by linear_combination -hZ_eq
  -- s | M (from s² | M²)
  have hs_dvd : s ∣ M := by
    have hsq_dvd : s ^ 2 ∣ M ^ 2 := ⟨s ^ 2 + 4 * (N : ℤ), by linarith [hM_sq]⟩
    exact (IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).mp hsq_dvd
  -- Set m = M/s, derive m² = s²+4N
  obtain ⟨m, hm⟩ := hs_dvd   -- M = s * m
  have hm_sq : m ^ 2 = s ^ 2 + 4 * (N : ℤ) := by
    have : s ^ 2 * m ^ 2 = s ^ 2 * (s ^ 2 + 4 * (N : ℤ)) :=
      calc s ^ 2 * m ^ 2 = (s * m) ^ 2 := by ring
        _ = M ^ 2 := by rw [← hm]
        _ = s ^ 2 * (s ^ 2 + 4 * (N : ℤ)) := hM_sq
    exact Int.eq_of_mul_eq_mul_left (pow_ne_zero _ hs_pos.ne') this
  -- Set k = m − 2s; compute k·s = N − 3z²
  set k : ℤ := m - 2 * s
  have hks : k * s = (N : ℤ) - 3 * z ^ 2 := by
    have h1 : s * m = M := hm.symm ▸ rfl
    have h2 : M = (N : ℤ) + 2 * s ^ 2 - 3 * z ^ 2 := hM_def
    have h3 : m * s = (N : ℤ) + 2 * s ^ 2 - 3 * z ^ 2 := by linarith [mul_comm s m, h1, h2]
    nlinarith [h3]
  -- k² = 3(4z²−s²) via k² = m² − 4ms + 4s² = (s²+4N) − 4(N−3z²+2s²) + 4s²
  have hm_s : m * s = (N : ℤ) - 3 * z ^ 2 + 2 * s ^ 2 := by nlinarith [hks]
  have hk_sq : k ^ 2 = 3 * (4 * z ^ 2 - s ^ 2) := by nlinarith [hm_sq, hm_s]
  -- 4z² > s² (from ν²(2a+b)² < ν²·4c² under hc2)
  have h4z2s2_nn : 0 ≤ 4 * z ^ 2 - s ^ 2 := by
    have hineq : (s : ℝ) ^ 2 < 4 * (z : ℝ) ^ 2 := by
      rw [hs_R, hz_R]
      have : (2 * a + b) ^ 2 < 4 * c ^ 2 := by nlinarith [hc2, mul_pos ha hb]
      nlinarith [sq_pos_of_pos hν]
    have hZ : (s : ℤ) ^ 2 < 4 * z ^ 2 := by exact_mod_cast hineq
    linarith
  -- 3 | k (from 3 | k²)
  have h3_dvd_k_sq : (3 : ℤ) ∣ k ^ 2 := ⟨4 * z ^ 2 - s ^ 2, by linarith [hk_sq]⟩
  have h3_dvd_k : (3 : ℤ) ∣ k :=
    (by norm_num : Prime (3 : ℤ)).dvd_of_dvd_pow h3_dvd_k_sq
  obtain ⟨j, hj⟩ := h3_dvd_k   -- k = 3j
  have hN15Z : (N : ℤ) = 15 := by exact_mod_cast hN15
  -- N = 15: (s+j)(s+3j) = 20 and z² = 5 − j s
  have hmk : m = 3 * j + 2 * s := by simp only [k] at hj; linarith
  have h20 : (s + j) * (s + 3 * j) = 20 := by
    rw [hmk, hN15Z] at hm_sq; nlinarith [hm_sq]
  have hz2 : z ^ 2 = 5 - j * s := by
    rw [hN15Z] at hks; rw [hj] at hks; nlinarith [hks]
  have hu_dvd : (s + j) ∣ 20 := ⟨s + 3 * j, h20.symm⟩
  have hu_le : (s + j).natAbs ≤ 20 := Nat.le_of_dvd (by norm_num)
    (by have := Int.natAbs_dvd_natAbs.mpr hu_dvd; simpa using this)
  obtain ⟨u, hu⟩ : ∃ u : ℤ, u = s + j := ⟨_, rfl⟩
  rw [← hu] at h20
  have hu_bd : -20 ≤ u ∧ u ≤ 20 := by omega
  have hsj : (s = 14 ∧ j = -4) ∨ (s = 2 ∧ j = -4) := by
    obtain ⟨hlo, hhi⟩ := hu_bd
    interval_cases u <;> omega
  rcases hsj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have : z ^ 2 = 61 := by linarith [hz2]
    have hzb : z ≤ 8 := by nlinarith
    interval_cases z <;> omega
  · have : z ^ 2 = 13 := by linarith [hz2]
    have hzb : z ≤ 4 := by nlinarith
    interval_cases z <;> omega

/-! ## Main theorem -/

/-- No prime `N > 3` admits a `CongruentDissection` with a 2π/3 model and an F3Data target. -/
theorem f3_prime_contradiction {N : ℕ} (D : CongruentDissection N)
    {α a b c ν : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : D.target.F3Data α a b c ν)
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (hN15 : N = 15) : False := by
  obtain ⟨-, hc0, -, -⟩ := cos_alpha_of_TwoPiThree D.model hm
  have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := c_sq D.model hm
  have hcpos : 0 < c := hc0
  -- Area formula
  have hNreal : (N : ℝ) = 3 * ν ^ 2 * (a + b) * (a + 2 * b) :=
    F3_area_formula D hm ht ha hb hν
  -- cor_int gives Mα, Mβ with flux equations
  obtain ⟨Mα, Mβ, hpar_α, hpar_β, hflux_α, hflux_β⟩ := Paper.cor_int D hα hm
  -- lemmaW_F3 gives the explicit flux values (two sign choices each)
  have hW_α := Row8.lemmaW_F3_alpha D.target hα ht
  have hW_β := Row8.lemmaW_F3_beta D.target hα ht
  -- Factor identities under hc2
  have hfact_α := F3_factor_alpha ν hc2
  have hfact_β := F3_factor_beta ν hc2
  -- Divisor positivity
  have hdiv_α : 0 < c + a - b := divisor_alpha_pos hc2 ha hb hcpos
  have hdiv_β : 0 < c + b - a := divisor_beta_pos hc2 ha hb hcpos
  -- N is odd (prime > 3 > 2)
  have hN_odd : ¬ (2 : ℤ) ∣ (N : ℤ) := by
    have : (N : ℤ) = 15 := by exact_mod_cast hN15
    rw [this]; norm_num
  -- Mα and Mβ are odd
  have hMα_odd : ¬ (2 : ℤ) ∣ Mα := fun h => hN_odd (by
    have := Int.dvd_sub hpar_α h; simp at this; exact this)
  have hMβ_odd : ¬ (2 : ℤ) ∣ Mβ := fun h => hN_odd (by
    have := Int.dvd_sub hpar_β h; simp at this; exact this)
  -- Mα + Mβ and Mβ − Mα are both even
  have hsum_even : (2 : ℤ) ∣ Mα + Mβ := by omega
  have hdiff_even : (2 : ℤ) ∣ Mβ - Mα := by omega
  -- Handle all 4 sign combinations
  -- In each case: derive hMα_val and hMβ_val, extract s = ν(2a+b) and z = νc from
  -- the sum/difference of Mα, Mβ, then apply f3_core.
  rcases hW_α with hα_pos | hα_neg <;> rcases hW_β with hβ_pos | hβ_neg
  · -- (++): Mα*(c+a-b) = ν*(c-2a-b)*(c+a-b), Mβ*(c+b-a) = -ν*(c+2a+b)*(c+b-a)
    have hMα_R : (Mα : ℝ) * (c + a - b) = ν * (-(c ^ 2) - c * (a + 2 * b) + 3 * b * (a + b)) :=
      hflux_α.symm.trans hα_pos
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = ν * (c ^ 2 - c * (a + 2 * b) - 3 * b * (a + b)) :=
      hflux_β.symm.trans hβ_pos
    have hMα_val : (Mα : ℝ) = ν * (c - 2 * a - b) :=
      mul_right_cancel₀ hdiv_α.ne' (hMα_R.trans hfact_α)
    have hMβ_val : (Mβ : ℝ) = -(ν * (c + 2 * a + b)) :=
      mul_right_cancel₀ hdiv_β.ne' (by linear_combination hMβ_R.trans hfact_β)
    -- 2ν(2a+b) = -(Mα+Mβ); 2νc = -(Mβ-Mα)
    have h2s : 2 * (ν * (2 * a + b)) = -((Mα : ℝ) + Mβ) := by rw [hMα_val, hMβ_val]; ring
    have h2z : 2 * (ν * c) = -((Mβ : ℝ) - Mα) := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨p, hp⟩ := hsum_even
    obtain ⟨q, hq⟩ := hdiff_even
    have hs_R : (-p : ℝ) = ν * (2 * a + b) := by
      have : (Mα + Mβ : ℝ) = 2 * p := by exact_mod_cast hp
      linarith [h2s]
    have hz_R : (-q : ℝ) = ν * c := by
      have : (Mβ - Mα : ℝ) = 2 * q := by exact_mod_cast hq
      linarith [h2z]
    have hs_pos : 0 < -p := by
      exact_mod_cast (show (0 : ℝ) < -p by rw [hs_R]; exact mul_pos hν (by linarith))
    have hz_pos : 0 < -q := by
      exact_mod_cast (show (0 : ℝ) < -q by rw [hz_R]; exact mul_pos hν hcpos)
    exact f3_core hN15 ha hb hν hc2 hNreal (-p) hs_pos (by exact_mod_cast hs_R)
      (-q) hz_pos (by exact_mod_cast hz_R)
  · -- (+-): Mα = ν(c-2a-b), Mβ = ν(c+2a+b)
    have hMα_R : (Mα : ℝ) * (c + a - b) = ν * (-(c ^ 2) - c * (a + 2 * b) + 3 * b * (a + b)) :=
      hflux_α.symm.trans hα_pos
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = -(ν * (c ^ 2 - c * (a + 2 * b) - 3 * b * (a + b))) :=
      hflux_β.symm.trans hβ_neg
    have hMα_val : (Mα : ℝ) = ν * (c - 2 * a - b) :=
      mul_right_cancel₀ hdiv_α.ne' (hMα_R.trans hfact_α)
    have hMβ_val : (Mβ : ℝ) = ν * (c + 2 * a + b) :=
      mul_right_cancel₀ hdiv_β.ne' (hMβ_R.trans (by linear_combination -hfact_β))
    -- 2ν(2a+b) = Mβ-Mα; 2νc = Mα+Mβ
    have h2s : 2 * (ν * (2 * a + b)) = (Mβ : ℝ) - Mα := by rw [hMα_val, hMβ_val]; ring
    have h2z : 2 * (ν * c) = (Mα : ℝ) + Mβ := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨q, hq⟩ := hdiff_even
    obtain ⟨p, hp⟩ := hsum_even
    have hs_R : (q : ℝ) = ν * (2 * a + b) := by
      have : (Mβ - Mα : ℝ) = 2 * q := by exact_mod_cast hq
      linarith [h2s]
    have hz_R : (p : ℝ) = ν * c := by
      have : (Mα + Mβ : ℝ) = 2 * p := by exact_mod_cast hp
      linarith [h2z]
    have hs_pos : 0 < q := by
      exact_mod_cast (show (0 : ℝ) < q by rw [hs_R]; exact mul_pos hν (by linarith))
    have hz_pos : 0 < p := by
      exact_mod_cast (show (0 : ℝ) < p by rw [hz_R]; exact mul_pos hν hcpos)
    exact f3_core hN15 ha hb hν hc2 hNreal q hs_pos (by exact_mod_cast hs_R)
      p hz_pos (by exact_mod_cast hz_R)
  · -- (-+): Mα = -ν(c-2a-b), Mβ = -ν(c+2a+b)
    have hMα_R : (Mα : ℝ) * (c + a - b) = -(ν * (-(c ^ 2) - c * (a + 2 * b) + 3 * b * (a + b))) :=
      hflux_α.symm.trans hα_neg
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = ν * (c ^ 2 - c * (a + 2 * b) - 3 * b * (a + b)) :=
      hflux_β.symm.trans hβ_pos
    have hMα_val : (Mα : ℝ) = -(ν * (c - 2 * a - b)) :=
      mul_right_cancel₀ hdiv_α.ne' (hMα_R.trans (by linear_combination -hfact_α))
    have hMβ_val : (Mβ : ℝ) = -(ν * (c + 2 * a + b)) :=
      mul_right_cancel₀ hdiv_β.ne' (by linear_combination hMβ_R.trans hfact_β)
    -- 2ν(2a+b) = -(Mβ-Mα); 2νc = -(Mα+Mβ)
    have h2s : 2 * (ν * (2 * a + b)) = -((Mβ : ℝ) - Mα) := by rw [hMα_val, hMβ_val]; ring
    have h2z : 2 * (ν * c) = -((Mα : ℝ) + Mβ) := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨q, hq⟩ := hdiff_even
    obtain ⟨p, hp⟩ := hsum_even
    have hs_R : (-q : ℝ) = ν * (2 * a + b) := by
      have : (Mβ - Mα : ℝ) = 2 * q := by exact_mod_cast hq
      linarith [h2s]
    have hz_R : (-p : ℝ) = ν * c := by
      have : (Mα + Mβ : ℝ) = 2 * p := by exact_mod_cast hp
      linarith [h2z]
    have hs_pos : 0 < -q := by
      exact_mod_cast (show (0 : ℝ) < -q by rw [hs_R]; exact mul_pos hν (by linarith))
    have hz_pos : 0 < -p := by
      exact_mod_cast (show (0 : ℝ) < -p by rw [hz_R]; exact mul_pos hν hcpos)
    exact f3_core hN15 ha hb hν hc2 hNreal (-q) hs_pos (by exact_mod_cast hs_R)
      (-p) hz_pos (by exact_mod_cast hz_R)
  · -- (--): Mα = -ν(c-2a-b), Mβ = ν(c+2a+b)
    have hMα_R : (Mα : ℝ) * (c + a - b) = -(ν * (-(c ^ 2) - c * (a + 2 * b) + 3 * b * (a + b))) :=
      hflux_α.symm.trans hα_neg
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = -(ν * (c ^ 2 - c * (a + 2 * b) - 3 * b * (a + b))) :=
      hflux_β.symm.trans hβ_neg
    have hMα_val : (Mα : ℝ) = -(ν * (c - 2 * a - b)) :=
      mul_right_cancel₀ hdiv_α.ne' (hMα_R.trans (by linear_combination -hfact_α))
    have hMβ_val : (Mβ : ℝ) = ν * (c + 2 * a + b) :=
      mul_right_cancel₀ hdiv_β.ne' (hMβ_R.trans (by linear_combination -hfact_β))
    -- 2ν(2a+b) = Mα+Mβ; 2νc = Mβ-Mα
    have h2s : 2 * (ν * (2 * a + b)) = (Mα : ℝ) + Mβ := by rw [hMα_val, hMβ_val]; ring
    have h2z : 2 * (ν * c) = (Mβ : ℝ) - Mα := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨p, hp⟩ := hsum_even
    obtain ⟨q, hq⟩ := hdiff_even
    have hs_R : (p : ℝ) = ν * (2 * a + b) := by
      have : (Mα + Mβ : ℝ) = 2 * p := by exact_mod_cast hp
      linarith [h2s]
    have hz_R : (q : ℝ) = ν * c := by
      have : (Mβ - Mα : ℝ) = 2 * q := by exact_mod_cast hq
      linarith [h2z]
    have hs_pos : 0 < p := by
      exact_mod_cast (show (0 : ℝ) < p by rw [hs_R]; exact mul_pos hν (by linarith))
    have hz_pos : 0 < q := by
      exact_mod_cast (show (0 : ℝ) < q by rw [hz_R]; exact mul_pos hν hcpos)
    exact f3_core hN15 ha hb hν hc2 hNreal p hs_pos (by exact_mod_cast hs_R)
      q hz_pos (by exact_mod_cast hz_R)

#check @f3_prime_contradiction

end Erdos634.Draft.R8N15F3
#print axioms Erdos634.Draft.R8N15F3.f3_prime_contradiction
