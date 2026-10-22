-- Draft/F1IrrationalRatio.lean — b/c ∉ ℚ for the F1 target (Step 3 of prop:F1free).
--
-- Proves `f1_b_over_c_irrational`: under the same hypotheses as `f1_pin_of_prime`,
-- the ratio b/c cannot be rational.
--
-- Argument (algebraic, no tile placement):
--   • `f1_pin_of_prime`: c*(N−1) = a*(N+1)
--   • c²=a²+ab+b²  (TwoPiThreeData law of cosines)
--   • If b = r·c (r : ℚ), substitute a = c·(N−1)/(N+1) and b = r·c into c²=a²+ab+b².
--     Dividing by c² gives the rational quadratic  (N+1)²r²+(N−1)(N+1)r−4N = 0.
--   • Complete the square: u := 2(N+1)r+(N−1) satisfies u² = N²+14N+1 (in ℚ).
--   • Coprimality argument: u.den = 1, so u.num² = N²+14N+1 in ℤ.
--   • `disc_not_square_prime` gives the contradiction.
--
-- ZERO sorry.  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).

import Erdos634.Draft.F1AlgebraPin
import Erdos634.InvariantProduct

open scoped Classical

namespace Erdos634.Draft.F1IrrationalRatioM

open Erdos634.Geometry

/-! ## Local restatement of c²=a²+ab+b² for TwoPiThreeData -/

private lemma c_sq_of_twoPiThree (T : Tri) {α a b c : ℝ}
    (h : T.TwoPiThreeData α a b c) : c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
  obtain ⟨σ, -, ha, -, hb, hγ, hc⟩ := h
  have hl := T.lawCos_perm σ
  rw [ha, hb, hc, hγ,
      show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three] at hl
  linarith

/-! ## Main theorem -/

set_option maxHeartbeats 400000 in
/-- For a prime `N > 3`, a 2π/3 model and an F1Data target, the ratio `b/c` is irrational.

This is the algebraic Step 3 of `prop:F1free` (PROOF_F1free.md): from `f1_pin_of_prime`
and `disc_not_square_prime`, no rational `r : ℚ` satisfies `b = r·c`.  Steps 4–5
(Lemma E geometric + K1/K2 corner argument) are not covered here. -/
theorem f1_b_over_c_irrational
    {N : ℕ} (D : CongruentDissection N) {α a b c μ : ℝ}
    (hα  : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hm  : D.model.TwoPiThreeData α a b c)
    (hF1 : D.target.F1Data α a b c μ)
    (hμ  : 0 < μ)
    (hpm : c * ((N : ℝ) - 1) = a * ((N : ℝ) + 1) ∧ μ * (c - a) = b)
    (h6  : 6 < N) :
    ¬ ∃ (r : ℚ), b = (r : ℝ) * c := by
  -- Side positivity
  obtain ⟨-, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  -- c² = a²+ab+b²
  have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := c_sq_of_twoPiThree D.model hm
  -- Algebraic pin: c*(N−1) = a*(N+1)
  have hpin : c * ((N : ℝ) - 1) = a * ((N : ℝ) + 1) :=
    hpm.1
  -- N ≥ 2 (prime), so N+1 > 0
  have hN2  : (2 : ℝ) ≤ (N : ℝ)    := by
    have h2 : 2 ≤ N := by omega
    exact_mod_cast h2
  have hN1p : (0 : ℝ) < (N : ℝ) + 1 := by linarith
  -- Assume b/c ∈ ℚ
  rintro ⟨r, hbrc⟩
  -- ── Step A: quadratic in r over ℚ ──────────────────────────────────────────
  -- From b = r·c and the pin, substitute into c² = a²+ab+b²:
  -- (N+1)²·r² + (N−1)·(N+1)·r − 4N = 0  in ℝ
  have hN1ne  : ((N : ℝ) + 1) ≠ 0 := hN1p.ne'
  have hcne   : c ≠ 0              := hc0.ne'
  have hc2pos : 0 < c ^ 2          := pow_pos hc0 2
  have hquad  : ((N : ℝ) + 1) ^ 2 * (r : ℝ) ^ 2 +
                ((N : ℝ) - 1) * ((N : ℝ) + 1) * (r : ℝ) -
                4 * (N : ℝ) = 0 := by
    rw [hbrc] at hc2
    -- a·(N+1) = c·(N−1)  [rearranging hpin]
    have hpin' : a * ((N : ℝ) + 1) = c * ((N : ℝ) - 1) := by linarith
    -- a²·(N+1)² = c²·(N−1)²  (from hpin': a·(N+1) = c·(N−1), square both sides)
    have ha_sq : a ^ 2 * ((N : ℝ) + 1) ^ 2 = c ^ 2 * ((N : ℝ) - 1) ^ 2 := by
      linear_combination (a * ((N : ℝ) + 1) + c * ((N : ℝ) - 1)) * hpin'
    -- a·(r·c)·(N+1)² = r·c²·(N−1)·(N+1)  (from hpin': a·(N+1) = c·(N−1))
    have h_arc : a * ((r : ℝ) * c) * ((N : ℝ) + 1) ^ 2 =
                 (r : ℝ) * c ^ 2 * ((N : ℝ) - 1) * ((N : ℝ) + 1) := by
      linear_combination (r : ℝ) * c * ((N : ℝ) + 1) * hpin'
    -- c²·(N+1)² = a²·(N+1)² + a·(r·c)·(N+1)² + r²·c²·(N+1)²
    have h1 : c ^ 2 * ((N : ℝ) + 1) ^ 2 =
              a ^ 2 * ((N : ℝ) + 1) ^ 2 +
              a * ((r : ℝ) * c) * ((N : ℝ) + 1) ^ 2 +
              (r : ℝ) ^ 2 * c ^ 2 * ((N : ℝ) + 1) ^ 2 := by
      linear_combination ((N : ℝ) + 1) ^ 2 * hc2
    -- c²·(N+1)² = c²·(N−1)² + r·c²·(N−1)·(N+1) + r²·c²·(N+1)²
    have hkey : c ^ 2 * ((N : ℝ) + 1) ^ 2 =
                c ^ 2 * ((N : ℝ) - 1) ^ 2 +
                (r : ℝ) * c ^ 2 * ((N : ℝ) - 1) * ((N : ℝ) + 1) +
                (r : ℝ) ^ 2 * c ^ 2 * ((N : ℝ) + 1) ^ 2 := by
      linarith [h1, ha_sq, h_arc]
    -- Divide by c²
    have hkey' : ((N : ℝ) + 1) ^ 2 = ((N : ℝ) - 1) ^ 2 +
                 (r : ℝ) * ((N : ℝ) - 1) * ((N : ℝ) + 1) +
                 (r : ℝ) ^ 2 * ((N : ℝ) + 1) ^ 2 :=
      mul_left_cancel₀ hc2pos.ne' (by linarith)
    nlinarith [sq_nonneg ((N : ℝ) + 1), sq_nonneg ((N : ℝ) - 1), hkey']
  -- Lift quadratic to ℚ (hquad is an identity about (r:ℝ); cast via ℚ injectivity)
  have hquad_Q : ((N : ℚ) + 1) ^ 2 * r ^ 2 +
                 ((N : ℚ) - 1) * ((N : ℚ) + 1) * r -
                 4 * (N : ℚ) = 0 := by
    have h : (((N : ℚ) + 1) ^ 2 * r ^ 2 +
              ((N : ℚ) - 1) * ((N : ℚ) + 1) * r -
              4 * (N : ℚ) : ℝ) = 0 := by push_cast; linarith [hquad]
    exact_mod_cast h
  -- ── Step B: complete the square in ℚ ────────────────────────────────────────
  -- u_q := 2·(N+1)·r + (N−1)  satisfies  u_q² = N²+14N+1  in ℚ
  set u_q : ℚ := 2 * ((N : ℚ) + 1) * r + ((N : ℚ) - 1) with hu_def
  have hu_rat : u_q ^ 2 = (N : ℚ) ^ 2 + 14 * (N : ℚ) + 1 := by
    rw [hu_def]; linear_combination 4 * hquad_Q
  -- ── Step C: coprimality argument → u_q.den = 1 ─────────────────────────────
  -- Clear denominator: u_q.num² = ((N:ℤ)²+14N+1) · u_q.den²  in ℤ
  have hmul : (u_q : ℚ) * u_q.den = u_q.num := by exact_mod_cast Rat.mul_den_eq_num u_q
  have hZ : u_q.num ^ 2 = ((N : ℤ) ^ 2 + 14 * (N : ℤ) + 1) * (u_q.den : ℤ) ^ 2 := by
    have hQ : (u_q.num : ℚ) ^ 2 =
              ((N : ℤ) ^ 2 + 14 * (N : ℤ) + 1 : ℤ) * (u_q.den : ℚ) ^ 2 := by
      calc (u_q.num : ℚ) ^ 2
          = (u_q * u_q.den) ^ 2                           := by rw [hmul]
        _ = u_q ^ 2 * (u_q.den : ℚ) ^ 2                 := by ring
        _ = ((N : ℚ) ^ 2 + 14 * (N : ℚ) + 1) * (u_q.den : ℚ) ^ 2 := by
              rw [hu_rat]
        _ = ((N : ℤ) ^ 2 + 14 * (N : ℤ) + 1 : ℤ) * (u_q.den : ℚ) ^ 2 := by push_cast; ring
    exact_mod_cast hQ
  -- (u_q.den:ℤ)² | u_q.num²
  have hdvd : (u_q.den : ℤ) ^ 2 ∣ u_q.num ^ 2 :=
    ⟨(N : ℤ) ^ 2 + 14 * (N : ℤ) + 1, by linear_combination hZ⟩
  -- IsCoprime (u_q.den:ℤ)² (u_q.num)²
  have hcop2 : IsCoprime ((u_q.den : ℤ) ^ 2) (u_q.num ^ 2) :=
    (Rat.isCoprime_num_den u_q).symm.pow_left.pow_right
  -- (u_q.den:ℤ)² | 1
  have hdvd1 : (u_q.den : ℤ) ^ 2 ∣ 1 :=
    hcop2.dvd_of_dvd_mul_left (show (u_q.den : ℤ) ^ 2 ∣ u_q.num ^ 2 * 1 by simpa using hdvd)
  -- (u_q.den:ℤ)² ≤ 1, so u_q.den = 1
  have hden1 : u_q.den = 1 := by
    have hle : (u_q.den : ℤ) ^ 2 ≤ 1 := Int.le_of_dvd one_pos hdvd1
    have hpos : (0 : ℤ) < u_q.den := by exact_mod_cast u_q.pos
    have hle1 : u_q.den ≤ 1 := by
      have : (u_q.den : ℤ) ≤ 1 := by nlinarith [sq_nonneg ((u_q.den : ℤ) - 1)]
      exact_mod_cast this
    exact Nat.le_antisymm hle1 u_q.pos
  -- u_q.num² = N²+14N+1  (over ℤ)
  have hnum_sq : u_q.num ^ 2 = (N : ℤ) ^ 2 + 14 * (N : ℤ) + 1 := by
    rw [hden1] at hZ; simpa using hZ
  -- Contradiction via disc_not_square_prime
  exact absurd hnum_sq.symm (Erdos634.InvariantProduct.disc_not_square (N : ℤ) u_q.num (by exact_mod_cast h6))

#check @f1_b_over_c_irrational
#print axioms f1_b_over_c_irrational

end Erdos634.Draft.F1IrrationalRatioM
