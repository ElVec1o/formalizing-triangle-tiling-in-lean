-- Draft/FluxE2Pi3Row8Arith.lean — Algebraic identities for the Row 8 rationality argument
-- ((private working notes, not included) §3).
-- Pure arithmetic: c² = a²+ab+b² and ring/linear_combination only.  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
--
-- These identities connect the cor:int divisors (c+a−b) and (c+b−a) to the flux closed forms
-- for F2, F3, F4.  They do not require any tile-placement layer.
--
-- Formalization debt on the prime-case VERIFIED path; not progress on the three /goal outcomes.

import Mathlib.Tactic

namespace Erdos634.Row8Arith

/-! ## Core divisor arithmetic under c² = a²+ab+b² -/

/-- The product of the two cor:int divisors is `3ab`. -/
theorem divisor_product {a b c : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (c + a - b) * (c + b - a) = 3 * a * b := by linear_combination hc2

/-- F4 factor connecting M_α to flux: `(a−c)·(c+a−b) = −b(2a+b−c)`. -/
theorem F4_factor_alpha {a b c : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (a - c) * (c + a - b) = -(b * (2 * a + b - c)) := by linear_combination -hc2

/-- F4 factor connecting M_β to flux: `(a+c)·(c+b−a) = b(2a+b+c)`. -/
theorem F4_factor_beta {a b c : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (a + c) * (c + b - a) = b * (2 * a + b + c) := by linear_combination hc2

/-- F4 product of M values: M_α · M_β = μ(a−c) · μ(a+c) = μ²(a²−c²) = −μ²·b(a+b). -/
theorem F4_M_product {a b c : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (a - c) * (a + c) = -(b * (a + b)) := by linear_combination -hc2

/-- F3 denominator product (same as divisor_product). -/
theorem F3_denominator_product {a b c : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (c + a - b) * (c + b - a) = 3 * a * b := divisor_product hc2

/-- F2 denominator product (same as divisor_product). -/
theorem F2_denominator_product {a b c : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (c + a - b) * (c + b - a) = 3 * a * b := divisor_product hc2

/-! ## Positivity under strict triangle inequalities -/

/-- For a 120°-triple with `a, b, c > 0` satisfying c²=a²+ab+b², we have `c+a−b > 0`. -/
theorem divisor_alpha_pos {a b c : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < c + a - b := by
  have hcb : b ^ 2 < c ^ 2 := by nlinarith [mul_pos ha hb]
  nlinarith [sq_nonneg (c - b), sq_nonneg (c + b)]

/-- For a 120°-triple with `a, b, c > 0` satisfying c²=a²+ab+b², we have `c+b−a > 0`. -/
theorem divisor_beta_pos {a b c : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < c + b - a := by
  have hca : a ^ 2 < c ^ 2 := by nlinarith [mul_pos ha hb]
  nlinarith [sq_nonneg (c - a), sq_nonneg (c + a)]

end Erdos634.Row8Arith

#print axioms Erdos634.Row8Arith.divisor_product
#print axioms Erdos634.Row8Arith.F4_factor_alpha
#print axioms Erdos634.Row8Arith.F4_factor_beta
#print axioms Erdos634.Row8Arith.F4_M_product
#print axioms Erdos634.Row8Arith.divisor_alpha_pos
#print axioms Erdos634.Row8Arith.divisor_beta_pos
