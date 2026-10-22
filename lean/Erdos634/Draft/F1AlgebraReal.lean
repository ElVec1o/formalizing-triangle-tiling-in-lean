-- Draft/F1AlgebraReal.lean — Real-valued ports of the F₁ algebraic lemmas.
-- These are word-for-word translations of `InvariantProduct.lean`'s F1_Ma/Mb/product/ratio/pin
-- from ℤ to ℝ.  All proofs use only `ring`, `linear_combination`, `mul_left_cancel₀` —
-- tactics that work in any commutative ring, and in particular in ℝ.
--
-- See (private working notes, not included) §5/R2 and §11 ("mechanical port") for the
-- justification.  ZERO sorry.  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).

import Mathlib.Tactic

open scoped Classical

namespace Erdos634.F1AlgebraReal

/-! ## Helpers -/

/-- `(2a+b−c)(2a+b+c) = 3a(a+b)` modulo `c²=a²+ab+b²`. -/
theorem F1_num_real (a b c : ℝ) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (2 * a + b - c) * (2 * a + b + c) = 3 * a * (a + b) := by
  linear_combination -hc

/-- `(c+a−b)(c+b−a) = 3ab` modulo `c²=a²+ab+b²`. -/
theorem XY_eq_real (a b c : ℝ) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (c + a - b) * (c + b - a) = 3 * (a * b) := by
  linear_combination hc

/-! ## Main algebraic lemmas -/

/-- `M_α · b = k · (c − a)` from the flux equation `M_α · (c+a−b) = k · (2a+b−c)`. -/
theorem F1_Ma_real (a b c k Ma : ℝ) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) (ha : a ≠ 0)
    (hMa : Ma * (c + a - b) = k * (2 * a + b - c)) :
    Ma * b = k * (c - a) := by
  have h3a : (3 : ℝ) * a ≠ 0 := by simpa using ha
  refine mul_left_cancel₀ h3a ?_
  have e1 : (3 * a) * (Ma * b) = Ma * ((c + a - b) * (c + b - a)) := by
    rw [XY_eq_real a b c hc]; ring
  have e2 : (3 * a) * (k * (c - a)) = k * ((2 * a + b - c) * (c + b - a)) := by
    linear_combination k * hc
  rw [e1, e2, ← mul_assoc, hMa, mul_assoc]

/-- `M_β · b = k · (c + a)` from the flux equation `M_β · (c+b−a) = k · (2a+b+c)`. -/
theorem F1_Mb_real (a b c k Mb : ℝ) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) (ha : a ≠ 0)
    (hMb : Mb * (c + b - a) = k * (2 * a + b + c)) :
    Mb * b = k * (c + a) := by
  have h3a : (3 : ℝ) * a ≠ 0 := by simpa using ha
  refine mul_left_cancel₀ h3a ?_
  have e1 : (3 * a) * (Mb * b) = Mb * ((c + b - a) * (c + a - b)) := by
    rw [show (c + b - a) * (c + a - b) = (c + a - b) * (c + b - a) by ring, XY_eq_real a b c hc]
    ring
  have e2 : (3 * a) * (k * (c + a)) = k * ((2 * a + b + c) * (c + a - b)) := by
    linear_combination (-k) * hc
  rw [e1, e2, ← mul_assoc, hMb, mul_assoc]

/-- `M_α · M_β = N` given the area identity `N·b = k²·(a+b)` and the two flux equations. -/
theorem F1_product_real (a b c k N Ma Mb : ℝ) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hN : N * b = k ^ 2 * (a + b))
    (hMa : Ma * (c + a - b) = k * (2 * a + b - c))
    (hMb : Mb * (c + b - a) = k * (2 * a + b + c)) :
    Ma * Mb = N := by
  have e1 := F1_Ma_real a b c k Ma hc ha hMa
  have e2 := F1_Mb_real a b c k Mb hc ha hMb
  have key : (Ma * Mb) * (b * b) = N * (b * b) :=
    calc (Ma * Mb) * (b * b) = (Ma * b) * (Mb * b) := by ring
      _ = (k * (c - a)) * (k * (c + a)) := by rw [e1, e2]
      _ = k ^ 2 * (a + b) * b := by linear_combination (k ^ 2) * hc
      _ = (N * b) * b := by rw [hN]
      _ = N * (b * b) := by ring
  exact mul_right_cancel₀ (mul_ne_zero hb hb) key

/-- `M_β · (c − a) = M_α · (c + a)` from the two flux equations. -/
theorem F1_ratio_real (a b c k Ma Mb : ℝ) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hMa : Ma * (c + a - b) = k * (2 * a + b - c))
    (hMb : Mb * (c + b - a) = k * (2 * a + b + c)) :
    Mb * (c - a) = Ma * (c + a) := by
  have e1 := F1_Ma_real a b c k Ma hc ha hMa
  have e2 := F1_Mb_real a b c k Mb hc ha hMb
  refine mul_right_cancel₀ hb ?_
  calc Mb * (c - a) * b = (Mb * b) * (c - a) := by ring
    _ = (k * (c + a)) * (c - a) := by rw [e2]
    _ = (k * (c - a)) * (c + a) := by ring
    _ = (Ma * b) * (c + a) := by rw [e1]
    _ = Ma * (c + a) * b := by ring

/-- With `M_α = 1` and `M_β = N`, the tile ratio is pinned: `c(N−1) = a(N+1)`. -/
theorem F1_pin_real (a c N : ℝ) (h : N * (c - a) = 1 * (c + a)) :
    c * (N - 1) = a * (N + 1) := by
  linear_combination h

#print axioms F1_Ma_real
#print axioms F1_Mb_real
#print axioms F1_product_real
#print axioms F1_ratio_real
#print axioms F1_pin_real

end Erdos634.F1AlgebraReal
