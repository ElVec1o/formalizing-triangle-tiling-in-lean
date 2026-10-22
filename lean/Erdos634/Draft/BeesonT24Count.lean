import Mathlib

/-!
# Beeson Theorem 24 (arXiv 1206.2229v4): the counting identity, general parameters

In the proof of Theorem 24 the isosceles triangle with base `mu*a`, legs `mu*c`, `mu = lam*a*b*(a+c)`, is assembled
from tile-similar triangles of scale `p = a c rho`, `q = b c rho`, `u = c w`, `t = a^2 rho`, `v = a w`
(`w = lam a (a+c) - c rho`), the parallelogram `P C R Q` (`t x r` cells, `r = mu - c^2 rho`) and the parallelogram
`G R L V` of height `h = rho c (a^2+b^2) - lam a^3 (a+c)` (cell count `v` per strip of width `a`, `t + r = w b`
per strip of width `b`; total `w*h`).  Number of tiles `p^2+q^2+u^2+t^2+v^2+2 t r + 2 w h`; with `a^2 + c b = c^2`
(i.e. `b = c - a^2/c`) this equals `mu^2 c / b` (the area equation).  The geometry is formalized per instance:
`BeesonT24_a_b_c.lean`.  Credit Beeson (arXiv 1206.2229), Laczkovich.  UNAUDITED.
-/

namespace Erdos634.BeesonT24Count

theorem thm24_count (a b c lam rho : ℤ) (h : a * a + c * b = c * c) :
    b * ((a * c * rho) ^ 2 + (b * c * rho) ^ 2 + (c * (lam * a * (a + c) - c * rho)) ^ 2 + (a ^ 2 * rho) ^ 2
      + (a * (lam * a * (a + c) - c * rho)) ^ 2
      + 2 * (a ^ 2 * rho) * (lam * a * b * (a + c) - c ^ 2 * rho)
      + 2 * (lam * a * (a + c) - c * rho) * (rho * c * (a ^ 2 + b ^ 2) - lam * a ^ 3 * (a + c)))
    = (lam * a * b * (a + c)) ^ 2 * c := by
  linear_combination (-b * (a ^ 4 * lam ^ 2 + 2 * a ^ 3 * c * lam ^ 2 - 2 * a ^ 2 * b * lam * rho
    + a ^ 2 * c ^ 2 * lam ^ 2 - 2 * a ^ 2 * c * lam * rho - a ^ 2 * rho ^ 2 - 2 * a * b * c * lam * rho
    - 2 * a * c ^ 2 * lam * rho + b * c * rho ^ 2 + c ^ 2 * rho ^ 2)) * h

/-- the strips: `h = x a + y b` gives `x v + y (t+r) = w h` cells, because `v = a w` and `t + r = b w` -/
theorem strips_cells (a b w x y : ℤ) : x * (a * w) + y * (b * w) = w * (x * a + y * b) := by ring

/-- the number of rows of the parallelogram `P C R Q` and the inequality `r >= 0, h >= a b`: instance `(2,3,4)`,
`lam = 1`, `rho = 2` (the Theorem 24 hypothesis `a^2 c < b (a^2 + b^2)` holds: `16 < 39`). -/
theorem hyp_2_3_4 : (2 : ℤ) * 2 * 4 < 3 * (2 * 2 + 3 * 3) ∧
    (4 : ℤ) ≥ 0 ∧ (56 : ℤ) ≥ 2 * 3 ∧ (56 : ℤ) = 28 * 2 + 0 * 3 ∧
    (1 * 2 * 3 * (2 + 4) - 4 ^ 2 * 2 : ℤ) = 4 ∧ (2 * 4 * (2 ^ 2 + 3 ^ 2) - 1 * 2 ^ 3 * (2 + 4) : ℤ) = 56 := by
  norm_num

theorem count_2_3_4 : (16 * 16 + 24 * 24 + 16 * 16 + 8 * 8 + 8 * 8 + 2 * 8 * 4 + 2 * 4 * 56 : ℤ) = 1728 := by
  norm_num

end Erdos634.BeesonT24Count
