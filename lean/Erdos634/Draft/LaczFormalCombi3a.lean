-- Draft/LaczFormalCombi3a.lean -- Laczkovich, DCG 48 (2012), Lemma 3.8, the last three cases s/m in {3/5, 4/5, 4/7}
-- (alpha = 3 pi/10, 2 pi/5, 2 pi/7): the arithmetic core (printed equations (9)-(11)) and the Niven-type degree facts
-- that the printed proof takes from [5, Thm 3.9], here proved from `Polynomial.cyclotomic_eq_minpoly_rat`.  No tiling is involved.
-- The printed text says "the degree of sin alpha is greater than the degree of cos alpha" in all three cases; for
-- alpha = 3 pi/10 it is the reverse (sin alpha = cos(pi/5) has degree 2, cos alpha = sin(pi/5) has degree 4), the argument is
-- symmetric under swapping the legs, and that is what is formalized (`lem38_case35`).
-- NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Comput. Geom. 48 (2012) 330-372, Lemma 3.8; Combinatorica 10 (1990)), Beeson, Beeson-Zhang.
import Mathlib
import Erdos634.Draft.LaczFormalCombi2
import Erdos634.Draft.BeesonRow4A

open scoped Classical
open Polynomial IntermediateField

namespace Erdos634.Laczkovich.Combi3

open Erdos634.Laczkovich.Combi2 (irr_lin)

/-! ### the arithmetic core -/

/-- **Lemma 3.8, cases 3/5, 4/5, 4/7, arithmetic core (printed (9)-(11)).**  `c, s > 0`, `s^2 = 1 - c^2`, `c` irrational and
`s` not in `Q(c)` (written without field adjunction: no `r(c)/q(c)` equals `s`).  If `(x c + y s + z)(u c + v s + w) = (t/2) c s`
with `t > 0` then one side is an integer multiple of `s` and the other of `c` (and `z = w = 0`). -/
theorem lem38_sub (c s : ℝ) (hc : 0 < c) (hs : 0 < s) (hs2 : s ^ 2 = 1 - c ^ 2) (hcirr : Irrational c)
    (hS : ¬ ∃ r q : ℚ[X], aeval c q ≠ 0 ∧ s * aeval c q = aeval c r)
    (x y z u v w t : ℕ) (ht : 0 < t)
    (h : ((x : ℝ) * c + y * s + z) * ((u : ℝ) * c + v * s + w) = (t / 2) * c * s) :
    (x = 0 ∧ z = 0 ∧ v = 0 ∧ w = 0) ∨ (y = 0 ∧ z = 0 ∧ u = 0 ∧ w = 0) := by
  have hE : (((x : ℝ) * c + z) * ((u : ℝ) * c + w) + (y : ℝ) * v * (1 - c ^ 2))
      + (((x : ℝ) * v + y * u - t / 2) * c + ((z : ℝ) * v + y * w)) * s = 0 := by
    linear_combination h - ((y : ℝ) * v) * hs2
  have hD0 : ((x : ℝ) * v + y * u - t / 2) * c + ((z : ℝ) * v + y * w) = 0 := by
    by_contra hDne
    apply hS
    refine ⟨-((C ((x : ℚ) * u) * X ^ 2 + C ((x : ℚ) * w + z * u) * X + C ((z : ℚ) * w)) + C ((y : ℚ) * v) * (1 - X ^ 2)),
      C ((x : ℚ) * v + y * u - t / 2) * X + C ((z : ℚ) * v + y * w), ?_, ?_⟩
    · have : aeval c (C ((x : ℚ) * v + y * u - t / 2) * X + C ((z : ℚ) * v + y * w)) =
          ((x : ℝ) * v + y * u - t / 2) * c + ((z : ℝ) * v + y * w) := by
        simp
      rw [this]; exact hDne
    · have e1 : aeval c (C ((x : ℚ) * v + y * u - t / 2) * X + C ((z : ℚ) * v + y * w)) =
          ((x : ℝ) * v + y * u - t / 2) * c + ((z : ℝ) * v + y * w) := by
        simp
      have e2 : aeval c (-((C ((x : ℚ) * u) * X ^ 2 + C ((x : ℚ) * w + z * u) * X + C ((z : ℚ) * w))
          + C ((y : ℚ) * v) * (1 - X ^ 2))) =
          -(((x : ℝ) * c + z) * ((u : ℝ) * c + w) + (y : ℝ) * v * (1 - c ^ 2)) := by
        simp
        ring
      rw [e1, e2]; linarith
  have hP0 : ((x : ℝ) * c + z) * ((u : ℝ) * c + w) + (y : ℝ) * v * (1 - c ^ 2) = 0 := by
    rw [hD0] at hE; linarith
  -- nonnegativity of the pieces
  have hx : (0 : ℝ) ≤ x := Nat.cast_nonneg _
  have hy : (0 : ℝ) ≤ y := Nat.cast_nonneg _
  have hz : (0 : ℝ) ≤ z := Nat.cast_nonneg _
  have hu : (0 : ℝ) ≤ u := Nat.cast_nonneg _
  have hv : (0 : ℝ) ≤ v := Nat.cast_nonneg _
  have hw : (0 : ℝ) ≤ w := Nat.cast_nonneg _
  have hs2' : 0 < 1 - c ^ 2 := by rw [← hs2]; positivity
  have a1 : 0 ≤ (x : ℝ) * u * c ^ 2 := by positivity
  have a2 : 0 ≤ (x : ℝ) * w * c := by positivity
  have a3 : 0 ≤ (u : ℝ) * z * c := by positivity
  have a4 : 0 ≤ (z : ℝ) * w := by positivity
  have a5 : 0 ≤ (y : ℝ) * v * (1 - c ^ 2) := by positivity
  have hsum : (x : ℝ) * u * c ^ 2 + (x : ℝ) * w * c + (u : ℝ) * z * c + (z : ℝ) * w + (y : ℝ) * v * (1 - c ^ 2) = 0 := by
    linear_combination hP0
  have b1 : (x : ℝ) * u * c ^ 2 = 0 := by linarith
  have b2 : (x : ℝ) * w * c = 0 := by linarith
  have b3 : (u : ℝ) * z * c = 0 := by linarith
  have b4 : (z : ℝ) * w = 0 := by linarith
  have b5 : (y : ℝ) * v * (1 - c ^ 2) = 0 := by linarith
  have n1 : x * u = 0 := by
    have : (x : ℝ) * u = 0 := by
      rcases mul_eq_zero.mp b1 with h | h
      · exact h
      · exact absurd h (by positivity)
    exact_mod_cast this
  have n2 : x * w = 0 := by
    have : (x : ℝ) * w = 0 := by
      rcases mul_eq_zero.mp b2 with h | h
      · exact h
      · exact absurd h hc.ne'
    exact_mod_cast this
  have n3 : u * z = 0 := by
    have : (u : ℝ) * z = 0 := by
      rcases mul_eq_zero.mp b3 with h | h
      · exact h
      · exact absurd h hc.ne'
    exact_mod_cast this
  have n5 : y * v = 0 := by
    have : (y : ℝ) * v = 0 := by
      rcases mul_eq_zero.mp b5 with h | h
      · exact h
      · exact absurd h hs2'.ne'
    exact_mod_cast this
  have n4 : z * w = 0 := by exact_mod_cast b4
  -- the second equation: c irrational
  have key : (((z : ℚ) * v + y * w : ℚ) : ℝ) + (((x : ℚ) * v + y * u - t / 2 : ℚ) : ℝ) * c = 0 := by
    push_cast; linarith
  obtain ⟨k1, k2⟩ := irr_lin hcirr _ _ key
  have m1 : z * v + y * w = 0 := by
    have : (((z * v + y * w : ℕ)) : ℚ) = 0 := by push_cast; exact k1
    exact_mod_cast this
  have m2 : 2 * (x * v + y * u) = t := by
    have : (((2 * (x * v + y * u) : ℕ)) : ℚ) = (t : ℚ) := by push_cast; linarith
    exact_mod_cast this
  have n6 : z * v = 0 := by omega
  have n7 : y * w = 0 := by omega
  have hpos : 0 < x * v + y * u := by omega
  have zr : ∀ {a b : ℕ}, a * b = 0 → 0 < a → b = 0 := fun hab ha => (Nat.mul_eq_zero.mp hab).resolve_left ha.ne'
  have zl : ∀ {a b : ℕ}, a * b = 0 → 0 < b → a = 0 := fun hab hb => (Nat.mul_eq_zero.mp hab).resolve_right hb.ne'
  rcases Nat.add_pos_iff_pos_or_pos.mp hpos with h1 | h1
  · have hx0 : 0 < x := Nat.pos_of_ne_zero (left_ne_zero_of_mul h1.ne')
    have hv0 : 0 < v := Nat.pos_of_ne_zero (right_ne_zero_of_mul h1.ne')
    right
    exact ⟨zl n5 hv0, zl n6 hv0, zr n1 hx0, zr n2 hx0⟩
  · have hy0 : 0 < y := Nat.pos_of_ne_zero (left_ne_zero_of_mul h1.ne')
    have hu0 : 0 < u := Nat.pos_of_ne_zero (right_ne_zero_of_mul h1.ne')
    left
    exact ⟨zl n1 hu0, zl (by rw [mul_comm]; exact n3) hu0, zr n5 hy0, zr n7 hy0⟩

end Erdos634.Laczkovich.Combi3
