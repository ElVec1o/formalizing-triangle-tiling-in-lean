-- Draft/R8N15Arith.lean — arithmetic for the R8 F4/F4' shapes at N = 15: `15 = (x+y)(2x+y)` with x ∈ ℕ>0, y ∈ ℚ>0
-- forces x = 2, y = 1 (then xc² = 7 is not a square).  N-free first steps of R8CompositeArg.  UNAUDITED.
import Mathlib

namespace Erdos634.Draft.R8N15Arith

theorem F4_form_15 (x : ℕ) (hx : 0 < x) (y : ℚ) (hy : 0 < y)
    (heq : ((15 : ℕ) : ℚ) = (↑x + y) * (2 * ↑x + y)) : x = 2 ∧ y = 1 := by
  have hnum_pos : 0 < y.num := Rat.num_pos.mpr hy
  have hden_pos : 0 < y.den := y.pos
  have hZ : ((15 : ℕ) : ℤ) * y.den ^ 2 = (↑x * ↑y.den + y.num) * (2 * ↑x * ↑y.den + y.num) := by
    have hd_ne : (y.den : ℚ) ≠ 0 := by exact_mod_cast hden_pos.ne'
    have hyd : y * (y.den : ℚ) = y.num := by exact_mod_cast Rat.mul_den_eq_num y
    have hQ : ((15 : ℕ) : ℚ) * y.den ^ 2 = (↑x * ↑y.den + y.num) * (2 * ↑x * ↑y.den + y.num) := by
      calc ((15 : ℕ) : ℚ) * y.den ^ 2
          = ((↑x + y) * (2 * ↑x + y)) * y.den ^ 2 := by rw [← heq]
        _ = (↑x * ↑y.den + y * ↑y.den) * (2 * ↑x * ↑y.den + y * ↑y.den) := by ring
        _ = (↑x * ↑y.den + ↑y.num) * (2 * ↑x * ↑y.den + ↑y.num) := by rw [hyd]
    exact_mod_cast hQ
  have hnn : (y.num.natAbs : ℤ) = y.num := Int.natAbs_of_nonneg (le_of_lt hnum_pos)
  have hNeq_nat : 15 * y.den ^ 2 = (x * y.den + y.num.natAbs) * (2 * x * y.den + y.num.natAbs) := by
    have hZ' : ((15 : ℕ) : ℤ) * y.den ^ 2 =
        (↑x * ↑y.den + ↑y.num.natAbs) * (2 * ↑x * ↑y.den + ↑y.num.natAbs) := by
      rw [hnn]; exact hZ
    exact_mod_cast hZ'
  set r := y.num.natAbs with hr
  set s := y.den with hs
  have hrpos : 0 < r := by simp [hr, Nat.pos_iff_ne_zero, ne_of_gt hnum_pos]
  have hcop : Nat.Coprime r s := y.reduced
  have hs_dvd_r2 : s ∣ r ^ 2 := by
    have hZ2 : (s : ℤ) ∣ (r : ℤ) ^ 2 := by
      have heqZ : (15 : ℤ) * s ^ 2 = (x * s + r) * (2 * x * s + r) := by exact_mod_cast hNeq_nat
      have hdvd : (s : ℤ) ∣ (↑x * ↑s + ↑r) * (2 * ↑x * ↑s + ↑r) := by
        rw [← heqZ]; exact ⟨15 * s, by ring⟩
      have heq2 : (↑x * ↑s + ↑r) * (2 * ↑x * ↑s + ↑r) =
          (r : ℤ) ^ 2 + s * (2 * x ^ 2 * s + 3 * x * r) := by ring
      rw [heq2] at hdvd
      have h2 : (s : ℤ) ∣ (s : ℤ) * (2 * x ^ 2 * s + 3 * x * r) := dvd_mul_right _ _
      have h3 := dvd_sub hdvd h2
      rwa [show (r : ℤ) ^ 2 + (s : ℤ) * (2 * ↑x ^ 2 * ↑s + 3 * ↑x * ↑r) -
          (s : ℤ) * (2 * ↑x ^ 2 * ↑s + 3 * ↑x * ↑r) = (r : ℤ) ^ 2 from by ring] at h3
    exact_mod_cast hZ2
  have hs1 : s = 1 := by
    have hcop2 : Nat.Coprime s (r ^ 2) := hcop.symm.pow_right 2
    have hs_dvd1 : s ∣ 1 := by
      have h := Nat.dvd_gcd (dvd_refl s) hs_dvd_r2
      rwa [hcop2] at h
    exact Nat.le_antisymm (Nat.le_of_dvd one_pos hs_dvd1) hden_pos
  rw [hs1] at hNeq_nat
  simp at hNeq_nat
  have hx7 : x ≤ 7 := by nlinarith
  have hr15 : r ≤ 15 := by nlinarith
  have hxr : x = 2 ∧ r = 1 := by
    interval_cases x <;> interval_cases r <;> omega
  refine ⟨hxr.1, ?_⟩
  have hyq : y = (y.num : ℚ) / (y.den : ℚ) := (Rat.num_div_den y).symm
  rw [hyq, show y.den = 1 from hs1]
  have : y.num = 1 := by
    have : (y.num.natAbs : ℤ) = y.num := hnn
    have h1 : y.num.natAbs = 1 := hxr.2
    omega
  rw [this]; norm_num

end Erdos634.Draft.R8N15Arith
#print axioms Erdos634.Draft.R8N15Arith.F4_form_15
