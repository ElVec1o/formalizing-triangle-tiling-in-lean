/-
Draft/CompositeS2Global.lean — S2 (target (2α, α, 2β)) at N = 22 and N = 42 by a GLOBAL divisibility argument
(new; no local obstruction exists at these N, see `CompositeS2Mod27`).
The point missed by the local closers: `S2Arith N` asks for an INTEGER S with N R² = S² A B, where
R = (q−p)(2q+p), A = 2q²−p², B = 3q²−p², gcd(p,q) = 1.  A is coprime to q−p and to q, and
A ≡ −2q² (mod 2q+p), whence  A ∣ 4N  (`s2_dvd`, valid for every N).  As A > q², q² < 4N.
N = 22: no 1 ≤ p < q ≤ 9 has A ∣ 88.  N = 42: A ∣ 168 only for (p,q) = (1,2), (2,3), and there the equation
itself (1050 = 77 S², 2688 = 322 S²) has no integer solution.  No p-adic input.
UNAUDITED.  Formalization debt, NOT /goal progress.  No sorry, no native_decide.
-/
import Erdos634.Draft.CompositeS2Arith

open scoped Classical

namespace Erdos634.Draft.CompositeS2Global

open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeS2Arith

/-- Global divisibility: any solution of the S2 integer equation has `A ∣ 4N`. -/
theorem s2_dvd (N : ℕ) (p q S : ℤ) (hcop : IsCoprime p q)
    (heq : (N : ℤ) * ((q - p) * (2 * q + p)) ^ 2 = S ^ 2 * (2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2)) :
    (2 * q ^ 2 - p ^ 2) ∣ 4 * (N : ℤ) := by
  obtain ⟨a, b, hab⟩ := hcop
  have cpu : IsCoprime p (q - p) := ⟨a + b, b, by linear_combination hab⟩
  have cpq : IsCoprime p q := ⟨a, b, hab⟩
  have hAu : IsCoprime (2 * q ^ 2 - p ^ 2) (q - p) := by
    have h1 : IsCoprime (p ^ 2) (q - p) := cpu.pow_left
    have h2 := h1.add_mul_left_left (z := 2 * (q - p) + 4 * p)
    have e : p ^ 2 + (q - p) * (2 * (q - p) + 4 * p) = 2 * q ^ 2 - p ^ 2 := by ring
    rwa [e] at h2
  have hAq : IsCoprime (2 * q ^ 2 - p ^ 2) (q ^ 4) := by
    have h1 : IsCoprime (-(p ^ 2)) q := (cpq.pow_left (m := 2)).neg_left
    have h2 := h1.add_mul_left_left (z := 2 * q)
    have e : -(p ^ 2) + q * (2 * q) = 2 * q ^ 2 - p ^ 2 := by ring
    rw [e] at h2
    exact h2.pow_right
  -- A ∣ N (uv)²
  have hd1 : (2 * q ^ 2 - p ^ 2) ∣ (N : ℤ) * (q - p) ^ 2 * (2 * q + p) ^ 2 :=
    ⟨S ^ 2 * (3 * q ^ 2 - p ^ 2), by linear_combination heq⟩
  have hd2 : (2 * q ^ 2 - p ^ 2) ∣ (N : ℤ) * (2 * q + p) ^ 2 := by
    have : (2 * q ^ 2 - p ^ 2) ∣ (q - p) ^ 2 * ((N : ℤ) * (2 * q + p) ^ 2) := by
      have e : (q - p) ^ 2 * ((N : ℤ) * (2 * q + p) ^ 2) = (N : ℤ) * (q - p) ^ 2 * (2 * q + p) ^ 2 := by ring
      rw [e]; exact hd1
    exact (hAu.pow_right (n := 2)).dvd_of_dvd_mul_left this
  obtain ⟨c, hc⟩ := hd2
  have hd3 : (2 * q ^ 2 - p ^ 2) ∣ 4 * (N : ℤ) * q ^ 4 := by
    refine ⟨(2 * q - p) ^ 2 * c - 2 * (2 * q + p) * (2 * q - p) * N + (2 * q ^ 2 - p ^ 2) * N, ?_⟩
    linear_combination ((2 * q - p) ^ 2) * hc
  exact hAq.dvd_of_dvd_mul_right hd3

/-- Finite check data. -/
theorem s2Arith_of_dvd (N : ℕ) (hN : 0 < N)
    (hfin : ∀ p q : ℤ, 0 < p → p < q → q ^ 2 < 4 * (N : ℤ) → (2 * q ^ 2 - p ^ 2) ∣ 4 * (N : ℤ) →
      ∀ S : ℤ, (N : ℤ) * ((q - p) * (2 * q + p)) ^ 2 =
        S ^ 2 * (2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2) → False) : S2Arith N := by
  intro p q S hp hpq hcop _hS heq
  have hd := s2_dvd N p q S hcop heq
  have hApos : 0 < 2 * q ^ 2 - p ^ 2 := by nlinarith
  have hle : 2 * q ^ 2 - p ^ 2 ≤ 4 * (N : ℤ) := Int.le_of_dvd (by positivity) hd
  have hq : q ^ 2 < 4 * (N : ℤ) := by nlinarith
  exact hfin p q hp hpq hq hd S heq

theorem s2Arith_22 : S2Arith 22 := by
  refine s2Arith_of_dvd 22 (by norm_num) ?_
  intro p q hp hpq hq hd S heq
  have hq1 : 1 < q := by omega
  have hq' : q ≤ 9 := by push_cast at hq; by_contra h; push Not at h; nlinarith
  interval_cases q <;> interval_cases p <;>
    first | (revert hd; norm_num; done) | (revert heq; generalize S ^ 2 = T; norm_num; omega)

theorem s2Arith_42 : S2Arith 42 := by
  refine s2Arith_of_dvd 42 (by norm_num) ?_
  intro p q hp hpq hq hd S heq
  have hq1 : 1 < q := by omega
  have hq' : q ≤ 12 := by push_cast at hq; by_contra h; push Not at h; nlinarith
  interval_cases q <;> interval_cases p <;>
    first | (revert hd; norm_num; done) | (revert heq; generalize S ^ 2 = T; norm_num; omega)

theorem s2Closed_22 : S2Closed 22 := s2Closed_of_arith 22 s2Arith_22
theorem s2Closed_42 : S2Closed 42 := s2Closed_of_arith 42 s2Arith_42

end Erdos634.Draft.CompositeS2Global

#print axioms Erdos634.Draft.CompositeS2Global.s2Closed_22
#print axioms Erdos634.Draft.CompositeS2Global.s2Closed_42
