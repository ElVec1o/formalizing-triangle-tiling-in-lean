import Mathlib

/-!
# Zhang Lemma 3 and Lemma 5 (arXiv 2512.22696v4): the arithmetic cores

Lemma 3: "If `a, b` are square-free, then if `X` is equiconstructible, `X = m a b` for an integer `m`."
Proof printed: `X^2 = a b N`; `gcd(a,b) = 1`, `a, b` square-free give `(ab) | N`, hence `(ab)^2 | X^2`.
Formal core (`lemma3`): `X N : N` with `X^2 = a b N`, `a b` squarefree, `Coprime a b`  =>  `a b | X`.
The integrality of `X` and the relation `X^2 = ab N` (area count) are the HYPOTHESES (printed: side lengths are
integers because the tile has integer sides and side `X` of `T` is a union of tile sides; `X^2 = abN` is the
area comparison `N = X^2/(ab)` of Sec. 3.1).  Neither is derived here.

Lemma 5: "If `a != b (mod 3)`, then if some triangle with angles `(2a,2b,a+b)` is tiled into `N` tiles,
`N = (a+2b)(b+2a) m^2` for an integer `m`."  Printed proof is arithmetic: the sides are
`((a+2b) a m, (b+2a) b m, c^2 m)` all integers, `m` rational; coprimality forces `m` integer; then count.
Formal core (`lemma5`): `m : Q` with `(a+2b) a m` and `(b+2a) b m` integers (`= p`, `q`), `Coprime a b`,
`a % 3 != b % 3`, `N a b = (a+2b) a m * (b+2a) b m` (the area ratio `N = (a+2b)(b+2a) m^2`, i.e. `N ab` = product of the
two sides over `1`)  =>  `m` is a natural number and `N = (a+2b)(b+2a) m^2`.
The hypotheses are satisfiable (witness `lemma5_wit`: tile `(3,5,7)`, `m = 1`, `N = 143`).
UNAUDITED.  Credit Zhang (arXiv 2512.22696v4), Beeson, Laczkovich.
-/

namespace Erdos634.ZhangRat6Arith

theorem lemma3 (a b X N : ℕ) (ha : Squarefree a) (hb : Squarefree b) (hab : Nat.Coprime a b)
    (h : X ^ 2 = a * b * N) : a * b ∣ X := by
  have h1 : a ∣ X ^ 2 := ⟨b * N, by rw [h]; ring⟩
  have h2 : b ∣ X ^ 2 := ⟨a * N, by rw [h]; ring⟩
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hab ((ha.dvd_pow_iff_dvd two_ne_zero).mp h1)
    ((hb.dvd_pow_iff_dvd two_ne_zero).mp h2)

theorem cop_lin (a b c : ℕ) (hab : Nat.Coprime a b) : Nat.Coprime (a + c * b) b := by
  simpa using (Nat.coprime_add_mul_right_left a b c).mpr hab

theorem coprime_sides (a b : ℕ) (hab : Nat.Coprime a b) (h3 : a % 3 ≠ b % 3) :
    Nat.Coprime ((a + 2 * b) * a) ((b + 2 * a) * b) := by
  have c1 : Nat.Coprime (a + 2 * b) b := cop_lin a b 2 hab
  have c2 : Nat.Coprime (b + 2 * a) a := cop_lin b a 2 hab.symm
  have c3 : Nat.Coprime (a + 2 * b) (b + 2 * a) := by
    set g := Nat.gcd (a + 2 * b) (b + 2 * a) with hg
    have g1 : g ∣ a + 2 * b := Nat.gcd_dvd_left _ _
    have g2 : g ∣ b + 2 * a := Nat.gcd_dvd_right _ _
    have g3a : g ∣ 3 * a := by
      have : 3 * a = 2 * (b + 2 * a) - (a + 2 * b) := by omega
      rw [this]; exact Nat.dvd_sub (Dvd.dvd.mul_left g2 2) g1
    have g3b : g ∣ 3 * b := by
      have : 3 * b = 2 * (a + 2 * b) - (b + 2 * a) := by omega
      rw [this]; exact Nat.dvd_sub (Dvd.dvd.mul_left g1 2) g2
    have g3 : g ∣ 3 := by
      have := Nat.dvd_gcd g3a g3b
      rwa [Nat.gcd_mul_left, hab, mul_one] at this
    have : g = 1 ∨ g = 3 := (Nat.dvd_prime Nat.prime_three).mp g3
    rcases this with h | h
    · exact h
    · exfalso; rw [h] at g1; omega
  exact Nat.Coprime.mul_right (Nat.Coprime.mul c3 c2.symm) (Nat.Coprime.mul c1 hab)

/-- Zhang Lemma 5, arithmetic core (hypotheses named in the header). -/
theorem lemma5 (a b N : ℕ) (m : ℚ) (hm : 0 < m) (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (h3 : a % 3 ≠ b % 3) (P Q : ℕ) (hP : (P : ℚ) = (a + 2 * b) * a * m)
    (hQ : (Q : ℚ) = (b + 2 * a) * b * m)
    (hN : (N : ℚ) * (a * b) = (a + 2 * b) * a * m * ((b + 2 * a) * b * m)) :
    ∃ k : ℕ, m = k ∧ N = (a + 2 * b) * (b + 2 * a) * k ^ 2 := by
  have hcop := coprime_sides a b hab h3
  have key : P * ((b + 2 * a) * b) = Q * ((a + 2 * b) * a) := by
    have : (P : ℚ) * ((b + 2 * a) * b) = Q * ((a + 2 * b) * a) := by rw [hP, hQ]; ring
    exact_mod_cast this
  have hd : (a + 2 * b) * a ∣ P :=
    hcop.dvd_of_dvd_mul_right ⟨Q, by rw [key]; ring⟩
  obtain ⟨k, hk⟩ := hd
  have hpos : (0 : ℚ) < (a + 2 * b) * a := by positivity
  have hmk : m = k := by
    have : ((a + 2 * b) * a : ℚ) * k = (a + 2 * b) * a * m := by
      rw [← hP, hk]; push_cast; ring
    exact (mul_left_cancel₀ hpos.ne' this).symm
  refine ⟨k, hmk, ?_⟩
  have hab' : (0 : ℚ) < a * b := by positivity
  have : (N : ℚ) = (a + 2 * b) * (b + 2 * a) * (k : ℚ) ^ 2 := by
    apply mul_right_cancel₀ hab'.ne'
    rw [hN, hmk]; ring
  exact_mod_cast this

/-- witness: tile `(3,5,7)`, `m = 1`, `N = 143`. -/
theorem lemma5_wit : ∃ k : ℕ, (1 : ℚ) = k ∧ 143 = (3 + 2 * 5) * (5 + 2 * 3) * k ^ 2 :=
  lemma5 3 5 143 1 one_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) 39 55
    (by norm_num) (by norm_num) (by norm_num)

theorem lemma3_wit : 3 * 5 ∣ 15 := lemma3 3 5 15 15 (Nat.prime_three.squarefree) (Nat.prime_five.squarefree) (by norm_num) (by norm_num)

end Erdos634.ZhangRat6Arith

#print axioms Erdos634.ZhangRat6Arith.lemma3
#print axioms Erdos634.ZhangRat6Arith.lemma5
#print axioms Erdos634.ZhangRat6Arith.lemma5_wit
