import Mathlib

/-!
# Laczkovich Thm 5.1, case (4): the finite check, specialised to the tile `(a, b, 2a+b)`, `3a + 2b = n`

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, p. 92, equations (4)-(6)), Laczkovich (Combinatorica 10 (1990),
pp. 299-300, the two leftover triples), Beeson, Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.

Printed (p. 92): if `a/n = 1/3, p = 3, q = 0` or `a/n = 1/6, p = 6, q = 0` then `n in {18, 24, 30}`, and with the conjugate relations
(5) `x{ka/n} + y{kb/n} + z{kc/n} = v'` (`k = 1 mod 6`), (6) the same with `1 - {.}` (`k = 5 mod 6`), `k = 5, 7, 11, 13`, every triple
is impossible or in (i)-(vii) except `(4/24, 6/24, 14/24) = (1/6, 1/4, 7/12)` and `(4/24, 2/24, 18/24)`.
Here all angles are integers in units of `pi/n`, `{ka/n} = ((k*a) % n)/n`.

For the tile family `(a, b, 2a + b)` with `3a + 2b = n` of `BeesonH1.Lacz51` the check is arithmetic: the only survivor is
`(n, a, b, c) = (24, 4, 6, 14)`, the tile `(pi/6, pi/4, 7 pi/12)`, which is the printed leftover triple, and it passes the conjugate
relations (5),(6) for `k = 5, 7, 11, 13` (so those relations cannot exclude it: the exclusion is the cited Combinatorica argument).
-/

namespace Erdos634.Lacz51

/-- In the family `c = 2a + b`, `3a + 2b = n`, `b > 0`: case (4) (`a/n = 1/3` or `1/6`) forces `(n,a,b,c) = (24,4,6,14)`. -/
theorem family_case4 {n a b c : ℕ} (hn : n = 18 ∨ n = 24 ∨ n = 30) (ha : 3 * a = n ∨ 6 * a = n)
    (hrel : 3 * a + 2 * b = n) (hb : 0 < b) (hc : c = 2 * a + b) : n = 24 ∧ a = 4 ∧ b = 6 ∧ c = 14 := by
  omega

/-- The survivor passes (5)/(6) for `k = 5, 7, 11, 13` with `(x,y,z) = (0,1,3)`, `v = 2` (`x a + y b + z c = v n`). -/
theorem survivor_tile : 0 * 4 + 1 * 6 + 3 * 14 = 2 * 24 := by decide

theorem survivor_conj :
    ∀ k ∈ ({5, 7, 11, 13} : Finset ℕ),
      ∃ v' ∈ ({1, 2} : Finset ℕ),
        (k % 6 = 1 → 0 * (k * 4 % 24) + 1 * (k * 6 % 24) + 3 * (k * 14 % 24) = v' * 24) ∧
        (k % 6 = 5 → 0 * (24 - k * 4 % 24) + 1 * (24 - k * 6 % 24) + 3 * (24 - k * 14 % 24) = v' * 24) := by
  decide

/-- Unit-orientation claim of p. 92: if `eta = -1` the conjugate target angles `pi - A, pi - B, pi - C` sum to `2 pi > pi`
(integer form: `A + B + C = n` gives `(n-A)+(n-B)+(n-C) = 2n > n`). -/
theorem eta_neg_impossible {n A B C : ℕ} (h : A + B + C = n) (hn : 0 < n) : n < (n - A) + (n - B) + (n - C) := by
  omega

end Erdos634.Lacz51

#print axioms Erdos634.Lacz51.family_case4
#print axioms Erdos634.Lacz51.survivor_conj
#print axioms Erdos634.Lacz51.eta_neg_impossible
