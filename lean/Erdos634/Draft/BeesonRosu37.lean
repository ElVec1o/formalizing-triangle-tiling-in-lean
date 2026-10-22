import Mathlib
import Erdos634.Draft.BeesonRowL30
import Erdos634.Draft.BeesonColL35L36

/-!
# Beeson-Rosu (arXiv 2607.23453 v2) Theorem 37, edge-arithmetic skeleton (no `j = 1` tiling of the isosceles-beta triangle)

NOTE, UNAUDITED.  Credit: Michael Beeson and Rosu (arXiv 2607.23453 v2, Lemmas 23, 30, 31, 34, 35, 36, Theorem 37), Beeson
(arXiv 1206.2229 v4), Laczkovich.  Formalization debt, not progress on the /goal outcomes.

Printed statement: "There is no `j = 1` tiling of the isosceles-beta triangle when `3 alpha + 2 beta = pi` with `alpha` not a
rational multiple of `pi`."  (triangle `(beta, beta, 3 alpha)`, legs `X = k c`, base `Y = m (b + 2c)` by Lemma 35, tile
`(a,b,c) = (km, k^2-m^2, k^2)`.)

Printed proof, as used here: (1) base `AC` carries a run of `>= k` c edges (Lemma 34, hypothesis vacuous since beta sits at `A, C`),
and by Lemma 30 D its edge decomposition `(p0,q0,r0)` of `Y` is `(0, m, 2m)`, so `p0 = 0`; (2) the leg `AB` carries a run of
`>= k` c edges (Lemma 34, applied because the middle tile at `B` has alpha at `B`), and its length is `k c`, so its decomposition is
`(0,0,k)`; (3) the tile at `A` has beta at `A`, so an `a` edge (a side adjacent to beta) lies on `AB` or `AC`: contradiction.

`thm37_edges` is steps (1)-(3) as integer arithmetic, with the GEOMETRIC INPUTS NAMED HYPOTHESES (they are the content of
Lemma 34 / Lemma 23 and the tile placement, which are not derived here):
  * `hbase`/`hleg`: edge-sum equations of `AC` and `AB` (`p a + q b + r c` = length),
  * `hrun0`/`hrun1`: Lemma 34 outputs, `r >= k` on `AC` and on `AB`,
  * `hA`: the tile at `A` (angle beta) contributes an `a` edge on `AB` or `AC`: `1 <= p0 or 1 <= p1`.
The conclusion `False` is the printed contradiction.  What is NOT proved: Lemma 34 (run of `k` c edges, geometric; partly in
`ThmDPig`), Lemma 23 (alpha, beta, gamma placement), Lemma 31/H1, and the passage from a `CongruentDissection` with the target
sides `(k c, k c, m(b+2c))` to these edge data (that is `BeesonCol2T41.NoIsoJ1`).  No tiling is constructed.
-/

namespace Erdos634.BeesonRosu37

/-- Steps (1)-(3) of the printed proof of Theorem 37. -/
theorem thm37_edges {k m : ℤ} (hm : 0 < m) (hmk : m < k) (hcop : IsCoprime m k)
    {p0 q0 r0 p1 q1 r1 : ℤ} (hp0 : 0 ≤ p0) (hq0 : 0 ≤ q0) (hp1 : 0 ≤ p1) (hq1 : 0 ≤ q1)
    (hbase : p0 * (k * m) + q0 * (k ^ 2 - m ^ 2) + r0 * k ^ 2 = m * ((k ^ 2 - m ^ 2) + 2 * k ^ 2))
    (hleg : p1 * (k * m) + q1 * (k ^ 2 - m ^ 2) + r1 * k ^ 2 = k * k ^ 2)
    (hrun0 : k ≤ r0) (hrun1 : k ≤ r1)
    (hA : 1 ≤ p0 ∨ 1 ≤ p1) : False := by
  have hk : 0 < k := by linarith
  have hb : 0 < k ^ 2 - m ^ 2 := by nlinarith
  have ha : 0 < k * m := by positivity
  have hD := BeesonRowL30.lemma30_D hm hmk hcop hp0 hq0 hrun0 hbase
  have hp0z : p0 = 0 := hD.1
  have hp1z : p1 = 0 := by
    have h1 : p1 * (k * m) + q1 * (k ^ 2 - m ^ 2) + (r1 - k) * k ^ 2 = 0 := by linear_combination hleg
    have : 0 ≤ (r1 - k) * k ^ 2 := mul_nonneg (by linarith) (by positivity)
    have h2 : p1 * (k * m) = 0 := by nlinarith [mul_nonneg hp1 ha.le, mul_nonneg hq1 hb.le]
    exact (mul_eq_zero.mp h2).resolve_right ha.ne'
  rcases hA with h | h <;> omega

/-- The base part is consistent: at `(k,m) = (3,2)` (`2m >= k`) the decomposition `(0, m, 2m)` with `r0 = 4 >= 3` satisfies
`hbase`, `hrun0`, `hp0`, `hq0`.  (The full hypothesis set is a `no tiling` reduction and cannot be jointly witnessed.) -/
theorem thm37_base_wit : ∃ (k m p0 q0 r0 : ℤ), 0 < m ∧ m < k ∧ IsCoprime m k ∧ 0 ≤ p0 ∧ 0 ≤ q0 ∧ k ≤ r0 ∧
    p0 * (k * m) + q0 * (k ^ 2 - m ^ 2) + r0 * k ^ 2 = m * ((k ^ 2 - m ^ 2) + 2 * k ^ 2) :=
  ⟨3, 2, 0, 2, 4, by norm_num, by norm_num, by norm_num [Int.isCoprime_iff_gcd_eq_one], le_rfl, by norm_num, by norm_num,
    by norm_num⟩

/-- Leg part consistent: `(0,0,k)` solves `hleg`, `hrun1`. -/
theorem thm37_leg_wit (k m : ℤ) (hk : 0 < k) :
    (0 : ℤ) * (k * m) + 0 * (k ^ 2 - m ^ 2) + k * k ^ 2 = k * k ^ 2 ∧ k ≤ k := ⟨by ring, le_rfl⟩

end Erdos634.BeesonRosu37

#print axioms Erdos634.BeesonRosu37.thm37_edges
#print axioms Erdos634.BeesonRosu37.thm37_base_wit
