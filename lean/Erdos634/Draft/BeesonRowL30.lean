import Mathlib

/-!
# Beeson-Rosu (arXiv 2607.23453 v2) Lemma 30: edge decompositions for the tile `(km, k^2-m^2, k^2)`

NOTE, UNAUDITED.  Credit: Michael Beeson and Rosu (arXiv 2607.23453 v2, Lemmas 28, 30; Def. 10.2), Beeson (arXiv 1206.2229 v4),
Laczkovich (DCG 48 (2012)), Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.

`(a, b, c) = (k m, k^2 - m^2, k^2)`, `0 < m < k`, `gcd(m, k) = 1`.  `lemma30_lattice` is the content of Lemma 28 used here
(every integer relation `p a + q b + r c = 0` is `xi (k,0,-m) + eta (m,k,-k)`), proved directly from coprimality.  Then
(A) `n a`, (B) `n b`, (C) `n c` (`1 <= n < k`) and (D) `m (b + 2c)` with `r >= k`, (E) `m (b + c)` with `r >= k`, exactly as
printed.  Pure integer arithmetic; no dissection.  Variables are naturals with `b + m^2 = k^2`.
-/

namespace Erdos634.BeesonRowL30

/-- relation lattice (Lemma 28 for this family) -/
theorem lemma30_lattice (k m p q r : ℤ) (hk : 0 < k) (hcop : IsCoprime m k)
    (h : p * (k * m) + q * (k ^ 2 - m ^ 2) + r * k ^ 2 = 0) :
    ∃ ξ η : ℤ, p = ξ * k + η * m ∧ q = η * k ∧ r = -ξ * m - η * k := by
  have hk0 : k ≠ 0 := hk.ne'
  have h1 : k ∣ q * m ^ 2 := by
    have : q * m ^ 2 = k * (p * m + q * k + r * k) := by linear_combination -h
    exact ⟨_, this⟩
  have hc2 : IsCoprime (m ^ 2) k := hcop.pow_left
  obtain ⟨η, hη⟩ : k ∣ q := hc2.symm.dvd_of_dvd_mul_right h1
  have hq : q = η * k := by rw [hη]; ring
  have h2 : p * m + η * (k ^ 2 - m ^ 2) + r * k = 0 := by
    have : k * (p * m + η * (k ^ 2 - m ^ 2) + r * k) = 0 := by rw [hq] at h; linear_combination h
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hk0
    · exact h
  have h3 : k ∣ m * (p - η * m) := ⟨-η * k - r, by linear_combination h2⟩
  obtain ⟨ξ, hξ⟩ : k ∣ p - η * m := hcop.symm.dvd_of_dvd_mul_left h3
  have hp : p = ξ * k + η * m := by linarith [hξ]
  refine ⟨ξ, η, hp, hq, ?_⟩
  have : k * (r + ξ * m + η * k) = 0 := by rw [hp] at h2; linear_combination h2
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hk0
  · linarith

section parts
variable {k m : ℤ} (hm : 0 < m) (hmk : m < k) (hcop : IsCoprime m k)
include hm hmk hcop

theorem eta_nonneg {q η : ℤ} (hq : 0 ≤ q) (e : q = η * k) : 0 ≤ η := by
  by_contra h; push_neg at h; nlinarith

/-- (A) the only edge decomposition of `n a` (`1 <= n < k`) is `(n,0,0)` -/
theorem lemma30_A {n p q r : ℤ} (hn : 1 ≤ n) (hnk : n < k) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (h : p * (k * m) + q * (k ^ 2 - m ^ 2) + r * k ^ 2 = n * (k * m)) : p = n ∧ q = 0 ∧ r = 0 := by
  obtain ⟨ξ, η, e1, e2, e3⟩ := lemma30_lattice k m (p - n) q r (by linarith) hcop (by linear_combination h)
  have hη := eta_nonneg hm hmk hcop hq e2
  rcases hη.eq_or_lt with h0 | h1
  · subst h0
    have hξ : ξ = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hl | hg
      · nlinarith
      · nlinarith
    subst hξ
    refine ⟨by linarith, by linarith, by linarith⟩
  · exfalso
    have hξ : ξ < -η := by
      by_contra hc; push_neg at hc
      nlinarith
    nlinarith

/-- (B) the only edge decomposition of `n b` (`1 <= n < k`) is `(0,n,0)` -/
theorem lemma30_B {n p q r : ℤ} (hn : 1 ≤ n) (hnk : n < k) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (h : p * (k * m) + q * (k ^ 2 - m ^ 2) + r * k ^ 2 = n * (k ^ 2 - m ^ 2)) :
    p = 0 ∧ q = n ∧ r = 0 := by
  obtain ⟨ξ, η, e1, e2, e3⟩ := lemma30_lattice k m p (q - n) r (by linarith) hcop (by linear_combination h)
  have hη : 0 ≤ η := by
    by_contra hc; push_neg at hc
    nlinarith
  rcases hη.eq_or_lt with h0 | h1
  · subst h0
    have hξ : ξ = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hl | hg
      · nlinarith
      · nlinarith
    subst hξ
    refine ⟨by linarith, by linarith, by linarith⟩
  · exfalso
    have hξ1 : -η < ξ := by
      by_contra hc; push_neg at hc
      nlinarith
    have hξ2 : ξ < -η := by
      by_contra hc; push_neg at hc
      nlinarith
    linarith

/-- (C) every edge decomposition of `n c` (`1 <= n < k`) has `q = 0` -/
theorem lemma30_C {n p q r : ℤ} (hn : 1 ≤ n) (hnk : n < k) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (h : p * (k * m) + q * (k ^ 2 - m ^ 2) + r * k ^ 2 = n * k ^ 2) : q = 0 := by
  obtain ⟨ξ, η, e1, e2, e3⟩ := lemma30_lattice k m p q (r - n) (by linarith) hcop (by linear_combination h)
  have hη := eta_nonneg hm hmk hcop hq e2
  rcases hη.eq_or_lt with h0 | h1
  · rw [e2, ← h0]; ring
  · exfalso
    have hξ : 1 - η ≤ ξ := by
      by_contra hc; push_neg at hc
      nlinarith
    nlinarith

/-- (D) `m (b + 2c)` with `r >= k`: only `(0, m, 2m)` (so none if `2m < k`) -/
theorem lemma30_D {p q r : ℤ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : k ≤ r)
    (h : p * (k * m) + q * (k ^ 2 - m ^ 2) + r * k ^ 2 = m * ((k ^ 2 - m ^ 2) + 2 * k ^ 2)) :
    p = 0 ∧ q = m ∧ r = 2 * m := by
  obtain ⟨ξ, η, e1, e2, e3⟩ := lemma30_lattice k m p (q - m) (r - 2 * m) (by linarith) hcop
    (by linear_combination h)
  have hη : 0 ≤ η := by
    by_contra hc; push_neg at hc
    nlinarith
  rcases hη.eq_or_lt with h0 | h1
  · subst h0
    have hξ : ξ = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hl | hg
      · nlinarith
      · nlinarith
    subst hξ
    refine ⟨by linarith, by linarith, by linarith⟩
  · exfalso
    have hξ : 1 - η ≤ ξ := by
      by_contra hc; push_neg at hc
      nlinarith
    nlinarith

/-- (E) `m (b + c)`: no edge decomposition has `r >= k` -/
theorem lemma30_E {p q r : ℤ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : k ≤ r)
    (h : p * (k * m) + q * (k ^ 2 - m ^ 2) + r * k ^ 2 = m * ((k ^ 2 - m ^ 2) + k ^ 2)) : False := by
  obtain ⟨ξ, η, e1, e2, e3⟩ := lemma30_lattice k m p (q - m) (r - m) (by linarith) hcop
    (by linear_combination h)
  have hη : 0 ≤ η := by
    by_contra hc; push_neg at hc
    nlinarith
  rcases hη.eq_or_lt with h0 | h1
  · subst h0
    have hξ : 0 ≤ ξ := by
      by_contra hc; push_neg at hc
      nlinarith
    nlinarith
  · have hξ : 1 - η ≤ ξ := by
      by_contra hc; push_neg at hc
      nlinarith
    nlinarith

end parts

/-- Witness for the hypotheses of (D) and its conclusion: the tile `(6,5,9)` (`k = 3`, `m = 2`) has the edge
decomposition `(0,2,4)` of `m (b + 2c) = 46` with `r = 4 >= k`. -/
theorem lemma30_D_wit : ∃ (k m p q r : ℤ), 0 < m ∧ m < k ∧ IsCoprime m k ∧ 0 ≤ p ∧ 0 ≤ q ∧ k ≤ r ∧
    p * (k * m) + q * (k ^ 2 - m ^ 2) + r * k ^ 2 = m * ((k ^ 2 - m ^ 2) + 2 * k ^ 2) ∧
    p = 0 ∧ q = m ∧ r = 2 * m :=
  ⟨3, 2, 0, 2, 4, by norm_num, by norm_num, ⟨-1, 1, by norm_num⟩, by norm_num, by norm_num, by norm_num,
    by norm_num, rfl, rfl, by norm_num⟩

/-- Witness for (A): `n = 2 < k = 3`, tile `(6,5,9)`, decomposition `(2,0,0)`. -/
theorem lemma30_A_wit : (2 : ℤ) * (3 * 2) + 0 * (3 ^ 2 - 2 ^ 2) + 0 * 3 ^ 2 = 2 * (3 * 2) := by norm_num

end Erdos634.BeesonRowL30

#print axioms Erdos634.BeesonRowL30.lemma30_D
