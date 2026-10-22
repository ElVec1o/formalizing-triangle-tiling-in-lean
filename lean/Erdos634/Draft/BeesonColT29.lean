import Mathlib
import Erdos634.Draft.BeesonRowL30

/-!
# Beeson-Rosu (arXiv 2607.23453 v2) Theorem 29: arithmetic of the relation lattice, tile `(km, k^2-m^2, k^2)`

NOTE, UNAUDITED.  Credit: Michael Beeson and Rosu (arXiv 2607.23453 v2, Lemma 28, Theorem 29), Beeson (arXiv 1206.2229 v4),
Laczkovich (DCG 48 (2012)), Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.

`a = m k`, `b = k^2 - m^2`, `c = k^2`, `0 < m < k`, `gcd(m, k) = 1` (here `IsCoprime m k`, integers).  The nine types of the
printed table: for each type, `∃` a relation attaining the printed minimum and every relation of that type is at least the
minimum.  The common quantity is `h a`, `h b` or `h c`; mixed types require `p, q >= 1`.  Pure integer arithmetic (the
lattice of Lemma 28 is `BeesonRowL30.lemma30_lattice`); no hypothesis beyond coprimality and `0 < m < k`; no H1.
The table's lengths are stated as `h * a` etc.
-/

namespace Erdos634.BeesonColT29

variable {k m : ℤ}

theorem cop_kb (hcop : IsCoprime m k) : IsCoprime k (k ^ 2 - m ^ 2) := by
  have h : IsCoprime k (-(m ^ 2)) := (hcop.symm.pow_right (n := 2)).neg_right
  have h3 := h.add_mul_left_right k
  have e : k ^ 2 - m ^ 2 = -(m ^ 2) + k * k := by ring
  rw [e]; exact h3

theorem cop_mb (hcop : IsCoprime m k) : IsCoprime m (k ^ 2 - m ^ 2) := by
  have h : IsCoprime m (k ^ 2) := hcop.pow_right (n := 2)
  have h3 := h.add_mul_left_right (-m)
  have e : k ^ 2 - m ^ 2 = k ^ 2 + m * (-m) := by ring
  rw [e]; exact h3

theorem cop_ab (hcop : IsCoprime m k) : IsCoprime (k * m) (k ^ 2 - m ^ 2) :=
  (cop_kb hcop).mul_left (cop_mb hcop)

/-- type `h a = p b + q c` (p, q >= 1): minimum `h = k ⌊k/m⌋ + k - m`. -/
theorem t29_a_bc (hm : 0 < m) (hmk : m < k) (hcop : IsCoprime m k) :
    (∃ h p q : ℤ, 1 ≤ p ∧ 1 ≤ q ∧ h * (k * m) = p * (k ^ 2 - m ^ 2) + q * k ^ 2 ∧ h = k * (k / m) + k - m) ∧
    ∀ h p q : ℤ, 1 ≤ p → 1 ≤ q → h * (k * m) = p * (k ^ 2 - m ^ 2) + q * k ^ 2 → k * (k / m) + k - m ≤ h := by
  have hk : 0 < k := by linarith
  have hd := Int.ediv_add_emod k m
  have hr0 := Int.emod_nonneg k hm.ne'
  have hr1 := Int.emod_lt_of_pos k hm
  set t := k / m with ht
  set ρ := k % m with hρ
  have ht1 : 1 ≤ t := by
    by_contra hc; push Not at hc
    have : t ≤ 0 := by linarith
    nlinarith
  refine ⟨⟨k * t + k - m, k, (t + 1) * m - k, by linarith, by nlinarith, ?_, rfl⟩, ?_⟩
  · have : k = m * t + ρ := hd.symm
    nlinarith [this]
  · intro h p q hp hq heq
    obtain ⟨ξ, η, e1, e2, e3⟩ := BeesonRowL30.lemma30_lattice k m h (-p) (-q) hk hcop (by linear_combination heq)
    -- p = -η k, q = ξ m + η k, h = ξ k + η m
    have hη : η ≤ -1 := by
      by_contra hc; push Not at hc
      have : 0 ≤ η := by linarith
      nlinarith
    obtain ⟨P, hP⟩ : ∃ P, P = -η := ⟨_, rfl⟩
    have hP1 : 1 ≤ P := by linarith
    have hqq : 1 ≤ ξ * m - P * k := by nlinarith
    have hξ : P * t + 1 ≤ ξ := by
      by_contra hc; push Not at hc
      have h1 : ξ ≤ P * t := by linarith
      have : ξ * m ≤ P * t * m := by nlinarith
      have h2 : k = m * t + ρ := hd.symm
      nlinarith
    have hh : h = ξ * k - P * m := by rw [e1]; nlinarith
    have htk : m ≤ t * k := by nlinarith
    nlinarith

/-- type `h a = p b`: minimum `h = b`, length `a b`. -/
theorem t29_a_b (hm : 0 < m) (hmk : m < k) (hcop : IsCoprime m k) :
    (∃ h p : ℤ, 1 ≤ h ∧ 1 ≤ p ∧ h * (k * m) = p * (k ^ 2 - m ^ 2) ∧ h = k ^ 2 - m ^ 2) ∧
    ∀ h p : ℤ, 1 ≤ h → 1 ≤ p → h * (k * m) = p * (k ^ 2 - m ^ 2) → k ^ 2 - m ^ 2 ≤ h := by
  have hk : 0 < k := by linarith
  have hb : 0 < k ^ 2 - m ^ 2 := by nlinarith
  refine ⟨⟨k ^ 2 - m ^ 2, k * m, by linarith, by nlinarith, by ring, rfl⟩, ?_⟩
  intro h p hh hp heq
  have hcb : IsCoprime (k * m) (k ^ 2 - m ^ 2) := cop_ab hcop
  have hdvd : (k ^ 2 - m ^ 2) ∣ h * (k * m) := ⟨p, by rw [heq]; ring⟩
  have := hcb.symm.dvd_of_dvd_mul_right hdvd
  exact Int.le_of_dvd hh this

/-- type `h a = q c`: minimum `h = k` (length `m k^2 = k a`). -/
theorem t29_a_c (hm : 0 < m) (hmk : m < k) (hcop : IsCoprime m k) :
    (∃ h q : ℤ, 1 ≤ h ∧ 1 ≤ q ∧ h * (k * m) = q * k ^ 2 ∧ h = k) ∧
    ∀ h q : ℤ, 1 ≤ h → 1 ≤ q → h * (k * m) = q * k ^ 2 → k ≤ h := by
  have hk : 0 < k := by linarith
  refine ⟨⟨k, m, by linarith, by linarith, by ring, rfl⟩, ?_⟩
  intro h q hh hq heq
  have h1 : h * m = q * k := by
    apply mul_left_cancel₀ hk.ne'
    linear_combination heq
  have : k ∣ h * m := ⟨q, by rw [h1]; ring⟩
  have := hcop.symm.dvd_of_dvd_mul_right this
  exact Int.le_of_dvd hh this

/-- type `h b = p a + q c` (p, q >= 1): minimum `h = k` (length `k b`). -/
theorem t29_b_ac (hm : 0 < m) (hmk : m < k) (hcop : IsCoprime m k) :
    (∃ h p q : ℤ, 1 ≤ p ∧ 1 ≤ q ∧ h * (k ^ 2 - m ^ 2) = p * (k * m) + q * k ^ 2 ∧ h = k) ∧
    ∀ h p q : ℤ, 1 ≤ h → 1 ≤ p → 1 ≤ q → h * (k ^ 2 - m ^ 2) = p * (k * m) + q * k ^ 2 → k ≤ h := by
  have hk : 0 < k := by linarith
  refine ⟨⟨k, k - m, k - m, by linarith, by linarith, by ring, rfl⟩, ?_⟩
  intro h p q hh hp hq heq
  obtain ⟨ξ, η, e1, e2, e3⟩ := BeesonRowL30.lemma30_lattice k m (-p) h (-q) hk hcop (by linear_combination heq)
  have : 1 ≤ η := by
    by_contra hc; push Not at hc
    nlinarith
  nlinarith

/-- type `h b = p a`: minimum `h = a`, length `a b`. -/
theorem t29_b_a (hm : 0 < m) (hmk : m < k) (hcop : IsCoprime m k) :
    (∃ h p : ℤ, 1 ≤ h ∧ 1 ≤ p ∧ h * (k ^ 2 - m ^ 2) = p * (k * m) ∧ h = k * m) ∧
    ∀ h p : ℤ, 1 ≤ h → 1 ≤ p → h * (k ^ 2 - m ^ 2) = p * (k * m) → k * m ≤ h := by
  have hk : 0 < k := by linarith
  have hb : 0 < k ^ 2 - m ^ 2 := by nlinarith
  have ⟨⟨h0, p0, g1, g2, g3, g4⟩, g5⟩ := t29_a_b hm hmk hcop
  refine ⟨⟨k * m, k ^ 2 - m ^ 2, by nlinarith, by linarith, by ring, rfl⟩, ?_⟩
  intro h p hh hp heq
  have := g5 p h hp hh (by linarith)
  have hh2 : k * m ≤ h := by
    -- from p*(k*m) = h*b with minimal-p version: h ≥ a  (symmetric to t29_a_b)
    have hcb : IsCoprime (k ^ 2 - m ^ 2) (k * m) := (cop_ab hcop).symm
    have hdvd : (k * m) ∣ h * (k ^ 2 - m ^ 2) := ⟨p, by rw [heq]; ring⟩
    have := hcb.symm.dvd_of_dvd_mul_right hdvd
    exact Int.le_of_dvd hh this
  exact hh2

/-- type `h b = q c`: minimum `h = c`, length `b c`. -/
theorem t29_b_c (hm : 0 < m) (hmk : m < k) (hcop : IsCoprime m k) :
    (∃ h q : ℤ, 1 ≤ h ∧ 1 ≤ q ∧ h * (k ^ 2 - m ^ 2) = q * k ^ 2 ∧ h = k ^ 2) ∧
    ∀ h q : ℤ, 1 ≤ h → 1 ≤ q → h * (k ^ 2 - m ^ 2) = q * k ^ 2 → k ^ 2 ≤ h := by
  have hk : 0 < k := by linarith
  have hb : 0 < k ^ 2 - m ^ 2 := by nlinarith
  refine ⟨⟨k ^ 2, k ^ 2 - m ^ 2, by nlinarith, by linarith, by ring, rfl⟩, ?_⟩
  intro h q hh hq heq
  have hcb : IsCoprime (k ^ 2) (k ^ 2 - m ^ 2) := (cop_kb hcop).pow_left
  have hdvd : (k ^ 2) ∣ h * (k ^ 2 - m ^ 2) := ⟨q, by rw [heq]; ring⟩
  have := hcb.dvd_of_dvd_mul_right hdvd
  exact Int.le_of_dvd hh this

/-- type `h c = p a + q b` (p, q >= 1): minimum `h = k` (length `k c`). -/
theorem t29_c_ab (hm : 0 < m) (hmk : m < k) (hcop : IsCoprime m k) :
    (∃ h p q : ℤ, 1 ≤ p ∧ 1 ≤ q ∧ h * k ^ 2 = p * (k * m) + q * (k ^ 2 - m ^ 2) ∧ h = k) ∧
    ∀ h p q : ℤ, 1 ≤ h → 1 ≤ p → 1 ≤ q → h * k ^ 2 = p * (k * m) + q * (k ^ 2 - m ^ 2) → k ≤ h := by
  have hk : 0 < k := by linarith
  refine ⟨⟨k, m, k, by linarith, by linarith, by ring, rfl⟩, ?_⟩
  intro h p q hh hp hq heq
  obtain ⟨ξ, η, e1, e2, e3⟩ := BeesonRowL30.lemma30_lattice k m (-p) (-q) h hk hcop (by linear_combination heq)
  -- -p = ξ k + η m, -q = η k, h = -ξ m - η k
  have hη : η ≤ -1 := by
    by_contra hc; push Not at hc
    nlinarith
  obtain ⟨t, ht⟩ : ∃ t, t = -η := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = -ξ := ⟨_, rfl⟩
  have ht1 : 1 ≤ t := by linarith
  have hh' : h = t * k + s * m := by rw [e3]; nlinarith
  have hp' : p = t * m + s * k := by nlinarith
  have hT : 1 ≤ t + s := by
    have : (t + s) * (k + m) = h + p := by rw [hh', hp']; ring
    by_contra hc; push Not at hc
    have : t + s ≤ 0 := by linarith
    nlinarith
  rcases le_or_gt 0 s with hs0 | hs0
  · nlinarith
  · nlinarith

/-- type `h c = p a`: minimum `h = m`, length `m c` (so `m c = k a`). -/
theorem t29_c_a (hm : 0 < m) (hmk : m < k) (hcop : IsCoprime m k) :
    (∃ h p : ℤ, 1 ≤ h ∧ 1 ≤ p ∧ h * k ^ 2 = p * (k * m) ∧ h = m) ∧
    ∀ h p : ℤ, 1 ≤ h → 1 ≤ p → h * k ^ 2 = p * (k * m) → m ≤ h := by
  have hk : 0 < k := by linarith
  refine ⟨⟨m, k, by linarith, by linarith, by ring, rfl⟩, ?_⟩
  intro h p hh hp heq
  have h1 : h * k = p * m := by
    apply mul_left_cancel₀ hk.ne'
    linear_combination heq
  have : m ∣ h * k := ⟨p, by rw [h1]; ring⟩
  have := hcop.dvd_of_dvd_mul_right this
  exact Int.le_of_dvd hh this

/-- type `h c = q b`: minimum `h = b`, length `b c`. -/
theorem t29_c_b (hm : 0 < m) (hmk : m < k) (hcop : IsCoprime m k) :
    (∃ h q : ℤ, 1 ≤ h ∧ 1 ≤ q ∧ h * k ^ 2 = q * (k ^ 2 - m ^ 2) ∧ h = k ^ 2 - m ^ 2) ∧
    ∀ h q : ℤ, 1 ≤ h → 1 ≤ q → h * k ^ 2 = q * (k ^ 2 - m ^ 2) → k ^ 2 - m ^ 2 ≤ h := by
  have hk : 0 < k := by linarith
  have hb : 0 < k ^ 2 - m ^ 2 := by nlinarith
  refine ⟨⟨k ^ 2 - m ^ 2, k ^ 2, by linarith, by nlinarith, by ring, rfl⟩, ?_⟩
  intro h q hh hq heq
  have hcb : IsCoprime (k ^ 2 - m ^ 2) (k ^ 2) := (cop_kb hcop).pow_left.symm
  have hdvd : (k ^ 2 - m ^ 2) ∣ h * k ^ 2 := ⟨q, by rw [heq]; ring⟩
  have := hcb.dvd_of_dvd_mul_right hdvd
  exact Int.le_of_dvd hh this

/-- Witness (m, k) = (2, 5): the hypotheses of every statement above hold. -/
theorem t29_wit : (0 : ℤ) < 2 ∧ (2 : ℤ) < 5 ∧ IsCoprime (2 : ℤ) 5 :=
  ⟨by norm_num, by norm_num, by rw [Int.isCoprime_iff_gcd_eq_one]; rfl⟩

end Erdos634.BeesonColT29
