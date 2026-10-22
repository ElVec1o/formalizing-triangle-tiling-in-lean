import Mathlib
import Erdos634.Gamma2Alpha

/-!
# Beeson, "Tilings of an isosceles triangle" (arXiv 1206.1974 v7), arithmetic lemmas of Sections 11 and 12

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.1974 v7, Sect. 11 and 12; arXiv 1206.2229), Laczkovich
(DCG 48 (2012)), Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.  Pure arithmetic, no tiling
hypotheses and NO use of H1 (alpha not in Q pi): the tiling theorems consume these.

* Lemma 11.2 (converse, and the bound `2k > m` that the printed statement carries): `l11_2_conv`, `l11_2_fwd`
  (the forward direction without the bound is `gamma2alpha_param`).
* Lemma 11.3 (side ratios): `l11_3`.
* Lemma 11.6 (squarefree part of `N` and of `b` agree; if `N` squarefree then `b = N l^2`): `l11_6`,
  `l11_6_sqfree`, and the passage from the area equation `X^2 = N k^2 b`: `sq_of_area`.
* Lemma 12.6 (pairwise coprime), Lemma 12.7 (`2b+a` coprime to `a`, `b`, `c` up to 2), Lemma 12.9 (i),(ii) in
  arithmetic form (the area equation `X^2 (2b+a) = N b c^2` with integer `X`): `l12_6`, `l12_7`, `l12_9_arith`.
Witnesses (hypotheses satisfied): `(4,5,6)` with `(k,m) = (2,3)`; `(3,5,7)` for `c^2 = a^2+b^2+ab` with
the 2673-tiling's `N = m^2 a (b+2a)`, `m = 9` (area equation checked numerically below).
-/

namespace Erdos634.Draft.BeesonIsoArith

/-! ## Lemma 11.2 -/

/-- Lemma 11.2, converse: `(k^2, m^2-k^2, km)` with `k < m < 2k` coprime is a triangle with `c^2 = a^2+ab`,
integer sides with no common factor. -/
theorem l11_2_conv (k m a b c : ℕ) (hcop : Nat.Coprime k m) (h1 : k < m) (h2 : m < 2 * k)
    (ha : a = k ^ 2) (hb : b + k ^ 2 = m ^ 2) (hc : c = k * m) :
    c ^ 2 = a ^ 2 + a * b ∧ c < a + b ∧ b < a + c ∧ a < b + c ∧ Nat.gcd (Nat.gcd a b) c = 1 := by
  subst ha hc
  have hab : k ^ 2 + b = m ^ 2 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have : (k * m) ^ 2 = k ^ 2 * (k ^ 2 + b) := by rw [hab]; ring
    rw [this]; ring
  · nlinarith
  · nlinarith
  · nlinarith
  · have hg1 : Nat.gcd (Nat.gcd (k ^ 2) b) (k * m) ∣ k ^ 2 :=
      (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
    have hg2 : Nat.gcd (Nat.gcd (k ^ 2) b) (k * m) ∣ b :=
      (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
    have hg3 : Nat.gcd (Nat.gcd (k ^ 2) b) (k * m) ∣ m ^ 2 := by
      rw [← hab]; exact dvd_add hg1 hg2
    have hc2 : Nat.Coprime (k ^ 2) (m ^ 2) := Nat.Coprime.pow 2 2 hcop
    have := Nat.dvd_gcd hg1 hg3
    rw [hc2.gcd_eq_one] at this
    exact Nat.dvd_one.mp this

/-- Lemma 11.2, forward with the bound: integer sides, no common factor, `c^2 = a^2 + ab`, `b < a + c`
(triangle inequality) give `(a,b,c) = (k^2, m^2-k^2, km)`, `k < m < 2k`, `k, m` coprime. -/
theorem l11_2_fwd (a b c : ℕ) (hb : 0 < b) (hc : c ^ 2 = a ^ 2 + a * b)
    (hcop : Nat.gcd (Nat.gcd a b) c = 1) (htri : b < a + c) :
    ∃ k m : ℕ, Nat.Coprime k m ∧ k < m ∧ m < 2 * k ∧ a = k ^ 2 ∧ b + k ^ 2 = m ^ 2 ∧ c = k * m := by
  obtain ⟨k, m, hkm, hlt, hak, hbm, hckm⟩ := gamma2alpha_param a b c hb hc hcop
  have hb' : b + k ^ 2 = m ^ 2 := by
    have : k ^ 2 < m ^ 2 := by nlinarith
    omega
  refine ⟨k, m, hkm, hlt, ?_, hak, hb', hckm⟩
  by_contra hh
  push_neg at hh
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hh
  subst hak hckm
  nlinarith

/-! ## Lemma 11.3 -/

/-- Lemma 11.3: for a triangle with `c^2 = a^2 + ab` (angles `(alpha, beta, 2 alpha)`):
`a/c > 1/2`, `a/b > 1/3`, `c/b > 2/3`; and if `b < a` then `a/c > 1/sqrt 2`. -/
theorem l11_3 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : c ^ 2 = a ^ 2 + a * b)
    (t2 : b < a + c) :
    1 / 2 < a / c ∧ 1 / 3 < a / b ∧ 2 / 3 < c / b ∧ (b < a → 1 / Real.sqrt 2 < a / c) := by
  have hc2 : c < 2 * a := by
    by_contra hh
    push_neg at hh
    nlinarith [mul_nonneg (sub_nonneg.2 hh) (by positivity : (0 : ℝ) ≤ c + a), mul_pos ha (sub_pos.2 t2)]
  have hb3 : b < 3 * a := by
    have : c ^ 2 < 4 * a ^ 2 := by nlinarith
    nlinarith
  have hcb : 2 * b < 3 * c := by
    -- 3 a c > 2 (c^2 - a^2) = 2 a b  <=>  2c^2 - 3ac - 2a^2 < 0
    have : a * (2 * b) < a * (3 * c) := by nlinarith
    exact lt_of_mul_lt_mul_left this ha.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ hc]; linarith
  · rw [lt_div_iff₀ hb]; linarith
  · rw [lt_div_iff₀ hb]; linarith
  · intro hba
    have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hc2' : c ^ 2 < 2 * a ^ 2 := by nlinarith
    have hlt : c < a * Real.sqrt 2 := by
      by_contra hh
      push_neg at hh
      have hm := mul_le_mul hh hh (by positivity) (by positivity)
      have : a * Real.sqrt 2 * (a * Real.sqrt 2) = 2 * a ^ 2 := by
        rw [show a * Real.sqrt 2 * (a * Real.sqrt 2) = a ^ 2 * (Real.sqrt 2 * Real.sqrt 2) by ring, hs2]; ring
      nlinarith
    rw [div_lt_div_iff₀ hs0 hc]; linarith

/-! ## Lemma 11.6 -/

/-- Two squarefree positive numbers whose product is a square are equal. -/
theorem sqfree_eq_of_mul_square {s t w : ℕ} (hs : Squarefree s) (ht : Squarefree t) (hst : s * t = w ^ 2)
    (hs0 : 0 < s) (ht0 : 0 < t) : s = t := by
  obtain ⟨s', t', hcop, hs', ht'⟩ := Nat.exists_coprime s t
  set g := Nat.gcd s t with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ hs0
  have hg2 : g ^ 2 ∣ w ^ 2 := ⟨s' * t', by rw [← hst, hs', ht']; ring⟩
  obtain ⟨w', hw'⟩ := (Nat.pow_dvd_pow_iff (by norm_num)).mp hg2
  have hsq : s' * t' = w' ^ 2 := by
    have h1 : g ^ 2 * (s' * t') = g ^ 2 * w' ^ 2 := by
      calc g ^ 2 * (s' * t') = s * t := by rw [hs', ht']; ring
        _ = w ^ 2 := hst
        _ = g ^ 2 * w' ^ 2 := by rw [hw']; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  have hu : IsUnit (gcd s' t') := by rw [Nat.isUnit_iff]; exact hcop
  have hu' : IsUnit (gcd t' s') := by rw [Nat.isUnit_iff]; exact hcop.symm
  obtain ⟨x, hx⟩ := exists_eq_pow_of_mul_eq_pow hu hsq
  obtain ⟨y, hy⟩ := exists_eq_pow_of_mul_eq_pow hu' (by rw [mul_comm]; exact hsq)
  have hx1 : x = 1 := by
    have : x * x ∣ s := ⟨g, by rw [hs', hx]; ring⟩
    exact Nat.isUnit_iff.mp (hs x this)
  have hy1 : y = 1 := by
    have : y * y ∣ t := ⟨g, by rw [ht', hy]; ring⟩
    exact Nat.isUnit_iff.mp (ht y this)
  rw [hs', ht', hx, hy, hx1, hy1]

/-- Lemma 11.6 (arithmetic core): if `N b` is a square (`N, b > 0`) then `N` and `b` have the same squarefree part
`s`: `N = u^2 s`, `b = v^2 s`, `s` squarefree.  Hence the squarefree part of `N` divides `b` and conversely. -/
theorem l11_6 (N b : ℕ) (hN : 0 < N) (hb : 0 < b) (hsq : ∃ w, N * b = w ^ 2) :
    ∃ s u v : ℕ, Squarefree s ∧ 0 < s ∧ N = u ^ 2 * s ∧ b = v ^ 2 * s ∧ s ∣ N ∧ s ∣ b := by
  obtain ⟨s, u, hs0, hu0, hu, hsf⟩ := Nat.sq_mul_squarefree_of_pos hN
  obtain ⟨t, v, ht0, hv0, hv, htf⟩ := Nat.sq_mul_squarefree_of_pos hb
  obtain ⟨w, hw⟩ := hsq
  have huv : (u * v) ^ 2 ∣ w ^ 2 := ⟨s * t, by rw [← hw, ← hu, ← hv]; ring⟩
  obtain ⟨z, hz⟩ := (Nat.pow_dvd_pow_iff (by norm_num)).mp huv
  have hst : s * t = z ^ 2 := by
    have h1 : (u * v) ^ 2 * (s * t) = (u * v) ^ 2 * z ^ 2 := by
      calc (u * v) ^ 2 * (s * t) = N * b := by rw [← hu, ← hv]; ring
        _ = w ^ 2 := hw
        _ = (u * v) ^ 2 * z ^ 2 := by rw [hz]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  have hteq : s = t := sqfree_eq_of_mul_square hsf htf hst hs0 ht0
  subst hteq
  exact ⟨s, u, v, hsf, hs0, hu.symm, hv.symm, ⟨u ^ 2, by rw [← hu]; ring⟩, ⟨v ^ 2, by rw [← hv]; ring⟩⟩

/-- Lemma 11.6, squarefree case: `N` squarefree and `N b` a square give `b = N l^2`. -/
theorem l11_6_sqfree (N b : ℕ) (hN : 0 < N) (hb : 0 < b) (hNsq : Squarefree N) (hsq : ∃ w, N * b = w ^ 2) :
    ∃ l : ℕ, b = N * l ^ 2 := by
  obtain ⟨s, u, v, hs, hs0, hNu, hbv, -, -⟩ := l11_6 N b hN hb hsq
  have hu1 : u = 1 := by
    have : u * u ∣ N := ⟨s, by rw [hNu]; ring⟩
    exact Nat.isUnit_iff.mp (hNsq u this)
  subst hu1
  refine ⟨v, ?_⟩
  rw [hbv]; simp at hNu; rw [← hNu]; ring

/-- From the area equation `X^2 = N k^2 b` (tile side `a = k^2`, `X` integer) to `N b = z^2`. -/
theorem sq_of_area (k X N b : ℕ) (hk : 0 < k) (h : X ^ 2 = N * k ^ 2 * b) : ∃ z, N * b = z ^ 2 := by
  have hd : k ^ 2 ∣ X ^ 2 := ⟨N * b, by rw [h]; ring⟩
  obtain ⟨z, hz⟩ := (Nat.pow_dvd_pow_iff (by norm_num)).mp hd
  refine ⟨z, ?_⟩
  have h1 : k ^ 2 * (N * b) = k ^ 2 * z ^ 2 := by
    calc k ^ 2 * (N * b) = N * k ^ 2 * b := by ring
      _ = X ^ 2 := h.symm
      _ = k ^ 2 * z ^ 2 := by rw [hz]; ring
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h1

/-! ## Lemmas 12.6, 12.7, 12.9 -/

/-- Lemma 12.6: `c^2 = a^2+b^2+ab`, no common factor, give pairwise coprime. -/
theorem l12_6 (a b c : ℕ) (hrel : c ^ 2 = a ^ 2 + b ^ 2 + a * b) (hg : Nat.gcd (Nat.gcd a b) c = 1) :
    Nat.Coprime a b ∧ Nat.Coprime b c ∧ Nat.Coprime a c := by
  have key : ∀ p : ℕ, p.Prime → p ∣ a → p ∣ b → p ∣ c → False := by
    intro p hp h1 h2 h3
    have : p ∣ Nat.gcd (Nat.gcd a b) c := Nat.dvd_gcd (Nat.dvd_gcd h1 h2) h3
    rw [hg] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  refine ⟨?_, ?_, ?_⟩
  · apply Nat.coprime_of_dvd
    intro p hp h1 h2
    apply key p hp h1 h2
    exact hp.dvd_of_dvd_pow (n := 2) (by
      rw [hrel]; exact dvd_add (dvd_add (dvd_pow h1 two_ne_zero) (dvd_pow h2 two_ne_zero))
        (dvd_mul_of_dvd_left h1 b))
  · apply Nat.coprime_of_dvd
    intro p hp hb hc
    have e1 : p ∣ a ^ 2 + (b ^ 2 + a * b) := by
      rw [show a ^ 2 + (b ^ 2 + a * b) = c ^ 2 by linarith]; exact dvd_pow hc two_ne_zero
    have e2 : p ∣ b ^ 2 + a * b := dvd_add (dvd_pow hb two_ne_zero) (dvd_mul_of_dvd_right hb a)
    have e3 : p ∣ a ^ 2 := (Nat.dvd_add_left e2).mp e1
    exact key p hp (hp.dvd_of_dvd_pow e3) hb hc
  · apply Nat.coprime_of_dvd
    intro p hp ha hc
    have e1 : p ∣ b ^ 2 + (a ^ 2 + a * b) := by
      rw [show b ^ 2 + (a ^ 2 + a * b) = c ^ 2 by linarith]; exact dvd_pow hc two_ne_zero
    have e2 : p ∣ a ^ 2 + a * b := dvd_add (dvd_pow ha two_ne_zero) (dvd_mul_of_dvd_left ha b)
    have e3 : p ∣ b ^ 2 := (Nat.dvd_add_left e2).mp e1
    exact key p hp ha (hp.dvd_of_dvd_pow e3) hc

/-- Lemma 12.7: for `c^2 = a^2+b^2+ab`, no common factor: `2b+a` is coprime to `b` and to `c`, and
`gcd(2b+a, a) = gcd(2, a)` (so coprime to `a` unless `a` is even, when the gcd is 2). -/
theorem l12_7 (a b c : ℕ) (hrel : c ^ 2 = a ^ 2 + b ^ 2 + a * b) (hg : Nat.gcd (Nat.gcd a b) c = 1) :
    Nat.Coprime (2 * b + a) b ∧ Nat.Coprime (2 * b + a) c ∧ Nat.gcd (2 * b + a) a = Nat.gcd 2 a := by
  obtain ⟨hab, hbc, hac⟩ := l12_6 a b c hrel hg
  refine ⟨?_, ?_, ?_⟩
  · apply Nat.coprime_of_dvd
    intro p hp h1 h2
    have : p ∣ a := (Nat.dvd_add_right (dvd_mul_of_dvd_right h2 2)).mp h1
    have h' : p ∣ Nat.gcd a b := Nat.dvd_gcd this h2
    rw [hab.gcd_eq_one] at h'
    exact hp.one_lt.ne' (Nat.dvd_one.mp h')
  · apply Nat.coprime_of_dvd
    intro p hp h1 hc
    have h4 : 4 * c ^ 2 = (2 * b + a) ^ 2 + 3 * a ^ 2 := by nlinarith [hrel]
    have h3a : p ∣ 3 * a ^ 2 := by
      have e1 : p ∣ (2 * b + a) ^ 2 + 3 * a ^ 2 := by
        rw [← h4]; exact dvd_mul_of_dvd_right (dvd_pow hc two_ne_zero) 4
      exact (Nat.dvd_add_right (dvd_pow h1 two_ne_zero)).mp e1
    rcases (Nat.Prime.dvd_mul hp).mp h3a with h3 | h3
    · have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
      subst hp3
      obtain ⟨t, ht⟩ := h1
      obtain ⟨s, hs⟩ := hc
      have hrelZ : ((3 * s : ℕ) : ℤ) ^ 2 = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (a : ℤ) * b := by
        rw [← hs]; exact_mod_cast hrel
      have ha' : (a : ℤ) = 3 * t - 2 * b := by
        have : ((2 * b + a : ℕ) : ℤ) = ((3 * t : ℕ) : ℤ) := by rw [ht]
        push_cast at this; linarith
      have hb3 : (3 : ℤ) ∣ (b : ℤ) ^ 2 := by
        refine ⟨(s : ℤ) ^ 2 + t * b - t ^ 2, ?_⟩
        rw [ha'] at hrelZ
        push_cast at hrelZ
        nlinarith [hrelZ]
      have hb3' : (3 : ℤ) ∣ (b : ℤ) := Int.prime_three.dvd_of_dvd_pow hb3
      have hb3'' : 3 ∣ b := by exact_mod_cast hb3'
      have ha3 : 3 ∣ a := (Nat.dvd_add_right (dvd_mul_of_dvd_right hb3'' 2)).mp ⟨t, ht⟩
      have : 3 ∣ Nat.gcd a b := Nat.dvd_gcd ha3 hb3''
      rw [hab.gcd_eq_one] at this
      exact absurd (Nat.dvd_one.mp this) (by norm_num)
    · have ha2 : p ∣ a := hp.dvd_of_dvd_pow h3
      have : p ∣ Nat.gcd a c := Nat.dvd_gcd ha2 hc
      rw [hac.gcd_eq_one] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  · apply Nat.dvd_antisymm
    · apply Nat.dvd_gcd _ (Nat.gcd_dvd_right _ _)
      have hga : Nat.gcd (2 * b + a) a ∣ a := Nat.gcd_dvd_right _ _
      have hg2b : Nat.gcd (2 * b + a) a ∣ 2 * b := (Nat.dvd_add_left hga).mp (Nat.gcd_dvd_left _ _)
      have hcg : Nat.Coprime (Nat.gcd (2 * b + a) a) b := Nat.Coprime.coprime_dvd_left hga hab
      exact hcg.dvd_of_dvd_mul_right hg2b
    · apply Nat.dvd_gcd _ (Nat.gcd_dvd_right _ _)
      exact dvd_add (dvd_mul_of_dvd_left (Nat.gcd_dvd_left _ _) b) (Nat.gcd_dvd_right _ _)

/-- Lemma 12.9 (i), (ii), arithmetic form: from the area equation `X^2 (2b+a) = N b c^2` (`X` integer, Lemma 12.8)
and `c^2 = a^2+b^2+ab`, no common factor: `2b+a` divides `N`, `N b = (2b+a) m^2`, `X = m c`; with `X Y = N b c`
(second area form, `m > 0`) one gets `Y = m (2b+a)`. -/
theorem l12_9_arith (a b c X N : ℕ) (hb : 0 < b) (hc : 0 < c)
    (hrel : c ^ 2 = a ^ 2 + b ^ 2 + a * b) (hg : Nat.gcd (Nat.gcd a b) c = 1)
    (harea : X ^ 2 * (2 * b + a) = N * b * c ^ 2) :
    (2 * b + a) ∣ N ∧ ∃ m, N * b = (2 * b + a) * m ^ 2 ∧ X = m * c := by
  obtain ⟨-, -, -⟩ := l12_6 a b c hrel hg
  obtain ⟨h1, h2, -⟩ := l12_7 a b c hrel hg
  have hcop : Nat.Coprime (2 * b + a) (b * c ^ 2) := Nat.Coprime.mul_right h1 (Nat.Coprime.pow_right 2 h2)
  have hd : (2 * b + a) ∣ N * (b * c ^ 2) := ⟨X ^ 2, by rw [← mul_assoc, ← harea]; ring⟩
  have hN : (2 * b + a) ∣ N := hcop.dvd_of_dvd_mul_right hd
  obtain ⟨n, hn⟩ := hN
  have hpos : 0 < 2 * b + a := by omega
  have hX : X ^ 2 = n * b * c ^ 2 := by
    have : X ^ 2 * (2 * b + a) = (n * b * c ^ 2) * (2 * b + a) := by rw [harea, hn]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hdv : c ^ 2 ∣ X ^ 2 := ⟨n * b, by rw [hX]; ring⟩
  obtain ⟨m, hm⟩ := (Nat.pow_dvd_pow_iff (by norm_num)).mp hdv
  have hmm : m ^ 2 = n * b := by
    have : c ^ 2 * m ^ 2 = c ^ 2 * (n * b) := by
      calc c ^ 2 * m ^ 2 = X ^ 2 := by rw [hm]; ring
        _ = c ^ 2 * (n * b) := by rw [hX]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  refine ⟨⟨n, hn⟩, m, ?_, by rw [hm]; ring⟩
  rw [hn, hmm]; ring

/-- Lemma 12.9 (ii), base: from `X = m c`, `N b = (2b+a) m^2` and the second area form `X Y = N b c` (`m, c > 0`):
`Y = m (2b+a)`. -/
theorem l12_9_Y (a b c X Y N m : ℕ) (hm : 0 < m) (hc : 0 < c) (hX : X = m * c)
    (hN : N * b = (2 * b + a) * m ^ 2) (hXY : X * Y = N * b * c) : Y = m * (2 * b + a) := by
  have h : (m * c) * Y = (m * c) * (m * (2 * b + a)) := by
    calc (m * c) * Y = N * b * c := by rw [← hX]; exact hXY
      _ = (2 * b + a) * m ^ 2 * c := by rw [hN]
      _ = (m * c) * (m * (2 * b + a)) := by ring
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h

/-- Witness (2673-tiling, `(a,b,c) = (5,3,7)`, `m = 27`, `X = 189`, `Y = 297`). -/
theorem wit_l12_9_Y : (297 : ℕ) = 27 * (2 * 3 + 5) :=
  l12_9_Y 5 3 7 189 297 2673 27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ## Witnesses -/

theorem wit_l11_2 : Nat.Coprime 2 3 ∧ (4 : ℕ) = 2 ^ 2 ∧ (5 : ℕ) + 2 ^ 2 = 3 ^ 2 ∧ (6 : ℕ) = 2 * 3 := by decide

/-- (4,5,6): the hypotheses of `l11_2_conv` hold and its conclusion is instantiated. -/
theorem wit_l11_2_inst :
    (6 : ℕ) ^ 2 = 4 ^ 2 + 4 * 5 ∧ 6 < 4 + 5 ∧ 5 < 4 + 6 ∧ 4 < 5 + 6 ∧ Nat.gcd (Nat.gcd 4 5) 6 = 1 :=
  l11_2_conv 2 3 4 5 6 (by decide) (by norm_num) (by norm_num) rfl (by norm_num) rfl

theorem wit_l11_3 : 1 / 2 < (4 : ℝ) / 6 ∧ 1 / 3 < (4 : ℝ) / 5 ∧ 2 / 3 < (6 : ℝ) / 5 ∧
    ((5 : ℝ) < 4 → 1 / Real.sqrt 2 < 4 / 6) := l11_3 4 5 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- 2673-tiling's tile `(3,5,7)`: `7^2 = 3^2 + 5^2 + 3*5`; area equation `X^2 (2b+a) = N b c^2` with
`X = 189 * 9 ... `: here `N = 2673`, `X = 21 * 9 * ...`; we check the Lemma 12.9 data `m = 9`, `X = m c = 63`... -/
theorem wit_l12_6 : Nat.Coprime 3 5 ∧ Nat.Coprime 5 7 ∧ Nat.Coprime 3 7 :=
  l12_6 3 5 7 (by norm_num) (by decide)

theorem wit_l12_7 : Nat.Coprime (2 * 5 + 3) 5 ∧ Nat.Coprime (2 * 5 + 3) 7 ∧ Nat.gcd (2 * 5 + 3) 3 = Nat.gcd 2 3 :=
  l12_7 3 5 7 (by norm_num) (by decide)

/-- Lemma 12.9 on the 2673-tiling (base angle is the tile's `beta`, so `(a,b,c) = (5,3,7)`): `X = 189`, `N = 2673`;
`2b+a = 11` divides `N`, `m = 27`, `X = m c`. -/
theorem wit_l12_9 : (2 * 3 + 5) ∣ 2673 ∧ ∃ m, 2673 * 3 = (2 * 3 + 5) * m ^ 2 ∧ 189 = m * 7 :=
  l12_9_arith 5 3 7 189 2673 (by norm_num) (by norm_num) (by norm_num) (by decide) (by norm_num)

/-- Lemma 11.6 on the 1125-tiling: tile `(4,5,6)`, `N = 1125 = 3^2 * 5^3`, `b = 5`: `N b = 75^2`, common squarefree part `5`. -/
theorem wit_l11_6 : ∃ s u v : ℕ, Squarefree s ∧ 0 < s ∧ 1125 = u ^ 2 * s ∧ 5 = v ^ 2 * s ∧ s ∣ 1125 ∧ s ∣ 5 :=
  l11_6 1125 5 (by norm_num) (by norm_num) ⟨75, by norm_num⟩

end Erdos634.Draft.BeesonIsoArith

#print axioms Erdos634.Draft.BeesonIsoArith.l11_2_conv
#print axioms Erdos634.Draft.BeesonIsoArith.l11_2_fwd
#print axioms Erdos634.Draft.BeesonIsoArith.l11_3
#print axioms Erdos634.Draft.BeesonIsoArith.l11_6
#print axioms Erdos634.Draft.BeesonIsoArith.l11_6_sqfree
#print axioms Erdos634.Draft.BeesonIsoArith.sq_of_area
#print axioms Erdos634.Draft.BeesonIsoArith.l12_6
#print axioms Erdos634.Draft.BeesonIsoArith.l12_7
#print axioms Erdos634.Draft.BeesonIsoArith.l12_9_arith
#print axioms Erdos634.Draft.BeesonIsoArith.l12_9_Y
#print axioms Erdos634.Draft.BeesonIsoArith.wit_l12_9
#print axioms Erdos634.Draft.BeesonIsoArith.wit_l11_6
