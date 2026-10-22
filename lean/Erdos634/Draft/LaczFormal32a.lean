-- Draft/LaczFormal32a.lean -- Laczkovich, Discrete Comput. Geom. 19 (1998) 411-425 (Tilings of polygons with similar triangles II), Lemma 10, core.
-- NOTE: the "geometric half" of DCG 48 (2012) Lemma 3.2 cites [3, Lemma 10]; [3] is the 1998 DCG 19 paper (NOT the 1990 Combinatorica paper), and
-- Lemma 10 there is purely arithmetic: a statement about integer vertex-count systems (no geometry).  This file: the case analysis
-- ("r_i = 0" branch, shape (1,0,2), counting contradiction with sum a_i < n).  Label NOTE, UNAUDITED.
-- Credit: Laczkovich (DCG 19 (1998) Lemma 10; DCG 48 (2012) Lemma 3.2; Combinatorica 10 (1990)), Beeson, Beeson-Zhang.
import Mathlib

open scoped BigOperators

namespace Erdos634.Draft.LaczFormal32

theorem pair_arith {x y z a c : ℝ} (hsum : x + y + z = 1)
    {s t u v : ℕ} (hs : 0 < s) (ht : 0 < t) (hu : 0 < u) (hv : 0 < v)
    (hD : (t:ℤ) * v = s * v + t * u) (ha : a < 1) (hc : c ≤ 2)
    (hai : a = s * x + t * y) (hcj : c = u * x + v * z) : v = 2 ∧ u = 1 ∧ t = 2 * s := by
  have hDr : (t:ℝ) * v = s * v + t * u := by exact_mod_cast hD
  have hE : (t:ℝ) * v = v * a + t * c := by
    rw [hai, hcj]; linear_combination (-((t:ℝ) * v)) * hsum + x * hDr
  have hv' : (0:ℝ) < v := by exact_mod_cast hv
  have ht' : (0:ℝ) < t := by exact_mod_cast ht
  have hlt : (t:ℝ) * v < v + 2 * t := by nlinarith
  have hlt' : (t:ℤ) * v < v + 2 * t := by exact_mod_cast hlt
  have hDn : t * v = s * v + t * u := by exact_mod_cast hD
  have hltn : t * v < v + 2 * t := by exact_mod_cast hlt'
  have hst : s < t := by
    by_contra h; push Not at h
    nlinarith [Nat.mul_pos ht hu, Nat.mul_le_mul_right v h]
  have huv : u < v := by
    by_contra h; push Not at h
    nlinarith [Nat.mul_le_mul_left t h, Nat.mul_le_mul_right v (Nat.succ_le_of_lt hs)]
  have ht2 : 2 ≤ t := by omega
  have hv2 : 2 ≤ v := by omega
  have hv3 : v ≤ 3 := by
    by_contra h; push Not at h
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 2 := ⟨t - 2, by omega⟩
    obtain ⟨v', rfl⟩ : ∃ v', v = v' + 4 := ⟨v - 4, by omega⟩
    nlinarith [Nat.zero_le (t' * v')]
  interval_cases v
  · have hu1 : u = 1 := by omega
    subst hu1
    refine ⟨rfl, rfl, by omega⟩
  · exfalso
    obtain rfl : t = 2 := by omega
    have : s = 1 := by omega
    subst this
    omega

set_option maxHeartbeats 1600000 in
theorem coreA {ι : Type*} [Fintype ι] [DecidableEq ι] (C : Finset ι) (a c : ι → ℝ) (x y z : ℝ)
    (P Q R : ι → ℕ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hsum1 : x + y + z = 1)
    (hE : ∀ k, (P k : ℝ) * x + Q k * y + R k * z = c k)
    (hcC : ∀ k ∈ C, c k = a k ∨ c k = a k - 1)
    (hcO : ∀ k ∉ C, c k = 0 ∨ c k = 1 ∨ c k = 2)
    (haC : ∀ k ∈ C, 0 < a k ∧ a k < 2 ∧ a k ≠ 1)
    (hsumA : ∑ k ∈ C, a k < C.card)
    (hPR : ∑ k, P k = ∑ k, R k)
    (hD : ∀ i j, ((Q i : ℤ) * R j - R i * Q j) - (P i * R j - R i * P j) + (P i * Q j - Q i * P j) = 0)
    (hmin : ∀ k, P k = 0 ∨ Q k = 0 ∨ R k = 0)
    (hnd : ∀ k, 0 < R k → ¬ (P k = 0 ∧ Q k = 0))
    (i : ι) (hiC : i ∈ C) (hai : a i < 1) (hRi : R i = 0) (hPi : 0 < P i) (hQi : 0 < Q i)
    (j0 : ι) (hj0R : 0 < R j0) (hj0Q : Q j0 = 0) : False := by
  have hcle : ∀ k, c k ≤ 2 := by
    intro k
    by_cases hk : k ∈ C
    · have := (haC k hk).2.1
      rcases hcC k hk with h | h <;> linarith
    · rcases hcO k hk with h | h | h <;> linarith
  have hP' : (0:ℝ) < P i := by exact_mod_cast hPi
  have hQ' : (0:ℝ) < Q i := by exact_mod_cast hQi
  have hRi' : (R i : ℝ) = 0 := by simp [hRi]
  have hEi := hE i
  rw [hRi'] at hEi
  have hci : c i = a i := by
    rcases hcC i hiC with h | h
    · exact h
    · exfalso
      have := mul_pos hP' hx
      have := mul_pos hQ' hy
      linarith
  have hai' : a i = P i * x + Q i * y := by linarith
  have keyA : ∀ j, 0 < R j → Q j = 0 → 0 < P j → (R j = 2 ∧ P j = 1 ∧ Q i = 2 * P i) := by
    intro j hjR hjQ hjP
    have hd := hD i j
    simp only [hRi, hjQ, Nat.cast_zero] at hd
    have hD' : (Q i : ℤ) * R j = P i * R j + Q i * P j := by linarith
    have hEj := hE j
    have hQj' : (Q j : ℝ) = 0 := by simp [hjQ]
    rw [hQj'] at hEj
    obtain ⟨h1, h2, h3⟩ := pair_arith (x := x) (y := y) (z := z) (a := a i) (c := c j) hsum1
      hPi hQi hjP hjR hD' hai (hcle j) hai' (by linarith)
    exact ⟨h1, h2, h3⟩
  have keyB : ∀ j, 0 < R j → P j = 0 → 0 < Q j → (R j = 2 ∧ Q j = 1 ∧ P i = 2 * Q i) := by
    intro j hjR hjP hjQ
    have hd := hD i j
    simp only [hRi, hjP, Nat.cast_zero] at hd
    have hD' : (P i : ℤ) * R j = Q i * R j + P i * Q j := by linarith
    have hEj := hE j
    have hPj' : (P j : ℝ) = 0 := by simp [hjP]
    rw [hPj'] at hEj
    obtain ⟨h1, h2, h3⟩ := pair_arith (x := y) (y := x) (z := z) (a := a i) (c := c j) (by linarith)
      hQi hPi hjQ hjR hD' hai (hcle j) (by linarith) (by linarith)
    exact ⟨h1, h2, h3⟩
  have hj0P : 0 < P j0 := Nat.pos_of_ne_zero (fun h => hnd j0 hj0R ⟨h, hj0Q⟩)
  have hq2 : Q i = 2 * P i := (keyA j0 hj0R hj0Q hj0P).2.2
  have hshape : ∀ j, 0 < R j → P j = 1 ∧ Q j = 0 ∧ R j = 2 := by
    intro j hjR
    rcases hmin j with h | h | h
    · have hjQ : 0 < Q j := Nat.pos_of_ne_zero (fun h' => hnd j hjR ⟨h, h'⟩)
      have := (keyB j hjR h hjQ).2.2
      omega
    · have hjP : 0 < P j := Nat.pos_of_ne_zero (fun h' => hnd j hjR ⟨h', h⟩)
      obtain ⟨h1, h2, -⟩ := keyA j hjR h hjP
      exact ⟨h2, h, h1⟩
    · omega
  have hr0 : ∀ j, R j = 0 → Q j = 2 * P j := by
    intro j hj
    have hd := hD i j
    simp only [hRi, hj, Nat.cast_zero] at hd
    have h1 : (P i : ℤ) * Q j = P i * (2 * P j) := by
      have : (Q i : ℤ) = 2 * P i := by exact_mod_cast hq2
      rw [this] at hd; linarith
    have h2 : P i * Q j = P i * (2 * P j) := by exact_mod_cast h1
    exact Nat.eq_of_mul_eq_mul_left hPi h2
  -- numerics
  have hq2' : (Q i : ℝ) = 2 * P i := by exact_mod_cast hq2
  have hP1 : (1:ℝ) ≤ P i := by exact_mod_cast hPi
  set u : ℝ := x + 2 * y with hu
  have hai2 : a i = P i * u := by rw [hai', hq2', hu]; ring
  have hu1 : u < 1 := by nlinarith
  have hu0 : 0 < u := by rw [hu]; linarith
  have hxz1 : 1 < x + 2 * z := by linarith
  have hxz2 : x + 2 * z = 2 - u := by rw [hu]; linarith
  -- the set R
  have hRC : ∀ j, 0 < R j → j ∈ C ∧ a j = x + 2 * z := by
    intro j hjR
    obtain ⟨h1, h2, h3⟩ := hshape j hjR
    have hEj := hE j
    have hcj : c j = x + 2 * z := by
      rw [h1, h2, h3] at hEj; push_cast at hEj; linarith
    have hjC : j ∈ C := by
      by_contra hn
      rcases hcO j hn with h | h | h <;> linarith
    refine ⟨hjC, ?_⟩
    have := (haC j hjC).2.1
    rcases hcC j hjC with h | h
    · linarith
    · linarith
  -- sums
  classical
  set m : ℕ := (Finset.univ.filter (fun j => 0 < R j)).card with hm
  have hRsum : ∑ k, R k = 2 * m := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => 0 < R j) R]
    have e1 : ∑ k ∈ Finset.univ.filter (fun j => 0 < R j), R k = 2 * m := by
      rw [hm, Finset.card_eq_sum_ones, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k hk => by
        have := (hshape k (Finset.mem_filter.1 hk).2).2.2; omega)
    have e2 : ∑ k ∈ Finset.univ.filter (fun j => ¬ 0 < R j), R k = 0 := by
      apply Finset.sum_eq_zero; intro k hk; have := (Finset.mem_filter.1 hk).2; omega
    omega
  have hPsum : ∑ k, P k = m + ∑ k ∈ Finset.univ.filter (fun j => ¬ 0 < R j), P k := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => 0 < R j) P]
    have e1 : ∑ k ∈ Finset.univ.filter (fun j => 0 < R j), P k = m := by
      rw [hm, Finset.card_eq_sum_ones]
      exact Finset.sum_congr rfl (fun k hk => (hshape k (Finset.mem_filter.1 hk).2).1)
    omega
  have hPn : ∑ k ∈ Finset.univ.filter (fun j => ¬ 0 < R j), P k = m := by omega
  have hCf : C.filter (fun j => 0 < R j) = Finset.univ.filter (fun j => 0 < R j) := by
    ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨(hRC j h).1, h⟩⟩
  set PC : ℕ := ∑ k ∈ C.filter (fun j => ¬ 0 < R j), P k with hPC
  have hPCle : PC ≤ m := by
    rw [← hPn]
    exact Finset.sum_le_sum_of_subset (Finset.monotone_filter_left _ (Finset.subset_univ C) |>.trans (le_refl _))
  have hPCge : (C.filter (fun j => ¬ 0 < R j)).card ≤ PC := by
    rw [Finset.card_eq_sum_ones, hPC]
    apply Finset.sum_le_sum
    intro k hk
    obtain ⟨hkC, hkR⟩ := Finset.mem_filter.1 hk
    have hkR0 : R k = 0 := by omega
    have hq := hr0 k hkR0
    have hEk := hE k
    have hcpos : 0 < c k := by
      have := haC k hkC
      rcases hcC k hkC with h | h
      · linarith [this.1]
      · have hc0 : 0 ≤ c k := by
          rw [← hEk]; positivity
        have : a k ≠ 1 := this.2.2
        rcases hc0.lt_or_eq with h' | h'
        · exact h'
        · exfalso; apply this; linarith
    by_contra hcon
    have hp0 : P k = 0 := by omega
    have : (P k : ℝ) = 0 := by simp [hp0]
    have hq0 : (Q k : ℝ) = 0 := by simp [hq, hp0]
    have hR0' : (R k : ℝ) = 0 := by simp [hkR0]
    rw [this, hq0, hR0'] at hEk
    linarith
  have hcard : m + (C.filter (fun j => ¬ 0 < R j)).card = C.card := by
    have := Finset.card_filter_add_card_filter_not (s := C) (fun j => 0 < R j)
    rw [hCf] at this; exact this
  -- lower bound on sum of a
  have hlow : ∑ k ∈ C, a k ≥ m * (x + 2 * z) + u * PC := by
    rw [← Finset.sum_filter_add_sum_filter_not C (fun j => 0 < R j) a]
    have e1 : ∑ k ∈ C.filter (fun j => 0 < R j), a k = m * (x + 2 * z) := by
      rw [hCf, hm, Finset.card_eq_sum_ones]
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [one_mul]; exact (hRC k (Finset.mem_filter.1 hk).2).2
    have e2 : ∑ k ∈ C.filter (fun j => ¬ 0 < R j), a k ≥ u * PC := by
      rw [hPC]; push_cast; rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨hkC, hkR⟩ := Finset.mem_filter.1 hk
      have hkR0 : R k = 0 := by omega
      have hq := hr0 k hkR0
      have hEk := hE k
      have hqr : (Q k : ℝ) = 2 * P k := by exact_mod_cast hq
      have hR0' : (R k : ℝ) = 0 := by simp [hkR0]
      rw [hqr, hR0'] at hEk
      have : c k = P k * u := by rw [hu]; linarith
      rcases hcC k hkC with h | h <;> nlinarith
    linarith
  have hPCle' : (PC : ℝ) ≤ m := by exact_mod_cast hPCle
  have hPCge' : (C.card : ℝ) - m ≤ PC := by
    have h1 : C.card ≤ m + PC := by omega
    have h2 : (C.card : ℝ) ≤ m + PC := by exact_mod_cast h1
    linarith
  have := mul_nonneg (sub_nonneg.2 hPCle') (sub_nonneg.2 hu1.le)
  rw [hxz2] at hlow
  nlinarith

end Erdos634.Draft.LaczFormal32
