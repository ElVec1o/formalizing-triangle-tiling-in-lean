-- Draft/LaczFormal32b.lean -- Laczkovich, DCG 19 (1998) Lemma 10 (minimal systems) and DCG 48 (2012) Lemma 3.2, ARITHMETIC form.
-- Statement: for reals x,y,z > 0 with x+y+z = 1, a finite set C of "corner" rows with values a_k in (0,2), a_k != 1, sum_{k in C} a_k < |C|, and
-- natural vectors (p_k,q_k,r_k) (rows k in a finite type) with p x + q y + r z = c_k, c_k in {a_k, a_k - 1} on C and in {0,1,2} off C,
-- sum p = sum q = sum r, and irregularity (p != q somewhere, p != r somewhere, q != r somewhere): x, y, z lie in the Q-span of {1} u {a_k}.
-- Proof: Laczkovich's minimisation (subtract (1,1,1) from a row with all entries positive) + Lemma 10 (D_ij != 0 for some pair) + Cramer.
-- NOT included: the translation of a tiling into such a system (vertex classification).  Label NOTE, UNAUDITED.
-- Credit: Laczkovich (DCG 19 (1998) Lemma 10; DCG 48 (2012) Lemma 3.2; Combinatorica 10 (1990)), Beeson, Beeson-Zhang.
import Mathlib
import Erdos634.Draft.LaczFormal32a
import Erdos634.Draft.LaczFormalLem32

open scoped BigOperators

namespace Erdos634.Draft.LaczFormal32

structure Good {ι : Type*} [Fintype ι] (C : Finset ι) (a : ι → ℝ) (x y z : ℝ) (P Q R : ι → ℕ) (c : ι → ℝ) : Prop where
  hE : ∀ k, (P k : ℝ) * x + Q k * y + R k * z = c k
  hcC : ∀ k ∈ C, c k = a k ∨ c k = a k - 1
  hcO : ∀ k ∉ C, c k = 0 ∨ c k = 1 ∨ c k = 2
  s1 : ∑ k, P k = ∑ k, Q k
  s2 : ∑ k, Q k = ∑ k, R k
  iv1 : ∃ i, P i ≠ Q i
  iv2 : ∃ i, P i ≠ R i
  iv3 : ∃ i, Q i ≠ R i

theorem coreR0 {ι : Type*} [Fintype ι] [DecidableEq ι] (C : Finset ι) (a c : ι → ℝ) (x y z : ℝ)
    (P Q R : ι → ℕ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hsum1 : x + y + z = 1)
    (hE : ∀ k, (P k : ℝ) * x + Q k * y + R k * z = c k)
    (hcC : ∀ k ∈ C, c k = a k ∨ c k = a k - 1)
    (hcO : ∀ k ∉ C, c k = 0 ∨ c k = 1 ∨ c k = 2)
    (haC : ∀ k ∈ C, 0 < a k ∧ a k < 2 ∧ a k ≠ 1)
    (hsumA : ∑ k ∈ C, a k < C.card)
    (hPR : ∑ k, P k = ∑ k, R k) (hQR : ∑ k, Q k = ∑ k, R k)
    (hD : ∀ i j, ((Q i : ℤ) * R j - R i * Q j) - (P i * R j - R i * P j) + (P i * Q j - Q i * P j) = 0)
    (hmin : ∀ k, P k = 0 ∨ Q k = 0 ∨ R k = 0)
    (hnd : ∀ k, 0 < R k → ¬ (P k = 0 ∧ Q k = 0))
    (i : ι) (hiC : i ∈ C) (hai : a i < 1) (hRi : R i = 0) (hPi : 0 < P i) (hQi : 0 < Q i) : False := by
  have hex : ∃ j, 0 < R j := by
    by_contra h
    push Not at h
    have h0 : ∑ k, R k = 0 := Finset.sum_eq_zero (fun k _ => by have := h k; omega)
    rw [← hPR] at h0
    have := (Finset.sum_eq_zero_iff.1 h0) i (Finset.mem_univ _)
    omega
  obtain ⟨j0, hj0⟩ := hex
  rcases hmin j0 with h | h | h
  · -- P j0 = 0, so Q j0 > 0: swap P and Q
    exact coreA C a c y x z Q P R hy hx hz (by linarith) (fun k => by have := hE k; linarith)
      hcC hcO haC hsumA hQR
      (fun i j => by have := hD i j; linarith)
      (fun k => by have := hmin k; tauto)
      (fun k hk => by have := hnd k hk; tauto) i hiC hai hRi hQi hPi j0 hj0 h
  · exact coreA C a c x y z P Q R hx hy hz hsum1 hE hcC hcO haC hsumA hPR hD hmin hnd i hiC hai hRi hPi hQi j0 hj0 h
  · omega

theorem lemma10_min {ι : Type*} [Fintype ι] [DecidableEq ι] {C : Finset ι} {a c : ι → ℝ} {x y z : ℝ}
    {P Q R : ι → ℕ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hsum1 : x + y + z = 1)
    (haC : ∀ k ∈ C, 0 < a k ∧ a k < 2 ∧ a k ≠ 1)
    (hsumA : ∑ k ∈ C, a k < C.card)
    (G : Good C a x y z P Q R c)
    (hmin : ∀ k, P k = 0 ∨ Q k = 0 ∨ R k = 0) :
    ∃ i j, LaczFormal.detD (P i) (Q i) (R i) (P j) (Q j) (R j) ≠ 0 := by
  by_contra hne
  push Not at hne
  have hD : ∀ i j, ((Q i : ℤ) * R j - R i * Q j) - (P i * R j - R i * P j) + (P i * Q j - Q i * P j) = 0 := by
    intro i j; have := hne i j; unfold LaczFormal.detD at this; exact this
  obtain ⟨i, hiC, hai⟩ : ∃ i ∈ C, a i < 1 := by
    by_contra h
    push Not at h
    have := Finset.card_nsmul_le_sum C a 1 h
    simp at this; linarith
  have hEi := G.hE i
  have hc0 : 0 ≤ c i := by rw [← hEi]; positivity
  have hci : c i = a i := by
    rcases G.hcC i hiC with h | h
    · exact h
    · linarith
  have hlive : ¬ (P i = 0 ∧ Q i = 0 ∧ R i = 0) := by
    rintro ⟨h1, h2, h3⟩
    have e1 : (P i : ℝ) = 0 := by simp [h1]
    have e2 : (Q i : ℝ) = 0 := by simp [h2]
    have e3 : (R i : ℝ) = 0 := by simp [h3]
    rw [e1, e2, e3] at hEi
    have := (haC i hiC).1
    linarith
  have hnd1 : ∀ k, P k = 0 → Q k = 0 → R k = 0 := by
    intro k h1 h2
    by_contra h3
    obtain ⟨i1, hi1⟩ := G.iv1
    apply hi1
    have := hD k i1
    simp only [h1, h2, Nat.cast_zero] at this
    have h4 : (R k : ℤ) * (P i1 - Q i1) = 0 := by linarith
    have h5 : (R k : ℤ) ≠ 0 := by exact_mod_cast h3
    have h6 : (P i1 : ℤ) = Q i1 := by
      rcases mul_eq_zero.1 h4 with h | h
      · exact absurd h h5
      · linarith
    exact_mod_cast h6
  have hnd2 : ∀ k, P k = 0 → R k = 0 → Q k = 0 := by
    intro k h1 h2
    by_contra h3
    obtain ⟨i1, hi1⟩ := G.iv2
    apply hi1
    have := hD k i1
    simp only [h1, h2, Nat.cast_zero] at this
    have h4 : (Q k : ℤ) * (R i1 - P i1) = 0 := by linarith
    have h5 : (Q k : ℤ) ≠ 0 := by exact_mod_cast h3
    have h6 : (P i1 : ℤ) = R i1 := by
      rcases mul_eq_zero.1 h4 with h | h
      · exact absurd h h5
      · linarith
    exact_mod_cast h6
  have hnd3 : ∀ k, Q k = 0 → R k = 0 → P k = 0 := by
    intro k h1 h2
    by_contra h3
    obtain ⟨i1, hi1⟩ := G.iv3
    apply hi1
    have := hD k i1
    simp only [h1, h2, Nat.cast_zero] at this
    have h4 : (P k : ℤ) * (Q i1 - R i1) = 0 := by linarith
    have h5 : (P k : ℤ) ≠ 0 := by exact_mod_cast h3
    have h6 : (Q i1 : ℤ) = R i1 := by
      rcases mul_eq_zero.1 h4 with h | h
      · exact absurd h h5
      · linarith
    exact_mod_cast h6
  rcases hmin i with h | h | h
  · -- P i = 0
    have hQi : 0 < Q i := Nat.pos_of_ne_zero (fun h' => hlive ⟨h, h', hnd1 i h h'⟩)
    have hRi : 0 < R i := Nat.pos_of_ne_zero (fun h' => hlive ⟨h, hnd2 i h h', h'⟩)
    exact coreR0 C a c y z x Q R P hy hz hx (by linarith) (fun k => by have := G.hE k; linarith)
      G.hcC G.hcO haC hsumA G.s1.symm (G.s1.trans G.s2).symm
      (fun i j => by linear_combination hD i j)
      (fun k => by have := hmin k; tauto)
      (fun k hk => by intro hh; have := hnd3 k hh.1 hh.2; omega) i hiC hai h hQi hRi
  · -- Q i = 0
    have hPi : 0 < P i := Nat.pos_of_ne_zero (fun h' => hlive ⟨h', h, hnd1 i h' h⟩)
    have hRi : 0 < R i := Nat.pos_of_ne_zero (fun h' => hlive ⟨hnd3 i h h', h, h'⟩)
    exact coreR0 C a c x z y P R Q hx hz hy (by linarith) (fun k => by have := G.hE k; linarith)
      G.hcC G.hcO haC hsumA G.s1 G.s2.symm
      (fun i j => by linear_combination (-1 : ℤ) * hD i j)
      (fun k => by have := hmin k; tauto)
      (fun k hk => by intro hh; have := hnd2 k hh.1 hh.2; omega) i hiC hai h hPi hRi
  · -- R i = 0
    have hPi : 0 < P i := Nat.pos_of_ne_zero (fun h' => hlive ⟨h', hnd2 i h' h, h⟩)
    have hQi : 0 < Q i := Nat.pos_of_ne_zero (fun h' => hlive ⟨hnd3 i h' h, h', h⟩)
    exact coreR0 C a c x y z P Q R hx hy hz hsum1 G.hE G.hcC G.hcO haC hsumA (G.s1.trans G.s2) G.s2 hD hmin
      (fun k hk => by intro hh; have := hnd1 k hh.1 hh.2; omega) i hiC hai h hPi hQi

end Erdos634.Draft.LaczFormal32
