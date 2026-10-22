-- Draft/LaczFormal32c.lean -- Laczkovich DCG 48 (2012) Lemma 3.2, ARITHMETIC form: minimisation + Lemma 10 (DCG 19 (1998)) + Cramer.
-- `lemma32_arith`: Good system (vertex-count rows with p x + q y + r z = c, counting sums, irregularity, corner values a_k in (0,2)\{1},
-- sum a_k < |C|) => x, y, z in the Q-span of {1} u {a_k}.  Axioms: see #print axioms below.  Label NOTE, UNAUDITED.
-- Credit: Laczkovich (DCG 19 (1998) Lemma 10; DCG 48 (2012) Lemma 3.2), Beeson, Beeson-Zhang.
import Mathlib
import Erdos634.Draft.LaczFormal32b

open scoped BigOperators

namespace Erdos634.Draft.LaczFormal32

theorem sum_dec {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℕ) (k : ι) (hk : 1 ≤ f k) :
    (∑ j, (if j = k then f j - 1 else f j)) + 1 = ∑ j, f j := by
  have : ∀ j, f j = (if j = k then f j - 1 else f j) + (if j = k then 1 else 0) := by
    intro j; by_cases h : j = k
    · subst h; simp; omega
    · simp [h]
  calc (∑ j, (if j = k then f j - 1 else f j)) + 1
      = ∑ j, ((if j = k then f j - 1 else f j) + (if j = k then 1 else 0)) := by
        rw [Finset.sum_add_distrib]; simp
    _ = ∑ j, f j := (Finset.sum_congr rfl (fun j _ => (this j).symm))

theorem good_dec {ι : Type*} [Fintype ι] [DecidableEq ι] {C : Finset ι} {a c : ι → ℝ} {x y z : ℝ}
    {P Q R : ι → ℕ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hsum1 : x + y + z = 1)
    (haC : ∀ k ∈ C, 0 < a k ∧ a k < 2 ∧ a k ≠ 1)
    (G : Good C a x y z P Q R c) (k : ι) (hP : 0 < P k) (hQ : 0 < Q k) (hR : 0 < R k) :
    Good C a x y z (fun j => if j = k then P j - 1 else P j) (fun j => if j = k then Q j - 1 else Q j)
      (fun j => if j = k then R j - 1 else R j) (fun j => if j = k then c j - 1 else c j) := by
  have hP' : (1:ℝ) ≤ P k := by exact_mod_cast hP
  have hQ' : (1:ℝ) ≤ Q k := by exact_mod_cast hQ
  have hR' : (1:ℝ) ≤ R k := by exact_mod_cast hR
  have hck : 1 ≤ c k := by
    have := G.hE k
    nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases h : j = k
    · subst h
      simp only [if_true]
      rw [Nat.cast_pred hP, Nat.cast_pred hQ, Nat.cast_pred hR]
      have := G.hE j
      linarith
    · simp only [h, if_false]; exact G.hE j
  · intro j hj
    by_cases h : j = k
    · subst h
      simp only [if_true]
      rcases G.hcC j hj with h1 | h1
      · right; linarith
      · have := (haC j hj).2.1; linarith
    · simp only [h, if_false]; exact G.hcC j hj
  · intro j hj
    by_cases h : j = k
    · subst h
      simp only [if_true]
      rcases G.hcO j hj with h1 | h1 | h1
      · linarith
      · left; linarith
      · right; left; linarith
    · simp only [h, if_false]; exact G.hcO j hj
  · have e1 := sum_dec P k hP; have e2 := sum_dec Q k hQ; have := G.s1; omega
  · have e1 := sum_dec Q k hQ; have e2 := sum_dec R k hR; have := G.s2; omega
  · obtain ⟨i, hi⟩ := G.iv1
    refine ⟨i, ?_⟩
    by_cases h : i = k
    · subst h; simp only [if_true]; omega
    · simp only [h, if_false]; exact hi
  · obtain ⟨i, hi⟩ := G.iv2
    refine ⟨i, ?_⟩
    by_cases h : i = k
    · subst h; simp only [if_true]; omega
    · simp only [h, if_false]; exact hi
  · obtain ⟨i, hi⟩ := G.iv3
    refine ⟨i, ?_⟩
    by_cases h : i = k
    · subst h; simp only [if_true]; omega
    · simp only [h, if_false]; exact hi

theorem minimize {ι : Type*} [Fintype ι] [DecidableEq ι] {C : Finset ι} {a : ι → ℝ} {x y z : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hsum1 : x + y + z = 1)
    (haC : ∀ k ∈ C, 0 < a k ∧ a k < 2 ∧ a k ≠ 1) :
    ∀ N : ℕ, ∀ (P Q R : ι → ℕ) (c : ι → ℝ), ∑ k, P k = N → Good C a x y z P Q R c →
      ∃ (P' Q' R' : ι → ℕ) (c' : ι → ℝ), Good C a x y z P' Q' R' c' ∧ ∀ k, P' k = 0 ∨ Q' k = 0 ∨ R' k = 0 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro P Q R c hN G
    by_cases h : ∃ k, 0 < P k ∧ 0 < Q k ∧ 0 < R k
    · obtain ⟨k, hP, hQ, hR⟩ := h
      have hG := good_dec hx hy hz hsum1 haC G k hP hQ hR
      have hs := sum_dec P k hP
      exact ih (∑ j, (if j = k then P j - 1 else P j)) (by omega) _ _ _ _ rfl hG
    · refine ⟨P, Q, R, c, G, fun k => ?_⟩
      by_contra hk
      push Not at hk
      exact h ⟨k, Nat.pos_of_ne_zero hk.1, Nat.pos_of_ne_zero hk.2.1, Nat.pos_of_ne_zero hk.2.2⟩

theorem lemma32_arith {ι : Type*} [Fintype ι] [DecidableEq ι] {C : Finset ι} {a c : ι → ℝ} {x y z : ℝ}
    {P Q R : ι → ℕ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hsum1 : x + y + z = 1)
    (haC : ∀ k ∈ C, 0 < a k ∧ a k < 2 ∧ a k ≠ 1)
    (hsumA : ∑ k ∈ C, a k < C.card)
    (G : Good C a x y z P Q R c) :
    x ∈ Submodule.span ℚ (insert (1:ℝ) (a '' (C : Set ι))) ∧ y ∈ Submodule.span ℚ (insert (1:ℝ) (a '' (C : Set ι))) ∧
      z ∈ Submodule.span ℚ (insert (1:ℝ) (a '' (C : Set ι))) := by
  obtain ⟨P2, Q2, R2, c2, G2, hm⟩ := minimize hx hy hz hsum1 haC _ P Q R c rfl G
  obtain ⟨i, j, hD⟩ := lemma10_min hx hy hz hsum1 haC hsumA G2 hm
  have h1 : (1:ℝ) ∈ Submodule.span ℚ (insert (1:ℝ) (a '' (C : Set ι))) := Submodule.subset_span (Set.mem_insert _ _)
  have hcs : ∀ k, c2 k ∈ Submodule.span ℚ (insert (1:ℝ) (a '' (C : Set ι))) := by
    intro k
    by_cases hk : k ∈ C
    · have hak : a k ∈ Submodule.span ℚ (insert (1:ℝ) (a '' (C : Set ι))) :=
        Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_image_of_mem a hk))
      rcases G2.hcC k hk with h | h
      · rw [h]; exact hak
      · rw [h]; exact Submodule.sub_mem _ hak h1
    · rcases G2.hcO k hk with h | h | h
      · rw [h]; exact Submodule.zero_mem _
      · rw [h]; exact h1
      · rw [h]
        have : (2:ℝ) = (2:ℚ) • (1:ℝ) := by simp [Rat.smul_def]
        rw [this]; exact Submodule.smul_mem _ _ h1
  exact LaczFormal.lemma32_alg (S := insert (1:ℝ) (a '' (C : Set ι))) (α := x) (β := y) (γ := z) (π' := 1)
    (δi := c2 i) (δj := c2 j) hD hsum1
    (by have := G2.hE i; push_cast; linarith) (by have := G2.hE j; push_cast; linarith) h1 (hcs i) (hcs j)

#print axioms lemma32_arith
#print axioms lemma10_min

end Erdos634.Draft.LaczFormal32
