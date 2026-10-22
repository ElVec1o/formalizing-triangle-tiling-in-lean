-- Draft/LaczFormalIIcWN26.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2 ("Fig. 5"), second half of step (a): ABSTRACT fan turning lemma.
-- In a `Fan6` (six sectors, labels alpha, beta, gamma twice each) let the ray `u (A+1)` separate two beta-corners (`l A = l (A+1) = 1`) and the ray `u (B+1)` separate two alpha-corners
-- (`l B = l (B+1) = 0`).  Then `u (B+1)` is positively parallel to `u (A+1)` rotated by `beta + alpha + t*gamma`, with `t in {0,1,2}` (the number of gamma-corners between the two rays on one side).
-- t = 1 is the straight case `alpha + beta + gamma = pi` (the paper's Fig. 5 does not exclude it by labels alone; it contributes turning angle 0 and does not affect `u = v + N`).
-- Tiling-free.  NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2, Lemma 4.8 / Fig. 5), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12Fan222

open Erdos634.Draft.LaczFormal.Graph

namespace Erdos634.Draft.LaczFormal.Graph

theorem per_reduce {α : Type*} (f : ℕ → α) (hf : ∀ j, f (j + 6) = f j) (n : ℕ) : f n = f (n % 6) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : n < 6
    · rw [Nat.mod_eq_of_lt h]
    · have h6 : n = (n - 6) + 6 := by omega
      have hh : n - 6 < n := by omega
      rw [h6, hf, ih (n - 6) hh]
      congr 1
      omega

theorem cnt6 {ω : Fin 3 → ℝ} {u v : ℕ → V2} {ℓ : ℕ → Fin 3} (F : Fan6 ω u v ℓ) (j : ℕ) (l : Fin 3) :
    (if ℓ j = l then 1 else 0) + (if ℓ (j + 1) = l then 1 else 0) + (if ℓ (j + 2) = l then 1 else 0) +
      (if ℓ (j + 3) = l then 1 else 0) + (if ℓ (j + 4) = l then 1 else 0) + (if ℓ (j + 5) = l then 1 else 0) = 2 := by
  have h := F.hcnt j l
  rw [Finset.card_filter] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero] at h
  exact h

/-- The labels in a window of six: the multiset is `{0,0,1,1,2,2}`. -/
theorem fan_turn {ω : Fin 3 → ℝ} {u v : ℕ → V2} {ℓ : ℕ → Fin 3} (F : Fan6 ω u v ℓ)
    (hu6 : ∀ j, u (j + 6) = u j) (hl6 : ∀ j, ℓ (j + 6) = ℓ j) {A B : ℕ}
    (hA0 : ℓ A = 1) (hA1 : ℓ (A + 1) = 1) (hB0 : ℓ B = 0) (hB1 : ℓ (B + 1) = 0) :
    ∃ t : ℕ, t ≤ 2 ∧ Par (u (B + 1)) (rot (ω 1 + ω 0 + (t : ℝ) * ω 2) (u (A + 1))) := by
  obtain ⟨m, hm6, hBm⟩ : ∃ m, m < 6 ∧ B % 6 = (A + m) % 6 := ⟨(B + 6 - A % 6) % 6, by omega, by omega⟩
  have eℓ : ∀ n, ℓ n = ℓ (n % 6) := per_reduce ℓ hl6
  have eu : ∀ n, u n = u (n % 6) := per_reduce u hu6
  have hℓB : ℓ B = ℓ (A + m) := by rw [eℓ B, hBm, ← eℓ]
  have hℓB1 : ℓ (B + 1) = ℓ (A + m + 1) := by
    rw [eℓ (B + 1), eℓ (A + m + 1)]; congr 1; omega
  have huB : u (B + 1) = u (A + 1 + m) := by
    rw [eu (B + 1), eu (A + 1 + m)]; congr 1; omega
  rw [hℓB] at hB0
  rw [hℓB1] at hB1
  have hrun := run_rotation (fun i => u (A + 1 + i)) (fun i => v (A + 1 + i)) (fun i => F.hu _) (fun i => by
    have := F.hpar (A + 1 + i); simpa [add_assoc] using this) m
  simp only [add_zero] at hrun
  rw [huB]
  have hwd : ∀ i, wd (u (A + 1 + i)) (v (A + 1 + i)) = ω (ℓ (A + 1 + i)) := fun i => F.hwd _
  simp only [hwd] at hrun
  have c1 := cnt6 F A 1
  have c0 := cnt6 F A 0
  have h3 : ∀ x : Fin 3, x ≠ 0 → x ≠ 1 → x = 2 := by decide
  interval_cases m
  · exfalso
    have h0 : ℓ A = 0 := hB0
    rw [hA0] at h0; exact absurd h0 (by decide)
  · exfalso
    have h0 : ℓ (A + 1) = 0 := hB0
    rw [hA1] at h0; exact absurd h0 (by decide)
  · refine ⟨0, by norm_num, ?_⟩
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hrun
    have e1 : ℓ (A + 1 + 1) = 0 := hB0
    simp only [add_zero, hA1, e1] at hrun
    convert hrun using 2
    ring
  · refine ⟨1, by norm_num, ?_⟩
    have e3 : ℓ (A + 3) = 0 := hB0
    have e4 : ℓ (A + 4) = 0 := hB1
    have hx : ℓ (A + 2) = 2 := by
      apply h3
      · intro h; simp [hA0, hA1, h, e3, e4] at c0
        all_goals first | omega | (revert c0; split_ifs <;> omega)
      · intro h; simp [hA0, hA1, h, e3, e4] at c1
        all_goals first | omega | (revert c1; split_ifs <;> omega)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hrun
    have e1 : ℓ (A + 1 + 1) = 2 := hx
    have e2 : ℓ (A + 1 + 2) = 0 := e3
    simp only [add_zero, hA1, e1, e2] at hrun
    convert hrun using 2
    push_cast; ring
  · refine ⟨2, by norm_num, ?_⟩
    have e4 : ℓ (A + 4) = 0 := hB0
    have e5 : ℓ (A + 5) = 0 := hB1
    have hx : ℓ (A + 2) = 2 := by
      apply h3
      · intro h; simp [hA0, hA1, h, e4, e5] at c0
        all_goals first | omega | (revert c0; split_ifs <;> omega)
      · intro h; simp [hA0, hA1, h, e4, e5] at c1
        all_goals first | omega | (revert c1; split_ifs <;> omega)
    have hy : ℓ (A + 3) = 2 := by
      apply h3
      · intro h; simp [hA0, hA1, h, e4, e5] at c0
        all_goals first | omega | (revert c0; split_ifs <;> omega)
      · intro h; simp [hA0, hA1, h, e4, e5] at c1
        all_goals first | omega | (revert c1; split_ifs <;> omega)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hrun
    have e1 : ℓ (A + 1 + 1) = 2 := hx
    have e2 : ℓ (A + 1 + 2) = 2 := hy
    have e3 : ℓ (A + 1 + 3) = 0 := e4
    simp only [add_zero, hA1, e1, e2, e3] at hrun
    convert hrun using 2
    push_cast; ring
  · exfalso
    have : ℓ (A + 5 + 1) = ℓ A := hl6 A
    rw [show A + 5 + 1 = A + 6 by ring] at hB1
    rw [hl6 A, hA0] at hB1
    exact absurd hB1 (by decide)

end Erdos634.Draft.LaczFormal.Graph
