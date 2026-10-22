-- Draft/LemmaCShapes.lean — Corollary C′ (target shapes), geometry-free arithmetic.
-- GENERATED case analysis (script /tmp/gen/gen.py, checked by Lean; not trusted): given the corner
-- splits of a label-count vector, the multiset of corner angles is one of the listed shapes.
-- Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Mathlib

namespace Erdos634.Draft.LemmaCShapes

/-- `θ` takes the values `x, y, z` in some order. -/
def TA (θ : Fin 3 → ℝ) (x y z : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), θ (σ 0) = x ∧ θ (σ 1) = y ∧ θ (σ 2) = z

theorem ta_of_idx (θ : Fin 3 → ℝ) (x y z : ℝ) (i j l : Fin 3)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hx : θ i = x) (hy : θ j = y) (hz : θ l = z) : TA θ x y z := by
  have key : ∀ i j l : Fin 3, i ≠ j → i ≠ l → j ≠ l → Function.Bijective ![i, j, l] := by decide
  refine ⟨Equiv.ofBijective _ (key i j l hij hil hjl), ?_, ?_, ?_⟩
  · simpa using hx
  · simpa using hy
  · simpa using hz

theorem fin3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide

set_option maxHeartbeats 4000000 in
theorem shapes_threeTwo (θ : Fin 3 → ℝ) (u v w : ℝ) (P Q R : Fin 3 → ℕ)
    (hu : u = 2 * w + v) (hrel : 3 * w + 2 * v = Real.pi)
    (hθ : ∀ k, θ k = (P k : ℝ) * u + (Q k : ℝ) * v + (R k : ℝ) * w)
    (hP : P 0 + P 1 + P 2 = 0) (hQ : Q 0 + Q 1 + Q 2 = 2) (hR : R 0 + R 1 + R 2 = 3)
    (hpos : ∀ k, 1 ≤ P k + Q k + R k) :
    TA θ v v (3 * w) ∨
    TA θ (w + v) (w + v) w ∨
    TA θ (2 * w) v (w + v) ∨
    TA θ (2 * w) w (2 * v) ∨
    TA θ w w (w + 2 * v) ∨
    TA θ w v u := by
  have h0 := hθ 0; have h1 := hθ 1; have h2 := hθ 2
  have p0 := hpos 0; have p1 := hpos 1; have p2 := hpos 2
  have hPk : P 0 = 0 ∧ P 1 = 0 ∧ P 2 = 0 := by omega
  obtain ⟨hP0, hP1, hP2⟩ := hPk
  rcases (by omega : Q 0 = 0 ∨ Q 0 = 1 ∨ Q 0 = 2) with e0 | e0 | e0
  · 
    rcases (by omega : R 0 = 1 ∨ R 0 = 2 ∨ R 0 = 3) with e1 | e1 | e1
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1 ∨ Q 1 = 2) with e2 | e2 | e2
      · 
        rcases (by omega : R 1 = 1 ∨ R 1 = 2) with e3 | e3
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1 ∨ R 1 = 2) with e3 | e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1 ∨ Q 1 = 2) with e2 | e2 | e2
      · 
        obtain e3 : R 1 = 1 := by omega
        obtain e4 : Q 2 = 2 := by omega
        obtain e5 : R 2 = 0 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))
      · 
        obtain e3 : R 1 = 0 := by omega
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 1 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
    · 
      obtain e2 : Q 1 = 1 := by omega
      obtain e3 : R 1 = 0 := by omega
      obtain e4 : Q 2 = 1 := by omega
      obtain e5 : R 2 = 0 := by omega
      rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
      push_cast at h0 h1 h2
      exact Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
  · 
    rcases (by omega : R 0 = 0 ∨ R 0 = 1 ∨ R 0 = 2) with e1 | e1 | e1
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1) with e2 | e2
      · 
        rcases (by omega : R 1 = 1 ∨ R 1 = 2 ∨ R 1 = 3) with e3 | e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1 ∨ R 1 = 2) with e3 | e3 | e3
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 3 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1) with e2 | e2
      · 
        rcases (by omega : R 1 = 1 ∨ R 1 = 2) with e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1) with e2 | e2
      · 
        obtain e3 : R 1 = 1 := by omega
        obtain e4 : Q 2 = 1 := by omega
        obtain e5 : R 2 = 0 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
      · 
        obtain e3 : R 1 = 0 := by omega
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 1 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
  · 
    rcases (by omega : R 0 = 0 ∨ R 0 = 1) with e1 | e1
    · 
      obtain e2 : Q 1 = 0 := by omega
      rcases (by omega : R 1 = 1 ∨ R 1 = 2) with e3 | e3
      · 
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 2 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
      · 
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 1 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
    · 
      obtain e2 : Q 1 = 0 := by omega
      obtain e3 : R 1 = 1 := by omega
      obtain e4 : Q 2 = 0 := by omega
      obtain e5 : R 2 = 1 := by omega
      rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
      push_cast at h0 h1 h2
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))

set_option maxHeartbeats 4000000 in
theorem shapes_twoAlpha (θ : Fin 3 → ℝ) (u v w : ℝ) (P Q R : Fin 3 → ℕ)
    (hu : u = 2 * w) (hv : v = Real.pi - 3 * w)
    (hθ : ∀ k, θ k = (P k : ℝ) * u + (Q k : ℝ) * v + (R k : ℝ) * w)
    (hP : P 0 + P 1 + P 2 = 0) (hQ : Q 0 + Q 1 + Q 2 = 1) (hR : R 0 + R 1 + R 2 = 3)
    (hpos : ∀ k, 1 ≤ P k + Q k + R k) :
    TA θ w w (v + w) ∨
    TA θ w v u := by
  have h0 := hθ 0; have h1 := hθ 1; have h2 := hθ 2
  have p0 := hpos 0; have p1 := hpos 1; have p2 := hpos 2
  have hPk : P 0 = 0 ∧ P 1 = 0 ∧ P 2 = 0 := by omega
  obtain ⟨hP0, hP1, hP2⟩ := hPk
  rcases (by omega : Q 0 = 0 ∨ Q 0 = 1) with e0 | e0
  · 
    rcases (by omega : R 0 = 1 ∨ R 0 = 2) with e1 | e1
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1) with e2 | e2
      · 
        rcases (by omega : R 1 = 1 ∨ R 1 = 2) with e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1) with e2 | e2
      · 
        obtain e3 : R 1 = 1 := by omega
        obtain e4 : Q 2 = 1 := by omega
        obtain e5 : R 2 = 0 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
      · 
        obtain e3 : R 1 = 0 := by omega
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 1 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
  · 
    rcases (by omega : R 0 = 0 ∨ R 0 = 1) with e1 | e1
    · 
      obtain e2 : Q 1 = 0 := by omega
      rcases (by omega : R 1 = 1 ∨ R 1 = 2) with e3 | e3
      · 
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 2 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
      · 
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 1 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
    · 
      obtain e2 : Q 1 = 0 := by omega
      obtain e3 : R 1 = 1 := by omega
      obtain e4 : Q 2 = 0 := by omega
      obtain e5 : R 2 = 1 := by omega
      rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
      push_cast at h0 h1 h2
      exact Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))

set_option maxHeartbeats 4000000 in
theorem shapes_right (θ : Fin 3 → ℝ) (u v w : ℝ) (P Q R : Fin 3 → ℕ)
    (hu : u = Real.pi / 2) (hw : w = Real.pi / 2 - v)
    (hθ : ∀ k, θ k = (P k : ℝ) * u + (Q k : ℝ) * v + (R k : ℝ) * w)
    (hP : P 0 + P 1 + P 2 = 0) (hQ : Q 0 + Q 1 + Q 2 = 2) (hR : R 0 + R 1 + R 2 = 2)
    (hpos : ∀ k, 1 ≤ P k + Q k + R k) :
    TA θ v v (2 * w) ∨
    TA θ (2 * v) w w ∨
    TA θ u v w := by
  have h0 := hθ 0; have h1 := hθ 1; have h2 := hθ 2
  have p0 := hpos 0; have p1 := hpos 1; have p2 := hpos 2
  have hPk : P 0 = 0 ∧ P 1 = 0 ∧ P 2 = 0 := by omega
  obtain ⟨hP0, hP1, hP2⟩ := hPk
  rcases (by omega : Q 0 = 0 ∨ Q 0 = 1 ∨ Q 0 = 2) with e0 | e0 | e0
  · 
    rcases (by omega : R 0 = 1 ∨ R 0 = 2) with e1 | e1
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1 ∨ Q 1 = 2) with e2 | e2 | e2
      · 
        obtain e3 : R 1 = 1 := by omega
        obtain e4 : Q 2 = 2 := by omega
        obtain e5 : R 2 = 0 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
      · 
        obtain e3 : R 1 = 0 := by omega
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 1 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
    · 
      obtain e2 : Q 1 = 1 := by omega
      obtain e3 : R 1 = 0 := by omega
      obtain e4 : Q 2 = 1 := by omega
      obtain e5 : R 2 = 0 := by omega
      rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
      push_cast at h0 h1 h2
      exact Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
  · 
    rcases (by omega : R 0 = 0 ∨ R 0 = 1) with e1 | e1
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1) with e2 | e2
      · 
        rcases (by omega : R 1 = 1 ∨ R 1 = 2) with e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1) with e2 | e2
      · 
        obtain e3 : R 1 = 1 := by omega
        obtain e4 : Q 2 = 1 := by omega
        obtain e5 : R 2 = 0 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
      · 
        obtain e3 : R 1 = 0 := by omega
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 1 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
  · 
    obtain e1 : R 0 = 0 := by omega
    obtain e2 : Q 1 = 0 := by omega
    obtain e3 : R 1 = 1 := by omega
    obtain e4 : Q 2 = 0 := by omega
    obtain e5 : R 2 = 1 := by omega
    rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
    push_cast at h0 h1 h2
    exact Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))

set_option maxHeartbeats 4000000 in
theorem shapes_twoPiThree (θ : Fin 3 → ℝ) (u v w : ℝ) (P Q R : Fin 3 → ℕ)
    (hu : u = 2 * Real.pi / 3) (hv : v = Real.pi / 3 - w)
    (hθ : ∀ k, θ k = (P k : ℝ) * u + (Q k : ℝ) * v + (R k : ℝ) * w)
    (hP : P 0 + P 1 + P 2 = 0) (hQ : Q 0 + Q 1 + Q 2 = 3) (hR : R 0 + R 1 + R 2 = 3)
    (hpos : ∀ k, 1 ≤ P k + Q k + R k) :
    (∀ k, θ k = Real.pi / 3) ∨
    TA θ w w (w + 3 * v) ∨
    TA θ v v (v + 3 * w) ∨
    TA θ w (w + v) (w + 2 * v) ∨
    TA θ v (w + v) (2 * w + v) ∨
    TA θ (2 * w) (2 * v) (w + v) ∨
    TA θ w (2 * w) (3 * v) ∨
    TA θ v (2 * v) (3 * w) ∨
    TA θ w (2 * v) (2 * w + v) ∨
    TA θ v (2 * w) (w + 2 * v) ∨
    TA θ w v u := by
  have h0 := hθ 0; have h1 := hθ 1; have h2 := hθ 2
  have p0 := hpos 0; have p1 := hpos 1; have p2 := hpos 2
  have hPk : P 0 = 0 ∧ P 1 = 0 ∧ P 2 = 0 := by omega
  obtain ⟨hP0, hP1, hP2⟩ := hPk
  rcases (by omega : Q 0 = 0 ∨ Q 0 = 1 ∨ Q 0 = 2 ∨ Q 0 = 3) with e0 | e0 | e0 | e0
  · 
    rcases (by omega : R 0 = 1 ∨ R 0 = 2 ∨ R 0 = 3) with e1 | e1 | e1
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1 ∨ Q 1 = 2 ∨ Q 1 = 3) with e2 | e2 | e2 | e2
      · 
        rcases (by omega : R 1 = 1 ∨ R 1 = 2) with e3 | e3
        · 
          obtain e4 : Q 2 = 3 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
        · 
          obtain e4 : Q 2 = 3 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1 ∨ R 1 = 2) with e3 | e3 | e3
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1 ∨ R 1 = 2) with e3 | e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1 ∨ Q 1 = 2 ∨ Q 1 = 3) with e2 | e2 | e2 | e2
      · 
        obtain e3 : R 1 = 1 := by omega
        obtain e4 : Q 2 = 3 := by omega
        obtain e5 : R 2 = 0 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
      · 
        obtain e3 : R 1 = 0 := by omega
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 1 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))
    · 
      rcases (by omega : Q 1 = 1 ∨ Q 1 = 2) with e2 | e2
      · 
        obtain e3 : R 1 = 0 := by omega
        obtain e4 : Q 2 = 2 := by omega
        obtain e5 : R 2 = 0 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))
      · 
        obtain e3 : R 1 = 0 := by omega
        obtain e4 : Q 2 = 1 := by omega
        obtain e5 : R 2 = 0 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))
  · 
    rcases (by omega : R 0 = 0 ∨ R 0 = 1 ∨ R 0 = 2 ∨ R 0 = 3) with e1 | e1 | e1 | e1
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1 ∨ Q 1 = 2) with e2 | e2 | e2
      · 
        rcases (by omega : R 1 = 1 ∨ R 1 = 2 ∨ R 1 = 3) with e3 | e3 | e3
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1 ∨ R 1 = 2 ∨ R 1 = 3) with e3 | e3 | e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 3 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1 ∨ R 1 = 2) with e3 | e3 | e3
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 3 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1 ∨ Q 1 = 2) with e2 | e2 | e2
      · 
        rcases (by omega : R 1 = 1 ∨ R 1 = 2) with e3 | e3
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1 ∨ R 1 = 2) with e3 | e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inl (fun k => by rcases fin3 k with rfl | rfl | rfl <;> linarith)
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1 ∨ Q 1 = 2) with e2 | e2 | e2
      · 
        obtain e3 : R 1 = 1 := by omega
        obtain e4 : Q 2 = 2 := by omega
        obtain e5 : R 2 = 0 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
      · 
        obtain e3 : R 1 = 0 := by omega
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 1 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))))
    · 
      obtain e2 : Q 1 = 1 := by omega
      obtain e3 : R 1 = 0 := by omega
      obtain e4 : Q 2 = 1 := by omega
      obtain e5 : R 2 = 0 := by omega
      rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
      push_cast at h0 h1 h2
      exact Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))
  · 
    rcases (by omega : R 0 = 0 ∨ R 0 = 1 ∨ R 0 = 2) with e1 | e1 | e1
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1) with e2 | e2
      · 
        rcases (by omega : R 1 = 1 ∨ R 1 = 2 ∨ R 1 = 3) with e3 | e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1 ∨ R 1 = 2) with e3 | e3 | e3
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 3 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))))
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1) with e2 | e2
      · 
        rcases (by omega : R 1 = 1 ∨ R 1 = 2) with e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1) with e2 | e2
      · 
        obtain e3 : R 1 = 1 := by omega
        obtain e4 : Q 2 = 1 := by omega
        obtain e5 : R 2 = 0 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
      · 
        obtain e3 : R 1 = 0 := by omega
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 1 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
  · 
    rcases (by omega : R 0 = 0 ∨ R 0 = 1) with e1 | e1
    · 
      obtain e2 : Q 1 = 0 := by omega
      rcases (by omega : R 1 = 1 ∨ R 1 = 2) with e3 | e3
      · 
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 2 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))
      · 
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 1 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))
    · 
      obtain e2 : Q 1 = 0 := by omega
      obtain e3 : R 1 = 1 := by omega
      obtain e4 : Q 2 = 0 := by omega
      obtain e5 : R 2 = 1 := by omega
      rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
      push_cast at h0 h1 h2
      exact Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))

end Erdos634.Draft.LemmaCShapes

#print axioms Erdos634.Draft.LemmaCShapes.shapes_threeTwo
#print axioms Erdos634.Draft.LemmaCShapes.shapes_twoAlpha
#print axioms Erdos634.Draft.LemmaCShapes.shapes_right
#print axioms Erdos634.Draft.LemmaCShapes.shapes_twoPiThree
