import Erdos634.Draft.LaczFormal9u
import Erdos634.Draft.LaczFormal9j

/-!
# Laczkovich DM 140 (1995), Theorem 2.6: the six shapes (angle triples (3)) and their pairwise non-similarity

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.6, display (3)), Beeson, Beeson-Zhang.  Formalization debt,
not /goal progress.

For `α` the six angle triples of the proof of Theorem 2.6 (rendered from the printed page):
`(α, α, π - 2α)`, `(α, π/2 - α, π/2)`, `(α, 2α, π - 3α)`, `(α, (π - 3α)/2, (π + α)/2)`, `(π/3 - 2α/3, α, 2π/3 - α/3)`,
`(α, π/3 - α, 2π/3)`.  `six_distinct`: for `0 < α < π/12` no two of them are permutations of each other (the printed proof gets this from the
irrationality of `α/π`, not proved here; the range `α < π/12` makes it elementary: the largest entries are separated).
-/

open scoped Classical

namespace Erdos634.Laczkovich9v

noncomputable def sixX (α : ℝ) : Fin 6 → ℝ := ![α, α, α, α, Real.pi / 3 - 2 * α / 3, α]
noncomputable def sixY (α : ℝ) : Fin 6 → ℝ :=
  ![α, Real.pi / 2 - α, 2 * α, (Real.pi - 3 * α) / 2, α, Real.pi / 3 - α]
noncomputable def sixZ (α : ℝ) : Fin 6 → ℝ :=
  ![Real.pi - 2 * α, Real.pi / 2, Real.pi - 3 * α, (Real.pi + α) / 2, 2 * Real.pi / 3 - α / 3, 2 * Real.pi / 3]

theorem perm6 (σ : Equiv.Perm (Fin 3)) :
    (σ 0 = 0 ∧ σ 1 = 1 ∧ σ 2 = 2) ∨ (σ 0 = 0 ∧ σ 1 = 2 ∧ σ 2 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0 ∧ σ 2 = 2) ∨
    (σ 0 = 1 ∧ σ 1 = 2 ∧ σ 2 = 0) ∨ (σ 0 = 2 ∧ σ 1 = 0 ∧ σ 2 = 1) ∨ (σ 0 = 2 ∧ σ 1 = 1 ∧ σ 2 = 0) := by
  revert σ; decide

/-- The largest entry of a triple. -/
def mx (f : Fin 3 → ℝ) : ℝ := max (f 0) (max (f 1) (f 2))

theorem mx_perm (a b : Fin 3 → ℝ) (σ : Equiv.Perm (Fin 3)) (h : ∀ k, b (σ k) = a k) : mx a = mx b := by
  have e0 := h 0
  have e1 := h 1
  have e2 := h 2
  unfold mx
  rcases perm6 σ with ⟨a0, a1, a2⟩ | ⟨a0, a1, a2⟩ | ⟨a0, a1, a2⟩ | ⟨a0, a1, a2⟩ | ⟨a0, a1, a2⟩ | ⟨a0, a1, a2⟩ <;>
    rw [a0] at e0 <;> rw [a1] at e1 <;> rw [a2] at e2 <;> rw [← e0, ← e1, ← e2] <;> ac_rfl

noncomputable def mxS (α : ℝ) : Fin 6 → ℝ :=
  ![Real.pi - 2 * α, Real.pi / 2, Real.pi - 3 * α, Real.pi / 2 + α / 2, 2 * Real.pi / 3 - α / 3, 2 * Real.pi / 3]

theorem mx_third {a b c : ℝ} (h1 : a ≤ c) (h2 : b ≤ c) : mx (![a, b, c] : Fin 3 → ℝ) = c := by
  unfold mx
  simp [h1, h2]

theorem mx_six (α : ℝ) (h0 : 0 < α) (h1 : α < Real.pi / 12) (i : Fin 6) :
    mx (![sixX α i, sixY α i, sixZ α i] : Fin 3 → ℝ) = mxS α i := by
  have hpi := Real.pi_pos
  fin_cases i <;> refine (mx_third ?_ ?_).trans ?_ <;> simp [sixX, sixY, sixZ, mxS] <;> linarith

theorem mxS_inj (α : ℝ) (h0 : 0 < α) (h1 : α < Real.pi / 12) (i j : Fin 6) (h : mxS α i = mxS α j) : i = j := by
  have hpi := Real.pi_pos
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp [mxS] at h; linarith)

/-- No two of the six triples are permutations of each other (for `0 < α < π/12`). -/
theorem six_distinct (α : ℝ) (h0 : 0 < α) (h1 : α < Real.pi / 12) :
    ∀ i j : Fin 6, i ≠ j → ∀ σ : Equiv.Perm (Fin 3),
      ¬ (∀ k, (![sixX α j, sixY α j, sixZ α j] : Fin 3 → ℝ) (σ k) = (![sixX α i, sixY α i, sixZ α i] : Fin 3 → ℝ) k) := by
  intro i j hij σ h
  have := mx_perm _ _ σ h
  rw [mx_six α h0 h1, mx_six α h0 h1] at this
  exact hij (mxS_inj α h0 h1 i j this)

end Erdos634.Laczkovich9v

#print axioms Erdos634.Laczkovich9v.six_distinct
