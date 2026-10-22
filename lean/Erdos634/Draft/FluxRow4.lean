-- Draft/FluxRow4.lean — consumer corollary for row 4 (L2 + L3 + L4 → P5 input,
-- (private working notes, not included):134): the two sign invariants of the `γ = 2α` tile.
-- Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).  Design: (private working notes, not included) §4.2 row 4 (`Row4.invariants`).
--
-- Grid `L = ℤπ + ℤα` (`GridChar.rank2 α`), `χ₁ = (−1)^j`, `χ₂ = (−1)^(j+k)` on `jπ + kα`.
-- Tile angles `α = (0,1)`, `π − 3α = (1,−3)`, `2α = (0,2)`; tile values `K₁ = −(a + c − b)`,
-- `K₂ = −(b + c − a)` (a, b, c opposite α, π − 3α, 2α).
--
-- `Row4.flux_signs` (shape-free) is witnessed (Draft/FluxRow4Witness.lean).  `Row4.invariants`
-- additionally assumes the base-α target shape `(α, α, π − 2α)`, sides `X, X, Y`; that target shape
-- has NO Lean witness (DESIGN.md §5) — it is a conditional, not a result, until one exists.
-- Named blockers left for row 4 (DESIGN.md §4.2): L1 (γ = 2α vertex figures), L4's law of sines,
-- P5's area `X² = N·ab`, C6/L7/L8 leg words, the case-split hypothesis.
-- Formalization debt; not progress on the /goal.
import Erdos634.Draft.FluxGrids
import Erdos634.Draft.FluxValue

open scoped Classical

namespace Erdos634.Geometry

/-- **A placement of the `γ = 2α` tile**: angles `(α, π − 3α, 2α)`, opposite sides `(a, b, c)`. -/
def Tri.TwoAlphaData (T : Tri) (α a b c : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3),
    T.angleAt (σ 0) = α ∧ T.oppLen (σ 0) = a ∧
    T.angleAt (σ 1) = Real.pi - 3 * α ∧ T.oppLen (σ 1) = b ∧
    T.angleAt (σ 2) = 2 * α ∧ T.oppLen (σ 2) = c

theorem Tri.twoAlpha_angles_mem {T : Tri} {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.TwoAlphaData α a b c) (b' : ZMod 2) :
    ∀ j, ((T.angleAt j : ℝ) : Real.Angle) ∈ (GridChar.rank2 α hα b' 0).L := by
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := h
  intro j
  obtain ⟨k, rfl⟩ := σ.surjective j
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  rcases hk with rfl | rfl | rfl
  · rw [h0, show ((α : ℝ) : Real.Angle)
        = ((((0 : ℤ) : ℝ) * Real.pi + ((1 : ℤ) : ℝ) * α : ℝ) : Real.Angle) by
      congr 1; push_cast; ring]
    exact GridChar.rank2_mem _ _ _ _ _ _
  · rw [h1, show ((Real.pi - 3 * α : ℝ) : Real.Angle)
        = ((((1 : ℤ) : ℝ) * Real.pi + ((-3 : ℤ) : ℝ) * α : ℝ) : Real.Angle) by
      congr 1; push_cast; ring]
    exact GridChar.rank2_mem _ _ _ _ _ _
  · rw [h2, show ((2 * α : ℝ) : Real.Angle)
        = ((((0 : ℤ) : ℝ) * Real.pi + ((2 : ℤ) : ℝ) * α : ℝ) : Real.Angle) by
      congr 1; push_cast; ring]
    exact GridChar.rank2_mem _ _ _ _ _ _

theorem twoAlpha_tileValue (T : Tri) {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.TwoAlphaData α a b c) (b' : ZMod 2) :
    (GridChar.rank2 α hα b' 0).tileValue T
      = (if ((1 : ℤ) : ZMod 2) + b' * ((-1 : ℤ) : ZMod 2) = 0 then 1 else -1) * a
        + (if ((0 : ℤ) : ZMod 2) + b' * ((3 : ℤ) : ZMod 2) = 0 then 1 else -1) * b
        + (if ((1 : ℤ) : ZMod 2) + b' * ((-2 : ℤ) : ZMod 2) = 0 then 1 else -1) * c := by
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  unfold GridChar.tileValue
  rw [← Equiv.sum_comp σ (fun j => (GridChar.rank2 α hα b' 0).chi
      ((Real.pi - T.angleAt j : ℝ) : Real.Angle) * T.oppLen j), Fin.sum_univ_three]
  rw [h0, o0, h1, o1, h2, o2,
    show Real.pi - α = ((1 : ℤ) : ℝ) * Real.pi + ((-1 : ℤ) : ℝ) * α by push_cast; ring,
    show Real.pi - (Real.pi - 3 * α) = ((0 : ℤ) : ℝ) * Real.pi + ((3 : ℤ) : ℝ) * α by
      push_cast; ring,
    show Real.pi - 2 * α = ((1 : ℤ) : ℝ) * Real.pi + ((-2 : ℤ) : ℝ) * α by push_cast; ring,
    GridChar.rank2_chi, GridChar.rank2_chi, GridChar.rank2_chi]

/-- **Row 4, shape-free.**  For an `N`-tiling by a `γ = 2α` tile with `α ∉ ℚπ`:
`Φ_{χ₁} = S₁ (a + c − b)`, `Φ_{χ₂} = S₂ (b + c − a)`, `S₁ ≡ S₂ ≡ N (mod 2)`, `|S₁|, |S₂| ≤ N`. -/
theorem Row4.flux_signs {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c) :
    ∃ S₁ S₂ : ℤ, (2 : ℤ) ∣ S₁ - N ∧ (2 : ℤ) ∣ S₂ - N ∧ |S₁| ≤ N ∧ |S₂| ≤ N ∧
      D.target.flux (GridChar.rank2 α hα 0 0).weight = (S₁ : ℝ) * (a + c - b) ∧
      D.target.flux (GridChar.rank2 α hα 1 0).weight = (S₂ : ℝ) * (b + c - a) := by
  obtain ⟨S, hS2, hSN, hSf⟩ := D.target_flux_signs (GridChar.rank2 α hα 0 0)
    (GridChar.rank2_sq _ _ _ _) (D.model.twoAlpha_angles_mem hα h 0)
  obtain ⟨S', hS2', hSN', hSf'⟩ := D.target_flux_signs (GridChar.rank2 α hα 1 0)
    (GridChar.rank2_sq _ _ _ _) (D.model.twoAlpha_angles_mem hα h 1)
  have hK1 : (GridChar.rank2 α hα 0 0).tileValue D.model = -(a + c - b) := by
    rw [twoAlpha_tileValue D.model hα h 0, if_neg (by decide), if_pos (by decide),
      if_neg (by decide)]
    ring
  have hK2 : (GridChar.rank2 α hα 1 0).tileValue D.model = -(b + c - a) := by
    rw [twoAlpha_tileValue D.model hα h 1, if_pos (by decide), if_neg (by decide),
      if_neg (by decide)]
    ring
  refine ⟨-S, -S', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show -S - (N : ℤ) = -(S - N) - 2 * N by ring]
    exact dvd_sub (dvd_neg.mpr hS2) (dvd_mul_right 2 _)
  · rw [show -S' - (N : ℤ) = -(S' - N) - 2 * N by ring]
    exact dvd_sub (dvd_neg.mpr hS2') (dvd_mul_right 2 _)
  · rw [abs_neg]; exact hSN
  · rw [abs_neg]; exact hSN'
  · rw [hSf, hK1]; push_cast; ring
  · rw [hSf', hK2]; push_cast; ring

/-- **`Row4.invariants`** (L2 + L3 + L4 → P5 input): with the base-α target shape — angles `α` at
vertices 0 and 1, sides `X, X` opposite them and `Y` opposite vertex 2 —
`Y − 2X = S₁ (a + c − b)` and `Y + 2X = S₂ (b + c − a)`, `S₁ ≡ S₂ ≡ N (mod 2)`.
CONDITIONAL: the target-shape hypotheses have no Lean witness. -/
theorem Row4.invariants {N : ℕ} (D : CongruentDissection N) {α a b c X Y : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoAlphaData α a b c)
    (hA : D.target.angleAt 0 = α) (hB : D.target.angleAt 1 = α)
    (hX : D.target.oppLen 0 = X ∧ D.target.oppLen 1 = X) (hY : D.target.oppLen 2 = Y) :
    ∃ S₁ S₂ : ℤ, (2 : ℤ) ∣ S₁ - N ∧ (2 : ℤ) ∣ S₂ - N ∧ |S₁| ≤ N ∧ |S₂| ≤ N ∧
      Y - 2 * X = (S₁ : ℝ) * (a + c - b) ∧ Y + 2 * X = (S₂ : ℝ) * (b + c - a) := by
  obtain ⟨S₁, S₂, h1, h2, h3, h4, hf1, hf2⟩ := Row4.flux_signs D hα h
  have hC : D.target.angleAt 2 = Real.pi - 2 * α := by
    have hs := D.target.angleAt_sum; rw [hA, hB] at hs; linarith
  have hT : ∀ b' : ZMod 2, ∀ k, ((D.target.angleAt k : ℝ) : Real.Angle)
      ∈ (GridChar.rank2 α hα b' 0).L := by
    intro b' k
    have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
    rcases hk with rfl | rfl | rfl
    · rw [hA, show ((α : ℝ) : Real.Angle)
          = ((((0 : ℤ) : ℝ) * Real.pi + ((1 : ℤ) : ℝ) * α : ℝ) : Real.Angle) by
        congr 1; push_cast; ring]
      exact GridChar.rank2_mem _ _ _ _ _ _
    · rw [hB, show ((α : ℝ) : Real.Angle)
          = ((((0 : ℤ) : ℝ) * Real.pi + ((1 : ℤ) : ℝ) * α : ℝ) : Real.Angle) by
        congr 1; push_cast; ring]
      exact GridChar.rank2_mem _ _ _ _ _ _
    · rw [hC, show ((Real.pi - 2 * α : ℝ) : Real.Angle)
          = ((((1 : ℤ) : ℝ) * Real.pi + ((-2 : ℤ) : ℝ) * α : ℝ) : Real.Angle) by
        congr 1; push_cast; ring]
      exact GridChar.rank2_mem _ _ _ _ _ _
  have hKT : ∀ b' : ZMod 2, (GridChar.rank2 α hα b' 0).tileValue D.target
      = (if ((1 : ℤ) : ZMod 2) + b' * ((-1 : ℤ) : ZMod 2) = 0 then 1 else -1) * X
        + (if ((1 : ℤ) : ZMod 2) + b' * ((-1 : ℤ) : ZMod 2) = 0 then 1 else -1) * X
        + (if ((0 : ℤ) : ZMod 2) + b' * ((2 : ℤ) : ZMod 2) = 0 then 1 else -1) * Y := by
    intro b'
    unfold GridChar.tileValue
    rw [Fin.sum_univ_three, hA, hB, hC, hX.1, hX.2, hY,
      show Real.pi - α = ((1 : ℤ) : ℝ) * Real.pi + ((-1 : ℤ) : ℝ) * α by push_cast; ring,
      show Real.pi - (Real.pi - 2 * α) = ((0 : ℤ) : ℝ) * Real.pi + ((2 : ℤ) : ℝ) * α by
        push_cast; ring,
      GridChar.rank2_chi, GridChar.rank2_chi]
  have hK1 : (GridChar.rank2 α hα 0 0).tileValue D.target = Y - 2 * X := by
    rw [hKT, if_neg (by decide), if_pos (by decide)]; ring
  have hK2 : (GridChar.rank2 α hα 1 0).tileValue D.target = Y + 2 * X := by
    rw [hKT, if_pos (by decide), if_pos (by decide)]; ring
  have p1 := D.target.flux_grid_pm _ (GridChar.rank2_sq α hα 0 0) (hT 0)
  have p2 := D.target.flux_grid_pm _ (GridChar.rank2_sq α hα 1 0) (hT 1)
  rw [hK1, hf1] at p1
  rw [hK2, hf2] at p2
  have hneg : ∀ S : ℤ, (2 : ℤ) ∣ S - N → (2 : ℤ) ∣ -S - N := fun S hS => by
    rw [show -S - (N : ℤ) = -(S - N) - 2 * N by ring]
    exact dvd_sub (dvd_neg.mpr hS) (dvd_mul_right 2 _)
  rcases p1 with e1 | e1 <;> rcases p2 with e2 | e2
  · exact ⟨S₁, S₂, h1, h2, h3, h4, e1.symm, e2.symm⟩
  · exact ⟨S₁, -S₂, h1, hneg _ h2, h3, by rw [abs_neg]; exact h4, e1.symm,
      by push_cast; linarith⟩
  · exact ⟨-S₁, S₂, hneg _ h1, h2, by rw [abs_neg]; exact h3, h4, by push_cast; linarith,
      e2.symm⟩
  · exact ⟨-S₁, -S₂, hneg _ h1, hneg _ h2, by rw [abs_neg]; exact h3, by rw [abs_neg]; exact h4,
      by push_cast; linarith, by push_cast; linarith⟩

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row4.flux_signs
#print axioms Erdos634.Geometry.Row4.invariants
