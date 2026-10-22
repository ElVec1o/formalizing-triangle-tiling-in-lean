-- Draft/FluxRow11.lean — consumer corollaries for rows 11/12 (step C: the χ± identities) and the
-- rationality layer (Beeson III Thm 1, the χ₋ half), for the `3α + 2β = π` tile family.
-- Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).  Design: (private working notes, not included) §4.2 rows 11/12, rationality.
--
-- Grid: `L = ℤπ + ℤθ`, `θ = α/2 + π/2` (∉ ℚπ when α ∉ ℚπ; cf. `BaseBetaE1.direction_free`).
-- The tile angles are `α = −π + 2θ`, `β = 2π − 3θ`, `γ = 2α + β = θ`.  `χ₊ = (−1)^j`,
-- `χ₋ = (−1)^(j+k)` on `jπ + kθ`; tile values `K₊ = −(c + b − a)`, `K₋ = a + b + c`.
-- No global direction-grid lemma is used (DESIGN.md §4.1): the colouring-existence step of Beeson's
-- Theorem 1 is replaced by the coset-representative weight.
--
-- NOT given here (named, per DESIGN.md §4.2): L4 algebra, L5a/L5b, the law of sines for the target,
-- R12's anchoring repair, the case split (B); the shape-specific boundary evaluations
-- (`Row11.boundary_baseAlpha` etc.) except on the real 44-tiling (`FluxGridWitness`).
-- Formalization debt; not progress on the /goal.
import Erdos634.Draft.FluxGrids
import Erdos634.Draft.FluxValue

open scoped Classical

namespace Erdos634.Geometry

/-- `θ = α/2 + π/2 ∉ ℚπ` when `α ∉ ℚπ`. -/
theorem theta_irr_of_alpha {α : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) :
    ¬ ∃ r : ℚ, α / 2 + Real.pi / 2 = (r : ℝ) * Real.pi := by
  rintro ⟨r, hr⟩
  apply hα
  refine ⟨2 * r - 1, ?_⟩
  push_cast
  linear_combination 2 * hr

/-- **χ₊** of rows 11/12: `(−1)^j` on `jπ + kθ`, anchor `0`. -/
noncomputable def chiPlus (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) : GridChar ℝ :=
  GridChar.rank2 (α / 2 + Real.pi / 2) (theta_irr_of_alpha hα) 0 0

/-- **χ₋** of rows 11/12 and Beeson III Thm 1: `(−1)^(j+k)` on `jπ + kθ`, anchor `0`. -/
noncomputable def chiMinus (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) : GridChar ℝ :=
  GridChar.rank2 (α / 2 + Real.pi / 2) (theta_irr_of_alpha hα) 1 0

/-- **A placement of the `3α + 2β = π` tile**: under some vertex order, angles `(α, β, 2α + β)`
with opposite sides `(a, b, c)`. -/
def Tri.ThreeAlphaData (T : Tri) (α β a b c : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3),
    T.angleAt (σ 0) = α ∧ T.oppLen (σ 0) = a ∧
    T.angleAt (σ 1) = β ∧ T.oppLen (σ 1) = b ∧
    T.angleAt (σ 2) = 2 * α + β ∧ T.oppLen (σ 2) = c

theorem Tri.threeAlpha_angles_mem {T : Tri} {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : T.ThreeAlphaData α β a b c) (b' : ZMod 2) :
    ∀ j, ((T.angleAt j : ℝ) : Real.Angle)
      ∈ (GridChar.rank2 (α / 2 + Real.pi / 2) (theta_irr_of_alpha hα) b' 0).L := by
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := h
  intro j
  obtain ⟨k, rfl⟩ := σ.surjective j
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  rcases hk with rfl | rfl | rfl
  · rw [h0, show ((α : ℝ) : Real.Angle)
        = ((((-1 : ℤ) : ℝ) * Real.pi + ((2 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) : ℝ) : Real.Angle) by
      congr 1; push_cast; ring]
    exact GridChar.rank2_mem _ _ _ _ _ _
  · rw [h1, show β = ((2 : ℤ) : ℝ) * Real.pi + ((-3 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) by
      push_cast; linarith]
    exact GridChar.rank2_mem _ _ _ _ _ _
  · rw [h2, show 2 * α + β = ((0 : ℤ) : ℝ) * Real.pi + ((1 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) by
      push_cast; linarith]
    exact GridChar.rank2_mem _ _ _ _ _ _

/-- The tile value on the rank-2 grid, from the three exterior angles
`π − α = 2π − 2θ`, `π − β = −π + 3θ`, `π − γ = π − θ`. -/
theorem threeAlpha_tileValue (T : Tri) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : T.ThreeAlphaData α β a b c) (b' : ZMod 2) :
    (GridChar.rank2 (α / 2 + Real.pi / 2) (theta_irr_of_alpha hα) b' 0).tileValue T
      = (if ((2 : ℤ) : ZMod 2) + b' * ((-2 : ℤ) : ZMod 2) = 0 then 1 else -1) * a
        + (if ((-1 : ℤ) : ZMod 2) + b' * ((3 : ℤ) : ZMod 2) = 0 then 1 else -1) * b
        + (if ((1 : ℤ) : ZMod 2) + b' * ((-1 : ℤ) : ZMod 2) = 0 then 1 else -1) * c := by
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  unfold GridChar.tileValue
  rw [← Equiv.sum_comp σ (fun j =>
    (GridChar.rank2 (α / 2 + Real.pi / 2) (theta_irr_of_alpha hα) b' 0).chi
      ((Real.pi - T.angleAt j : ℝ) : Real.Angle) * T.oppLen j), Fin.sum_univ_three]
  rw [h0, o0, h1, o1, h2, o2,
    show Real.pi - α = ((2 : ℤ) : ℝ) * Real.pi + ((-2 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) by
      push_cast; ring,
    show Real.pi - β = ((-1 : ℤ) : ℝ) * Real.pi + ((3 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) by
      push_cast; linarith,
    show Real.pi - (2 * α + β) = ((1 : ℤ) : ℝ) * Real.pi + ((-1 : ℤ) : ℝ) * (α / 2 + Real.pi / 2) by
      push_cast; linarith,
    GridChar.rank2_chi, GridChar.rank2_chi, GridChar.rank2_chi]

theorem threeAlpha_tileValue_plus (T : Tri) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : T.ThreeAlphaData α β a b c) : (chiPlus α hα).tileValue T = -(c + b - a) := by
  unfold chiPlus
  rw [threeAlpha_tileValue T hα hrel h 0, if_pos (by decide), if_neg (by decide),
    if_neg (by decide)]
  ring

theorem threeAlpha_tileValue_minus (T : Tri) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : T.ThreeAlphaData α β a b c) : (chiMinus α hα).tileValue T = a + b + c := by
  unfold chiMinus
  rw [threeAlpha_tileValue T hα hrel h 1, if_pos (by decide), if_pos (by decide),
    if_pos (by decide)]
  ring

/-- **Rows 11/12, step C (`Row11.chi_identities`).**  For an `N`-tiling by a `3α + 2β = π` tile
with `α ∉ ℚπ`, the boundary fluxes are `Φ₊ = K (c + b − a)` and `Φ₋ = M (a + b + c)` with integers
`K ≡ M ≡ N (mod 2)`, `|K|, |M| ≤ N`.  No target-shape hypothesis. -/
theorem Row11.chi_identities {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) :
    ∃ K M : ℤ, (2 : ℤ) ∣ K - N ∧ (2 : ℤ) ∣ M - N ∧ |K| ≤ N ∧ |M| ≤ N ∧
      D.target.flux (chiPlus α hα).weight = (K : ℝ) * (c + b - a) ∧
      D.target.flux (chiMinus α hα).weight = (M : ℝ) * (a + b + c) := by
  obtain ⟨S, hS2, hSN, hSf⟩ := D.target_flux_signs (chiPlus α hα)
    (GridChar.rank2_sq _ _ _ _) (D.model.threeAlpha_angles_mem hα hrel h 0)
  obtain ⟨S', hS2', hSN', hSf'⟩ := D.target_flux_signs (chiMinus α hα)
    (GridChar.rank2_sq _ _ _ _) (D.model.threeAlpha_angles_mem hα hrel h 1)
  refine ⟨-S, S', ?_, hS2', ?_, hSN', ?_, ?_⟩
  · rw [show -S - (N : ℤ) = -(S - N) - 2 * N by ring]
    exact dvd_sub (dvd_neg.mpr hS2) (dvd_mul_right 2 _)
  · rw [abs_neg]; exact hSN
  · rw [hSf, threeAlpha_tileValue_plus D.model hα hrel h]; push_cast; ring
  · rw [hSf', threeAlpha_tileValue_minus D.model hα hrel h]

/-- **Beeson III, Theorem 1 (the colouring number), without the colouring-existence step.**
`Φ₋(∂ABC) = M (a + b + c)` with `M ≡ N (mod 2)`, `|M| ≤ N`. -/
theorem Rationality.beeson_thm1 {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) :
    ∃ M : ℤ, (2 : ℤ) ∣ M - N ∧ |M| ≤ N ∧
      D.target.flux (chiMinus α hα).weight = (M : ℝ) * (a + b + c) := by
  obtain ⟨-, M, -, hM2, -, hMN, -, hMf⟩ := Row11.chi_identities D hα hrel h
  exact ⟨M, hM2, hMN, hMf⟩

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row11.chi_identities
#print axioms Erdos634.Geometry.Rationality.beeson_thm1
