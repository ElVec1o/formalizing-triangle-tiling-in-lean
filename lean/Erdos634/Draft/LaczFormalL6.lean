-- Draft/LaczFormalL6.lean -- atom L6 (irrational half): tile angles of a congruent dissection of an
-- EQUILATERAL triangle when the tile has an irrational angle.
-- Statement source: Beeson-Rosu (arXiv 2607.23453), proof of Theorem 3, list (i)-(v), attributed to
-- Laczkovich, Tilings of triangles / DCG 48 (2012), Thm 3.3; cases (iv), (v):
-- tile angles (alpha, beta, pi/3) or (alpha, beta, 2pi/3), alpha not in Q*pi.
-- Proof: from OUR `LemmaCFinal.lemmaC_general` (shape classification, any N), by inspecting the five
-- cases at an equilateral target.  The rational cases (i)-(iii) are NOT here (they need Laczkovich's
-- commensurable-angle classification; see TABLE.md, atoms L6/L9).
-- UNAUDITED beyond TABLE.md.
import Erdos634.Draft.LaczFormalBase
import Erdos634.Draft.G3CSixtyControl
import Erdos634.Draft.G3CEqui135Control

open scoped Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional

namespace Erdos634.Draft.LaczFormal

/-- **L6, irrational half (Laczkovich 2012, Thm 3.3 (iv),(v); Beeson-Rosu proof of Thm 3).**
A congruent dissection (any `N`, reflections allowed, not necessarily edge to edge) of an equilateral
triangle by a tile with an irrational angle: the tile's angles are `(α, 2π/3−α, π/3)` or
`(α, π/3−α, 2π/3)` with `α ∉ ℚπ`. -/
theorem equilateral_tile_irr {N : ℕ} (D : CongruentDissection N) (hEq : Equilateral D)
    (hirr : ∃ k, IrrPi (D.model.angleAt k)) :
    (∃ α : ℝ, IrrPi α ∧ TileAngles D α (2 * Real.pi / 3 - α) (Real.pi / 3)) ∨
    (∃ α : ℝ, IrrPi α ∧ TileAngles D α (Real.pi / 3 - α) (2 * Real.pi / 3)) := by
  by_cases hs : SimilarTM D
  · exfalso
    obtain ⟨μ, τ, h⟩ := hs
    obtain ⟨k, hk⟩ := hirr
    have := (h (τ.symm k)).1
    rw [hEq, Equiv.apply_symm_apply] at this
    exact hk ⟨1 / 3, by rw [← this]; push_cast; ring⟩
  rcases Erdos634.Draft.LemmaCFinal.lemmaC_general D hirr hs with
    h | h | h | h | h
  · -- right tile
    exfalso
    obtain ⟨α, -, -, hα0, -, γ, hγ, i, j, -, hi, -⟩ := h
    have hα := irrPi_of_irrational hα0
    have hi' := hEq i
    rw [hi] at hi'
    rcases hγ with h | h
    · exact irrPi_ne hα (1 / 3) (by push_cast; linarith)
    · exact irrPi_ne hα (1 / 6) (by push_cast; linarith)
  · exfalso
    obtain ⟨α, a, b, c, hα, -, i, j, -, hi, -⟩ := h
    have hi' := hEq i
    rw [hi] at hi'
    exact irrPi_ne hα (1 / 3) (by push_cast; linarith)
  · obtain ⟨α, a, b, c, hα, σ, h0, -, h1, -, h2, -⟩ := h
    exact Or.inl ⟨α, hα, σ, h0, h1, h2⟩
  · obtain ⟨α, a, b, c, hα, hd, -⟩ := h
    obtain ⟨σ, h0, -, h1, -, h2, -⟩ := hd
    exact Or.inr ⟨α, hα, σ, h0, h1, h2⟩
  · exfalso
    obtain ⟨α, β, a, b, c, hα, hrel, -, hsh⟩ := h
    rcases hsh with h | h | h | h | h
    · have := (tgt_eq_third hEq h).2.2
      exact irrPi_ne hα (1 / 9) (by push_cast; linarith)
    · have := (tgt_eq_third hEq h).2.2
      exact irrPi_ne hα (1 / 3) (by push_cast; linarith)
    · have := (tgt_eq_third hEq h).1
      exact irrPi_ne hα (1 / 6) (by push_cast; linarith)
    · have := (tgt_eq_third hEq h).2.1
      exact irrPi_ne hα (1 / 3) (by push_cast; linarith)
    · have := (tgt_eq_third hEq h).1
      exact irrPi_ne hα (1 / 3) (by push_cast; linarith)

/-- Non-vacuity (π/3 branch): the hypotheses hold for the certified `N = 1440` dissection of an
equilateral triangle by the tile `3360·(5,8,7)` (`cos α = 11/14`, `α ∉ ℚπ`). -/
theorem equilateral_tile_irr_witness_60 :
    ∃ (N : ℕ) (D : CongruentDissection N), Equilateral D ∧ ∃ k, IrrPi (D.model.angleAt k) := by
  obtain ⟨N, D, α, a, b, c, hα, ⟨σ, h0, -⟩, -, hE⟩ :=
    Erdos634.Draft.G3CSixtyControl.lemmaP_premises_satisfied
  exact ⟨N, D, hE, σ 0, h0 ▸ hα⟩

/-- Non-vacuity (2π/3 branch): `N = 1215`, tile `1890·(3,5,7)`, `cos α = 13/14`. -/
theorem equilateral_tile_irr_witness_120 :
    ∃ (N : ℕ) (D : CongruentDissection N), Equilateral D ∧ ∃ k, IrrPi (D.model.angleAt k) := by
  obtain ⟨hα, ⟨σ, h0, -⟩, hE⟩ := Erdos634.Draft.G3CEqui135Control.premises
  exact ⟨_, _, hE, σ 0, h0 ▸ hα⟩

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.equilateral_tile_irr
#print axioms Erdos634.Draft.LaczFormal.equilateral_tile_irr_witness_60
#print axioms Erdos634.Draft.LaczFormal.equilateral_tile_irr_witness_120
