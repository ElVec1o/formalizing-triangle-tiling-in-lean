-- Draft/F1K2Core.lean — No γ-tile at any corner of an F₁ target (Step 5 core, K₂ ingredient).
--
-- Proves:
--   `f1_v3_corner_filling`  (algebraic):   if p·α + q·(π/3−α) + r·(2π/3) + s·π = 2π/3−α
--                                           with α/π ∉ ℚ, then r = 0.
--   `f1_no_gamma_at_corners` (geometric):  in an F₁ dissection with a 2π/3 model, no tile
--                                           presents angle 2π/3 at any corner of the target.
--
-- Together with `tri_adjacent_edges_inter_vertex` (BLOCKER-K2, F1BoundaryK2.lean) this
-- closes Lemma K₂: T′ cannot have its γ-vertex at V₂ (or any corner), so T′ cannot exist.
--
-- Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).  ZERO sorry.

import Erdos634.Draft.F1V2Corner

open scoped Classical
open Erdos634.Draft.TheoremPConditional

namespace Erdos634.Geometry

open Erdos634.TilePlacement (corner_multiplicities)
open Erdos634.Geometry.Dissection (congruentDissection_localAngle_mem)

private instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp⟩

/-! ## Algebraic: the V₃ filling has r = 0 -/

/-- **F₁ V₃-corner counting (algebraic).**  If nonneg integers (p,q,r,s) satisfy
  p·α + q·(π/3−α) + r·(2π/3) + s·π = 2π/3−α  with α/π ∉ ℚ,
then r = 0.

This is the algebraic core for the (2π/3−α)-corner of an F₁ target. -/
theorem f1_v3_corner_filling {α : ℝ} (hirr : IrrPi α) (p q r s : ℕ)
    (hsum : (p : ℝ) * α + (q : ℝ) * (Real.pi / 3 - α) +
            (r : ℝ) * (2 * Real.pi / 3) + (s : ℝ) * Real.pi = 2 * Real.pi / 3 - α) :
    r = 0 := by
  -- Rearrange: 3(p−q+1)·α + (q+2r+3s−2)·π = 0, apply angle_indep.
  -- hA: p = q−1 (hence q ≥ 1); hB: q+2r+3s = 2.  Combined with q ≥ 1: only q=2,r=0,s=0.
  obtain ⟨hA, hB⟩ := angle_indep hirr
    (3 * ((p : ℤ) - q + 1)) ((q : ℤ) + 2 * r + 3 * s - 2)
    (by push_cast; linarith [hsum, show (3 : ℝ) * (Real.pi / 3) = Real.pi from by ring])
  omega

/-! ## Geometric: no γ-tile at any corner -/

/-- **F₁: no γ-tile at any corner.**  In an F₁ dissection with a 2π/3 model and α/π ∉ ℚ,
no tile presents angle 2π/3 at any corner of the target.

This is the key K₂ step: the γ-vertex of any tile T′ cannot coincide with a corner of the
target, so (combined with BLOCKER-K2) the γ-vertex of T′ is not on V₁V₂ at all unless T′'s
a-edge and b-edge both meet V₂ — which is impossible because V₂ has no γ-tile. -/
theorem f1_no_gamma_at_corners {N : ℕ} (D : CongruentDissection N) {α a b c μ : ℝ}
    (hirr : IrrPi α) (hm : D.model.TwoPiThreeData α a b c)
    (hF1 : D.target.F1Data α a b c μ) :
    ∀ (k : Fin 3) (i : Fin N),
      (D.tile i).localAngle (D.target.pts k) ≠ 2 * Real.pi / 3 := by
  -- Extract σ from F1Data
  obtain ⟨-, hgrid⟩ := hF1
  obtain ⟨σ, hα_eq, -, hπ3_eq, -, h2π3α_eq, -⟩ := hgrid
  intro k i hki
  -- Local angle membership for all tiles at k
  have hvals : ∀ j, (D.tile j).localAngle (D.target.pts k) ∈
      ({α, Real.pi / 3 - α, 2 * Real.pi / 3, Real.pi, 0} : Finset ℝ) :=
    fun j => f1_localAngle_mem D hm k j
  -- Corner multiplicity equation at k
  have hmeq := corner_multiplicities D.toDissection
    α (Real.pi / 3 - α) (2 * Real.pi / 3)
    (irrPi_ne_beta hirr) (irrPi_ne_twoThirdsPi hirr) (irrPi_ne_pi hirr) (irrPi_ne_zero hirr)
    (irrPi_beta_ne_gamma hirr) (irrPi_beta_ne_pi hirr) (irrPi_beta_ne_zero hirr)
    twoThirdsPi_ne_pi twoThirdsPi_ne_zero Real.pi_ne_zero k hvals
  -- Set up the four cardinality finsets
  set nα  := ({j : Fin N | (D.tile j).localAngle (D.target.pts k) = α} : Finset (Fin N)).card
  set nβ  := ({j : Fin N | (D.tile j).localAngle (D.target.pts k) = Real.pi / 3 - α}
               : Finset (Fin N)).card
  set nγ  := ({j : Fin N | (D.tile j).localAngle (D.target.pts k) = 2 * Real.pi / 3}
               : Finset (Fin N)).card
  set nπ  := ({j : Fin N | (D.tile j).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card
  -- tile i is in the γ-set
  have hi_mem : i ∈ ({j : Fin N | (D.tile j).localAngle (D.target.pts k) = 2 * Real.pi / 3}
                      : Finset (Fin N)) := by simpa using hki
  have hnγ_pos : 0 < nγ := Finset.card_pos.mpr ⟨i, hi_mem⟩
  -- Dispatch by which corner k is
  -- The three corners are σ 0 (α), σ 1 (π/3), σ 2 (2π/3-α); k is one of them.
  -- Use fin_cases or rcases on k being in the image of σ.
  -- We need: the corner angle at k is < 2π/3.
  -- Case: k = σ 0, corner = α → f1_corner_single_tile gives nγ = 0.
  -- Case: k = σ 1, corner = π/3 → f1_v2_corner_filling gives nγ = 0.
  -- Case: k = σ 2, corner = 2π/3-α → f1_v3_corner_filling gives nγ = 0.
  -- In each case nγ = 0 contradicts hnγ_pos.
  -- Since σ is a bijection Fin 3 → Fin 3, k = σ 0 ∨ k = σ 1 ∨ k = σ 2.
  have hcov : k = σ 0 ∨ k = σ 1 ∨ k = σ 2 := by
    have : Function.Surjective σ := σ.surjective
    obtain ⟨j, hj⟩ := this k
    fin_cases j <;> simp_all
  rcases hcov with rfl | rfl | rfl
  · -- k = σ 0, corner angle = α
    have hcorner : cornerAngle (D.target.pts (σ 0 + 1)) (D.target.pts (σ 0))
        (D.target.pts (σ 0 + 2)) = α := by
      show D.target.angleAt (σ 0) = α; rw [hα_eq]; push_cast; ring
    rw [hcorner] at hmeq
    obtain ⟨-, -, h3, -⟩ := f1_corner_single_tile hirr nα nβ nγ nπ (by push_cast at hmeq ⊢; linarith)
    omega
  · -- k = σ 1, corner angle = π/3
    have hcorner : cornerAngle (D.target.pts (σ 1 + 1)) (D.target.pts (σ 1))
        (D.target.pts (σ 1 + 2)) = Real.pi / 3 := by
      show D.target.angleAt (σ 1) = Real.pi / 3; rw [hπ3_eq]; push_cast; ring
    rw [hcorner] at hmeq
    obtain ⟨-, -, h3, -⟩ := f1_v2_corner_filling hirr nα nβ nγ nπ (by push_cast at hmeq ⊢; linarith)
    omega
  · -- k = σ 2, corner angle = 2π/3 - α
    have hcorner : cornerAngle (D.target.pts (σ 2 + 1)) (D.target.pts (σ 2))
        (D.target.pts (σ 2 + 2)) = 2 * Real.pi / 3 - α := by
      show D.target.angleAt (σ 2) = 2 * Real.pi / 3 - α; rw [h2π3α_eq]; push_cast; ring
    rw [hcorner] at hmeq
    have h3 := f1_v3_corner_filling hirr nα nβ nγ nπ (by push_cast at hmeq ⊢; linarith)
    omega

end Erdos634.Geometry
