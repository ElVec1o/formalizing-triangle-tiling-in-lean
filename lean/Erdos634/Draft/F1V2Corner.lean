-- Draft/F1V2Corner.lean — V₂ corner filling for prop:F1free (Step 5, Lemma K₂ ingredient).
--
-- Proves:
--   `f1_v2_corner_filling`  (algebraic):  if p·α + q·(π/3−α) + r·(2π/3) + s·π = π/3
--                                          with α/π ∉ ℚ, then (p,q,r,s) = (1,1,0,0).
--   `f1_v2_no_gamma_tile`   (geometric):  in an F₁ dissection with a 2π/3 model, no tile
--                                          presents angle 2π/3 at the π/3-corner V₂.
--
-- Consequence: the γ-vertex of T′ (angle 2π/3) cannot be V₂, so the K₂ argument in
-- PROOF_F1free.md §3 Step 5 reaches a contradiction.  This is one of the two pieces the
-- F1FreeStatement assembly needs from Step 5.
--
-- Pure angle arithmetic (algebraic half) + `corner_multiplicities` (geometric half).
-- ZERO sorry.  (Header updated 2026-10-01: the K₁/K₂ blockers named in F1CornerK are discharged downstream by
-- `F1FreeProof.f1_free_statement`.)

import Erdos634.Draft.F1CornerK
import Erdos634.Draft.FluxE2Pi3Row7

open scoped Classical
open Erdos634.Draft.TheoremPConditional

namespace Erdos634.Geometry

open Erdos634.TilePlacement (corner_multiplicities)
open Erdos634.Geometry.Dissection (congruentDissection_localAngle_mem)

private instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp⟩

/-! ## Algebraic: the V₂ filling is (1,1,0,0) -/

/-- **F₁ V₂-corner counting (algebraic).**  If nonneg integers (p,q,r,s) satisfy
  p·α + q·(π/3−α) + r·(2π/3) + s·π = π/3  with α/π ∉ ℚ,
then (p,q,r,s) = (1,1,0,0).

This is the algebraic core of the K₂ step: no tile contributes angle 2π/3 (γ) at the
π/3-corner V₂ of an F₁ target. -/
theorem f1_v2_corner_filling {α : ℝ} (hirr : IrrPi α) (p q r s : ℕ)
    (hsum : (p : ℝ) * α + (q : ℝ) * (Real.pi / 3 - α) +
            (r : ℝ) * (2 * Real.pi / 3) + (s : ℝ) * Real.pi = Real.pi / 3) :
    p = 1 ∧ q = 1 ∧ r = 0 ∧ s = 0 := by
  -- Rearrange: 3(p−q)·α + (q+2r+3s−1)·π = 0, then apply angle_indep.
  obtain ⟨hA, hB⟩ := angle_indep hirr
    (3 * ((p : ℤ) - q)) ((q : ℤ) + 2 * r + 3 * s - 1)
    (by push_cast; linarith [hsum, show (3 : ℝ) * (Real.pi / 3) = Real.pi from by ring])
  omega

/-! ## Geometric: no tile has angle 2π/3 at V₂ -/

/-- **F₁ V₂ no-γ-tile.**  At the π/3-corner V₂ of an F₁ target with a 2π/3 model,
no tile presents angle 2π/3 (the model's γ-angle).

The corner index `k₂` and the zero-count are both returned.  Consequence: the γ-vertex of
any tile T′ cannot be V₂; together with `tri_adjacent_edges_inter_vertex` (BLOCKER-K2)
this closes Lemma K₂. -/
theorem f1_v2_no_gamma_tile {N : ℕ} (D : CongruentDissection N) {α a b c μ : ℝ}
    (hirr : IrrPi α) (hm : D.model.TwoPiThreeData α a b c)
    (hF1 : D.target.F1Data α a b c μ) :
    ∃ k₂ : Fin 3,
      cornerAngle (D.target.pts (k₂ + 1)) (D.target.pts k₂) (D.target.pts (k₂ + 2)) =
        Real.pi / 3 ∧
      ({i : Fin N | (D.tile i).localAngle (D.target.pts k₂) =
          2 * Real.pi / 3} : Finset (Fin N)).card = 0 := by
  -- Extract σ: σ 1 is the π/3-vertex (V₂)
  obtain ⟨-, hgrid⟩ := hF1
  obtain ⟨σ, -, -, hπ3_eq, -, -, -⟩ := hgrid
  use σ 1
  -- Corner angle at σ 1 = π/3
  have hcorner : cornerAngle (D.target.pts (σ 1 + 1)) (D.target.pts (σ 1))
      (D.target.pts (σ 1 + 2)) = Real.pi / 3 := by
    show D.target.angleAt (σ 1) = Real.pi / 3
    rw [hπ3_eq]; push_cast; ring
  refine ⟨hcorner, ?_⟩
  -- Membership of each tile's local angle at σ 1 in {α, π/3−α, 2π/3, π, 0}
  have hvals : ∀ i, (D.tile i).localAngle (D.target.pts (σ 1)) ∈
      ({α, Real.pi / 3 - α, 2 * Real.pi / 3, Real.pi, 0} : Finset ℝ) :=
    fun i => f1_localAngle_mem D hm (σ 1) i
  -- Corner multiplicity equation at σ 1: n_α·α + n_β·(π/3−α) + n_γ·(2π/3) + n_π·π = π/3
  have hmeq := corner_multiplicities D.toDissection
    α (Real.pi / 3 - α) (2 * Real.pi / 3)
    (irrPi_ne_beta hirr) (irrPi_ne_twoThirdsPi hirr) (irrPi_ne_pi hirr) (irrPi_ne_zero hirr)
    (irrPi_beta_ne_gamma hirr) (irrPi_beta_ne_pi hirr) (irrPi_beta_ne_zero hirr)
    twoThirdsPi_ne_pi twoThirdsPi_ne_zero Real.pi_ne_zero (σ 1) hvals
  rw [hcorner] at hmeq
  -- Apply algebraic lemma: (p,q,r,s) = (1,1,0,0), so r (= n_γ card) = 0
  obtain ⟨-, -, h_r, -⟩ := f1_v2_corner_filling hirr
    ({i | (D.tile i).localAngle (D.target.pts (σ 1)) = α} : Finset (Fin N)).card
    ({i | (D.tile i).localAngle (D.target.pts (σ 1)) = Real.pi / 3 - α} : Finset (Fin N)).card
    ({i | (D.tile i).localAngle (D.target.pts (σ 1)) = 2 * Real.pi / 3} : Finset (Fin N)).card
    ({i | (D.tile i).localAngle (D.target.pts (σ 1)) = Real.pi} : Finset (Fin N)).card
    (by push_cast at hmeq ⊢; linarith)
  exact h_r

end Erdos634.Geometry
