-- Draft/F1K2Contradiction.lean — K₂ core contradiction (Step 5 of prop:F1free).
--
-- Proves:
--   `f1_k2_contradiction` — if a tile in an F₁ dissection has its γ-vertex X lying on
--                            two DISTINCT sides of the target, then False.
--
-- This is the abstract K₂ step.  The caller (F1FreeStatement assembly) will supply:
--   (a) the γ-vertex X = (D.tile i).pts(σ'(2)) of T′,
--   (b) j₁ = the target side containing T′'s a-edge (hence X ∈ target.edge j₁), and
--   (c) j₂ = the target side containing T′'s b-edge (hence X ∈ target.edge j₂).
-- Since j₁ ≠ j₂, by `tri_adjacent_edges_inter_vertex` X is a corner of the target, and
-- `f1_no_gamma_at_corners` yields the contradiction.
--
-- Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).  ZERO sorry.

import Erdos634.Draft.F1K2Core
import Erdos634.Draft.F1BoundaryK2

open scoped Classical
open Erdos634.Draft.TheoremPConditional

namespace Erdos634.Geometry

private instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp⟩

/-- **K₂ contradiction.** In an F₁ dissection, if a tile's γ-vertex lies on two distinct
sides of the target, that is impossible: it would have to be a corner of the target, but
`f1_no_gamma_at_corners` shows no tile presents angle 2π/3 at any corner. -/
theorem f1_k2_contradiction {N : ℕ} (D : CongruentDissection N) {α a b c μ : ℝ}
    (hirr : IrrPi α) (hm : D.model.TwoPiThreeData α a b c)
    (hF1 : D.target.F1Data α a b c μ)
    -- tile i has its γ-vertex at X
    (i : Fin N) (X : Plane)
    (hγ : (D.tile i).localAngle X = 2 * Real.pi / 3)
    -- X lies on two DISTINCT sides of the target
    (j₁ j₂ : Fin 3) (hj : j₁ ≠ j₂)
    (hX1 : X ∈ D.target.edge j₁)
    (hX2 : X ∈ D.target.edge j₂) :
    False := by
  -- Step 1: identify the shared vertex by a Fin 3 case split.
  -- For any two distinct sides of a triangle, tri_adjacent_edges_inter_vertex (applied in the
  -- right order) forces their intersection to the shared vertex.
  have hno := f1_no_gamma_at_corners D hirr hm hF1
  fin_cases j₁ <;> fin_cases j₂ <;> simp_all (config := { decide := true }) <;>
  { first
    | { -- j₂ = j₁ + 1: apply with k = j₁
        have hX := tri_adjacent_edges_inter_vertex D.target _ hX1 hX2
        exact hno _ i (hX ▸ hγ) }
    | { -- j₁ = j₂ + 1: apply with k = j₂ (swap roles)
        have hX := tri_adjacent_edges_inter_vertex D.target _ hX2 hX1
        exact hno _ i (hX ▸ hγ) } }

end Erdos634.Geometry
