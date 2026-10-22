-- Draft/F1BoundaryK2.lean — BLOCKER-K2: adjacent sides of a triangle share only their vertex.
--
-- Proves:
--   `tri_adjacent_edges_inter_vertex` — if X lies on edge k and edge (k+1) of a triangle,
--                                        then X equals their shared vertex T.pts (k+1).
--
-- This is BLOCKER-K2 of `prop:F1free` / `F1FreeStatement`.
-- Pure geometry from AffineBasis; no dissection machinery.
-- Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).  ZERO sorry.

import Erdos634.SideWall

namespace Erdos634.Geometry

open Erdos634

private lemma fin3_add3_eq (k : Fin 3) : k + 3 = k := by fin_cases k <;> decide
private lemma fin3_kp2_add1_eq (k : Fin 3) : k + 2 + 1 = k + 3 := by fin_cases k <;> decide
private lemma fin3_kp3_eq (k : Fin 3) : k + 2 + 1 = k := by fin_cases k <;> decide

/-- **BLOCKER-K2.** In a non-degenerate triangle, two adjacent edges share only their common
vertex: if `X ∈ edge k ∩ edge (k+1)` then `X = T.pts (k+1)`. -/
theorem tri_adjacent_edges_inter_vertex (T : Tri) (k : Fin 3) {X : Plane}
    (hek : X ∈ T.edge k) (hek1 : X ∈ T.edge (k + 1)) :
    X = T.pts (k + 1) := by
  -- Step 1: from X ∈ edge k, get coord (k+2) X = 0
  have hc_kp2 : T.basis.coord (k + 2) X = 0 := by
    have := Erdos634.SideWall.wallFun_eq_zero T k hek
    simp [Erdos634.SideWall.wallFun] at this
    linarith
  -- Step 2: from X ∈ edge (k+1), get coord ((k+1)+2) X = coord k X = 0
  -- Note: (k+1)+2 = k+3 = k in Fin 3
  have hc_k : T.basis.coord k X = 0 := by
    have h := Erdos634.SideWall.wallFun_eq_zero T (k + 1) hek1
    simp [Erdos634.SideWall.wallFun] at h
    -- wallFun T (k+1) = -(coord ((k+1)+2)) = -(coord (k+3)) = -(coord k)
    have heq : ((k : Fin 3) + 1 + 2 : Fin 3) = k := by fin_cases k <;> decide
    rw [← heq]; linarith
  -- Step 3: coords sum to 1, so coord (k+1) X = 1
  have hsum : ∑ i, T.basis.coord i X = 1 := T.basis.sum_coord_apply_eq_one X
  have hc_kp1 : T.basis.coord (k + 1) X = 1 := by
    rw [Fin.sum_univ_three] at hsum
    -- hsum : coord 0 + coord 1 + coord 2 = 1
    -- Need: coord (k+1) = 1 given coord k = 0, coord (k+2) = 0
    fin_cases k <;> simp_all
  -- Step 4: X = T.pts (k+1) from the linear combination formula
  have hrec : ∑ i, T.basis.coord i X • T.pts i = X :=
    T.basis.linear_combination_coord_eq_self X
  rw [← hrec, Fin.sum_univ_three]
  fin_cases k <;> simp_all [zero_smul, one_smul, zero_add, add_zero]

end Erdos634.Geometry
