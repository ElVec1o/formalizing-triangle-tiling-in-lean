/-
Draft/N240.lean -- `240` is a tile count: the equilateral triangle of side `60` is cut into `240` copies of `(3, 5, 7)`.

`R240TilingBridge.r240_dissection_shape` (kernel-checked certificate `R240Tiling`, coordinates in `ℤ[√3]`): the
equilateral triangle with side `840 = 14 · 60` is cut into `240` congruent triangles with sides
`42, 70, 98 = 14 · (3, 5, 7)`.

    theorem tileCount_240 : TileCount 240
    theorem equilateral_60_by_357 :
        ∃ D : CongruentDissection 240, HasSides D.target 60 60 60 ∧ HasSides D.model 3 5 7

THE TILING IS NOT OURS.  It is D. Paliy's 240-tile seed (`research/final-closure-oct8/equilateral240/`,
`MACRO_240_PROOF.md`, 8 October 2026, in `github.com/DenisUkranian/erdos-634-tilings`; unrefereed): fifteen convex
polygons of the triangular lattices of the tile.  The 240 triangles were reconstructed here from his table of
regions (`data/witnesses/tiling_240_3_5_7_on_60_60_60.exact.txt`), verified exactly by
(private working notes, not included), and turned into the certificate by (private working notes, not included).
What this file adds is a check by the Lean kernel.  Our own search for this tiling (lowest uncovered point, 30
minutes) did not find it.

WHY IT MATTERS HERE.  The side of an equilateral triangle tiled by `(3, 5, 7)` is `15 m`.  A sentence in the
literature (Y. X. Zhang, arXiv:2512.22696v4, p. 6, citing M. Beeson's "Tiling an equilateral triangle") says that
sides below `105` "are known to not exist".  This tiling has side `60`: that sentence is false, and no analytic
bound of that form can be formalized.  (Beeson's paper states a computer exclusion for `N < 105` in its section on
tiles with an angle `π/3`; for an angle `2π/3` it states only that `N` is not prime and `N ≥ 12`.)  The case
`m = 3` (side `45`, `N = 135`) is NOT decided by this file.

Composite-N statement; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.R240TilingBridge
import Erdos634.Realizable
import Erdos634.Draft.TileCountFamilies
import Erdos634.Draft.HasSidesPerm

namespace Erdos634.Draft.N240

open Erdos634.Geometry Erdos634.Draft.TileCountFamilies Erdos634.Draft.FDBBaseBetaE1

/-- **240 is a tile count** (tiling due to D. Paliy; kernel-checked here). -/
theorem tileCount_240 : TileCount 240 := Erdos634.R240TilingBridge.r240_nonempty_congruentDissection

/-- `240 k²` is a tile count for every `k ≥ 1`. -/
theorem tileCount_240_sq {k : ℕ} (hk : 0 < k) : TileCount (k * k * 240) := tileCount_scale tileCount_240 hk

theorem eq_of_sq {d c : ℝ} (hd : 0 ≤ d) (hc : 0 < c) (h : d ^ 2 = c ^ 2) : d = c := by
  have h2 : (d - c) * (d + c) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · linarith
  · linarith

open Erdos634.Realizable in
/-- **The equilateral triangle of side `60` is cut into `240` congruent triangles with sides `3, 5, 7`.** -/
theorem equilateral_60_by_357 :
    ∃ D : CongruentDissection 240, HasSides D.target 60 60 60 ∧ HasSides D.model 3 5 7 := by
  obtain ⟨D, t01, t12, t20, m01, m12, m20⟩ := Erdos634.R240TilingBridge.r240_dissection_shape
  have hν : (0:ℝ) < 1 / 14 := by norm_num
  set Ds := scaleDissection (D.model.pts 0) (1 / 14) hν.ne' D with hDs
  have htd : ∀ i j : Fin 3,
      dist (Ds.target.pts i) (Ds.target.pts j) = 1 / 14 * dist (D.target.pts i) (D.target.pts j) := by
    intro i j
    rw [hDs, scaleDissection_target_pts, scaleDissection_target_pts, homothetyEquiv_dist, abs_of_pos hν]
  have hmd : ∀ i j : Fin 3,
      dist (Ds.model.pts i) (Ds.model.pts j) = 1 / 14 * dist (D.model.pts i) (D.model.pts j) := by
    intro i j
    rw [hDs, scaleDissection_model_pts, scaleDissection_model_pts, homothetyEquiv_dist, abs_of_pos hν]
  have T01 : dist (D.target.pts 0) (D.target.pts 1) = 840 :=
    eq_of_sq dist_nonneg (by norm_num) (by rw [t01]; norm_num)
  have T12 : dist (D.target.pts 1) (D.target.pts 2) = 840 :=
    eq_of_sq dist_nonneg (by norm_num) (by rw [t12]; norm_num)
  have T20 : dist (D.target.pts 2) (D.target.pts 0) = 840 :=
    eq_of_sq dist_nonneg (by norm_num) (by rw [t20]; norm_num)
  have M01 : dist (D.model.pts 0) (D.model.pts 1) = 42 :=
    eq_of_sq dist_nonneg (by norm_num) (by rw [m01]; norm_num)
  have M12 : dist (D.model.pts 1) (D.model.pts 2) = 98 :=
    eq_of_sq dist_nonneg (by norm_num) (by rw [m12]; norm_num)
  have M20 : dist (D.model.pts 2) (D.model.pts 0) = 70 :=
    eq_of_sq dist_nonneg (by norm_num) (by rw [m20]; norm_num)
  -- `HasSides T a b c` with the identity labelling reads `dist 1 2 = a`, `dist 2 0 = b`, `dist 0 1 = c`
  have hT : HasSides Ds.target 60 60 60 :=
    ⟨Equiv.refl _, by simp only [Equiv.refl_apply]; rw [htd, T12]; norm_num,
      by simp only [Equiv.refl_apply]; rw [htd, T20]; norm_num,
      by simp only [Equiv.refl_apply]; rw [htd, T01]; norm_num⟩
  have hM : HasSides Ds.model 7 5 3 :=
    ⟨Equiv.refl _, by simp only [Equiv.refl_apply]; rw [hmd, M12]; norm_num,
      by simp only [Equiv.refl_apply]; rw [hmd, M20]; norm_num,
      by simp only [Equiv.refl_apply]; rw [hmd, M01]; norm_num⟩
  exact ⟨Ds, hT, hasSides_rot (hasSides_rot (hasSides_swap hM))⟩

end Erdos634.Draft.N240

#print axioms Erdos634.Draft.N240.tileCount_240
#print axioms Erdos634.Draft.N240.equilateral_60_by_357
