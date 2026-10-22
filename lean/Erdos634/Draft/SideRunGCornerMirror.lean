/-
Draft/SideRunGCornerMirror.lean -- written 14 October 2026.  UNAUDITED.  In `AllThreshold`.  Module R2 (mirror file) of the plan for `thm:cornerrun`: **the mirror condition of alternative (ii), literally**.

PAPER.  `thm:cornerrun`, (ii): "... whose first tile and the tile beside it at `A'` are mirror images in their common `b`-edge ...".

WHAT IS PROVED HERE.
* `MirrorBeside D₀ e f A' i₀ T`: the first tile `i₀` has the vertices `A'`, `E`, `W` with `|W A'| = b = f² − e²` (so `A' W` is its `b`-edge at `A'`); the tile `T` has the vertices `A'`, `W` (it is beside `i₀`, across this edge) and a third
  vertex `R` which is the REFLECTION of `E` in the line `A' W` (`EuclideanGeometry.reflection (affineSpan ℝ {A', W}) E`).
* `MirrorDist D₀ e f A' i₀ T`: the same in distances (the form that the lattice gives): `|E A'| = c`, `|W A'| = b`, `|E W| = a`, and `T` has the vertices `A'`, `W`, `R` with `R ≠ E`, `|R A'| = |E A'|`, `|R W| = |E W|`.
* `mirrorBeside_of_dist`: `MirrorDist → MirrorBeside` (`0 < e < f`).  The vertices `E` is not on the line `A' W` (the three distances `c, b, a` cannot be those of three collinear points: `|t| b = c`, `|1 − t| b = a` has no solution for `0 < e < f`),
  so `E` is not its own reflection; the reflection of `E` has the same distances from `A'` and `W` as `E`; two circles in the plane meet in at most two points (`EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two`), so `R ≠ E` is the reflection.

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunTools
import Mathlib.Geometry.Euclidean.Projection
import Mathlib.Geometry.Euclidean.Basic

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.SideRunGA

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Set

variable {N : ℕ}

/-- **The mirror condition of (ii)** (paper: "whose first tile and the tile beside it at `A'` are mirror images in their common `b`-edge"), for the dissection `D₀`: the first tile `i₀` has the vertices `A'`, `E`, `W`, with
`|W A'| = b = f² − e²` (so `A' W` is its `b`-edge at `A'`); the tile `T` has the vertices `A'`, `W` (it is beside `i₀`, across this edge) and a third vertex `R`, the reflection of `E` in the line `A' W`. -/
def MirrorBeside (D₀ : CongruentDissection N) (e f : ℝ) (A' : Plane) (i₀ T : Fin N) : Prop :=
  ∃ E W R : Plane, HasV D₀ i₀ A' E W ∧ dist W A' = f ^ 2 - e ^ 2 ∧ HasV D₀ T A' W R ∧
    R = EuclideanGeometry.reflection (affineSpan ℝ {A', W}) E

/-- the mirror condition in distances: the first tile has the sides `|A' E| = c`, `|A' W| = b`, `|E W| = a`; the tile `T` beside it has the vertices `A'`, `W`, and a third vertex `R ≠ E` at the same distances `c`, `a` from `A'`, `W` -/
def MirrorDist (D₀ : CongruentDissection N) (e f : ℝ) (A' : Plane) (i₀ T : Fin N) : Prop :=
  ∃ E W R : Plane, HasV D₀ i₀ A' E W ∧ dist E A' = f ^ 2 ∧ dist W A' = f ^ 2 - e ^ 2 ∧ dist E W = e * f ∧
    HasV D₀ T A' W R ∧ R ≠ E ∧ dist R A' = dist E A' ∧ dist R W = dist E W

/-- the distances `c, b, a` of a triangle with `0 < e < f` are not those of three collinear points -/
theorem not_collinear_dist {e f : ℝ} (he : 0 < e) (hef : e < f) {A' W E : Plane}
    (hEA : dist E A' = f ^ 2) (hWA : dist W A' = f ^ 2 - e ^ 2) (hEW : dist E W = e * f) :
    E ∉ affineSpan ℝ {A', W} := by
  intro hmem
  have hf : 0 < f := he.trans hef
  obtain ⟨t, ht⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq (k := ℝ)).mp hmem
  have h1 : dist E A' = |t| * (f ^ 2 - e ^ 2) := by
    rw [← ht, dist_lineMap_left, Real.norm_eq_abs, dist_comm A' W, hWA]
  have h2 : dist E W = |1 - t| * (f ^ 2 - e ^ 2) := by
    rw [← ht, dist_lineMap_right, Real.norm_eq_abs, dist_comm A' W, hWA]
  rw [hEA] at h1
  rw [hEW] at h2
  have hp1 := mul_pos he (sub_pos.mpr hef)
  have hp2 := mul_pos he hf
  have hp3 := mul_pos (sub_pos.mpr hef) (show 0 < 2 * f + e by linarith)
  rcases le_or_gt 0 t with h0 | h0
  · rw [abs_of_nonneg h0] at h1
    rcases le_or_gt 1 t with h3 | h3
    · rw [abs_of_nonpos (by linarith)] at h2
      nlinarith
    · rw [abs_of_pos (by linarith)] at h2
      nlinarith
  · rw [abs_of_neg h0] at h1
    rw [abs_of_pos (by linarith)] at h2
    nlinarith

/-- **`MirrorDist → MirrorBeside`**: the third vertex `R ≠ E` of the tile `T` beside the first tile across its `b`-edge, which has the distances of `E` from `A'` and `W`, is the reflection of `E` in the line `A' W` -/
theorem mirrorBeside_of_dist {D₀ : CongruentDissection N} {e f : ℝ} (he : 0 < e) (hef : e < f) {A' : Plane}
    {i₀ T : Fin N} (h : MirrorDist D₀ e f A' i₀ T) : MirrorBeside D₀ e f A' i₀ T := by
  obtain ⟨E, W, R, hV, hEA, hWA, hEW, hT, hRE, hRA, hRW⟩ := h
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
  have hAW : A' ≠ W := by
    intro h
    rw [← h, dist_self] at hWA
    linarith
  refine ⟨E, W, R, hV, hWA, hT, ?_⟩
  have hA's : A' ∈ affineSpan ℝ {A', W} := left_mem_affineSpan_pair ℝ A' W
  have hWs : W ∈ affineSpan ℝ {A', W} := right_mem_affineSpan_pair ℝ A' W
  have hEs := not_collinear_dist he hef hEA hWA hEW
  have hfin : Module.finrank ℝ Plane = 2 := finrank_euclideanSpace_fin
  have hd1 : dist (EuclideanGeometry.reflection (affineSpan ℝ {A', W}) E) A' = dist E A' := by
    rw [dist_comm, EuclideanGeometry.dist_reflection_eq_of_mem _ hA's, dist_comm]
  have hd2 : dist (EuclideanGeometry.reflection (affineSpan ℝ {A', W}) E) W = dist E W := by
    rw [dist_comm, EuclideanGeometry.dist_reflection_eq_of_mem _ hWs, dist_comm]
  have hne : E ≠ EuclideanGeometry.reflection (affineSpan ℝ {A', W}) E := by
    intro h
    exact hEs ((EuclideanGeometry.reflection_eq_self_iff E).mp h.symm)
  rcases EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two hfin hAW hne rfl hd1 hRA rfl hd2 hRW
    with h | h
  · exact absurd h hRE
  · exact h

end Erdos634.Draft.SideRunGA

#print axioms Erdos634.Draft.SideRunGA.not_collinear_dist
#print axioms Erdos634.Draft.SideRunGA.mirrorBeside_of_dist
