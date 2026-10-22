import Erdos634.Draft.LaczFormalL26Trap

/-!
# Laczkovich Theorem 2.4, fourth triple: the five tiles and the trapezoid in the chart

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94), Beeson, Beeson-Zhang, Zhang.

Chart `(0; w₁, d₁)` with `|w₁| = |d₁| = u = R.c/(a₀ b₀)` (`b₀ = 1 - a₀²`) and `⟨w₁, d₁⟩ = u² (2 - a₀²)/2`.
`tile_ok`: a coordinate triangle whose three chart squared sides are `k²` times those of `Δ` is a rational similar tile.
`chart_iUnion`: finite unions of closed, interior-disjoint chart dissections.
-/

namespace Erdos634.LaczL26

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL21 Erdos634.LaczL24

theorem tile_ok (R : RTri) (a0 : ℚ) (ha0 : 0 < a0) (ha1 : a0 < 1)
    (hA : R.a = a0 * R.c) (hB : R.b = (1 - a0 ^ 2) * R.c) (w d : Plane)
    (hdet : w 0 * d 1 - w 1 * d 0 ≠ 0)
    (hw : inner ℝ w w = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2)
    (hd : inner ℝ d d = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2)
    (hwd : inner ℝ w d = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2 * (2 - (a0 : ℝ) ^ 2) / 2)
    (x0 y0 x1 y1 x2 y2 : ℝ) (hdet3 : det3 x0 y0 x1 y1 x2 y2 ≠ 0) (k : ℚ) (hk : 0 < k) (kr : ℝ)
    (hkr : (k : ℝ) = kr)
    (e01 : (x0 - x1) ^ 2 + (2 - (a0 : ℝ) ^ 2) * ((x0 - x1) * (y0 - y1)) + (y0 - y1) ^ 2
      = kr ^ 2 * (a0 : ℝ) ^ 2 * (1 - (a0 : ℝ) ^ 2) ^ 2)
    (e12 : (x1 - x2) ^ 2 + (2 - (a0 : ℝ) ^ 2) * ((x1 - x2) * (y1 - y2)) + (y1 - y2) ^ 2
      = kr ^ 2 * (a0 : ℝ) ^ 4 * (1 - (a0 : ℝ) ^ 2) ^ 2)
    (e20 : (x2 - x0) ^ 2 + (2 - (a0 : ℝ) ^ 2) * ((x2 - x0) * (y2 - y0)) + (y2 - y0) ^ 2
      = kr ^ 2 * (a0 : ℝ) ^ 2 * (1 - (a0 : ℝ) ^ 2) ^ 4) :
    RatSimTile R.Δ (Erdos634.DissectionMap.mapTri (chartEquiv 0 w d hdet) (mkTri x0 y0 x1 y1 x2 y2 hdet3)) := by
  have hc := R.pc
  have ha0r : (0 : ℝ) < a0 := by exact_mod_cast ha0
  have hb0q : 0 < 1 - a0 ^ 2 := by nlinarith
  have hb0r : (0 : ℝ) < 1 - (a0 : ℝ) ^ 2 := by exact_mod_cast hb0q
  have hcr : (0 : ℝ) < R.c := by exact_mod_cast hc
  have hU : (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) * ((a0 : ℝ) * (1 - (a0 : ℝ) ^ 2)) = R.c := by
    push_cast; field_simp
  set U : ℝ := (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) with hUdef
  have hAr : (R.a : ℝ) = a0 * R.c := by exact_mod_cast hA
  have hBr : (R.b : ℝ) = (1 - (a0 : ℝ) ^ 2) * R.c := by exact_mod_cast hB
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  refine chart_tile R 0 w d hdet (R.c / (a0 * (1 - a0 ^ 2))) (R.c / (a0 * (1 - a0 ^ 2))) hw hd
    (U ^ 2 * (2 - (a0 : ℝ) ^ 2) / 2) hwd x0 y0 x1 y1 x2 y2 hdet3 1 k hk ?_ ?_ ?_
  · have d01 : dist (R.Δ.pts ((1 : Equiv.Perm (Fin 3)) 0)) (R.Δ.pts ((1 : Equiv.Perm (Fin 3)) 1)) = R.c := R.hc
    rw [d01]
    have : (x0 - x1) ^ 2 * U ^ 2 + 2 * ((x0 - x1) * (y0 - y1)) * (U ^ 2 * (2 - (a0 : ℝ) ^ 2) / 2)
        + (y0 - y1) ^ 2 * U ^ 2 = U ^ 2 * ((x0 - x1) ^ 2 + (2 - (a0 : ℝ) ^ 2) * ((x0 - x1) * (y0 - y1))
        + (y0 - y1) ^ 2) := by ring
    rw [this, e01]
    calc U ^ 2 * (kr ^ 2 * (a0 : ℝ) ^ 2 * (1 - (a0 : ℝ) ^ 2) ^ 2)
        = kr ^ 2 * (U * ((a0 : ℝ) * (1 - (a0 : ℝ) ^ 2))) ^ 2 := by ring
      _ = _ := by rw [hU, ← hkr]; try ring
  · have d12 : dist (R.Δ.pts ((1 : Equiv.Perm (Fin 3)) 1)) (R.Δ.pts ((1 : Equiv.Perm (Fin 3)) 2)) = R.a := R.ha
    rw [d12]
    have : (x1 - x2) ^ 2 * U ^ 2 + 2 * ((x1 - x2) * (y1 - y2)) * (U ^ 2 * (2 - (a0 : ℝ) ^ 2) / 2)
        + (y1 - y2) ^ 2 * U ^ 2 = U ^ 2 * ((x1 - x2) ^ 2 + (2 - (a0 : ℝ) ^ 2) * ((x1 - x2) * (y1 - y2))
        + (y1 - y2) ^ 2) := by ring
    rw [this, e12, hAr]
    calc U ^ 2 * (kr ^ 2 * (a0 : ℝ) ^ 4 * (1 - (a0 : ℝ) ^ 2) ^ 2)
        = kr ^ 2 * (a0 : ℝ) ^ 2 * (U * ((a0 : ℝ) * (1 - (a0 : ℝ) ^ 2))) ^ 2 := by ring
      _ = _ := by rw [hU, ← hkr]; try ring
  · have d20 : dist (R.Δ.pts ((1 : Equiv.Perm (Fin 3)) 2)) (R.Δ.pts ((1 : Equiv.Perm (Fin 3)) 0)) = R.b := R.hb
    rw [d20]
    have : (x2 - x0) ^ 2 * U ^ 2 + 2 * ((x2 - x0) * (y2 - y0)) * (U ^ 2 * (2 - (a0 : ℝ) ^ 2) / 2)
        + (y2 - y0) ^ 2 * U ^ 2 = U ^ 2 * ((x2 - x0) ^ 2 + (2 - (a0 : ℝ) ^ 2) * ((x2 - x0) * (y2 - y0))
        + (y2 - y0) ^ 2) := by ring
    rw [this, e20, hBr]
    calc U ^ 2 * (kr ^ 2 * (a0 : ℝ) ^ 2 * (1 - (a0 : ℝ) ^ 2) ^ 4)
        = kr ^ 2 * (1 - (a0 : ℝ) ^ 2) ^ 2 * (U * ((a0 : ℝ) * (1 - (a0 : ℝ) ^ 2))) ^ 2 := by ring
      _ = _ := by rw [hU, ← hkr]; try ring

/-- Closed, interior-disjoint chart dissections have a chart dissection union. -/
theorem chart_iUnion {R : RTri} {A w d : Plane} {h : w 0 * d 1 - w 1 * d 0 ≠ 0} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (S : ι → Set Plane) (hr : ∀ i, ChartRSD R A w d h (S i)) (hcl : ∀ i, IsClosed (S i))
    (hd : Pairwise fun i j => Disjoint (interior (S i)) (interior (S j))) :
    ChartRSD R A w d h (⋃ i, S i) := by
  unfold ChartRSD at *
  have hcont : Continuous (chartEquiv A w d h) := AffineEquiv.continuous_of_finiteDimensional _
  have hcont' : Continuous (chartEquiv A w d h).symm := AffineEquiv.continuous_of_finiteDimensional _
  let eh : Plane ≃ₜ Plane := ⟨(chartEquiv A w d h).toEquiv, hcont, hcont'⟩
  have hcl' : ∀ i, IsClosed (chartEquiv A w d h '' S i) := fun i => eh.isClosedMap _ (hcl i)
  have := ratSimDiss_iUnion (Δ := R.Δ) (fun i => chartEquiv A w d h '' S i) hr hcl'
    (fun i j hij => disjoint_interior_image _ (hd hij))
  rwa [← Set.image_iUnion] at this

end Erdos634.LaczL26
