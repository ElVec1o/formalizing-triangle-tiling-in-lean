import Erdos634.Draft.LaczFormalL22Par

/-!
# Laczkovich Sect. 2: chart-level toolkit for the trapezoid lemmas

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94), Beeson, Beeson-Zhang, Zhang.

* relabelling of `Δ` (`RTri.rot`, `RatSimDiss.relabel`): the lemmas are proved with the angle at vertex `0`; the
  angle at another vertex is obtained by rotating the labels;
* `ChartRSD`: a chart-plane set whose chart image is a `RatSimDiss`; `chart_union`, `chart_single`;
* `chart_tile`: a chart triangle is a rational similar tile if its Gram squared sides are `k²` times the sides
  of `Δ` (rational arithmetic only).
-/

namespace Erdos634.LaczL22

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL21 Erdos634.Realizable

/-! ## Relabelling -/

theorem congr_scale_relabel (Δ : Tri) (τ : Equiv.Perm (Fin 3)) (ρ : ℝ) (hρ : ρ ≠ 0) :
    (scaleTri ρ hρ (Δ.relabel τ)).Congruent (scaleTri ρ hρ Δ) := by
  set S2 := scaleTri ρ hρ Δ with hS2
  have : (scaleTri ρ hρ (Δ.relabel τ)).Congruent (S2.relabel τ) := by
    refine Erdos634.SssCongruent.congruent_of_dist ?_
    intro i j
    simp only [Tri.relabel_pts, hS2, scaleTri_pts, Erdos634.Realizable.dist_homothety]
  exact this.trans (S2.congruent_relabel τ).symm

theorem RatSimTile.relabel {Δ T : Tri} (τ : Equiv.Perm (Fin 3)) (h : RatSimTile (Δ.relabel τ) T) :
    RatSimTile Δ T := by
  obtain ⟨hr, ρ, hρ, hc⟩ := h
  exact ⟨hr, ρ, hρ, hc.trans (congr_scale_relabel Δ τ ρ hρ.ne')⟩

theorem RatSimDiss.relabel {Δ : Tri} {S : Set Plane} (τ : Equiv.Perm (Fin 3))
    (h : RatSimDiss (Δ.relabel τ) S) : RatSimDiss Δ S := by
  obtain ⟨ι, f, t, hc, hd, hr⟩ := h
  exact ⟨ι, f, t, hc, hd, fun i => (hr i).relabel τ⟩

/-- Rotate the labels of `Δ`: vertex `1` becomes vertex `0`. -/
noncomputable def RTri.rot (R : RTri) : RTri where
  Δ := R.Δ.relabel (finRotate 3)
  a := R.b
  b := R.c
  c := R.a
  ha := by show dist (R.Δ.pts 2) (R.Δ.pts 0) = _; exact R.hb
  hb := by show dist (R.Δ.pts 0) (R.Δ.pts 1) = _; exact R.hc
  hc := by show dist (R.Δ.pts 1) (R.Δ.pts 2) = _; exact R.ha
  pa := R.pb
  pb := R.pc
  pc := R.pa

/-! ## Chart sets -/

/-- A chart-plane set whose image under the chart is a rational similar dissection. -/
def ChartRSD (R : RTri) (A w d : Plane) (h : w 0 * d 1 - w 1 * d 0 ≠ 0) (S : Set Plane) : Prop :=
  RatSimDiss R.Δ (chartEquiv A w d h '' S)

theorem disjoint_interior_image (e : Plane ≃ᵃ[ℝ] Plane) {S U : Set Plane}
    (h : Disjoint (interior S) (interior U)) :
    Disjoint (interior (e '' S)) (interior (e '' U)) := by
  have hcont : Continuous e := AffineEquiv.continuous_of_finiteDimensional e
  have hcont' : Continuous e.symm := AffineEquiv.continuous_of_finiteDimensional e.symm
  let eh : Plane ≃ₜ Plane := ⟨e.toEquiv, hcont, hcont'⟩
  have himg : ∀ S : Set Plane, interior (e '' S) = e '' interior S := fun S => (eh.image_interior S).symm
  rw [himg, himg]
  exact (Set.disjoint_image_iff e.injective).mpr h

theorem chart_union {R : RTri} {A w d : Plane} {h : w 0 * d 1 - w 1 * d 0 ≠ 0} {S U : Set Plane}
    (hS : ChartRSD R A w d h S) (hU : ChartRSD R A w d h U)
    (hd : Disjoint (interior S) (interior U)) : ChartRSD R A w d h (S ∪ U) := by
  unfold ChartRSD at *
  rw [Set.image_union]
  exact hS.union hU (disjoint_interior_image _ hd)

theorem chart_mono_eq {R : RTri} {A w d : Plane} {h : w 0 * d 1 - w 1 * d 0 ≠ 0} {S U : Set Plane}
    (hS : ChartRSD R A w d h S) (e : S = U) : ChartRSD R A w d h U := e ▸ hS

theorem chart_single {R : RTri} {A w d : Plane} {h : w 0 * d 1 - w 1 * d 0 ≠ 0} (t : Tri)
    (ht : RatSimTile R.Δ (Erdos634.DissectionMap.mapTri (chartEquiv A w d h) t)) :
    ChartRSD R A w d h t.carrier := by
  unfold ChartRSD
  refine ⟨Unit, inferInstance, fun _ => Erdos634.DissectionMap.mapTri (chartEquiv A w d h) t,
    ?_, ?_, fun _ => ht⟩
  · simp only [Set.iUnion_const]; exact Erdos634.DissectionMap.mapTri_carrier _ _
  · intro i j hij; exact absurd (Subsingleton.elim i j) hij

theorem chart_rect {R : RTri} (A w d : Plane) (h : w 0 * d 1 - w 1 * d 0 ≠ 0) (W Dd : ℚ)
    (hW : 0 < W) (hD : 0 < Dd) (hw : inner ℝ w w = (W : ℝ) ^ 2) (hd : inner ℝ d d = (Dd : ℝ) ^ 2)
    (hwd : inner ℝ w d = (W : ℝ) * Dd * (R.cos0 : ℝ)) (s0 t0 p q : ℚ) (hp : 0 < p) (hq : 0 < q) :
    ChartRSD R A w d h (rectSet (s0 : ℝ) ((s0 : ℝ) + p) (t0 : ℝ) ((t0 : ℝ) + q)) :=
  rect_ratSim R A w d h W Dd hW hD hw hd hwd s0 t0 p q hp hq

/-- A chart triangle with prescribed Gram squared sides is a rational similar tile. -/
theorem chart_tile (R : RTri) (A w d : Plane) (h : w 0 * d 1 - w 1 * d 0 ≠ 0) (W Dd : ℚ)
    (hw : inner ℝ w w = (W : ℝ) ^ 2) (hd : inner ℝ d d = (Dd : ℝ) ^ 2) (g : ℝ)
    (hwd : inner ℝ w d = g) (x0 y0 x1 y1 x2 y2 : ℝ) (hdet : det3 x0 y0 x1 y1 x2 y2 ≠ 0)
    (σ : Equiv.Perm (Fin 3)) (k : ℚ) (hk : 0 < k)
    (h01 : (x0 - x1) ^ 2 * (W : ℝ) ^ 2 + 2 * ((x0 - x1) * (y0 - y1)) * g + (y0 - y1) ^ 2 * (Dd : ℝ) ^ 2
      = (k : ℝ) ^ 2 * dist (R.Δ.pts (σ 0)) (R.Δ.pts (σ 1)) ^ 2)
    (h12 : (x1 - x2) ^ 2 * (W : ℝ) ^ 2 + 2 * ((x1 - x2) * (y1 - y2)) * g + (y1 - y2) ^ 2 * (Dd : ℝ) ^ 2
      = (k : ℝ) ^ 2 * dist (R.Δ.pts (σ 1)) (R.Δ.pts (σ 2)) ^ 2)
    (h20 : (x2 - x0) ^ 2 * (W : ℝ) ^ 2 + 2 * ((x2 - x0) * (y2 - y0)) * g + (y2 - y0) ^ 2 * (Dd : ℝ) ^ 2
      = (k : ℝ) ^ 2 * dist (R.Δ.pts (σ 2)) (R.Δ.pts (σ 0)) ^ 2) :
    RatSimTile R.Δ (Erdos634.DissectionMap.mapTri (chartEquiv A w d h) (mkTri x0 y0 x1 y1 x2 y2 hdet)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hsq : ∀ (p q : Plane), dist (chartEquiv A w d h p) (chartEquiv A w d h q) ^ 2
      = (p 0 - q 0) ^ 2 * (W : ℝ) ^ 2 + 2 * ((p 0 - q 0) * (p 1 - q 1)) * g
        + (p 1 - q 1) ^ 2 * (Dd : ℝ) ^ 2 := by
    intro p q
    rw [dist_chart_sq, hw, hd, hwd]
  refine ratSimTile_of_cong R.rational k hk ?_
  refine congr_of_sq3 _ R.Δ σ k hk' ?_ ?_ ?_
  · show dist (chartEquiv A w d h (mkPt x0 y0)) (chartEquiv A w d h (mkPt x1 y1)) ^ 2 = _
    rw [hsq]; simpa only [mkPt_zero, mkPt_one] using h01
  · show dist (chartEquiv A w d h (mkPt x1 y1)) (chartEquiv A w d h (mkPt x2 y2)) ^ 2 = _
    rw [hsq]; simpa only [mkPt_zero, mkPt_one] using h12
  · show dist (chartEquiv A w d h (mkPt x2 y2)) (chartEquiv A w d h (mkPt x0 y0)) ^ 2 = _
    rw [hsq]; simpa only [mkPt_zero, mkPt_one] using h20

end Erdos634.LaczL22
