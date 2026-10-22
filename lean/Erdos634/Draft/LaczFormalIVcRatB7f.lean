-- Draft/LaczFormalIVcRatB7f.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch), BLUEPRINT Part B, item B7, stage f: NO KITE CELL ALONG THE SUPPORTING LINE.
--   `frontier_of_fb_zero`: a point of a closed set A lying in the half plane {fb >= 0} of a frame with fb = 0 is a frontier point.
--   `kite_cell_excluded`: in a VWTiling of a convex A inside {fb >= 0}, no cell of a kite contains both U = F.pt 0 0 and F.pt 1 0 (a kite cell with an edge on the line fb = 0).
--   Route (the printed step P3): the kite lies in A, so on one side of the line; two distinct points of the kite on the line force V or W onto the line (`kite_support`, B7b); V, W are not frontier points (`vw_not_boundary`, B5).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatB7e

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

theorem frontier_of_fb_zero {b : ℝ} (F : Frame b) (hb : 0 < b) {A : Set Plane} (hcl : IsClosed A) (hbel : ∀ y ∈ A, 0 ≤ F.fb y)
    {y : Plane} (hy : y ∈ A) (h0 : F.fb y = 0) : y ∈ frontier A := by
  refine ⟨subset_closure hy, fun hint => ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
  set δ : ℝ := ε / (2 * b) with hδ
  have hδp : 0 < δ := by positivity
  set z : Plane := F.pt (F.fa y) (-δ) with hz
  have hy' : y = F.pt (F.fa y) 0 := by
    have := F.recon hb y
    rwa [h0] at this
  have hdist : dist z y = δ * b := by
    have h2 : dist z y ^ 2 = (δ * b) ^ 2 := by
      rw [dist_sq7]
      have e0 : z 0 - y 0 = -δ * F.q0 := by rw [hz, hy', F.pt_zero, F.pt_zero]; ring_nf; rw [← hy']; ring
      have e1 : z 1 - y 1 = -δ * F.q1 := by rw [hz, hy', F.pt_one, F.pt_one]; ring_nf; rw [← hy']; ring
      rw [e0, e1]
      have := F.hq
      linear_combination δ ^ 2 * this
    have := dist_nonneg (x := z) (y := y)
    nlinarith [sq_nonneg (dist z y - δ * b), mul_pos hδp hb]
  have hδb : δ * b = ε / 2 := by rw [hδ]; field_simp
  have hzA : z ∈ A := hball (by rw [Metric.mem_ball, hdist, hδb]; linarith)
  have := hbel z hzA
  rw [hz, F.fb_pt hb] at this
  linarith

theorem KiteData.V_mem {b : ℝ} (K : KiteData b) : K.V ∈ K.set := by
  have hD := hD4 K.hD
  exact (ct_carrier hD K.V).mpr ⟨0, 0, le_rfl, le_rfl, by norm_num, by simp [KiteData.V, mkPt_zero], by simp [KiteData.V, mkPt_one]⟩

theorem KiteData.W_mem {b : ℝ} (K : KiteData b) : K.W ∈ K.set := by
  have hD := hD4 K.hD
  exact (ct_carrier hD K.W).mpr ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by simp [KiteData.W, mkPt_zero], by simp [KiteData.W, mkPt_one]⟩

/-- **B7f.** -/
theorem VWTiling.kite_cell_excluded {b : ℝ} {A : Set Plane} {ιK ιR : Type} [Fintype ιK] [Fintype ιR] (T : VWTiling b A ιK ιR)
    (hb : 0 < b) (hconv : Convex ℝ A) (F : Frame b) (hbel : ∀ y ∈ A, 0 ≤ F.fb y) (k : ιK) (i : Fin 4)
    (hx : F.pt 0 0 ∈ ((T.K k).cell i).carrier) (hy : F.pt 1 0 ∈ ((T.K k).cell i).carrier) : False := by
  have hKA : (T.K k).set ⊆ A := fun y hy => by rw [← T.cover]; exact Or.inl (Set.mem_iUnion.mpr ⟨k, hy⟩)
  have hD := F.D_ne hb
  have key : ∀ y : Plane, F.fb y = (-F.p1 / F.D) * y 0 + (F.p0 / F.D) * y 1 + (F.p1 * F.U0 - F.p0 * F.U1) / F.D := by
    intro y; unfold Frame.fb; ring
  have hK : ∀ y ∈ (T.K k).set, 0 ≤ (-F.p1 / F.D) * y 0 + (F.p0 / F.D) * y 1 + (F.p1 * F.U0 - F.p0 * F.U1) / F.D := by
    intro y hy; rw [← key]; exact hbel y (hKA hy)
  have hne : F.pt 0 0 ≠ F.pt 1 0 := by
    intro h
    have h0 := congrArg (fun y : Plane => y 0) h
    have h1 := congrArg (fun y : Plane => y 1) h
    simp only [F.pt_zero, F.pt_one] at h0 h1
    have e0 : F.p0 = 0 := by linarith
    have e1 : F.p1 = 0 := by linarith
    have := F.hp
    rw [e0, e1] at this
    nlinarith [mul_pos hb hb]
  have hx' : F.pt 0 0 ∈ (T.K k).set := (T.K k).cell_subset i hx
  have hy' : F.pt 1 0 ∈ (T.K k).set := (T.K k).cell_subset i hy
  have e1 : (-F.p1 / F.D) * (F.pt 0 0) 0 + (F.p0 / F.D) * (F.pt 0 0) 1 + (F.p1 * F.U0 - F.p0 * F.U1) / F.D = 0 := by
    rw [← key]; exact F.fb_pt hb 0 0
  have e2 : (-F.p1 / F.D) * (F.pt 1 0) 0 + (F.p0 / F.D) * (F.pt 1 0) 1 + (F.p1 * F.U0 - F.p0 * F.U1) / F.D = 0 := by
    rw [← key]; exact F.fb_pt hb 1 0
  have hcl := T.region_closed
  have hnb := T.vw_not_boundary hb hconv
  rcases kite_support (T.K k) _ _ _ hK hx' hy' hne e1 e2 with h | h
  · rw [← key] at h
    exact hnb.1 k (frontier_of_fb_zero F hb hcl hbel (hKA (T.K k).V_mem) h)
  · rw [← key] at h
    exact hnb.2 k (frontier_of_fb_zero F hb hcl hbel (hKA (T.K k).W_mem) h)

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.VWTiling.kite_cell_excluded
