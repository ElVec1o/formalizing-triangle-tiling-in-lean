-- Draft/LaczFormalIVcRatB7g.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch), BLUEPRINT Part B, item B7, stage g: A CELL THROUGH U AND ITS VERTEX.
--   `exists_cell_at`: if U = F.pt 0 0 and a point y with fa y > 0 lie in a convex A tiled by (finitely many) cells, some cell contains U and a point with fa > 0 (the cell through the points U + eps (y - U), eps -> 0).
--   `vertex_of_corner`: a triangle in the closed quadrant {fa >= 0, fb >= 0} of the frame containing U has U as a vertex (barycentric: U is an extreme point of the quadrant).
--   `vertex_of_second_cell`: if two different cells of a VWTiling of a convex A contain a frontier point U, U is a vertex of each (the local angles are >= pi/3 each and add to at most pi).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatB7f

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

theorem Frame.fa_eq {b : ℝ} (F : Frame b) (y : Plane) :
    F.fa y = (F.q1 / F.D) * y 0 - (F.q0 / F.D) * y 1 + (F.q0 * F.U1 - F.q1 * F.U0) / F.D := by
  unfold Frame.fa; ring

theorem Frame.fb_eq {b : ℝ} (F : Frame b) (y : Plane) :
    F.fb y = (-F.p1 / F.D) * y 0 + (F.p0 / F.D) * y 1 + (F.p1 * F.U0 - F.p0 * F.U1) / F.D := by
  unfold Frame.fb; ring

/-- **B7g (corner).** -/
theorem vertex_of_corner {b : ℝ} (F : Frame b) (hb : 0 < b) (c : Tri) (hq : ∀ y ∈ c.carrier, 0 ≤ F.fa y ∧ 0 ≤ F.fb y)
    (hU : F.pt 0 0 ∈ c.carrier) : ∃ j, c.pts j = F.pt 0 0 := by
  set U := F.pt 0 0 with hUdef
  have hnn : ∀ k, 0 ≤ c.basis.coord k U := by
    have := hU; rw [c.carrier_eq_nonneg_coord] at this; exact this
  have hsum : c.basis.coord 0 U + c.basis.coord 1 U + c.basis.coord 2 U = 1 := by
    have := c.basis.sum_coord_apply_eq_one (k := ℝ) U
    rwa [Fin.sum_univ_three] at this
  have hb' := Erdos634.Subdivision.bary_expand c U
  have e0 : U 0 = c.basis.coord 0 U * (c.pts 0) 0 + c.basis.coord 1 U * (c.pts 1) 0 + c.basis.coord 2 U * (c.pts 2) 0 := by
    have := congrArg (fun y : Plane => y 0) hb'
    simpa using this
  have e1 : U 1 = c.basis.coord 0 U * (c.pts 0) 1 + c.basis.coord 1 U * (c.pts 1) 1 + c.basis.coord 2 U * (c.pts 2) 1 := by
    have := congrArg (fun y : Plane => y 1) hb'
    simpa using this
  have hfa : F.fa U = c.basis.coord 0 U * F.fa (c.pts 0) + c.basis.coord 1 U * F.fa (c.pts 1) + c.basis.coord 2 U * F.fa (c.pts 2) := by
    rw [F.fa_eq U, F.fa_eq (c.pts 0), F.fa_eq (c.pts 1), F.fa_eq (c.pts 2)]
    linear_combination (F.q1 / F.D) * e0 - (F.q0 / F.D) * e1 - ((F.q0 * F.U1 - F.q1 * F.U0) / F.D) * hsum
  have hfb : F.fb U = c.basis.coord 0 U * F.fb (c.pts 0) + c.basis.coord 1 U * F.fb (c.pts 1) + c.basis.coord 2 U * F.fb (c.pts 2) := by
    rw [F.fb_eq U, F.fb_eq (c.pts 0), F.fb_eq (c.pts 1), F.fb_eq (c.pts 2)]
    linear_combination (-F.p1 / F.D) * e0 + (F.p0 / F.D) * e1 - ((F.p1 * F.U0 - F.p0 * F.U1) / F.D) * hsum
  have hfaU : F.fa U = 0 := F.fa_pt hb 0 0
  have hfbU : F.fb U = 0 := F.fb_pt hb 0 0
  have hv : ∀ k, 0 ≤ F.fa (c.pts k) ∧ 0 ≤ F.fb (c.pts k) := fun k => hq _ (pts_mem c k)
  have hex : ∃ k, 0 < c.basis.coord k U := by
    by_contra h
    push Not at h
    have := h 0; have := h 1; have := h 2; linarith [hnn 0, hnn 1, hnn 2]
  obtain ⟨k, hk⟩ := hex
  refine ⟨k, ?_⟩
  have t0 : 0 ≤ c.basis.coord 0 U * F.fa (c.pts 0) := mul_nonneg (hnn 0) (hv 0).1
  have t1 : 0 ≤ c.basis.coord 1 U * F.fa (c.pts 1) := mul_nonneg (hnn 1) (hv 1).1
  have t2 : 0 ≤ c.basis.coord 2 U * F.fa (c.pts 2) := mul_nonneg (hnn 2) (hv 2).1
  have s0 : 0 ≤ c.basis.coord 0 U * F.fb (c.pts 0) := mul_nonneg (hnn 0) (hv 0).2
  have s1 : 0 ≤ c.basis.coord 1 U * F.fb (c.pts 1) := mul_nonneg (hnn 1) (hv 1).2
  have s2 : 0 ≤ c.basis.coord 2 U * F.fb (c.pts 2) := mul_nonneg (hnn 2) (hv 2).2
  have hA : c.basis.coord k U * F.fa (c.pts k) = 0 := by
    fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> linarith
  have hB : c.basis.coord k U * F.fb (c.pts k) = 0 := by
    fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> linarith
  have ha0 : F.fa (c.pts k) = 0 := by
    rcases mul_eq_zero.mp hA with h | h
    · exact absurd h hk.ne'
    · exact h
  have hb0 : F.fb (c.pts k) = 0 := by
    rcases mul_eq_zero.mp hB with h | h
    · exact absurd h hk.ne'
    · exact h
  have := F.recon hb (c.pts k)
  rw [ha0, hb0] at this
  exact this

namespace VWTiling
variable {b : ℝ} {A : Set Plane} {ιK ιR : Type} [Fintype ιK] [Fintype ιR] (T : VWTiling b A ιK ιR)

/-- **B7g (cell through U).** -/
theorem exists_cell_at (hb : 0 < b) (hconv : Convex ℝ A) (F : Frame b) (hUA : F.pt 0 0 ∈ A) {y : Plane} (hyA : y ∈ A)
    (hya : 0 < F.fa y) :
    ∃ c : CellIdx ιK ιR, F.pt 0 0 ∈ (T.cellT c).carrier ∧ ∃ z ∈ (T.cellT c).carrier, 0 < F.fa z := by
  by_contra hcon
  push Not at hcon
  set U := F.pt 0 0 with hUdef
  set S : Set (CellIdx ιK ιR) := {c | U ∉ (T.cellT c).carrier} with hS
  have hcl : IsClosed (⋃ c ∈ S, (T.cellT c).carrier) :=
    (Set.toFinite S).isClosed_biUnion (fun c _ => (T.cellT c).isCompact.isClosed)
  have hUn : U ∉ ⋃ c ∈ S, (T.cellT c).carrier := by
    simp only [Set.mem_iUnion, exists_prop, not_exists, not_and]
    intro c hc hmem
    exact hc hmem
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hcl.isOpen_compl U hUn
  set ε : ℝ := min 1 (δ / (2 * (dist U y + 1))) with hε
  have hεp : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  set z : Plane := AffineMap.lineMap U y ε with hz
  have hzA : z ∈ A := hconv.lineMap_mem hUA hyA ⟨hεp.le, hε1⟩
  obtain ⟨ya, yb, hy0, hy1⟩ := F.coords hb y
  have hya' : F.fa y = ya := (F.fa_fb_of hb hy0 hy1).1
  have hU0 : U 0 = F.U0 := by rw [hUdef, F.pt_zero]; ring
  have hU1 : U 1 = F.U1 := by rw [hUdef, F.pt_one]; ring
  have hfz : F.fa z = ε * ya := by
    have z0 : z 0 = F.U0 + (ε * ya) * F.p0 + (ε * yb) * F.q0 := by
      rw [hz, AffineMap.lineMap_apply]; simp only [vsub_eq_sub, vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      rw [hU0, hy0]; ring
    have z1 : z 1 = F.U1 + (ε * ya) * F.p1 + (ε * yb) * F.q1 := by
      rw [hz, AffineMap.lineMap_apply]; simp only [vsub_eq_sub, vadd_eq_add, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      rw [hU1, hy1]; ring
    exact (F.fa_fb_of hb z0 z1).1
  have hfzpos : 0 < F.fa z := by rw [hfz, ← hya']; exact mul_pos hεp hya
  have hdz : dist z U < δ := by
    rw [hz, dist_lineMap_left, Real.norm_eq_abs, abs_of_pos hεp]
    have h1 : ε * dist U y ≤ δ / (2 * (dist U y + 1)) * dist U y := by
      apply mul_le_mul_of_nonneg_right (min_le_right _ _) dist_nonneg
    have h2 : δ / (2 * (dist U y + 1)) * dist U y < δ := by
      have hd := dist_nonneg (x := U) (y := y)
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  rw [← T.cells_cover] at hzA
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hzA
  by_cases hUc : U ∈ (T.cellT c).carrier
  · exact absurd hfzpos (not_lt.mpr (hcon c hUc z hc))
  · have : z ∈ ⋃ c ∈ S, (T.cellT c).carrier := Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hUc, hc⟩⟩
    exact hball (Metric.mem_ball.mpr hdz) this

/-- **B7g (second cell).** -/
theorem vertex_of_second_cell (hb : 0 < b) (hconv : Convex ℝ A) {c c' : CellIdx ιK ιR} (hne : c ≠ c') {q : Plane}
    (hfr : q ∈ frontier A) (hq : q ∈ (T.cellT c).carrier) (hq' : q ∈ (T.cellT c').carrier) : ∃ j, (T.cellT c).pts j = q := by
  have hN : 0 < Fintype.card (CellIdx ιK ιR) := Fintype.card_pos_iff.mpr ⟨c⟩
  have hle := sum_localAngle_frontier_le (T.cellDiss hb).toRegionDissection hN hconv (T.interior_nonempty_of_cell c)
    T.region_closed (q := q) hfr
  rw [T.sum_cellDiss hb] at hle
  have hcg := T.cell_congruent hb
  have hnn : ∀ d, 0 ≤ (T.cellT d).localAngle q := fun d => (T.cellT d).localAngle_nonneg _
  have h2 : (T.cellT c).localAngle q + (T.cellT c').localAngle q ≤ ∑ d : CellIdx ιK ιR, (T.cellT d).localAngle q := by
    have hp := Finset.sum_pair (f := fun d => (T.cellT d).localAngle q) hne
    rw [← hp]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun d _ _ => hnn d)
  have h1 := (localAngle_mem_equi hb (hcg c) hq).1
  have h1' := (localAngle_mem_equi hb (hcg c') hq').1
  have hpi := Real.pi_pos
  rcases localAngle_cases' (T.cellT c) q with ⟨j, hj, _⟩ | h | h | h
  · exact ⟨j, hj.symm⟩
  · exfalso; linarith
  · exfalso; linarith
  · exfalso; linarith

end VWTiling

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.VWTiling.exists_cell_at
#print axioms Erdos634.Draft.LaczFormal.RG.VWTiling.vertex_of_second_cell
