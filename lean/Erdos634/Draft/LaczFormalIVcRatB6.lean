-- Draft/LaczFormalIVcRatB6.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch), BLUEPRINT Part B, item B6: `corner_piece`.
--   T a VWTiling of a convex A (hb : 0 < b), X a point at which A has interior angle pi/3 in the sense of area
--   (hX : for all small r, area (A ∩ B(X,r)) = (pi/3)/2 * r^2).  Then there is a rhombus rho such that
--     * X is one of the two pi/3 corners of rhombus rho (X = x or X = x+s+w),
--     * rhombus rho is the ONLY rhombus whose set contains X, and NO kite set contains X
--   i.e. X is a corner of exactly one piece, with angle pi/3 there, and that piece is a rhombus.
--   Proof: area count gives exactly one equilateral cell through X, with X a vertex (`corner_cell`); kite cells are excluded: apex V k by V k = W k' (three more cells),
--   every other kite vertex lies in a second cell of the same kite except the two base ends, which are excluded by `tri_edge_frontier` (the W of the kite would lie on bd A)
--   and B5 (`vw_not_boundary`); rhombus vertices x+s, x+w lie in both cells.
--   Blueprint deviation: "angle pi/3" is the area statement (the local angle of A at X as defined in AngleSumDissection), not a ConvPoly vertex angle; the ConvPoly bridge is NOT done here.
--   Hypotheses: A convex; VWTiling data; hX (witnessed by any rhombus corner, see `witRhomb_corner_vol` NOT proved: no area witness here).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatB6a

open scoped Classical Fin.NatCast
open MeasureTheory
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace Erdos634.Draft.LaczFormal.RG

theorem plane_ext' {p q : Plane} (h0 : p 0 = q 0) (h1 : p 1 = q 1) : p = q := by
  ext i; fin_cases i
  · exact h0
  · exact h1

theorem pts_mem (T : Tri) (n : Fin 3) : T.pts n ∈ T.carrier := subset_convexHull ℝ _ ⟨n, rfl⟩

/-- Vertex incidences of the four kite cells: every vertex is the apex, a base end, or lies in a second cell. -/
theorem kite_vertex_cases {b : ℝ} (K : KiteData b) (i : Fin 4) (j : Fin 3) :
    (i = 0 ∧ j = 2) ∨ (∃ i', i' ≠ i ∧ (K.cell i).pts j ∈ (K.cell i').carrier) ∨ (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 1) := by
  have eq : ∀ (i i' : Fin 4) (j j' : Fin 3), (K.cell i).pts j = (K.cell i').pts j' → i' ≠ i →
      ∃ i', i' ≠ i ∧ (K.cell i).pts j ∈ (K.cell i').carrier := fun i i' j j' h hne => ⟨i', hne, by rw [h]; exact pts_mem _ _⟩
  fin_cases i <;> fin_cases j
  · right; left; exact eq _ 1 _ 2 (plane_ext' (by simp [KiteData.cell, kiteCell, ct, mkTri_pts] <;> ring) (by simp [KiteData.cell, kiteCell, ct, mkTri_pts] <;> ring)) (by decide)
  · right; left; exact eq _ 2 _ 2 (plane_ext' (by simp [KiteData.cell, kiteCell, ct, mkTri_pts] <;> ring) (by simp [KiteData.cell, kiteCell, ct, mkTri_pts] <;> ring)) (by decide)
  · left; exact ⟨rfl, rfl⟩
  · right; right; left; exact ⟨rfl, rfl⟩
  · right; left; exact eq _ 2 _ 0 (plane_ext' (by simp [KiteData.cell, kiteCell, ct, mkTri_pts] <;> ring) (by simp [KiteData.cell, kiteCell, ct, mkTri_pts] <;> ring)) (by decide)
  · right; left; exact eq _ 0 _ 0 (plane_ext' (by simp [KiteData.cell, kiteCell, ct, mkTri_pts] <;> ring) (by simp [KiteData.cell, kiteCell, ct, mkTri_pts] <;> ring)) (by decide)
  · right; left; exact eq _ 1 _ 1 (plane_ext' (by simp [KiteData.cell, kiteCell, ct, mkTri_pts] <;> ring) (by simp [KiteData.cell, kiteCell, ct, mkTri_pts] <;> ring)) (by decide)
  · right; right; right; exact ⟨rfl, rfl⟩
  · right; left; exact eq _ 0 _ 1 (plane_ext' (by simp [KiteData.cell, kiteCell, ct, mkTri_pts] <;> ring) (by simp [KiteData.cell, kiteCell, ct, mkTri_pts] <;> ring)) (by decide)
  · right; left; exact eq _ 0 _ 1 (plane_ext' (by simp [KiteData.cell, kiteCell, ct, mkTri_pts] <;> ring) (by simp [KiteData.cell, kiteCell, ct, mkTri_pts] <;> ring)) (by decide)
  · right; left; exact eq _ 0 _ 0 (plane_ext' (by simp [KiteData.cell, kiteCell, ct, mkTri_pts] <;> ring) (by simp [KiteData.cell, kiteCell, ct, mkTri_pts] <;> ring)) (by decide)
  · right; left; exact eq _ 1 _ 1 (plane_ext' (by simp [KiteData.cell, kiteCell, ct, mkTri_pts] <;> ring) (by simp [KiteData.cell, kiteCell, ct, mkTri_pts] <;> ring)) (by decide)

/-- Vertex incidences of the two rhombus cells: the pi/3 corners `x`, `x+s+w`, or a vertex shared by both cells. -/
theorem rhomb_vertex_cases {b : ℝ} (R : RhombData b) (i : Fin 2) (j : Fin 3) :
    (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) ∨ (∃ i', i' ≠ i ∧ (R.cell i).pts j ∈ (R.cell i').carrier) := by
  have eq : ∀ (i i' : Fin 2) (j j' : Fin 3), (R.cell i).pts j = (R.cell i').pts j' → i' ≠ i →
      ∃ i', i' ≠ i ∧ (R.cell i).pts j ∈ (R.cell i').carrier := fun i i' j j' h hne => ⟨i', hne, by rw [h]; exact pts_mem _ _⟩
  fin_cases i <;> fin_cases j
  · right; right; exact eq _ 1 _ 1 (plane_ext' (by simp [RhombData.cell, rhombCell, ct, mkTri_pts] <;> ring) (by simp [RhombData.cell, rhombCell, ct, mkTri_pts] <;> ring)) (by decide)
  · right; right; exact eq _ 1 _ 0 (plane_ext' (by simp [RhombData.cell, rhombCell, ct, mkTri_pts] <;> ring) (by simp [RhombData.cell, rhombCell, ct, mkTri_pts] <;> ring)) (by decide)
  · left; exact ⟨rfl, rfl⟩
  · right; right; exact eq _ 0 _ 1 (plane_ext' (by simp [RhombData.cell, rhombCell, ct, mkTri_pts] <;> ring) (by simp [RhombData.cell, rhombCell, ct, mkTri_pts] <;> ring)) (by decide)
  · right; right; exact eq _ 0 _ 0 (plane_ext' (by simp [RhombData.cell, rhombCell, ct, mkTri_pts] <;> ring) (by simp [RhombData.cell, rhombCell, ct, mkTri_pts] <;> ring)) (by decide)
  · right; left; exact ⟨rfl, rfl⟩

/-- Near a vertex of an equilateral tile whose corner the set `A` fills in area, `A` is no larger than the tile. -/
theorem corner_vol_le {A : Set Plane} {T : Tri} {b : ℝ} (hb : 0 < b) (hT : T.Congruent (eqT b hb)) (j : Fin 3) {ρ : ℝ} (hρ : 0 < ρ)
    (hX : ∀ r, 0 < r → r ≤ ρ → volume (A ∩ Metric.ball (T.pts j) r) = ENNReal.ofReal (Real.pi / 3 / 2 * r ^ 2)) :
    ∃ r0 > 0, ∀ r, 0 < r → r ≤ r0 → volume (A ∩ Metric.ball (T.pts j) r) ≤ volume (T.carrier ∩ Metric.ball (T.pts j) r) := by
  obtain ⟨rT, hrT, hv⟩ := T.volume_inter_ball_localAngle (T.pts j)
  refine ⟨min ρ rT, lt_min hρ hrT, fun r hr hle => ?_⟩
  rw [hX r hr (hle.trans (min_le_left _ _)), hv r hr (hle.trans (min_le_right _ _)), localAngle_vertex_equi hb hT j]

namespace VWTiling
variable {b : ℝ} {A : Set Plane} {ιK ιR : Type} [Fintype ιK] [Fintype ιR] (T : VWTiling b A ιK ιR)

/-- **The area count at a pi/3 corner**: exactly one cell contains `X`, and `X` is a vertex of it. -/
theorem corner_cell (hb : 0 < b) {X : Plane} {ρ : ℝ} (hρ : 0 < ρ)
    (hX : ∀ r, 0 < r → r ≤ ρ → volume (A ∩ Metric.ball X r) = ENNReal.ofReal (Real.pi / 3 / 2 * r ^ 2)) :
    ∃ c0 : CellIdx ιK ιR, (∃ j, X = (T.cellT c0).pts j) ∧ ∀ c, X ∈ (T.cellT c).carrier → c = c0 := by
  have hpi := Real.pi_pos
  have hN : 0 < Fintype.card (CellIdx ιK ιR) := by
    rcases isEmpty_or_nonempty (CellIdx ιK ιR) with he | hne
    · exfalso
      have hA : A = ∅ := by rw [← T.cells_cover]; exact Set.iUnion_of_empty _
      have h1 := hX ρ hρ le_rfl
      rw [hA, Set.empty_inter, measure_empty] at h1
      have h2 : 0 < Real.pi / 3 / 2 * ρ ^ 2 := by positivity
      exact absurd h1 (ENNReal.ofReal_pos.mpr h2).ne
    · exact Fintype.card_pos
  have hsum := sum_localAngle_of_vol (T.cellDiss hb).toRegionDissection hN X (Real.pi / 3) (by positivity) ρ hρ hX
  have hsum' : ∑ c : CellIdx ιK ιR, (T.cellT c).localAngle X = Real.pi / 3 := by
    rw [← T.sum_cellDiss hb X]; exact hsum
  have hc := T.cell_congruent hb
  have hnn : ∀ c, 0 ≤ (T.cellT c).localAngle X := fun c => (T.cellT c).localAngle_nonneg X
  obtain ⟨c0, hc0⟩ : ∃ c0, X ∈ (T.cellT c0).carrier := by
    by_contra hall
    push Not at hall
    have : ∑ c : CellIdx ιK ιR, (T.cellT c).localAngle X = 0 :=
      Finset.sum_eq_zero fun c _ => Tri.localAngle_eq_zero_of_not_mem _ (hall c)
    linarith
  have huniq : ∀ c, X ∈ (T.cellT c).carrier → c = c0 := by
    intro c hmem
    by_contra hne
    have h1 := (localAngle_mem_equi hb (hc c) hmem).1
    have h0 := (localAngle_mem_equi hb (hc c0) hc0).1
    have h2 : (T.cellT c).localAngle X + (T.cellT c0).localAngle X ≤ ∑ c : CellIdx ιK ιR, (T.cellT c).localAngle X := by
      have hp := Finset.sum_pair (f := fun c => (T.cellT c).localAngle X) hne
      rw [← hp]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun c _ _ => hnn c)
    linarith
  refine ⟨c0, ?_, huniq⟩
  have h3 : (T.cellT c0).localAngle X ≤ ∑ c : CellIdx ιK ιR, (T.cellT c).localAngle X :=
    Finset.single_le_sum (fun c _ => hnn c) (Finset.mem_univ c0)
  have h4 := (localAngle_mem_equi hb (hc c0) hc0).1
  exact (localAngle_mem_equi hb (hc c0) hc0).2 (by linarith)

/-- **B6.** A corner `X` of `A` with area angle pi/3 is a pi/3 corner of exactly one piece, a rhombus. -/
theorem corner_piece (hb : 0 < b) (hconv : Convex ℝ A) {X : Plane} {ρ : ℝ} (hρ : 0 < ρ)
    (hX : ∀ r, 0 < r → r ≤ ρ → volume (A ∩ Metric.ball X r) = ENNReal.ofReal (Real.pi / 3 / 2 * r ^ 2)) :
    ∃ r : ιR, (X = mkPt (T.R r).x0 (T.R r).x1 ∨
        X = mkPt ((T.R r).x0 + (T.R r).s0 + (T.R r).w0) ((T.R r).x1 + (T.R r).s1 + (T.R r).w1)) ∧
      (∀ r', X ∈ (T.R r').set → r' = r) ∧ (∀ k, X ∉ (T.K k).set) := by
  obtain ⟨c0, ⟨j, hXj⟩, U⟩ := T.corner_cell hb hρ hX
  have hnb := T.vw_not_boundary hb hconv
  have hc := T.cell_congruent hb
  have hsubA : ∀ c, (T.cellT c).carrier ⊆ A := fun c =>
    (Set.subset_iUnion (fun c => (T.cellT c).carrier) c).trans T.cells_cover.subset
  rcases c0 with ⟨k, i⟩ | ⟨r, i⟩
  · -- a kite cell: impossible
    exfalso
    rcases kite_vertex_cases (T.K k) i j with ⟨rfl, rfl⟩ | ⟨i', hne, hmem⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- apex
      obtain ⟨k', hk'⟩ := T.vwV k
      obtain ⟨hW1, _, _⟩ := kite_W_vertices (v0 := (T.K k').v0) (v1 := (T.K k').v1) (T.K k').hD
      have hX0 : X = (T.K k).V := hXj
      have hmem : X ∈ (T.cellT (Sum.inl (k', 1))).carrier := by
        have e : X = ((T.K k').cell 1).pts 1 := by rw [hX0, hk']; exact hW1.symm
        rw [e]; exact pts_mem _ _
      have := U _ hmem
      simp at this
    · have := U (Sum.inl (k, i')) (by rw [hXj]; exact hmem)
      simp at this
      exact hne this
    · -- base end of cell 1
      obtain ⟨hW1, _, _⟩ := kite_W_vertices (v0 := (T.K k).v0) (v1 := (T.K k).v1) (T.K k).hD
      obtain ⟨r0, hr0, hv⟩ := corner_vol_le hb (hc (Sum.inl (k, 1))) 0 hρ (by rw [← hXj]; exact hX)
      have hf := tri_edge_frontier hconv ((T.K k).cell 1) (hsubA (Sum.inl (k, 1))) (j := 0) (m := 2) (n := 1) (by decide) (by decide) hr0 hv
      have e : (T.K k).W = ((T.K k).cell 1).pts 1 := hW1.symm
      have : (T.K k).W ∈ frontier A := by rw [e]; exact hf
      exact hnb.2 k this
    · -- base end of cell 2
      obtain ⟨_, hW2, _⟩ := kite_W_vertices (v0 := (T.K k).v0) (v1 := (T.K k).v1) (T.K k).hD
      obtain ⟨r0, hr0, hv⟩ := corner_vol_le hb (hc (Sum.inl (k, 2))) 1 hρ (by rw [← hXj]; exact hX)
      have hf := tri_edge_frontier hconv ((T.K k).cell 2) (hsubA (Sum.inl (k, 2))) (j := 1) (m := 2) (n := 0) (by decide) (by decide) hr0 hv
      have e : (T.K k).W = ((T.K k).cell 2).pts 0 := hW2.symm
      have : (T.K k).W ∈ frontier A := by rw [e]; exact hf
      exact hnb.2 k this
  · rcases rhomb_vertex_cases (T.R r) i j with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨i', hne, hmem⟩
    · refine ⟨r, Or.inl hXj, ?_, ?_⟩
      · intro r' hr'
        rw [← (T.R r').set_eq_iUnion] at hr'
        obtain ⟨i2, hi2⟩ := Set.mem_iUnion.mp hr'
        have := U (Sum.inr (r', i2)) hi2
        simp at this; exact this.1
      · intro k' hk'
        rw [← (T.K k').set_eq_iUnion] at hk'
        obtain ⟨i2, hi2⟩ := Set.mem_iUnion.mp hk'
        have := U (Sum.inl (k', i2)) hi2
        simp at this
    · refine ⟨r, Or.inr ?_, ?_, ?_⟩
      · rw [hXj]; exact plane_ext' (by simp [VWTiling.cellT, RhombData.cell, rhombCell, ct, mkTri_pts] <;> ring) (by simp [VWTiling.cellT, RhombData.cell, rhombCell, ct, mkTri_pts] <;> ring)
      · intro r' hr'
        rw [← (T.R r').set_eq_iUnion] at hr'
        obtain ⟨i2, hi2⟩ := Set.mem_iUnion.mp hr'
        have := U (Sum.inr (r', i2)) hi2
        simp at this; exact this.1
      · intro k' hk'
        rw [← (T.K k').set_eq_iUnion] at hk'
        obtain ⟨i2, hi2⟩ := Set.mem_iUnion.mp hk'
        have := U (Sum.inl (k', i2)) hi2
        simp at this
    · exfalso
      have := U (Sum.inr (r, i')) (by rw [hXj]; exact hmem)
      simp at this
      exact hne this

end VWTiling

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.VWTiling.corner_piece
#print axioms Erdos634.Draft.LaczFormal.RG.VWTiling.corner_cell
#print axioms Erdos634.Draft.LaczFormal.RG.kite_vertex_cases
#print axioms Erdos634.Draft.LaczFormal.RG.rhomb_vertex_cases
