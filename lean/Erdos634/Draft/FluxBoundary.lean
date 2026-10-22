-- Draft/FluxBoundary.lean — `lem:cancel`, layer 1, part 3: side edges carry the target's
-- direction and sum to its side lengths.  Imported into All.lean (All.lean:445).
-- Design: (private working notes, not included) §2.3 step 3, §3.3.
--
-- Formalization debt on the prime-case VERIFIED path; not progress on the three /goal outcomes.
--
-- Reuse (cited): `exists_supporting`, `target_contact_side`, `hasEdgeChains_edge`,
-- `Tri.edge_inward`, `proportional_of_disjoint_pos`, `crossL(_ne_zero)`,
-- `eq_zero_of_cross_eq_zero`, `Dissection.sameside_edges_subsingleton`,
-- `sum_hausdorff_of_partition`, `Tri.hausdorff_edge`.
-- `unit_smul_of_pos` is the positive mirror of `unit_smul_of_neg` (Dissection.lean), new.
import Erdos634.Draft.FluxCore

open scoped Classical

namespace Erdos634.Geometry

open MeasureTheory Set

variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **Normalisation keeps a direction under a positive scalar.** -/
theorem unit_smul_of_pos {u v : Plane} {c : ℝ} (hc : 0 < c) (hu : u ≠ 0) (hv : v = c • u) :
    ‖v‖⁻¹ • v = ‖u‖⁻¹ • u := by
  have hun : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu
  have hcne : c ≠ 0 := ne_of_gt hc
  have hune : ‖u‖ ≠ 0 := ne_of_gt hun
  subst hv
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, smul_smul]
  congr 1
  field_simp

/-- **A tile edge on a target side carries the target's own ccw direction.**  With `(g, c)` the
supporting functional of side `j`, `Tri.edge_inward` applied to the tile and to the target at the
common midpoint makes both cross-functionals negative multiples of `g`
(`proportional_of_disjoint_pos`), so the two left-directions are positive multiples. -/
theorem Dissection.eDir_of_side (D : Dissection N) {e : Fin N × Fin 3} {j : Fin 3}
    (h : D.eSet e ⊆ D.target.edge j) : D.eDir e = D.target.leftUnit j := by
  have hsucc : ∀ i : Fin 3, i ≠ i + 1 := by decide
  have hshift : ∀ i : Fin 3, i + 2 + 1 = i := by decide
  have hab : (D.tile e.1).pts e.2 ≠ (D.tile e.1).pts (e.2 + 1) := fun hh =>
    hsucc e.2 ((D.tile e.1).indep.injective hh)
  have ha : (D.tile e.1).pts e.2 ∈ (D.tile e.1).edge e.2 := left_mem_segment ℝ _ _
  have hb : (D.tile e.1).pts (e.2 + 1) ∈ (D.tile e.1).edge e.2 := right_mem_segment ℝ _ _
  obtain ⟨hxT, hxa, hxb⟩ := mem_ne_ends_of_avg hab ha hb
  obtain ⟨hzT, hpT⟩ := (D.tile e.1).onEdge_param (k := e.2) hxT hxa hxb
  have haS : (D.tile e.1).pts e.2 ∈ D.target.edge j := h ha
  have hbS : (D.tile e.1).pts (e.2 + 1) ∈ D.target.edge j := h hb
  obtain ⟨hxS, hxA, hxB⟩ := mem_ne_ends_of_avg hab haS hbS
  obtain ⟨hzS, hpS⟩ := D.target.onEdge_param (k := j) hxS hxA hxB
  obtain ⟨g, c, hg, hle, hj, hj1, hj2⟩ := exists_supporting D.target j
  have hgx : g (((1:ℝ)/2) • (D.tile e.1).pts e.2 + ((1:ℝ)/2) • (D.tile e.1).pts (e.2 + 1))
      = c := by
    have hS := target_contact_side D.target g c hle hj hj1 hj2
    have hmem : ((1:ℝ)/2) • (D.tile e.1).pts e.2 + ((1:ℝ)/2) • (D.tile e.1).pts (e.2 + 1)
        ∈ {y ∈ D.target.carrier | g y = c} := by
      rw [hS]; exact hxS
    exact hmem.2
  have hleT : ∀ y ∈ (D.tile e.1).carrier, g y ≤ c := fun y hy =>
    hle y (tile_subset_target D e.1 hy)
  have hinT : ∀ v, g v < 0 → 0 < cross ((D.tile e.1).leftDir e.2) v := by
    intro v hv
    have := (D.tile e.1).edge_inward g c hg hleT hzT hpT hgx hv
    rwa [hshift] at this
  have hinS : ∀ v, g v < 0 → 0 < cross (D.target.leftDir j) v := by
    intro v hv
    have := D.target.edge_inward g c hg hle hzS hpS hgx hv
    rwa [hshift] at this
  have hnegcross : ∀ w v : Plane, cross w (-v) = - cross w v := by
    intro w v; simp only [cross, PiLp.neg_apply]; ring
  have hdisjT : ∀ v, ¬ (0 < crossL ((D.tile e.1).leftDir e.2) v ∧ 0 < g v) := by
    rintro v ⟨h1, h2⟩
    have h3 := hinT (-v) (by rw [map_neg]; linarith)
    rw [crossL_apply] at h1
    rw [hnegcross] at h3
    linarith
  have hdisjS : ∀ v, ¬ (0 < crossL (D.target.leftDir j) v ∧ 0 < g v) := by
    rintro v ⟨h1, h2⟩
    have h3 := hinS (-v) (by rw [map_neg]; linarith)
    rw [crossL_apply] at h1
    rw [hnegcross] at h3
    linarith
  obtain ⟨c₁, hc₁, hgT⟩ := proportional_of_disjoint_pos (crossL ((D.tile e.1).leftDir e.2)) g
    (crossL_ne_zero ((D.tile e.1).leftDir_ne_zero e.2)) hg hdisjT
  obtain ⟨c₂, hc₂, hgS⟩ := proportional_of_disjoint_pos (crossL (D.target.leftDir j)) g
    (crossL_ne_zero (D.target.leftDir_ne_zero j)) hg hdisjS
  have hc₂ne : c₂ ≠ 0 := ne_of_lt hc₂
  have hprop : D.target.leftDir j = (c₁ / c₂) • (D.tile e.1).leftDir e.2 := by
    have hzero : ∀ v, cross (D.target.leftDir j - (c₁ / c₂) • (D.tile e.1).leftDir e.2) v = 0 := by
      intro v
      have e1 := hgT v
      have e2 := hgS v
      rw [crossL_apply] at e1 e2
      have hrel : cross (D.target.leftDir j) v = (c₁ / c₂) * cross ((D.tile e.1).leftDir e.2) v := by
        rw [div_mul_eq_mul_div, eq_div_iff hc₂ne]
        linear_combination e1 - e2
      simp only [cross, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hrel ⊢
      linear_combination hrel
    exact sub_eq_zero.mp (eq_zero_of_cross_eq_zero hzero)
  have hpos : 0 < c₁ / c₂ := div_pos_of_neg_of_neg hc₁ hc₂
  have hunit := unit_smul_of_pos hpos ((D.tile e.1).leftDir_ne_zero e.2) hprop
  apply Subtype.ext
  show ‖(D.tile e.1).leftDir e.2‖⁻¹ • (D.tile e.1).leftDir e.2
    = ‖D.target.leftDir j‖⁻¹ • D.target.leftDir j
  exact hunit.symm

/-- **Side edges sum to the side length.**  The explicit family `sideEdges j` covers side `j`
(`hasEdgeChains_edge`) and its members meet pairwise in at most a point
(`sameside_edges_subsingleton`). -/
theorem Dissection.side_len_sum (D : Dissection N) (j : Fin 3) :
    ∑ e ∈ D.sideEdges j, D.eLen e = dist (D.target.pts j) (D.target.pts (j + 1)) := by
  obtain ⟨g, c, hg, hle, hj, hj1, hj2⟩ := exists_supporting D.target j
  have hS : {x ∈ D.target.carrier | g x = c} = D.target.edge j :=
    target_contact_side D.target g c hle hj hj1 hj2
  have hmemS : ∀ e ∈ D.sideEdges j, D.eSet e ⊆ D.target.edge j := fun e he => by
    unfold Dissection.sideEdges at he
    exact (Finset.mem_filter.mp he).2
  have hon : ∀ e ∈ D.sideEdges j, ∀ y ∈ (D.tile e.1).edge e.2, g y = c := by
    intro e he y hy
    have hy' : y ∈ {x ∈ D.target.carrier | g x = c} := by rw [hS]; exact hmemS e he hy
    exact hy'.2
  have hleT : ∀ e : Fin N × Fin 3, ∀ y ∈ (D.tile e.1).carrier, g y ≤ c :=
    fun e y hy => hle y (tile_subset_target D e.1 hy)
  have hcov : D.target.edge j \ ∅ ⊆ ⋃ e ∈ D.sideEdges j, D.eSet e := by
    rintro y ⟨hy, -⟩
    obtain ⟨part, hpart⟩ := hasEdgeChains_edge D j
    have hy' := (Set.ext_iff.mp hpart y).mpr hy
    obtain ⟨e, he, hye⟩ := Set.mem_iUnion₂.mp hy'
    refine Set.mem_iUnion₂.mpr ⟨e, ?_, hye⟩
    unfold Dissection.sideEdges
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun z hz => ?_⟩
    exact (Set.ext_iff.mp hpart z).mp (Set.mem_iUnion₂.mpr ⟨e, he, hz⟩)
  have hsum := sum_hausdorff_of_partition (D.sideEdges j) D.eSet (D.target.edge j) ∅
    Set.finite_empty
    (fun e _ => ((D.tile e.1).isClosed_edge e.2).measurableSet)
    (fun e₁ h₁ e₂ h₂ hne => D.sameside_edges_subsingleton g c hg hne (hleT e₁) (hleT e₂)
      (hon e₁ h₁) (hon e₂ h₂))
    hmemS hcov
  have hfin : ∀ e ∈ D.sideEdges j,
      (Measure.hausdorffMeasure 1 : Measure Plane) (D.eSet e) ≠ ⊤ := by
    intro e _
    rw [show D.eSet e = (D.tile e.1).edge e.2 from rfl, Tri.hausdorff_edge]
    exact edist_ne_top _ _
  have hreal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_sum hfin, Tri.hausdorff_edge, edist_dist,
    ENNReal.toReal_ofReal dist_nonneg] at hreal
  rw [← hreal]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [show D.eSet e = (D.tile e.1).edge e.2 from rfl, Tri.hausdorff_edge, edist_dist,
    ENNReal.toReal_ofReal dist_nonneg]
  rfl

/-- **The boundary edges carry the target's flux.** -/
theorem Dissection.side_flux (D : Dissection N) (f : Dir → E) :
    ∑ j : Fin 3, ∑ e ∈ D.sideEdges j, D.eLen e • f (D.eDir e) = D.target.flux f := by
  unfold Tri.flux
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : ∑ e ∈ D.sideEdges j, D.eLen e • f (D.eDir e)
      = ∑ e ∈ D.sideEdges j, D.eLen e • f (D.target.leftUnit j) := by
    refine Finset.sum_congr rfl fun e he => ?_
    unfold Dissection.sideEdges at he
    rw [D.eDir_of_side (Finset.mem_filter.mp he).2]
  rw [h1, ← Finset.sum_smul, D.side_len_sum j]

end Erdos634.Geometry
