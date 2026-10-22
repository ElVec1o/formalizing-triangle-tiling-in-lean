-- Draft/LaczFormalFluxPolyFin.lean -- FLUX-CANCELLATION for polygon targets, part 4 (final): tile edges on a side carry the side direction, side edges sum to
-- the side length, and the POLYGON FLUX CANCELLATION
--     `ConvPoly.flux_cancel`:  for a dissection R of a strictly convex polygon P into triangles and an ODD direction weight f (f(-d) = -f(d)),
--     sum over tiles of Tri.flux f  =  sum over the sides of P of (side length) * f(side direction)          [= P.flux f].
-- Here Tri.flux T f = sum over the three sides of T (directed with T on its left) of length * f(direction); Dir = unit vectors of the plane.
-- Hypotheses: R.region = P.carrier (the dissection is of P); f odd.  No hypothesis on the tiles (congruence not needed).
-- NOTE / UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 7.3/8.3: the additive functional Phi), Beeson, Beeson-Zhang.  Port of Draft/FluxCancel.lean chain.
import Erdos634.Draft.LaczFormalFluxPolyBdy
import Erdos634.Draft.LaczFormalFluxPolySame
import Erdos634.Draft.FluxBoundary

open scoped Classical
open MeasureTheory Set Erdos634.Geometry Erdos634.RegionDissection
set_option linter.dupNamespace false

namespace Erdos634.Draft.LaczFormal.Thm21

variable {N M : ℕ} [NeZero M] {E : Type*} [AddCommGroup E] [Module ℝ E]

namespace ConvPoly
variable (P : ConvPoly M)

/-- The unit direction of the `j`-th side `v_j -> v_{j+1}` (interior on the left). -/
noncomputable def sideDir (j : Fin M) : Dir :=
  ⟨‖P.e j‖⁻¹ • P.e j, by
    rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (P.e_ne_zero P.three_le j))⟩

/-- The flux of a direction weight through the ccw boundary of the polygon: sum of (side length) * f(side direction). -/
noncomputable def flux (f : Dir → E) : E := ∑ j, P.side j • f (P.sideDir j)

/-- Tile edges lying on side `j`. -/
noncomputable def sideEdges (R : RegionDissection N) (j : Fin M) : Finset (Fin N × Fin 3) :=
  Finset.univ.filter fun e => R.eSet e ⊆ P.sideSet j

/-- Two distinct sides meet only at their common vertex. -/
theorem side_inter {j j' : Fin M} (hjj : j' ≠ j) {x : Plane} (hx : x ∈ P.sideSet j) (hx' : x ∈ P.sideSet j') :
    (j' = j + 1 ∧ x = P.v (j + 1)) ∨ (j' = j - 1 ∧ x = P.v j) := by
  have hM := P.three_le
  obtain ⟨s, t, hs, ht, hst, hxe⟩ := hx
  have hs' : s = 1 - t := by linarith
  subst hs'
  have hc0 := P.c_sideSet hx'
  rw [← hxe] at hc0
  by_contra hcon
  push Not at hcon
  have h1 : j' = j + 1 → t < 1 := fun h =>
    lt_of_le_of_ne (by linarith) (fun h1 => hcon.1 h (by rw [← hxe, h1]; simp))
  have h2 : j' = j - 1 → 0 < t := fun h =>
    lt_of_le_of_ne ht (fun h0 => hcon.2 h (by rw [← hxe, ← h0]; simp))
  have := P.c_edge_pos hM j ⟨ht, by linarith⟩ hjj h1 h2
  linarith

theorem sideEdges_disjoint (R : RegionDissection N) {j j' : Fin M} (h : j ≠ j') :
    Disjoint (P.sideEdges R j) (P.sideEdges R j') := by
  have hM := P.three_le
  rw [Finset.disjoint_left]
  intro e he he'
  have hj := (Finset.mem_filter.mp he).2
  have hj' := (Finset.mem_filter.mp he').2
  have ha : (R.tile e.1).pts e.2 ∈ R.eSet e := left_mem_segment ℝ _ _
  have hb : (R.tile e.1).pts (e.2 + 1) ∈ R.eSet e := right_mem_segment ℝ _ _
  have hsucc : ∀ i : Fin 3, i ≠ i + 1 := by decide
  have hne : (R.tile e.1).pts e.2 ≠ (R.tile e.1).pts (e.2 + 1) := fun hh =>
    hsucc e.2 ((R.tile e.1).indep.injective hh)
  have h1 := P.side_inter (Ne.symm h) (hj ha) (hj' ha)
  have h2 := P.side_inter (Ne.symm h) (hj hb) (hj' hb)
  have hf := (fin_facts hM j).2.2.2.1
  rcases h1 with ⟨e1, x1⟩ | ⟨e1, x1⟩ <;> rcases h2 with ⟨e2, x2⟩ | ⟨e2, x2⟩
  · exact hne (x1.trans x2.symm)
  · exact hf (e1.symm.trans e2)
  · exact hf (e2.symm.trans e1)
  · exact hne (x1.trans x2.symm)

end ConvPoly

namespace ConvPoly
variable (P : ConvPoly M)

omit [Module ℝ E] in
/-- **The edge sum splits** into interior edges and the edges on each side of the polygon. -/
theorem sum_split (R : RegionDissection N) (hR : R.region = P.carrier) (g : Fin N × Fin 3 → E) :
    ∑ e, g e = ∑ e ∈ R.intEdges, g e + ∑ j : Fin M, ∑ e ∈ P.sideEdges R j, g e := by
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin M))) (P.sideEdges R) :=
    fun j _ j' _ hjj' => P.sideEdges_disjoint R hjj'
  rw [← Finset.sum_biUnion hdisj]
  have hsucc : ∀ i : Fin 3, i ≠ i + 1 := by decide
  have hunion : R.intEdges ∪ (Finset.univ : Finset (Fin M)).biUnion (P.sideEdges R) = Finset.univ := by
    ext e
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true]
    by_cases h : e ∈ R.intEdges
    · exact Or.inl h
    · right
      have hab : (R.tile e.1).pts e.2 ≠ (R.tile e.1).pts (e.2 + 1) := fun hh =>
        hsucc e.2 ((R.tile e.1).indep.injective hh)
      obtain ⟨hm, hA, hB⟩ := mem_ne_ends_of_avg hab (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
      have hn : ((1:ℝ)/2) • (R.tile e.1).pts e.2 + ((1:ℝ)/2) • (R.tile e.1).pts (e.2 + 1) ∉ interior P.carrier := by
        intro hi
        exact h (R.mem_intEdges_of_interior hm (hR ▸ hi))
      obtain ⟨j, hj⟩ := P.edge_on_side R hR e hm hA hB hn
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  have hdis2 : Disjoint R.intEdges ((Finset.univ : Finset (Fin M)).biUnion (P.sideEdges R)) := by
    rw [Finset.disjoint_left]
    intro e he he'
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at he'
    obtain ⟨j, hj⟩ := he'
    obtain ⟨x, hx, hxi⟩ := (Finset.mem_filter.mp he).2
    exact P.not_interior_of_sideSet ((Finset.mem_filter.mp hj).2 hx) (hR ▸ hxi)
  rw [← Finset.sum_union hdis2, hunion]

end ConvPoly

theorem _root_.Erdos634.RegionDissection.RegionDissection.cover_side (R : RegionDissection N) (g : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (hg : g ≠ 0) (hle : ∀ x ∈ R.region, g x ≤ c) {A B : Plane} (hnd : A ≠ B)
    (hS : {x ∈ R.region | g x = c} = segment ℝ A B) :
    segment ℝ A B ⊆ ⋃ e ∈ (Finset.univ.filter fun e : Fin N × Fin 3 => (R.tile e.1).edge e.2 ⊆ segment ℝ A B),
      (R.tile e.1).edge e.2 := by
  classical
  set S : Set Plane := segment ℝ A B with hSdef
  set part : Finset (Fin N × Fin 3) :=
    Finset.univ.filter (fun e : Fin N × Fin 3 => (R.tile e.1).edge e.2 ⊆ S) with hpart
  have hFfin : (Set.range fun (jk : Fin N × Fin 3) => (R.tile jk.1).pts jk.2).Finite := Set.finite_range _
  have hUclosed : IsClosed (⋃ e ∈ part, (R.tile e.1).edge e.2) :=
    Set.Finite.isClosed_biUnion (Finset.finite_toSet part) (fun e _ => (R.tile e.1).isClosed_edge e.2)
  have hkey : S \ (Set.range fun (jk : Fin N × Fin 3) => (R.tile jk.1).pts jk.2)
            ⊆ ⋃ e ∈ part, (R.tile e.1).edge e.2 := by
    rintro x ⟨hxS, hxF⟩
    have hxt : x ∈ R.region ∧ g x = c := by
      have : x ∈ {x | x ∈ R.region ∧ g x = c} := by rw [hS]; exact hxS
      exact this
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp (by rw [R.covers]; exact hxt.1)
    have hlej : ∀ y ∈ (R.tile j).carrier, g y ≤ c := fun y hy => hle y (R.tile_sub_region j hy)
    have hxv : ∀ k, x ≠ (R.tile j).pts k := by
      intro k hk; exact hxF ⟨(j, k), hk.symm⟩
    obtain ⟨k, hk⟩ := contact_is_edge (R.tile j) g c hg hlej hxj hxt.2 hxv
    have hsub : (R.tile j).edge k ⊆ S := by
      rw [← hk]
      rintro y ⟨hy1, hy2⟩
      have : y ∈ {x | x ∈ R.region ∧ g x = c} := ⟨R.tile_sub_region j hy1, hy2⟩
      rw [hS] at this; exact this
    refine Set.mem_iUnion₂.mpr ⟨(j, k), ?_, ?_⟩
    · rw [hpart, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hsub⟩
    · rw [← hk]; exact ⟨hxj, hxt.2⟩
  calc S ⊆ closure (S \ (Set.range fun (jk : Fin N × Fin 3) => (R.tile jk.1).pts jk.2)) :=
        Erdos634.SegmentDense.subset_closure_diff_finite hnd hFfin
    _ ⊆ closure (⋃ e ∈ part, (R.tile e.1).edge e.2) := closure_mono hkey
    _ = _ := hUclosed.closure_eq

namespace ConvPoly
variable (P : ConvPoly M)

/-- The supporting functional of side `j`: `y ↦ -cross(e_j, y)`; the polygon lies in `{sideG ≤ sideC}`. -/
noncomputable def sideG (j : Fin M) : Plane →ₗ[ℝ] ℝ := -(crossL (P.e j))
/-- The supporting constant of side `j`. -/
noncomputable def sideC (j : Fin M) : ℝ := -cross (P.e j) (P.v j)

theorem sideG_apply (j : Fin M) (y : Plane) : P.sideG j y = -cross (P.e j) y := by
  simp [sideG, crossL_apply]

theorem c_eq (j : Fin M) (y : Plane) : P.c j y = cross (P.e j) y - cross (P.e j) (P.v j) := by
  simp only [c, cross2, cross, PiLp.sub_apply]; ring

theorem sideG_eq_iff (j : Fin M) (y : Plane) : P.sideG j y = P.sideC j ↔ P.c j y = 0 := by
  rw [sideG_apply, sideC, c_eq]; constructor <;> intro h <;> linarith

theorem sideG_le (j : Fin M) {y : Plane} (hy : y ∈ P.carrier) : P.sideG j y ≤ P.sideC j := by
  have h1 : 0 ≤ P.c j y := hy j
  rw [sideG_apply, sideC]; have h2 := P.c_eq j y; linarith

theorem sideG_ne (j : Fin M) : P.sideG j ≠ 0 :=
  neg_ne_zero.mpr (crossL_ne_zero (P.e_ne_zero P.three_le j))

theorem side_contact (j : Fin M) :
    {x ∈ P.carrier | P.sideG j x = P.sideC j} = P.sideSet j := by
  ext x; constructor
  · rintro ⟨hx, h⟩
    obtain ⟨t, ht, hW⟩ := P.edge_param P.three_le hx ((P.sideG_eq_iff j x).mp h)
    exact ⟨1 - t, t, by linarith [ht.2], ht.1, by ring, hW.symm⟩
  · intro hx
    exact ⟨P.sideSet_sub_carrier j hx, (P.sideG_eq_iff j x).mpr (P.c_sideSet hx)⟩

/-- **A tile edge on side `j` carries the side's own ccw direction.** -/
theorem eDir_of_side (R : RegionDissection N) (hR : R.region = P.carrier) {e : Fin N × Fin 3} {j : Fin M}
    (h : R.eSet e ⊆ P.sideSet j) : R.eDir e = P.sideDir j := by
  have hsucc : ∀ i : Fin 3, i ≠ i + 1 := by decide
  have hshift : ∀ i : Fin 3, i + 2 + 1 = i := by decide
  have hab : (R.tile e.1).pts e.2 ≠ (R.tile e.1).pts (e.2 + 1) := fun hh =>
    hsucc e.2 ((R.tile e.1).indep.injective hh)
  obtain ⟨hxT, hxa, hxb⟩ := mem_ne_ends_of_avg hab (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
  obtain ⟨hzT, hpT⟩ := (R.tile e.1).onEdge_param (k := e.2) hxT hxa hxb
  have hgx : P.sideG j (((1:ℝ)/2) • (R.tile e.1).pts e.2 + ((1:ℝ)/2) • (R.tile e.1).pts (e.2 + 1)) = P.sideC j :=
    (P.sideG_eq_iff j _).mpr (P.c_sideSet (h hxT))
  have hleT : ∀ y ∈ (R.tile e.1).carrier, P.sideG j y ≤ P.sideC j := fun y hy =>
    P.sideG_le j (hR ▸ R.tile_sub_region e.1 hy)
  have hg := P.sideG_ne j
  have hinT : ∀ v, P.sideG j v < 0 → 0 < cross ((R.tile e.1).leftDir e.2) v := by
    intro v hv
    have := (R.tile e.1).edge_inward (P.sideG j) (P.sideC j) hg hleT hzT hpT hgx hv
    rwa [hshift] at this
  have hnegcross : ∀ w v : Plane, cross w (-v) = - cross w v := by
    intro w v; simp only [cross, PiLp.neg_apply]; ring
  have hdisjT : ∀ v, ¬ (0 < crossL ((R.tile e.1).leftDir e.2) v ∧ 0 < P.sideG j v) := by
    rintro v ⟨h1, h2⟩
    have h3 := hinT (-v) (by rw [map_neg]; linarith)
    rw [crossL_apply] at h1
    rw [hnegcross] at h3
    linarith
  obtain ⟨c₁, hc₁, hgT⟩ := proportional_of_disjoint_pos (crossL ((R.tile e.1).leftDir e.2)) (P.sideG j)
    (crossL_ne_zero ((R.tile e.1).leftDir_ne_zero e.2)) hg hdisjT
  have hprop : P.e j = (-c₁) • (R.tile e.1).leftDir e.2 := by
    have hzero : ∀ v, cross (P.e j - (-c₁) • (R.tile e.1).leftDir e.2) v = 0 := by
      intro v
      have e1 := hgT v
      rw [P.sideG_apply, crossL_apply] at e1
      simp only [cross, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at e1 ⊢
      linarith
    exact sub_eq_zero.mp (eq_zero_of_cross_eq_zero hzero)
  have hc₁' : (-c₁) ≠ 0 := by linarith
  have hpos : 0 < (-c₁)⁻¹ := inv_pos.mpr (by linarith)
  have hv : (R.tile e.1).leftDir e.2 = (-c₁)⁻¹ • P.e j := by
    rw [hprop, smul_smul, inv_mul_cancel₀ hc₁', one_smul]
  have hunit := unit_smul_of_pos hpos (P.e_ne_zero P.three_le j) hv
  apply Subtype.ext
  show ‖(R.tile e.1).leftDir e.2‖⁻¹ • (R.tile e.1).leftDir e.2 = ‖P.e j‖⁻¹ • P.e j
  exact hunit

/-- **Side edges sum to the side length.** -/
theorem side_len_sum (R : RegionDissection N) (hR : R.region = P.carrier) (j : Fin M) :
    ∑ e ∈ P.sideEdges R j, R.eLen e = P.side j := by
  have hnd : P.v j ≠ P.v (j + 1) := by
    intro hh
    apply P.e_ne_zero P.three_le j
    unfold e; rw [← hh]; simp
  have hS : {x ∈ R.region | P.sideG j x = P.sideC j} = segment ℝ (P.v j) (P.v (j + 1)) := by
    rw [hR]; exact P.side_contact j
  have hle : ∀ x ∈ R.region, P.sideG j x ≤ P.sideC j := fun x hx => P.sideG_le j (hR ▸ hx)
  have hcov0 := R.cover_side (P.sideG j) (P.sideC j) (P.sideG_ne j) hle hnd hS
  have hmemS : ∀ e ∈ P.sideEdges R j, R.eSet e ⊆ P.sideSet j := fun e he =>
    (Finset.mem_filter.mp he).2
  have hon : ∀ e ∈ P.sideEdges R j, ∀ y ∈ (R.tile e.1).edge e.2, P.sideG j y = P.sideC j := fun e he y hy =>
    (P.sideG_eq_iff j y).mpr (P.c_sideSet (hmemS e he hy))
  have hleT : ∀ e : Fin N × Fin 3, ∀ y ∈ (R.tile e.1).carrier, P.sideG j y ≤ P.sideC j :=
    fun e y hy => hle y (R.tile_sub_region e.1 hy)
  have hcov : P.sideSet j \ ∅ ⊆ ⋃ e ∈ P.sideEdges R j, R.eSet e := by
    intro y hy
    exact hcov0 hy.1
  have hsum := sum_hausdorff_of_partition (P.sideEdges R j) R.eSet (P.sideSet j) ∅
    Set.finite_empty
    (fun e _ => ((R.tile e.1).isClosed_edge e.2).measurableSet)
    (fun e₁ h₁ e₂ h₂ hne => R.sameside_edges_subsingleton (P.sideG j) (P.sideC j) (P.sideG_ne j) hne
      (hleT e₁) (hleT e₂) (hon e₁ h₁) (hon e₂ h₂))
    hmemS hcov
  have hfin : ∀ e ∈ P.sideEdges R j,
      (Measure.hausdorffMeasure 1 : Measure Plane) (R.eSet e) ≠ ⊤ := by
    intro e _
    rw [show R.eSet e = (R.tile e.1).edge e.2 from rfl, Tri.hausdorff_edge]
    exact edist_ne_top _ _
  have hreal := congrArg ENNReal.toReal hsum
  have hseg : (Measure.hausdorffMeasure 1 : Measure Plane) (P.sideSet j) = edist (P.v j) (P.v (j + 1)) :=
    MeasureTheory.hausdorffMeasure_segment _ _
  rw [ENNReal.toReal_sum hfin, hseg, edist_dist, ENNReal.toReal_ofReal dist_nonneg] at hreal
  rw [show P.side j = dist (P.v j) (P.v (j + 1)) from rfl, ← hreal]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [show R.eSet e = (R.tile e.1).edge e.2 from rfl, Tri.hausdorff_edge, edist_dist,
    ENNReal.toReal_ofReal dist_nonneg]
  rfl

/-- **The boundary edges carry the polygon's flux.** -/
theorem side_flux (R : RegionDissection N) (hR : R.region = P.carrier) (f : Dir → E) :
    ∑ j : Fin M, ∑ e ∈ P.sideEdges R j, R.eLen e • f (R.eDir e) = P.flux f := by
  unfold flux
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : ∑ e ∈ P.sideEdges R j, R.eLen e • f (R.eDir e) = ∑ e ∈ P.sideEdges R j, R.eLen e • f (P.sideDir j) := by
    refine Finset.sum_congr rfl fun e he => ?_
    rw [P.eDir_of_side R hR (Finset.mem_filter.mp he).2]
  rw [h1, ← Finset.sum_smul, P.side_len_sum R hR j]

theorem pos_of_region (R : RegionDissection N) (hR : R.region = P.carrier) : 0 < N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · exfalso
    subst h
    have hv := P.v_mem_carrier 0
    rw [← hR, ← R.covers] at hv
    simp at hv
  · exact h

/-- **POLYGON FLUX CANCELLATION** (`lem:cancel` for a convex-polygon target).  For a dissection `R` of the strictly convex polygon `P` into triangles
(no congruence needed, not necessarily edge to edge) and an odd direction weight `f` (`f (-d) = - f d`):
`sum over tiles of Tri.flux f = P.flux f`. -/
theorem flux_cancel (R : RegionDissection N) (hR : R.region = P.carrier) (f : Dir → E)
    (hodd : ∀ d, f (Dir.neg d) = - f d) :
    ∑ i, (R.tile i).flux f = P.flux f := by
  rw [R.flux_sum_eq, P.sum_split R hR, R.interior_flux_zero (P.pos_of_region R hR) (P.edgeDich R hR) f hodd, zero_add,
    P.side_flux R hR]

end ConvPoly

end Erdos634.Draft.LaczFormal.Thm21
