-- Draft/A1CornerLattice.lean — row0c Lemma 1 (b′) (node A1): every tile corner lies in P + L.
--
-- Formalization debt on a paper-level PROVED result (PROOF_row0c.md §3.1 with repair (b′) of
-- Paperwork P1 A1); NOT /goal progress.  Imported into All.lean (All.lean:656); on the theoremP_6 closure (UNAUDITED).  H59: no (e, f) evaluated.
--
-- Statements.
-- * `corner_mem_edgeSpan` (any `Dissection`, no angle hypothesis): every tile corner, and every
--   target corner, lies in `A + L_D`, where `A = target.pts 0` and `L_D` is the ℤ-span of all tile
--   edge vectors.
-- * `lemma1_positions` (Lemma 1 (b′) as written): for a `CongruentDissection` whose model angles are
--   `a_k·π/n`, every tile corner lies in `A + L`, where `L = Lform D n` is the ℤ-span of
--   `s_k · d`, `s_k` the model side lengths and `d` ranging over the unit vectors whose direction
--   lies in `θ₀ + (π/n)ℤ`, `θ₀` the direction of target side AB (the paper's `s_i e^{ijπ/n}` after
--   rotating AB to the real axis).  Part (a), `A1Dir.edge_dir_coset`, is the input that puts every
--   tile edge vector in `L`.
--
-- Route: the U/W argument of `A1EdgeDirections`, run with class "corners in c + L" instead of an
-- angle coset, on `target \ vertexSet` (preconnected: `convex_diff_finite_isPreconnected`, proved
-- here by two-segment paths avoiding finitely many measure-zero lines).  A common point of a bad
-- and a good tile is a shared non-vertex point, where `A1SharedClass.shared_cls` applies.  No
-- maximal segment is constructed; no tile-intersection graph is built.
import Erdos634.Draft.A1SharedClass

open scoped Classical

namespace Erdos634.Geometry.A1Pos

open Erdos634.Geometry Set MeasureTheory

variable {N : ℕ}

/-! ## A convex set with interior, minus a finite set, is preconnected -/

theorem volume_line_eq_zero {v p : Plane} (hv : v ≠ 0) :
    volume {y : Plane | cross v (y - p) = 0} = 0 := by
  have hset : {y : Plane | cross v (y - p) = 0} =
      (AffineSubspace.mk' p (LinearMap.ker (crossL v)) : Set Plane) := by
    ext y
    simp [AffineSubspace.mem_mk', LinearMap.mem_ker, crossL_apply]
  rw [hset]
  refine Measure.addHaar_affineSubspace volume _ ?_
  intro htop
  have hmem : (EuclideanSpace.single 0 (-(v 1)) + EuclideanSpace.single 1 (v 0)) + p ∈
      AffineSubspace.mk' p (LinearMap.ker (crossL v)) := by
    rw [htop]; exact AffineSubspace.mem_top ℝ Plane _
  rw [AffineSubspace.mem_mk', vsub_eq_sub, add_sub_cancel_right, LinearMap.mem_ker,
    crossL_apply] at hmem
  exact (cross_perp_pos hv).ne' hmem

theorem cross_eq_zero_of_mem_segment {a c f : Plane} (hf : f ∈ segment ℝ a c) :
    cross (f - a) (c - a) = 0 := by
  rw [segment_eq_image'] at hf
  obtain ⟨θ, -, rfl⟩ := hf
  rw [add_sub_cancel_left, cross_smul_left, cross_self, mul_zero]

theorem convex_diff_finite_isPreconnected {K : Set Plane} (hK : Convex ℝ K)
    (hint : (interior K).Nonempty) {F : Set Plane} (hF : F.Finite) : IsPreconnected (K \ F) := by
  refine isPreconnected_of_forall_pair fun a ha b hb => ?_
  set Z : Set Plane :=
    ⋃ f ∈ F, ({y | cross (f - a) (y - a) = 0} ∪ {y | cross (f - b) (y - b) = 0}) with hZdef
  have hZ : volume Z = 0 := by
    refine (measure_biUnion_null_iff hF.countable).mpr fun f hf => ?_
    have hfa : f - a ≠ 0 := sub_ne_zero.mpr fun h => ha.2 (h ▸ hf)
    have hfb : f - b ≠ 0 := sub_ne_zero.mpr fun h => hb.2 (h ▸ hf)
    exact measure_union_null (volume_line_eq_zero hfa) (volume_line_eq_zero hfb)
  obtain ⟨c, hcK, hcZ⟩ : ∃ c ∈ interior K, c ∉ Z := by
    by_contra h
    push Not at h
    have hpos := isOpen_interior.measure_pos volume hint
    have := measure_mono (μ := volume) (show interior K ⊆ Z from h)
    rw [hZ] at this
    exact (lt_of_lt_of_le hpos this).ne rfl
  have hc : c ∈ K := interior_subset hcK
  have hA : segment ℝ a c ⊆ K \ F := by
    intro y hy
    refine ⟨hK.segment_subset ha.1 hc hy, fun hyF => hcZ ?_⟩
    exact mem_iUnion₂.mpr ⟨y, hyF, Or.inl (cross_eq_zero_of_mem_segment hy)⟩
  have hB : segment ℝ b c ⊆ K \ F := by
    intro y hy
    refine ⟨hK.segment_subset hb.1 hc hy, fun hyF => hcZ ?_⟩
    exact mem_iUnion₂.mpr ⟨y, hyF, Or.inr (cross_eq_zero_of_mem_segment hy)⟩
  refine ⟨segment ℝ a c ∪ segment ℝ b c, union_subset hA hB, Or.inl (left_mem_segment ℝ a c),
    Or.inr (left_mem_segment ℝ b c), ?_⟩
  exact IsPreconnected.union c (right_mem_segment ℝ a c) (right_mem_segment ℝ b c)
    (convex_segment a c).isPreconnected (convex_segment b c).isPreconnected

/-! ## All tiles in one class -/

theorem exists_nonvertex (D : Dissection N) (i : Fin N) :
    ∃ x ∈ (D.tile i).carrier, x ∉ D.vertexSet := by
  have hns : ¬ (D.tile i).carrier ⊆ D.vertexSet := fun h =>
    (D.tile i).volume_pos.ne'
      (measure_mono_null h (D.vertexSet_finite.countable.measure_zero _))
  obtain ⟨x, hx, hxv⟩ := Set.not_subset.mp hns
  exact ⟨x, hx, hxv⟩

/-- **One class.**  All tiles have their corners in one coset of `L`. -/
theorem all_cls_eq (D : Dissection N) (L : AddSubgroup Plane)
    (hL : ∀ k (m : Fin 3), (D.tile k).pts (m + 1) - (D.tile k).pts m ∈ L) (i j : Fin N) :
    tileCls D L i = tileCls D L j := by
  by_contra hij
  set κ := tileCls D L i
  let U : Set Plane := ⋃ k ∈ {k | tileCls D L k ≠ κ}, (D.tile k).carrier
  let W : Set Plane := ⋃ k ∈ {k | tileCls D L k = κ}, (D.tile k).carrier
  have hUc : IsClosed U :=
    (Set.toFinite _).isClosed_biUnion fun k _ => (D.tile k).isCompact.isClosed
  have hWc : IsClosed W :=
    (Set.toFinite _).isClosed_biUnion fun k _ => (D.tile k).isCompact.isClosed
  have hconn : IsPreconnected (D.target.carrier \ D.vertexSet) :=
    convex_diff_finite_isPreconnected D.target.convex D.target.interior_nonempty
      D.vertexSet_finite
  have hcov : D.target.carrier \ D.vertexSet ⊆ U ∪ W := by
    rintro x ⟨hx, -⟩
    rw [← D.covers] at hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    by_cases hg : tileCls D L k = κ
    · exact Or.inr (mem_biUnion (x := k) hg hk)
    · exact Or.inl (mem_biUnion (x := k) hg hk)
  have hW : ((D.target.carrier \ D.vertexSet) ∩ W).Nonempty := by
    obtain ⟨x, hx, hxv⟩ := exists_nonvertex D i
    exact ⟨x, ⟨tile_subset_target D i hx, hxv⟩, mem_biUnion (x := i) (rfl : tileCls D L i = κ) hx⟩
  have hU : ((D.target.carrier \ D.vertexSet) ∩ U).Nonempty := by
    obtain ⟨x, hx, hxv⟩ := exists_nonvertex D j
    exact ⟨x, ⟨tile_subset_target D j hx, hxv⟩, mem_biUnion (x := j) (Ne.symm hij) hx⟩
  obtain ⟨x, ⟨-, hxv⟩, hxU, hxW⟩ :=
    isPreconnected_closed_iff.mp hconn U W hUc hWc hcov hU hW
  obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hxU
  obtain ⟨k', hk', hxk'⟩ := mem_iUnion₂.mp hxW
  have hkk : k ≠ k' := fun h => hk (h ▸ hk')
  exact hk ((shared_cls D L hL hkk hxk hxk' hxv).trans hk')

/-! ## Target corners are tile corners -/

theorem target_vertex_extreme (T : Tri) (k : Fin 3) :
    T.pts k ∈ T.carrier.extremePoints ℝ := by
  have hb : ∀ i : Fin 3, T.pts i = (T.basis : Fin 3 → Plane) i := fun _ => rfl
  refine mem_extremePoints.mpr ⟨subset_convexHull ℝ _ ⟨k, rfl⟩, fun y hy z hz hk => ?_⟩
  obtain ⟨α, β, hα, hβ, hαβ, hyz⟩ := hk
  rw [T.carrier_eq_nonneg_coord] at hy hz
  have hzero : ∀ l, l ≠ k → T.basis.coord l y = 0 ∧ T.basis.coord l z = 0 := by
    intro l hl
    have h1 : T.basis.coord l (α • y + β • z) = α * T.basis.coord l y + β * T.basis.coord l z := by
      rw [Convex.combo_affine_apply hαβ]; rfl
    rw [hyz, hb, AffineBasis.coord_apply_ne _ hl] at h1
    have hy0 := hy l
    have hz0 := hz l
    constructor <;> nlinarith [mul_nonneg hα.le hy0, mul_nonneg hβ.le hz0]
  have hvert : ∀ w : Plane, (∀ l, l ≠ k → T.basis.coord l w = 0) → w = T.pts k := by
    intro w hw
    have hne : k + 1 ≠ k + 2 := by fin_cases k <;> decide
    have h1 : k + 1 ≠ k := by fin_cases k <;> decide
    have h2 : k + 2 ≠ k := by fin_cases k <;> decide
    obtain ⟨p, hp⟩ := T.eq_vertex_of_two_coords_zero hne (hw _ h1) (hw _ h2)
    have hall : ∀ q : Fin 3, q = k ∨ q = k + 1 ∨ q = k + 2 := by
      have : ∀ u v : Fin 3, v = u ∨ v = u + 1 ∨ v = u + 2 := by decide
      exact fun q => this k q
    rcases hall p with rfl | rfl | rfl
    · exact hp
    · have := hw _ h1
      rw [hp, hb, AffineBasis.coord_apply_eq] at this
      exact absurd this one_ne_zero
    · have := hw _ h2
      rw [hp, hb, AffineBasis.coord_apply_eq] at this
      exact absurd this one_ne_zero
  exact ⟨hvert y fun l hl => (hzero l hl).1, hvert z fun l hl => (hzero l hl).2⟩

theorem target_vertex_is_tile_vertex (D : Dissection N) (k : Fin 3) :
    ∃ i m, D.target.pts k = (D.tile i).pts m := by
  have hk : D.target.pts k ∈ D.target.carrier := subset_convexHull ℝ _ ⟨k, rfl⟩
  rw [← D.covers] at hk
  obtain ⟨i, hi⟩ := mem_iUnion.mp hk
  have hext : D.target.pts k ∈ (D.tile i).carrier.extremePoints ℝ :=
    inter_extremePoints_subset_extremePoints_of_subset (tile_subset_target D i)
      ⟨hi, target_vertex_extreme D.target k⟩
  obtain ⟨m, hm⟩ := extremePoints_convexHull_subset hext
  exact ⟨i, m, hm.symm⟩

/-! ## Corners in `A + L` -/

/-- The ℤ-span of all tile edge vectors. -/
noncomputable def edgeSpan (D : Dissection N) : AddSubgroup Plane :=
  AddSubgroup.closure {v | ∃ k : Fin N, ∃ m : Fin 3, v = (D.tile k).pts (m + 1) - (D.tile k).pts m}

theorem edge_mem_edgeSpan (D : Dissection N) (k : Fin N) (m : Fin 3) :
    (D.tile k).pts (m + 1) - (D.tile k).pts m ∈ edgeSpan D :=
  AddSubgroup.subset_closure ⟨k, m, rfl⟩

/-- **Corners in `A + L`, general form.**  For any subgroup `L` containing every tile edge vector,
every tile corner lies in `A + L`, `A = target.pts 0`. -/
theorem corner_mem_of_edges (D : Dissection N) (L : AddSubgroup Plane)
    (hL : ∀ k (m : Fin 3), (D.tile k).pts (m + 1) - (D.tile k).pts m ∈ L) (i : Fin N) (k : Fin 3) :
    (D.tile i).pts k - D.target.pts 0 ∈ L := by
  obtain ⟨i₀, m₀, hA⟩ := target_vertex_is_tile_vertex D 0
  have h1 := vertex_cls D L hL i k
  have h2 := vertex_cls D L hL i₀ m₀
  rw [all_cls_eq D L hL i i₀, ← h2, ← hA, QuotientAddGroup.eq] at h1
  have := neg_mem h1
  simpa [neg_add_eq_sub, sub_eq_add_neg, add_comm] using this

/-- **Lemma 1 (b′), lattice-free form (any `Dissection`).**  Every tile corner and every target
corner lies in `A + L_D`, `L_D` the ℤ-span of the tile edge vectors. -/
theorem corner_mem_edgeSpan (D : Dissection N) :
    (∀ i k, (D.tile i).pts k - D.target.pts 0 ∈ edgeSpan D) ∧
      ∀ k, D.target.pts k - D.target.pts 0 ∈ edgeSpan D := by
  refine ⟨corner_mem_of_edges D _ (edge_mem_edgeSpan D), fun k => ?_⟩
  obtain ⟨i, m, h⟩ := target_vertex_is_tile_vertex D k
  rw [h]
  exact corner_mem_of_edges D _ (edge_mem_edgeSpan D) i m

/-! ## The paper's lattice `L` -/

/-- The paper's `L`: the ℤ-span of `s_k · d`, `s_k = |model side k|`, `d` a unit vector with
direction in `θ₀ + (π/n)ℤ`, `θ₀` the direction of target side AB. -/
noncomputable def Lform (D : CongruentDissection N) (n : ℕ) : AddSubgroup Plane :=
  AddSubgroup.closure {v | ∃ (k : Fin 3) (d : Dir),
    d.angle - (D.target.leftUnit 0).angle ∈ A1Dir.H n ∧
      v = dist (D.model.pts k) (D.model.pts (k + 1)) • d.1}

theorem side_length_model (D : CongruentDissection N) (i : Fin N) (m : Fin 3) :
    ∃ k : Fin 3, ‖(D.tile i).pts (m + 1) - (D.tile i).pts m‖
      = dist (D.model.pts k) (D.model.pts (k + 1)) := by
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent i).dist_eq
  have hsucc : ∀ l : Fin 3, l + 1 ≠ l := by decide
  have hneq : σ (m + 1) ≠ σ m := fun h => hsucc m (σ.injective h)
  have key : ∀ p q : Fin 3, p ≠ q → q = p + 1 ∨ p = q + 1 := by decide
  rw [← dist_eq_norm, hσ]
  rcases key _ _ hneq with h | h
  · exact ⟨σ (m + 1), by rw [h]⟩
  · exact ⟨σ m, by rw [dist_comm, h]⟩

/-- **Every tile edge vector lies in the paper's `L`** — part (a) is the input. -/
theorem edge_mem_Lform (D : CongruentDissection N) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) (i : Fin N) (m : Fin 3) :
    (D.tile i).pts (m + 1) - (D.tile i).pts m ∈ Lform D n := by
  set v := (D.tile i).pts (m + 1) - (D.tile i).pts m with hvdef
  have hsucc : ∀ l : Fin 3, l + 1 ≠ l := by decide
  have hv : v ≠ 0 := sub_ne_zero.mpr fun h => hsucc m ((D.tile i).indep.injective h)
  have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let dv : Dir := ⟨‖v‖⁻¹ • v, by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnv]⟩
  have hvd : v = ‖v‖ • dv.1 := by
    show v = ‖v‖ • (‖v‖⁻¹ • v)
    rw [smul_smul, mul_inv_cancel₀ hnv, one_smul]
  have hcos := A1Dir.edge_dir_coset D hn a ha i m
  have hang : dv.angle - (D.target.leftUnit 0).angle ∈ A1Dir.H n := by
    rcases (D.tile i).leftDir_eq_or m with h | h
    · have hdu : (D.tile i).leftUnit m = dv := by
        apply Subtype.ext
        simp only [Tri.leftUnit, dv, h, hvdef]
      rwa [hdu] at hcos
    · have hdu : (D.tile i).leftUnit m = Dir.neg dv := by
        apply Subtype.ext
        simp only [Tri.leftUnit, Dir.neg, dv, h, hvdef, norm_neg, smul_neg]
      rw [hdu, Dir.angle_neg] at hcos
      have := sub_mem hcos (A1Dir.pi_mem hn)
      convert this using 1
      abel
  obtain ⟨k, hk⟩ := side_length_model D i m
  refine AddSubgroup.subset_closure ⟨k, dv, hang, ?_⟩
  rw [← hk]
  exact hvd

/-- **Lemma 1 (b′) (row0c §3.1, repaired in P1 A1), on a real `CongruentDissection`.**  If the
model's angles are `a_k·π/n`, every tile corner lies in `A + L`, `A = target.pts 0` and `L` the
ℤ-span of `s_k · e^{i(θ₀ + jπ/n)}` (`Lform`).  Reflections allowed, not edge-to-edge, no
connectivity hypothesis.  (The target corners too: `lemma1_positions_target`.) -/
theorem lemma1_positions (D : CongruentDissection N) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) (i : Fin N) (k : Fin 3) :
    (D.tile i).pts k - D.target.pts 0 ∈ Lform D n :=
  corner_mem_of_edges D.toDissection _ (edge_mem_Lform D hn a ha) i k

theorem lemma1_positions_target (D : CongruentDissection N) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) (k : Fin 3) :
    D.target.pts k - D.target.pts 0 ∈ Lform D n := by
  obtain ⟨i, m, h⟩ := target_vertex_is_tile_vertex D.toDissection k
  rw [h]
  exact lemma1_positions D hn a ha i m

/-- Joint witness: the real `CongruentDissection 2` of `CaseALemmaHPiFour` (n = 4, angles
(1,2,1)·π/4) satisfies every hypothesis of `lemma1_positions`. -/
theorem lemma1_positions_witness (i : Fin 2) (k : Fin 3) :
    (Erdos634.Draft.CaseALemmaHPiFour.dissection.tile i).pts k
      - Erdos634.Draft.CaseALemmaHPiFour.dissection.target.pts 0
      ∈ Lform Erdos634.Draft.CaseALemmaHPiFour.dissection 4 :=
  lemma1_positions _ (n := 4) (by norm_num) ![1, 2, 1]
    Erdos634.Draft.CaseALemmaVWitness.model_angles i k

end Erdos634.Geometry.A1Pos

#print axioms Erdos634.Geometry.A1Pos.convex_diff_finite_isPreconnected
#print axioms Erdos634.Geometry.A1Pos.all_cls_eq
#print axioms Erdos634.Geometry.A1Pos.corner_mem_edgeSpan
#print axioms Erdos634.Geometry.A1Pos.lemma1_positions
#print axioms Erdos634.Geometry.A1Pos.lemma1_positions_target
#print axioms Erdos634.Geometry.A1Pos.lemma1_positions_witness
