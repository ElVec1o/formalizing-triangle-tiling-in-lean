-- Draft/A1EdgeDirections.lean — row0c Lemma 1 (a) (node A1, blocker B-L1 part (a)):
-- in a CongruentDissection whose model angles are a_k·π/n, EVERY tile edge direction lies in the
-- single coset θ₀ + (π/n)ℤ of Real.Angle, θ₀ the direction of target side 0 (A→B, up to π).
--
-- Formalization debt on a paper-level PROVED result (PROOF_row0c.md §3.1(a)); NOT /goal progress.
-- Imported into All.lean (All.lean:648); on the theoremP_6 closure (UNAUDITED).  H59: no (e, f) evaluated.
--
-- Route.  The paper uses the connectivity of the tile-intersection graph.  That graph is never
-- built here: connectivity is replaced by the connectedness of ℝ² minus the (finite) vertex set
-- (Mathlib `Set.Countable.isConnected_compl_of_one_lt_rank`).  Split the plane into
--   U = ⋃ (tiles in a wrong coset),   W = ⋃ (tiles in the right coset) ∪ (int target)ᶜ,
-- both closed, covering ℝ².  A non-vertex point of U ∩ W is either shared by two distinct tiles
-- (then `Dissection.leftUnit_neg` gives antiparallel edges, same coset since π ∈ (π/n)ℤ) or a
-- boundary point of the target on a wrong tile (then `edge_interior_or_side` + `eDir_of_side`
-- make that edge a target side).  So U ∩ W ⊆ vertexSet, and connectedness forces U = ∅.
--
-- Reuse (cited): Tri.leftUnit_turn_of_pos/neg, Dir.angle_neg (FluxTurn); Dissection.leftUnit_neg,
-- eq_vertex_of_two_coords_zero, mem_edge_of_coord_zero, ball_subset_of_pos, vertexSet(_finite),
-- tile_subset_target (Dissection); edge_interior_or_side (FluxCore); eDir_of_side (FluxBoundary);
-- congruent_corner_angles; CaseA.LemmaV.target_angle_nat; CosetPropagation is NOT needed.
import Erdos634.Draft.CaseALemmaVWitness
import Erdos634.Draft.FluxBoundary

open scoped Classical

namespace Erdos634.Geometry.A1Dir

open Erdos634.Geometry Set

/-- The angle subgroup `(π/n)ℤ ⊂ ℝ/2πℤ`. -/
noncomputable def H (n : ℕ) : AddSubgroup Real.Angle :=
  AddSubgroup.zmultiples (((Real.pi / n : ℝ)) : Real.Angle)

theorem natmul_mem (n a : ℕ) : ((a * Real.pi / n : ℝ) : Real.Angle) ∈ H n := by
  refine AddSubgroup.mem_zmultiples_iff.mpr ⟨(a : ℤ), ?_⟩
  rw [← Real.Angle.coe_zsmul, zsmul_eq_mul]
  congr 1
  push_cast
  ring

theorem pi_mem {n : ℕ} (hn : 0 < n) : ((Real.pi : ℝ) : Real.Angle) ∈ H n := by
  have h := natmul_mem n n
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rwa [show (n : ℝ) * Real.pi / n = Real.pi by field_simp] at h

/-- **Tile-local rule, one step.** -/
theorem turn_mem {n : ℕ} (hn : 0 < n) (T : Tri)
    (hT : ∀ k, ∃ a : ℕ, T.angleAt k = a * Real.pi / n) (k : Fin 3) :
    (T.leftUnit (k + 1)).angle - (T.leftUnit k).angle ∈ H n := by
  obtain ⟨a, ha⟩ := hT (k + 1)
  have hmem : ((Real.pi - T.angleAt (k + 1) : ℝ) : Real.Angle) ∈ H n := by
    rw [Real.Angle.coe_sub, ha]
    exact sub_mem (pi_mem hn) (natmul_mem n a)
  rcases T.det_pos_or_neg with h | h
  · rw [T.leftUnit_turn_of_pos h k]
    simpa using hmem
  · rw [T.leftUnit_turn_of_neg h k]
    simpa using neg_mem hmem

/-- **Tile-local rule.**  A triangle with angles in `(π/n)ℕ` has its three edge directions in one
coset of `(π/n)ℤ`. -/
theorem tile_local {n : ℕ} (hn : 0 < n) (T : Tri)
    (hT : ∀ k, ∃ a : ℕ, T.angleAt k = a * Real.pi / n) (k : Fin 3) :
    (T.leftUnit k).angle - (T.leftUnit 0).angle ∈ H n := by
  have h01 : (T.leftUnit 1).angle - (T.leftUnit 0).angle ∈ H n := turn_mem hn T hT 0
  have h12 : (T.leftUnit 2).angle - (T.leftUnit 1).angle ∈ H n := turn_mem hn T hT 1
  have hk : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  rcases hk k with rfl | rfl | rfl
  · simp
  · exact h01
  · have := add_mem h12 h01
    rwa [sub_add_sub_cancel] at this

/-- A point of a triangle that is not a vertex is interior or in the relative interior of one edge. -/
theorem pt_cases (T : Tri) {x : Plane} (hx : x ∈ T.carrier) (hv : ∀ m, x ≠ T.pts m) :
    (∀ i, 0 < T.basis.coord i x) ∨
      ∃ m, T.basis.coord m x = 0 ∧ ∀ j, j ≠ m → 0 < T.basis.coord j x := by
  rw [T.carrier_eq_nonneg_coord] at hx
  by_cases h : ∃ m, T.basis.coord m x = 0
  · obtain ⟨m, hm⟩ := h
    refine Or.inr ⟨m, hm, fun j hj => lt_of_le_of_ne (hx j) (fun h0 => ?_)⟩
    obtain ⟨p, hp⟩ := T.eq_vertex_of_two_coords_zero hj h0.symm hm
    exact hv p hp
  · push Not at h
    exact Or.inl fun i => lt_of_le_of_ne (hx i) (Ne.symm (h i))

theorem mem_interior_of_pos (T : Tri) {x : Plane} (hpos : ∀ i, 0 < T.basis.coord i x) :
    x ∈ interior T.carrier := by
  obtain ⟨r, hr, hsub⟩ := T.ball_subset_of_pos hpos
  exact mem_interior.mpr ⟨_, hsub, Metric.isOpen_ball, Metric.mem_ball_self hr⟩

/-- An interior point of one tile lies in no other tile. -/
theorem interior_meets {N : ℕ} (D : Dissection N) {i j : Fin N} (hij : i ≠ j) {x : Plane}
    (hxi : x ∈ interior (D.tile i).carrier) (hxj : x ∈ (D.tile j).carrier) : False := by
  have hcl : (D.tile j).carrier ⊆ closure (interior (D.tile j).carrier) := by
    rw [(D.tile j).convex.closure_interior_eq_closure_of_nonempty_interior
      (D.tile j).interior_nonempty]
    exact subset_closure
  obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.mp (hcl hxj) _ isOpen_interior hxi
  exact Set.disjoint_left.mp (D.interiors_disjoint hij) hy1 hy2

/-- **Shared point.**  Two distinct tiles through a common non-vertex point carry antiparallel
edges there. -/
theorem shared_point {N : ℕ} (D : Dissection N) {i j : Fin N} (hij : i ≠ j) {x : Plane}
    (hxi : x ∈ (D.tile i).carrier) (hxj : x ∈ (D.tile j).carrier) (hxv : x ∉ D.vertexSet) :
    ∃ k k', (D.tile j).leftUnit k' = Dir.neg ((D.tile i).leftUnit k) := by
  have hnv := D.notMem_vertexSet hxv
  rcases pt_cases _ hxi (hnv i) with hp | ⟨m, hm, ho⟩
  · exact (interior_meets D hij (mem_interior_of_pos _ hp) hxj).elim
  rcases pt_cases _ hxj (hnv j) with hp' | ⟨m', hm', ho'⟩
  · exact (interior_meets D hij.symm (mem_interior_of_pos _ hp') hxi).elim
  exact ⟨m + 1, m' + 1, D.leftUnit_neg hij hm ho hm' ho'⟩

/-- **Boundary point.**  A tile through a non-vertex point off the target's interior has an edge
carrying a target side's direction. -/
theorem boundary_point {N : ℕ} (D : Dissection N) {i : Fin N} {x : Plane}
    (hxi : x ∈ (D.tile i).carrier) (hxv : x ∉ D.vertexSet)
    (hxint : x ∉ interior D.target.carrier) :
    ∃ k j, (D.tile i).leftUnit k = D.target.leftUnit j := by
  have hnv := D.notMem_vertexSet hxv
  rcases pt_cases _ hxi (hnv i) with hp | ⟨m, hm, ho⟩
  · exact absurd (interior_mono (tile_subset_target D i) (mem_interior_of_pos _ hp)) hxint
  have hxe : x ∈ D.eSet (i, m + 1) := (D.tile i).mem_edge_of_coord_zero hm ho
  rcases D.edge_interior_or_side (i, m + 1) hxe (hnv i _) (hnv i _) with h | ⟨j, hj⟩
  · exact absurd h hxint
  · have h2 := D.eDir_of_side hj
    unfold Dissection.eDir at h2
    exact ⟨_, _, h2⟩

/-- Tile angles of a congruent dissection with model angles in `(π/n)ℕ`. -/
theorem tile_angles {N : ℕ} (D : CongruentDissection N) {n : ℕ} (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) (i : Fin N) (k : Fin 3) :
    ∃ b : ℕ, (D.tile i).angleAt k = b * Real.pi / n := by
  obtain ⟨k', hk'⟩ := congruent_corner_angles (D.tiles_congruent i).symm k
  refine ⟨a k', ?_⟩
  have h := ha k'
  unfold Tri.angleAt at h ⊢
  rw [hk']
  exact h

/-- Within a tile, one edge is in a coset iff edge 0 is. -/
theorem edge_iff {n : ℕ} (hn : 0 < n) (T : Tri)
    (hT : ∀ k, ∃ a : ℕ, T.angleAt k = a * Real.pi / n) (θ : Real.Angle) (k : Fin 3) :
    (T.leftUnit k).angle - θ ∈ H n ↔ (T.leftUnit 0).angle - θ ∈ H n := by
  have hl := tile_local hn T hT k
  constructor
  · intro h
    have := sub_mem h hl
    rwa [sub_sub_sub_cancel_left] at this
  · intro h
    have := add_mem hl h
    rwa [sub_add_sub_cancel] at this

theorem one_lt_rank : 1 < Module.rank ℝ Plane := by
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace]
  norm_num

/-- **Lemma 1 (a), tile form.**  Every tile's edge-0 direction lies in the coset of target side 0. -/
theorem tile_dir_coset {N : ℕ} (D : CongruentDissection N) {n : ℕ} (hn : 0 < n)
    (a : Fin 3 → ℕ) (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) (i : Fin N) :
    ((D.tile i).leftUnit 0).angle - (D.target.leftUnit 0).angle ∈ H n := by
  set θ₀ := (D.target.leftUnit 0).angle with hθ₀
  have htile := tile_angles D a ha
  have htgt : ∀ j, (D.target.leftUnit j).angle - θ₀ ∈ H n :=
    tile_local hn D.target (CaseA.LemmaV.target_angle_nat D hn a ha)
  let good : Fin N → Prop := fun i => ((D.tile i).leftUnit 0).angle - θ₀ ∈ H n
  have hedge : ∀ i k, ((D.tile i).leftUnit k).angle - θ₀ ∈ H n ↔ good i :=
    fun i k => edge_iff hn (D.tile i) (htile i) θ₀ k
  by_contra hbad0
  let U : Set Plane := ⋃ i ∈ {i | ¬ good i}, (D.tile i).carrier
  let W : Set Plane := (⋃ i ∈ {i | good i}, (D.tile i).carrier) ∪ (interior D.target.carrier)ᶜ
  have hUc : IsClosed U :=
    (Set.toFinite _).isClosed_biUnion fun i _ => (D.tile i).isCompact.isClosed
  have hWc : IsClosed W :=
    ((Set.toFinite _).isClosed_biUnion fun i _ => (D.tile i).isCompact.isClosed).union
      isOpen_interior.isClosed_compl
  have hcov : (D.vertexSet)ᶜ ⊆ U ∪ W := by
    intro x _
    by_cases hx : x ∈ interior D.target.carrier
    · have hx' : x ∈ ⋃ i, (D.tile i).carrier := by
        rw [D.covers]; exact interior_subset hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx'
      by_cases hg : good j
      · exact Or.inr (Or.inl (Set.mem_biUnion (x := j) hg hj))
      · exact Or.inl (Set.mem_biUnion (x := j) hg hj)
    · exact Or.inr (Or.inr hx)
  have hconn : IsPreconnected (D.vertexSet)ᶜ :=
    (D.vertexSet_finite.countable.isConnected_compl_of_one_lt_rank one_lt_rank).isPreconnected
  have hUne : ((D.vertexSet)ᶜ ∩ U).Nonempty := by
    have hns : ¬ (D.tile i).carrier ⊆ D.vertexSet := fun h =>
      (D.tile i).volume_pos.ne'
        (MeasureTheory.measure_mono_null h (D.vertexSet_finite.countable.measure_zero _))
    obtain ⟨x, hx, hxv⟩ := Set.not_subset.mp hns
    exact ⟨x, hxv, Set.mem_biUnion (x := i) hbad0 hx⟩
  have hWne : ((D.vertexSet)ᶜ ∩ W).Nonempty := by
    have hK : IsCompact (D.target.carrier ∪ D.vertexSet) :=
      D.target.isCompact.union D.vertexSet_finite.isCompact
    obtain ⟨x, hx⟩ : (D.target.carrier ∪ D.vertexSet)ᶜ.Nonempty := by
      rw [Set.nonempty_compl]
      intro h
      rw [h] at hK
      exact noncompact_univ Plane hK
    exact ⟨x, fun h => hx (Or.inr h), Or.inr fun hi => hx (Or.inl (interior_subset hi))⟩
  obtain ⟨x, hxv, hxU, hxW⟩ := isPreconnected_closed_iff.mp hconn U W hUc hWc hcov hUne hWne
  obtain ⟨i', hi', hxi⟩ := Set.mem_iUnion₂.mp hxU
  rcases hxW with hA | hB
  · obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hA
    have hij : i' ≠ j := fun h => hi' (h ▸ hj)
    obtain ⟨k, k', hkk⟩ := shared_point D.toDissection hij hxi hxj hxv
    have h1 := (hedge j k').mpr hj
    rw [hkk, Dir.angle_neg] at h1
    apply hi'
    rw [← hedge i' k]
    have := sub_mem h1 (pi_mem hn)
    convert this using 1
    abel
  · obtain ⟨k, j, hkj⟩ := boundary_point D.toDissection hxi hxv hB
    apply hi'
    rw [← hedge i' k, hkj]
    exact htgt j

/-- **Lemma 1 (a) (row0c §3.1(a)), on a real `CongruentDissection`.**  If the model's angles are
`a_k·π/n`, every tile edge direction lies in `θ₀ + (π/n)ℤ`, where `θ₀` is the direction of target
side 0 (its left-hand unit direction, i.e. `B − A` up to the sign absorbed by `π ∈ (π/n)ℤ`).
No edge-to-edge hypothesis, reflections allowed, no connectivity hypothesis. -/
theorem edge_dir_coset {N : ℕ} (D : CongruentDissection N) {n : ℕ} (hn : 0 < n)
    (a : Fin 3 → ℕ) (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) (i : Fin N) (k : Fin 3) :
    ((D.tile i).leftUnit k).angle - (D.target.leftUnit 0).angle ∈ H n :=
  (edge_iff hn (D.tile i) (tile_angles D a ha i) _ k).mpr (tile_dir_coset D hn a ha i)

/-- Joint witness: the real `CongruentDissection 2` of `CaseALemmaHPiFour` (n = 4, angles
(1,2,1)·π/4) satisfies every hypothesis. -/
theorem edge_dir_coset_witness (i : Fin 2) (k : Fin 3) :
    ((Erdos634.Draft.CaseALemmaHPiFour.dissection.tile i).leftUnit k).angle
      - (Erdos634.Draft.CaseALemmaHPiFour.dissection.target.leftUnit 0).angle ∈ H 4 :=
  edge_dir_coset _ (n := 4) (by norm_num) ![1, 2, 1]
    Erdos634.Draft.CaseALemmaVWitness.model_angles i k

end Erdos634.Geometry.A1Dir

#print axioms Erdos634.Geometry.A1Dir.edge_dir_coset
#print axioms Erdos634.Geometry.A1Dir.edge_dir_coset_witness
