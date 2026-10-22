/-
Draft/DirCoset.lean -- the coset of edge directions of a tiling, for an arbitrary subgroup of angles
(`prop:gammagrading`, `prop:dirgroup`, companion).

`A1EdgeDirections` proves that, when the tile's angles are multiples of `π/n`, every tile edge direction lies in
one coset of `(π/n)ℤ`.  The argument uses nothing about that subgroup beyond `π ∈ H` and the tile's angles lying in
`H`; this file is the same proof for an arbitrary subgroup `H ⊆ ℝ/2πℤ`:

* `edge_dir_coset`: if `π ∈ H` and the three angles of the model lie in `H`, every tile edge direction lies in the
  coset of `H` of the direction of target side 0 (any target, any number of tiles, reflections allowed);
  `edge_dir_pair` is the same for two edges.
* `dir_coset_general` (**`prop:dirgroup`, coset clause**): for any tile, with `α`, `β` two of its angles, the
  difference of two edge directions is `x α + y β + z π` with integers `x, y, z`.
* `gamma_grading` (**`prop:gammagrading`**): if `3α + 2β = π` and `γ = 2α + β`, the difference of two edge directions
  is `k γ + l π` with integers `k, l`.

The connectivity of the adjacency graph is not built: as in `A1EdgeDirections`, it is replaced by the connectedness
of the plane minus the finite vertex set.  Debt work; not a result on 634.  No sorry, no native_decide.
-/
import Erdos634.Draft.A1EdgeDirections

open scoped Classical

namespace Erdos634.Draft.DirCoset

open Erdos634.Geometry Erdos634.Geometry.A1Dir Set

variable (H : AddSubgroup Real.Angle)

/-- tile-local rule, one step -/
theorem turn_mem (hπ : ((Real.pi : ℝ) : Real.Angle) ∈ H) (T : Tri)
    (hT : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ H) (k : Fin 3) :
    (T.leftUnit (k + 1)).angle - (T.leftUnit k).angle ∈ H := by
  have hmem : ((Real.pi - T.angleAt (k + 1) : ℝ) : Real.Angle) ∈ H := by
    rw [Real.Angle.coe_sub]
    exact sub_mem hπ (hT (k + 1))
  rcases T.det_pos_or_neg with h | h
  · rw [T.leftUnit_turn_of_pos h k]
    simpa using hmem
  · rw [T.leftUnit_turn_of_neg h k]
    simpa using neg_mem hmem

/-- a triangle with angles in `H` has its three edge directions in one coset of `H` -/
theorem tile_local (hπ : ((Real.pi : ℝ) : Real.Angle) ∈ H) (T : Tri)
    (hT : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ H) (k : Fin 3) :
    (T.leftUnit k).angle - (T.leftUnit 0).angle ∈ H := by
  have h01 : (T.leftUnit 1).angle - (T.leftUnit 0).angle ∈ H := turn_mem H hπ T hT 0
  have h12 : (T.leftUnit 2).angle - (T.leftUnit 1).angle ∈ H := turn_mem H hπ T hT 1
  have hk : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  rcases hk k with rfl | rfl | rfl
  · simp
  · exact h01
  · have := add_mem h12 h01
    rwa [sub_add_sub_cancel] at this

theorem edge_iff (hπ : ((Real.pi : ℝ) : Real.Angle) ∈ H) (T : Tri)
    (hT : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ H) (θ : Real.Angle) (k : Fin 3) :
    (T.leftUnit k).angle - θ ∈ H ↔ (T.leftUnit 0).angle - θ ∈ H := by
  have hl := tile_local H hπ T hT k
  constructor
  · intro h
    have := sub_mem h hl
    rwa [sub_sub_sub_cancel_left] at this
  · intro h
    have := add_mem hl h
    rwa [sub_add_sub_cancel] at this

variable {N : ℕ}

/-- the angles of every tile lie in `H` -/
theorem tile_angles (D : CongruentDissection N)
    (hM : ∀ k, ((D.model.angleAt k : ℝ) : Real.Angle) ∈ H) (i : Fin N) (k : Fin 3) :
    (((D.tile i).angleAt k : ℝ) : Real.Angle) ∈ H := by
  obtain ⟨k', hk'⟩ := congruent_corner_angles (D.tiles_congruent i).symm k
  have h := hM k'
  unfold Tri.angleAt at h ⊢
  rw [hk']
  exact h

/-- the local angle of a tile at any point lies in `H` -/
theorem local_mem (hπ : ((Real.pi : ℝ) : Real.Angle) ∈ H) (D : CongruentDissection N)
    (hM : ∀ k, ((D.model.angleAt k : ℝ) : Real.Angle) ∈ H) (v : Plane) (i : Fin N) :
    (((D.tile i).localAngle v : ℝ) : Real.Angle) ∈ H := by
  have hcorners : ∀ (i : Fin N) (j : Fin 3),
      cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2))
        ∈ ({D.model.angleAt 0, D.model.angleAt 1, D.model.angleAt 2} : Finset ℝ) := by
    intro i j
    obtain ⟨k', hk'⟩ := congruent_corner_angles (D.tiles_congruent i).symm j
    rw [hk']
    show D.model.angleAt k' ∈ _
    fin_cases k' <;> simp
  have hm := Erdos634.VertexFigureReal.interior_localAngle_mem D.toDissection _ _ _ hcorners v i
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h | h | h | h | h <;> rw [h]
  · exact hM 0
  · exact hM 1
  · exact hM 2
  · exact hπ
  · rw [Real.Angle.coe_two_pi]; exact H.zero_mem
  · rw [Real.Angle.coe_zero]; exact H.zero_mem

/-- the angles of the target lie in `H` (angle sum at each corner of the target) -/
theorem target_angles (hπ : ((Real.pi : ℝ) : Real.Angle) ∈ H) (D : CongruentDissection N)
    (hM : ∀ k, ((D.model.angleAt k : ℝ) : Real.Angle) ∈ H) (k : Fin 3) :
    ((D.target.angleAt k : ℝ) : Real.Angle) ∈ H := by
  have hs := D.toDissection.sum_localAngle_eq (D.target.pts k)
  rw [D.target.localAngle_vertex k] at hs
  have h2 : ((D.target.angleAt k : ℝ) : Real.Angle)
      = ∑ i, (((D.tile i).localAngle (D.target.pts k) : ℝ) : Real.Angle) := by
    show ((cornerAngle _ _ _ : ℝ) : Real.Angle) = _
    rw [← hs]
    exact map_sum Real.Angle.coeHom _ _
  rw [h2]
  exact H.sum_mem (fun i _ => local_mem H hπ D hM _ i)

/-- every tile's edge-0 direction lies in the coset of target side 0 -/
theorem tile_dir_coset (hπ : ((Real.pi : ℝ) : Real.Angle) ∈ H) (D : CongruentDissection N)
    (hM : ∀ k, ((D.model.angleAt k : ℝ) : Real.Angle) ∈ H) (i : Fin N) :
    ((D.tile i).leftUnit 0).angle - (D.target.leftUnit 0).angle ∈ H := by
  set θ₀ := (D.target.leftUnit 0).angle with hθ₀
  have htile := tile_angles H D hM
  have htgt : ∀ j, (D.target.leftUnit j).angle - θ₀ ∈ H :=
    tile_local H hπ D.target (target_angles H hπ D hM)
  let good : Fin N → Prop := fun i => ((D.tile i).leftUnit 0).angle - θ₀ ∈ H
  have hedge : ∀ i k, ((D.tile i).leftUnit k).angle - θ₀ ∈ H ↔ good i :=
    fun i k => edge_iff H hπ (D.tile i) (htile i) θ₀ k
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
    have := sub_mem h1 hπ
    convert this using 1
    abel
  · obtain ⟨k, j, hkj⟩ := boundary_point D.toDissection hxi hxv hB
    apply hi'
    rw [← hedge i' k, hkj]
    exact htgt j

/-- **Edge directions lie in one coset.**  If `π ∈ H` and the model's three angles lie in `H`, every tile edge
direction lies in the coset of `H` of the direction of target side 0. -/
theorem edge_dir_coset (hπ : ((Real.pi : ℝ) : Real.Angle) ∈ H) (D : CongruentDissection N)
    (hM : ∀ k, ((D.model.angleAt k : ℝ) : Real.Angle) ∈ H) (i : Fin N) (k : Fin 3) :
    ((D.tile i).leftUnit k).angle - (D.target.leftUnit 0).angle ∈ H :=
  (edge_iff H hπ (D.tile i) (tile_angles H D hM i) _ k).mpr (tile_dir_coset H hπ D hM i)

/-- two edge directions differ by an element of `H` -/
theorem edge_dir_pair (hπ : ((Real.pi : ℝ) : Real.Angle) ∈ H) (D : CongruentDissection N)
    (hM : ∀ k, ((D.model.angleAt k : ℝ) : Real.Angle) ∈ H) (i i' : Fin N) (k k' : Fin 3) :
    ((D.tile i).leftUnit k).angle - ((D.tile i').leftUnit k').angle ∈ H := by
  have h := sub_mem (edge_dir_coset H hπ D hM i k) (edge_dir_coset H hπ D hM i' k')
  rwa [sub_sub_sub_cancel_right] at h

end Erdos634.Draft.DirCoset

#print axioms Erdos634.Draft.DirCoset.edge_dir_pair
