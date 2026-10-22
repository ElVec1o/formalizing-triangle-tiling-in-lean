-- Draft/H1fNG.lean — ATOM H1.f (SCOPE_H1_full.md §3(a), §6): the neighbour graph of a dissection
-- is connected.  Self-contained, standard axioms, no sorry.  Formalization debt; NOT /goal progress.
--
--   `nbrGraph D`  : tiles i ≠ j are adjacent iff their carriers share a segment of positive length.
--   `nbrGraph_connected D` : this graph is connected (for any `Dissection N`).
--
-- Proof (the paper's): split the tiles into the class A of a base tile and its complement B.  The
-- two unions are closed, cover the (convex) target, and meet in a FINITE set F (each pairwise
-- intersection tile_i ∩ tile_j is convex with no segment, hence a subsingleton).  Pick a in the
-- interior of a base tile and b in the interior of a B-tile; a "pencil" point z of the target,
-- outside the finitely many lines (a,f), (b,f), f ∈ F, joins them by two segments avoiding F; a
-- connected subset of A∪B missing A∩B cannot meet both closed pieces.
import Erdos634.Dissection
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open MeasureTheory Set

namespace Erdos634.H1fNG

open Erdos634.Geometry

/-- The zero set of an affine functional `z ↦ cross u (z - a)` (`u ≠ 0`) is a null line. -/
theorem volume_cross_zero (u a : Plane) (hu : u ≠ 0) :
    volume {z : Plane | cross u (z - a) = 0} = 0 := by
  have h1 : {z : Plane | cross u (z - a) = 0} =
      (fun z => z + (-a)) ⁻¹' (LinearMap.ker (crossL u) : Set Plane) := by
    ext z; simp [sub_eq_add_neg]
  rw [h1, measure_preimage_add_right]
  refine Measure.addHaar_submodule volume _ ?_
  intro h
  exact crossL_ne_zero hu (LinearMap.ker_eq_top.mp h)

/-- A point on the segment `[a,z]` is on the line through `a` and `z`. -/
theorem cross_zero_of_mem_segment {a z f : Plane} (h : f ∈ segment ℝ a z) :
    cross (f - a) (z - a) = 0 := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := h
  have : s = 1 - t := by linarith
  subst this
  simp only [cross, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- **Pencil lemma.**  In a set of positive area there is a point `z` off all the finitely many
lines `(a,f)` and `(b,f)`, `f ∈ F`  (a, b ∉ F). -/
theorem exists_pencil_point (S : Set Plane) (hS : 0 < volume S) (F : Set Plane) (hF : F.Finite)
    (a b : Plane) (ha : a ∉ F) (hb : b ∉ F) :
    ∃ z ∈ S, ∀ f ∈ F, cross (f - a) (z - a) ≠ 0 ∧ cross (f - b) (z - b) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hsub : S ⊆ ⋃ f ∈ F, ({z | cross (f - a) (z - a) = 0} ∪ {z | cross (f - b) (z - b) = 0}) := by
    intro z hz
    obtain ⟨f, hf, h⟩ := hcon z hz
    simp only [mem_iUnion]
    refine ⟨f, hf, ?_⟩
    by_cases h1 : cross (f - a) (z - a) = 0
    · exact Or.inl h1
    · exact Or.inr (h h1)
  have hnull : volume (⋃ f ∈ F, ({z | cross (f - a) (z - a) = 0} ∪
      {z | cross (f - b) (z - b) = 0})) = 0 := by
    rw [measure_biUnion_null_iff hF.countable]
    intro f hf
    refine measure_union_null (volume_cross_zero _ _ ?_) (volume_cross_zero _ _ ?_)
    · intro h; exact ha ((sub_eq_zero.mp h) ▸ hf)
    · intro h; exact hb ((sub_eq_zero.mp h) ▸ hf)
  exact hS.ne' (measure_mono_null hsub hnull)

namespace Dissection'

variable {N : ℕ}

/-- A point of the interior of one tile lies in no other tile (carriers are the closures of their
interiors). -/
theorem not_mem_of_mem_interior (D : Dissection N) {i j : Fin N} (hij : i ≠ j) {x : Plane}
    (hx : x ∈ interior (D.tile i).carrier) : x ∉ (D.tile j).carrier := by
  intro hxj
  have hcl : closure (interior (D.tile j).carrier) = (D.tile j).carrier := by
    rw [(D.tile j).convex.closure_interior_eq_closure_of_nonempty_interior
      (D.tile j).interior_nonempty, (D.tile j).isCompact.isClosed.closure_eq]
  rw [← hcl, mem_closure_iff] at hxj
  obtain ⟨y, hy1, hy2⟩ := hxj _ isOpen_interior hx
  exact Set.disjoint_left.mp (D.interiors_disjoint hij) hy1 hy2

end Dissection'

open Dissection' in
/-- **The neighbour graph.**  Distinct tiles are adjacent iff they share a segment of positive
length. -/
def nbrGraph {N : ℕ} (D : Dissection N) : SimpleGraph (Fin N) where
  Adj i j := i ≠ j ∧ ∃ x y : Plane, x ≠ y ∧ segment ℝ x y ⊆ (D.tile i).carrier ∩ (D.tile j).carrier
  symm := fun i j ⟨h, x, y, hxy, hs⟩ => ⟨h.symm, x, y, hxy, by rwa [inter_comm]⟩
  loopless := ⟨fun i h => h.1 rfl⟩

/-- **NG.**  The neighbour graph of a dissection is connected. -/
theorem nbrGraph_preconnected {N : ℕ} (D : Dissection N) : (nbrGraph D).Preconnected := by
  classical
  intro i0 j0
  by_contra hj0
  set G := nbrGraph D with hG
  set A : Set (Fin N) := {i | G.Reachable i0 i} with hA
  have hi0 : i0 ∈ A := SimpleGraph.Reachable.refl _
  have hj0' : j0 ∈ Aᶜ := hj0
  set UA : Set Plane := ⋃ i ∈ A, (D.tile i).carrier with hUA
  set UB : Set Plane := ⋃ i ∈ Aᶜ, (D.tile i).carrier with hUB
  have hclA : IsClosed UA :=
    (Set.toFinite A).isClosed_biUnion fun i _ => (D.tile i).isCompact.isClosed
  have hclB : IsClosed UB :=
    (Set.toFinite Aᶜ).isClosed_biUnion fun i _ => (D.tile i).isCompact.isClosed
  -- pairwise intersections across the cut are subsingletons
  have hsing : ∀ i ∈ A, ∀ j ∈ Aᶜ, ((D.tile i).carrier ∩ (D.tile j).carrier).Subsingleton := by
    intro i hi j hj x hx y hy
    by_contra hxy
    have hseg : segment ℝ x y ⊆ (D.tile i).carrier ∩ (D.tile j).carrier :=
      ((D.tile i).convex.inter (D.tile j).convex).segment_subset hx hy
    have hadj : G.Adj i j := by
      refine ⟨?_, x, y, hxy, hseg⟩
      rintro rfl; exact hj hi
    exact hj (hi.trans hadj.reachable)
  set F : Set Plane := ⋃ i ∈ A, ⋃ j ∈ Aᶜ, ((D.tile i).carrier ∩ (D.tile j).carrier) with hF
  have hFfin : F.Finite :=
    (Set.toFinite A).biUnion fun i hi => (Set.toFinite Aᶜ).biUnion fun j hj =>
      (hsing i hi j hj).finite
  have hUAB : UA ∩ UB ⊆ F := by
    rintro x ⟨hxA, hxB⟩
    simp only [hUA, hUB, mem_iUnion] at hxA hxB
    obtain ⟨i, hi, hxi⟩ := hxA
    obtain ⟨j, hj, hxj⟩ := hxB
    simp only [hF, mem_iUnion]
    exact ⟨i, hi, j, hj, hxi, hxj⟩
  -- base points
  obtain ⟨a, ha⟩ := (D.tile i0).interior_nonempty
  obtain ⟨b, hb⟩ := (D.tile j0).interior_nonempty
  have haA : a ∈ UA := by
    simp only [hUA, mem_iUnion]; exact ⟨i0, hi0, interior_subset ha⟩
  have hbB : b ∈ UB := by
    simp only [hUB, mem_iUnion]; exact ⟨j0, hj0', interior_subset hb⟩
  have haF : a ∉ F := by
    intro h
    simp only [hF, mem_iUnion] at h
    obtain ⟨i, hi, j, hj, _, haj⟩ := h
    refine Dissection'.not_mem_of_mem_interior D ?_ ha haj
    rintro rfl; exact hj hi0
  have hbF : b ∉ F := by
    intro h
    simp only [hF, mem_iUnion] at h
    obtain ⟨i, hi, j, hj, hbi, _⟩ := h
    refine Dissection'.not_mem_of_mem_interior D ?_ hb hbi
    rintro rfl; exact hj0' hi
  have haT : a ∈ D.target.carrier := tile_subset_target D i0 (interior_subset ha)
  have hbT : b ∈ D.target.carrier := tile_subset_target D j0 (interior_subset hb)
  obtain ⟨z, hzT, hz⟩ := exists_pencil_point D.target.carrier D.target.volume_pos F hFfin a b haF hbF
  have hseg1 : segment ℝ a z ⊆ D.target.carrier := D.target.convex.segment_subset haT hzT
  have hseg2 : segment ℝ z b ⊆ D.target.carrier :=
    D.target.convex.segment_subset hzT hbT
  have hav1 : ∀ f ∈ F, f ∉ segment ℝ a z := fun f hf h =>
    (hz f hf).1 (cross_zero_of_mem_segment h)
  have hav2 : ∀ f ∈ F, f ∉ segment ℝ z b := fun f hf h => by
    rw [segment_symm] at h
    exact (hz f hf).2 (cross_zero_of_mem_segment h)
  have hW : IsPreconnected (segment ℝ a z ∪ segment ℝ z b) :=
    IsPreconnected.union z (right_mem_segment ℝ a z) (left_mem_segment ℝ z b)
      (convex_segment a z).isPreconnected (convex_segment z b).isPreconnected
  have hcover : segment ℝ a z ∪ segment ℝ z b ⊆ UA ∪ UB := by
    intro x hx
    have hxT : x ∈ D.target.carrier := by
      rcases hx with hx | hx
      · exact hseg1 hx
      · exact hseg2 hx
    rw [← D.covers] at hxT
    simp only [mem_iUnion] at hxT
    obtain ⟨i, hxi⟩ := hxT
    by_cases hi : i ∈ A
    · left; simp only [hUA, mem_iUnion]; exact ⟨i, hi, hxi⟩
    · right; simp only [hUB, mem_iUnion]; exact ⟨i, hi, hxi⟩
  obtain ⟨x, hxW, hxA, hxB⟩ := isPreconnected_closed_iff.1 hW UA UB hclA hclB hcover
    ⟨a, Or.inl (left_mem_segment ℝ a z), haA⟩ ⟨b, Or.inr (right_mem_segment ℝ z b), hbB⟩
  have hxF := hUAB ⟨hxA, hxB⟩
  rcases hxW with hx | hx
  · exact hav1 x hxF hx
  · exact hav2 x hxF hx

/-- **NG (connected form).** -/
theorem nbrGraph_connected {N : ℕ} (D : Dissection N) : (nbrGraph D).Connected :=
  haveI : Nonempty (Fin N) := ⟨⟨0, D.pos⟩⟩
  ⟨nbrGraph_preconnected D⟩

end Erdos634.H1fNG
