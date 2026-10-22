import Erdos634.BaseSelection
import Erdos634.Draft.BeesonColoringLemma12

/-!
# Beeson (arXiv 1206.2229v4) Lemma 12, connectivity, part 1: two non-adjacent tiles meet in a finite set

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Lemma 12), Laczkovich (DCG 48 (2012)), Beeson-Zhang.

* `Tri.edge_of_not_interior`: a point of a tile that is not interior lies on an edge.
* `Dissection.mem_edges_of_inter`: a common point of two distinct tiles lies on an edge of each (it is interior to neither:
  a point interior to one and in the other, which is the closure of its interior, would give a common interior point).
* `Dissection.inter_finite_of_not_adj`: two distinct tiles that are not adjacent meet in a finite set (pigeonhole on the
  nine pairs of edges: ten distinct common points give two on the same edge of each tile, i.e. `Adj`).
-/

open scoped Classical

namespace Erdos634.Geometry

open Set

variable {N : ℕ}

theorem Tri.edge_of_not_interior (T : Tri) {x : Plane} (hx : x ∈ T.carrier)
    (hn : x ∉ interior T.carrier) : ∃ k : Fin 3, x ∈ T.edge k := by
  have hnn : ∀ j, 0 ≤ T.basis.coord j x := by
    have h : x ∈ T.carrier := hx
    rw [T.carrier_eq_nonneg_coord] at h
    exact h
  by_cases hpos : ∀ j, 0 < T.basis.coord j x
  · exfalso
    obtain ⟨r, hr, hsub⟩ := T.ball_subset_of_pos hpos
    exact hn (mem_interior.mpr ⟨Metric.ball x r, hsub, Metric.isOpen_ball, Metric.mem_ball_self hr⟩)
  · push_neg at hpos
    obtain ⟨k, hk⟩ := hpos
    have h0 : T.basis.coord k x = 0 := le_antisymm hk (hnn k)
    refine ⟨k + 1, ?_⟩
    rw [Tri.edge, show k + 1 + 1 = k + 2 from by omega]
    exact Erdos634.BaseSelection.coord_zero_mem_segment T k x h0 hnn

theorem Tri.closure_interior_eq (T : Tri) : closure (interior T.carrier) = T.carrier := by
  rw [T.convex.closure_interior_eq_closure_of_nonempty_interior T.interior_nonempty]
  exact T.isCompact.isClosed.closure_eq

theorem Dissection.not_mem_interior_of_inter (D : Dissection N) {i j : Fin N} (hij : i ≠ j) {x : Plane}
    (hxi : x ∈ (D.tile i).carrier) (hxj : x ∈ (D.tile j).carrier) :
    x ∉ interior (D.tile i).carrier := by
  intro hint
  have hcl : x ∈ closure (interior (D.tile j).carrier) := by
    rw [(D.tile j).closure_interior_eq]; exact hxj
  obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.mp hcl _ isOpen_interior hint
  exact Set.disjoint_left.mp (D.interiors_disjoint hij) hy1 hy2

theorem Dissection.mem_edges_of_inter (D : Dissection N) {i j : Fin N} (hij : i ≠ j) {x : Plane}
    (hxi : x ∈ (D.tile i).carrier) (hxj : x ∈ (D.tile j).carrier) :
    (∃ k, x ∈ (D.tile i).edge k) ∧ ∃ l, x ∈ (D.tile j).edge l :=
  ⟨(D.tile i).edge_of_not_interior hxi (D.not_mem_interior_of_inter hij hxi hxj),
   (D.tile j).edge_of_not_interior hxj (D.not_mem_interior_of_inter hij.symm hxj hxi)⟩

theorem Dissection.inter_finite_of_not_adj (D : Dissection N) {i j : Fin N} (hij : i ≠ j)
    (hna : ¬ D.Adj i j) : ((D.tile i).carrier ∩ (D.tile j).carrier).Finite := by
  by_contra hinf
  have hinf' : ((D.tile i).carrier ∩ (D.tile j).carrier).Infinite := hinf
  obtain ⟨s, hs, hcard⟩ := hinf'.exists_subset_card_eq 10
  let f : Plane → Fin 3 × Fin 3 := fun x =>
    if h : x ∈ (D.tile i).carrier ∩ (D.tile j).carrier then
      ((D.mem_edges_of_inter hij h.1 h.2).1.choose, (D.mem_edges_of_inter hij h.1 h.2).2.choose)
    else (0, 0)
  have hmaps : ∀ x ∈ s, f x ∈ (Finset.univ : Finset (Fin 3 × Fin 3)) := fun x _ => Finset.mem_univ _
  have hlt : (Finset.univ : Finset (Fin 3 × Fin 3)).card < s.card := by
    rw [hcard]; simp
  obtain ⟨p, hp, q, hq, hpq, hfe⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  have hpm : p ∈ (D.tile i).carrier ∩ (D.tile j).carrier := hs hp
  have hqm : q ∈ (D.tile i).carrier ∩ (D.tile j).carrier := hs hq
  simp only [f, dif_pos hpm, dif_pos hqm, Prod.mk.injEq] at hfe
  obtain ⟨hk, hl⟩ := hfe
  apply hna
  refine ⟨hij, (D.mem_edges_of_inter hij hpm.1 hpm.2).1.choose, (D.mem_edges_of_inter hij hpm.1 hpm.2).2.choose,
    p, q, hpq, (D.mem_edges_of_inter hij hpm.1 hpm.2).1.choose_spec, ?_,
    (D.mem_edges_of_inter hij hpm.1 hpm.2).2.choose_spec, ?_⟩
  · rw [hk]; exact (D.mem_edges_of_inter hij hqm.1 hqm.2).1.choose_spec
  · rw [hl]; exact (D.mem_edges_of_inter hij hqm.1 hqm.2).2.choose_spec

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Dissection.inter_finite_of_not_adj
