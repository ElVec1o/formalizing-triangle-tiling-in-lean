import Erdos634.Draft.BeesonColoringConnEdge
import Erdos634.Draft.BeesonColoringConnTopo
import Erdos634.Draft.BeesonColoringLemma12U

/-!
# Beeson (arXiv 1206.2229v4) Lemma 12: the tile-adjacency graph of EVERY dissection of a triangle is connected,
# hence the colouring is unique up to swapping colours, unconditionally

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Lemma 12), Laczkovich (DCG 48 (2012)), Beeson-Zhang.

Closes the GAP named in `BeesonColoringLemma12U`.  Route (differs from the printed path-parity proof):
`BeesonColoringConnEdge.inter_finite_of_not_adj` (non-adjacent distinct tiles meet in a finite set; pigeonhole on edge
pairs), `BeesonColoringConnTopo.no_split` (a convex body is not a union of two closed sets meeting in a finite set unless
one contains the other), positive area of a tile.  The two closed sets are the unions of the tiles in the adjacency
component of tile `i` and of the other tiles.
-/

open scoped Classical

namespace Erdos634.Geometry

open MeasureTheory Set

variable {N : ℕ}

theorem Dissection.adjConnected (D : Dissection N) : D.AdjConnected := by
  intro i j
  by_contra hij
  set A : Set (Fin N) := {a | Relation.ReflTransGen (fun a b => D.Adj a b) i a} with hA
  set UA : Set Plane := ⋃ a ∈ A, (D.tile a).carrier with hUA
  set UB : Set Plane := ⋃ b ∈ Aᶜ, (D.tile b).carrier with hUB
  have hiA : i ∈ A := Relation.ReflTransGen.refl
  have hjA : j ∈ Aᶜ := hij
  have hU : UA ∪ UB = D.target.carrier := by
    rw [← D.covers]
    ext x
    simp only [hUA, hUB, mem_union, mem_iUnion, exists_prop]
    constructor
    · rintro (⟨a, _, h⟩ | ⟨a, _, h⟩) <;> exact ⟨a, h⟩
    · rintro ⟨a, h⟩
      by_cases ha : a ∈ A
      · exact Or.inl ⟨a, ha, h⟩
      · exact Or.inr ⟨a, ha, h⟩
  have hclA : IsClosed UA :=
    Set.Finite.isClosed_biUnion (Set.toFinite _) fun a _ => (D.tile a).isCompact.isClosed
  have hclB : IsClosed UB :=
    Set.Finite.isClosed_biUnion (Set.toFinite _) fun a _ => (D.tile a).isCompact.isClosed
  have hF : (UA ∩ UB).Finite := by
    have hfin : (⋃ a ∈ A, ⋃ b ∈ Aᶜ, ((D.tile a).carrier ∩ (D.tile b).carrier)).Finite := by
      refine Set.Finite.biUnion (Set.toFinite _) fun a ha => Set.Finite.biUnion (Set.toFinite _) fun b hb => ?_
      have hab : a ≠ b := fun h => hb (h ▸ ha)
      refine D.inter_finite_of_not_adj hab fun hadj => hb ?_
      exact Relation.ReflTransGen.tail ha hadj
    refine hfin.subset ?_
    rintro x ⟨hxA, hxB⟩
    simp only [hUA, hUB, mem_iUnion, exists_prop] at hxA hxB
    obtain ⟨a, ha, hxa⟩ := hxA
    obtain ⟨b, hb, hxb⟩ := hxB
    simp only [mem_iUnion, exists_prop]
    exact ⟨a, ha, b, hb, hxa, hxb⟩
  have hnull : ∀ k : Fin N, (D.tile k).carrier ⊆ UA ∩ UB → False := by
    intro k hk
    have h0 : volume (UA ∩ UB) = 0 := hF.measure_zero volume
    have := measure_mono_null hk h0
    exact (D.tile k).volume_pos.ne' this
  rcases no_split D.target.convex D.target.interior_nonempty hclA hclB hU hF with h | h
  · refine hnull i fun x hx => ?_
    have hxA : x ∈ UA := mem_biUnion hiA hx
    exact ⟨hxA, h hxA⟩
  · refine hnull j fun x hx => ?_
    have hxB : x ∈ UB := mem_biUnion hjA hx
    exact ⟨h hxB, hxB⟩

/-- **Beeson Lemma 12, uniqueness, unconditional**: two proper 2-colourings of any dissection of a triangle agree or are
opposite. -/
theorem Dissection.colouring_unique' (D : Dissection N) {ε ε' : Fin N → ℤ}
    (h : D.ProperColouring ε) (h' : D.ProperColouring ε') :
    ε' = ε ∨ ε' = fun i => - ε i :=
  Dissection.colouring_unique D.adjConnected h h'

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Dissection.adjConnected
#print axioms Erdos634.Geometry.Dissection.colouring_unique'
