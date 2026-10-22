import Erdos634.Draft.BeesonColoringLemma12

/-!
# Beeson (arXiv 1206.2229v4) Lemma 12: uniqueness of the colouring up to swapping colours (conditional on connectivity)

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Lemma 12), Laczkovich (DCG 48 (2012)), Beeson-Zhang.

Two proper 2-colourings (`Dissection.ProperColouring`) of a dissection whose tile-adjacency graph is connected
(`Dissection.AdjConnected`) agree or are opposite.  GAP, named and NOT closed here: that the adjacency graph of EVERY
dissection of a triangle is connected (a planar-topology fact: tiles meeting only in points, convex region minus a finite
set is connected; needs the characterisation "two disjoint-interior triangles meeting in two points share part of an
edge").  Hypothesis non-vacuous: `adjConnected_of_subsingleton` (`N <= 1`).  The printed path-parity proof of Lemma 12 is not
attempted (the flux route of `flux_colouring` is used instead).
-/

namespace Erdos634.Geometry

variable {N : ℕ}

/-- the tile-adjacency graph is connected -/
def Dissection.AdjConnected (D : Dissection N) : Prop :=
  ∀ i j : Fin N, Relation.ReflTransGen (fun a b => D.Adj a b) i j

theorem adjConnected_of_subsingleton (D : Dissection N) (hN : N ≤ 1) : D.AdjConnected := by
  intro i j
  have : i = j := by ext; omega
  subst this; exact Relation.ReflTransGen.refl

theorem Dissection.colouring_unique {D : Dissection N} (hc : D.AdjConnected) {ε ε' : Fin N → ℤ}
    (h : D.ProperColouring ε) (h' : D.ProperColouring ε') :
    ε' = ε ∨ ε' = fun i => - ε i := by
  have key : ∀ i j, ε' i * ε i = ε' j * ε j := by
    intro i j
    induction hc i j with
    | refl => rfl
    | @tail b c _ hstep ih =>
      have e1 := h.2 b c hstep
      have e2 := h'.2 b c hstep
      rw [ih, e1, e2]; ring
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; left; funext i; exact i.elim0
  · let i0 : Fin N := ⟨0, hN⟩
    have hp : ∀ i, ε' i * ε i = ε' i0 * ε i0 := fun i => key i i0
    rcases h.1 i0 with a | a <;> rcases h'.1 i0 with b | b
    · left; funext i; have := hp i; rw [a, b] at this
      rcases h.1 i with c | c <;> rcases h'.1 i with d | d <;> simp_all
    · right; funext i; have := hp i; rw [a, b] at this
      rcases h.1 i with c | c <;> rcases h'.1 i with d | d <;> simp_all
    · right; funext i; have := hp i; rw [a, b] at this
      rcases h.1 i with c | c <;> rcases h'.1 i with d | d <;> simp_all
    · left; funext i; have := hp i; rw [a, b] at this
      rcases h.1 i with c | c <;> rcases h'.1 i with d | d <;> simp_all

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Dissection.colouring_unique
