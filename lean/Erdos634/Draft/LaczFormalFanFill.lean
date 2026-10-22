import Erdos634.Draft.LaczFormalFanVertex

/-!
# Filling a side fan with three tiles

Erdős #634, rule W2.  Credit: AI assistant (item 3, band program), Laczkovich (DCG 48 (2012), Sect. 4), Beeson–Roșu,
Beeson, Paliy.  UNAUDITED.

`fill_side`: at a vertex `V` of a side of the target whose tiles are exactly `s0, s1, u`, and whose cyclic fan is
exterior, `s0`, `s1`, `u`: if `s0` starts along the boundary ray, `s1` starts where `s0` ends, and the exterior
sector does not start where `s1` ends, then `u` starts where `s1` ends and the exterior sector starts where `u` ends.
-/

namespace Erdos634.Draft.LaczFormal.Graph

open Erdos634.Geometry

variable {N : ℕ}

namespace ExtFan

variable {D : Dissection N} {V : Plane}

theorem fill_side (F : ExtFan D V Unit) {s0 s1 u : AtV D V}
    (hall : ∀ x : AtV D V, x = s0 ∨ x = s1 ∨ x = u) (h0u : s0 ≠ u) (h1u : s1 ≠ u)
    (hstart : Par (F.p s0) (F.qe ())) (h10 : Par (F.p s1) (F.q s0)) (hnot : ¬ Par (F.pe ()) (F.q s1)) :
    Par (F.p u) (F.q s1) ∧ Par (F.pe ()) (F.q u) := by
  obtain ⟨x, hx⟩ := F.succ_exists (Sum.inl s1)
  have hxu : x = Sum.inl u := by
    rcases x with y | j
    · rcases hall y with rfl | rfl | rfl
      · exfalso
        have := F.pred_unique (o := Sum.inl y) (o1 := Sum.inl s1) (o2 := Sum.inr ()) hx hstart
        exact absurd this Sum.inl_ne_inr
      · exact absurd hx (F.succ_ne_self _)
      · rfl
    · exfalso
      rw [show j = () from Subsingleton.elim _ _] at hx
      exact hnot hx
  subst hxu
  refine ⟨hx, ?_⟩
  obtain ⟨z, hz⟩ := F.succ_exists (Sum.inl u)
  rcases z with y | j
  · exfalso
    rcases hall y with rfl | rfl | rfl
    · have := F.pred_unique (o := Sum.inl y) (o1 := Sum.inl u) (o2 := Sum.inr ()) hz hstart
      exact absurd this Sum.inl_ne_inr
    · have := F.pred_unique (o := Sum.inl y) (o1 := Sum.inl u) (o2 := Sum.inl s0) hz h10
      exact h0u (Sum.inl_injective this).symm
    · exact absurd hz (F.succ_ne_self _)
  · rw [show j = () from Subsingleton.elim _ _] at hz
    exact hz

end ExtFan

end Erdos634.Draft.LaczFormal.Graph
