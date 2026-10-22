-- Draft/LaczFormalCombi4a.lean -- the geometric wiring behind Laczkovich, DCG 48 (2012), Lemma 3.8 ("the sides of A are x cos a + y sin a + z"):
-- for ANY `PolyTiling` (any congruent dissection of a convex polygon, reflections allowed, not edge-to-edge) every side of the polygon has length
-- `x a + y b + z c` with `x, y, z` natural numbers and `a, b, c` the three side lengths of the model triangle.  Proof: the side is a chain of
-- tile edges (`edge_data`, `walkT_dist_sum`), each of which is a side of a tile congruent to the model.
-- NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Comput. Geom. 48 (2012), Lemma 3.8; Combinatorica 10 (1990)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormal32e1
import Erdos634.Draft.LaczFormalRGCaseVc2

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement
open Erdos634.Draft.LaczFormal.RG

namespace Erdos634.Laczkovich.Combi4

variable {N M : ℕ} [NeZero M]

/-- A side of a tile congruent to the model has one of the model's three side lengths. -/
theorem tile_dist_mem (C : CongruentRegionDissection N) (i : Fin N) {k k' : Fin 3} (h : k ≠ k') :
    dist ((C.tile i).pts k) ((C.tile i).pts k') = sideOpp C.model 0 ∨
    dist ((C.tile i).pts k) ((C.tile i).pts k') = sideOpp C.model 1 ∨
    dist ((C.tile i).pts k) ((C.tile i).pts k') = sideOpp C.model 2 := by
  obtain ⟨σ, hσ⟩ := (C.tiles_congruent i).dist_eq
  rw [hσ k k']
  have hne : σ k ≠ σ k' := fun he => h (σ.injective he)
  generalize σ k = j at hne ⊢
  generalize σ k' = j' at hne ⊢
  fin_cases j <;> fin_cases j' <;> simp [sideOpp] at hne ⊢
  all_goals first
    | (left; rfl) | (left; exact dist_comm (C.model.pts _) (C.model.pts _)) | (right; left; rfl) | (right; left; exact dist_comm (C.model.pts _) (C.model.pts _))
    | (right; right; rfl) | (right; right; exact dist_comm (C.model.pts _) (C.model.pts _))

theorem list_sum_comb (l : List ℝ) (a b c : ℝ) (h : ∀ x ∈ l, x = a ∨ x = b ∨ x = c) :
    ∃ x y z : ℕ, l.sum = x * a + y * b + z * c := by
  induction l with
  | nil => exact ⟨0, 0, 0, by simp⟩
  | cons t l ih =>
    obtain ⟨x, y, z, hs⟩ := ih (fun u hu => h u (List.mem_cons_of_mem _ hu))
    rcases h t (List.mem_cons_self) with rfl | rfl | rfl
    · exact ⟨x + 1, y, z, by simp [hs]; ring⟩
    · exact ⟨x, y + 1, z, by simp [hs]; ring⟩
    · exact ⟨x, y, z + 1, by simp [hs]; ring⟩

/-- **Every side of a tiled convex polygon is a nonnegative integer combination of the three side lengths of the tile.** -/
theorem side_comb (T : PolyTiling N M) (i : Fin M) :
    ∃ x y z : ℕ, T.P.side i = x * sideOpp T.C.model 0 + y * sideOpp T.C.model 1 + z * sideOpp T.C.model 2 := by
  classical
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  obtain ⟨L, e0, el, W, -, -, -, -, -, -⟩ := edge_data T.C T.P T.region_eq i
  have hsum := walkT_dist_sum W
  have hmem := walkT_mem_step W
  have hside : T.P.side i = dist (T.P.v i) (T.P.v (i + 1)) := rfl
  rw [hside, ← hsum]
  refine list_sum_comb _ _ _ _ ?_
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  obtain ⟨kk, f, g, hk, hf, hfk, -⟩ := hmem e he
  rw [← hk, ← hf]
  exact tile_dist_mem T.C e.1 hfk.symm

end Erdos634.Laczkovich.Combi4

#print axioms Erdos634.Laczkovich.Combi4.side_comb
