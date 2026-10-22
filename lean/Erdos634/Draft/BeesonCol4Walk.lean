-- Draft/BeesonCol4Walk.lean -- edge-level placement layer, part 1: the tiles with an edge on a line are the steps of the walk, in order, each once.
--   `walk_tail_param` (steps are ordered along the line), `walk_complete` (every left tile edge lying inside the walked segment IS a step of the walk;
--   uses `overlap_eq` and `tri_edges_par_eq`), `walk_tiles_nodup` (distinct steps have distinct tiles).
-- Reusable for Beeson (arXiv 1206.2229 v4) Lemma 31 Cases 1a-2 and Lemma 40 ("tiles with an edge on AB").  NOTE, UNAUDITED.
-- Credit: Beeson (arXiv 1206.2229 v4), Beeson-Rosu, Laczkovich (DCG 48 (2012), Sect. 4), Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.
import Erdos634.Draft.LaczFormalBZL7h1
import Erdos634.Draft.LaczFormalIVcRatBr5a

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

theorem vec_iff (A B : Plane) (c : ℝ) (d : V2) :
    toV2 (B - A) = (c * d.1, c * d.2) ↔ B 0 - A 0 = c * d.1 ∧ B 1 - A 1 = c * d.2 := by
  rw [toV2_sub, Prod.mk.injEq]

/-- Every step of a walk starts at `X + t d` with `t >= 0`: the steps are ordered along the line. -/
theorem walk_tail_param {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y L) : ∀ e ∈ L, ∃ t : ℝ, 0 ≤ t ∧ toV2 (e.2.1 - X) = (t * d.1, t * d.2) := by
  induction W with
  | nil X => intro e he; exact absurd he (by simp)
  | @cons i X X' Y L hS W ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | h
    · exact ⟨0, le_rfl, by rw [vec_iff]; simp⟩
    · obtain ⟨t, ht, hte⟩ := ih e h
      obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := id hS
      obtain ⟨c, hc, hcw⟩ := hpar.smul
      refine ⟨c + t, by positivity, ?_⟩
      rw [vec_iff] at hcw hte ⊢
      constructor <;> linarith [hcw.1, hcw.2, hte.1, hte.2]

/-- **Completeness of the walk.**  A tile with a left edge `A -> B` along `d`, lying inside the walked segment `X -> Y`
(`A = X + s d`, `B = A + c d`, `Y = B + u d`, `s, u >= 0 < c`) is a step of the walk: no tile edge on the line is missing from `L`. -/
theorem walk_complete {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y L) {j : Fin N} {A B : Plane} (hj : TriStep (D.tile j) d A B)
    {s c u : ℝ} (hd : d ≠ 0) (hs : 0 ≤ s) (hc : 0 < c) (hu : 0 ≤ u)
    (hA : toV2 (A - X) = (s * d.1, s * d.2)) (hAB : toV2 (B - A) = (c * d.1, c * d.2))
    (hBY : toV2 (Y - B) = (u * d.1, u * d.2)) : (j, A, B) ∈ L := by
  revert s hs hA hBY
  induction W with
  | nil X =>
    intro s hs hA hBY
    exfalso
    rw [vec_iff] at hA hAB hBY
    have h1 : (s + c + u) * d.1 = 0 := by linarith [hA.1, hAB.1, hBY.1]
    have h2 : (s + c + u) * d.2 = 0 := by linarith [hA.2, hAB.2, hBY.2]
    have hpos : s + c + u ≠ 0 := by positivity
    apply hd
    exact Prod.ext ((mul_eq_zero.mp h1).resolve_left hpos) ((mul_eq_zero.mp h2).resolve_left hpos)
  | @cons i X X' Y L hS W ih =>
    intro s hs hA hBY
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := id hS
    obtain ⟨c1, hc1, hcw⟩ := hpar.smul
    have hcw' : toV2 (X' - X) = (c1 * d.1, c1 * d.2) := by
      have := hcw
      rwa [show toV2 (X' - X) = _ from rfl] at this ⊢
    by_cases hlt : s < c1
    · have hji : j = i := overlap_eq D hj hS hc1 hc hs hlt hcw' hAB hA
      subst hji
      obtain ⟨hAX, hBX⟩ := tri_edges_par_eq (D.tile j) hj hS
      subst hAX hBX
      exact List.mem_cons_self ..
    · push Not at hlt
      refine List.mem_cons_of_mem _ (ih (s := s - c1) (by linarith) ?_ hBY)
      rw [vec_iff] at hA hcw' ⊢
      constructor <;> linarith [hA.1, hA.2, hcw'.1, hcw'.2]

/-- Distinct steps of a walk have distinct tiles. -/
theorem walk_tiles_nodup {D : RegionDissection N} {d : V2} {X Y : Plane} {L : List (Fin N × Plane × Plane)}
    (W : WalkT D d X Y L) : (L.map fun e => e.1).Nodup := by
  induction W with
  | nil X => simp
  | @cons i X X' Y L hS W ih =>
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih⟩
    intro hmem
    obtain ⟨e, he, hei⟩ := List.mem_map.mp hmem
    obtain ⟨t, ht, hte⟩ := walk_tail_param W e he
    have hSe := walkT_mem_step W e he
    rw [hei] at hSe
    obtain ⟨hU, -⟩ := tri_edges_par_eq (D.tile i) hS hSe
    obtain ⟨-, -, -, -, -, -, -, -, hpar, -⟩ := id hS
    obtain ⟨c1, hc1, hcw⟩ := hpar.smul
    have hdne : d ≠ 0 := hpar.ne_right
    rw [← hU] at hte
    rw [vec_iff] at hte
    have hcw2 := hcw
    have h1 : (c1 + t) * d.1 = 0 := by
      have := congrArg Prod.fst hcw2
      simp only [toV2_sub] at this
      linarith [hte.1]
    have h2 : (c1 + t) * d.2 = 0 := by
      have := congrArg Prod.snd hcw2
      simp only [toV2_sub] at this
      linarith [hte.2]
    have hpos : c1 + t ≠ 0 := by positivity
    exact hdne (Prod.ext ((mul_eq_zero.mp h1).resolve_left hpos) ((mul_eq_zero.mp h2).resolve_left hpos))

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.walk_complete
#print axioms Erdos634.Draft.LaczFormal.RG.walk_tiles_nodup
