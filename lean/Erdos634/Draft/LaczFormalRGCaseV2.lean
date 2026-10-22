-- Draft/LaczFormalRGCaseV2.lean -- Laczkovich DCG 48 (2012), Theorem 2.1, Case V (gamma = pi/2), SUBCASE Va: the polygon is a rectangle and conclusion (i) holds
-- when `a` is not a nonnegative rational combination of `b, c` (Sect. 9.1).  Stated for `PolyTiling N 4` (a quadrilateral; that a convex polygon with all angles pi/2 has 4 vertices
-- needs the angle sum of a convex polygon, NOT done here).
-- UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 9, Lemma 4.1, Lemma 9.1), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRGIdx

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

theorem side_rect (P : ConvPoly 4) (hrect : P.v 0 + P.v 2 = P.v 1 + P.v 3) :
    P.side 2 = P.side 0 ∧ P.side 1 = P.side 3 := by
  constructor
  · unfold ConvPoly.side
    show dist (P.v 2) (P.v (2 + 1)) = dist (P.v 0) (P.v (0 + 1))
    have e1 : (2 : Fin 4) + 1 = 3 := by decide
    have e2 : (0 : Fin 4) + 1 = 1 := by decide
    rw [e1, e2, dist_eq_norm, dist_eq_norm]
    have : P.v 2 - P.v 3 = -(P.v 0 - P.v 1) := by
      have h := hrect
      calc P.v 2 - P.v 3 = (P.v 0 + P.v 2) - (P.v 0 + P.v 3) := by abel
        _ = (P.v 1 + P.v 3) - (P.v 0 + P.v 3) := by rw [h]
        _ = -(P.v 0 - P.v 1) := by abel
    rw [this, norm_neg]
  · unfold ConvPoly.side
    show dist (P.v 1) (P.v (1 + 1)) = dist (P.v 3) (P.v (3 + 1))
    have e1 : (1 : Fin 4) + 1 = 2 := by decide
    have e2 : (3 : Fin 4) + 1 = 0 := by decide
    rw [e1, e2, dist_eq_norm, dist_eq_norm]
    have : P.v 1 - P.v 2 = P.v 0 - P.v 3 := by
      have h := hrect
      calc P.v 1 - P.v 2 = (P.v 1 + P.v 3) - (P.v 2 + P.v 3) := by abel
        _ = (P.v 0 + P.v 2) - (P.v 2 + P.v 3) := by rw [h]
        _ = P.v 0 - P.v 3 := by abel
    rw [this, norm_sub_rev]

/-- **Case V, subcase Va.**  A regular tiling of a convex quadrilateral by congruent right triangles, `a` not a nonnegative rational combination of `b, c`: the quadrilateral is a rectangle and
the ratio of its sides is a rational multiple of `sin α / sin β`, i.e. conclusion (i) of Theorem 2.1. -/
theorem caseV_Va {N : ℕ} (T : PolyTiling N 4) (hreg : RegularPQ T.C) (hγ : angleAt T.C.model 2 = Real.pi / 2)
    (hnc : NotComb (slen T.C 0) (slen T.C 1) (slen T.C 2)) : Concl1 T.C T.P := by
  obtain ⟨idx, hA, hcnt⟩ := hreg
  have hidx := idx_dist_of_angle T.C idx hA
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hV : CaseV T.C idx := ⟨hidx, hA, hnc, hγ, fun X => hcnt X⟩
  have hang : ∀ i : Fin 4, T.P.angle i = Real.pi / 2 := by
    intro i
    have := (corner_arms T.C idx hV T.P T.region_eq (i - 1)).1
    rwa [sub_add_cancel] at this
  have hrect := rect_of_angles T.P hang
  obtain ⟨i, m, hm, hi⟩ := some_side_multiple T.C idx hV T.P T.region_eq
  obtain ⟨hs2, hs1⟩ := side_rect T.P hrect
  have hside : T.P.side 0 = m * sideOpp T.C.model 0 ∨ T.P.side 3 = m * sideOpp T.C.model 0 := by
    fin_cases i
    · exact Or.inl hi
    · right; rw [← hs1]; exact hi
    · left; rw [← hs2]; exact hi
    · exact Or.inr hi
  have hl := lemma41_poly T hrect (Or.inl (by rw [hang 0, hγ])) m hm hside
  refine ⟨⟨rfl, fun i => ?_⟩, ⟨0, by rw [hang 0, hγ]⟩, ?_⟩
  · fin_cases i
    · exact hrect
    · show T.P.v 1 + T.P.v (1 + 2) = T.P.v (1 + 1) + T.P.v (1 + 3)
      have e1 : (1 : Fin 4) + 2 = 3 := by decide
      have e2 : (1 : Fin 4) + 1 = 2 := by decide
      have e3 : (1 : Fin 4) + 3 = 0 := by decide
      rw [e1, e2, e3]; exact hrect.symm.trans (add_comm _ _)
    · show T.P.v 2 + T.P.v (2 + 2) = T.P.v (2 + 1) + T.P.v (2 + 3)
      have e1 : (2 : Fin 4) + 2 = 0 := by decide
      have e2 : (2 : Fin 4) + 1 = 3 := by decide
      have e3 : (2 : Fin 4) + 3 = 1 := by decide
      rw [e1, e2, e3]; exact (add_comm _ _).trans (hrect.trans (add_comm _ _))
    · show T.P.v 3 + T.P.v (3 + 2) = T.P.v (3 + 1) + T.P.v (3 + 3)
      have e1 : (3 : Fin 4) + 2 = 1 := by decide
      have e2 : (3 : Fin 4) + 1 = 0 := by decide
      have e3 : (3 : Fin 4) + 3 = 2 := by decide
      rw [e1, e2, e3]; exact (add_comm _ _).trans hrect.symm
  · rcases hl with ⟨q, hq⟩ | ⟨q, hq⟩
    · left; exact ⟨q, by rw [hs1]; exact hq⟩
    · right; exact ⟨q, by rw [hs1]; exact hq⟩

end Erdos634.Draft.LaczFormal.RG
