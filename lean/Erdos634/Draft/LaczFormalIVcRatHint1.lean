-- Draft/LaczFormalIVcRatHint1.lean -- WITNESS FOR THE `hint` BRANCH of `ivc_rat_final` (Laczkovich DCG 48 (2012), Sect. 8.3, Concl9 / Thm 2.1 (ix)).
--   Audit gap G1 (AUDIT_UNAUDITED_2026-10-22b/item1): "the hint branch has no witness at M >= 5".  Resolution: the hint branch is NONEMPTY, and `rhexT`
--   (Wit3) is already in it.  In `rhexT` the tile is (1, 2, sqrt 3) with c = slen 2 = sqrt 3, while all six hexagon sides have length 2 (hypotenuse), NOT c.
--   So the all-c branch of `hint_or_allc` is impossible (a side of length 2 cannot be a sum of k edges of length sqrt 3), hence `hint_or_allc` returns `hint`
--   (every c-length tile step has an interior open-segment point), and `ivc_rat_final` runs through the branch `hint` -> BrHyp -> no pi/3 corner -> M = 6.
--   (The comment "all six sides = c = 2" in Wit3's audit notes is a mislabel: c = sqrt 3.)
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatWit4
import Erdos634.Draft.LaczFormalIVcRatBr8a

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

theorem rhexT_slen2 : slen rhexT.C 2 = Real.sqrt 3 := rT_slen2

/-- k * sqrt 3 is never 2. -/
theorem nat_mul_sqrt3_ne_two (k : ℕ) : (k : ℝ) * Real.sqrt 3 ≠ 2 := by
  intro h
  have h3 : (k : ℝ) ^ 2 * 3 = 4 := by
    have := congrArg (fun x => x ^ 2) h
    simp only [mul_pow, Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)] at this
    linarith
  have h4 : k ^ 2 * 3 = 4 := by exact_mod_cast h3
  have hk : k ≤ 2 := by nlinarith
  interval_cases k <;> omega

/-- The all-`c` branch of `hint_or_allc` is empty for `rhexT`. -/
theorem rhexT_not_allc :
    ¬ ∃ L : Fin 6 → List (Fin (2 + 2 + 2 + 2 + 2 + 2) × Plane × Plane),
      (∀ i, WalkT rhexT.C.toRegionDissection (toV2 (rhexT.P.e i)) (rhexT.P.v i) (rhexT.P.v (i + 1)) (L i)) ∧ (∀ i, L i ≠ []) ∧
      ∀ i, ∀ e ∈ L i, dist e.2.1 e.2.2 = slen rhexT.C 2 := by
  rintro ⟨L, hW, hne, hc⟩
  have hsum := walkT_dist_sum (hW 0)
  have hmap : (L 0).map (fun e => dist e.2.1 e.2.2) = (L 0).map (fun _ => Real.sqrt 3) :=
    List.map_congr_left (fun e he => by rw [hc 0 e he, rhexT_slen2])
  rw [hmap, List.map_const', List.sum_replicate, nsmul_eq_mul] at hsum
  have hs : dist (rhexT.P.v 0) (rhexT.P.v (0 + 1)) = 2 := rhexPoly_side 0
  rw [hs] at hsum
  exact nat_mul_sqrt3_ne_two _ hsum

/-- **Witness for the `hint` branch:** `rhexT` (M = 6 >= 5) satisfies the `hint` hypothesis of `BrHyp`: every tile step of length c has an interior open-segment point. -/
theorem rhexT_hint :
    ∀ (i : Fin (2 + 2 + 2 + 2 + 2 + 2)) (d : V2) (U V : Plane), TriStep (rhexT.C.tile i) d U V → dist U V = slen rhexT.C 2 →
      ∃ m ∈ openSegment ℝ U V, m ∈ interior rhexT.C.region := by
  classical
  obtain ⟨idx, hA, hcnt⟩ := rhexC_regular
  haveI : HasFansC rhexT.C.toRegionDissection := hasFansC_poly _ rhexT.P rhexT.region_eq
  have hab : Comm (slen rhexT.C 0) (slen rhexT.C 1) := rT_comm
  have hac : ¬ Comm (slen rhexT.C 0) (slen rhexT.C 2) := rT_notComm
  have hC : CaseC rhexT.C idx := ⟨idx_dist_of_angle rhexT.C idx hA, hA, fun X => hcnt X, notComb_c_of_comm (slen_pos rhexT.C 2) hab hac⟩
  rcases hint_or_allc rhexT.C idx hC rhexT.P rhexT.region_eq with h | h
  · exact h
  · exact absurd h rhexT_not_allc

#print axioms Erdos634.Draft.LaczFormal.RG.rhexT_not_allc
#print axioms Erdos634.Draft.LaczFormal.RG.rhexT_hint

end Erdos634.Draft.LaczFormal.RG
