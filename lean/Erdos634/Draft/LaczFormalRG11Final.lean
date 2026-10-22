-- Draft/LaczFormalRG11Final.lean -- **Theorem 2.1, Case II (gamma < pi/2, gamma != pi/3), Subcase IIa** (Laczkovich DCG 48 (2012), Sect. 6.1): `a` is not a nonnegative rational combination of `b, c`.
-- `caseII_a`: every regular tiling of a convex polygon by congruent triangles satisfies conclusion (i).  (The printed text writes `R = N-2, N-1, N` for the three cases; the correct quantity is `P`, the number of
-- polygon vertices of type `alpha+beta`; `P = N-1, N` are impossible (`caseIIa_P_eq`), `P = N-2` gives the parallelogram.)  NOTE, UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Sect. 4, 6.1), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG11IIa

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

/-- **Theorem 2.1, Case II, Subcase IIa.** -/
theorem caseII_a {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) (h1 : angleAt T.C.model 2 < Real.pi / 2) (h3 : angleAt T.C.model 2 ≠ Real.pi / 3)
    (hnc : NotComb (slen T.C 0) (slen T.C 1) (slen T.C 2)) : Concl1 T.C T.P := by
  classical
  obtain ⟨idx, hA, hcnt⟩ := hreg
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hregc : ∀ X, cnt T.C idx X 0 = cnt T.C idx X 1 := fun X => hcnt X
  have hidx := idx_dist_of_angle T.C idx hA
  have hCA : CaseA T.C idx := ⟨hidx, hA, hnc, hregc⟩
  obtain ⟨hall, hM4, a, ang1, ang2, ang3, c0, c2⟩ := caseII_core T.C T.P T.region_eq idx hCA h1 h3
  subst hM4
  have hI := side_hyps2 T.C T.P T.region_eq idx hCA h1 h3 a (fun hb => hall a (by unfold Blocked; tauto))
  have hO := side_hyps2 T.C T.P T.region_eq idx hCA h1 h3 (a + 1) (fun hb => hall (a + 1) (by unfold Blocked; tauto))
  have hside := gamma_vertex_multiple T.C T.P T.region_eq idx hCA a c0 (by rw [← hregc]; exact c0) c2 hI.1 hI.2 hO.1 hO.2
  exact concl1_of_gamma_para T a ang1 ang2 ang3 hside

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.caseII_a
