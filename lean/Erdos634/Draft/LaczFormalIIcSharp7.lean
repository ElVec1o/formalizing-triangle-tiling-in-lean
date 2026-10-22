-- Draft/LaczFormalIIcSharp7.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2-6.3, repair of the hStrn gap (AI assistant plan IIC_STRN.md, S7, the statement the Lemma 6.3 lane needs): under the hypotheses of `gexc_matching'`,
-- EVERY exceptional point is an interior point of the region and receives EXACTLY `cnt gamma - cnt alpha` edges of Gamma_except (`gexc_exc_interior_exact`).
-- Proof: M1 of `gexc_matching'` (exact count, no `hStrn`) against the boundary capacity `exc_capacity_boundary` (count + cnt alpha + 1 <= cnt gamma).  This replaces the printed "the equations at E and F must be alpha+beta+(k+1)gamma = 2pi" (Lemma 6.3) by "interior + exactly k arrivals" (nothing about the type).
-- NOTE, UNAUDITED.  The global hypothesis block is that of `gexc_matching` (Case IIc, `P = N`); satisfiability is witnessed by GenWitK (204-tile octagon, genTiling_thm21) and IsoWitM (it is the hypothesis set of a proof by contradiction in the paper).
-- Credit: Laczkovich (DCG 48 (2012), Sect. 6.2-6.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcSharp5
import Erdos634.Draft.LaczFormalIIcSharp6

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

/-- **S7.** Every exceptional point is interior, and receives exactly `cnt gamma - cnt alpha` edges. -/
theorem gexc_exc_interior_exact [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    (h1 : D.model.angleAt 2 < Real.pi / 2) (h3 : D.model.angleAt 2 ≠ Real.pi / 3) (G : AngGen (fun l => D.model.angleAt l))
    (hcor : ∀ j : Fin M, cnt D idx (P.v j) 0 = 1 ∧ cnt D idx (P.v j) 1 = 1 ∧ cnt D idx (P.v j) 2 = 0) :
    ∀ E ∈ excVerts2 D idx P, E ∈ interior D.region ∧
      ((vtxSet D.toRegionDissection).filter (fun X => GExc D idx X E)).card = cnt D idx E 2 - cnt D idx E 0 := by
  intro E hE
  have hM1 := (gexc_matching' D P hreg idx hC hab hac h1 h3 G hcor).2.1 E hE
  refine ⟨?_, hM1⟩
  by_contra hb
  have := exc_capacity_boundary D P hreg idx hC h1 h3 hE hb
  have hlt := (Finset.mem_filter.mp hE).2
  omega

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.gexc_exc_interior_exact
