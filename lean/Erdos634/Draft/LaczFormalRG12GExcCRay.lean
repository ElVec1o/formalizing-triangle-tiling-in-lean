-- Draft/LaczFormalRG12GExcCRay.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2, blueprint lemma L6 `c_ray_principle` (F7): in Case IIc (`CaseC`, `Gamma_c` empty by Lemma 4.6) at a point `X` with `NoBack` along `d` there is NO
-- pair (left tile starting at `X` along `d` with first side `c`, right tile ending at `X` along `-d` whose side on the ray is not `c`).  Route: `ga_edge_of_local` for the relabelled dissection (`a := c`, `gcEdge_iff`), then `gc_empty`.
-- Hypotheses: `CaseC`, `HasFansC`, a convex polygon tiling (`hreg`), `a, b` commensurable and `a, c` not (as `gc_empty`).  Non-vacuity: the hypotheses of `gc_empty` are witnessed on the 30-60-90 parallelogram (`vTiling_gc_empty`).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 4, Lemmas 4.5, 4.6, Sect. 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12GExc
import Erdos634.Draft.LaczFormalRG8Final

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ}

/-- **L6 (c-ray principle).** -/
theorem c_ray_principle [NeZero M] (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (P : ConvPoly M) (hreg : D.region = P.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (hC : CaseC D idx) (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2))
    {d : V2} (hd : d ≠ 0) {X : Plane} (hX : ∃ j k, (D.tile j).pts k = X) (hnb : NoBack D.toRegionDissection d X)
    {i1 : Fin N} {U1 : Plane} (hl : TriStep (D.tile i1) d X U1) (hla : dist X U1 = slen D 2)
    {i2 : Fin N} {U2 : Plane} (hr : TriStep (D.tile i2) (neg2 d) U2 X) (hra : dist U2 X ≠ slen D 2) : False := by
  classical
  have hG := hC.caseG
  haveI : HasFansC (relabelC D).toRegionDissection := (inferInstance : HasFansC D.toRegionDissection)
  have hE : ∃ H, GcEdge D X H := by
    rw [show (∃ H, GcEdge D X H) ↔ ∃ H, GaEdge (relabelC D).toRegionDissection (slen (relabelC D) 0) X H from
      exists_congr fun H => gcEdge_iff D X H]
    have e0 : slen (relabelC D) 0 = slen D 2 := relabelC_slen0 D
    exact ga_edge_of_local (relabelC D) (relabelCIdx idx) hG.hidx hG.hnc hd hX hnb (i1 := i1) (U1 := U1) hl (by rw [e0]; exact hla)
      (i2 := i2) (U2 := U2) hr (by rw [e0]; exact hra)
  obtain ⟨H, hH⟩ := hE
  exact gc_empty D P hreg idx hC hab hac X H hH

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.c_ray_principle
