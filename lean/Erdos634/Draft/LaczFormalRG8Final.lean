-- Draft/LaczFormalRG8Final.lean -- **Lemma 4.6 of Laczkovich (DCG 48 (2012))**, polygon version: in a regular tiling of a convex polygon by congruent triangles, if `a, b` are commensurable and `c` is not a rational
-- multiple of `a`, then the graph `Gamma_c` has no edge.  Unconditional (the arrival statement is `arrival_of_caseC`).  NOTE, UNAUDITED.
-- Witness: the two-triangle parallelogram of the 30-60-90 tile (2, 1, sqrt 3) satisfies all hypotheses (`vTiling_gc_empty`).
-- Credit: Laczkovich (DCG 48 (2012), Lemma 4.6), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG8Align
import Erdos634.Draft.LaczFormalRG6IVcWit

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

/-- **Lemma 4.6, convex polygon, hypotheses `CaseC`.** -/
theorem gc_empty (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (Pg : ConvPoly M) (hreg : D.region = Pg.carrier)
    (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx)
    (hab : Comm (slen D 0) (slen D 1)) (hac : ¬ Comm (slen D 0) (slen D 2)) : ∀ X H, ¬ GcEdge D X H :=
  gc_empty_of_arrival D Pg hreg idx h (arrival_of_caseC D idx h) hab hac

/-- **Lemma 4.6 for a regular tiling of a convex polygon** (any `γ`). -/
theorem polytiling_gc_empty {N M : ℕ} [NeZero M] (T : PolyTiling N M) (hreg : RegularPQ T.C) (hab : Comm (slen T.C 0) (slen T.C 1))
    (hac : ¬ Comm (slen T.C 0) (slen T.C 2)) : ∀ X H, ¬ GcEdge T.C X H := by
  classical
  obtain ⟨idx, hA, hcnt⟩ := hreg
  haveI : HasFansC T.C.toRegionDissection := hasFansC_poly _ T.P T.region_eq
  have hC : CaseC T.C idx := ⟨idx_dist_of_angle T.C idx hA, hA, fun X => hcnt X, notComb_c_of_comm (slen_pos T.C 2) hab hac⟩
  intro X H hE
  exact gc_empty T.C T.P T.region_eq idx hC hab hac X H hE

/-- **NON-VACUITY of Lemma 4.6**: on the two-triangle parallelogram of the 30-60-90 tile `(2, 1, sqrt 3)` all hypotheses hold (regular, `a, b` commensurable, `c` not commensurable with `a`). -/
theorem vTiling_gc_empty : ∀ X H, ¬ GcEdge vTiling.C X H :=
  polytiling_gc_empty vTiling (pDiss_regular one_pos vT_pos) vTiling_comm vTiling_notComm

end Erdos634.Draft.LaczFormal.RG
