-- Draft/LaczFormalIVcRatBr5c.lean -- Laczkovich DCG 48 (2012), Sect. 8.3 (Subcase IVc, rational branch): BRIDGE item (1), stage Br5c.
--   `hint_or_allc`: for a regular (CaseC) tiling of a convex polygon with a, b commensurable and c not, EITHER every tile left step of length c has an interior
--   open-segment point (the hypothesis `hint` of `BrHyp`), OR there are side walks all of whose tile edges have length c (the second branch of B1).
--   Combines `sides_edge_dichotomy` (B1) with `hint_of_no_c_walk` (Br5b).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 4, 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatBr5b
import Erdos634.Draft.LaczFormalIVcRatB1

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

variable {N M : ℕ} [NeZero M]

theorem hint_or_allc (D : CongruentRegionDissection N) [HasFansC D.toRegionDissection] (idx : Fin N → Equiv.Perm (Fin 3)) (h : CaseC D idx)
    (P : ConvPoly M) (hreg : D.region = P.carrier) :
    (∀ (i : Fin N) (d : V2) (U V : Plane), TriStep (D.tile i) d U V → dist U V = slen D 2 → ∃ m ∈ openSegment ℝ U V, m ∈ interior D.region) ∨
    (∃ L : Fin M → List (Fin N × Plane × Plane), (∀ i, WalkT D.toRegionDissection (toV2 (P.e i)) (P.v i) (P.v (i + 1)) (L i)) ∧ (∀ i, L i ≠ []) ∧
      ∀ i, ∀ e ∈ L i, dist e.2.1 e.2.2 = slen D 2) := by
  obtain ⟨L, hW, hne, hcase⟩ := sides_edge_dichotomy D idx h P hreg
  rcases hcase with hall | hnone
  · exact Or.inr ⟨L, hW, hne, hall⟩
  · exact Or.inl (hint_of_no_c_walk D P hreg L hW hnone)

#print axioms Erdos634.Draft.LaczFormal.RG.hint_or_allc
#print axioms Erdos634.Draft.LaczFormal.RG.hint_of_no_c_walk
#print axioms Erdos634.Draft.LaczFormal.RG.overlap_eq
#print axioms Erdos634.Draft.LaczFormal.RG.tri_edges_par_eq
#print axioms Erdos634.Draft.LaczFormal.RG.step_near_interior

end Erdos634.Draft.LaczFormal.RG
