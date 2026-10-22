-- Draft/LaczFormalIIcWN19.lean -- Laczkovich (DCG 48 (2012)), Sect. 6.2: a cycle of Gamma_kite (distinct vertices) is a simple polygon (WN18, step (a) first half)
-- whose winding number off the polygon is {0, sigma}, sigma = +-1 (WN13, Jordan-type dichotomy B5): the "C-degree" {wind != 0} of (b) is the whole of one side.
-- NOTE, UNAUDITED.  The hypothesis `GKite`-cycle is NOT witnessed here (no tiling with a closed Gamma_kite chain has been exhibited).  Credit: Laczkovich (DCG 48 (2012), Sect. 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN18

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord Filter Topology

namespace Erdos634.Draft.LaczFormal.RG

theorem gkite_cycle_wind_dichotomy {N : ℕ} [NeZero N] (D : CongruentRegionDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) {m : ℕ} [NeZero m]
    (C : Fin m → Plane) (hC : ∀ k : Fin m, GKite D idx (C k) (C (k + 1))) (hinj : Function.Injective C) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ z : Plane, z ∉ Erdos634.Draft.LaczFormal.WN.edgeSetP C →
      Erdos634.Draft.LaczFormal.WN.windP C z = 0 ∨ Erdos634.Draft.LaczFormal.WN.windP C z = σ := by
  obtain ⟨hm, hs⟩ := gkite_cycle_simple D idx C hC hinj
  exact Erdos634.Draft.LaczFormal.WN.simple_wind_dichotomy_plane hs hinj hm

#print axioms gkite_cycle_wind_dichotomy

end Erdos634.Draft.LaczFormal.RG
