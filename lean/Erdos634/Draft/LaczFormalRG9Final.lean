-- Draft/LaczFormalRG9Final.lean -- statement-level packaging of Case I of Laczkovich's Theorem 2.1 (`Thm21_I`) and its proof from `thm21_I`.  UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Theorem 2.1, Sect. 5), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG9Ib
import Erdos634.Draft.LaczFormalRG9SideC2

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

/-- Case I of Theorem 2.1: `γ > π/2`, `γ ≠ 2π/3`. -/
def Thm21_I : Prop :=
  ∀ (N M : ℕ) [NeZero M] (T : PolyTiling N M), RegularPQ T.C → Real.pi / 2 < angleAt T.C.model 2 → angleAt T.C.model 2 ≠ 2 * Real.pi / 3 → Thm21Concl T.C T.P

theorem thm21_I_stmt : Thm21_I := fun _ _ _ T hreg h1 h3 => thm21_I T hreg h1 h3

end Erdos634.Draft.LaczFormal.RG
