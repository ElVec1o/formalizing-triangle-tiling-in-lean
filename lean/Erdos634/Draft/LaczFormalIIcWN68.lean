-- Draft/LaczFormalIIcWN68.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3), Lemma 6.2: `IIcNoKites` FROM THE NAMED SUPPLY `IIcKiteLayerSupply`.
-- `IIcKiteLayerSupply` says: for every Case IIc tiling (generic angles, corner counts as in `IIcNoKites`) with `kiteB <> empty`, the tile-level layer `KiteLayer M` (WN67) exists.
-- `iicNoKites_of_supply : IIcKiteLayerSupply -> IIcNoKites` is then a proved implication (via `kiteLayer_false`): all pure-geometry steps (d1) polygon orientation, (h) convexity of the
-- innermost cycle, (i) cyclic order of the chord ends, the angle sum, and the metric ring step are proved; the supply is exactly what remains.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3, Lemma 6.2), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcL8ab
import Erdos634.Draft.LaczFormalIIcWN67

open scoped Classical Fin.NatCast
open EuclideanGeometry Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

/-- The tile-level supply (NOT proved): a `KiteLayer` for every tiling violating `IIcNoKites`. -/
def IIcKiteLayerSupply : Prop :=
  ∀ (N M : ℕ) [NeZero M] (T : PolyTiling N M) (idx : Fin N → Equiv.Perm (Fin 3)), CaseC T.C idx →
    angleAt T.C.model 2 < Real.pi / 2 → angleAt T.C.model 2 ≠ Real.pi / 3 → Comm (slen T.C 0) (slen T.C 1) → ¬ Comm (slen T.C 0) (slen T.C 2) →
    AngGen (fun l => T.C.model.angleAt l) →
    (∀ j : Fin M, cnt T.C idx (T.P.v j) 0 = 1 ∧ cnt T.C idx (T.P.v j) 1 = 1 ∧ cnt T.C idx (T.P.v j) 2 = 0) →
    kiteB T.C idx ≠ ∅ → Nonempty (Erdos634.Draft.LaczFormal.WN.KiteLayer M)

theorem iicNoKites_of_supply (H : IIcKiteLayerSupply) : IIcNoKites := by
  intro N M _ T idx hC h1 h3 hab hac hAng hcor
  by_contra hne
  obtain ⟨K⟩ := H N M T idx hC h1 h3 hab hac hAng hcor hne
  exact Erdos634.Draft.LaczFormal.WN.kiteLayer_false K

#print axioms iicNoKites_of_supply

end Erdos634.Draft.LaczFormal.RG
