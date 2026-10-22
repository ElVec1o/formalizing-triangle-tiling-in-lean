-- Draft/LaczFormalIIcGenWitD3.lean -- WITNESS of the GENERIC Case IIc block (alpha != beta), step D3: kernel evaluation that the 204 pairs (alpha-vertex, beta-vertex) of the tiles are pairwise distinct (the tiling contains NO KITE:
-- two tiles on opposite sides of an edge, both with alpha at the same end and beta at the other, would have equal pairs).  NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcGenWitB

namespace Erdos634.Draft.LaczFormal.GenWit

def abL : List (Pt × Pt) := tileTab.map fun t => (t.p0, t.p1)

theorem ab_nodup : abL.Nodup := by decide +kernel

end Erdos634.Draft.LaczFormal.GenWit
