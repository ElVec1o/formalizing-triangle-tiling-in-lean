-- Draft/LaczFormalIIcGenWitD.lean -- WITNESS of the GENERIC Case IIc block (alpha != beta), step D: kernel evaluation of the remaining Bool checks (tiles valid/congruent/inside, octagon convex, fan, area sums, corner counts).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcGenWitB

namespace Erdos634.Draft.LaczFormal.GenWit

open Z2

theorem tileTab_length : tileTab.length = 204 := by decide +kernel
theorem tiles_ok : tileTab.all (fun t => validB t && congB t && inB t) = true := by decide +kernel
theorem conv_ok : convB = true := by decide +kernel
theorem fan_ok : fanTab.all (fun t => posT t && inB t) = true := by decide +kernel
theorem fan_pairs_ok : pairsAll fanTab = true := by decide +kernel

end Erdos634.Draft.LaczFormal.GenWit
