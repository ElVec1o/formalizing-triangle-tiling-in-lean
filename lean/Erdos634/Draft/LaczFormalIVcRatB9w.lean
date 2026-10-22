-- Draft/LaczFormalIVcRatB9w.lean -- witness for B9 (`vw_star`, `corner_cone`): the one-rhombus tiling vw_witness (b = 1) satisfies every hypothesis
--   (convex, area corner pi/3 at X = x by `witRhomb_corner_vol`) and the conclusion is obtained: a frame at X and k, m >= 1 with A = box.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatB9b
import Erdos634.Draft.LaczFormalIVcRatB6w

open scoped Classical Fin.NatCast
open MeasureTheory
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

theorem vw_star_witness :
    ∃ F : Frame 1, F.pt 0 0 = mkPt witRhomb.x0 witRhomb.x1 ∧ ∃ k m : ℕ, 1 ≤ k ∧ 1 ≤ m ∧
      witRhomb.set = {y | 0 ≤ F.fa y ∧ F.fa y ≤ (k : ℝ) ∧ 0 ≤ F.fb y ∧ F.fb y ≤ (m : ℝ)} := by
  obtain ⟨ρ, hρ, hv⟩ := witRhomb_corner_vol
  exact vw_witness.vw_star one_pos witRhomb_convex hρ hv

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.vw_star_witness
