-- Draft/LaczFormalBZL7b.lean -- WITNESS for `bz_L7_triangle` / `bz_L7_polygon`: the certified N = 1215 tiling of the equilateral triangle by 1890*(3,5,7) (Herdt/Zhang; BZWit)
-- gives a PolyTiling with RegularPQ, gamma = 2pi/3, alpha not in Q pi, so every hypothesis (M = 3) is satisfied and the conclusion holds.
-- No witness for the M = 4 (Concl1) or M = 6 (Concl6) branches.  NOTE, UNAUDITED.  Credit: Herdt, Zhang, Beeson-Zhang, Laczkovich.
import Erdos634.Draft.LaczFormalBZL7a
import Erdos634.Draft.LaczFormalBZWit

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.TilePlacement Erdos634.Draft.LaczFormal.Thm21 Erdos634.Draft.LaczFormal.RG Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.G3CEqui135Control

namespace Erdos634.Draft.LaczFormal.BZWit

theorem bz_L7_hyp_witness : ∃ (N : ℕ) (T : PolyTiling N 3), RegularPQ T.C ∧ angleAt T.C.model 2 = 2 * Real.pi / 3 ∧
    ¬ ∃ r : ℚ, angleAt T.C.model 0 = (r : ℝ) * Real.pi := by
  obtain ⟨hA0, hA1, hA2, hP⟩ := polyTiling_angles D data heq
  set T := polyTiling_of_dissection D data heq with hT
  have hα' : ¬ ∃ r : ℚ, angleAt T.C.model 0 = (r : ℝ) * Real.pi := by rw [hA0]; exact α_irr
  exact ⟨_, T, regular_of_irr T hA2 hα' hP, hA2, hα'⟩

theorem bz_L7_triangle_witness : ∃ (N : ℕ) (T : PolyTiling N 3), Comm (slen T.C 0) (slen T.C 1) ∧ Comm (slen T.C 0) (slen T.C 2) := by
  obtain ⟨N, T, h1, h2, h3⟩ := bz_L7_hyp_witness
  exact ⟨N, T, bz_L7_triangle T h1 h2 h3⟩

end Erdos634.Draft.LaczFormal.BZWit

#print axioms Erdos634.Draft.LaczFormal.BZWit.bz_L7_hyp_witness
#print axioms Erdos634.Draft.LaczFormal.BZWit.bz_L7_triangle_witness
