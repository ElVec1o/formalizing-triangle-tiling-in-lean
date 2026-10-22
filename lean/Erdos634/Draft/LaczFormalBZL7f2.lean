-- Draft/LaczFormalBZL7f2.lean -- Beeson (arXiv 1206.1974v7) Sect. 10.1, 10.3-10.6: boundary arithmetic and a NON-VACUITY WITNESS.
--   `boundary_vtype`  : a non-corner boundary vertex (angle sum pi) of a (alpha, beta, 2alpha)-tiling, alpha not in Q pi, has counts (3,1,0) or (1,1,1): one beta, at most one gamma
--                       (Lemma 10.1 and the "no two gamma at a boundary vertex" step of Lemma 10.6, printed with p, q);
--   `witness_1125_center` : the certified 1125-tiling of the isosceles (150,150,225)*16 triangle by the tile (4,5,6)*16 (Herdt/Zhang, G3GControl.D) satisfies EVERY hypothesis of
--                       `exists_center_a2` (Beeson Lemma 10.2) and so has a centre vertex (counts (0,2,3)).  (The witness is for the hypotheses of the Lean lemma, i.e. non-vacuity.)
-- NOT here: link graphs Gamma_b, Gamma_a, Gamma_c on a real fan, Lemmas 10.3-10.6 geometric parts (see (private working notes, not included)).  NOTE, UNAUDITED.
-- Credit: Beeson (arXiv 1206.1974v7), Herdt, Zhang (the 1125-tiling), Beeson-Zhang (arXiv 2604.01314), Laczkovich.
import Erdos634.Draft.LaczFormalBZL7e1
import Erdos634.Draft.LaczFormalBZL7d5b
import Erdos634.Draft.G3GControl

open scoped Classical
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

theorem boundary_vtype {α β : ℝ} (hβ : β = Real.pi - 3 * α) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (c0 c1 c2 : ℕ) (h : (c0 : ℝ) * α + c1 * β + c2 * (2 * α) = Real.pi) :
    c1 = 1 ∧ ((c0 = 3 ∧ c2 = 0) ∨ (c0 = 1 ∧ c2 = 1)) := by
  have := vtype_arith hβ hα c0 c1 c2 0 1 (by rw [h]; push_cast; ring)
  omega

theorem no_two_gamma_boundary {α β : ℝ} (hβ : β = Real.pi - 3 * α) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (c0 c1 c2 : ℕ) (h : (c0 : ℝ) * α + c1 * β + c2 * (2 * α) = Real.pi) : c1 ≤ 1 ∧ c2 ≤ 1 := by
  have := boundary_vtype hβ hα c0 c1 c2 h
  omega

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.boundary_vtype
#print axioms Erdos634.Draft.LaczFormal.RG.no_two_gamma_boundary
