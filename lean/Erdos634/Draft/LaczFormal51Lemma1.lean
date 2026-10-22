-- Draft/LaczFormal51Lemma1.lean -- Beeson (arXiv 1206.2229 v4) LEMMA 1 (H1) with NO Laczkovich hypothesis left:
--   `lemma1_unconditional` : 3 alpha + 2 beta = pi, D a CongruentDissection of a triangle by the tile (alpha, beta, 2 alpha + beta) (`ThreeAlphaData`), target not similar (AAA) ==> alpha is not a rational multiple of pi.
--   `lemma6_unconditional` : the corresponding dichotomy of Beeson's Lemma 6.
-- Inputs: `Lacz51Gen2.lacz51_all` (Laczkovich Thm 5.1 for this tile, every denominator) and `BeesonH1.lacz53_thm` (Thm 5.3, the instance used), `BeesonH1.lemma1_of_laczkovich`.
-- NOTE, UNAUDITED.  Credit: Beeson (arXiv 1206.2229 v4, Lemma 1), Laczkovich (Discrete Math. 140 (1995) Thm 5.1, 5.3), Beeson-Zhang.
import Erdos634.Draft.LaczFormal51Gen2
import Erdos634.Draft.LaczFormal53

namespace Erdos634.BeesonH1

open Erdos634 Erdos634.Geometry Erdos634.BeesonColoring

theorem lemma1_unconditional {N : ℕ} (D : CongruentDissection N)
    {α β a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) :
    ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi :=
  lemma1_of_lacz51 Erdos634.Lacz51Gen2.lacz51_all D hrel h hns

theorem lemma6_unconditional {N : ℕ} (D : CongruentDissection N)
    {α β a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (h : D.model.ThreeAlphaData α β a b c) :
    Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β) ∨
    ((∀ k, vcount D k (2 * α + β) = 0) ∧ (∑ k, vcount D k α) = 3 ∧ (∑ k, vcount D k β) = 2 ∧
      (∑ k, (vcount D k α + vcount D k β)) = 5) :=
  lemma6_of_lacz51 Erdos634.Lacz51Gen2.lacz51_all D hrel h

end Erdos634.BeesonH1

#print axioms Erdos634.BeesonH1.lemma1_unconditional
#print axioms Erdos634.BeesonH1.lemma6_unconditional
