import Erdos634.Draft.BeesonL28
import Erdos634.Draft.BeesonColoringThm1ColourWit77

/-!
# Witness for `lemma28`: the 77-tiling by `(2,3,4)`, shape `(2alpha, alpha, 2beta)`

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Lemma 28 and the table after Lemma 27, `kappa = 2/7`),
Beeson-Zhang, Laczkovich.  The hypotheses of `lemma28` hold (the 77-tiling, `alpha44_irr` as H1) and
`kappa = (M1+M2)/(M2-M1) = 2/7 = s/(2-s^2)` with `s = 1/2`, as in Beeson's remark.
-/

open scoped Classical

namespace Erdos634.BeesonColoring.W77

open Erdos634.Geometry Erdos634.Draft.FluxGridWitness Erdos634.Geometry.A1Field

theorem lemma28_at_77 : ∃ D : CongruentDissection 77, ∃ M1 M2 : ℤ, (M2 : ℝ) - M1 ≠ 0 ∧
    ((M1 : ℝ) + M2) / ((M2 : ℝ) - M1) = 2 / 7 ∧ 0 < ((M1 : ℝ) + M2) / ((M2 : ℝ) - M1) ∧
    ((M1 : ℝ) + M2) / ((M2 : ℝ) - M1) < 1 := by
  obtain ⟨D, h, e0, e1, e2, -, -, -⟩ := exists_D77'
  have hrel := three_α_two_β
  obtain ⟨M1, M2, hne, κ, hκ, hs, q0, q1, -, -⟩ :=
    (lemma28 D α44_irr hrel h).2.2.2 (Or.inr ⟨e0, e1, e2⟩)
  refine ⟨D, M1, M2, hne, ?_, ?_, ?_⟩
  · rw [← hκ, hs]; norm_num
  · rw [← hκ]; exact q0
  · rw [← hκ]; exact q1

end Erdos634.BeesonColoring.W77

#print axioms Erdos634.BeesonColoring.W77.lemma28_at_77
