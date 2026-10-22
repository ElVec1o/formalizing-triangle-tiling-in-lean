import Erdos634.Draft.BeesonL28b
import Erdos634.Draft.BeesonL28Wit77

/-!
# Witness for `lemma28_printed`: every hypothesis holds at the 77-tiling by `(2,3,4)`

NOTE, UNAUDITED.  SUPERSEDED by BeesonL28c3.lemma28_printed2 (2026-10-22): the triquadratic clause in
`lemma28_printed` is trivially true and the κ clauses are existential; do not cite it as the printed Lemma 28.
Kept because this file still uses it.  The printed shape `(2alpha, alpha, 2beta)` is realised by the 77-tiling; `hrel`, the
irrationality of `delta/pi = (alpha+beta)/pi` (from `alpha44_irr` via `delta_irr_iff`) and
`ThreeAlphaData` hold, and the conclusion gives `kappa = 2/7` as in Beeson's remark after Lemma 27.
Credit: Michael Beeson (arXiv 1206.2229 v4), Beeson-Zhang, Laczkovich.
-/

open scoped Classical

namespace Erdos634.BeesonColoring.W77

open Erdos634.Geometry Erdos634.Draft.FluxGridWitness Erdos634.Geometry.A1Field

theorem lemma28_printed_at_77 : ∃ D : CongruentDissection 77, ∃ M1 M2 : ℤ, (M2 : ℝ) - M1 ≠ 0 ∧
    ((M1 : ℝ) + M2) / ((M2 : ℝ) - M1) = 2 / 7 := by
  obtain ⟨D, h, e0, e1, e2, -, -, -⟩ := exists_D77'
  have hrel := three_α_two_β
  obtain ⟨M1, M2, hne, κ, hκ, hs, -, -, -⟩ :=
    (lemma28_printed D ((delta_irr_iff hrel).mp α44_irr) hrel h).2.2.2 (Or.inr ⟨e0, e1, e2⟩)
  refine ⟨D, M1, M2, hne, ?_⟩
  rw [← hκ, hs]; norm_num

end Erdos634.BeesonColoring.W77

#print axioms Erdos634.BeesonColoring.W77.lemma28_printed_at_77
