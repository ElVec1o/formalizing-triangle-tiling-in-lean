import Erdos634.Draft.BeesonL10
import Erdos634.Draft.BeesonColoringThm1ColourWit77

/-!
# Witness for Beeson Lemma 10 (`BeesonL10`): the 77-tiling

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Fig. 15, Lemma 10), Laczkovich, Beeson-Zhang.
Every hypothesis of `lemma10` holds on Beeson's 77-tiling (H1 is `alpha44_irr`; "ABC not similar to T" as in
`lemma11_at_77`), so the conclusions (vertex types, `NC = 1 + N1 + 2 N2 + N3`) hold for it.  The tiles of the 77-tiling are
hidden behind an existential, so the numerical values of `NC, N1, N2, N3` are not computed here.
-/

open scoped Classical

namespace Erdos634.BeesonColoring.W77

open Erdos634.Geometry Erdos634.Draft.FluxGridWitness

theorem lemma10_at_77 : ∃ D : CongruentDissection 77,
    (∀ v ∈ cornerPts D.toDissection, v ∉ Set.range D.target.pts →
      vecAt D α44 β44 v = (3, 2, 0) ∨ vecAt D α44 β44 v = (1, 1, 1) ∨ vecAt D α44 β44 v = (2, 2, 2) ∨
      vecAt D α44 β44 v = (6, 4, 0) ∨ vecAt D α44 β44 v = (4, 3, 1) ∨ vecAt D α44 β44 v = (0, 1, 3)) ∧
    ((cornerPts D.toDissection).filter (fun v => vecAt D α44 β44 v = (0, 1, 3))).card
      = 1 + ((cornerPts D.toDissection).filter (fun v => vecAt D α44 β44 v = (3, 2, 0))).card
        + 2 * ((cornerPts D.toDissection).filter (fun v => vecAt D α44 β44 v = (6, 4, 0))).card
        + ((cornerPts D.toDissection).filter (fun v => vecAt D α44 β44 v = (4, 3, 1))).card := by
  obtain ⟨D, h, e0, e1, e2, -, -, -⟩ := exists_D77'
  refine ⟨D, lemma10 D α44_irr three_α_two_β h ?_⟩
  obtain ⟨-, -, -, hα, hβ⟩ := model_abc_pos h
  have hrel := three_α_two_β
  rw [e0, e1, e2]
  intro hT
  unfold Triple3 at hT
  rcases hT with ⟨x, y, z⟩ | ⟨x, y, z⟩ | ⟨x, y, z⟩ | ⟨x, y, z⟩ | ⟨x, y, z⟩ | ⟨x, y, z⟩ <;>
    first | (exfalso; linarith) | exact α44_irr ⟨1 / 7, by push_cast; linarith⟩

end Erdos634.BeesonColoring.W77

#print axioms Erdos634.BeesonColoring.W77.lemma10_at_77
