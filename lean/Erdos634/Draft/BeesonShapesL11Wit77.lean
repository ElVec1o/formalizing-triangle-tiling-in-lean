import Erdos634.Draft.BeesonShapesL5L6L11
import Erdos634.Draft.BeesonColoringThm1ColourWit77

/-!
# Witness for Beeson Lemma 6 / Lemma 11 (`BeesonShapesL5L6L11`): the 77-tiling

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Fig. 15, Lemmas 6, 11), Laczkovich, Beeson-Zhang.
Every hypothesis of `lemma11` holds on Beeson's 77-tiling (target `(2 alpha, alpha, 2 beta)`, tile `(2,3,4)`):
`H1` is `alpha44_irr`, `ThreeAlphaData` is `exists_D77'`, and "ABC not similar to T" is derived (the only candidate
vertex order forces `beta = 2 alpha`, hence `7 alpha = pi`, contradicting `H1`).  Conclusion read off: the fifth shape.
Not witnessed here: the first disjunct of `lemma6` (ABC similar to T: a tiling of a triangle by tiles similar to it
is not constructed in this file).
-/

open scoped Classical

namespace Erdos634.BeesonColoring.W77

open Erdos634.Geometry Erdos634.Draft.FluxGridWitness

theorem lemma11_at_77 : ∃ D : CongruentDissection 77,
    FiveShapes (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α44 β44 ∧
    (∑ k, vcount D k α44) = 3 ∧ (∑ k, vcount D k β44) = 2 ∧
    (∀ k, vcount D k (2 * α44 + β44) = 0) ∧ (∀ k, 1 ≤ vcount D k α44 + vcount D k β44) := by
  obtain ⟨D, h, e0, e1, e2, -, -, -⟩ := exists_D77'
  refine ⟨D, lemma11 D α44_irr three_α_two_β h ?_⟩
  obtain ⟨-, -, -, hα, hβ⟩ := model_abc_pos h
  have hrel := three_α_two_β
  rw [e0, e1, e2]
  intro hT
  unfold Triple3 at hT
  rcases hT with ⟨x, y, z⟩ | ⟨x, y, z⟩ | ⟨x, y, z⟩ | ⟨x, y, z⟩ | ⟨x, y, z⟩ | ⟨x, y, z⟩ <;>
    first | (exfalso; linarith) | exact α44_irr ⟨1 / 7, by push_cast; linarith⟩

end Erdos634.BeesonColoring.W77

#print axioms Erdos634.BeesonColoring.W77.lemma11_at_77
