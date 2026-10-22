import Erdos634.Draft.BeesonShapesL5L6L11
import Erdos634.Draft.FluxRow2Witness

/-!
# Witness for the first (similar) disjunct of Beeson Lemma 6 (`BeesonShapesL5L6L11.lemma6`)

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Lemma 6), Laczkovich, Beeson-Zhang.
All hypotheses of `lemma6` are exhibited on `FluxRow2Witness.D2`, the scale-2 ladder of the `(2,3,4)` model
(a real `CongruentDissection 4`, target similar to the tile): `H1` is `alpha44_irr`, `3 alpha + 2 beta = pi` is
`three_α_two_β`, `ThreeAlphaData` is read off the model angles/opposite sides `(16, 24, 32)`.
The FIRST disjunct (angles of ABC a permutation of `(alpha, beta, gamma)`) is exhibited; the 77-tiling exercises the
second (`W77.lemma11_at_77`).  The second disjunct is not refuted on `D2` here.
-/

open scoped Classical

namespace Erdos634.BeesonColoring.W44Sim

open Erdos634.Geometry Erdos634.Draft.FluxGridWitness Erdos634.Draft.FluxRow2Witness

theorem M44_gamma : M44.angleAt 1 = 2 * α44 + β44 := by
  have hs := M44.angleAt_sum
  have h0 : M44.angleAt 0 = β44 := rfl
  have h2 : M44.angleAt 2 = α44 := rfl
  have h := three_α_two_β
  rw [h0, h2] at hs
  linarith

theorem M'_opp (k : Fin 3) : M'.oppLen k = M44.oppLen k := by
  unfold Tri.oppLen
  rw [M'_pts]

theorem D2_data : D2.model.ThreeAlphaData α44 β44 16 24 32 := by
  refine ⟨(finRotate 3).symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (M'_angle _).trans rfl
  · exact (M'_opp _).trans m_opp.2.2
  · exact (M'_angle _).trans rfl
  · exact (M'_opp _).trans m_opp.1
  · exact (M'_angle _).trans M44_gamma
  · exact (M'_opp _).trans m_opp.2.1

/-- `lemma6` on the similar dissection: the first disjunct holds. -/
theorem lemma6_similar_case : ∃ D : CongruentDissection (2 * 2),
    D.model.ThreeAlphaData α44 β44 16 24 32 ∧
    Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α44 β44 (2 * α44 + β44) := by
  refine ⟨D2, D2_data, ?_⟩
  have e0 := (D2_sim 0).1
  have e1 := (D2_sim 1).1
  have e2 := (D2_sim 2).1
  have a0 : D2.model.angleAt 0 = M44.angleAt 0 := M'_angle 0
  have a1 : D2.model.angleAt 1 = M44.angleAt 1 := M'_angle 1
  have a2 : D2.model.angleAt 2 = M44.angleAt 2 := M'_angle 2
  rw [e0, e1, e2, a0, a1, a2]
  show Triple3 β44 (M44.angleAt 1) α44 α44 β44 (2 * α44 + β44)
  rw [M44_gamma]
  unfold Triple3
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))

/-- The hypotheses of `lemma6` are all satisfied on `D2` (`H1`, `3 alpha + 2 beta = pi`, `ThreeAlphaData`). -/
theorem lemma6_applies :
    Triple3 (D2.target.angleAt 0) (D2.target.angleAt 1) (D2.target.angleAt 2) α44 β44 (2 * α44 + β44) ∨
    ((∀ k, vcount D2 k (2 * α44 + β44) = 0) ∧ (∑ k, vcount D2 k α44) = 3 ∧ (∑ k, vcount D2 k β44) = 2 ∧
      (∑ k, (vcount D2 k α44 + vcount D2 k β44)) = 5) :=
  lemma6 D2 α44_irr three_α_two_β D2_data

end Erdos634.BeesonColoring.W44Sim

#print axioms Erdos634.BeesonColoring.W44Sim.lemma6_similar_case
