import Erdos634.Draft.BeesonL28d2
import Erdos634.Draft.DirCoset

/-!
# Beeson (arXiv 1206.2229v4) Lemma 19 (`AnchorCoset`) proved, hence Lemma 28 with printed signs UNCONDITIONAL

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Lemma 19, Lemma 28), Laczkovich (DCG 48 (2012)),
Beeson-Zhang.  Formalization debt, not progress on the /goal outcomes.

Sketch.  (1) Within one tile the edge directions differ by the exterior angles `pi - angle_k`, which lie in `L` because
`pi in L` (GridChar.pi_mem) and the model angles `alpha, beta, 2alpha+beta` lie in `L = Z pi + Z theta`, `theta =
alpha/2+pi/2` (this uses `3 alpha + 2 beta = pi`: `beta = (pi - 3 alpha)/2`; `alpha not in Q pi` only makes `theta`
irrational so `L` is a rank-2 grid).  (2) Across a shared segment the two tiles have opposite edge directions
(`Dissection.Adj.leftUnit_neg`), i.e. differ by `pi in L`.  (3) The coset of the anchor (direction of AB) is reached at a
corner tile.  Steps (1)-(3) are already `DirCoset.edge_dir_coset` (proved there with the connectedness of the plane minus
the vertex set instead of the adjacency graph, so `Dissection.adjConnected` is not needed).  This file only instantiates
it with `H = (chiAt alpha _ 0 anc).L`.
-/

open scoped Classical

namespace Erdos634.BeesonColoring

open Erdos634.Geometry Erdos634.Geometry.A1Field

variable {N : ℕ}

/-- **Beeson Lemma 19, proved**: `AnchorCoset` holds for every congruent dissection with a `ThreeAlphaData` model. -/
theorem anchorCoset_of_threeAlpha (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c) : AnchorCoset D α hα := by
  intro i k
  exact Erdos634.Draft.DirCoset.edge_dir_coset (chiAt α hα 0 (D.target.leftUnit 0).angle).L
    (chiAt α hα 0 (D.target.leftUnit 0).angle).pi_mem D
    (D.model.threeAlpha_angles_mem hα hrel h 0) i k

end Erdos634.BeesonColoring

#print axioms Erdos634.BeesonColoring.anchorCoset_of_threeAlpha
