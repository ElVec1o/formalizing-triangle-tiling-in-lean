import Erdos634.Draft.BeesonT25
import Erdos634.Draft.G3HRows

/-!
# Witness for `t25_i` (Beeson Theorem 25 (i)): the 84-tiling

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Thm 25), Beeson-Zhang, Laczkovich.
84-tiling of the isosceles-alpha target `(alpha, alpha, alpha + 2 beta)` (sides `192, 192, 336`) by the tile `(16, 24, 32)`,
`s = 1/2`: the equation reads `84 * (1/2)(5/2)^2 = M^2 (3/2)(7/4)`, so `M^2 = 100`, `M = 10` (the value computed
independently in `W84.t4_M2_at_84`), and `M^2 = 100 <= 168 = 2 N`.  H1 is `alpha44_irr`.
-/

open scoped Classical

namespace Erdos634.BeesonColoring.W84

open Erdos634.Geometry
open Erdos634.Draft.FluxGridWitness (α44 β44 α44_irr three_α_two_β)

theorem t25_at_84 : ∃ M : ℤ, M = 10 := by
  have hrel := three_α_two_β
  have hd := Erdos634.Draft.G3CS3Control.data
  have e0 := Erdos634.Draft.G3CS3Control.target_angle0
  have e1 := Erdos634.Draft.G3CS3Control.target_angle1
  have e2 : Erdos634.Draft.G3CS3Control.D.target.angleAt 2 = α44 + 2 * β44 := by
    have := Erdos634.Draft.G3CS3Control.D.target.angleAt_sum
    rw [e0, e1] at this; linarith
  obtain ⟨M, hM, -, -, heq, hle⟩ := t25_i Erdos634.Draft.G3CS3Control.D α44_irr hrel hd e0 e1 e2
  rw [Erdos634.Draft.G3CS3Control.len84] at heq hle
  norm_num at heq
  refine ⟨M, ?_⟩
  have h2 : (M : ℝ) ^ 2 = 100 := by linarith
  have h3 : M ^ 2 = 100 := by exact_mod_cast h2
  nlinarith [h3, hM]

end Erdos634.BeesonColoring.W84

#print axioms Erdos634.BeesonColoring.W84.t25_at_84
