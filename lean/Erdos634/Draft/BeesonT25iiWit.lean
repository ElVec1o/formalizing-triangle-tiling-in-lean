import Erdos634.Draft.BeesonT25ii
import Erdos634.Draft.G3HRows

/-!
# Witness for `t25_ii` (Beeson Theorem 25 (ii)): the 84-tiling

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Thm 25), Beeson-Zhang, Laczkovich.
The 84-tiling of the isosceles-alpha target by the tile `(16,24,32) = 8 * (2,3,4)`, so `g = 8`, `k = 2`, `m = 1`
(coprime, `(mk, k^2-m^2, k^2) = (2,3,4)`).  Every hypothesis of `t25_ii` holds; the conclusion gives `M`, `j` with
`M = 5 j`, `84 * 1 = j^2 * 3 * 7`, i.e. `j = 2`, `M = 10` (the value found independently in `W84.t25_at_84`).
H1 is `alpha44_irr`.  Hypotheses of the printed `g = 1` case are not witnessed in Lean (no primitive-tile tiling of an
isosceles-alpha triangle is formalized in the project; the printed statement is the `g = 1` instance of the one proved).
-/

open scoped Classical

namespace Erdos634.BeesonColoring.W84

open Erdos634.Geometry
open Erdos634.Draft.FluxGridWitness (α44 β44 α44_irr three_α_two_β)

theorem t25_ii_at_84 : ∃ M j : ℤ, M = 10 ∧ j = 2 ∧ M = 5 * j := by
  have hrel := three_α_two_β
  have hd := Erdos634.Draft.G3CS3Control.data
  have e0 := Erdos634.Draft.G3CS3Control.target_angle0
  have e1 := Erdos634.Draft.G3CS3Control.target_angle1
  have e2 : Erdos634.Draft.G3CS3Control.D.target.angleAt 2 = α44 + 2 * β44 := by
    have := Erdos634.Draft.G3CS3Control.D.target.angleAt_sum
    rw [e0, e1] at this; linarith
  obtain ⟨M, j, hM, hMj, heq⟩ := t25_ii Erdos634.Draft.G3CS3Control.D α44_irr hrel hd e0 e1 e2
    8 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [Erdos634.Draft.G3CS3Control.len84] at heq
  push_cast at heq hMj
  norm_num at heq hMj
  have hj2 : j ^ 2 = 4 := by linarith
  have hjpos : 0 < j := by
    by_contra hh
    have : M ≤ 0 := by rw [hMj]; linarith
    linarith
  have hj : j = 2 := by nlinarith
  exact ⟨M, j, by rw [hMj, hj]; norm_num, hj, by rw [hMj]⟩

end Erdos634.BeesonColoring.W84

#print axioms Erdos634.BeesonColoring.W84.t25_ii_at_84
