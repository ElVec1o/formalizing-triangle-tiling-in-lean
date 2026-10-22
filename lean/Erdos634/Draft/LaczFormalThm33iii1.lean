-- Draft/LaczFormalThm33iii1.lean -- Laczkovich DCG 48 (2012) Thm 3.3, clause (iii), module 1 of 3.
--   `equil_sides`        : a triangle whose three angles are pi/3 has three equal sides (law of sines);
--   `type_arith_pi3`     : c0 a + c1 b + c2 (pi/3) = m (pi/3), a + b = 2pi/3, a not in Q pi  =>  c0 = c1;
--   `regular_of_irr_pi3` : PolyTiling of an equilateral triangle, gamma = pi/3, alpha not in Q pi  =>  RegularPQ (the analogue of BZ8.regular_of_irr);
--   `polyTilingOf`       : a CongruentDissection of an equilateral triangle, relabelled by sigma, is a PolyTiling with model angles D.model.angleAt (sigma j).
-- No Lemma 3.2 is used: for an irrational tile the regularity p = q at every vertex follows from the vertex angle sums (2 pi, pi, pi/3).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Thm 2.1, Lemma 3.2, Thm 3.3; Discrete Math 140 (1995)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalBZ8
import Erdos634.Draft.LaczFormalThm21Assembly
import Erdos634.TriLawSin

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement

namespace Erdos634.Draft.LaczFormal.RG

variable {N : ℕ}

/-- Equal angles `pi/3` give equal sides (sine rule). -/
theorem equil_sides (T : Tri) (h : ∀ k : Fin 3, T.angleAt k = Real.pi / 3) :
    ∀ j : Fin 3, dist (T.pts j) (T.pts (j + 1)) = dist (T.pts 0) (T.pts 1) := by
  have hs : Real.sin (Real.pi / 3) ≠ 0 := by
    have : 0 < Real.sin (Real.pi / 3) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
    exact this.ne'
  have key : ∀ j : Fin 3, Erdos634.TilePlacement.sideOpp T j = Erdos634.TilePlacement.sideOpp T (j + 1) := by
    intro j
    have := Erdos634.TriLawSin.sin_angleAt_mul_sideOpp T j
    have h1 : Erdos634.TilePlacement.angleAt T (j + 1) = Real.pi / 3 := h (j + 1)
    have h2 : Erdos634.TilePlacement.angleAt T j = Real.pi / 3 := h j
    rw [h1, h2] at this
    exact mul_left_cancel₀ hs this
  have a0 : Erdos634.TilePlacement.sideOpp T 0 = Erdos634.TilePlacement.sideOpp T 1 := key 0
  have a1 : Erdos634.TilePlacement.sideOpp T 1 = Erdos634.TilePlacement.sideOpp T 2 := key 1
  have e0 : dist (T.pts 1) (T.pts 2) = Erdos634.TilePlacement.sideOpp T 0 := rfl
  have e1 : dist (T.pts 2) (T.pts 0) = Erdos634.TilePlacement.sideOpp T 1 := rfl
  have e2 : dist (T.pts 0) (T.pts 1) = Erdos634.TilePlacement.sideOpp T 2 := rfl
  intro j
  fin_cases j
  · rfl
  · show dist (T.pts 1) (T.pts 2) = _
    rw [e0, e2, a0, a1]
  · show dist (T.pts 2) (T.pts 0) = _
    rw [e1, e2, a1]

end Erdos634.Draft.LaczFormal.RG
