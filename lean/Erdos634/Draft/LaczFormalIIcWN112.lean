-- Draft/LaczFormalIIcWN112.lean -- Laczkovich (DCG 48 (2012), Sect. 6.3, Fig. 8), R4: the TURNS of a ring quadrilateral at its end `W` on the cycle (pure complex plane).
-- Data at a convex vertex `Y` of the cycle with neighbours `X`, `Z`: the arrival ray `U - Y` of the chord (`gexc_arrive_dir`) and the position of the cycle edges: case B (chain counter-clockwise) `RotPos (Z-Y) (X-Y) (a+b)`,
-- `RotPos (Z-Y) (U-Y) (pi+b)`; case A (clockwise) `RotPos (X-Y) (Z-Y) (a+b)`, `RotPos (X-Y) (U-Y) (pi+a)`.  The neighbour `N` of the corner polygon is on the `X` side (`pred`) or the `Z` side (`succ`).
-- Result, the turn of the walk `U -> Y -> N` (`tau_a`) and of the walk `N -> Y -> U` (`tau_d`):  B/pred: `a`, `-a`; B/succ: `-b`, `b`; A/succ: `b`, `-b`; A/pred: `-a`, `a`.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 6.3, Fig. 5, 8), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIIcWN110

open scoped Classical Fin.NatCast
open Complex

namespace Erdos634.Draft.LaczFormal.WN

theorem RotPos.congr_angle {z1 z2 : ℂ} {θ θ' : ℝ} (h : RotPos z1 z2 θ) (e : θ = θ') : RotPos z1 z2 θ' := e ▸ h

theorem rotPos_flip (Y U : ℂ) : RotPos (Y - U) (U - Y) Real.pi := by
  have : U - Y = -(Y - U) := by ring
  rw [this]; exact RotPos.neg_self

/-- Case B (counter-clockwise chain), neighbour on the `X` side. -/
theorem w_turn_B_pred {Y U X Z N : ℂ} {a b : ℝ} (h1 : RotPos (Z - Y) (X - Y) (a + b)) (h2 : RotPos (Z - Y) (U - Y) (Real.pi + b))
    (hN : RotPos (X - Y) (N - Y) 0) : RotPos (Y - U) (N - Y) a ∧ RotPos (Y - N) (U - Y) (-a) := by
  constructor
  · have := ((rotPos_flip Y U).trans h2.symm).trans (h1.trans hN)
    exact this.congr_angle (by ring)
  · have := ((rotPos_flip Y N).trans (hN.symm.trans (h1.symm.trans h2)))
    have := this.shift (-1)
    exact this.congr_angle (by ring)

theorem w_turn_B_succ {Y U X Z N : ℂ} {a b : ℝ} (h2 : RotPos (Z - Y) (U - Y) (Real.pi + b))
    (hN : RotPos (Z - Y) (N - Y) 0) : RotPos (Y - U) (N - Y) (-b) ∧ RotPos (Y - N) (U - Y) b := by
  constructor
  · have := (rotPos_flip Y U).trans (h2.symm.trans hN)
    exact this.congr_angle (by ring)
  · have := (rotPos_flip Y N).trans (hN.symm.trans h2)
    have := this.shift (-1)
    exact this.congr_angle (by ring)

/-- Case A (clockwise chain), neighbour on the `Z` side. -/
theorem w_turn_A_succ {Y U X Z N : ℂ} {a b : ℝ} (h1 : RotPos (X - Y) (Z - Y) (a + b)) (h2 : RotPos (X - Y) (U - Y) (Real.pi + a))
    (hN : RotPos (Z - Y) (N - Y) 0) : RotPos (Y - U) (N - Y) b ∧ RotPos (Y - N) (U - Y) (-b) := by
  constructor
  · have := ((rotPos_flip Y U).trans h2.symm).trans (h1.trans hN)
    exact this.congr_angle (by ring)
  · have := (rotPos_flip Y N).trans (hN.symm.trans (h1.symm.trans h2))
    have := this.shift (-1)
    exact this.congr_angle (by ring)

theorem w_turn_A_pred {Y U X Z N : ℂ} {a b : ℝ} (h2 : RotPos (X - Y) (U - Y) (Real.pi + a))
    (hN : RotPos (X - Y) (N - Y) 0) : RotPos (Y - U) (N - Y) (-a) ∧ RotPos (Y - N) (U - Y) a := by
  constructor
  · have := (rotPos_flip Y U).trans (h2.symm.trans hN)
    exact this.congr_angle (by ring)
  · have := (rotPos_flip Y N).trans (hN.symm.trans h2)
    have := this.shift (-1)
    exact this.congr_angle (by ring)

#print axioms w_turn_B_pred
#print axioms w_turn_B_succ
#print axioms w_turn_A_succ
#print axioms w_turn_A_pred

end Erdos634.Draft.LaczFormal.WN
