-- Draft/LaczFormalRG12Shape.lean -- **Shape of the Lemma 4.8 pair** (Laczkovich DCG 48 (2012), Lemma 4.8, last sentence): two triangles on opposite sides of a common segment `UV`, with third vertices `W`, `W'`,
-- whose remaining side lengths agree either "straight" (`|UW'| = |UW|`, `|VW'| = |VW|`) or "crossed" (`|UW'| = |VW|`, `|VW'| = |UW|`): then `W'` is the reflection of `W` in the line `UV` (a KITE) in the first case and the
-- point reflection of `W` in the midpoint of `UV` (a PARALLELOGRAM) in the second case.  Pure plane geometry (coordinates), no tilings.  NOTE, UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Lemma 4.8), Beeson, Beeson-Zhang.
import Mathlib

namespace Erdos634.Draft.LaczFormal.RG

/-- Real-coordinate core. `v = (p,q)`, `w`, `u` are the vectors `V-U`, `W-U`, `W'-U`; the triangles lie on opposite sides: `cross v w > 0 > cross v u`. -/
theorem kite_real (p q wx wy ux uy : ℝ)
    (h1 : ux ^ 2 + uy ^ 2 = wx ^ 2 + wy ^ 2) (h2 : (ux - p) ^ 2 + (uy - q) ^ 2 = (wx - p) ^ 2 + (wy - q) ^ 2)
    (hc : 0 < p * wy - q * wx) (hc' : p * uy - q * ux < 0) :
    (p ^ 2 + q ^ 2) * ux = (p * wx + q * wy) * p + (p * wy - q * wx) * q ∧
    (p ^ 2 + q ^ 2) * uy = (p * wx + q * wy) * q - (p * wy - q * wx) * p := by
  have hd : p * ux + q * uy = p * wx + q * wy := by linear_combination (1 / 2 : ℝ) * (h1 - h2)
  have hsq : (p * uy - q * ux) ^ 2 = (p * wy - q * wx) ^ 2 := by
    linear_combination (p ^ 2 + q ^ 2) * h1 - (p * ux + q * uy + (p * wx + q * wy)) * hd
  have hneg : p * uy - q * ux = -(p * wy - q * wx) := by
    have : (p * uy - q * ux - (p * wy - q * wx)) * (p * uy - q * ux + (p * wy - q * wx)) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  constructor
  · linear_combination p * hd + (-q) * hneg
  · linear_combination q * hd + p * hneg

/-- Same side, same distances: the point is `W` itself. -/
theorem same_real (p q wx wy ux uy : ℝ)
    (h1 : ux ^ 2 + uy ^ 2 = wx ^ 2 + wy ^ 2) (h2 : (ux - p) ^ 2 + (uy - q) ^ 2 = (wx - p) ^ 2 + (wy - q) ^ 2)
    (hc : 0 < p * wy - q * wx) (hc' : 0 < p * uy - q * ux) : ux = wx ∧ uy = wy := by
  have hpq : p ^ 2 + q ^ 2 ≠ 0 := by
    intro h
    have hp : p = 0 := by nlinarith [sq_nonneg p, sq_nonneg q]
    have hq : q = 0 := by nlinarith [sq_nonneg p, sq_nonneg q]
    subst hp; subst hq; simp at hc
  have hd : p * ux + q * uy = p * wx + q * wy := by linear_combination (1 / 2 : ℝ) * (h1 - h2)
  have hsq : (p * uy - q * ux) ^ 2 = (p * wy - q * wx) ^ 2 := by
    linear_combination (p ^ 2 + q ^ 2) * h1 - (p * ux + q * uy + (p * wx + q * wy)) * hd
  have hpos : p * uy - q * ux = p * wy - q * wx := by
    have : (p * uy - q * ux - (p * wy - q * wx)) * (p * uy - q * ux + (p * wy - q * wx)) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  constructor
  · apply mul_left_cancel₀ hpq
    linear_combination p * hd + (-q) * hpos
  · apply mul_left_cancel₀ hpq
    linear_combination q * hd + p * hpos

/-- The crossed case: `W' = U + V - W` (coordinates `u = v - w`). -/
theorem para_real (p q wx wy ux uy : ℝ)
    (h1 : ux ^ 2 + uy ^ 2 = (wx - p) ^ 2 + (wy - q) ^ 2) (h2 : (ux - p) ^ 2 + (uy - q) ^ 2 = wx ^ 2 + wy ^ 2)
    (hc : 0 < p * wy - q * wx) (hc' : p * uy - q * ux < 0) :
    ux = p - wx ∧ uy = q - wy := by
  obtain ⟨e1, e2⟩ := same_real p q wx wy (p - ux) (q - uy) (by linear_combination h2) (by linear_combination h1) hc
    (by nlinarith [hc'])
  exact ⟨by linarith, by linarith⟩

end Erdos634.Draft.LaczFormal.RG
