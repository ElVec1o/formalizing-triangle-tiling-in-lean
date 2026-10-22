-- Draft/LaczFormalIVcRatWit4.lean -- the witness `rat_hex_witness` shows the RIGHT branch: for the tiling `rhexT` the conclusion is exactly `Concl9`
-- (Laczkovich DCG 48 (2012), Thm 2.1 (ix)): M = 6, rational, all angles 2pi/3, gamma = pi/3, (alpha, beta) = (pi/6, pi/2).  All data derived directly
-- (side lengths of the hexagon, interior angles by inner products, tile angles from Wit3), NOT by re-running the dispatch.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 2 (vi), 8.3, Thm 2.1 (ix)), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatWit3

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

theorem Phi_sub (a b c d : ℝ) : Phi a b - Phi c d = Phi (a - c) (b - d) := by
  ext i; fin_cases i <;> simp [Phi, mkPt] <;> ring

theorem Phi_norm_sq (a b : ℝ) : ‖Phi a b‖ ^ 2 = a ^ 2 + a * b + b ^ 2 := by
  have hh := sqrt3_sq'
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Phi, mkPt, iT]
  nlinarith [hh]

theorem Phi_inner (a b c d : ℝ) : inner ℝ (Phi a b) (Phi c d) = a * c + (a * d + b * c) / 2 + b * d := by
  have hh := sqrt3_sq'
  simp [PiLp.inner_apply, Fin.sum_univ_two, Phi, mkPt, iT]
  linear_combination (b * d / 4) * hh

theorem Phi_norm_two (a b : ℝ) (h : a ^ 2 + a * b + b ^ 2 = 4) : ‖Phi a b‖ = 2 := by
  have := Phi_norm_sq a b
  nlinarith [norm_nonneg (Phi a b)]

/-- Interior angle `2 pi / 3` from two edge vectors of norm 2 with inner product -2. -/
theorem angle_120 (a b c d : ℝ) (h1 : a ^ 2 + a * b + b ^ 2 = 4) (h2 : c ^ 2 + c * d + d ^ 2 = 4)
    (h3 : a * c + (a * d + b * c) / 2 + b * d = -2) :
    InnerProductGeometry.angle (Phi a b) (Phi c d) = 2 * Real.pi / 3 := by
  have n1 : ‖Phi a b‖ = 2 := by
    have := Phi_norm_sq a b
    nlinarith [norm_nonneg (Phi a b)]
  have n2 : ‖Phi c d‖ = 2 := by
    have := Phi_norm_sq c d
    nlinarith [norm_nonneg (Phi c d)]
  unfold InnerProductGeometry.angle
  rw [Phi_inner, h3, n1, n2]
  have : (-2 : ℝ) / (2 * 2) = Real.cos (2 * Real.pi / 3) := by
    have : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    rw [this, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num
  rw [this, Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]

theorem rhexPoly_angle (i : Fin 6) : rhexPoly.angle i = 2 * Real.pi / 3 := by
  unfold ConvPoly.angle cornerAngle EuclideanGeometry.angle
  simp only [vsub_eq_sub]
  fin_cases i <;> simp [rhexPoly, Phi_sub] <;> norm_num <;>
    exact angle_120 _ _ _ _ (by norm_num) (by norm_num) (by norm_num)

theorem rhexPoly_side (i : Fin 6) : rhexPoly.side i = 2 := by
  unfold ConvPoly.side
  rw [dist_eq_norm]
  fin_cases i <;> simp [rhexPoly, Phi_sub] <;> norm_num <;>
    exact Phi_norm_two _ _ (by norm_num)

theorem rhexPoly_rational : RationalPoly rhexPoly := by
  intro i j
  rw [rhexPoly_side, rhexPoly_side]
  exact ⟨1, 1, one_pos, one_pos, by norm_num⟩

/-- **The witness shows the right branch:** for `rhexT` the conclusion is `Concl9` (Thm 2.1 (ix)), derived from the data. -/
theorem rhexT_concl9 : Concl9 rhexT.C rhexT.P :=
  ⟨rfl, rhexPoly_rational, rhexPoly_angle, rT_gamma, Or.inl ⟨rT_alpha, rT_beta⟩⟩

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.rhexT_concl9
