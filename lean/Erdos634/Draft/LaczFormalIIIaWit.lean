-- Draft/LaczFormalIIIaWit.lean -- NON-VACUITY of `caseIIIa_repaired`: the two-triangle parallelogram tiled by two copies of the tile (a,b,c) = (1, sqrt2, sqrt(3+sqrt2)), gamma = 2pi/3 at the vertex opposite c,
-- NotComb a b c (proved: r = p sqrt2 + q c is impossible), regular (pDiss_regular).  All hypotheses of `caseIIIa_repaired` hold; Concl1 obtained.
-- Caveat: 2-tile tiling, so the counting repair is not exercised nontrivially (M = 4).  UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012)), Beeson-Zhang.
import Erdos634.Draft.LaczFormalBZBridge
import Erdos634.Draft.LaczFormalRG9IcWit

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

noncomputable def w3S : ℝ := -(1 / 2)
noncomputable def w3T : ℝ := Real.sqrt 3 / 2
theorem w3T_pos : 0 < w3T := by unfold w3T; positivity

noncomputable def w3Tiling : PolyTiling 2 4 := pTiling (Real.sqrt 2) w3S w3T (by positivity) w3T_pos

theorem w3_slen0 : slen w3Tiling.C 0 = 1 := by
  show dist (mkPt w3S w3T) (mkPt 0 0) = 1
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt, w3S, w3T]
  rw [abs_of_nonneg (Real.sqrt_nonneg 3), div_pow, sqrt3_sq]; norm_num

theorem w3_slen1 : slen w3Tiling.C 1 = Real.sqrt 2 := by
  show dist (mkPt 0 0) (mkPt (Real.sqrt 2) 0) = Real.sqrt 2
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt]

theorem w3_slen2 : slen w3Tiling.C 2 = Real.sqrt (3 + Real.sqrt 2) := by
  show dist (mkPt (Real.sqrt 2) 0) (mkPt w3S w3T) = Real.sqrt (3 + Real.sqrt 2)
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt, w3S, w3T]
  congr 1
  rw [Real.dist_eq, sq_abs, abs_of_nonneg (Real.sqrt_nonneg 3), div_pow, sqrt3_sq]
  nlinarith [sqrt2_sq, sqrt3_sq]

theorem w3_notComb : NotComb (slen w3Tiling.C 0) (slen w3Tiling.C 1) (slen w3Tiling.C 2) := by
  rw [w3_slen0, w3_slen1, w3_slen2]
  intro r p q hr e
  have h2 : Irrational (Real.sqrt 2) := irrational_sqrt_two
  have hsq : (Real.sqrt (3 + Real.sqrt 2)) ^ 2 = 3 + Real.sqrt 2 := Real.sq_sqrt (by positivity)
  set c := Real.sqrt (3 + Real.sqrt 2)
  set x := Real.sqrt 2
  have e' : (r : ℝ) = p * x + q * c := by linarith
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    simp at e'
    have hp : (p : ℝ) ≠ 0 := by intro h; rw [h] at e'; simp at e'; linarith
    apply h2
    exact ⟨(r : ℚ) / p, by push_cast; field_simp; linarith⟩
  · have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have hc : (q : ℝ) * c = r - p * x := by linarith
    have h3 : ((q : ℝ) * c) ^ 2 = (r - p * x) ^ 2 := by rw [hc]
    have hx2 : x ^ 2 = 2 := sqrt2_sq
    have key : ((q : ℝ) ^ 2 + 2 * r * p) * x = (r : ℝ) ^ 2 + 2 * p ^ 2 - 3 * q ^ 2 := by
      have : ((q : ℝ) * c) ^ 2 = q ^ 2 * (3 + x) := by rw [mul_pow, hsq]
      nlinarith
    have hpos : (0 : ℝ) < (q : ℝ) ^ 2 + 2 * r * p := by positivity
    apply h2
    refine ⟨(((r : ℚ) ^ 2 + 2 * p ^ 2 - 3 * q ^ 2) / ((q : ℚ) ^ 2 + 2 * r * p)), ?_⟩
    push_cast
    field_simp
    linarith

theorem w3_gamma : angleAt w3Tiling.C.model 2 = 2 * Real.pi / 3 := by
  show EuclideanGeometry.angle (mkPt (Real.sqrt 2) 0) (mkPt 0 0) (mkPt w3S w3T) = 2 * Real.pi / 3
  unfold EuclideanGeometry.angle
  simp only [vsub_eq_sub]
  have hn : ‖mkPt w3S w3T - mkPt 0 0‖ = 1 := by
    rw [← dist_eq_norm]; have := w3_slen0; unfold slen at this; exact this
  have hn1 : ‖mkPt (Real.sqrt 2) 0 - mkPt 0 0‖ = Real.sqrt 2 := by
    rw [← dist_eq_norm]; have := w3_slen1; unfold slen at this; rw [dist_comm]; exact this
  have hin : inner ℝ (mkPt (Real.sqrt 2) 0 - mkPt 0 0) (mkPt w3S w3T - mkPt 0 0) = Real.sqrt 2 * w3S := by
    simp [PiLp.inner_apply, Fin.sum_univ_two, mkPt]; ring
  unfold InnerProductGeometry.angle
  rw [hin, hn, hn1]
  have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have : Real.sqrt 2 * w3S / (Real.sqrt 2 * 1) = Real.cos (2 * Real.pi / 3) := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
    unfold w3S; field_simp
  rw [mul_one] at *
  rw [this, Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]

/-- **NON-VACUITY of `caseIIIa_repaired`**: every hypothesis is witnessed; Concl1 follows. -/
theorem caseIIIa_witness : Concl1 w3Tiling.C w3Tiling.P :=
  caseIIIa_repaired w3Tiling (pDiss_regular (by positivity) w3T_pos) w3_gamma w3_notComb

#print axioms Erdos634.Draft.LaczFormal.RG.caseIIIa_witness

end Erdos634.Draft.LaczFormal.RG
