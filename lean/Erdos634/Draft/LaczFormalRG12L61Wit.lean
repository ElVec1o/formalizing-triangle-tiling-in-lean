-- Draft/LaczFormalRG12L61Wit.lean -- NON-VACUITY of `lemma61` (Laczkovich DCG 48 (2012), Lemma 6.1, Subcase IIc): the rhombus (0,0), (1,0), (1 + sqrt2/2, sqrt2/2), (sqrt2/2, sqrt2/2) tiled by two copies of the isosceles
-- triangle with sides (a, b, c) = (1, 1, sqrt(2 - sqrt 2)), gamma = pi/4 (< pi/2, != pi/3): a, b commensurable, c not a rational multiple of a, regular.  All hypotheses of `lemma61` hold.
-- Caveat: a 2-tile tiling (all tile vertices are polygon vertices), so the propagation along sides and the exceptional count are not exercised nontrivially.  UNAUDITED.
-- Credit: Laczkovich (DCG 48 (2012), Lemma 6.1), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalRG12L61Final
import Erdos634.Draft.LaczFormalRG9IcWit

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

noncomputable def w61Tiling : PolyTiling 2 4 := pTiling 1 oT oT one_pos oT_pos

theorem w61_slen0 : slen w61Tiling.C 0 = 1 := by
  show dist (mkPt oT oT) (mkPt 0 0) = 1
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt, oT]
  rw [abs_of_nonneg (Real.sqrt_nonneg 2)]
  nlinarith [sqrt2_sq]

theorem w61_slen1 : slen w61Tiling.C 1 = 1 := by
  show dist (mkPt 0 0) (mkPt 1 0) = 1
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt]

theorem w61_slen2 : slen w61Tiling.C 2 = Real.sqrt (2 - Real.sqrt 2) := by
  show dist (mkPt 1 0) (mkPt oT oT) = Real.sqrt (2 - Real.sqrt 2)
  rw [EuclideanSpace.dist_eq]
  simp [Fin.sum_univ_two, mkPt, oT]
  rw [Real.dist_eq, abs_of_nonneg (Real.sqrt_nonneg 2)]
  congr 1
  rw [sq_abs]
  nlinarith [sqrt2_sq]

theorem w61_comm : Comm (slen w61Tiling.C 0) (slen w61Tiling.C 1) := by
  rw [w61_slen0, w61_slen1]
  exact ⟨1, 1, one_pos, one_pos, by norm_num⟩

theorem w61_notComm : ¬ Comm (slen w61Tiling.C 0) (slen w61Tiling.C 2) := by
  rw [w61_slen0, w61_slen2]
  rintro ⟨p, q, hp, hq, e⟩
  have h2 : Irrational (Real.sqrt 2) := irrational_sqrt_two
  apply h2
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hc : Real.sqrt (2 - Real.sqrt 2) = (p : ℝ) / q := by
    field_simp; linarith
  have hlt : Real.sqrt 2 ≤ 2 := by
    have := sqrt2_sq
    nlinarith [Real.sqrt_nonneg 2]
  have hsq : (Real.sqrt (2 - Real.sqrt 2)) ^ 2 = 2 - Real.sqrt 2 := Real.sq_sqrt (by linarith)
  refine ⟨2 - ((p : ℚ) / q) ^ 2, ?_⟩
  push_cast
  rw [← hc]
  linarith

theorem w61_gamma : angleAt w61Tiling.C.model 2 = Real.pi / 4 := by
  show EuclideanGeometry.angle (mkPt 1 0) (mkPt 0 0) (mkPt oT oT) = Real.pi / 4
  unfold EuclideanGeometry.angle
  simp only [vsub_eq_sub]
  have hn : ‖mkPt oT oT - mkPt 0 0‖ = 1 := by
    rw [← dist_eq_norm]
    have := w61_slen0
    unfold slen at this
    exact this
  have hn1 : ‖mkPt 1 0 - mkPt 0 0‖ = 1 := by
    rw [← dist_eq_norm]
    have := w61_slen1
    unfold slen at this
    rw [dist_comm]; exact this
  have hin : inner ℝ (mkPt 1 0 - mkPt 0 0) (mkPt oT oT - mkPt 0 0) = oT := by
    simp [PiLp.inner_apply, Fin.sum_univ_two, mkPt]
  unfold InnerProductGeometry.angle
  rw [hin, hn, hn1]
  have : oT / (1 * 1) = Real.cos (Real.pi / 4) := by
    rw [Real.cos_pi_div_four]
    unfold oT; ring
  rw [this, Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]

/-- **NON-VACUITY of Lemma 6.1**: all hypotheses hold on this two-triangle rhombus (`γ = π/4`, `a = b = 1`, `c = √(2-√2)`); the conclusion of `lemma61` is obtained. -/
theorem lemma61_witness : Concl1 w61Tiling.C w61Tiling.P ∨ ∀ j : Fin 4, w61Tiling.P.angle j = Real.pi - angleAt w61Tiling.C.model 2 := by
  apply lemma61 w61Tiling (pDiss_regular one_pos oT_pos)
  · rw [w61_gamma]; linarith [Real.pi_pos]
  · rw [w61_gamma]; intro h; linarith [Real.pi_pos]
  · exact w61_comm
  · exact w61_notComm

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.lemma61_witness
