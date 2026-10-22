-- Draft/LaczFormalIVcRatB6w.lean -- witness of the hypotheses of `VWTiling.corner_piece` (B6): the one-rhombus VWTiling `vw_witness` (b = 1, A = Par), X = the corner x = 0.
--   `Par_convex`, `witRhomb_convex` : A convex.  `witRhomb_corner_vol` : area (A ∩ B(X, r)) = (pi/3)/2 * r^2 for all small r (cell 0 contributes pi/3, cell 1 does not contain X).
--   `corner_piece_witness_concl` : the hypotheses of `corner_piece` are satisfiable (Par_convex, witRhomb_corner_vol, hb = 1) and the conclusion is obtained for the witness (the unique rhombus, X = x).
--   Control: `witRhomb_x_not_cell1` (x is not in the second cell, the exclusion step used for the area count); no control for the side vertices x+s, x+w (their area angle 2pi/3 is NOT proved here).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatB6

open scoped Classical Fin.NatCast
open MeasureTheory
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace Erdos634.Draft.LaczFormal.RG

theorem Par_convex (g0 g1 u0 u1 w0 w1 : ℝ) : Convex ℝ (Par g0 g1 u0 u1 w0 w1) := by
  intro p hp q hq a b ha hb hab
  obtain ⟨l, m, hl, hl1, hm, hm1, hp0, hp1⟩ := hp
  obtain ⟨l', m', hl', hl1', hm', hm1', hq0, hq1⟩ := hq
  have hb' : b = 1 - a := by linarith
  refine ⟨a * l + b * l', a * m + b * m', by positivity, by nlinarith, by positivity, by nlinarith, ?_, ?_⟩
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; rw [hp0, hq0]; subst hb'; ring
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; rw [hp1, hq1]; subst hb'; ring

theorem witRhomb_convex : Convex ℝ witRhomb.set := Par_convex _ _ _ _ _ _

/-- The corner `x` of the witness rhombus is not in the second cell. -/
theorem witRhomb_x_not_cell1 : mkPt witRhomb.x0 witRhomb.x1 ∉ (witRhomb.cell 1).carrier := by
  have s3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  intro h
  have h' : mkPt witRhomb.x0 witRhomb.x1 ∈ (ct (witRhomb.x0 + witRhomb.s0 + witRhomb.w0) (witRhomb.x1 + witRhomb.s1 + witRhomb.w1)
      (-witRhomb.s0) (-witRhomb.s1) (-witRhomb.w0) (-witRhomb.w1) (hD2 witRhomb.hD)).carrier := h
  obtain ⟨l, m, hl, hm, hlm, h0, h1⟩ := (ct_carrier (hD2 witRhomb.hD) _).mp h'
  simp only [mkPt_zero, mkPt_one, witRhomb] at h0 h1
  have hm1 : m = 1 := by
    have : Real.sqrt 3 * (1 - m) = 0 := by linarith
    rcases mul_eq_zero.mp this with h2 | h2
    · linarith
    · linarith
  have hl1 : l = 1 := by rw [hm1] at h0; linarith
  linarith

/-- Area at the corner `x = 0` of the witness. -/
theorem witRhomb_corner_vol : ∃ ρ > 0, ∀ r, 0 < r → r ≤ ρ →
    volume (witRhomb.set ∩ Metric.ball (mkPt witRhomb.x0 witRhomb.x1) r) = ENNReal.ofReal (Real.pi / 3 / 2 * r ^ 2) := by
  have hb : (0 : ℝ) < 1 := one_pos
  set X := mkPt witRhomb.x0 witRhomb.x1 with hX
  have hc : ∀ c, (vw_witness.cellT c).Congruent (eqT 1 hb) := vw_witness.cell_congruent hb
  have e0 : X = (witRhomb.cell 0).pts 2 := plane_ext' (by simp [hX, RhombData.cell, rhombCell, ct, mkTri_pts, witRhomb]) (by simp [hX, RhombData.cell, rhombCell, ct, mkTri_pts, witRhomb])
  obtain ⟨r0, hr0, h0⟩ := (witRhomb.cell 0).volume_inter_ball_localAngle X
  obtain ⟨r1, hr1, h1⟩ := (witRhomb.cell 1).volume_inter_ball_localAngle X
  have hla0 : (witRhomb.cell 0).localAngle X = Real.pi / 3 := by
    rw [e0]; exact localAngle_vertex_equi hb (hc (Sum.inr ((), 0))) 2
  have hla1 : (witRhomb.cell 1).localAngle X = 0 := Tri.localAngle_eq_zero_of_not_mem _ witRhomb_x_not_cell1
  refine ⟨min r0 r1, lt_min hr0 hr1, fun r hr hle => ?_⟩
  have hD := (vw_witness.cellDiss hb).toRegionDissection
  have hsum := volume_inter_ball_eq_sum (vw_witness.cellDiss hb).toRegionDissection X r
  have hsum2 : ∑ i, volume (((vw_witness.cellDiss hb).tile i).carrier ∩ Metric.ball X r)
      = ∑ c : VWTiling.CellIdx Empty Unit, volume ((vw_witness.cellT c).carrier ∩ Metric.ball X r) :=
    (Fintype.equivFin (VWTiling.CellIdx Empty Unit)).symm.sum_comp (fun c => volume ((vw_witness.cellT c).carrier ∩ Metric.ball X r))
  have hreg : (vw_witness.cellDiss hb).toRegionDissection.region = witRhomb.set := rfl
  rw [← hreg, hsum, hsum2]
  simp only [VWTiling.CellIdx, Fintype.sum_sum_type, Fintype.sum_prod_type, Finset.univ_eq_empty, Finset.sum_empty, zero_add,
    Fintype.sum_unique, Fin.sum_univ_two]
  show volume ((witRhomb.cell 0).carrier ∩ Metric.ball X r) + volume ((witRhomb.cell 1).carrier ∩ Metric.ball X r) = _
  rw [h0 r hr (hle.trans (min_le_left _ _)), h1 r hr (hle.trans (min_le_right _ _)), hla0, hla1]
  simp

/-- The conclusion of `corner_piece` applied to the witness. -/
theorem corner_piece_witness_concl :
    ∃ r : Unit, (mkPt witRhomb.x0 witRhomb.x1 = mkPt (vw_witness.R r).x0 (vw_witness.R r).x1 ∨
        mkPt witRhomb.x0 witRhomb.x1 = mkPt ((vw_witness.R r).x0 + (vw_witness.R r).s0 + (vw_witness.R r).w0)
          ((vw_witness.R r).x1 + (vw_witness.R r).s1 + (vw_witness.R r).w1)) ∧
      (∀ r', mkPt witRhomb.x0 witRhomb.x1 ∈ (vw_witness.R r').set → r' = r) ∧ (∀ k : Empty, mkPt witRhomb.x0 witRhomb.x1 ∉ (vw_witness.K k).set) := by
  obtain ⟨ρ, hρ, hv⟩ := witRhomb_corner_vol
  exact vw_witness.corner_piece one_pos witRhomb_convex hρ hv

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.witRhomb_corner_vol
#print axioms Erdos634.Draft.LaczFormal.RG.corner_piece_witness_concl
