-- Draft/LaczFormalIVcRatB7w.lean -- witness and control for `VWTiling.row_of_rhombi` (B7j).
--   Witness: the one-rhombus VWTiling `vw_witness` (b = 1, A = witRhomb.set = Par 0 s w with s = (1,0), w = (1/2, sqrt 3/2)) with the frame X = 0, p = s, q = w: A is convex with nonempty interior, inside the quadrant
--   {fa >= 0, fb >= 0}, X in A, so the hypotheses of `row_of_rhombi` hold; `row_witness` is the conclusion (a row of at least one rhombus, ending on the ray).  No kites occur in the witness (as in B4/B5/B6): the kite branches of the proof are exercised only abstractly.
--   Control: the frame at the other corner of the side (X' = s, same p, q) violates the quadrant hypothesis (`row_control`): the hypothesis `hquad` is not trivially true.
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012), Sect. 8.3), Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalIVcRatB7j
import Erdos634.Draft.LaczFormalIVcRatB6w

open scoped Classical Fin.NatCast
open Erdos634.Geometry Erdos634.RegionDissection Erdos634.Draft.LaczFormal.Graph Erdos634.Draft.LaczFormal.Thm21 Erdos634.TilePlacement Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.RG

private theorem s3sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

/-- The frame of the witness: `U = 0`, `p = (1,0)`, `q = (1/2, sqrt 3 / 2)`, `b = 1`. -/
noncomputable def witFrame : Frame 1 where
  U0 := 0
  U1 := 0
  p0 := 1
  p1 := 0
  q0 := 1 / 2
  q1 := Real.sqrt 3 / 2
  hp := by norm_num
  hq := by
    have h4 : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by rw [div_pow, s3sq]; norm_num
    rw [h4]; norm_num
  hpq := by norm_num

/-- The frame at the corner `s` of the side (control). -/
noncomputable def witFrame' : Frame 1 := { witFrame with U0 := 1 }

theorem witRhomb_fa_fb {y : Plane} (hy : y ∈ witRhomb.set) : 0 ≤ witFrame.fa y ∧ 0 ≤ witFrame.fb y := by
  obtain ⟨l, m, hl, hl1, hm, hm1, e0, e1⟩ := hy
  have := witFrame.fa_fb_of one_pos (y := y) (a := l) (β := m) (by rw [e0]; simp [witFrame, witRhomb]) (by rw [e1]; simp [witFrame, witRhomb])
  rw [this.1, this.2]; exact ⟨hl, hm⟩

theorem witRhomb_interior : (interior witRhomb.set).Nonempty := by
  obtain ⟨x, hx⟩ := (witRhomb.cell 0).interior_nonempty
  exact ⟨x, interior_mono (witRhomb.cell_subset 0) hx⟩

theorem witFrame_pt_zero_mem : witFrame.pt 0 0 ∈ witRhomb.set :=
  ⟨0, 0, le_rfl, by norm_num, le_rfl, by norm_num, by simp [Frame.pt_zero, witFrame, witRhomb], by simp [Frame.pt_one, witFrame, witRhomb]⟩

/-- **Witness**: the hypotheses of `row_of_rhombi` hold and so does its conclusion. -/
theorem row_witness : ∃ k : ℕ, 1 ≤ k ∧ (∀ i : ℕ, i < k → ∃ r, (vw_witness.R r).set = VWTiling.rowPar witFrame i) ∧
    witFrame.pt (k : ℝ) 0 ∈ witRhomb.set ∧ ∀ t : ℝ, (k : ℝ) < t → witFrame.pt t 0 ∉ witRhomb.set :=
  vw_witness.row_of_rhombi one_pos (Par_convex _ _ _ _ _ _) witFrame (fun y hy => witRhomb_fa_fb hy) witFrame_pt_zero_mem witRhomb_interior

/-- **Control**: at the other corner of the side the quadrant hypothesis fails (the point `0` has `fa = -1`). -/
theorem row_control : ¬ ∀ y ∈ witRhomb.set, 0 ≤ witFrame'.fa y ∧ 0 ≤ witFrame'.fb y := by
  intro h
  have h0 : (0 : Plane) ∈ witRhomb.set := by
    have := witFrame_pt_zero_mem
    have e : witFrame.pt 0 0 = 0 := by
      apply plane_ext' <;> simp [Frame.pt_zero, Frame.pt_one, witFrame]
    rwa [e] at this
  have := (h 0 h0).1
  have hD : witFrame'.D ≠ 0 := witFrame'.D_ne one_pos
  have e : witFrame'.fa 0 = -1 := by
    unfold Frame.fa Frame.D
    have hs : Real.sqrt 3 ≠ 0 := by positivity
    simp [witFrame', witFrame]
  rw [e] at this
  norm_num at this

end Erdos634.Draft.LaczFormal.RG

#print axioms Erdos634.Draft.LaczFormal.RG.row_witness
#print axioms Erdos634.Draft.LaczFormal.RG.row_control
