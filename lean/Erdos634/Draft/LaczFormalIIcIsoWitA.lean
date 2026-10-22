-- Draft/LaczFormalIIcIsoWitA.lean -- NON-VACUITY witness for `IIcIsoCore` (Laczkovich, DCG 48 (2012), Thm 2.1, Case IIc, alpha = beta), step A: the regular octagon,
-- coordinates and numerics.  Vertices V k = (cos(k pi/4), sin(k pi/4)), k : Fin 8, centre O = (0,0); tile i = triangle (V i, V (i+1), O) (apex pi/4 at O, base angles 3 pi/8).
-- NOTE, UNAUDITED.  Credit: Laczkovich (DCG 48 (2012)), Beeson, Beeson-Zhang.
import Erdos634.CertCoord
import Erdos634.Draft.LaczFormalThm21Def

open Erdos634.Geometry Erdos634.CertCoord

namespace Erdos634.Draft.LaczFormal.IsoWit

/-- `h = sqrt 2 / 2`. -/
noncomputable def hh : ℝ := Real.sqrt 2 / 2
theorem hh_pos : 0 < hh := by unfold hh; positivity
theorem hh_sq : hh * hh = 1 / 2 := by
  unfold hh; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]

noncomputable def cx : Fin 8 → ℝ := ![1, hh, 0, -hh, -1, -hh, 0, hh]
noncomputable def cy : Fin 8 → ℝ := ![0, hh, 1, hh, 0, -hh, -1, -hh]

theorem cxy_sq (a : Fin 8) : cx a * cx a + cy a * cy a = 1 := by
  fin_cases a <;> simp [cx, cy] <;> nlinarith [hh_sq]

theorem cx_add4 (a : Fin 8) : cx (a + 4) = - cx a := by
  fin_cases a <;> simp [cx] <;> decide
theorem cy_add4 (a : Fin 8) : cy (a + 4) = - cy a := by
  fin_cases a <;> simp [cy] <;> decide


/-- cross product of two vertices -/
noncomputable def cr (a b : Fin 8) : ℝ := cx a * cy b - cy a * cx b

theorem cr_1 (a : Fin 8) : cr a (a + 1) = hh := by
  fin_cases a <;> simp [cr, cx, cy] <;> nlinarith [hh_sq]
theorem cr_3 (a : Fin 8) : cr a (a + 3) = hh := by
  fin_cases a <;> simp [cr, cx, cy] <;> nlinarith [hh_sq]
theorem cr_5 (a : Fin 8) : cr a (a + 5) = -hh := by
  fin_cases a <;> simp [cr, cx, cy] <;> nlinarith [hh_sq]
theorem cr_7 (a : Fin 8) : cr a (a + 7) = -hh := by
  fin_cases a <;> simp [cr, cx, cy] <;> nlinarith [hh_sq]

theorem V_inj {a b : Fin 8} (hx : cx a = cx b) (hy : cy a = cy b) : a = b := by
  fin_cases a <;> fin_cases b <;> simp [cx, cy] at hx hy ⊢ <;> first | rfl | (exfalso; nlinarith [hh_pos, hh_sq]) | skip

theorem mkPt_inj {a b c d : ℝ} (h : mkPt a b = mkPt c d) : a = c ∧ b = d := by
  have h0 := congrArg (fun p : Plane => p 0) h
  have h1 := congrArg (fun p : Plane => p 1) h
  simp at h0 h1
  exact ⟨h0, h1⟩

end Erdos634.Draft.LaczFormal.IsoWit
