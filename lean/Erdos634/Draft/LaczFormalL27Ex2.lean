import Erdos634.Draft.LaczFormalL27Ex

/-!
# Laczkovich Theorem 2.4, triples 2, 3, 5: the explicit big triangles

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.4, Fig. 5), Beeson, Beeson-Zhang, Zhang.
-/

namespace Erdos634.LaczL27

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24 Erdos634.LaczL26 EuclideanGeometry

variable {a : ℝ}

theorem xL_neg (h : Hyp0 a) : xL a < 0 := by
  have h1 := h.ha; have h2 := h.hb; have h3 := h.hK
  unfold xL; have : 0 < a ^ 2 * gK a / gb a := by positivity
  linarith

theorem sR_pos (h : Hyp0 a) : 0 < sR a := by
  have h1 := h.ha; have h3 := h.hK
  unfold sR; positivity

theorem sR_lt_xY (h : Hyp0 a) : sR a < xY a := by
  have h1 := h.ha; have h2 := h.hb; have h3 := h.hK
  unfold xY sR; have : 0 < a ^ 2 * gK a / gb a := by positivity
  linarith

theorem det_B5 (h : Hyp0 a) : det3 (sP a) (tP a) (xL a) 0 (sR a) 0 ≠ 0 := by
  have e : det3 (sP a) (tP a) (xL a) 0 (sR a) 0 = tP a * (sR a - xL a) := by unfold det3; ring
  rw [e]
  have := h.hK; have := xL_neg h; have := sR_pos h
  have : 0 < tP a := by unfold tP; exact h.hK
  have : 0 < sR a - xL a := by linarith
  positivity

theorem det_B2 (h : Hyp0 a) : det3 (sP a) (tP a) (xL a) 0 (xY a) 0 ≠ 0 := by
  have e : det3 (sP a) (tP a) (xL a) 0 (xY a) 0 = tP a * (xY a - xL a) := by unfold det3; ring
  rw [e]
  have : 0 < tP a := by unfold tP; exact h.hK
  have : 0 < xY a - xL a := by linarith [xL_neg h, xY_pos h]
  positivity

theorem det_B3_eq (h : Hyp0 a) :
    det3 (xY a) 0 (sP a) (tP a) (vX a) (vY a) = a ^ 2 * (3 - a ^ 2) * (2 - a ^ 2) * gK a ^ 2 / gb a := by
  have hb := h.hb.ne'
  unfold det3 xY sP tP vX vY gb gK at *; field_simp; ring

theorem det_B3 (h : Hyp0 a) : det3 (xY a) 0 (sP a) (tP a) (vX a) (vY a) ≠ 0 := by
  rw [det_B3_eq h]
  have h1 := h.ha; have h2 := h.hb; have h3 := h.hK
  have h4 : 0 < 3 - a ^ 2 := by unfold gb at h2; nlinarith
  have h5 : 0 < 2 - a ^ 2 := by unfold gb at h2; nlinarith
  positivity

noncomputable def B5 (h : Hyp0 a) : Tri := mkTri (sP a) (tP a) (xL a) 0 (sR a) 0 (det_B5 h)
noncomputable def B2 (h : Hyp0 a) : Tri := mkTri (sP a) (tP a) (xL a) 0 (xY a) 0 (det_B2 h)

theorem B5_carrier (h : Hyp0 a) :
    (B5 h).carrier = (hfan (sP a) (tP a) h.hK (show xL a ≠ sR a from ((xL_neg h).trans (sR_pos h)).ne)).carrier := by
  refine carrier_eq_of_range ?_
  rw [hfan_range]; unfold B5; rw [mkTri_pts, range_mk3]

theorem B2_carrier (h : Hyp0 a) :
    (B2 h).carrier = (hfan (sP a) (tP a) h.hK (show xL a ≠ xY a from ((xL_neg h).trans (sR_pos h |>.trans (sR_lt_xY h))).ne)).carrier := by
  refine carrier_eq_of_range ?_
  rw [hfan_range]; unfold B2; rw [mkTri_pts, range_mk3]

noncomputable def B3 (h : Hyp0 a) : Tri := mkTri (xY a) 0 (sP a) (tP a) (vX a) (vY a) (det_B3 h)

theorem B3_carrier (h : Hyp0 a) :
    (B3 h).carrier = (fA h (show -gK a ≠ cL a from (by
        have := h.hK; have := h.hb
        unfold cL; unfold gb at *; unfold gK at *; nlinarith [sq_nonneg a] : -gK a < cL a).ne)).carrier := by
  refine carrier_eq_of_range ?_
  rw [fA_range]; unfold B3; rw [mkTri_pts, range_mk3]
  have e1 : mkPt (0 + -gK a * gb a) (0 + -gK a * -1) = mkPt (sP a) (tP a) := by
    congr 1 <;> (try simp only [sP, tP]) <;> ring
  have e2 : mkPt (0 + cL a * gb a) (0 + cL a * (-1)) = mkPt (vX a) (vY a) := by
    congr 1 <;> (try simp only [cL, vX, vY]) <;> ring
  rw [e1, e2]

end Erdos634.LaczL27
