-- Draft/RAPieces.lean — the two cevian cuts of Δ₁(e,f): `Δ₁ = West ⊔ A₁ ⊔ East` (prop:cevianatom
-- items 1-5).  Coordinates and side lengths.  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Draft.RWEast

open scoped Classical
open Erdos634.Geometry Erdos634.BaseBetaTargetCoord Erdos634.CertCoord Erdos634.Draft.RWPieces

namespace Erdos634.Draft.RAPieces

variable {e f : ℝ}

/-- wall foot `xQ = e f²`. -/
noncomputable def xQ (e f : ℝ) : ℝ := e * f ^ 2

theorem xQ_pos (he : 0 < e) (hef : e < f) : 0 < xQ e f := by
  have : 0 < f := lt_trans he hef; unfold xQ; positivity

theorem xQ_lt_xP (he : 0 < e) (hef : e < f) : xQ e f < xP e f := by
  rw [xP_eq]; unfold xQ; nlinarith [mul_pos he (by nlinarith : 0 < f ^ 2 - e ^ 2)]

theorem det_west (he : 0 < e) (hef : e < f) :
    det3 (baseLen e f / 2) (height e f) 0 0 (xQ e f) 0 ≠ 0 := by
  have := mul_pos (xQ_pos he hef) (height_pos he hef)
  unfold det3; nlinarith

theorem det_mid (he : 0 < e) (hef : e < f) :
    det3 (baseLen e f / 2) (height e f) (xQ e f) 0 (baseLen e f) 0 ≠ 0 := by
  have h1 := lt_trans (xQ_lt_xP he hef) (xP_lt he hef)
  have := mul_pos (sub_pos.mpr h1) (height_pos he hef)
  unfold det3; nlinarith

theorem det_atom (he : 0 < e) (hef : e < f) :
    det3 (baseLen e f / 2) (height e f) (xQ e f) 0 (xP e f) 0 ≠ 0 := by
  have := mul_pos (sub_pos.mpr (xQ_lt_xP he hef)) (height_pos he hef)
  unfold det3; nlinarith

/-- `(A, W, Q)`. -/
noncomputable def westTri (he : 0 < e) (hef : e < f) : Tri :=
  mkTri (baseLen e f / 2) (height e f) 0 0 (xQ e f) 0 (det_west he hef)

/-- `(A, Q, E)`. -/
noncomputable def midTri (he : 0 < e) (hef : e < f) : Tri :=
  mkTri (baseLen e f / 2) (height e f) (xQ e f) 0 (baseLen e f) 0 (det_mid he hef)

/-- The atom `(A, Q, P)`. -/
noncomputable def atomTri (he : 0 < e) (hef : e < f) : Tri :=
  mkTri (baseLen e f / 2) (height e f) (xQ e f) 0 (xP e f) 0 (det_atom he hef)

theorem d_WQ (he : 0 < e) (hef : e < f) :
    dist (mkPt 0 0) (mkPt (xQ e f) 0) = e * f ^ 2 := by
  have hf : 0 < f := lt_trans he hef
  refine eq_of_sq_eq dist_nonneg (by positivity) ?_
  rw [dist_sq_mkPt]; unfold xQ; ring

theorem d_QP (he : 0 < e) (hef : e < f) :
    dist (mkPt (xQ e f) 0) (mkPt (xP e f) 0) = e * (f ^ 2 - e ^ 2) := by
  have hf : 0 < f := lt_trans he hef
  refine eq_of_sq_eq dist_nonneg (mul_nonneg he.le (by nlinarith)) ?_
  rw [dist_sq_mkPt, xP_eq]; unfold xQ; ring

theorem d_AQ (he : 0 < e) (hef : e < f) :
    dist (mkPt (baseLen e f / 2) (height e f)) (mkPt (xQ e f) 0) = f * (f ^ 2 - e ^ 2) := by
  have hf : 0 < f := lt_trans he hef
  have hD := sq_sqrtD he hef
  refine eq_of_sq_eq dist_nonneg (mul_nonneg hf.le (by nlinarith)) ?_
  rw [dist_sq_mkPt]
  have hH : height e f ^ 2 = (f ^ 2 - e ^ 2) ^ 2 * (4 * f ^ 2 - e ^ 2) / 4 := by
    unfold height
    rw [div_pow, mul_pow, hD]; unfold Dr; ring
  have hx : baseLen e f / 2 - xQ e f = e * (f ^ 2 - e ^ 2) / 2 := by
    unfold xQ baseLen Nq; ring
  rw [hx]
  have : (height e f - 0) ^ 2 = height e f ^ 2 := by ring
  rw [this, hH]; ring

end Erdos634.Draft.RAPieces

#print axioms Erdos634.Draft.RAPieces.d_AQ
