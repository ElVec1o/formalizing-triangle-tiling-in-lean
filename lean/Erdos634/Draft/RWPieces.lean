-- Draft/RWPieces.lean — coordinates and side lengths of the cevian cut of the base-β target
-- `Δ₁(e,f)`: `Δ₁ = W₁ ⊔ East` (prop:cevianatom, Steps 1-2).  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.BaseBetaTargetCoord
import Erdos634.CertCoord
import Erdos634.Draft.RWGlue

open scoped Classical
open Erdos634.Geometry Erdos634.BaseBetaTargetCoord Erdos634.CertCoord

namespace Erdos634.Draft.RWPieces

theorem eq_of_sq_eq {d v : ℝ} (hd : 0 ≤ d) (hv : 0 ≤ v) (h : d ^ 2 = v ^ 2) : d = v := by
  nlinarith [sq_nonneg (d - v), sq_nonneg (d + v)]

variable {e f : ℝ}

/-- cut foot: `xP = L − e f²`. -/
noncomputable def xP (e f : ℝ) : ℝ := baseLen e f - e * f ^ 2

theorem xP_eq (e f : ℝ) : xP e f = e * (2 * f ^ 2 - e ^ 2) := by
  unfold xP baseLen Nq; ring

theorem xP_pos (he : 0 < e) (hef : e < f) : 0 < xP e f := by
  rw [xP_eq]; have : 0 < f := lt_trans he hef
  exact mul_pos he (by nlinarith)

theorem xP_lt (he : 0 < e) (hef : e < f) : xP e f < baseLen e f := by
  unfold xP; have : 0 < f := lt_trans he hef; nlinarith [mul_pos he (pow_pos this 2)]

theorem det_w (he : 0 < e) (hef : e < f) :
    det3 (baseLen e f / 2) (height e f) 0 0 (xP e f) 0 ≠ 0 := by
  have := mul_pos (xP_pos he hef) (height_pos he hef)
  unfold det3; nlinarith

theorem det_e (he : 0 < e) (hef : e < f) :
    det3 (baseLen e f / 2) (height e f) (xP e f) 0 (baseLen e f) 0 ≠ 0 := by
  have := mul_pos (sub_pos.mpr (xP_lt he hef)) (height_pos he hef)
  unfold det3; nlinarith

/-- The west piece `W₁ = (A, W, P)`. -/
noncomputable def wTri (he : 0 < e) (hef : e < f) : Tri :=
  mkTri (baseLen e f / 2) (height e f) 0 0 (xP e f) 0 (det_w he hef)

/-- The east piece `(A, P, E)`. -/
noncomputable def eTri (he : 0 < e) (hef : e < f) : Tri :=
  mkTri (baseLen e f / 2) (height e f) (xP e f) 0 (baseLen e f) 0 (det_e he hef)

theorem d_AW (he : 0 < e) (hef : e < f) :
    dist (mkPt (baseLen e f / 2) (height e f)) (mkPt 0 0) = f ^ 3 := by
  rw [dist_comm]; exact dist_leg₀ he hef

theorem d_AE (he : 0 < e) (hef : e < f) :
    dist (mkPt (baseLen e f / 2) (height e f)) (mkPt (baseLen e f) 0) = f ^ 3 := by
  rw [dist_comm]; exact dist_leg₁ he hef

theorem d_WP (he : 0 < e) (hef : e < f) :
    dist (mkPt 0 0) (mkPt (xP e f) 0) = e * (2 * f ^ 2 - e ^ 2) := by
  have hx := xP_pos he hef
  have hf : 0 < f := lt_trans he hef
  refine eq_of_sq_eq dist_nonneg (by rw [← xP_eq]; exact hx.le) ?_
  rw [dist_sq_mkPt, ← xP_eq]; ring

theorem d_PE (he : 0 < e) (hef : e < f) :
    dist (mkPt (xP e f) 0) (mkPt (baseLen e f) 0) = e * f ^ 2 := by
  have hf : 0 < f := lt_trans he hef
  refine eq_of_sq_eq dist_nonneg (by positivity) ?_
  rw [dist_sq_mkPt]
  have : baseLen e f - xP e f = e * f ^ 2 := by unfold xP; ring
  have h2 : (xP e f - baseLen e f) ^ 2 = (e * f ^ 2) ^ 2 := by rw [← this]; ring
  rw [h2]; ring

theorem d_AP (he : 0 < e) (hef : e < f) :
    dist (mkPt (baseLen e f / 2) (height e f)) (mkPt (xP e f) 0) = f * (f ^ 2 - e ^ 2) := by
  have hf : 0 < f := lt_trans he hef
  have hD := sq_sqrtD he hef
  refine eq_of_sq_eq dist_nonneg (mul_nonneg hf.le (by nlinarith)) ?_
  rw [dist_sq_mkPt]
  have hH : height e f ^ 2 = (f ^ 2 - e ^ 2) ^ 2 * (4 * f ^ 2 - e ^ 2) / 4 := by
    unfold height
    rw [div_pow, mul_pow, hD]; unfold Dr; ring
  have hx : baseLen e f / 2 - xP e f = -(e * (f ^ 2 - e ^ 2) / 2) := by
    rw [xP_eq]; unfold baseLen Nq; ring
  rw [hx]
  have : (height e f - 0) ^ 2 = height e f ^ 2 := by ring
  rw [this, hH]; ring

end Erdos634.Draft.RWPieces

#print axioms Erdos634.Draft.RWPieces.d_AP
