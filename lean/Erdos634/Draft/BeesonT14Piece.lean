import Erdos634.Draft.BeesonT14Abs

/-!
# Beeson Theorem 14, general parameters: scaled tiles in a chart

For a tile `T0 = (0,0),(c,0),(xb,yb)` with squared sides `c^2` (01), `bb` (02), `aa` (12), and a chart
with scale `lam` and `rt0 * rt0 = D0` (chart point `(X,W)` is the plane point `(X/lam, rt0 W/lam)`), a triangle
whose chart side lengths satisfy `dX^2 + D0 dW^2 = lam^2 m^2 (side)^2` is tiled by `m^2` tiles.
Credit Beeson (arXiv 1206.2229), Beeson-Zhang, Zhang (arXiv 2512.22696), Laczkovich.  UNAUDITED.
-/

namespace Erdos634.BeesonT14Piece

open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.RegionDissection
  Erdos634.GlueCut Erdos634.SssCongruent Erdos634.ZhangL1 Erdos634.ZhangPara
  Erdos634.ZhangSporadic Erdos634.ZhangThm4 Erdos634.BeesonT14Chart Erdos634.BeesonT14Abs

theorem Dis_of_congr {R : Tri} {n : ℕ} (x0 y0 x1 y1 x2 y2 u0 v0 u1 v1 u2 v2 : ℝ)
    (hP : 0 < det3 x0 y0 x1 y1 x2 y2) (hQ : 0 < det3 u0 v0 u1 v1 u2 v2)
    (hc : (mkTri x0 y0 x1 y1 x2 y2 hP.ne').Congruent (mkTri u0 v0 u1 v1 u2 v2 hQ.ne'))
    (h : Dis R (TriSet x0 y0 x1 y1 x2 y2) n) : Dis R (TriSet u0 v0 u1 v1 u2 v2) n := by
  obtain ⟨C, hr, hm⟩ := h
  have hr' : C.region = (mkTri _ _ _ _ _ _ hP.ne').carrier := by
    rw [hr]; exact TriSet_eq_carrier hP
  obtain ⟨E, hE, hEm⟩ := Erdos634.Draft.CVCCevianCut.transport (C.toCongruentDissection _ hr') _ hc
  refine ⟨E.toRegion, ?_, hEm.trans hm⟩
  show E.target.carrier = _
  rw [hE]
  exact (TriSet_eq_carrier hQ).symm

/-- squared side table of the tile: `01 = cc`, `02 = bb`, `12 = aa` -/
noncomputable def Dt (cc bb aa : ℝ) : Fin 3 → Fin 3 → ℝ := ![![0, cc, bb], ![cc, 0, aa], ![bb, aa, 0]]

theorem Dt_diag (cc bb aa : ℝ) (i : Fin 3) : Dt cc bb aa i i = 0 := by
  fin_cases i <;> rfl
theorem Dt_symm (cc bb aa : ℝ) (i j : Fin 3) : Dt cc bb aa i j = Dt cc bb aa j i := by
  fin_cases i <;> fin_cases j <;> rfl

noncomputable def tile (c xb yb : ℝ) (h : 0 < det3 0 0 c 0 xb yb) : Tri := mkTri 0 0 c 0 xb yb h.ne'

section piece
variable {c xb yb bb aa : ℝ}

theorem tile_scaled (h0 : 0 < det3 0 0 c 0 xb yb) (m : ℕ) (hm : 0 < m) :
    Dis (tile c xb yb h0) (TriSet 0 0 (0 + m * (c - 0)) (0 + m * (0 - 0)) (0 + m * (xb - 0))
      (0 + m * (yb - 0))) (m * m) :=
  Dis_scaled 0 0 c 0 xb yb h0 (Tri.Congruent.refl _) m hm _ _ _ _ rfl rfl rfl rfl

theorem tile_scaled_dist (hbb : xb ^ 2 + yb ^ 2 = bb) (haa : (c - xb) ^ 2 + yb ^ 2 = aa) (m : ℕ)
    (hdet : 0 < det3 0 0 (0 + m * (c - 0)) (0 + m * (0 - 0)) (0 + m * (xb - 0))
      (0 + m * (yb - 0))) (i j : Fin 3) :
    dist ((mkTri 0 0 (0 + m * (c - 0)) (0 + m * (0 - 0)) (0 + m * (xb - 0))
      (0 + m * (yb - 0)) hdet.ne').pts i)
      ((mkTri 0 0 (0 + m * (c - 0)) (0 + m * (0 - 0)) (0 + m * (xb - 0))
      (0 + m * (yb - 0)) hdet.ne').pts j) ^ 2 = m * m * Dt (c * c) bb aa i j := by
  fin_cases i <;> fin_cases j <;> simp [mkTri, dist_sq_mkPt, Dt] <;> nlinarith [hbb, haa]

set_option maxHeartbeats 1000000 in
theorem Dis_piece_gen (h0 : 0 < det3 0 0 c 0 xb yb) (hbb : xb ^ 2 + yb ^ 2 = bb)
    (haa : (c - xb) ^ 2 + yb ^ 2 = aa) {lam rt0 D0 : ℝ} (hlam : 0 < lam) (hrt : 0 < rt0)
    (hD : rt0 * rt0 = D0) (m : ℕ) (hm : 0 < m) (σ : Equiv.Perm (Fin 3))
    (X0 W0 X1 W1 X2 W2 : ℝ) (hdet : 0 < detR X0 W0 X1 W1 X2 W2)
    (h01 : (X1 - X0) ^ 2 + D0 * (W1 - W0) ^ 2 = lam ^ 2 * (m * m * Dt (c * c) bb aa (σ 0) (σ 1)))
    (h02 : (X2 - X0) ^ 2 + D0 * (W2 - W0) ^ 2 = lam ^ 2 * (m * m * Dt (c * c) bb aa (σ 0) (σ 2)))
    (h12 : (X2 - X1) ^ 2 + D0 * (W2 - W1) ^ 2 = lam ^ 2 * (m * m * Dt (c * c) bb aa (σ 1) (σ 2))) :
    Dis (tile c xb yb h0) (CS (1 / lam) (rt0 / lam) (TriR X0 W0 X1 W1 X2 W2)) (m * m) := by
  have hα : 0 < 1 / lam := by positivity
  have hβ : 0 < rt0 / lam := by positivity
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hdP : 0 < det3 (1 / lam * X0) (rt0 / lam * W0) (1 / lam * X1) (rt0 / lam * W1)
      (1 / lam * X2) (rt0 / lam * W2) := by
    have : det3 (1 / lam * X0) (rt0 / lam * W0) (1 / lam * X1) (rt0 / lam * W1)
      (1 / lam * X2) (rt0 / lam * W2) = (1 / lam) * (rt0 / lam) * detR X0 W0 X1 W1 X2 W2 := by
      simp only [det3, detR]; ring
    rw [this]; positivity
  have hdQ : 0 < det3 0 0 (0 + m * (c - 0)) (0 + m * (0 - 0)) (0 + m * (xb - 0))
      (0 + m * (yb - 0)) := by
    have : det3 0 0 (0 + m * (c - 0)) (0 + m * (0 - 0)) (0 + m * (xb - 0)) (0 + m * (yb - 0))
        = (m : ℝ) ^ 2 * det3 0 0 c 0 xb yb := by simp only [det3]; ring
    rw [this]; positivity
  have key := Dis_of_congr (R := tile c xb yb h0) _ _ _ _ _ _ _ _ _ _ _ _ hdQ hdP ?_ (tile_scaled h0 m hm)
  · exact key.congr (TriSet_CS hα hβ _ _ _ _ _ _) rfl
  · refine congruent_of_sq_dist_perm σ.symm ?_
    intro i j
    have e := tile_scaled_dist hbb haa m hdQ i j
    rw [e]
    have hlam2 : lam ^ 2 ≠ 0 := by positivity
    have dd : ∀ (A B C D : ℝ), dist (mkPt (1 / lam * A) (rt0 / lam * B)) (mkPt (1 / lam * C) (rt0 / lam * D)) ^ 2
        = ((C - A) ^ 2 + D0 * (D - B) ^ 2) / lam ^ 2 := by
      intro A B C D
      rw [dist_sq_mkPt, ← hD]
      field_simp
      ring
    have P0 : (mkTri (1 / lam * X0) (rt0 / lam * W0) (1 / lam * X1) (rt0 / lam * W1) (1 / lam * X2)
        (rt0 / lam * W2) hdP.ne').pts 0 = mkPt (1 / lam * X0) (rt0 / lam * W0) := rfl
    have P1 : (mkTri (1 / lam * X0) (rt0 / lam * W0) (1 / lam * X1) (rt0 / lam * W1) (1 / lam * X2)
        (rt0 / lam * W2) hdP.ne').pts 1 = mkPt (1 / lam * X1) (rt0 / lam * W1) := rfl
    have P2 : (mkTri (1 / lam * X0) (rt0 / lam * W0) (1 / lam * X1) (rt0 / lam * W1) (1 / lam * X2)
        (rt0 / lam * W2) hdP.ne').pts 2 = mkPt (1 / lam * X2) (rt0 / lam * W2) := rfl
    have d01 := dd X0 W0 X1 W1
    have d02 := dd X0 W0 X2 W2
    have d12 := dd X1 W1 X2 W2
    rw [h01] at d01; rw [h02] at d02; rw [h12] at d12
    have q01 : lam ^ 2 * (m * m * Dt (c * c) bb aa (σ 0) (σ 1)) / lam ^ 2 = m * m * Dt (c * c) bb aa (σ 0) (σ 1) := by
      field_simp
    have q02 : lam ^ 2 * (m * m * Dt (c * c) bb aa (σ 0) (σ 2)) / lam ^ 2 = m * m * Dt (c * c) bb aa (σ 0) (σ 2) := by
      field_simp
    have q12 : lam ^ 2 * (m * m * Dt (c * c) bb aa (σ 1) (σ 2)) / lam ^ 2 = m * m * Dt (c * c) bb aa (σ 1) (σ 2) := by
      field_simp
    rw [q01] at d01; rw [q02] at d02; rw [q12] at d12
    have key : ∀ a b : Fin 3, dist ((mkTri (1 / lam * X0) (rt0 / lam * W0) (1 / lam * X1) (rt0 / lam * W1)
        (1 / lam * X2) (rt0 / lam * W2) hdP.ne').pts a) ((mkTri (1 / lam * X0) (rt0 / lam * W0)
        (1 / lam * X1) (rt0 / lam * W1) (1 / lam * X2) (rt0 / lam * W2) hdP.ne').pts b) ^ 2
        = m * m * Dt (c * c) bb aa (σ a) (σ b) := by
      intro a b
      have d10 : dist (mkPt (1 / lam * X1) (rt0 / lam * W1)) (mkPt (1 / lam * X0) (rt0 / lam * W0)) ^ 2
          = m * m * Dt (c * c) bb aa (σ 1) (σ 0) := by rw [dist_comm, Dt_symm]; exact d01
      have d20 : dist (mkPt (1 / lam * X2) (rt0 / lam * W2)) (mkPt (1 / lam * X0) (rt0 / lam * W0)) ^ 2
          = m * m * Dt (c * c) bb aa (σ 2) (σ 0) := by rw [dist_comm, Dt_symm]; exact d02
      have d21 : dist (mkPt (1 / lam * X2) (rt0 / lam * W2)) (mkPt (1 / lam * X1) (rt0 / lam * W1)) ^ 2
          = m * m * Dt (c * c) bb aa (σ 2) (σ 1) := by rw [dist_comm, Dt_symm]; exact d12
      have d00 : ∀ A B : ℝ, dist (mkPt A B) (mkPt A B) ^ 2 = m * m * Dt (c * c) bb aa (σ 0) (σ 0) := by
        intro A B; rw [Dt_diag]; simp
      have d11 : ∀ A B : ℝ, dist (mkPt A B) (mkPt A B) ^ 2 = m * m * Dt (c * c) bb aa (σ 1) (σ 1) := by
        intro A B; rw [Dt_diag]; simp
      have d22 : ∀ A B : ℝ, dist (mkPt A B) (mkPt A B) ^ 2 = m * m * Dt (c * c) bb aa (σ 2) (σ 2) := by
        intro A B; rw [Dt_diag]; simp
      match a, b with
      | 0, 0 => rw [P0]; exact d00 _ _
      | 0, 1 => rw [P0, P1]; exact d01
      | 0, 2 => rw [P0, P2]; exact d02
      | 1, 0 => rw [P0, P1]; exact d10
      | 1, 1 => rw [P1]; exact d11 _ _
      | 1, 2 => rw [P1, P2]; exact d12
      | 2, 0 => rw [P0, P2]; exact d20
      | 2, 1 => rw [P1, P2]; exact d21
      | 2, 2 => rw [P2]; exact d22 _ _
    rw [key, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end piece

end Erdos634.BeesonT14Piece
