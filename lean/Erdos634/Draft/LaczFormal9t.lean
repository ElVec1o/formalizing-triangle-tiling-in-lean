import Erdos634.Draft.LaczFormal9s
import Erdos634.Draft.LaczFormalTransportCor

/-!
# Laczkovich DM 140 (1995), Theorem 2.3: the dissection of the isosceles triangle `GFC` of Fig. 3 into congruent copies of `Δ`

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.3, Fig. 3, Lemma 2.1, Lemma 2.2), Beeson, Beeson-Zhang, Zhang.
Formalization debt, not /goal progress.

`thm23_first`: `Δ` rational with `b = 2 k a`, `c = (4k² - 1) a` (`k = cos α ∈ (1/2, 1)` rational, angles `α, 2α, π - 3α` at the vertices `0, 1, 2`).
Then the explicit triangle `T = G F C` (angles `α` at `T₀` and at `T₁`, apex `T₂`) is the union of finitely many congruent triangles similar
to `Δ` (model `scaleTri (1/q) Δ`); `thm23_any` moves this to every triangle with these two angles.
-/

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24 Erdos634.LaczL21 Erdos634.Realizable
  Erdos634.Laczkovich9n Erdos634.Laczkovich9o Erdos634.Laczkovich9r Erdos634.Laczkovich9s EuclideanGeometry

namespace Erdos634.Laczkovich9t

theorem thm23_first (R : RTri) (k : ℚ) (hk : (1 : ℚ) / 2 < k) (hk2 : k < 1)
    (hB : R.b = 2 * k * R.a) (hC : R.c = (4 * k ^ 2 - 1) * R.a) :
    ∃ (T : Tri) (q : ℕ) (hq : 0 < q) (M : ℕ)
      (C : Erdos634.RegionDissection.CongruentRegionDissection M),
      C.region = T.carrier ∧
      C.model = scaleTri (1 / (q : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hq)).ne' R.Δ ∧
      cornerAngle (T.pts 1) (T.pts 0) (T.pts 2) = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) ∧
      cornerAngle (T.pts 2) (T.pts 1) (T.pts 0) = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) := by
  obtain ⟨rb, rc, rW, rD, rG⟩ := real_facts R k hB hC
  have hcp := cR_pos hk
  have hcq : (0 : ℚ) < 4 * k ^ 2 - 1 := by nlinarith
  have hkq : (0 : ℚ) < k := by linarith
  have hra : (0 : ℚ) < R.a := R.pa
  have hWpos : 0 < qW R.a k := by unfold qW; positivity
  have hDpos : 0 < qD R.a k := by unfold qD; positivity
  have hW' : (0 : ℝ) < ((qW R.a k : ℚ) : ℝ) := by exact_mod_cast hWpos
  have hD' : (0 : ℝ) < ((qD R.a k : ℚ) : ℝ) := by exact_mod_cast hDpos
  have hk1' : ((k : ℝ)) ^ 2 < 1 := by
    have h0 : (0 : ℝ) < k := by exact_mod_cast hkq
    have h1 : (k : ℝ) < 1 := by exact_mod_cast hk2
    nlinarith
  obtain ⟨w, d, hw0, hd0, hwd0, hdet⟩ := exists_gram_chart ((qW R.a k : ℚ) : ℝ) ((qD R.a k : ℚ) : ℝ) (k : ℝ)
    hW' hD' hk1'
  have hw : inner ℝ w w = ((qW R.a k : ℚ) : ℝ) ^ 2 := hw0
  have hd : inner ℝ d d = ((qD R.a k : ℚ) : ℝ) ^ 2 := hd0
  have hwd : inner ℝ w d = ((qG R.a k : ℚ) : ℝ) := by
    rw [hwd0]; unfold qG; push_cast; ring
  set Φ := chartEquiv 0 w d hdet with hΦ
  have key := tgt_chart R k hk hB hC 0 w d hdet hw hd hwd
  obtain ⟨q, hq, M, C, hC1, hC2⟩ := RatSimDiss.toCongruent R.rational key
  have hwn : ‖w‖ = ((qW R.a k : ℚ) : ℝ) := by
    refine eq_of_sq_eq' (norm_nonneg _) hW'.le ?_
    rw [← real_inner_self_eq_norm_sq]; exact hw
  have hdn : ‖d‖ = ((qD R.a k : ℚ) : ℝ) := by
    refine eq_of_sq_eq' (norm_nonneg _) hD'.le ?_
    rw [← real_inner_self_eq_norm_sq]; exact hd
  have hcc0 : (4 * (k : ℝ) ^ 2 - 1) ≠ 0 := by rw [← cR_eq]; exact hcp.ne'
  have hk0 : (k : ℝ) ≠ 0 := by
    have : (0 : ℝ) < k := by exact_mod_cast hkq
    exact this.ne'
  have hra0 : (R.a : ℝ) ≠ 0 := by exact_mod_cast hra.ne'
  have hn0 : (4 * (k : ℝ) ^ 2 - 1) ^ 2 + 1 ≠ 0 := by positivity
  have hn1 : (cR k) ^ 2 + 1 ≠ 0 := by positivity
  have hf := wf_gt hcp
  have hh := wh_gt hcp
  -- the three vertices
  have eF : Φ (mkPt (wf (cR k)) 0) - Φ (mkPt 0 0) = wf (cR k) • w := by
    rw [hΦ, chartEquiv_apply, chartEquiv_apply]; simp only [mkPt_zero, mkPt_one]; module
  have eC : Φ (mkPt 0 (wh (cR k))) - Φ (mkPt 0 0) = wh (cR k) • d := by
    rw [hΦ, chartEquiv_apply, chartEquiv_apply]; simp only [mkPt_zero, mkPt_one]; module
  have hangG : cornerAngle (Φ (mkPt (wf (cR k)) 0)) (Φ (mkPt 0 0)) (Φ (mkPt 0 (wh (cR k))))
      = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) := by
    have h1 : ‖R.Δ.pts 1 - R.Δ.pts 0‖ = R.c := by rw [← dist_eq_norm, dist_comm]; exact R.hc
    have h2 : ‖R.Δ.pts 2 - R.Δ.pts 0‖ = R.b := by rw [← dist_eq_norm]; exact R.hb
    unfold cornerAngle EuclideanGeometry.angle
    simp only [vsub_eq_sub]
    rw [eF, eC, InnerProductGeometry.angle_smul_left_of_pos _ _ (by linarith : 0 < wf (cR k)),
      InnerProductGeometry.angle_smul_right_of_pos _ _ (by linarith : 0 < wh (cR k))]
    unfold InnerProductGeometry.angle
    rw [R.inner_uv, h1, h2, hwd0, hwn, hdn, rb, rc, rW, rD]
    congr 1
    rw [cR_eq] at hcp
    push_cast
    field_simp
    ring
  have hiso : dist (Φ (mkPt 0 (wh (cR k)))) (Φ (mkPt 0 0)) = dist (Φ (mkPt 0 (wh (cR k)))) (Φ (mkPt (wf (cR k)) 0)) := by
    refine eq_of_sq_eq' dist_nonneg dist_nonneg ?_
    rw [dist_chart_sq, dist_chart_sq, hw, hd, hwd]
    simp only [mkPt_zero, mkPt_one]
    rw [rW, rD, rG]
    simp only [wf, wh, cR_eq]
    push_cast
    field_simp
    ring
  refine ⟨Erdos634.DissectionMap.mapTri Φ (triT (cR k) hcp), q, hq, M, C, ?_, hC2, hangG, ?_⟩
  · rw [hC1, Erdos634.DissectionMap.mapTri_carrier]
  · have hb := angle_eq_angle_of_dist_eq hiso
    have hc' := angle_comm (Φ (mkPt (wf (cR k)) 0)) (Φ (mkPt 0 0)) (Φ (mkPt 0 (wh (cR k))))
    show cornerAngle (Φ (mkPt 0 (wh (cR k)))) (Φ (mkPt (wf (cR k)) 0)) (Φ (mkPt 0 0)) = _
    rw [← hangG]
    unfold cornerAngle
    exact hb.symm.trans hc'.symm

end Erdos634.Laczkovich9t

#print axioms Erdos634.Laczkovich9t.thm23_first
