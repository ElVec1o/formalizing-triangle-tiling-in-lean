import Erdos634.Draft.LaczFormalL26Main

/-!
# Laczkovich Theorem 2.4, fourth triple `(α, α+β, α+β)`, in the range `N(a₀) > 0`

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.4, Fig. 5), Beeson (arXiv 1206.2229,
Sect. 13.3, Theorem 23 and Lemma 52), Beeson-Zhang, Zhang.

PRINT GAP: the paper says only "Similar constructions apply for the other triples listed in (1); see Fig. 5".  The first
picture of Fig. 5 (tall isosceles triangle, apex `α`, base angles `α+β`) is the construction formalized here; its pieces
lie inside the target exactly when `N(a₀) = a₀⁶ - 2a₀⁴ + 3a₀² - 1 > 0`, i.e. `(b/c)³ < (1 - b/c)²`, `b/c < 0.5698...`
(Beeson, Theorem 23 / Lemma 52); for `a₀` with `N(a₀) < 0` the pictured pieces leave the target.
-/

namespace Erdos634.LaczL26

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL21 Erdos634.LaczL24 Erdos634.Realizable

theorem gram2 (w d : Plane) (p q p' q' : ℝ) :
    inner ℝ (p • w + q • d) (p' • w + q' • d)
      = p * p' * inner ℝ w w + (p * q' + q * p') * inner ℝ w d + q * q' * inner ℝ d d := by
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm d w]; ring

theorem norm_comb (w d : Plane) (p q x : ℝ) (hx : 0 ≤ x)
    (h : inner ℝ (p • w + q • d) (p • w + q • d) = x ^ 2) : ‖p • w + q • d‖ = x :=
  eq_of_sq_eq' (norm_nonneg _) hx (by rw [← real_inner_self_eq_norm_sq]; exact h)

set_option maxHeartbeats 2000000 in
/-- **Laczkovich Theorem 2.4, fourth triple `(α, α+β, α+β)`, for `N(a₀) > 0`.**  `Δ = (a, b, c)` a rational tile with
`a = a₀ c`, `b = (1 - a₀²) c` (`3α + 2β = π`, `a₀ = 2 sin(α/2) ∈ (0,1)`), and `a₀⁶ - 2a₀⁴ + 3a₀² - 1 > 0` (equivalently
`(b/c)³ < (1 - b/c)²`).  Then the isosceles triangle `T = L R P` (apex `P = T₂` with angle `α`, base angles `α+β`) is the union
of finitely many congruent triangles similar to `Δ`. -/
theorem thm24_fourth (R : RTri) (a0 : ℚ) (ha0 : 0 < a0) (ha1 : a0 < 1)
    (hA : R.a = a0 * R.c) (hB : R.b = (1 - a0 ^ 2) * R.c)
    (hN : 0 < a0 ^ 4 - (1 - a0 ^ 2) ^ 3) :
    ∃ (T : Tri) (q : ℕ) (hq : 0 < q) (M : ℕ)
      (C : Erdos634.RegionDissection.CongruentRegionDissection M),
      C.region = T.carrier ∧
      C.model = scaleTri (1 / (q : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hq)).ne' R.Δ ∧
      dist (T.pts 2) (T.pts 0) = dist (T.pts 2) (T.pts 1) ∧
      cornerAngle (T.pts 0) (T.pts 2) (T.pts 1)
        = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) := by
  have hc := R.pc
  have ha0r : (0 : ℝ) < a0 := by exact_mod_cast ha0
  have ha1r : (a0 : ℝ) < 1 := by exact_mod_cast ha1
  have hb0q : (0 : ℚ) < 1 - a0 ^ 2 := by nlinarith
  have hb0r : (0 : ℝ) < 1 - (a0 : ℝ) ^ 2 := by exact_mod_cast hb0q
  have hcr : (0 : ℝ) < R.c := by exact_mod_cast hc
  have hupos : (0 : ℚ) < R.c / (a0 * (1 - a0 ^ 2)) := by positivity
  have hcos2 : (((2 - (a0 : ℝ) ^ 2) / 2) : ℝ) ^ 2 < 1 := by nlinarith
  obtain ⟨w1, d1, hw0, hd0, hwd0, hdet⟩ := exists_gram_chart
    (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ))
    ((2 - (a0 : ℝ) ^ 2) / 2) (by exact_mod_cast hupos) (by exact_mod_cast hupos) hcos2
  have hwd : inner ℝ w1 d1 = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2 * (2 - (a0 : ℝ) ^ 2) / 2 := by
    rw [hwd0]; ring
  have key := fourth_chart R a0 ha0 ha1 hA hB hN w1 d1 hdet hw0 hd0 hwd
  have hyp := hyp_of_q a0 ha0 ha1 hN
  unfold ChartRSD at key
  obtain ⟨q, hq, M, C, hC1, hC2⟩ := RatSimDiss.toCongruent R.rational key
  set U : ℝ := (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) with hUdef
  have hUpos : 0 < U := by rw [hUdef]; exact_mod_cast hupos
  have hAr : (R.a : ℝ) = a0 * R.c := by exact_mod_cast hA
  have hBr : (R.b : ℝ) = (1 - (a0 : ℝ) ^ 2) * R.c := by exact_mod_cast hB
  have hUab : U * ((a0 : ℝ) * (1 - (a0 : ℝ) ^ 2)) = R.c := by
    rw [hUdef]; push_cast; field_simp
  have hKpos : 0 < gK (a0 : ℝ) := hyp.hK
  refine ⟨Erdos634.DissectionMap.mapTri (chartEquiv 0 w1 d1 hdet) (triT hyp), q, hq, M, C, ?_, hC2, ?_, ?_⟩
  · rw [hC1, Erdos634.DissectionMap.mapTri_carrier]
  · -- isosceles at the apex
    refine eq_of_sq_eq' dist_nonneg dist_nonneg ?_
    show dist (chartEquiv 0 w1 d1 hdet (mkPt (sP (a0 : ℝ)) (tP (a0 : ℝ)))) (chartEquiv 0 w1 d1 hdet (mkPt 0 0)) ^ 2
      = dist (chartEquiv 0 w1 d1 hdet (mkPt (sP (a0 : ℝ)) (tP (a0 : ℝ))))
        (chartEquiv 0 w1 d1 hdet (mkPt (sR (a0 : ℝ)) 0)) ^ 2
    rw [dist_chart_sq, dist_chart_sq]
    simp only [mkPt_zero, mkPt_one]
    rw [hw0, hd0, hwd]
    unfold sP tP sR gb gK
    ring
  · -- the apex angle
    have e1 : chartEquiv 0 w1 d1 hdet (mkPt 0 0) - chartEquiv 0 w1 d1 hdet (mkPt (sP (a0 : ℝ)) (tP (a0 : ℝ)))
        = (-(sP (a0 : ℝ))) • w1 + (-(tP (a0 : ℝ))) • d1 := by
      rw [chartEquiv_apply, chartEquiv_apply]; simp only [mkPt_zero, mkPt_one]; module
    have e2 : chartEquiv 0 w1 d1 hdet (mkPt (sR (a0 : ℝ)) 0)
        - chartEquiv 0 w1 d1 hdet (mkPt (sP (a0 : ℝ)) (tP (a0 : ℝ)))
        = (sR (a0 : ℝ) - sP (a0 : ℝ)) • w1 + (-(tP (a0 : ℝ))) • d1 := by
      rw [chartEquiv_apply, chartEquiv_apply]; simp only [mkPt_zero, mkPt_one]; module
    have hKa : 0 ≤ U * gK (a0 : ℝ) * a0 := by positivity
    have n1 : ‖(-(sP (a0 : ℝ))) • w1 + (-(tP (a0 : ℝ))) • d1‖ = U * gK (a0 : ℝ) * a0 := by
      refine norm_comb w1 d1 _ _ _ hKa ?_
      rw [gram2, hw0, hd0, hwd]
      unfold sP tP gb gK; ring
    have n2 : ‖(sR (a0 : ℝ) - sP (a0 : ℝ)) • w1 + (-(tP (a0 : ℝ))) • d1‖ = U * gK (a0 : ℝ) * a0 := by
      refine norm_comb w1 d1 _ _ _ hKa ?_
      rw [gram2, hw0, hd0, hwd]
      unfold sR sP tP gb gK; ring
    have h1 : ‖R.Δ.pts 1 - R.Δ.pts 0‖ = R.c := by rw [← dist_eq_norm, dist_comm]; exact R.hc
    have h2 : ‖R.Δ.pts 2 - R.Δ.pts 0‖ = R.b := by rw [← dist_eq_norm]; exact R.hb
    show EuclideanGeometry.angle (chartEquiv 0 w1 d1 hdet (mkPt 0 0))
        (chartEquiv 0 w1 d1 hdet (mkPt (sP (a0 : ℝ)) (tP (a0 : ℝ))))
        (chartEquiv 0 w1 d1 hdet (mkPt (sR (a0 : ℝ)) 0))
      = EuclideanGeometry.angle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2)
    unfold EuclideanGeometry.angle
    simp only [vsub_eq_sub]
    rw [e1, e2]
    unfold InnerProductGeometry.angle
    rw [n1, n2, R.inner_uv, h1, h2, gram2, hw0, hd0, hwd, hAr, hBr]
    congr 1
    have hK0 : gK (a0 : ℝ) ≠ 0 := hKpos.ne'
    have hU0 : U ≠ 0 := hUpos.ne'
    have hb0 : (1 - (a0 : ℝ) ^ 2) ≠ 0 := hb0r.ne'
    have ha00 : (a0 : ℝ) ≠ 0 := ha0r.ne'
    have hc0 : (R.c : ℝ) ≠ 0 := hcr.ne'
    rw [← hUab]
    unfold sR sP tP gb gK
    unfold gK at hK0
    field_simp
    ring

end Erdos634.LaczL26
