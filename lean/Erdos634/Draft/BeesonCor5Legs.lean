import Erdos634.Draft.BeesonCor5

/-!
# Beeson Corollary 5 with the legs exported (for Corollary 6)

NOTE, UNAUDITED.  Credit: Beeson (arXiv 1206.2229, Cor 5, Cor 6, Thm 23, Thm 24), Laczkovich (Discrete Math. 140
(1995); DCG 48 (2012)), Beeson-Zhang, Zhang.

Cor 6's proof uses Cor 5's isosceles triangle "with legs of length `L` say" and then integer ratios `L(b+c)`, `L c`.
`cor5` (BeesonCor5) does not export the legs.  Here both branches export them: the leg `l0` of the tiled triangle and the
tile scale `s` satisfy `l0 * rr = pp * s` with naturals `pp, rr > 0`, i.e. `l0 / s = pp / rr` is RATIONAL (it is the leg in
units of the integer tile `(a,b,c)`).  Thm 24 branch: `s = 1`, `l0 = mu c` natural.  Fourth-triple branch: `s = 1/q`,
`l0 = (a^2+b^2)/b` (copy of `thm24_fourth` with one more conjunct, the chart norm).
-/

namespace Erdos634.LaczL26

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL21 Erdos634.LaczL24 Erdos634.Realizable

set_option maxHeartbeats 2000000 in
/-- **Laczkovich Theorem 2.4, fourth triple `(α, α+β, α+β)`, for `N(a₀) > 0`.**  `Δ = (a, b, c)` a rational tile with
`a = a₀ c`, `b = (1 - a₀²) c` (`3α + 2β = π`, `a₀ = 2 sin(α/2) ∈ (0,1)`), and `a₀⁶ - 2a₀⁴ + 3a₀² - 1 > 0` (equivalently
`(b/c)³ < (1 - b/c)²`).  Then the isosceles triangle `T = L R P` (apex `P = T₂` with angle `α`, base angles `α+β`) is the union
of finitely many congruent triangles similar to `Δ`. -/
theorem thm24_fourth_legs (R : RTri) (a0 : ℚ) (ha0 : 0 < a0) (ha1 : a0 < 1)
    (hA : R.a = a0 * R.c) (hB : R.b = (1 - a0 ^ 2) * R.c)
    (hN : 0 < a0 ^ 4 - (1 - a0 ^ 2) ^ 3) :
    ∃ (T : Tri) (q : ℕ) (hq : 0 < q) (M : ℕ)
      (C : Erdos634.RegionDissection.CongruentRegionDissection M),
      C.region = T.carrier ∧
      C.model = scaleTri (1 / (q : ℝ)) (one_div_pos.mpr (Nat.cast_pos.mpr hq)).ne' R.Δ ∧
      dist (T.pts 2) (T.pts 0) = dist (T.pts 2) (T.pts 1) ∧
      cornerAngle (T.pts 0) (T.pts 2) (T.pts 1)
        = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) ∧
      dist (T.pts 2) (T.pts 0) * (R.b : ℝ) = (R.a : ℝ) ^ 2 + (R.b : ℝ) ^ 2 := by
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
  refine ⟨Erdos634.DissectionMap.mapTri (chartEquiv 0 w1 d1 hdet) (triT hyp), q, hq, M, C, ?_, hC2, ?_, ?_, ?_⟩
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
  · -- the leg length: `leg * b = a^2 + b^2`
    have e1 : chartEquiv 0 w1 d1 hdet (mkPt 0 0) - chartEquiv 0 w1 d1 hdet (mkPt (sP (a0 : ℝ)) (tP (a0 : ℝ)))
        = (-(sP (a0 : ℝ))) • w1 + (-(tP (a0 : ℝ))) • d1 := by
      rw [chartEquiv_apply, chartEquiv_apply]; simp only [mkPt_zero, mkPt_one]; module
    have hKa : 0 ≤ U * gK (a0 : ℝ) * a0 := by positivity
    have n1 : ‖(-(sP (a0 : ℝ))) • w1 + (-(tP (a0 : ℝ))) • d1‖ = U * gK (a0 : ℝ) * a0 := by
      refine norm_comb w1 d1 _ _ _ hKa ?_
      rw [gram2, hw0, hd0, hwd]
      unfold sP tP gb gK; ring
    show dist (chartEquiv 0 w1 d1 hdet (mkPt (sP (a0 : ℝ)) (tP (a0 : ℝ)))) (chartEquiv 0 w1 d1 hdet (mkPt 0 0))
      * (R.b : ℝ) = _
    rw [dist_comm, dist_eq_norm, e1, n1, hAr, hBr]
    have : U * gK (a0 : ℝ) * a0 * ((1 - (a0 : ℝ) ^ 2) * R.c)
        = (U * ((a0 : ℝ) * (1 - (a0 : ℝ) ^ 2))) * gK (a0 : ℝ) * R.c := by ring
    rw [this, hUab]
    unfold gK; ring

end Erdos634.LaczL26

namespace Erdos634.BeesonCor5Legs

open Erdos634.Geometry Erdos634.CertCoord Erdos634.RegionDissection Erdos634.ZhangPara Erdos634.ZhangSporadic
  Erdos634.LaczL22 Erdos634.BeesonT24Exists Erdos634.Realizable Erdos634.LaczL24 Erdos634.BeesonCor5

/-- Cor 5, Thm 24 branch, legs exported. -/
theorem cor5_thm24_legs (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (h : a * a + c * b = c * c)
    (hg : Nat.gcd (Nat.gcd a b) c = 1) (hlt : a * a * c < b * (a * a + b * b)) (R : RTri)
    (hRa : R.a = (a : ℚ)) (hRb : R.b = (b : ℚ)) (hRc : R.c = (c : ℚ)) :
    ∃ (s : ℝ) (hs : 0 < s) (N : ℕ) (D : CongruentDissection N),
      dist (D.target.pts 2) (D.target.pts 0) = dist (D.target.pts 2) (D.target.pts 1) ∧
      cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1)
        = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) ∧
      D.model.Congruent (scaleTri s hs.ne' R.Δ) ∧
      ∃ pp rr : ℕ, 0 < pp ∧ 0 < rr ∧ dist (D.target.pts 2) (D.target.pts 0) * (rr : ℝ) = pp * s := by
  have hg2 := gcd_ab_of_three a b c h hg
  obtain ⟨lam, n, T, x0, y0, x1, y1, x2, y2, hd, hl, t1, t2, t3, s1, s2, s3, hD⟩ :=
    beeson_thm24_exists a b c ha hb h hg2 hlt
  obtain ⟨C, hr, hm⟩ := hD
  have hcpos : 0 < c := by rcases Nat.eq_zero_or_pos c with h0 | h0 <;> [(subst h0; simp at h; omega); exact h0]
  set mu : ℝ := ((lam * a * b * (a + c) : ℕ) : ℝ) with hmu
  have hmupos : 0 < mu := by rw [hmu]; exact_mod_cast Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hl ha) hb) (by omega)
  set T' := mkTri x0 y0 x1 y1 x2 y2 hd.ne' with hT'
  have e01 : dist (T'.pts 0) (T'.pts 1) ^ 2 = (mu * a) ^ 2 := by
    show dist (mkPt x0 y0) (mkPt x1 y1) ^ 2 = _
    rw [dist_sq_mkPt]
    calc _ = (x1 - x0) ^ 2 + (y1 - y0) ^ 2 := by ring
      _ = _ := by rw [s1]; simp only [hmu]; push_cast; ring
  have e02 : dist (T'.pts 0) (T'.pts 2) ^ 2 = (mu * c) ^ 2 := by
    show dist (mkPt x0 y0) (mkPt x2 y2) ^ 2 = _
    rw [dist_sq_mkPt]
    calc _ = (x2 - x0) ^ 2 + (y2 - y0) ^ 2 := by ring
      _ = _ := by rw [s2]; simp only [hmu]; push_cast; ring
  have e12 : dist (T'.pts 1) (T'.pts 2) ^ 2 = (mu * c) ^ 2 := by
    show dist (mkPt x1 y1) (mkPt x2 y2) ^ 2 = _
    rw [dist_sq_mkPt]
    calc _ = (x2 - x1) ^ 2 + (y2 - y1) ^ 2 := by ring
      _ = _ := by rw [s3]; simp only [hmu]; push_cast; ring
  have hcR : (0 : ℝ) < c := Nat.cast_pos.mpr hcpos
  refine ⟨1, one_pos, n, C.toCongruentDissection T' (hr.trans (TriSet_eq_carrier hd)), ?_, ?_, ?_, ?_⟩
  · show dist (T'.pts 2) (T'.pts 0) = dist (T'.pts 2) (T'.pts 1)
    rw [dist_comm (T'.pts 2) (T'.pts 0), dist_comm (T'.pts 2) (T'.pts 1)]
    exact (eq_of_sq_eq' dist_nonneg (by positivity) e02).trans
      (eq_of_sq_eq' dist_nonneg (by positivity) e12).symm
  · exact apex_angle T' R a b c mu hmupos ha hb h hRa hRb hRc e01 e02 e12
  · show C.model.Congruent _
    rw [hm]
    refine congr_of_sq3 T R.Δ 1 1 one_pos ?_ ?_ ?_
    · have : dist (R.Δ.pts ((1 : Equiv.Perm (Fin 3)) 0)) (R.Δ.pts ((1 : Equiv.Perm (Fin 3)) 1)) = c := by
        simp [R.hc, hRc]
      rw [this, t1]; ring
    · have : dist (R.Δ.pts ((1 : Equiv.Perm (Fin 3)) 1)) (R.Δ.pts ((1 : Equiv.Perm (Fin 3)) 2)) = a := by
        simp [R.ha, hRa]
      rw [this, t3]; ring
    · have : dist (R.Δ.pts ((1 : Equiv.Perm (Fin 3)) 2)) (R.Δ.pts ((1 : Equiv.Perm (Fin 3)) 0)) = b := by
        simp [R.hb, hRb]
      rw [this, dist_comm, t2]; ring
  · refine ⟨lam * a * b * (a + c) * c, 1, ?_, one_pos, ?_⟩
    · exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hl ha) hb) (by omega)) hcpos
    · show dist (T'.pts 2) (T'.pts 0) * ((1 : ℕ) : ℝ) = _
      rw [dist_comm, eq_of_sq_eq' dist_nonneg (by positivity) e02]
      simp only [hmu]; push_cast; ring

/-- Cor 5, fourth-triple branch, legs exported. -/
theorem cor5_fourth_legs (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hbc : b < c) (h : a * a + c * b = c * c)
    (hlt : (b : ℝ) ^ 3 < c * (c - b) ^ 2) (R : RTri)
    (hRa : R.a = (a : ℚ)) (hRb : R.b = (b : ℚ)) (hRc : R.c = (c : ℚ)) :
    ∃ (s : ℝ) (hs : 0 < s) (N : ℕ) (D : CongruentDissection N),
      dist (D.target.pts 2) (D.target.pts 0) = dist (D.target.pts 2) (D.target.pts 1) ∧
      cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1)
        = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) ∧
      D.model.Congruent (scaleTri s hs.ne' R.Δ) ∧
      ∃ pp rr : ℕ, 0 < pp ∧ 0 < rr ∧ dist (D.target.pts 2) (D.target.pts 0) * (rr : ℝ) = pp * s := by
  have hcR : (0 : ℚ) < c := by exact_mod_cast (by omega : 0 < c)
  have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
  have haQ : (0 : ℚ) < a := by exact_mod_cast ha
  have hbcQ : (b : ℚ) < c := by exact_mod_cast hbc
  have hhQ : (a : ℚ) * a + c * b = c * c := by exact_mod_cast h
  have hltQ : (b : ℚ) ^ 3 < c * (c - b) ^ 2 := by exact_mod_cast hlt
  obtain ⟨T, q, hq, M, C, hC1, hC2, hiso, hang, hleg⟩ :=
    Erdos634.LaczL26.thm24_fourth_legs R ((a : ℚ) / c) (by positivity) (by rw [div_lt_one hcR]; nlinarith)
      (by rw [hRa, hRc]; field_simp)
      (by rw [hRb, hRc]; field_simp; nlinarith [hhQ])
      (by
        have hcb : (c : ℚ) - b ≠ 0 := by linarith
        have hu : ((a : ℚ) / c) ^ 2 = (c - b) / c := by
          field_simp; nlinarith [hhQ]
        have h4 : ((a : ℚ) / c) ^ 4 = ((c - b) / c) ^ 2 := by rw [← hu]; ring
        have h1 : (1 : ℚ) - (c - b) / c = b / c := by field_simp; ring
        rw [h4, hu, h1]
        have e : ((c - b : ℚ) / c) ^ 2 - (b / c) ^ 3 = (c * (c - b) ^ 2 - b ^ 3) / c ^ 3 := by
          field_simp
        rw [e]
        exact div_pos (by linarith) (by positivity))
  refine ⟨1 / (q : ℝ), one_div_pos.mpr (Nat.cast_pos.mpr hq), M, C.toCongruentDissection T hC1, hiso, hang,
    by show C.model.Congruent _; rw [hC2]; exact Tri.Congruent.refl _, ?_⟩
  have hbpos : 0 < b := hb
  refine ⟨q * (a * a + b * b), b, Nat.mul_pos hq (by positivity), hb, ?_⟩
  show dist (T.pts 2) (T.pts 0) * ((b : ℕ) : ℝ) = _
  have h1 : dist (T.pts 2) (T.pts 0) * (R.b : ℝ) = (R.a : ℝ) ^ 2 + (R.b : ℝ) ^ 2 := hleg
  rw [hRa, hRb] at h1
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  push_cast at h1 ⊢
  field_simp
  linarith

/-- **Cor 5 with the legs exported**: the leg `l0` of the tiled isosceles triangle and the tile scale `s` satisfy
`l0 * rr = pp * s` (naturals), i.e. `l0 / s` is rational. -/
theorem cor5_legs (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (h : a * a + c * b = c * c)
    (hg : Nat.gcd (Nat.gcd a b) c = 1) (R : RTri)
    (hRa : R.a = (a : ℚ)) (hRb : R.b = (b : ℚ)) (hRc : R.c = (c : ℚ)) :
    ∃ (s : ℝ) (hs : 0 < s) (N : ℕ) (D : CongruentDissection N),
      dist (D.target.pts 2) (D.target.pts 0) = dist (D.target.pts 2) (D.target.pts 1) ∧
      cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1)
        = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) ∧
      D.model.Congruent (scaleTri s hs.ne' R.Δ) ∧
      ∃ pp rr : ℕ, 0 < pp ∧ 0 < rr ∧ dist (D.target.pts 2) (D.target.pts 0) * (rr : ℝ) = pp * s := by
  have hcpos : 0 < c := by rcases Nat.eq_zero_or_pos c with h0 | h0 <;> [(subst h0; simp at h; omega); exact h0]
  have hbc : b < c := by
    by_contra hcon
    push_neg at hcon
    have : c * c ≤ c * b := Nat.mul_le_mul_left c hcon
    nlinarith
  have hsub : a * a = c * (c - b) := by
    obtain ⟨d, hd⟩ : ∃ d, c = b + d := ⟨c - b, by omega⟩
    subst hd; rw [Nat.add_sub_cancel_left]; nlinarith
  rcases Erdos634.BeesonLemma52.lemma52 a b c hb hbc hsub with ⟨h1, _⟩ | ⟨h2, _⟩
  · -- (i): `b^3 < c (c-b)^2`
    have hhR : (a : ℝ) ^ 2 = c * (c - b) := by
      have : ((a * a : ℕ) : ℝ) = ((c * (c - b) : ℕ) : ℝ) := by rw [hsub]
      push_cast [Nat.cast_sub hbc.le] at this; nlinarith [this]
    have hcR : (0 : ℝ) < c := Nat.cast_pos.mpr hcpos
    have hbR : (0 : ℝ) < b := Nat.cast_pos.mpr hb
    refine cor5_fourth_legs a b c ha hb hbc h ?_ R hRa hRb hRc
    rw [hhR] at h1
    rw [← sub_pos] at h1
    have e : (c * (c - b) / b + b - (c + b ^ 2 / c) : ℝ) = (c * (c - b) ^ 2 - b ^ 3) / (b * c) := by
      field_simp; ring
    rw [e] at h1
    have := (div_pos_iff_of_pos_right (by positivity)).mp h1
    linarith
  · have hlt : a * a * c < b * (a * a + b * b) := by exact_mod_cast (by nlinarith [h2] : (a : ℝ) * a * c < b * (a * a + b * b))
    exact cor5_thm24_legs a b c ha hb h hg hlt R hRa hRb hRc

#print axioms cor5_legs
end Erdos634.BeesonCor5Legs
