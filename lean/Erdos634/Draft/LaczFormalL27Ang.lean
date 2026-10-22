import Erdos634.Draft.LaczFormalL27Third
import Erdos634.Draft.LaczFormalTransportCor

/-!
# Laczkovich Theorem 2.4, triples 2, 3, 5: angles

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94), Beeson, Beeson-Zhang, Zhang.

Angle bookkeeping for the chart pieces: law-of-cosines transfer of angles between proportional triangles, rays along the
chart axis, and the relation `3α + 2β = π` of the tile `(a₀ c, (1-a₀²) c, c)`.
-/

namespace Erdos634.LaczL27

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24 Erdos634.LaczL26 EuclideanGeometry

theorem angle_eq_of_prop {p v q p' v' q' : Plane} {k : ℝ} (hk : 0 < k)
    (h1 : dist p v = k * dist p' v') (h2 : dist q v = k * dist q' v') (h3 : dist p q = k * dist p' q')
    (hp : p' ≠ v') (hq : q' ≠ v') : ∠ p v q = ∠ p' v' q' := by
  have l1 := EuclideanGeometry.law_cos p v q
  have l2 := EuclideanGeometry.law_cos p' v' q'
  have d1 : 0 < dist p' v' := dist_pos.mpr hp
  have d2 : 0 < dist q' v' := dist_pos.mpr hq
  rw [h1, h2, h3] at l1
  have hz : (2 * (k * k) * dist p' v' * dist q' v') * (Real.cos (∠ p v q) - Real.cos (∠ p' v' q')) = 0 := by
    linear_combination l1 - (k * k) * l2
  have hne : 2 * (k * k) * dist p' v' * dist q' v' ≠ 0 := by positivity
  have hc : Real.cos (∠ p v q) = Real.cos (∠ p' v' q') := by
    have := (mul_eq_zero.mp hz).resolve_left hne
    linarith
  exact Real.injOn_cos ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩ ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩ hc

/-- A point on the same ray from `x` gives the same angle. -/
theorem angle_ray {p x r l : Plane} {c : ℝ} (hc : 0 < c) (h : r - x = c • (l - x)) : ∠ p x r = ∠ p x l := by
  unfold EuclideanGeometry.angle
  simp only [vsub_eq_sub]
  rw [h, InnerProductGeometry.angle_smul_right_of_pos _ _ hc]

theorem chart_pt (w d : Plane) (hdet : w 0 * d 1 - w 1 * d 0 ≠ 0) (s t : ℝ) :
    chartEquiv 0 w d hdet (mkPt s t) = s • w + t • d := by
  rw [chartEquiv_apply]; simp only [mkPt_zero, mkPt_one]; module

theorem chart_ray (w d : Plane) (hdet : w 0 * d 1 - w 1 * d 0 ≠ 0) (s s' x : ℝ) (t : ℝ) :
    chartEquiv 0 w d hdet (mkPt s t) - chartEquiv 0 w d hdet (mkPt x t) = (s - x) • w := by
  rw [chart_pt, chart_pt]; module

/-- Distances in the chart from the Gram form. -/
theorem chart_dist (w d : Plane) (hdet : w 0 * d 1 - w 1 * d 0 ≠ 0) (a U : ℝ)
    (hw : inner ℝ w w = U ^ 2) (hd : inner ℝ d d = U ^ 2) (hwd : inner ℝ w d = U ^ 2 * (2 - a ^ 2) / 2)
    (x0 y0 x1 y1 K : ℝ) (hK : 0 ≤ K) (h : U ^ 2 * Qf a (x0 - x1) (y0 - y1) = K ^ 2) :
    dist (chartEquiv 0 w d hdet (mkPt x0 y0)) (chartEquiv 0 w d hdet (mkPt x1 y1)) = K := by
  refine eq_of_sq_eq' dist_nonneg hK ?_
  rw [dist_chart_sq, mkPt_zero, mkPt_zero, mkPt_one, mkPt_one, hw, hd, hwd, ← h]
  unfold Qf; ring


theorem delta_ne (R : RTri) {i j : Fin 3} (h : i ≠ j) : R.Δ.pts i ≠ R.Δ.pts j :=
  fun he => h (R.Δ.indep.injective he)

section tiles

variable (R : RTri) (a0 : ℚ) (ha0 : 0 < a0) (ha1 : a0 < 1)
  (hA : R.a = a0 * R.c) (hB : R.b = (1 - a0 ^ 2) * R.c) (w d : Plane)
  (hdet : w 0 * d 1 - w 1 * d 0 ≠ 0)
  (hw : inner ℝ w w = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2)
  (hd : inner ℝ d d = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2)
  (hwd : inner ℝ w d = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2 * (2 - (a0 : ℝ) ^ 2) / 2)

include ha0 ha1 hA hB hdet hw hd hwd

/-- Angles at the two vertices `p₀` (angle `α`) and `p₁` (angle `β`) of a chart tile of scale `k`. -/
theorem tile_angles (x0 y0 x1 y1 x2 y2 k : ℝ) (hk : 0 < k)
    (h01 : Qf (a0 : ℝ) (x0 - x1) (y0 - y1) = k ^ 2 * (a0 : ℝ) ^ 2 * (1 - (a0 : ℝ) ^ 2) ^ 2)
    (h12 : Qf (a0 : ℝ) (x1 - x2) (y1 - y2) = k ^ 2 * (a0 : ℝ) ^ 4 * (1 - (a0 : ℝ) ^ 2) ^ 2)
    (h20 : Qf (a0 : ℝ) (x2 - x0) (y2 - y0) = k ^ 2 * (a0 : ℝ) ^ 2 * (1 - (a0 : ℝ) ^ 2) ^ 4) :
    ∠ (chartEquiv 0 w d hdet (mkPt x1 y1)) (chartEquiv 0 w d hdet (mkPt x0 y0)) (chartEquiv 0 w d hdet (mkPt x2 y2))
        = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) ∧
      ∠ (chartEquiv 0 w d hdet (mkPt x0 y0)) (chartEquiv 0 w d hdet (mkPt x1 y1)) (chartEquiv 0 w d hdet (mkPt x2 y2))
        = ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) := by
  have hc := R.pc
  have ha0r : (0 : ℝ) < a0 := by exact_mod_cast ha0
  have hb0q : 0 < 1 - a0 ^ 2 := by nlinarith
  have hb0r : (0 : ℝ) < 1 - (a0 : ℝ) ^ 2 := by exact_mod_cast hb0q
  have hcr : (0 : ℝ) < R.c := by exact_mod_cast hc
  have hAr : (R.a : ℝ) = a0 * R.c := by exact_mod_cast hA
  have hBr : (R.b : ℝ) = (1 - (a0 : ℝ) ^ 2) * R.c := by exact_mod_cast hB
  set U : ℝ := (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) with hUdef
  have hUab : U * ((a0 : ℝ) * (1 - (a0 : ℝ) ^ 2)) = R.c := by
    rw [hUdef]; push_cast; field_simp
  have c01 : dist (chartEquiv 0 w d hdet (mkPt x0 y0)) (chartEquiv 0 w d hdet (mkPt x1 y1)) = k * dist (R.Δ.pts 0) (R.Δ.pts 1) := by
    rw [R.hc]
    refine chart_dist w d hdet (a0 : ℝ) U hw hd hwd x0 y0 x1 y1 _ (by positivity) ?_
    rw [h01]; calc U ^ 2 * (k ^ 2 * (a0 : ℝ) ^ 2 * (1 - (a0 : ℝ) ^ 2) ^ 2)
        = k ^ 2 * (U * ((a0 : ℝ) * (1 - (a0 : ℝ) ^ 2))) ^ 2 := by ring
      _ = _ := by rw [hUab]; ring
  have c12 : dist (chartEquiv 0 w d hdet (mkPt x1 y1)) (chartEquiv 0 w d hdet (mkPt x2 y2)) = k * dist (R.Δ.pts 1) (R.Δ.pts 2) := by
    rw [R.ha, hAr]
    refine chart_dist w d hdet (a0 : ℝ) U hw hd hwd x1 y1 x2 y2 _ (by positivity) ?_
    rw [h12]; calc U ^ 2 * (k ^ 2 * (a0 : ℝ) ^ 4 * (1 - (a0 : ℝ) ^ 2) ^ 2)
        = k ^ 2 * (a0 : ℝ) ^ 2 * (U * ((a0 : ℝ) * (1 - (a0 : ℝ) ^ 2))) ^ 2 := by ring
      _ = _ := by rw [hUab]; ring
  have c20 : dist (chartEquiv 0 w d hdet (mkPt x2 y2)) (chartEquiv 0 w d hdet (mkPt x0 y0)) = k * dist (R.Δ.pts 2) (R.Δ.pts 0) := by
    rw [R.hb, hBr]
    refine chart_dist w d hdet (a0 : ℝ) U hw hd hwd x2 y2 x0 y0 _ (by positivity) ?_
    rw [h20]; calc U ^ 2 * (k ^ 2 * (a0 : ℝ) ^ 2 * (1 - (a0 : ℝ) ^ 2) ^ 4)
        = k ^ 2 * (1 - (a0 : ℝ) ^ 2) ^ 2 * (U * ((a0 : ℝ) * (1 - (a0 : ℝ) ^ 2))) ^ 2 := by ring
      _ = _ := by rw [hUab]; ring
  have n01 := delta_ne R (show (0 : Fin 3) ≠ 1 by decide)
  have n02 := delta_ne R (show (0 : Fin 3) ≠ 2 by decide)
  have n12 := delta_ne R (show (1 : Fin 3) ≠ 2 by decide)
  constructor
  · refine angle_eq_of_prop hk ?_ ?_ ?_ n01.symm n02.symm
    · rw [dist_comm, c01, dist_comm (R.Δ.pts 0)]
    · rw [c20]
    · rw [c12]
  · refine angle_eq_of_prop hk ?_ ?_ ?_ n01 n12.symm
    · rw [c01]
    · rw [dist_comm, c12, dist_comm (R.Δ.pts 1)]
    · rw [dist_comm, c20, dist_comm (R.Δ.pts 0)]

end tiles


section apex

variable (R : RTri) (a0 : ℚ) (ha0 : 0 < a0) (ha1 : a0 < 1)
  (hA : R.a = a0 * R.c) (hB : R.b = (1 - a0 ^ 2) * R.c)
  (w1 d1 : Plane) (hdet : w1 0 * d1 1 - w1 1 * d1 0 ≠ 0)
  (hw : inner ℝ w1 w1 = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2)
  (hd : inner ℝ d1 d1 = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2)
  (hwd : inner ℝ w1 d1 = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2 * (2 - (a0 : ℝ) ^ 2) / 2)

include ha0 ha1 hA hB hdet hw hd hwd

/-- The triangle `T = L R P` is isosceles at `P`, with apex angle `α`. -/
theorem T4_iso_apex :
    dist (chartEquiv 0 w1 d1 hdet (mkPt (sP (a0 : ℝ)) (tP (a0 : ℝ)))) (chartEquiv 0 w1 d1 hdet (mkPt 0 0))
      = dist (chartEquiv 0 w1 d1 hdet (mkPt (sP (a0 : ℝ)) (tP (a0 : ℝ)))) (chartEquiv 0 w1 d1 hdet (mkPt (sR (a0 : ℝ)) 0)) ∧
    ∠ (chartEquiv 0 w1 d1 hdet (mkPt 0 0)) (chartEquiv 0 w1 d1 hdet (mkPt (sP (a0 : ℝ)) (tP (a0 : ℝ))))
        (chartEquiv 0 w1 d1 hdet (mkPt (sR (a0 : ℝ)) 0)) = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) := by
  have hyp := hyp0_of_q a0 ha0 ha1
  have hc := R.pc
  have ha0r : (0 : ℝ) < a0 := by exact_mod_cast ha0
  have ha1r : (a0 : ℝ) < 1 := by exact_mod_cast ha1
  have hb0q : (0 : ℚ) < 1 - a0 ^ 2 := by nlinarith
  have hb0r : (0 : ℝ) < 1 - (a0 : ℝ) ^ 2 := by exact_mod_cast hb0q
  have hcr : (0 : ℝ) < R.c := by exact_mod_cast hc
  have hupos : (0 : ℚ) < R.c / (a0 * (1 - a0 ^ 2)) := by positivity
  set U : ℝ := (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) with hUdef
  have hUpos : 0 < U := by rw [hUdef]; exact_mod_cast hupos
  have hAr : (R.a : ℝ) = a0 * R.c := by exact_mod_cast hA
  have hBr : (R.b : ℝ) = (1 - (a0 : ℝ) ^ 2) * R.c := by exact_mod_cast hB
  have hUab : U * ((a0 : ℝ) * (1 - (a0 : ℝ) ^ 2)) = R.c := by
    rw [hUdef]; push_cast; field_simp
  have hKpos : 0 < gK (a0 : ℝ) := hyp.hK
  have hwd' : inner ℝ w1 d1 = U ^ 2 * (2 - (a0 : ℝ) ^ 2) / 2 := hwd
  constructor
  · refine eq_of_sq_eq' dist_nonneg dist_nonneg ?_
    rw [dist_chart_sq, dist_chart_sq]
    simp only [mkPt_zero, mkPt_one]
    rw [hw, hd, hwd']
    unfold sP tP sR gb gK
    ring
  · have e1 : chartEquiv 0 w1 d1 hdet (mkPt 0 0) - chartEquiv 0 w1 d1 hdet (mkPt (sP (a0 : ℝ)) (tP (a0 : ℝ)))
        = (-(sP (a0 : ℝ))) • w1 + (-(tP (a0 : ℝ))) • d1 := by
      rw [chart_pt, chart_pt]; module
    have e2 : chartEquiv 0 w1 d1 hdet (mkPt (sR (a0 : ℝ)) 0)
        - chartEquiv 0 w1 d1 hdet (mkPt (sP (a0 : ℝ)) (tP (a0 : ℝ)))
        = (sR (a0 : ℝ) - sP (a0 : ℝ)) • w1 + (-(tP (a0 : ℝ))) • d1 := by
      rw [chart_pt, chart_pt]; module
    have hKa : 0 ≤ U * gK (a0 : ℝ) * a0 := by positivity
    have n1 : ‖(-(sP (a0 : ℝ))) • w1 + (-(tP (a0 : ℝ))) • d1‖ = U * gK (a0 : ℝ) * a0 := by
      refine norm_comb w1 d1 _ _ _ hKa ?_
      rw [gram2, hw, hd, hwd']
      unfold sP tP gb gK; ring
    have n2 : ‖(sR (a0 : ℝ) - sP (a0 : ℝ)) • w1 + (-(tP (a0 : ℝ))) • d1‖ = U * gK (a0 : ℝ) * a0 := by
      refine norm_comb w1 d1 _ _ _ hKa ?_
      rw [gram2, hw, hd, hwd']
      unfold sR sP tP gb gK; ring
    have h1 : ‖R.Δ.pts 1 - R.Δ.pts 0‖ = R.c := by rw [← dist_eq_norm, dist_comm]; exact R.hc
    have h2 : ‖R.Δ.pts 2 - R.Δ.pts 0‖ = R.b := by rw [← dist_eq_norm]; exact R.hb
    unfold EuclideanGeometry.angle
    simp only [vsub_eq_sub]
    rw [e1, e2]
    unfold InnerProductGeometry.angle
    rw [n1, n2, R.inner_uv, h1, h2, gram2, hw, hd, hwd', hAr, hBr]
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

end apex


/-- **`3α + 2β = π`** for the tile `(a₀ c, (1-a₀²) c, c)`, `0 < a₀ < 1` (`α` at `Δ₀`, `β` at `Δ₁`). -/
theorem tile_relation (R : RTri) (a0 : ℚ) (ha0 : 0 < a0) (ha1 : a0 < 1)
    (hA : R.a = a0 * R.c) (hB : R.b = (1 - a0 ^ 2) * R.c) :
    3 * ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) + 2 * ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) = Real.pi := by
  have hc := R.pc
  have ha0r : (0 : ℝ) < a0 := by exact_mod_cast ha0
  have ha1r : (a0 : ℝ) < 1 := by exact_mod_cast ha1
  have hcr : (0 : ℝ) < R.c := by exact_mod_cast hc
  have hAr : (R.a : ℝ) = a0 * R.c := by exact_mod_cast hA
  have hBr : (R.b : ℝ) = (1 - (a0 : ℝ) ^ 2) * R.c := by exact_mod_cast hB
  have hb0 : (0 : ℝ) < 1 - (a0 : ℝ) ^ 2 := by nlinarith
  set u : ℝ := (a0 : ℝ) with hu
  set α := ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) with hαdef
  set β := ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) with hβdef
  have lα := EuclideanGeometry.law_cos (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2)
  have lβ := EuclideanGeometry.law_cos (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2)
  have d10 : dist (R.Δ.pts 1) (R.Δ.pts 0) = R.c := by rw [dist_comm]; exact R.hc
  have d12 : dist (R.Δ.pts 1) (R.Δ.pts 2) = R.a := R.ha
  have d20 : dist (R.Δ.pts 2) (R.Δ.pts 0) = R.b := R.hb
  have d01 : dist (R.Δ.pts 0) (R.Δ.pts 1) = R.c := R.hc
  have d02 : dist (R.Δ.pts 0) (R.Δ.pts 2) = R.b := by rw [dist_comm]; exact R.hb
  have d21 : dist (R.Δ.pts 2) (R.Δ.pts 1) = R.a := by rw [dist_comm]; exact R.ha
  rw [d12, d10, d20] at lα
  rw [d02, d01, d21] at lβ
  rw [hAr, hBr] at lα lβ
  have cα : Real.cos α = (2 - u ^ 2) / 2 := by
    have : (2 * (R.c * R.c) * (1 - u ^ 2)) * (Real.cos α - (2 - u ^ 2) / 2) = 0 := by
      linear_combination lα
    have hne : (2 * (R.c * R.c) * (1 - u ^ 2)) ≠ 0 := by positivity
    have := (mul_eq_zero.mp this).resolve_left hne
    linarith
  have cβ : Real.cos β = u * (3 - u ^ 2) / 2 := by
    have : (2 * (R.c * R.c) * u) * (Real.cos β - u * (3 - u ^ 2) / 2) = 0 := by
      linear_combination lβ
    have hne : (2 * (R.c * R.c) * u) ≠ 0 := by positivity
    have := (mul_eq_zero.mp this).resolve_left hne
    linarith
  have hα0 : 0 ≤ α := angle_nonneg _ _ _
  have hαπ : α ≤ Real.pi := angle_le_pi _ _ _
  have hβ0 : 0 ≤ β := angle_nonneg _ _ _
  have hβπ : β ≤ Real.pi := angle_le_pi _ _ _
  have hα3 : α ≤ Real.pi / 3 := by
    by_contra hcon
    push_neg at hcon
    have := Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hαπ hcon.le
    rw [Real.cos_pi_div_three, cα] at this
    nlinarith
  have hβ2 : β ≤ Real.pi / 2 := by
    by_contra hcon
    push_neg at hcon
    have := Real.cos_nonpos_of_pi_div_two_le_of_le hcon.le (by linarith)
    rw [cβ] at this
    nlinarith
  have hcos : Real.cos (2 * β) = Real.cos (Real.pi - 3 * α) := by
    rw [Real.cos_two_mul, Real.cos_pi_sub, Real.cos_three_mul, cα, cβ]
    ring
  have := Real.injOn_cos ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hcos
  linarith

section base

variable (R : RTri) (a0 : ℚ) (ha0 : 0 < a0) (ha1 : a0 < 1)
  (hA : R.a = a0 * R.c) (hB : R.b = (1 - a0 ^ 2) * R.c)
  (hN : T4RSD R a0 ha0 ha1) (w1 d1 : Plane) (hdet : w1 0 * d1 1 - w1 1 * d1 0 ≠ 0)
  (hw : inner ℝ w1 w1 = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2)
  (hd : inner ℝ d1 d1 = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2)
  (hwd : inner ℝ w1 d1 = (((R.c / (a0 * (1 - a0 ^ 2)) : ℚ) : ℝ)) ^ 2 * (2 - (a0 : ℝ) ^ 2) / 2)

include ha0 ha1 hA hB hN hdet hw hd hwd

/-- Base angles of `T = L R P`: both `α + β` (`= (π - α)/2`). -/
theorem T4_base :
    ∠ (chartEquiv 0 w1 d1 hdet (mkPt (sP (a0 : ℝ)) (tP (a0 : ℝ)))) (chartEquiv 0 w1 d1 hdet (mkPt 0 0))
        (chartEquiv 0 w1 d1 hdet (mkPt (sR (a0 : ℝ)) 0))
      = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) + ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) ∧
    ∠ (chartEquiv 0 w1 d1 hdet (mkPt (sP (a0 : ℝ)) (tP (a0 : ℝ)))) (chartEquiv 0 w1 d1 hdet (mkPt (sR (a0 : ℝ)) 0))
        (chartEquiv 0 w1 d1 hdet (mkPt 0 0))
      = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) + ∠ (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) := by
  obtain ⟨hiso, hap⟩ := T4_iso_apex R a0 ha0 ha1 hA hB w1 d1 hdet hw hd hwd
  have hrel := tile_relation R a0 ha0 ha1 hA hB
  set S : Tri := Erdos634.DissectionMap.mapTri (chartEquiv 0 w1 d1 hdet) (triT0 (hyp0_of_q a0 ha0 ha1)) with hS
  have hiso' : dist (S.pts 2) (S.pts 0) = dist (S.pts 2) (S.pts 1) := hiso
  have hsum := Erdos634.LaczTransport.base_angle S hiso'
  have hap' : ∠ (S.pts 0) (S.pts 2) (S.pts 1) = ∠ (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) := hap
  have hL := angle_eq_angle_of_dist_eq hiso'
  constructor
  · show ∠ (S.pts 2) (S.pts 0) (S.pts 1) = _
    rw [hL]; linarith
  · show ∠ (S.pts 2) (S.pts 1) (S.pts 0) = _
    linarith

end base

end Erdos634.LaczL27
