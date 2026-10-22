import Erdos634.Draft.LaczFormalL30Theta
import Erdos634.AngleThreshold
import Erdos634.Draft.LaczFormalL25Wit

/-!
# Laczkovich Theorem 2.5, triple `(2α, 2β, α+β)` (Fig. 7, second picture): the theorem for `b < a`

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.5, Fig. 7), Beeson, Beeson-Zhang, Zhang.

`Θ = A L V` has angle `2α` at `A`, `2β` at `L`, `α+β = π/3` at `V`.  Range: `b < a`.
-/

namespace Erdos634.LaczL30

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24 Erdos634.Realizable
  Erdos634.DissectionMap

theorem ang_double (p q r : Plane) (α : ℝ) (hα : 0 ≤ α) (hα2 : α ≤ Real.pi / 2)
    (h : Real.cos (cornerAngle p q r) = 2 * Real.cos α ^ 2 - 1) : cornerAngle p q r = α + α := by
  have hc : Real.cos (α + α) = 2 * Real.cos α ^ 2 - 1 := by rw [← two_mul, Real.cos_two_mul]
  exact Real.injOn_cos ⟨EuclideanGeometry.angle_nonneg p q r, EuclideanGeometry.angle_le_pi p q r⟩
    ⟨by linarith, by linarith [Real.pi_pos]⟩ (h.trans hc.symm)

section final

variable (R : RTri) (hγ : R.a ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2) (hab : R.b < R.a)
  (w d : Plane) (hdet : w 0 * d 1 - w 1 * d 0 ≠ 0)
  (hw : inner ℝ w w = (R.a : ℝ) ^ 2) (hd : inner ℝ d d = (R.a : ℝ) ^ 2)
  (hwd : inner ℝ w d = (R.a : ℝ) * (R.a : ℝ) * (-1 / 2))

include hw hd hwd

theorem chart_dsq (x0 y0 x1 y1 : ℝ) :
    dist (chartEquiv 0 w d hdet (mkPt x0 y0)) (chartEquiv 0 w d hdet (mkPt x1 y1)) ^ 2
      = (R.a : ℝ) ^ 2 * ((x0 - x1) ^ 2 - (x0 - x1) * (y0 - y1) + (y0 - y1) ^ 2) := by
  rw [dist_chart_sq, hw, hd, hwd]; simp only [mkPt_zero, mkPt_one]; ring

omit hw hd hwd
include hγ hab hdet hw hd hwd

set_option maxHeartbeats 4000000 in
/-- the three side lengths of `Θ` (`|AV| = c`, `|LV| = ν c`, `|AL| = c (1+K+K²)/(K(2+K))`). -/
theorem theta_dist (K : ℝ) (hKR : K = ((kq R : ℚ) : ℝ)) (hk0 : 0 < K) (hk1 : K < 1) :
    dist (chartEquiv 0 w d hdet (mkPt (-K) (-K))) (chartEquiv 0 w d hdet (mkPt 1 0)) = R.c ∧
    dist (chartEquiv 0 w d hdet (mkPt (th K) (nu K))) (chartEquiv 0 w d hdet (mkPt 1 0)) = nu K * R.c ∧
    dist (chartEquiv 0 w d hdet (mkPt (-K) (-K))) (chartEquiv 0 w d hdet (mkPt (th K) (nu K)))
      = (1 + K + K ^ 2) / (K * (2 + K)) * R.c := by
  obtain ⟨hb, hc2⟩ := real_facts R hγ
  rw [← hKR] at hb hc2
  have hc0 : (0 : ℝ) < R.c := by exact_mod_cast R.pc
  have hn := nu_pos hk0 hk1
  have h1 : K ≠ 0 := hk0.ne'
  have h2 : (2 : ℝ) + K ≠ 0 := by linarith
  have h4 : (1 : ℝ) + K + K ^ 2 ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · refine eq_of_sq_eq' dist_nonneg hc0.le ?_
    rw [chart_dsq R w d hdet hw hd hwd, hc2]; ring
  · refine eq_of_sq_eq' dist_nonneg (by positivity) ?_
    rw [chart_dsq R w d hdet hw hd hwd, mul_pow, hc2]
    unfold th nu; field_simp; ring
  · refine eq_of_sq_eq' dist_nonneg (by positivity) ?_
    rw [chart_dsq R w d hdet hw hd hwd, mul_pow, hc2]
    unfold th nu; field_simp; ring

set_option maxHeartbeats 4000000 in
theorem thm25_t5_chart (K : ℝ) (hKR : K = ((kq R : ℚ) : ℝ)) (hk0 : 0 < K) (hk1 : K < 1) :
    cornerAngle (chartEquiv 0 w d hdet (mkPt (th K) (nu K))) (chartEquiv 0 w d hdet (mkPt (-K) (-K)))
        (chartEquiv 0 w d hdet (mkPt 1 0))
      = cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) + cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) ∧
    cornerAngle (chartEquiv 0 w d hdet (mkPt 1 0)) (chartEquiv 0 w d hdet (mkPt (th K) (nu K)))
        (chartEquiv 0 w d hdet (mkPt (-K) (-K)))
      = cornerAngle (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) + cornerAngle (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) := by
  obtain ⟨hb, hc2⟩ := real_facts R hγ
  rw [← hKR] at hb hc2
  have ha : (0 : ℝ) < R.a := by exact_mod_cast R.pa
  have hb0 : (0 : ℝ) < R.b := by exact_mod_cast R.pb
  have hc0 : (0 : ℝ) < R.c := by exact_mod_cast R.pc
  have hn := nu_pos hk0 hk1
  have ht := th_pos hk0 hk1
  have h1 : K ≠ 0 := hk0.ne'
  have h2 : (2 : ℝ) + K ≠ 0 := by linarith
  have h3 : K + th K ≠ 0 := by linarith
  have h4 : (1 : ℝ) + K + K ^ 2 ≠ 0 := by positivity
  have hγR : (R.a : ℝ) ^ 2 + R.a * R.b + R.b ^ 2 = (R.c : ℝ) ^ 2 := by exact_mod_cast hγ
  obtain ⟨dAV, dLV, dAL⟩ := theta_dist R hγ hab w d hdet hw hd hwd K hKR hk0 hk1
  have hAV0 : dist (chartEquiv 0 w d hdet (mkPt (-K) (-K))) (chartEquiv 0 w d hdet (mkPt 1 0)) ≠ 0 := by
    rw [dAV]; exact hc0.ne'
  have hAL0 : dist (chartEquiv 0 w d hdet (mkPt (-K) (-K))) (chartEquiv 0 w d hdet (mkPt (th K) (nu K))) ≠ 0 := by
    rw [dAL]; positivity
  have hLV0 : dist (chartEquiv 0 w d hdet (mkPt (th K) (nu K))) (chartEquiv 0 w d hdet (mkPt 1 0)) ≠ 0 := by
    rw [dLV]; positivity
  -- cosines of the tile angles
  have dΔ1 : dist (R.Δ.pts 1) (R.Δ.pts 0) = R.c := by rw [dist_comm]; exact R.hc
  have dΔ2 : dist (R.Δ.pts 2) (R.Δ.pts 0) = R.b := R.hb
  have dΔ3 : dist (R.Δ.pts 1) (R.Δ.pts 2) = R.a := R.ha
  have dΔ4 : dist (R.Δ.pts 0) (R.Δ.pts 1) = R.c := R.hc
  have dΔ5 : dist (R.Δ.pts 2) (R.Δ.pts 1) = R.a := by rw [dist_comm]; exact R.ha
  have dΔ6 : dist (R.Δ.pts 0) (R.Δ.pts 2) = R.b := by rw [dist_comm]; exact R.hb
  have cα := Erdos634.AngleThreshold.cos_of_sides (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2)
    (by rw [dΔ1]; exact hc0.ne') (by rw [dΔ2]; exact hb0.ne')
  rw [dΔ1, dΔ2, dΔ3] at cα
  have cβ := Erdos634.AngleThreshold.cos_of_sides (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2)
    (by rw [dΔ4]; exact hc0.ne') (by rw [dΔ5]; exact ha.ne')
  rw [dΔ4, dΔ5, dΔ6] at cβ
  -- α, β ≤ π/2 (their cosines are positive)
  have hαpos : 0 < Real.cos (cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2)) := by
    rw [cα]; refine div_pos ?_ (by positivity); nlinarith [hγR, mul_pos ha hb0, sq_pos_of_pos hb0]
  have hβpos : 0 < Real.cos (cornerAngle (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2)) := by
    rw [cβ]; refine div_pos ?_ (by positivity); nlinarith [hγR, mul_pos ha hb0, sq_pos_of_pos ha]
  have hα2 : cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) ≤ Real.pi / 2 := by
    by_contra hcon; push_neg at hcon
    have hle : cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2) ≤ Real.pi := EuclideanGeometry.angle_le_pi _ _ _
    have := Real.cos_nonpos_of_pi_div_two_le_of_le hcon.le (by linarith [Real.pi_pos])
    linarith
  have hβ2 : cornerAngle (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) ≤ Real.pi / 2 := by
    by_contra hcon; push_neg at hcon
    have hle : cornerAngle (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2) ≤ Real.pi := EuclideanGeometry.angle_le_pi _ _ _
    have := Real.cos_nonpos_of_pi_div_two_le_of_le hcon.le (by linarith [Real.pi_pos])
    linarith
  have cA2 : Real.cos (cornerAngle (R.Δ.pts 1) (R.Δ.pts 0) (R.Δ.pts 2)) ^ 2
      = (2 * K + 1) ^ 2 / (4 * (1 + K + K ^ 2)) := by
    rw [cα, div_pow]
    have e : (2 * (R.c : ℝ) * R.b) ^ 2 = 4 * (R.c : ℝ) ^ 2 * (R.b : ℝ) ^ 2 := by ring
    rw [e, hc2, hb]
    field_simp
    ring
  have cB2 : Real.cos (cornerAngle (R.Δ.pts 0) (R.Δ.pts 1) (R.Δ.pts 2)) ^ 2
      = (2 + K) ^ 2 / (4 * (1 + K + K ^ 2)) := by
    rw [cβ, div_pow]
    have e : (2 * (R.c : ℝ) * R.a) ^ 2 = 4 * (R.c : ℝ) ^ 2 * (R.a : ℝ) ^ 2 := by ring
    rw [e, hc2, hb]
    field_simp
    ring
  constructor
  · refine ang_double _ _ _ _ (EuclideanGeometry.angle_nonneg _ _ _) hα2 ?_
    -- cos at A
    have cA := Erdos634.AngleThreshold.cos_of_sides (chartEquiv 0 w d hdet (mkPt (th K) (nu K)))
      (chartEquiv 0 w d hdet (mkPt (-K) (-K))) (chartEquiv 0 w d hdet (mkPt 1 0))
      (by rw [dist_comm]; exact hAL0) (by rw [dist_comm]; exact hAV0)
    rw [cA, dist_comm (chartEquiv 0 w d hdet (mkPt (th K) (nu K))) (chartEquiv 0 w d hdet (mkPt (-K) (-K))),
      dist_comm (chartEquiv 0 w d hdet (mkPt 1 0)) (chartEquiv 0 w d hdet (mkPt (-K) (-K))), dAL, dAV, dLV, cA2]
    unfold nu; field_simp; ring
  · refine ang_double _ _ _ _ (EuclideanGeometry.angle_nonneg _ _ _) hβ2 ?_
    have cL := Erdos634.AngleThreshold.cos_of_sides (chartEquiv 0 w d hdet (mkPt 1 0))
      (chartEquiv 0 w d hdet (mkPt (th K) (nu K))) (chartEquiv 0 w d hdet (mkPt (-K) (-K)))
      (by rw [dist_comm]; exact hLV0) hAL0
    rw [cL, dist_comm (chartEquiv 0 w d hdet (mkPt 1 0)) (chartEquiv 0 w d hdet (mkPt (th K) (nu K))),
      dist_comm (chartEquiv 0 w d hdet (mkPt 1 0)) (chartEquiv 0 w d hdet (mkPt (-K) (-K))), dLV, dAL, dAV, cB2]
    unfold nu; field_simp; ring

end final

#print axioms thm25_t5_chart

end Erdos634.LaczL30
