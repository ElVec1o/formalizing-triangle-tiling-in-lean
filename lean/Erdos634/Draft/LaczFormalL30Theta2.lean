import Erdos634.Draft.LaczFormalL30Final

/-!
# Laczkovich Theorem 2.5, triple `(2α, 2β, α+β)`: the triangle `Θ` for every rational tile with `γ = 2π/3`

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.5, Fig. 7), Beeson, Beeson-Zhang, Zhang.

`theta_lt` (`b < a`): a triangle `T` with `T₀` (angle `2α`), `T₁` (angle `2β`), `T₂` (angle `π/3`), rational sides, which is a
rational similar dissection.  `theta_all`: every rational tile with `γ = 2π/3` (the case `a = b` is impossible for a rational
tile, `c² = 3a²`); for `a < b` the roles of `α, β` are exchanged (`RTri.sw01`) and the vertices `T₀, T₁` swapped.
-/

namespace Erdos634.LaczL30

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL21 Erdos634.LaczL24 Erdos634.Realizable
  Erdos634.DissectionMap
open Erdos634.LaczL27 (carrier_eq_of_range range_mk3)

private theorem htri3 : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide

section theta2

variable (R : RTri) (hγ : R.a ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2) (hab : R.b < R.a)
  (w d : Plane) (hdet : w 0 * d 1 - w 1 * d 0 ≠ 0)
  (hw : inner ℝ w w = (R.a : ℝ) ^ 2) (hd : inner ℝ d d = (R.a : ℝ) ^ 2)
  (hwd : inner ℝ w d = (R.a : ℝ) * (R.a : ℝ) * (-1 / 2))

include hγ hab hdet hw hd hwd

set_option maxHeartbeats 4000000 in
theorem theta_angleV (K : ℝ) (hKR : K = ((kq R : ℚ) : ℝ)) (hk0 : 0 < K) (hk1 : K < 1) :
    cornerAngle (chartEquiv 0 w d hdet (mkPt (-K) (-K))) (chartEquiv 0 w d hdet (mkPt 1 0))
        (chartEquiv 0 w d hdet (mkPt (th K) (nu K))) = Real.pi / 3 := by
  obtain ⟨dAV, dLV, dAL⟩ := theta_dist R hγ hab w d hdet hw hd hwd K hKR hk0 hk1
  have hc0 : (0 : ℝ) < R.c := by exact_mod_cast R.pc
  have hn := nu_pos hk0 hk1
  have h1 : K ≠ 0 := hk0.ne'
  have h2 : (2 : ℝ) + K ≠ 0 := by linarith
  have h4 : (1 : ℝ) + K + K ^ 2 ≠ 0 := by positivity
  have hAV0 : dist (chartEquiv 0 w d hdet (mkPt (-K) (-K))) (chartEquiv 0 w d hdet (mkPt 1 0)) ≠ 0 := by
    rw [dAV]; exact hc0.ne'
  have hLV0 : dist (chartEquiv 0 w d hdet (mkPt (th K) (nu K))) (chartEquiv 0 w d hdet (mkPt 1 0)) ≠ 0 := by
    rw [dLV]; positivity
  have c := Erdos634.AngleThreshold.cos_of_sides (chartEquiv 0 w d hdet (mkPt (-K) (-K)))
    (chartEquiv 0 w d hdet (mkPt 1 0)) (chartEquiv 0 w d hdet (mkPt (th K) (nu K))) hAV0 hLV0
  rw [dAV, dLV, dAL] at c
  have hc : Real.cos (cornerAngle (chartEquiv 0 w d hdet (mkPt (-K) (-K))) (chartEquiv 0 w d hdet (mkPt 1 0))
      (chartEquiv 0 w d hdet (mkPt (th K) (nu K)))) = Real.cos (Real.pi / 3) := by
    rw [c, Real.cos_pi_div_three]
    unfold nu; field_simp; ring
  exact Real.injOn_cos ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
    ⟨by positivity, by linarith [Real.pi_pos]⟩ hc

set_option maxHeartbeats 4000000 in
theorem theta_chart_T (K : ℝ) (hKR : K = ((kq R : ℚ) : ℝ)) (hk0 : 0 < K) (hk1 : K < 1) :
    ∃ T : Tri, RatSimDiss R.Δ T.carrier ∧ IsRationalTri T ∧
      T.pts 0 = chartEquiv 0 w d hdet (mkPt (-K) (-K)) ∧ T.pts 1 = chartEquiv 0 w d hdet (mkPt (th K) (nu K)) ∧
      T.pts 2 = chartEquiv 0 w d hdet (mkPt 1 0) := by
  have hdetT : det3 (-K) (-K) (th K) (nu K) 1 0 ≠ 0 := by
    have e : det3 (-K) (-K) (th K) (nu K) 1 0 = - det3 (-K) (-K) 1 0 (th K) (nu K) := by unfold det3; ring
    rw [e]; exact neg_ne_zero.mpr (detpos_Th hk0 hk1).ne'
  refine ⟨mapTri (chartEquiv 0 w d hdet) (mkTri (-K) (-K) (th K) (nu K) 1 0 hdetT), ?_, ?_, rfl, rfl, rfl⟩
  · have h := chart_Theta R hγ hab w d hdet hw hd hwd
    have e : (mkTri (-K) (-K) (th K) (nu K) 1 0 hdetT).carrier = (tTh hk0 hk1).carrier := by
      refine carrier_eq_of_range ?_
      show Set.range (mkTri (-K) (-K) (th K) (nu K) 1 0 hdetT).pts = Set.range (mkTri (-K) (-K) 1 0 (th K) (nu K) _).pts
      rw [mkTri_pts, mkTri_pts, range_mk3, range_mk3]
      ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    unfold ChartRSD at h
    rw [mapTri_carrier, e]
    have hK : K = ((kq R : ℚ) : ℝ) := hKR
    subst hK
    exact h
  · obtain ⟨dAV, dLV, dAL⟩ := theta_dist R hγ hab w d hdet hw hd hwd K hKR hk0 hk1
    have hnc : ((nuq R : ℚ) : ℝ) = nu K := by rw [hKR]; exact nuq_cast R
    have rAV : ∃ s : ℚ, dist (chartEquiv 0 w d hdet (mkPt (-K) (-K))) (chartEquiv 0 w d hdet (mkPt 1 0)) = s :=
      ⟨R.c, by rw [dAV]⟩
    have rLV : ∃ s : ℚ, dist (chartEquiv 0 w d hdet (mkPt (th K) (nu K))) (chartEquiv 0 w d hdet (mkPt 1 0)) = s :=
      ⟨nuq R * R.c, by rw [dLV, ← hnc]; push_cast; ring⟩
    have rAL : ∃ s : ℚ, dist (chartEquiv 0 w d hdet (mkPt (-K) (-K))) (chartEquiv 0 w d hdet (mkPt (th K) (nu K))) = s :=
      ⟨(1 + kq R + kq R ^ 2) / (kq R * (2 + kq R)) * R.c, by rw [dAL, hKR]; push_cast; ring⟩
    intro j k
    rcases htri3 j with rfl | rfl | rfl <;> rcases htri3 k with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · obtain ⟨s, hs⟩ := rAL; exact ⟨s, hs⟩
    · obtain ⟨s, hs⟩ := rAV; exact ⟨s, hs⟩
    · obtain ⟨s, hs⟩ := rAL; exact ⟨s, by rw [dist_comm]; exact hs⟩
    · exact ⟨0, by simp⟩
    · obtain ⟨s, hs⟩ := rLV; exact ⟨s, hs⟩
    · obtain ⟨s, hs⟩ := rAV; exact ⟨s, by rw [dist_comm]; exact hs⟩
    · obtain ⟨s, hs⟩ := rLV; exact ⟨s, by rw [dist_comm]; exact hs⟩
    · exact ⟨0, by simp⟩

end theta2

#print axioms theta_chart_T
#print axioms theta_angleV

end Erdos634.LaczL30
