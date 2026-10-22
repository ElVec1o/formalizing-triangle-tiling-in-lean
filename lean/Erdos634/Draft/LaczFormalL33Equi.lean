import Erdos634.Draft.LaczFormalL33Final

/-!
# Laczkovich Theorem 2.5, triple `(α+β, α+β, α+β)`: the equilateral triangle for every rational tile with `γ = 2π/3`

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.5, Fig. 7), Beeson, Beeson-Zhang, Zhang.

For `a < b` exchange `α` and `β` (`RTri.sw01`; the equilateral triangle is symmetric); `a = b` is impossible
(`LaczL30.a_ne_b`).
-/

namespace Erdos634.LaczL33

open Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL21 Erdos634.LaczL22 Erdos634.LaczL24 Erdos634.Realizable Erdos634.DissectionMap
  Erdos634.LaczL30
open Erdos634.LaczL27 (carrier_eq_of_range range_mk3)

private theorem htri4 : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide

/-- an equilateral triangle has angle `π/3`. -/
theorem equi_angle (p q r : Plane) (c : ℝ) (hc : 0 < c) (h1 : dist p q = c) (h2 : dist r q = c) (h3 : dist p r = c) :
    cornerAngle p q r = Real.pi / 3 := by
  have hcos := Erdos634.AngleThreshold.cos_of_sides p q r (by rw [h1]; exact hc.ne') (by rw [h2]; exact hc.ne')
  rw [h1, h2, h3] at hcos
  have : Real.cos (cornerAngle p q r) = Real.cos (Real.pi / 3) := by
    rw [hcos, Real.cos_pi_div_three]; field_simp; ring
  exact Real.injOn_cos ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
    ⟨by positivity, by linarith [Real.pi_pos]⟩ this

theorem equi_lt (R : RTri) (hγ : R.a ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2) (hab : R.b < R.a) :
    ∃ T : Tri, RatSimDiss R.Δ T.carrier ∧ IsRationalTri T ∧
      cornerAngle (T.pts 1) (T.pts 0) (T.pts 2) = Real.pi / 3 ∧
      cornerAngle (T.pts 2) (T.pts 1) (T.pts 0) = Real.pi / 3 ∧
      cornerAngle (T.pts 0) (T.pts 2) (T.pts 1) = Real.pi / 3 := by
  have ha : (0 : ℝ) < R.a := by exact_mod_cast R.pa
  obtain ⟨w, d, hw, hd, hwd, hdet⟩ := exists_gram_chart (R.a : ℝ) (R.a : ℝ) (-1 / 2) ha ha (by norm_num)
  set K : ℝ := ((kq R : ℚ) : ℝ) with hKdef
  have hk0 := hK0 R
  have hk1 := hK1 R hab
  obtain ⟨dAV, dVR, dAR⟩ := equi_dist R hγ hab w d hdet hw hd hwd K rfl
  have hc0 : (0 : ℝ) < R.c := by exact_mod_cast R.pc
  have hdetT : det3 (-K) (-K) 1 0 (1 - K) 1 ≠ 0 := (detpos_E hk0 hk1).ne'
  have e : (mkTri (-K) (-K) 1 0 (1 - K) 1 hdetT).carrier = (tE hk0 hk1).carrier := rfl
  have hRat : ∀ x : ℚ, ((x : ℚ) : ℝ) = (x : ℝ) := fun _ => rfl
  refine ⟨mapTri (chartEquiv 0 w d hdet) (mkTri (-K) (-K) 1 0 (1 - K) 1 hdetT), ?_, ?_, ?_, ?_, ?_⟩
  · have h := chart_E R hγ hab w d hdet hw hd hwd
    unfold ChartRSD at h
    rw [mapTri_carrier, e]; exact h
  · intro j k
    rcases htri4 j with rfl | rfl | rfl <;> rcases htri4 k with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨R.c, dAV⟩
    · exact ⟨R.c, dAR⟩
    · exact ⟨R.c, by show dist (chartEquiv 0 w d hdet (mkPt 1 0)) (chartEquiv 0 w d hdet (mkPt (-K) (-K))) = _
                     rw [dist_comm]; exact dAV⟩
    · exact ⟨0, by simp⟩
    · exact ⟨R.c, dVR⟩
    · exact ⟨R.c, by show dist (chartEquiv 0 w d hdet (mkPt (1 - K) 1)) (chartEquiv 0 w d hdet (mkPt (-K) (-K))) = _
                     rw [dist_comm]; exact dAR⟩
    · exact ⟨R.c, by show dist (chartEquiv 0 w d hdet (mkPt (1 - K) 1)) (chartEquiv 0 w d hdet (mkPt 1 0)) = _
                     rw [dist_comm]; exact dVR⟩
    · exact ⟨0, by simp⟩
  · show cornerAngle (chartEquiv 0 w d hdet (mkPt 1 0)) (chartEquiv 0 w d hdet (mkPt (-K) (-K)))
      (chartEquiv 0 w d hdet (mkPt (1 - K) 1)) = _
    exact equi_angle _ _ _ R.c hc0 (by rw [dist_comm]; exact dAV) (by rw [dist_comm]; exact dAR) dVR
  · show cornerAngle (chartEquiv 0 w d hdet (mkPt (1 - K) 1)) (chartEquiv 0 w d hdet (mkPt 1 0))
      (chartEquiv 0 w d hdet (mkPt (-K) (-K))) = _
    exact equi_angle _ _ _ R.c hc0 (by rw [dist_comm]; exact dVR) dAV (by rw [dist_comm]; exact dAR)
  · show cornerAngle (chartEquiv 0 w d hdet (mkPt (-K) (-K))) (chartEquiv 0 w d hdet (mkPt (1 - K) 1))
      (chartEquiv 0 w d hdet (mkPt 1 0)) = _
    exact equi_angle _ _ _ R.c hc0 dAR dVR dAV

theorem equi_all (R : RTri) (hγ : R.a ^ 2 + R.a * R.b + R.b ^ 2 = R.c ^ 2) :
    ∃ T : Tri, RatSimDiss R.Δ T.carrier ∧ IsRationalTri T ∧
      cornerAngle (T.pts 1) (T.pts 0) (T.pts 2) = Real.pi / 3 ∧
      cornerAngle (T.pts 2) (T.pts 1) (T.pts 0) = Real.pi / 3 ∧
      cornerAngle (T.pts 0) (T.pts 2) (T.pts 1) = Real.pi / 3 := by
  rcases lt_trichotomy R.b R.a with hab | hab | hab
  · exact equi_lt R hγ hab
  · exact absurd hab.symm (a_ne_b R hγ)
  · have hγ' : R.sw01.a ^ 2 + R.sw01.a * R.sw01.b + R.sw01.b ^ 2 = R.sw01.c ^ 2 := by
      simp only [RTri.sw01]; linarith [hγ]
    have hlt : R.sw01.b < R.sw01.a := by simp only [RTri.sw01]; exact hab
    obtain ⟨T, h1, h2, a1, a2, a3⟩ := equi_lt R.sw01 hγ' hlt
    exact ⟨T, RatSimDiss.relabel (Δ := R.Δ) (Equiv.swap 0 1) h1, h2, a1, a2, a3⟩

#print axioms equi_all

end Erdos634.LaczL33
