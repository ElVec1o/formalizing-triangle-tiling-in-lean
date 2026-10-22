import Erdos634.Draft.LaczFormalTrapChart3

/-!
# Laczkovich Lemma 2.2 (iii) with ALL FOUR printed angles (isosceles trapezoid)

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Lemma 2.2 (iii): "every rational isosceles trapezoid with angles
`β, β, α+γ, α+γ`"), Beeson, Beeson-Zhang, Zhang.

`lemma22_iii_four`: a convex quadrilateral `A B C D` (counterclockwise) with `‖AB‖ = W`, `‖AD‖ = D` rational and ANGLES `∠DAB = ∠ABC = β`,
`∠BCD = ∠CDA = α+γ` is a finite union of rational triangles similar to `Δ`; parallelism `C - D = τ (B - A)`, `τ = tTauI a b c W D`, and
the leg `‖BC‖ = D` are DERIVED (`Z sin β = D sin β` from the two equal base angles).  Same method as `lemma22_ii_four` (TrapChart3).
Witness `wit_iii_four`: tile `(2,3,4)`, `W = 4`, `D = 1`, `τ = 21/32`.
-/

namespace Erdos634.LaczTrapChart

open Erdos634 Erdos634.Geometry Erdos634.CertCoord Erdos634.LaczL22 Erdos634.LaczL24 Erdos634.LaczL35 Erdos634.LaczL37
  EuclideanGeometry

set_option maxHeartbeats 3200000 in
/-- **Laczkovich Lemma 2.2 (iii) with all four printed angles** (isosceles trapezoid `β, β, α+γ, α+γ`; the leg `|BC| = D` and the parallelism are DERIVED). -/
theorem lemma22_iii_four (R : RTri) (A B C D : Plane) (W Dd : ℚ) (hW : 0 < W) (hD : 0 < Dd)
    (hwn : ‖B - A‖ = W) (hdn : ‖D - A‖ = Dd)
    (hAng : ∠ B A D = vang R.Δ 1) (hBng : ∠ A B C = vang R.Δ 1)
    (_hCng : ∠ B C D = vang R.Δ 0 + vang R.Δ 2) (hDng : ∠ C D A = vang R.Δ 0 + vang R.Δ 2)
    (o1 : 0 < (B 0 - A 0) * (C 1 - B 1) - (B 1 - A 1) * (C 0 - B 0))
    (_o2 : 0 < (C 0 - B 0) * (D 1 - C 1) - (C 1 - B 1) * (D 0 - C 0))
    (o3 : 0 < (D 0 - C 0) * (A 1 - D 1) - (D 1 - C 1) * (A 0 - D 0))
    (o4 : 0 < (A 0 - D 0) * (B 1 - A 1) - (A 1 - D 1) * (B 0 - A 0)) :
    C - D = ((tTauI R.a R.b R.c W Dd : ℚ) : ℝ) • (B - A) ∧ RatSimDiss R.Δ (convexHull ℝ {A, B, C, D}) := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hDr : (0 : ℝ) < Dd := by exact_mod_cast hD
  have ha : (0 : ℝ) < R.a := by exact_mod_cast R.pa
  have hb : (0 : ℝ) < R.b := by exact_mod_cast R.pb
  have hc : (0 : ℝ) < R.c := by exact_mod_cast R.pc
  have hsum := vang_sum R.Δ
  have hcb := RTri.cos_vang1 R
  have hcg := RTri.cos_vang2 R
  obtain ⟨hsin, hsb, hsg⟩ := sin_rel R
  have hag : vang R.Δ 0 + vang R.Δ 2 = Real.pi - vang R.Δ 1 := by linarith
  have hab : vang R.Δ 0 + vang R.Δ 1 = Real.pi - vang R.Δ 2 := by linarith
  obtain ⟨E1d, E1c⟩ := angleD B A D _ hAng
  obtain ⟨E4d, E4c⟩ := angleD A D C (vang R.Δ 0 + vang R.Δ 2) (by rw [angle_comm]; exact hDng)
  obtain ⟨E2d, E2c⟩ := angleD C B A (vang R.Δ 1) (by rw [angle_comm]; exact hBng)
  rw [hag, Real.cos_pi_sub] at E4d
  rw [hag, Real.sin_pi_sub] at E4c
  have nAD : ‖A - D‖ = Dd := by rw [norm_sub_rev]; exact hdn
  have nAB : ‖A - B‖ = W := by rw [norm_sub_rev]; exact hwn
  rw [hwn, hdn] at E1d E1c
  rw [nAD] at E4d E4c
  rw [nAB] at E2d E2c
  have E1c' := E1c (by
    have e : (B 0 - A 0) * (D 1 - A 1) - (B 1 - A 1) * (D 0 - A 0) = (A 0 - D 0) * (B 1 - A 1) - (A 1 - D 1) * (B 0 - A 0) := by ring
    rw [e]; exact o4)
  have E4c' := E4c (by
    have e : (A 0 - D 0) * (C 1 - D 1) - (A 1 - D 1) * (C 0 - D 0) = (D 0 - C 0) * (A 1 - D 1) - (D 1 - C 1) * (A 0 - D 0) := by ring
    rw [e]; exact o3)
  have E2c' := E2c (by
    have e : (C 0 - B 0) * (A 1 - B 1) - (C 1 - B 1) * (A 0 - B 0) = (B 0 - A 0) * (C 1 - B 1) - (B 1 - A 1) * (C 0 - B 0) := by ring
    rw [e]; exact o1)
  obtain ⟨n, hn⟩ : ∃ n, n = ‖C - D‖ := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = ‖C - B‖ := ⟨_, rfl⟩
  rw [← hn] at E4d E4c'
  rw [← hZ] at E2d E2c'
  have hnpos : 0 < n := by
    rcases (hn ▸ norm_nonneg (C - D)).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at E4c'
      have : (0 : ℝ) < (A 0 - D 0) * (C 1 - D 1) - (A 1 - D 1) * (C 0 - D 0) := by
        have e : (A 0 - D 0) * (C 1 - D 1) - (A 1 - D 1) * (C 0 - D 0) = (D 0 - C 0) * (A 1 - D 1) - (D 1 - C 1) * (A 0 - D 0) := by ring
        rw [e]; exact o3
      rw [E4c'] at this
      simp at this
  have hvv : (D 0 - A 0) ^ 2 + (D 1 - A 1) ^ 2 = (Dd : ℝ) ^ 2 := by
    have := norm_sq_plane (D - A)
    rw [hdn] at this
    simp only [PiLp.sub_apply] at this
    linarith
  have huu : (B 0 - A 0) ^ 2 + (B 1 - A 1) ^ 2 = (W : ℝ) ^ 2 := by
    have := norm_sq_plane (B - A)
    rw [hwn] at this
    simp only [PiLp.sub_apply] at this
    linarith
  obtain ⟨h0, h1⟩ := trap_alg1 (B 0 - A 0) (B 1 - A 1) (D 0 - A 0) (D 1 - A 1) (C 0 - D 0) (C 1 - D 1) W Dd n
    (Real.cos (vang R.Δ 1)) (Real.sin (vang R.Δ 1)) hDr hvv
    (by linear_combination E1d) (by linear_combination E1c')
    (by linear_combination (-1) * E4d) (by linear_combination E4c')
  set τ : ℝ := n / W with hτdef
  have hτpos : 0 < τ := by positivity
  have hw0 : C 0 - D 0 = τ * (B 0 - A 0) := by rw [hτdef]; field_simp; linarith
  have hw1 : C 1 - D 1 = τ * (B 1 - A 1) := by rw [hτdef]; field_simp; linarith
  have hCD : C - D = τ • (B - A) := by
    ext i
    fin_cases i
    · simpa using hw0
    · simpa using hw1
  have e1 : Z * Real.sin (vang R.Δ 1) = Dd * Real.sin (vang R.Δ 1) := by
    have : (W : ℝ) * (Z * Real.sin (vang R.Δ 1)) = W * (Dd * Real.sin (vang R.Δ 1)) := by
      linear_combination (-1) * E2c' + (-(B 1 - A 1)) * hw0 + (B 0 - A 0) * hw1 + E1c'
    exact mul_left_cancel₀ hWr.ne' this
  have e2 : (τ - 1) * W + Dd * Real.cos (vang R.Δ 1) = -(Z * Real.cos (vang R.Δ 1)) := by
    have : (W : ℝ) * ((τ - 1) * W + Dd * Real.cos (vang R.Δ 1)) = W * (-(Z * Real.cos (vang R.Δ 1))) := by
      linear_combination (-1) * E2d + (-(τ - 1)) * huu + (-1) * E1d + (-(B 0 - A 0)) * hw0 + (-(B 1 - A 1)) * hw1
    exact mul_left_cancel₀ hWr.ne' this
  have hZD : Z = Dd := mul_right_cancel₀ hsb.ne' e1
  rw [hZD] at e2
  have hτq : ((tTauI R.a R.b R.c W Dd : ℚ) : ℝ) = τ := by
    simp only [tTauI]
    push_cast
    rw [hcb] at e2
    field_simp at e2 ⊢
    nlinarith [e2]
  have hC' : C - D = ((tTauI R.a R.b R.c W Dd : ℚ) : ℝ) • (B - A) := by rw [hτq]; exact hCD
  have hpos : 0 < tTauI R.a R.b R.c W Dd := by
    have : (0 : ℝ) < ((tTauI R.a R.b R.c W Dd : ℚ) : ℝ) := by rw [hτq]; exact hτpos
    exact_mod_cast this
  exact ⟨hC', lemma22_iii_vert R A B C D W Dd hW hD hwn hdn hAng hpos hC'⟩


set_option maxHeartbeats 3200000 in
/-- **Witness for `lemma22_iii_four`** (every hypothesis holds): tile `(2,3,4)`, `A = (0,0)`, `B = (4,0)`, `C = (53/16, √135/16)`, `D = (11/16, √135/16)`;
angles `β, β, α+γ, α+γ`, counterclockwise, `‖BC‖ = 1 = ‖AD‖`. -/
theorem wit_iii_four :
    RatSimDiss R234.Δ (convexHull ℝ {mkPt 0 0, mkPt 4 0, mkPt (53 / 16) (Real.sqrt 135 / 16),
      mkPt (11 / 16) (Real.sqrt 135 / 16)}) := by
  have h135 : Real.sqrt 135 * Real.sqrt 135 = 135 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 135 := Real.sqrt_pos.mpr (by norm_num)
  have hpi := Real.pi_pos
  have hcb : Real.cos (vang R234.Δ 1) = 11 / 16 := by rw [RTri.cos_vang1]; simp [R234]; norm_num
  have hsum := vang_sum R234.Δ
  have g0 : 0 ≤ vang R234.Δ 0 := angle_nonneg _ _ _
  have g1 : 0 ≤ vang R234.Δ 1 := angle_nonneg _ _ _
  have g2 : 0 ≤ vang R234.Δ 2 := angle_nonneg _ _ _
  have hag : vang R234.Δ 0 + vang R234.Δ 2 = Real.pi - vang R234.Δ 1 := by linarith
  have hwn : ‖mkPt 4 0 - mkPt 0 0‖ = ((4 : ℚ) : ℝ) := by
    rw [mkPt_sub]; exact norm_mkPt_of _ _ _ (by norm_num) (by norm_num)
  have hdn : ‖mkPt (11 / 16) (Real.sqrt 135 / 16) - mkPt 0 0‖ = ((1 : ℚ) : ℝ) := by
    rw [mkPt_sub]; exact norm_mkPt_of _ _ _ (by norm_num) (by push_cast; nlinarith)
  have hAng : ∠ (mkPt 4 0) (mkPt 0 0) (mkPt (11 / 16) (Real.sqrt 135 / 16)) = vang R234.Δ 1 := by
    apply ang_of _ _ _ _ 4 1 (11 / 16) g1 (by linarith) (by rw [hwn]; norm_num) (by rw [hdn]; norm_num) (by norm_num) (by norm_num)
    · rw [mkPt_sub, mkPt_sub, inner_mkPt]; norm_num
    · exact hcb
  have hBng : ∠ (mkPt 0 0) (mkPt 4 0) (mkPt (53 / 16) (Real.sqrt 135 / 16)) = vang R234.Δ 1 := by
    apply ang_of _ _ _ _ 4 1 (11 / 16) g1 (by linarith)
    · rw [mkPt_sub]; exact norm_mkPt_of _ _ _ (by norm_num) (by norm_num)
    · rw [mkPt_sub]; exact norm_mkPt_of _ _ _ (by norm_num) (by nlinarith)
    · norm_num
    · norm_num
    · rw [mkPt_sub, mkPt_sub, inner_mkPt]; norm_num
    · exact hcb
  have hCng : ∠ (mkPt 4 0) (mkPt (53 / 16) (Real.sqrt 135 / 16)) (mkPt (11 / 16) (Real.sqrt 135 / 16))
      = vang R234.Δ 0 + vang R234.Δ 2 := by
    rw [hag]
    apply ang_of _ _ _ _ 1 (21 / 8) (-11 / 16) (by linarith) (by linarith)
    · rw [mkPt_sub]; exact norm_mkPt_of _ _ _ (by norm_num) (by nlinarith)
    · rw [mkPt_sub]; exact norm_mkPt_of _ _ _ (by norm_num) (by norm_num)
    · norm_num
    · norm_num
    · rw [mkPt_sub, mkPt_sub, inner_mkPt]; norm_num
    · rw [Real.cos_pi_sub, hcb]; norm_num
  have hDng : ∠ (mkPt (53 / 16) (Real.sqrt 135 / 16)) (mkPt (11 / 16) (Real.sqrt 135 / 16)) (mkPt 0 0)
      = vang R234.Δ 0 + vang R234.Δ 2 := by
    rw [hag]
    apply ang_of _ _ _ _ (21 / 8) 1 (-11 / 16) (by linarith) (by linarith)
    · rw [mkPt_sub]; exact norm_mkPt_of _ _ _ (by norm_num) (by norm_num)
    · rw [mkPt_sub]; exact norm_mkPt_of _ _ _ (by norm_num) (by nlinarith)
    · norm_num
    · norm_num
    · rw [mkPt_sub, mkPt_sub, inner_mkPt]; norm_num
    · rw [Real.cos_pi_sub, hcb]; norm_num
  have key := lemma22_iii_four R234 (mkPt 0 0) (mkPt 4 0) (mkPt (53 / 16) (Real.sqrt 135 / 16)) (mkPt (11 / 16) (Real.sqrt 135 / 16))
    4 1 (by norm_num) (by norm_num) hwn hdn hAng hBng hCng hDng
    (by simp only [PiLp.sub_apply, mkPt_zero, mkPt_one]; nlinarith)
    (by simp only [PiLp.sub_apply, mkPt_zero, mkPt_one]; nlinarith)
    (by simp only [PiLp.sub_apply, mkPt_zero, mkPt_one]; nlinarith)
    (by simp only [PiLp.sub_apply, mkPt_zero, mkPt_one]; nlinarith)
  exact key.2

#print axioms Erdos634.LaczTrapChart.wit_iii_four

#print axioms Erdos634.LaczTrapChart.lemma22_iii_four

end Erdos634.LaczTrapChart
