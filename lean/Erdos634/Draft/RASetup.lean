-- Draft/RASetup.lean — Row 13 with the area identity: on the base-(α+β) target `(α+β, α+β, α)`,
-- `s = a/c`, an integer `K` with `K c (1−s) = X` (the leg) and `N (1+s) = K² (1−s)`.
-- The setup of Theorem R-A (S5).  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
import Erdos634.Draft.FluxDRow13
import Erdos634.Draft.FluxDRow12b

open scoped Classical

namespace Erdos634.Geometry

variable {N : ℕ}

set_option maxHeartbeats 4000000 in
theorem Row13.setup (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
    (h : D.model.ThreeAlphaData α β a b c)
    (hP0 : D.target.angleAt 0 = α + β) (hP1 : D.target.angleAt 1 = α + β) :
    ∃ (s : ℝ) (K : ℤ), 0 < s ∧ s < 1 ∧ 0 < c ∧ a = s * c ∧ b = (1 - s ^ 2) * c ∧
      D.target.oppLen 1 = D.target.oppLen 0 ∧ D.target.oppLen 2 = s * D.target.oppLen 0 ∧
      (K : ℝ) * c * (1 - s) = D.target.oppLen 0 ∧
      (N : ℝ) * (1 + s) = (K : ℝ) ^ 2 * (1 - s) := by
  have hP2 : D.target.angleAt 2 = α := by
    have := D.target.angleAt_sum; rw [hP0, hP1] at this; linarith
  obtain ⟨K, M, -, -, -, -, hK, hM⟩ := Row13.boundary D hα hrel h hP0 hP1 hP2
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  obtain ⟨tγ, tα, tβ, -⟩ := threeAlpha_sin_table hrel
  have ls1 := D.model.lawSin (σ 0) (σ 2)
  have ls2 := D.model.lawSin (σ 1) (σ 2)
  rw [h0, o2, h2, o0, tα, tγ] at ls1
  rw [h1, o2, h2, o1, tβ, tγ] at ls2
  have hαpos : 0 < α := h0 ▸ D.model.angleAt_pos' (σ 0)
  have hβpos : 0 < β := h1 ▸ D.model.angleAt_pos' (σ 1)
  have hπ := Real.pi_pos
  have hAB : Real.sin (α + β) = Real.cos (α / 2) := by
    rw [show α + β = Real.pi - (2 * α + β) by linarith, Real.sin_pi_sub, tγ]
  have lt0 := D.target.lawSin 0 2
  have lt1 := D.target.lawSin 1 2
  rw [hP0, hP2, hAB, tα] at lt0
  rw [hP1, hP2, hAB, tα] at lt1
  have hco : 0 < Real.cos (α / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs0 : 0 < Real.sin (α / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hs1 : Real.sin (α / 2) < 1 / 2 := by
    rw [← Real.sin_pi_div_six]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  have hc : 0 < c := o2 ▸ D.model.oppLen_pos (σ 2)
  have hX : 0 < D.target.oppLen 0 := D.target.oppLen_pos 0
  set u := Real.sin (α / 2) with hudef
  set co := Real.cos (α / 2) with hcodef
  set X := D.target.oppLen 0 with hXdef
  set X₁ := D.target.oppLen 1 with hX1def
  set Y := D.target.oppLen 2 with hYdef
  have ha : a = 2 * u * c := mul_left_cancel₀ hco.ne' (by linear_combination (-1 : ℝ) * ls1)
  have hb : b = (1 - 4 * u ^ 2) * c := mul_left_cancel₀ hco.ne' (by linear_combination (-1 : ℝ) * ls2)
  -- `Y = sX`, `X₁ = X`
  have hY : Y = 2 * u * X := mul_left_cancel₀ hco.ne' (by linear_combination lt0)
  have hY1 : Y = 2 * u * X₁ := mul_left_cancel₀ hco.ne' (by linear_combination lt1)
  have hX1 : X₁ = X := mul_left_cancel₀ (mul_pos two_pos hs0).ne' (by linear_combination hY - hY1)
  rw [hX1, hY, ha, hb] at hK hM
  -- `K c (1 − s) = X`, `M c (1 + s) = X` (`s = 2u`)
  have hKc : (K : ℝ) * c * (1 - 2 * u) = X := by
    have e : (2 + 2 * u) * ((K : ℝ) * c * (1 - 2 * u) - X) = 0 := by linear_combination hK
    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left (by linarith))
  have hMc : (M : ℝ) * c * (1 + 2 * u) = X := by
    have e : (2 - 2 * u) * ((M : ℝ) * c * (1 + 2 * u) - X) = 0 := by linear_combination hM
    exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left (by linarith))
  -- area identity
  have hKpos : (0 : ℝ) < K := by
    by_contra hn; push Not at hn
    have := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hn hc.le)
      (by linarith : (0 : ℝ) ≤ 1 - 2 * u)
    linarith
  have hXpos : 0 < X := hX
  have hA := D.abs_detTri_target
  have hsq : Erdos634.AreaDet.detTri D.target ^ 2
      = (N : ℝ) ^ 2 * Erdos634.AreaDet.detTri D.model ^ 2 := by
    rw [← sq_abs (Erdos634.AreaDet.detTri D.target), hA, mul_pow, sq_abs]
  have hT := D.target.four_detTri_sq_symm
  have hMo := D.model.four_detTri_sq_symm
  rw [Tri.sum_pow_perm' D.model 2 σ, Tri.sum_pow_perm' D.model 4 σ, o0, o1, o2] at hMo
  rw [Fin.sum_univ_three, Fin.sum_univ_three, ← hXdef, ← hX1def, ← hYdef, hX1, hY] at hT
  rw [ha, hb] at hMo
  have hs0' : 0 < 2 * u := by linarith
  have hs1' : 2 * u < 1 := by linarith
  have hkey : (2 * u) ^ 2 * (4 - (2 * u) ^ 2) *
      ((X ^ 2 - N * c ^ 2 * (1 - (2 * u) ^ 2)) * (X ^ 2 + N * c ^ 2 * (1 - (2 * u) ^ 2))) = 0 := by
    linear_combination (-1 : ℝ) * hT + (N : ℝ) ^ 2 * hMo + 4 * hsq
  have hlt1 : (2 * u) ^ 2 < 1 := pow_lt_one₀ hs0'.le hs1' (by norm_num)
  have hG : 0 < (2 * u) ^ 2 * (4 - (2 * u) ^ 2) :=
    mul_pos (pow_pos hs0' 2) (by linarith)
  have hpos2 : 0 < X ^ 2 + N * c ^ 2 * (1 - (2 * u) ^ 2) :=
    add_pos_of_pos_of_nonneg (pow_pos hXpos 2)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg N) (sq_nonneg c)) (by linarith))
  have hArea : X ^ 2 = N * c ^ 2 * (1 - (2 * u) ^ 2) := by
    rcases mul_eq_zero.mp hkey with e | e
    · exact absurd e hG.ne'
    · rcases mul_eq_zero.mp e with e' | e'
      · linarith
      · exact absurd e' hpos2.ne'
  have hfin : c ^ 2 * (1 - 2 * u) * ((N : ℝ) * (1 + 2 * u) - (K : ℝ) ^ 2 * (1 - 2 * u)) = 0 := by
    have : ((K : ℝ) * c * (1 - 2 * u)) ^ 2 = N * c ^ 2 * (1 - (2 * u) ^ 2) := by rw [hKc]; exact hArea
    linear_combination (-1 : ℝ) * this
  have hne : c ^ 2 * (1 - 2 * u) ≠ 0 := by
    have : 0 < 1 - 2 * u := by linarith
    exact (mul_pos (pow_pos hc 2) this).ne'
  refine ⟨2 * u, K, hs0', hs1', hc, ha, by rw [hb]; ring, hX1, hY, hKc, ?_⟩
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfin).resolve_left hne)

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row13.setup
