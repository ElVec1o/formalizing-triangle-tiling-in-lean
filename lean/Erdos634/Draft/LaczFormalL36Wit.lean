import Erdos634.Draft.LaczFormalL35Print

/-!
# Witnesses for the printed Theorems 2.4 / 2.5 (`LaczFormalL35Print`)

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94), Beeson, Beeson-Zhang, Zhang.

Every hypothesis of `thm24_printed` is satisfied at `α = 2 arcsin(1/4)` (`sin(α/2) = 1/4`, tile `(2,3,4)` up to scale) with a
triangle `T` of angles `(β, β, 3α)` (the `T` is the triangle produced by `thm24_second_all` for the tile of `tile24`);
every hypothesis of `thm25_printed` is satisfied at `α = arccos(11/14)` (`cos α = 11/14`, `√3 sin α = 15/14`, tile `(5,3,7)` up
to scale) with an equilateral `T`.  The conclusions `PrintedConcl` are obtained from the theorems.
-/

namespace Erdos634.LaczL36

open Erdos634 Erdos634.Geometry Erdos634.LaczL22 Erdos634.LaczL28 Erdos634.LaczL35 EuclideanGeometry

theorem wit24_printed :
    ∃ α β γ : ℝ, 0 < α ∧ α < Real.pi / 3 ∧ (∃ q : ℚ, Real.sin (α / 2) = q) ∧ β = (Real.pi - 3 * α) / 2 ∧
      γ = (Real.pi + α) / 2 ∧ ∃ T : Tri, HasAngles T β β (3 * α) ∧ PrintedConcl T α β γ := by
  set α : ℝ := 2 * Real.arcsin (1 / 4) with hα
  have hsin : Real.sin (α / 2) = ((1 / 4 : ℚ) : ℝ) := by
    rw [hα, show 2 * Real.arcsin (1 / 4) / 2 = Real.arcsin (1 / 4) by ring,
      Real.sin_arcsin (by norm_num) (by norm_num)]
    norm_num
  have h0 : 0 < α := by
    rw [hα]; have := Real.arcsin_pos.mpr (show (0 : ℝ) < 1 / 4 by norm_num); linarith
  have h1 : α < Real.pi / 3 := by
    rw [hα]
    by_contra hc
    push_neg at hc
    have h6 : Real.pi / 6 ≤ Real.arcsin (1 / 4) := by linarith
    have := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (Real.arcsin_le_pi_div_two _) h6
    rw [Real.sin_pi_div_six, Real.sin_arcsin (by norm_num) (by norm_num)] at this
    norm_num at this
  obtain ⟨R, a0, ha0, ha1, hA, hB, r0, r1, r2⟩ := tile24 α h0 h1 (1 / 4) hsin
  obtain ⟨T, q, hq, M, C, hC1, hC2, g1, g2⟩ := thm24_second_all R a0 ha0 ha1 hA hB
  have hβ : (Real.pi - 3 * α) / 2 = (Real.pi - 3 * α) / 2 := rfl
  have t1 : vang T 1 = (Real.pi - 3 * α) / 2 := by rw [← ang1, g1]; rw [ang1]; exact r1
  have t2 : vang T 2 = (Real.pi - 3 * α) / 2 := by rw [← ang2, g2]; rw [ang1]; exact r1
  have t0 : vang T 0 = 3 * α := by have := vang_sum T; linarith
  have hH : HasAngles T ((Real.pi - 3 * α) / 2) ((Real.pi - 3 * α) / 2) (3 * α) :=
    (show HasAngles T (3 * α) ((Real.pi - 3 * α) / 2) ((Real.pi - 3 * α) / 2) from
      ⟨1, by simpa using t0, by simpa using t1, by simpa using t2⟩).s01.s12
  refine ⟨α, (Real.pi - 3 * α) / 2, (Real.pi + α) / 2, h0, h1, ⟨1 / 4, hsin⟩, rfl, rfl, T, hH, ?_⟩
  exact thm24_printed α _ _ h0 h1 ⟨1 / 4, hsin⟩ rfl rfl T (Or.inr (Or.inr (Or.inl hH)))

theorem wit25_printed :
    ∃ α β γ : ℝ, 0 < α ∧ α < Real.pi / 3 ∧ (∃ u : ℚ, Real.sqrt 3 * Real.sin α = u) ∧ (∃ v : ℚ, Real.cos α = v) ∧
      β = Real.pi / 3 - α ∧ γ = 2 * Real.pi / 3 ∧
      ∃ T : Tri, HasAngles T (α + β) (α + β) (α + β) ∧ PrintedConcl T α β γ := by
  set α : ℝ := Real.arccos (11 / 14) with hα
  have hcos : Real.cos α = ((11 / 14 : ℚ) : ℝ) := by
    rw [hα, Real.cos_arccos (by norm_num) (by norm_num)]; norm_num
  have hsin : Real.sqrt 3 * Real.sin α = ((15 / 14 : ℚ) : ℝ) := by
    rw [hα, Real.sin_arccos, ← Real.sqrt_mul (by norm_num),
      show (3 : ℝ) * (1 - (11 / 14) ^ 2) = (15 / 14) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  have h0 : 0 < α := by rw [hα]; exact Real.arccos_pos.mpr (by norm_num)
  have h1 : α < Real.pi / 3 := by
    by_contra hc
    push_neg at hc
    have := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos]) (Real.arccos_le_pi _) hc
    rw [Real.cos_pi_div_three, ← hα, hcos] at this
    norm_num at this
  obtain ⟨R, hRγ, r0, r1, r2⟩ := tile25 α h0 h1 (15 / 14) (11 / 14) hsin hcos
  obtain ⟨T, hT, -, g1, g2, -⟩ := Erdos634.LaczL33.equi_all R hRγ
  have t0 : vang T 0 = Real.pi / 3 := g1
  have t1 : vang T 1 = Real.pi / 3 := g2
  have t2 : vang T 2 = Real.pi / 3 := by have := vang_sum T; linarith
  have hH : HasAngles T (α + (Real.pi / 3 - α)) (α + (Real.pi / 3 - α)) (α + (Real.pi / 3 - α)) :=
    ⟨1, by simpa using (by linarith : vang T 0 = _), by simpa using (by linarith : vang T 1 = _),
      by simpa using (by linarith : vang T 2 = _)⟩
  refine ⟨α, Real.pi / 3 - α, 2 * Real.pi / 3, h0, h1, ⟨15 / 14, hsin⟩, ⟨11 / 14, hcos⟩, rfl, rfl, T, hH, ?_⟩
  exact thm25_printed α _ _ h0 h1 ⟨15 / 14, hsin⟩ ⟨11 / 14, hcos⟩ rfl rfl T
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hH)))))

#print axioms wit24_printed
#print axioms wit25_printed

end Erdos634.LaczL36
