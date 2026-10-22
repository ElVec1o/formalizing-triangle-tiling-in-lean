import Erdos634.BADL2
import Erdos634.BaseBetaE1

/-!
# BAD layer L2, step S0: the angle data from the side lengths

Written 2026-10-03.  UNAUDITED.  From the side lengths `(ef, f²-e², f²)` of the model (opposite the
vertices `σ 0, σ 1, σ 2`, `0 < e < f`) the law of cosines gives `cos α = (2f²-e²)/(2f²)`,
`cos β = e(3f²-e²)/(2f³)`, then `3α+2β = π`, and Niven gives `α/π` irrational.  For an isosceles
target with legs `X` and base `Y` with `Y/(2X) = cos α` the base angles equal `α`.
-/

namespace Erdos634.BADL2
open Erdos634.Geometry

noncomputable section

theorem ang_bounds (T : Tri) (k : Fin 3) : 0 ≤ T.angleAt k ∧ T.angleAt k ≤ Real.pi :=
  ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩

theorem opp_pos (T : Tri) (k : Fin 3) : 0 < T.oppLen k := by
  unfold Tri.oppLen
  apply dist_pos.mpr
  intro h
  have := T.indep.injective h
  fin_cases k <;> simp at this

theorem cos_laws (T : Tri) :
    2 * T.oppLen 1 * T.oppLen 2 * Real.cos (T.angleAt 0)
        = T.oppLen 1 ^ 2 + T.oppLen 2 ^ 2 - T.oppLen 0 ^ 2 ∧
    2 * T.oppLen 2 * T.oppLen 0 * Real.cos (T.angleAt 1)
        = T.oppLen 2 ^ 2 + T.oppLen 0 ^ 2 - T.oppLen 1 ^ 2 ∧
    2 * T.oppLen 0 * T.oppLen 1 * Real.cos (T.angleAt 2)
        = T.oppLen 0 ^ 2 + T.oppLen 1 ^ 2 - T.oppLen 2 ^ 2 := by
  have o0 : T.oppLen 0 = dist (T.pts 1) (T.pts 2) := rfl
  have o1 : T.oppLen 1 = dist (T.pts 2) (T.pts 0) := rfl
  have o2 : T.oppLen 2 = dist (T.pts 0) (T.pts 1) := rfl
  have a0 : T.angleAt 0 = EuclideanGeometry.angle (V := Plane) (T.pts 1) (T.pts 0) (T.pts 2) := rfl
  have a1 : T.angleAt 1 = EuclideanGeometry.angle (V := Plane) (T.pts 2) (T.pts 1) (T.pts 0) := rfl
  have a2 : T.angleAt 2 = EuclideanGeometry.angle (V := Plane) (T.pts 0) (T.pts 2) (T.pts 1) := rfl
  have l0 := EuclideanGeometry.law_cos (V := Plane) (T.pts 1) (T.pts 0) (T.pts 2)
  have l1 := EuclideanGeometry.law_cos (V := Plane) (T.pts 2) (T.pts 1) (T.pts 0)
  have l2 := EuclideanGeometry.law_cos (V := Plane) (T.pts 0) (T.pts 2) (T.pts 1)
  rw [dist_comm (T.pts 1) (T.pts 0)] at l0
  rw [dist_comm (T.pts 2) (T.pts 1)] at l1
  rw [dist_comm (T.pts 0) (T.pts 2)] at l2
  rw [o0, o1, o2, a0, a1, a2]
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith [l0, l1, l2]

/-- the three cosine laws, transported along a labelling `σ` of the sides. -/
theorem cos_laws_perm (T : Tri) (σ : Equiv.Perm (Fin 3)) (a b c : ℝ)
    (hl0 : T.oppLen (σ 0) = a) (hl1 : T.oppLen (σ 1) = b) (hl2 : T.oppLen (σ 2) = c) :
    2 * b * c * Real.cos (T.angleAt (σ 0)) = b ^ 2 + c ^ 2 - a ^ 2 ∧
    2 * a * c * Real.cos (T.angleAt (σ 1)) = a ^ 2 + c ^ 2 - b ^ 2 ∧
    2 * a * b * Real.cos (T.angleAt (σ 2)) = a ^ 2 + b ^ 2 - c ^ 2 := by
  obtain ⟨b0, b1, b2⟩ := cos_laws T
  have h01 : σ 0 ≠ σ 1 := fun h => absurd (σ.injective h) (by decide)
  have h02 : σ 0 ≠ σ 2 := fun h => absurd (σ.injective h) (by decide)
  have h12 : σ 1 ≠ σ 2 := fun h => absurd (σ.injective h) (by decide)
  rcases perm3 _ _ _ h01 h02 h12 with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
    ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;>
  · rw [h0] at hl0 ⊢
    rw [h1] at hl1 ⊢
    rw [h2] at hl2 ⊢
    rw [hl0, hl1, hl2] at b0 b1 b2
    refine ⟨?_, ?_, ?_⟩ <;> linarith

theorem tile_angles (T : Tri) (σ : Equiv.Perm (Fin 3)) (e f : ℤ) (h0 : 0 < e) (hef : e < f)
    (hl0 : T.oppLen (σ 0) = (e : ℝ) * f) (hl1 : T.oppLen (σ 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hl2 : T.oppLen (σ 2) = (f : ℝ) ^ 2) :
    Real.cos (T.angleAt (σ 0)) = (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (2 * (f : ℝ) ^ 2) ∧
    3 * T.angleAt (σ 0) + 2 * T.angleAt (σ 1) = Real.pi ∧
    T.angleAt (σ 2) = Real.pi - T.angleAt (σ 0) - T.angleAt (σ 1) ∧
    ¬∃ r : ℚ, T.angleAt (σ 0) = r * Real.pi := by
  obtain ⟨c0, c1, c2⟩ := cos_laws_perm T σ _ _ _ hl0 hl1 hl2
  have he : (0 : ℝ) < e := by exact_mod_cast h0
  have hf : (0 : ℝ) < f := by exact_mod_cast lt_trans h0 hef
  have hef' : (e : ℝ) < f := by exact_mod_cast hef
  have hb : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hcα : Real.cos (T.angleAt (σ 0)) = (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (2 * (f : ℝ) ^ 2) := by
    rw [eq_div_iff (by positivity)]
    have hbc : (0 : ℝ) < 2 * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * (f : ℝ) ^ 2 := by positivity
    apply mul_left_cancel₀ (ne_of_gt hbc)
    nlinarith [c0]
  have hcβ : Real.cos (T.angleAt (σ 1)) = (e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
      / (2 * (f : ℝ) ^ 3) := by
    rw [eq_div_iff (by positivity)]
    have hac : (0 : ℝ) < 2 * ((e : ℝ) * f) * (f : ℝ) ^ 2 := by positivity
    apply mul_left_cancel₀ (ne_of_gt hac)
    nlinarith [c1]
  obtain ⟨α0, α1⟩ := ang_bounds T (σ 0)
  obtain ⟨β0, β1⟩ := ang_bounds T (σ 1)
  have hα3 : T.angleAt (σ 0) ≤ Real.pi / 3 := by
    by_contra hlt
    push Not at hlt
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) α1 hlt
    rw [Real.cos_pi_div_three, hcα] at this
    rw [div_lt_iff₀ (by positivity)] at this
    nlinarith
  have hβ2 : T.angleAt (σ 1) ≤ Real.pi / 2 := by
    by_contra hlt
    push Not at hlt
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) β1 hlt
    rw [Real.cos_pi_div_two, hcβ] at this
    have : 0 ≤ (e : ℝ) * (3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (2 * (f : ℝ) ^ 3) := by
      apply div_nonneg
      · apply mul_nonneg he.le; nlinarith
      · positivity
    linarith
  have key : 3 * T.angleAt (σ 0) = Real.pi - 2 * T.angleAt (σ 1) := by
    refine Real.injOn_cos ?_ ?_ ?_
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
    · rw [Real.cos_pi_sub, Real.cos_three_mul, Real.cos_two_mul, hcα, hcβ]
      field_simp
      ring
  have h3 : 3 * T.angleAt (σ 0) + 2 * T.angleAt (σ 1) = Real.pi := by linarith
  refine ⟨hcα, h3, ?_, ?_⟩
  · have hs := T.angleAt_sum
    have hperm : T.angleAt (σ 0) + T.angleAt (σ 1) + T.angleAt (σ 2) = Real.pi := by
      have := Equiv.sum_comp σ (fun k => T.angleAt k)
      rw [Fin.sum_univ_three, Fin.sum_univ_three] at this
      linarith [T.angleAt_sum]
    linarith
  · have hsin : Real.sin (T.angleAt (σ 0) / 2) = (e.toNat : ℝ) / (2 * (f.toNat : ℝ)) := by
      have e1 : ((e.toNat : ℕ) : ℝ) = (e : ℝ) := by exact_mod_cast Int.toNat_of_nonneg h0.le
      have f1 : ((f.toNat : ℕ) : ℝ) = (f : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg (lt_trans h0 hef).le
      rw [e1, f1]
      have hsq : Real.sin (T.angleAt (σ 0) / 2) ^ 2 = ((e : ℝ) / (2 * f)) ^ 2 := by
        have h1 := Real.cos_two_mul (T.angleAt (σ 0) / 2)
        have h2 := Real.sin_sq_add_cos_sq (T.angleAt (σ 0) / 2)
        rw [show 2 * (T.angleAt (σ 0) / 2) = T.angleAt (σ 0) by ring] at h1
        have hs : Real.sin (T.angleAt (σ 0) / 2) ^ 2 = (1 - Real.cos (T.angleAt (σ 0))) / 2 := by
          linarith
        rw [hs, hcα]
        field_simp
        ring
      have hnn : 0 ≤ Real.sin (T.angleAt (σ 0) / 2) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
      exact (pow_left_inj₀ hnn (by positivity) (by norm_num)).mp hsq
    exact Erdos634.BaseBetaE1.tile_alpha_irrational e.toNat f.toNat
      (by omega) (by omega) _ hsin

end

end Erdos634.BADL2

#print axioms Erdos634.BADL2.tile_angles
