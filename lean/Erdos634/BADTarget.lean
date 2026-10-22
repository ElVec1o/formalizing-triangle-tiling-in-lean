import Erdos634.BADFluxTile2

/-!
# BAD layer L2, step S3: the target flux is the boundary polynomial

Written 2026-10-03.  UNAUDITED.  For the isosceles target with base angles `α` (angles at vertices 0,1;
sides opposite them `X`, side opposite vertex 2 is `Y`), the anchored flux equals
`Y + X t² + X t⁻²` in `ℝ[T;T⁻¹]`, in both orientations.
-/

open LaurentPolynomial

namespace Erdos634.BADL2
open Erdos634.Geometry

noncomputable section

theorem w0_neg {R : Type*} [CommRing R] (G : GridChar R) (T : Tri) (hT : T.det < 0)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) :
    G.weight (T.leftUnit 0) = G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle)
      * (G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) * G.weight (T.leftUnit 2)) := by
  have t0 := T.leftUnit_turn_of_neg hT 0
  have t1 := T.leftUnit_turn_of_neg hT 1
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl] at t0 t1
  have w1 : G.weight (T.leftUnit 1)
      = G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) * G.weight (T.leftUnit 2) := by
    unfold GridChar.weight
    rw [t1, G.val_add _ (pi_sub_mem' G T h 2)]
  have w0 : G.weight (T.leftUnit 0)
      = G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle) * G.weight (T.leftUnit 1) := by
    unfold GridChar.weight
    rw [t0, G.val_add _ (pi_sub_mem' G T h 1)]
  rw [w0, w1]

theorem target_flux (α β : ℝ) (hα : ¬∃ r : ℚ, α = r * Real.pi) (hβ : 3 * α + 2 * β = Real.pi)
    (X Y : ℝ) (Tt : Tri) (h0 : Tt.angleAt 0 = α) (h1 : Tt.angleAt 1 = α)
    (l0 : Tt.oppLen 0 = X) (l1 : Tt.oppLen 1 = X) (l2 : Tt.oppLen 2 = Y) :
    Tt.flux (gc α β hα hβ (Tt.leftUnit 0).angle).weight
      = C Y + C X * (T 1 : LR) ^ 2 + C X * (T (-1) : LR) ^ 2 := by
  set G := gc α β hα hβ (Tt.leftUnit 0).angle with hG
  have hsum := Tt.angleAt_sum
  have h2 : Tt.angleAt 2 = Real.pi - α - α := by linarith
  have hA : ((Tt.angleAt 0 : ℝ) : Real.Angle) ∈ G.L := by
    rw [h0]; exact mem_coord α β hα hβ _ 1 0 _ (by simp)
  have hB : ((Tt.angleAt 1 : ℝ) : Real.Angle) ∈ G.L := by
    rw [h1]; exact mem_coord α β hα hβ _ 1 0 _ (by simp)
  have hC : ((Tt.angleAt 2 : ℝ) : Real.Angle) ∈ G.L := by
    rw [h2]; exact mem_coord α β hα hβ _ 1 2 _ (by push_cast; linarith)
  have hL : ∀ k, ((Tt.angleAt k : ℝ) : Real.Angle) ∈ G.L := by
    intro k
    fin_cases k
    exacts [hA, hB, hC]
  have c1 : G.chi ((Real.pi - Tt.angleAt 1 : ℝ) : Real.Angle) = T (-1) * T (-1) := by
    rw [h1]; exact chi_Ang α β hα hβ _ 0
  have c2 : G.chi ((Real.pi - Tt.angleAt 2 : ℝ) : Real.Angle) = (T 1 : LR) ^ 4 := by
    rw [chi_coord α β hα hβ _ 2 0 _ (by rw [h2]; push_cast; ring), psi0_apply]
    have e : BAD.ee 2 0 = 1 := by
      unfold BAD.ee
      rw [show (2 : ℤ) - 0 = 2 * 1 by norm_num, Int.negOnePow_two_mul]; rfl
    have k : BAD.kk 2 0 = 4 := by decide
    rw [e, k, T_pow]
    simp only [Int.cast_one, map_one, one_mul]
    norm_num
  have w0 : G.weight (Tt.leftUnit 0) = 1 := G.val_anchor
  have hu : (T 1 : LR) * T (-1) = 1 := T1_mul
  have cX : ∀ r : ℝ, algebraMap ℝ LR r = C r := fun r => (LaurentPolynomial.C_eq_algebraMap r).symm
  rcases Tt.det_pos_or_neg with hT | hT
  · rw [flux_pos_R G Tt hT hL, w0, c1, c2, cX, cX, cX, l0, l1, l2]
    linear_combination (C X * (T 1) ^ 2 * (T 1 * T (-1) + 1)) * hu
  · rw [flux_neg_R G Tt hT hL, c1, c2, cX, cX, cX, l0, l1, l2]
    have H := w0_neg G Tt hT hL
    rw [w0, c1, c2] at H
    set w2 := G.weight (Tt.leftUnit 2)
    have hw2 : w2 = T (-1) * T (-1) := by
      linear_combination (-(T (-1) * T (-1) : LR)) * H
        + (-w2 * (1 + T 1 * T (-1) + (T 1 * T (-1)) ^ 2 + (T 1 * T (-1)) ^ 3)) * hu
    rw [hw2]
    linear_combination (C X * (T 1) ^ 2 * (T 1 * T (-1) + 1)
      + C Y * (T 1 * T (-1) + 1) * ((T 1 * T (-1)) ^ 2 + 1)) * hu

end

end Erdos634.BADL2

#print axioms Erdos634.BADL2.target_flux
