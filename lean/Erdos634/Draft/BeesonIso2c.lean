-- Draft/BeesonIso2c.lean -- Beeson, "Tilings of an isosceles triangle" (arXiv 1206.1974v7), Lemma 12.8, GEOMETRIC form (the analogue for the tile (alpha, pi/3 - alpha, 2 pi/3) of `Row4.sides` + `Row4.P5`'s area step).
--   `beeson_l12_8_geo` : D a CongruentDissection (any N) of an isosceles triangle with base angles alpha (target corners 0 and 1) by the tile (alpha, pi/3 - alpha, 2 pi/3) with opposite sides (a, b, c):
--                        with X = oppLen 0 (leg), Y = oppLen 2 (base):   c^2 = a^2+b^2+ab,  X^2 (2b+a) = N b c^2,  X Y = N b c,  oppLen 1 = oppLen 0.
--   (Algebraic form with the geometric facts as hypotheses: BeesonRow4B.l12_8.)  Hypotheses are exactly the row's; alpha irrational is NOT needed.
-- WITNESS STATUS: no isosceles tiling by this tile is known, so the geometric hypotheses (a CongruentDissection of such a target) are unwitnessed; the algebraic conclusion is witnessed on (3,5,7) by BeesonRow4B.wit_l12_8.
-- NOTE, UNAUDITED.  Credit: Beeson (arXiv 1206.1974v7, Lemma 12.8), Laczkovich, Beeson-Zhang, Herdt, Zhang.
import Erdos634.Draft.FluxDRow4
import Erdos634.Draft.FluxPaper
import Erdos634.Draft.FluxCRow5

open scoped Classical

namespace Erdos634.Draft.BeesonIso2c

open Erdos634.Geometry

variable {N : ℕ}

theorem beeson_l12_8_geo (D : CongruentDissection N) {α a b c : ℝ}
    (h : D.model.TwoPiThreeData α a b c)
    (hA : D.target.angleAt 0 = α) (hB : D.target.angleAt 1 = α) :
    c ^ 2 = a ^ 2 + b ^ 2 + a * b ∧ D.target.oppLen 1 = D.target.oppLen 0 ∧
    D.target.oppLen 0 ^ 2 * (2 * b + a) = N * b * c ^ 2 ∧
    D.target.oppLen 0 * D.target.oppLen 2 = N * b * c := by
  obtain ⟨σ, h0, o0, h1, o1, h2, o2⟩ := h
  have hC : D.target.angleAt 2 = Real.pi - 2 * α := by
    have hs := D.target.angleAt_sum; rw [hA, hB] at hs; linarith
  have hαpos : 0 < α := h0 ▸ D.model.angleAt_pos' (σ 0)
  have hβpos : 0 < Real.pi / 3 - α := h1 ▸ D.model.angleAt_pos' (σ 1)
  have hπ := Real.pi_pos
  have hsα : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hαpos (by linarith)
  have hκpos : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs2 : Real.sin (Real.pi - 2 * α) = 2 * Real.sin α * Real.cos α := by
    rw [Real.sin_pi_sub, Real.sin_two_mul]
  -- target sides
  have lt0 := D.target.lawSin 0 2
  have lt1 := D.target.lawSin 1 2
  rw [hA, hC, hs2] at lt0
  rw [hB, hC, hs2] at lt1
  have hX : 0 < D.target.oppLen 0 := D.target.oppLen_pos 0
  have hY : D.target.oppLen 2 = 2 * Real.cos α * D.target.oppLen 0 :=
    mul_left_cancel₀ hsα.ne' (by linear_combination lt0)
  have hY1 : D.target.oppLen 2 = 2 * Real.cos α * D.target.oppLen 1 :=
    mul_left_cancel₀ hsα.ne' (by linear_combination lt1)
  have hX1 : D.target.oppLen 1 = D.target.oppLen 0 :=
    mul_left_cancel₀ (mul_pos two_pos hκpos).ne' (by linear_combination hY - hY1)
  -- tile: law of cosines at the 2 pi/3 corner and at the alpha corner
  have lc2 := D.model.lawCos_perm σ
  rw [h2, o2, o0, o1] at lc2
  have hcos23 : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
    have : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    rw [this, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num
  rw [hcos23] at lc2
  have hrel : c ^ 2 = a ^ 2 + b ^ 2 + a * b := by linarith
  have lc0 := D.model.lawCos_perm ((Equiv.swap (0 : Fin 3) 2).trans σ)
  have t0 : ((Equiv.swap (0 : Fin 3) 2).trans σ) 0 = σ 2 := by simp
  have t1 : ((Equiv.swap (0 : Fin 3) 2).trans σ) 1 = σ 1 := by
    simp [Equiv.swap_apply_of_ne_of_ne (show (1 : Fin 3) ≠ 0 by decide) (show (1 : Fin 3) ≠ 2 by decide)]
  have t2 : ((Equiv.swap (0 : Fin 3) 2).trans σ) 2 = σ 0 := by simp
  rw [t0, t1, t2, h0, o0, o2, o1] at lc0
  have hbpos : 0 < b := o1 ▸ D.model.oppLen_pos (σ 1)
  have hcpos : 0 < c := o2 ▸ D.model.oppLen_pos (σ 2)
  have hcosα : 2 * c * Real.cos α = 2 * b + a := by
    have : b * (2 * c * Real.cos α - (2 * b + a)) = 0 := by nlinarith [lc0, hrel]
    have := (mul_eq_zero.mp this).resolve_left hbpos.ne'
    linarith
  -- areas
  have hA' := D.abs_detTri_target
  have hsq : Erdos634.AreaDet.detTri D.target ^ 2
      = (N : ℝ) ^ 2 * Erdos634.AreaDet.detTri D.model ^ 2 := by
    rw [← sq_abs (Erdos634.AreaDet.detTri D.target), hA', mul_pow, sq_abs]
  have hT := D.target.four_detTri_sq_symm
  have hMo := D.model.four_detTri_sq_symm
  rw [Tri.sum_pow_perm' D.model 2 σ, Tri.sum_pow_perm' D.model 4 σ, o0, o1, o2] at hMo
  rw [Fin.sum_univ_three, Fin.sum_univ_three, hX1, hY] at hT
  set X := D.target.oppLen 0 with hXdef
  set κ := Real.cos α with hκdef
  have hκ1 : 1 - κ ^ 2 = Real.sin α ^ 2 := by
    have := Real.sin_sq_add_cos_sq α; linarith
  -- 4 det_M^2 = 4 b^2 c^2 - (2bc kappa)^2
  have hMo' : 4 * Erdos634.AreaDet.detTri D.model ^ 2 = 4 * b ^ 2 * c ^ 2 * (1 - κ ^ 2) := by
    rw [hMo]
    have e : 2 * c * κ = 2 * b + a := by linarith
    have h1 : 4 * b ^ 2 * c ^ 2 * (1 - κ ^ 2) = 4 * b ^ 2 * c ^ 2 - (b * (2 * c * κ)) ^ 2 := by ring
    rw [h1, e]
    linear_combination (2 * (a ^ 2 + b ^ 2) - 4 * b ^ 2 - (a ^ 2 + b ^ 2 + a * b) - c ^ 2) * hrel
  have key : (1 - κ ^ 2) * (4 * κ ^ 2 * X ^ 4 - N ^ 2 * (b * c) ^ 2) = 0 := by
    have hT' : 4 * Erdos634.AreaDet.detTri D.target ^ 2 = 16 * κ ^ 2 * (1 - κ ^ 2) * X ^ 4 := by
      rw [hT]; ring
    have : 16 * κ ^ 2 * (1 - κ ^ 2) * X ^ 4 = (N : ℝ) ^ 2 * (4 * b ^ 2 * c ^ 2 * (1 - κ ^ 2)) := by
      rw [← hT', ← hMo']; linear_combination 4 * hsq
    linear_combination (1 / 4 : ℝ) * this
  have h4 : 4 * κ ^ 2 * X ^ 4 = N ^ 2 * (b * c) ^ 2 :=
    sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left (by rw [hκ1]; positivity))
  have h5 : 2 * κ * X ^ 2 = N * (b * c) := by
    have hl : 0 < 2 * κ * X ^ 2 := by positivity
    have hr : 0 ≤ (N : ℝ) * (b * c) := by positivity
    have : (2 * κ * X ^ 2) ^ 2 = ((N : ℝ) * (b * c)) ^ 2 := by linear_combination h4
    exact (sq_eq_sq₀ hl.le hr).mp this
  refine ⟨hrel, hX1, ?_, ?_⟩
  · have : (X ^ 2 * (2 * b + a)) = X ^ 2 * (2 * c * κ) := by rw [← hcosα]
    rw [this]
    linear_combination c * h5
  · rw [hY]; linear_combination h5

end Erdos634.Draft.BeesonIso2c

#print axioms Erdos634.Draft.BeesonIso2c.beeson_l12_8_geo
