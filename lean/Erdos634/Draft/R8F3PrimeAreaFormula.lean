-- Draft/R8F3PrimeAreaFormula.lean — Area formula for the F3′ target shape.
-- Proves `N = 3 · ν² · (a+b) · (2a+b)` for a CongruentDissection whose model is a 2π/3 tile
-- and whose target is an F3PrimeData shape (angles β, 2β, 3α; sides νc², νc(2a+b), 3νa(a+b)).
-- This is the a↔b mirror of R8F3AreaFormula.
--
-- Key polynomial identity (hc2 : c²=a²+ab+b²):
--   4·det(F3′)² = 27·ν⁴·a²·b²·(a+b)²·(2a+b)²
-- Certificate: ν⁴·(c⁶−(7a²+7ab+b²)c⁴−9a²(a+b)²c²−27a²(a+b)²(3a²+3ab+b²))·(c²−a²−ab−b²)
-- ZERO sorry.

import Erdos634.Draft.FluxCRow2
import Erdos634.Draft.FluxCRow5
import Erdos634.Draft.FluxE2Pi3Row8Mirrors
import Erdos634.Draft.ThmIso

open scoped Classical

namespace Erdos634.Draft.R8F3PrimeAreaFormula

open Erdos634.Geometry Erdos634.AreaDet

private lemma twoPiThree_c_sq (T : Tri) {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
  obtain ⟨σ, -, ha, -, hb, hγ, hc⟩ := h
  have hlc := T.lawCos_perm σ
  rw [ha, hb, hc, hγ,
      show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three] at hlc
  linarith

theorem target_F3prime_four_det_sq {α a b c ν : ℝ} (T : Tri) (h : T.F3PrimeData α a b c ν)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    4 * Erdos634.AreaDet.detTri T ^ 2 =
      27 * ν ^ 4 * a ^ 2 * b ^ 2 * (a + b) ^ 2 * (2 * a + b) ^ 2 := by
  obtain ⟨-, hgrid⟩ := h
  obtain ⟨σ, -, o0, -, o1, -, o2⟩ := hgrid
  have hM := T.four_detTri_sq_sym
  rw [T.sum_perm 2 σ, T.sum_perm 4 σ, o0, o1, o2] at hM
  linear_combination hM -
    ν ^ 4 * (c ^ 6 - (7 * a ^ 2 + 7 * a * b + b ^ 2) * c ^ 4
      - 9 * a ^ 2 * (a + b) ^ 2 * c ^ 2
      - 27 * a ^ 2 * (a + b) ^ 2 * (3 * a ^ 2 + 3 * a * b + b ^ 2)) * hc2

theorem F3prime_area_formula {N : ℕ} (D : CongruentDissection N) {α a b c ν : ℝ}
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : D.target.F3PrimeData α a b c ν)
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν) :
    (N : ℝ) = 3 * ν ^ 2 * (a + b) * (2 * a + b) := by
  have hc2 := twoPiThree_c_sq D.model hm
  have hdet := D.abs_detTri_target
  have hdet_sq : Erdos634.AreaDet.detTri D.target ^ 2 =
      (N : ℝ) ^ 2 * Erdos634.AreaDet.detTri D.model ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hdet
    simp only [mul_pow, sq_abs] at h
    exact h
  have hmod_det := Erdos634.Draft.ThmIso.model_four_det_sq D.model hm
  have htgt_det := target_F3prime_four_det_sq D.target ht hc2
  have key : 27 * ν ^ 4 * a ^ 2 * b ^ 2 * (a + b) ^ 2 * (2 * a + b) ^ 2 =
      3 * (N : ℝ) ^ 2 * a ^ 2 * b ^ 2 := by
    linear_combination -htgt_det + (N : ℝ) ^ 2 * hmod_det + 4 * hdet_sq
  have hν4_eq : 9 * ν ^ 4 * (a + b) ^ 2 * (2 * a + b) ^ 2 = (N : ℝ) ^ 2 :=
    mul_left_cancel₀ (by positivity : (3 : ℝ) * a ^ 2 * b ^ 2 ≠ 0) (by linear_combination key)
  have h_sq_eq : (3 * ν ^ 2 * (a + b) * (2 * a + b)) ^ 2 = (N : ℝ) ^ 2 := by
    have : (3 * ν ^ 2 * (a + b) * (2 * a + b)) ^ 2 =
        9 * ν ^ 4 * (a + b) ^ 2 * (2 * a + b) ^ 2 := by ring
    rw [this, hν4_eq]
  have hLpos : (0 : ℝ) ≤ 3 * ν ^ 2 * (a + b) * (2 * a + b) := by positivity
  have hRpos : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  exact ((pow_left_inj₀ hLpos hRpos two_ne_zero).mp h_sq_eq).symm

#check @F3prime_area_formula
#print axioms F3prime_area_formula

end Erdos634.Draft.R8F3PrimeAreaFormula
