-- Draft/R8F4PrimeAreaFormula.lean — Area formula for the F4′ target shape.
-- Proves `N = ν² · (a+b) · (a+2b)` for a CongruentDissection whose model is a 2π/3 tile
-- and whose target is an F4PrimeData shape (angles β, 2α, α+2β; opposite sides νbc, νa(a+2b), νc(a+b)).
--
-- This is the F4′-analogue of R8F4AreaFormula (F4 with a↔b).
-- Proof: two det-sq formulas + abs_detTri_target → square-root argument.
-- ZERO sorry.  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04) (formalization debt, part of R8ReductionStatement).
--
-- Key polynomial identity (hc2 : c²=a²+ab+b²):
--   4·det(F4′)² = 3·ν⁴·a²·b²·(a+b)²·(a+2b)²
-- Coefficient: -ν⁴·a²·(a+2b)²·(c²−a²−3ab−3b²)

import Erdos634.Draft.FluxCRow2
import Erdos634.Draft.FluxCRow5
import Erdos634.Draft.FluxE2Pi3Row8Mirrors
import Erdos634.Draft.ThmIso

open scoped Classical

namespace Erdos634.Draft.R8F4PrimeAreaFormula

open Erdos634.Geometry Erdos634.AreaDet

/-! ## Auxiliary: c² = a²+ab+b² for TwoPiThreeData -/

private lemma twoPiThree_c_sq (T : Tri) {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
  obtain ⟨σ, -, ha, -, hb, hγ, hc⟩ := h
  have hlc := T.lawCos_perm σ
  rw [ha, hb, hc, hγ,
      show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three] at hlc
  linarith

/-! ## Lemma 1: det formula for the F4′ target -/

/-- `4 · det(T)² = 3 · ν⁴ · a² · b² · (a+b)² · (a+2b)²` for an F4PrimeData triangle. -/
theorem target_F4prime_four_det_sq {α a b c ν : ℝ} (T : Tri) (h : T.F4PrimeData α a b c ν)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    4 * Erdos634.AreaDet.detTri T ^ 2 =
      3 * ν ^ 4 * a ^ 2 * b ^ 2 * (a + b) ^ 2 * (a + 2 * b) ^ 2 := by
  obtain ⟨-, hgrid⟩ := h
  obtain ⟨σ, -, o0, -, o1, -, o2⟩ := hgrid
  have hM := T.four_detTri_sq_sym
  rw [T.sum_perm 2 σ, T.sum_perm 4 σ, o0, o1, o2] at hM
  linear_combination hM -
    ν ^ 4 * a ^ 2 * (a + 2 * b) ^ 2 * (c ^ 2 - a ^ 2 - 3 * a * b - 3 * b ^ 2) * hc2

/-! ## Lemma 2: area formula N = ν² · (a+b) · (a+2b) -/

/-- For a `CongruentDissection` with a 2π/3 model and an F4PrimeData target,
    `(N : ℝ) = ν² · (a+b) · (a+2b)`. -/
theorem F4prime_area_formula {N : ℕ} (D : CongruentDissection N) {α a b c ν : ℝ}
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : D.target.F4PrimeData α a b c ν)
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν) :
    (N : ℝ) = ν ^ 2 * (a + b) * (a + 2 * b) := by
  have hc2 := twoPiThree_c_sq D.model hm
  have hdet := D.abs_detTri_target
  have hdet_sq : Erdos634.AreaDet.detTri D.target ^ 2 =
      (N : ℝ) ^ 2 * Erdos634.AreaDet.detTri D.model ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hdet
    simp only [mul_pow, sq_abs] at h
    exact h
  have hmod_det := Erdos634.Draft.ThmIso.model_four_det_sq D.model hm
  have htgt_det := target_F4prime_four_det_sq D.target ht hc2
  have key : 3 * ν ^ 4 * a ^ 2 * b ^ 2 * (a + b) ^ 2 * (a + 2 * b) ^ 2 =
      3 * (N : ℝ) ^ 2 * a ^ 2 * b ^ 2 := by
    linear_combination -htgt_det + (N : ℝ) ^ 2 * hmod_det + 4 * hdet_sq
  have hν4_eq : ν ^ 4 * (a + b) ^ 2 * (a + 2 * b) ^ 2 = (N : ℝ) ^ 2 :=
    mul_left_cancel₀ (by positivity : (3 : ℝ) * a ^ 2 * b ^ 2 ≠ 0) (by linear_combination key)
  have h_sq_eq : (ν ^ 2 * (a + b) * (a + 2 * b)) ^ 2 = (N : ℝ) ^ 2 := by
    have : (ν ^ 2 * (a + b) * (a + 2 * b)) ^ 2 = ν ^ 4 * (a + b) ^ 2 * (a + 2 * b) ^ 2 := by ring
    rw [this, hν4_eq]
  have hLpos : (0 : ℝ) ≤ ν ^ 2 * (a + b) * (a + 2 * b) := by positivity
  have hRpos : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  exact ((pow_left_inj₀ hLpos hRpos two_ne_zero).mp h_sq_eq).symm

#check @F4prime_area_formula
#print axioms F4prime_area_formula

end Erdos634.Draft.R8F4PrimeAreaFormula
