-- Draft/F1AreaIdentity.lean — Area identity for the F1 target shape.
-- Proves `N · b = μ² · (a + b)` for a CongruentDissection whose model is a 2π/3 tile
-- and whose target is an F1Data shape (angles α, π/3, π/3+β; opposite sides μa, μc, μ(a+b)).
--
-- This is the F1-analogue of `base_alpha_area_identity` in Draft/ThmIso.lean.
-- Proof: two det-sq formulas + abs_detTri_target → square-root argument.
-- ZERO sorry. Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04) (formalization debt).
--
-- Contribution: unlocks the algebraic chain for `F1FreeStatement` (prop:F1free, C8).

import Erdos634.Draft.FluxCRow2
import Erdos634.Draft.FluxCRow5
import Erdos634.Draft.FluxE2Pi3Row7
import Erdos634.Draft.ThmIso

open scoped Classical

namespace Erdos634.Draft.F1AreaIdentity

open Erdos634.Geometry Erdos634.AreaDet

/-! ## Auxiliary: c² = a²+ab+b² for TwoPiThreeData -/

private lemma twoPiThree_c_sq {α a b c : ℝ} (T : Tri) (h : T.TwoPiThreeData α a b c) :
    c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
  obtain ⟨σ, -, ha, -, hb, hγ, hc⟩ := h
  have hlc := T.lawCos_perm σ
  rw [ha, hb, hc, hγ,
      show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three] at hlc
  linarith

/-! ## Lemma 1: det formula for the F1 target -/

/-- `4 · det(T)² = 3 · μ⁴ · a² · (a+b)²` for an F1Data triangle. -/
theorem target_F1_four_det_sq {α a b c μ : ℝ} (T : Tri) (h : T.F1Data α a b c μ)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    4 * Erdos634.AreaDet.detTri T ^ 2 = 3 * μ ^ 4 * a ^ 2 * (a + b) ^ 2 := by
  obtain ⟨-, hgrid⟩ := h
  obtain ⟨σ, -, o0, -, o1, -, o2⟩ := hgrid
  have hM := T.four_detTri_sq_sym
  rw [T.sum_perm 2 σ, T.sum_perm 4 σ, o0, o1, o2] at hM
  linear_combination hM - μ ^ 4 * (c ^ 2 - (3 * a ^ 2 + 3 * a * b + b ^ 2)) * hc2

/-! ## Lemma 2: area identity N · b = μ² · (a + b) -/

/-- For a `CongruentDissection` with a 2π/3 model and an F1Data target,
`N · b = μ² · (a + b)`. -/
theorem F1_area_identity {N : ℕ} (D : CongruentDissection N) {α a b c μ : ℝ}
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : D.target.F1Data α a b c μ)
    (ha : 0 < a) (hb : 0 < b) (hμ : 0 < μ) :
    (N : ℝ) * b = μ ^ 2 * (a + b) := by
  have hc2 := twoPiThree_c_sq D.model hm
  have hdet := D.abs_detTri_target
  have hdet_sq : Erdos634.AreaDet.detTri D.target ^ 2
      = (N : ℝ) ^ 2 * Erdos634.AreaDet.detTri D.model ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hdet
    simp only [mul_pow, sq_abs] at h
    exact h
  have hmod_det := Erdos634.Draft.ThmIso.model_four_det_sq D.model hm
  have htgt_det := target_F1_four_det_sq D.target ht hc2
  have key : 3 * μ ^ 4 * a ^ 2 * (a + b) ^ 2 = 3 * (N : ℝ) ^ 2 * a ^ 2 * b ^ 2 := by
    linear_combination -htgt_det + (N : ℝ) ^ 2 * hmod_det + 4 * hdet_sq
  have hμ4_eq : μ ^ 4 * (a + b) ^ 2 = (N : ℝ) ^ 2 * b ^ 2 :=
    mul_left_cancel₀ (by positivity : (3 : ℝ) * a ^ 2 ≠ 0) (by linear_combination key)
  have h_sq_eq : (μ ^ 2 * (a + b)) ^ 2 = ((N : ℝ) * b) ^ 2 := by
    have : (μ ^ 2 * (a + b)) ^ 2 = μ ^ 4 * (a + b) ^ 2 := by ring
    rw [this, hμ4_eq]; ring
  have hLpos : (0 : ℝ) ≤ μ ^ 2 * (a + b) := by positivity
  have hRpos : (0 : ℝ) ≤ (N : ℝ) * b := mul_nonneg (Nat.cast_nonneg N) hb.le
  exact ((pow_left_inj₀ hLpos hRpos two_ne_zero).mp h_sq_eq).symm

#check @F1_area_identity
#print axioms F1_area_identity

end Erdos634.Draft.F1AreaIdentity
