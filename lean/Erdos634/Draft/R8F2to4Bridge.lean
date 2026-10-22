-- Draft/R8F2to4Bridge.lean — bridges from TgtAngles to FXData for the five F2–F4′ shapes.
--
-- Each theorem maps:
--   TgtAngles D (shape angles) → ∃ ν > 0, D.target.FXData α a b c ν
--
-- Method: law of sines (D.target) + model side ratios + trig identities.
-- All five bridges (F2/F3/F3′/F4/F4′) are ZERO sorry.
--
-- These assemble into R8ReductionStatement (with the five FX contradictions).

import Erdos634.Draft.ThmIsoShBridge
import Erdos634.Draft.FluxE2Pi3Row8F2
import Erdos634.Draft.FluxE2Pi3Row8F3
import Erdos634.Draft.FluxE2Pi3Row8F4
import Erdos634.Draft.FluxE2Pi3Row8Mirrors
import Erdos634.Draft.R8F2Contradiction
import Erdos634.Draft.R8F3Contradiction
import Erdos634.Draft.R8F3PrimeContradiction
import Erdos634.Draft.R8F4Contradiction
import Erdos634.Draft.R8F4PrimeContradiction
import Erdos634.Draft.TheoremPConditional

open scoped Classical

namespace Erdos634.Draft.R8F2to4Bridge

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional
open A1Field (sin_angle_pos)

/-! ## Private trig lemmas -/

private lemma key_sin_F2 (α : ℝ) :
    Real.sin α + 2 * Real.sin (Real.pi / 3 - α) =
    2 * Real.sin (Real.pi / 3) * Real.cos α := by
  rw [Real.sin_sub (Real.pi / 3) α, Real.cos_pi_div_three]; ring

private lemma key_sin_F2b (α : ℝ) :
    Real.sin (Real.pi / 3 - α) + 2 * Real.sin α =
    2 * Real.sin (Real.pi / 3) * Real.cos (Real.pi / 3 - α) := by
  rw [Real.sin_sub (Real.pi / 3) α, Real.cos_sub (Real.pi / 3) α, Real.cos_pi_div_three]
  have h_s3_sq : Real.sin (Real.pi / 3) ^ 2 = 3 / 4 := by
    rw [Real.sin_pi_div_three, div_pow, Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)]; norm_num
  linear_combination -2 * Real.sin α * h_s3_sq

private lemma sin_two_pi3_eq (α : ℝ) :
    Real.sin (2 * Real.pi / 3) = Real.sin (Real.pi / 3) := by
  rw [show (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub]

/-! ## F2 bridge: (2α, 2β, π/3) → F2Data -/

/-- From `TgtAngles D (2α) (2β) (π/3)` (F₂ shape) and model `TwoPiThreeData α a b c`,
    construct `F2Data α a b c ν` with explicit `ν > 0`. -/
theorem f2_data_of_shape {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : TgtAngles D (2 * α) (2 * (Real.pi / 3 - α)) (α + (Real.pi / 3 - α))) :
    ∃ ν > 0, D.target.F2Data α a b c ν := by
  -- Normalise angle expression
  have htN : TgtAngles D (2 * α) (2 * (Real.pi / 3 - α)) (Real.pi / 3) := by
    obtain ⟨σt, h0, h1, h2⟩ := ht; exact ⟨σt, h0, h1, by linarith⟩
  -- Extract model data
  obtain ⟨_, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  obtain ⟨σm, hα0m, ham, hβ1m, hbm, hγ2m, hcm⟩ := hm
  obtain ⟨σ, ht0, ht1, ht2⟩ := htN
  -- Model law of sines: sin(α)·c = sin(π/3)·a
  have hm02 := D.model.lawSin (σm 0) (σm 2)
  rw [hα0m, hγ2m, ham, hcm] at hm02
  have hm02' : Real.sin α * c = Real.sin (Real.pi / 3) * a := by
    linarith [sin_two_pi3_eq α ▸ hm02]
  -- Model law of sines: sin(π/3−α)·c = sin(π/3)·b
  have hm12 := D.model.lawSin (σm 1) (σm 2)
  rw [hβ1m, hγ2m, hbm, hcm] at hm12
  have hm12' : Real.sin (Real.pi / 3 - α) * c = Real.sin (Real.pi / 3) * b := by
    linarith [sin_two_pi3_eq α ▸ hm12]
  -- Positivity
  have hsin_π3 : 0 < Real.sin (Real.pi / 3) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  -- Scale ν = oppLen(σ2) / c²  (the π/3-angle vertex)
  have hoppL2_pos : 0 < D.target.oppLen (σ 2) := D.target.oppLen_pos (σ 2)
  refine ⟨D.target.oppLen (σ 2) / c ^ 2, by positivity, by positivity, ?_⟩
  -- Key auxiliary squares
  have ha_sq : Real.sin α ^ 2 * c ^ 2 = Real.sin (Real.pi / 3) ^ 2 * a ^ 2 := by
    linear_combination (Real.sin α * c + Real.sin (Real.pi / 3) * a) * hm02'
  have hab : Real.sin α * Real.sin (Real.pi / 3 - α) * c ^ 2 =
      Real.sin (Real.pi / 3) ^ 2 * (a * b) := by
    linear_combination Real.sin (Real.pi / 3 - α) * c * hm02' +
      Real.sin (Real.pi / 3) * a * hm12'
  have hb_sq : Real.sin (Real.pi / 3 - α) ^ 2 * c ^ 2 =
      Real.sin (Real.pi / 3) ^ 2 * b ^ 2 := by
    linear_combination (Real.sin (Real.pi / 3 - α) * c + Real.sin (Real.pi / 3) * b) * hm12'
  -- Main identity for side 0: sin(π/3)·a(a+2b) = 2·sin(α)·cos(α)·c²
  have hmul : 2 * Real.sin (Real.pi / 3) * Real.sin α * Real.cos α * c ^ 2 =
      Real.sin (Real.pi / 3) ^ 2 * (a * (a + 2 * b)) := by
    linear_combination (-c ^ 2 * Real.sin α) * key_sin_F2 α + ha_sq + 2 * hab
  have hmain0 : Real.sin (Real.pi / 3) * (a * (a + 2 * b)) =
      2 * Real.sin α * Real.cos α * c ^ 2 :=
    mul_left_cancel₀ hsin_π3.ne'
      (show Real.sin (Real.pi / 3) * (Real.sin (Real.pi / 3) * (a * (a + 2 * b))) =
          Real.sin (Real.pi / 3) * (2 * Real.sin α * Real.cos α * c ^ 2) by
        linear_combination -hmul)
  -- Main identity for side 1: sin(π/3)·b(2a+b) = 2·sin(β)·cos(β)·c²
  have hmul_b : 2 * Real.sin (Real.pi / 3) * Real.sin (Real.pi / 3 - α) *
      Real.cos (Real.pi / 3 - α) * c ^ 2 =
      Real.sin (Real.pi / 3) ^ 2 * (b * (2 * a + b)) := by
    linear_combination (-c ^ 2 * Real.sin (Real.pi / 3 - α)) * key_sin_F2b α + hb_sq + 2 * hab
  have hmain1 : Real.sin (Real.pi / 3) * (b * (2 * a + b)) =
      2 * Real.sin (Real.pi / 3 - α) * Real.cos (Real.pi / 3 - α) * c ^ 2 :=
    mul_left_cancel₀ hsin_π3.ne'
      (show Real.sin (Real.pi / 3) * (Real.sin (Real.pi / 3) * (b * (2 * a + b))) =
          Real.sin (Real.pi / 3) * (2 * Real.sin (Real.pi / 3 - α) *
            Real.cos (Real.pi / 3 - α) * c ^ 2) by
        linear_combination -hmul_b)
  -- Target law of sines
  have ht02 := D.target.lawSin (σ 0) (σ 2)
  rw [ht0, ht2] at ht02
  have ht02' : 2 * Real.sin α * Real.cos α * D.target.oppLen (σ 2) =
      Real.sin (Real.pi / 3) * D.target.oppLen (σ 0) := by
    rwa [Real.sin_two_mul] at ht02
  have ht12 := D.target.lawSin (σ 1) (σ 2)
  rw [ht1, ht2] at ht12
  have ht12' : 2 * Real.sin (Real.pi / 3 - α) * Real.cos (Real.pi / 3 - α) *
      D.target.oppLen (σ 2) = Real.sin (Real.pi / 3) * D.target.oppLen (σ 1) := by
    rwa [Real.sin_two_mul] at ht12
  -- Side equality for oppLen(σ0): oppLen(σ0)·c² = oppLen(σ2)·a(a+2b)
  have hkey0 : D.target.oppLen (σ 0) * c ^ 2 =
      D.target.oppLen (σ 2) * (a * (a + 2 * b)) :=
    mul_left_cancel₀ hsin_π3.ne' (by
      have h1 : Real.sin (Real.pi / 3) * (D.target.oppLen (σ 0) * c ^ 2) =
          2 * Real.sin α * Real.cos α * c ^ 2 * D.target.oppLen (σ 2) := by
        linear_combination -c ^ 2 * ht02'
      have h2 : Real.sin (Real.pi / 3) * (D.target.oppLen (σ 2) * (a * (a + 2 * b))) =
          2 * Real.sin α * Real.cos α * c ^ 2 * D.target.oppLen (σ 2) := by
        linear_combination D.target.oppLen (σ 2) * hmain0
      linarith)
  have hside0 : D.target.oppLen (σ 0) = D.target.oppLen (σ 2) / c ^ 2 * (a * (a + 2 * b)) := by
    field_simp [show c ^ 2 ≠ 0 from by positivity]; linarith [hkey0]
  -- Side equality for oppLen(σ1): oppLen(σ1)·c² = oppLen(σ2)·b(2a+b)
  have hkey1 : D.target.oppLen (σ 1) * c ^ 2 =
      D.target.oppLen (σ 2) * (b * (2 * a + b)) :=
    mul_left_cancel₀ hsin_π3.ne' (by
      have h1 : Real.sin (Real.pi / 3) * (D.target.oppLen (σ 1) * c ^ 2) =
          2 * Real.sin (Real.pi / 3 - α) * Real.cos (Real.pi / 3 - α) * c ^ 2 *
            D.target.oppLen (σ 2) := by
        linear_combination -c ^ 2 * ht12'
      have h2 : Real.sin (Real.pi / 3) * (D.target.oppLen (σ 2) * (b * (2 * a + b))) =
          2 * Real.sin (Real.pi / 3 - α) * Real.cos (Real.pi / 3 - α) * c ^ 2 *
            D.target.oppLen (σ 2) := by
        linear_combination D.target.oppLen (σ 2) * hmain1
      linarith)
  have hside1 : D.target.oppLen (σ 1) = D.target.oppLen (σ 2) / c ^ 2 * (b * (2 * a + b)) := by
    field_simp [show c ^ 2 ≠ 0 from by positivity]; linarith [hkey1]
  -- Side 2 is trivial
  have hside2 : D.target.oppLen (σ 2) = D.target.oppLen (σ 2) / c ^ 2 * c ^ 2 :=
    (div_mul_cancel₀ _ (show c ^ 2 ≠ 0 from by positivity)).symm
  -- Assemble GridTriData
  exact ⟨σ,
    by rw [ht0]; push_cast; ring,
    hside0,
    by rw [ht1]; push_cast; ring,
    hside1,
    by rw [ht2]; push_cast; ring,
    hside2⟩

/-! ## F3 bridge: (α, 2α, 3β) → F3Data -/

/-- Key trig identity for F3: sin(3*(π/3−α))·c² = 3·sin(α)·b·(a+b). -/
private lemma key_sin_F3 (α a b c : ℝ)
    (ha_sq : Real.sin α ^ 2 * c ^ 2 = Real.sin (Real.pi / 3) ^ 2 * a ^ 2)
    (h_s3_sq : Real.sin (Real.pi / 3) ^ 2 = 3 / 4)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    Real.sin (3 * (Real.pi / 3 - α)) * c ^ 2 = 3 * Real.sin α * b * (a + b) := by
  have hstep : Real.sin (3 * (Real.pi / 3 - α)) = 3 * Real.sin α - 4 * Real.sin α ^ 3 := by
    rw [show 3 * (Real.pi / 3 - α) = Real.pi - 3 * α by ring, Real.sin_pi_sub, Real.sin_three_mul]
  rw [hstep]
  linear_combination 3 * Real.sin α * hc2 + (-4 * Real.sin α) * ha_sq +
    (-4 * Real.sin α * a ^ 2) * h_s3_sq

theorem f3_data_of_shape {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : TgtAngles D α (2 * α) (3 * (Real.pi / 3 - α))) :
    ∃ ν > 0, D.target.F3Data α a b c ν := by
  obtain ⟨hcos, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  obtain ⟨σm, hα0m, ham, hβ1m, hbm, hγ2m, hcm⟩ := hm
  obtain ⟨σ, ht0, ht1, ht2⟩ := ht
  have hm02 := D.model.lawSin (σm 0) (σm 2)
  rw [hα0m, hγ2m, ham, hcm] at hm02
  have hm02' : Real.sin α * c = Real.sin (Real.pi / 3) * a := by
    linarith [sin_two_pi3_eq α ▸ hm02]
  have hsin_π3 : 0 < Real.sin (Real.pi / 3) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have hsin_α : 0 < Real.sin α := by nlinarith [hsin_π3, hc0, ha0, hm02']
  have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
    have hlc := D.model.lawCos_perm σm
    rw [ham, hbm, hcm, hγ2m,
        show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
        Real.cos_pi_sub, Real.cos_pi_div_three] at hlc
    linarith
  have ha_sq : Real.sin α ^ 2 * c ^ 2 = Real.sin (Real.pi / 3) ^ 2 * a ^ 2 := by
    linear_combination (Real.sin α * c + Real.sin (Real.pi / 3) * a) * hm02'
  have h_s3_sq : Real.sin (Real.pi / 3) ^ 2 = 3 / 4 := by
    rw [Real.sin_pi_div_three, div_pow, Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)]; norm_num
  have hcos' : 2 * Real.cos α * c = a + 2 * b := by
    have hcos2 := hcos
    field_simp [show (2 : ℝ) * c ≠ 0 from by positivity] at hcos2; linarith
  have hoppL0_pos : 0 < D.target.oppLen (σ 0) := D.target.oppLen_pos (σ 0)
  refine ⟨D.target.oppLen (σ 0) / c ^ 2, by positivity, by positivity, ?_⟩
  have hside0 : D.target.oppLen (σ 0) = D.target.oppLen (σ 0) / c ^ 2 * c ^ 2 :=
    (div_mul_cancel₀ _ (show c ^ 2 ≠ 0 from by positivity)).symm
  -- Side 1: sin(α)*opp1 = sin(2α)*opp0 → opp1*c = opp0*(a+2b)
  have ht01 := D.target.lawSin (σ 0) (σ 1)
  rw [ht0, ht1, Real.sin_two_mul] at ht01
  have hkey1 : D.target.oppLen (σ 1) * c = D.target.oppLen (σ 0) * (a + 2 * b) :=
    mul_left_cancel₀ hsin_α.ne' (by
      linear_combination c * ht01 + Real.sin α * D.target.oppLen (σ 0) * hcos')
  have hside1 : D.target.oppLen (σ 1) = D.target.oppLen (σ 0) / c ^ 2 * (c * (a + 2 * b)) := by
    have h : D.target.oppLen (σ 1) * c ^ 2 = D.target.oppLen (σ 0) * (c * (a + 2 * b)) := by
      linear_combination c * hkey1
    field_simp [show c ^ 2 ≠ 0 from by positivity]; linarith [h]
  -- Side 2: sin(α)*opp2 = sin(3*(π/3-α))*opp0 → opp2*c² = 3*b*(a+b)*opp0
  have ht02 := D.target.lawSin (σ 0) (σ 2)
  rw [ht0, ht2] at ht02
  have hkeysin := key_sin_F3 α a b c ha_sq h_s3_sq hc2
  have hkey2 : D.target.oppLen (σ 2) * c ^ 2 =
      D.target.oppLen (σ 0) * (3 * b * (a + b)) :=
    mul_left_cancel₀ hsin_α.ne' (by
      have h1 : Real.sin α * (D.target.oppLen (σ 2) * c ^ 2) =
          Real.sin (3 * (Real.pi / 3 - α)) * D.target.oppLen (σ 0) * c ^ 2 := by
        linear_combination c ^ 2 * ht02
      have h2 : Real.sin (3 * (Real.pi / 3 - α)) * D.target.oppLen (σ 0) * c ^ 2 =
          Real.sin α * (D.target.oppLen (σ 0) * (3 * b * (a + b))) := by
        linear_combination D.target.oppLen (σ 0) * hkeysin
      linarith)
  have hside2 : D.target.oppLen (σ 2) = D.target.oppLen (σ 0) / c ^ 2 * (3 * b * (a + b)) := by
    field_simp [show c ^ 2 ≠ 0 from by positivity]; linarith [hkey2]
  exact ⟨σ,
    by rw [ht0]; push_cast; ring,
    hside0,
    by rw [ht1]; push_cast; ring,
    hside1,
    by rw [ht2]; push_cast; ring,
    by linarith [hside2]⟩


/-! ## F3′ bridge: (β, 2β, 3α) → F3PrimeData -/

theorem f3prime_data_of_shape {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : TgtAngles D (Real.pi / 3 - α) (2 * (Real.pi / 3 - α)) (3 * α)) :
    ∃ ν > 0, D.target.F3PrimeData α a b c ν := by
  obtain ⟨hcos, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  obtain ⟨σm, hα0m, ham, hβ1m, hbm, hγ2m, hcm⟩ := hm
  obtain ⟨σ, ht0, ht1, ht2⟩ := ht
  -- Law of sines on model: sin(β)*c = sin(π/3)*b
  have hm12 := D.model.lawSin (σm 1) (σm 2)
  rw [hβ1m, hγ2m, hbm, hcm] at hm12
  have hm12' : Real.sin (Real.pi / 3 - α) * c = Real.sin (Real.pi / 3) * b := by
    linarith [sin_two_pi3_eq (Real.pi / 3 - α) ▸ hm12]
  -- Law of sines on model: sin(α)*c = sin(π/3)*a
  have hm02 := D.model.lawSin (σm 0) (σm 2)
  rw [hα0m, hγ2m, ham, hcm] at hm02
  have hm02' : Real.sin α * c = Real.sin (Real.pi / 3) * a := by
    linarith [sin_two_pi3_eq α ▸ hm02]
  have hsin_π3 : 0 < Real.sin (Real.pi / 3) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have hsin_β : 0 < Real.sin (Real.pi / 3 - α) := by nlinarith [hsin_π3, hc0, hb0, hm12']
  have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
    have hlc := D.model.lawCos_perm σm
    rw [ham, hbm, hcm, hγ2m,
        show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
        Real.cos_pi_sub, Real.cos_pi_div_three] at hlc
    linarith
  have hb_sq : Real.sin (Real.pi / 3 - α) ^ 2 * c ^ 2 = Real.sin (Real.pi / 3) ^ 2 * b ^ 2 := by
    linear_combination (Real.sin (Real.pi / 3 - α) * c + Real.sin (Real.pi / 3) * b) * hm12'
  have h_s3_sq : Real.sin (Real.pi / 3) ^ 2 = 3 / 4 := by
    rw [Real.sin_pi_div_three, div_pow, Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)]; norm_num
  -- cos(β)*c = (2a+b)/2
  have hcos_β : 2 * Real.cos (Real.pi / 3 - α) * c = 2 * a + b := by
    rw [Real.cos_sub (Real.pi / 3) α, Real.cos_pi_div_three]
    have hcos' : 2 * Real.cos α * c = a + 2 * b := by
      field_simp [show (2 : ℝ) * c ≠ 0 from by positivity] at hcos; linarith
    linear_combination (1 / 2 : ℝ) * hcos' + 2 * Real.sin (Real.pi / 3) * hm02' + 2 * a * h_s3_sq
  have hoppL0_pos : 0 < D.target.oppLen (σ 0) := D.target.oppLen_pos (σ 0)
  refine ⟨D.target.oppLen (σ 0) / c ^ 2, by positivity, by positivity, ?_⟩
  have hside0 : D.target.oppLen (σ 0) = D.target.oppLen (σ 0) / c ^ 2 * c ^ 2 :=
    (div_mul_cancel₀ _ (show c ^ 2 ≠ 0 from by positivity)).symm
  -- Side 1: sin(β)*opp1 = sin(2β)*opp0 → opp1*c = opp0*(2a+b)
  have ht01 := D.target.lawSin (σ 0) (σ 1)
  rw [ht0, ht1, Real.sin_two_mul] at ht01
  have hkey1 : D.target.oppLen (σ 1) * c = D.target.oppLen (σ 0) * (2 * a + b) :=
    mul_left_cancel₀ hsin_β.ne' (by
      linear_combination c * ht01 + Real.sin (Real.pi / 3 - α) * D.target.oppLen (σ 0) * hcos_β)
  have hside1 : D.target.oppLen (σ 1) = D.target.oppLen (σ 0) / c ^ 2 * (c * (2 * a + b)) := by
    have h : D.target.oppLen (σ 1) * c ^ 2 = D.target.oppLen (σ 0) * (c * (2 * a + b)) := by
      linear_combination c * hkey1
    field_simp [show c ^ 2 ≠ 0 from by positivity]; linarith [h]
  -- Side 2: sin(β)*opp2 = sin(3α)*opp0 → opp2*c² = 3*a*(a+b)*opp0
  have ht02 := D.target.lawSin (σ 0) (σ 2)
  rw [ht0, ht2] at ht02
  have hkeysin := key_sin_F3 (Real.pi / 3 - α) b a c hb_sq h_s3_sq (by linarith [hc2])
  -- hkeysin: sin(3*(π/3-(π/3-α)))*c² = 3*sin(β)*a*(b+a)
  have hkeysin' : Real.sin (3 * α) * c ^ 2 = 3 * Real.sin (Real.pi / 3 - α) * a * (a + b) := by
    have := hkeysin; rw [show 3 * (Real.pi / 3 - (Real.pi / 3 - α)) = 3 * α by ring] at this; linarith
  have hkey2 : D.target.oppLen (σ 2) * c ^ 2 =
      D.target.oppLen (σ 0) * (3 * a * (a + b)) :=
    mul_left_cancel₀ hsin_β.ne' (by
      have h1 : Real.sin (Real.pi / 3 - α) * (D.target.oppLen (σ 2) * c ^ 2) =
          Real.sin (3 * α) * D.target.oppLen (σ 0) * c ^ 2 := by
        linear_combination c ^ 2 * ht02
      have h2 : Real.sin (3 * α) * D.target.oppLen (σ 0) * c ^ 2 =
          Real.sin (Real.pi / 3 - α) * (D.target.oppLen (σ 0) * (3 * a * (a + b))) := by
        linear_combination D.target.oppLen (σ 0) * hkeysin'
      linarith)
  have hside2 : D.target.oppLen (σ 2) = D.target.oppLen (σ 0) / c ^ 2 * (3 * a * (a + b)) := by
    field_simp [show c ^ 2 ≠ 0 from by positivity]; linarith [hkey2]
  exact ⟨σ,
    by rw [ht0]; push_cast; ring,
    hside0,
    by rw [ht1]; push_cast; ring,
    hside1,
    by rw [ht2]; push_cast; ring,
    by linarith [hside2]⟩

/-! ## F4 bridge: (α, 2β, 2α+β=α+π/3) → F4Data -/

theorem f4_data_of_shape {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : TgtAngles D α (2 * (Real.pi / 3 - α)) (2 * α + (Real.pi / 3 - α))) :
    ∃ ν > 0, D.target.F4Data α a b c ν := by
  obtain ⟨hcos, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  obtain ⟨σm, hα0m, ham, hβ1m, hbm, hγ2m, hcm⟩ := hm
  obtain ⟨σ, ht0, ht1, ht2⟩ := ht
  have hm02 := D.model.lawSin (σm 0) (σm 2)
  rw [hα0m, hγ2m, ham, hcm] at hm02
  have hm02' : Real.sin α * c = Real.sin (Real.pi / 3) * a := by
    linarith [sin_two_pi3_eq α ▸ hm02]
  have hm12 := D.model.lawSin (σm 1) (σm 2)
  rw [hβ1m, hγ2m, hbm, hcm] at hm12
  have hm12' : Real.sin (Real.pi / 3 - α) * c = Real.sin (Real.pi / 3) * b := by
    linarith [sin_two_pi3_eq (Real.pi / 3 - α) ▸ hm12]
  have hsin_π3 : 0 < Real.sin (Real.pi / 3) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have hsin_α : 0 < Real.sin α := by nlinarith [hsin_π3, hc0, ha0, hm02']
  have hcos' : 2 * Real.cos α * c = a + 2 * b := by
    field_simp [show (2 : ℝ) * c ≠ 0 from by positivity] at hcos; linarith
  have hcos_β : 2 * Real.cos (Real.pi / 3 - α) * c = 2 * a + b := by
    have h_s3_sq : Real.sin (Real.pi / 3) ^ 2 = 3 / 4 := by
      rw [Real.sin_pi_div_three, div_pow, Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)]; norm_num
    rw [Real.cos_sub (Real.pi / 3) α, Real.cos_pi_div_three]
    linear_combination (1 / 2 : ℝ) * hcos' + 2 * Real.sin (Real.pi / 3) * hm02' + 2 * a * h_s3_sq
  -- sin(α+π/3)*a = sin(α)*(a+b)
  have h_sin_sum : Real.sin (α + Real.pi / 3) * a = Real.sin α * (a + b) := by
    apply mul_left_cancel₀ hc0.ne'
    have key : c * (Real.sin (α + Real.pi / 3) * a) = c * (Real.sin α * (a + b)) := by
      rw [Real.sin_add, Real.cos_pi_div_three]
      linear_combination Real.sin (Real.pi / 3) * a / 2 * hcos' - (a + 2 * b) / 2 * hm02'
    linarith
  have hoppL0_pos : 0 < D.target.oppLen (σ 0) := D.target.oppLen_pos (σ 0)
  refine ⟨D.target.oppLen (σ 0) / (a * c), by positivity, by positivity, ?_⟩
  have hside0 : D.target.oppLen (σ 0) = D.target.oppLen (σ 0) / (a * c) * (a * c) :=
    (div_mul_cancel₀ _ (show a * c ≠ 0 from by positivity)).symm
  -- Side 1: sin(α)*opp1 = sin(2β)*opp0 → a*c*opp1 = b*(2a+b)*opp0
  have ht01 := D.target.lawSin (σ 0) (σ 1)
  rw [ht0, ht1, Real.sin_two_mul] at ht01
  have hkey1 : D.target.oppLen (σ 1) * (a * c) = D.target.oppLen (σ 0) * (b * (2 * a + b)) :=
    mul_left_cancel₀ hsin_π3.ne' (by
      linear_combination -c * D.target.oppLen (σ 1) * hm02' + c ^ 2 * ht01 +
        D.target.oppLen (σ 0) * Real.sin (Real.pi / 3 - α) * c * hcos_β +
        D.target.oppLen (σ 0) * (2 * a + b) * hm12')
  have hside1 : D.target.oppLen (σ 1) = D.target.oppLen (σ 0) / (a * c) * (b * (2 * a + b)) := by
    field_simp [show a ≠ 0 from ha0.ne', show c ≠ 0 from hc0.ne']; linarith [hkey1]
  -- Side 2: sin(α)*opp2 = sin(α+π/3)*opp0 → a*opp2 = (a+b)*opp0
  have ht02 := D.target.lawSin (σ 0) (σ 2)
  rw [ht0, ht2, show 2 * α + (Real.pi / 3 - α) = α + Real.pi / 3 by ring] at ht02
  have hkey2 : D.target.oppLen (σ 2) * a = D.target.oppLen (σ 0) * (a + b) :=
    mul_left_cancel₀ hsin_α.ne' (by
      linear_combination a * ht02 + D.target.oppLen (σ 0) * h_sin_sum)
  have hside2 : D.target.oppLen (σ 2) = D.target.oppLen (σ 0) / (a * c) * (c * (a + b)) := by
    field_simp [show a ≠ 0 from ha0.ne', show c ≠ 0 from hc0.ne']; linarith [hkey2]
  exact ⟨σ,
    by rw [ht0]; push_cast; ring,
    hside0,
    by rw [ht1]; push_cast; ring,
    hside1,
    by rw [ht2]; push_cast; ring,
    by linarith [hside2]⟩

/-! ## F4′ bridge: (β, 2α, 2π/3−α) → F4PrimeData -/

theorem f4prime_data_of_shape {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : TgtAngles D (Real.pi / 3 - α) (2 * α) (α + 2 * (Real.pi / 3 - α))) :
    ∃ ν > 0, D.target.F4PrimeData α a b c ν := by
  obtain ⟨hcos, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  obtain ⟨σm, hα0m, ham, hβ1m, hbm, hγ2m, hcm⟩ := hm
  obtain ⟨σ, ht0, ht1, ht2⟩ := ht
  have hm02 := D.model.lawSin (σm 0) (σm 2)
  rw [hα0m, hγ2m, ham, hcm] at hm02
  have hm02' : Real.sin α * c = Real.sin (Real.pi / 3) * a := by
    linarith [sin_two_pi3_eq α ▸ hm02]
  have hm12 := D.model.lawSin (σm 1) (σm 2)
  rw [hβ1m, hγ2m, hbm, hcm] at hm12
  have hm12' : Real.sin (Real.pi / 3 - α) * c = Real.sin (Real.pi / 3) * b := by
    linarith [sin_two_pi3_eq (Real.pi / 3 - α) ▸ hm12]
  have hsin_π3 : 0 < Real.sin (Real.pi / 3) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have hsin_β : 0 < Real.sin (Real.pi / 3 - α) := by nlinarith [hsin_π3, hc0, hb0, hm12']
  have hcos' : 2 * Real.cos α * c = a + 2 * b := by
    field_simp [show (2 : ℝ) * c ≠ 0 from by positivity] at hcos; linarith
  -- sin(π/3+α)*b = sin(β)*(a+b)
  have h_sin_sum' : Real.sin (Real.pi / 3 + α) * b = Real.sin (Real.pi / 3 - α) * (a + b) := by
    apply mul_left_cancel₀ hc0.ne'
    have key : c * (Real.sin (Real.pi / 3 + α) * b) = c * (Real.sin (Real.pi / 3 - α) * (a + b)) := by
      rw [Real.sin_add, Real.sin_sub, Real.cos_pi_div_three]
      linear_combination -(Real.sin (Real.pi / 3) * a / 2) * hcos' + (a + 2 * b) / 2 * hm02'
    linarith
  have hoppL0_pos : 0 < D.target.oppLen (σ 0) := D.target.oppLen_pos (σ 0)
  refine ⟨D.target.oppLen (σ 0) / (b * c), by positivity, by positivity, ?_⟩
  have hside0 : D.target.oppLen (σ 0) = D.target.oppLen (σ 0) / (b * c) * (b * c) :=
    (div_mul_cancel₀ _ (show b * c ≠ 0 from by positivity)).symm
  -- Side 1: sin(β)*opp1 = sin(2α)*opp0 → b*c*opp1 = a*(a+2b)*opp0
  have ht01 := D.target.lawSin (σ 0) (σ 1)
  rw [ht0, ht1, Real.sin_two_mul] at ht01
  have hkey1 : D.target.oppLen (σ 1) * (b * c) = D.target.oppLen (σ 0) * (a * (a + 2 * b)) :=
    mul_left_cancel₀ hsin_π3.ne' (by
      linear_combination -c * D.target.oppLen (σ 1) * hm12' + c ^ 2 * ht01 +
        D.target.oppLen (σ 0) * Real.sin α * c * hcos' +
        D.target.oppLen (σ 0) * (a + 2 * b) * hm02')
  have hside1 : D.target.oppLen (σ 1) = D.target.oppLen (σ 0) / (b * c) * (a * (a + 2 * b)) := by
    field_simp [show b ≠ 0 from hb0.ne', show c ≠ 0 from hc0.ne']; linarith [hkey1]
  -- Side 2: sin(β)*opp2 = sin(α+2β)*opp0 = sin(π/3+α)*opp0 → b*opp2 = (a+b)*opp0
  have ht02 := D.target.lawSin (σ 0) (σ 2)
  rw [ht0, ht2, show α + 2 * (Real.pi / 3 - α) = Real.pi - (Real.pi / 3 + α) by ring,
      Real.sin_pi_sub] at ht02
  have hkey2 : D.target.oppLen (σ 2) * b = D.target.oppLen (σ 0) * (a + b) :=
    mul_left_cancel₀ hsin_β.ne' (by
      linear_combination b * ht02 + D.target.oppLen (σ 0) * h_sin_sum')
  have hside2 : D.target.oppLen (σ 2) = D.target.oppLen (σ 0) / (b * c) * (c * (a + b)) := by
    field_simp [show b ≠ 0 from hb0.ne', show c ≠ 0 from hc0.ne']; linarith [hkey2]
  exact ⟨σ,
    by rw [ht0]; push_cast; ring,
    hside0,
    by rw [ht1]; push_cast; ring,
    hside1,
    by rw [ht2]; push_cast; ring,
    by linarith [hside2]⟩

/-! ## Assembly: R8ReductionStatement -/

/-- C9: No prime N tiles an F₂–F₄′ target by a 2π/3 tile. All five bridges are sorry-free. -/
theorem r8_reduction_statement : R8ReductionStatement := by
  intro N D hprime _hmod4 hN3 α a b c hirr hm hshape
  obtain ⟨_, _, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  rcases hshape with hF2 | hF3 | hF3' | hF4 | hF4'
  · obtain ⟨ν, hνpos, hF2data⟩ := f2_data_of_shape D hm hF2
    exact R8F2Contradiction.f2_prime_contradiction D hirr hm hF2data ha0 hb0 hνpos hprime hN3
  · obtain ⟨ν, hνpos, hF3data⟩ := f3_data_of_shape D hm hF3
    exact R8F3Contradiction.f3_prime_contradiction D hirr hm hF3data ha0 hb0 hνpos hprime hN3
  · obtain ⟨ν, hνpos, hF3pdata⟩ := f3prime_data_of_shape D hm hF3'
    exact R8F3PrimeContradiction.f3prime_contradiction D hirr hm hF3pdata ha0 hb0 hνpos hprime hN3
  · obtain ⟨ν, hνpos, hF4data⟩ := f4_data_of_shape D hm hF4
    exact R8F4Contradiction.f4_prime_contradiction D hirr hm hF4data ha0 hb0 hνpos hprime (by linarith)
  · obtain ⟨ν, hνpos, hF4pdata⟩ := f4prime_data_of_shape D hm hF4'
    exact R8F4PrimeContradiction.f4prime_prime_contradiction D hirr hm hF4pdata ha0 hb0 hνpos hprime (by linarith)

#check @f2_data_of_shape
#check @r8_reduction_statement

end Erdos634.Draft.R8F2to4Bridge
