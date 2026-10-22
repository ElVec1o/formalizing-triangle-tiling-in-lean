-- Draft/R8F2Contradiction.lean — No prime N > 3 admits a CongruentDissection with 2π/3 model
-- and F2Data target.  ZERO sorry.

import Erdos634.Draft.FluxPaper
import Erdos634.Draft.FluxE2Pi3Row8F2
import Erdos634.Draft.FluxE2Pi3Row8Arith
import Erdos634.Draft.R8F2AreaFormula
import Erdos634.Draft.R8CompositeArg
import Erdos634.Draft.R8N15Arith
import Erdos634.Draft.ThmIsoShBridge
import Erdos634.Draft.FluxDSideWord

open scoped Classical

namespace Erdos634.Draft.R8N15F2

open Erdos634.Geometry
open Erdos634.Row8Arith
open Erdos634.Draft.R8F2AreaFormula (F2_area_formula)
open Erdos634.Draft.R8CompositeArg (no_prime_F4_form)

private lemma c_sq (T : Tri) {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
  obtain ⟨σ, -, ha, -, hb, hγ, hc⟩ := h
  have hl := T.lawCos_perm σ
  rw [ha, hb, hc, hγ, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three] at hl
  linarith

-- Factor identities
private lemma F2_factor_alpha {ν a b c : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ν * (a - b - c) * (c + a - b) = -(3 * ν * a * b) := by linear_combination -ν * hc2

private lemma F2_factor_beta {ν a b c : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    -(ν * (a - b + c)) * (c + b - a) = -(3 * ν * a * b) := by linear_combination -ν * hc2

-- Flux value rewritten as -(3νab) — pure arithmetic
private lemma flux_eq_neg3ab {ν a b c : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ν * (c ^ 2 - a * (a + 2 * b) - b * (2 * a + b)) = -(3 * ν * a * b) := by
  linear_combination ν * hc2

/-! ## N = 3z² − δ² -/

private lemma f2_N_eq {N : ℕ} {a b c ν : ℝ} {δ z : ℤ}
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hNreal : (N : ℝ) = ν ^ 2 * (a + 2 * b) * (2 * a + b))
    (hδ : (δ : ℝ) = ν * (a - b)) (hz : (z : ℝ) = ν * c) :
    (N : ℤ) = 3 * z ^ 2 - δ ^ 2 := by
  have hR : (N : ℝ) = 3 * (z : ℝ) ^ 2 - (δ : ℝ) ^ 2 := by
    rw [hδ, hz, hNreal]; nlinarith [hc2]
  exact_mod_cast hR

/-! ## δ = 0 case -/

private lemma f2_delta_zero_False {N : ℕ} (hN15 : N = 15)
    {z : ℤ} (hNeq : (N : ℤ) = 3 * z ^ 2) : False := by
  have h15 : (N : ℤ) = 15 := by exact_mod_cast hN15
  have h5 : z ^ 2 = 5 := by linarith
  have h1 : z ≤ 2 := by nlinarith
  have h2 : -2 ≤ z := by nlinarith
  interval_cases z <;> omega

/-! ## toNat helper -/

private lemma toNat_pos_of_pos {k : ℤ} (hk : 0 < k) : 0 < k.toNat := by
  have h : 0 < (k.toNat : ℤ) := by rw [Int.toNat_of_nonneg hk.le]; exact hk
  exact_mod_cast h

private lemma toNat_cast_real {k : ℤ} (hk : 0 < k) : (k.toNat : ℝ) = (k : ℝ) := by
  have h : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk.le
  exact_mod_cast h

/-! ## w ∈ ℚ cases — reuse no_prime_F4_form -/

-- δ > 0: N = (δ + 3νb)(2δ + 3νb), apply no_prime_F4_form with x=δ.toNat, y=3νb
private lemma f2_wQ_pos {N : ℕ} (hN15 : N = 15)
    {a b ν : ℝ} (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (hNreal : (N : ℝ) = ν ^ 2 * (a + 2 * b) * (2 * a + b))
    {δ : ℤ} (hδ : (δ : ℝ) = ν * (a - b)) (hδ_pos : 0 < δ)
    (w_q : ℚ) (hw : (w_q : ℝ) = ν * (a + b)) : δ = 2 := by
  -- y_q = (w_q - δ)/2 = νb ∈ ℚ
  set y_q : ℚ := (w_q - (δ : ℚ)) / 2
  have hy_R : (y_q : ℝ) = ν * b := by
    have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
    have : (y_q : ℝ) * 2 = ν * b * 2 := by
      push_cast [y_q]; field_simp; linarith [hw, hδ]
    linarith
  have hy_pos : 0 < y_q := by
    have : (0 : ℝ) < (y_q : ℝ) := by rw [hy_R]; exact mul_pos hν hb
    exact_mod_cast this
  -- δ.toNat as ℝ = ν(a-b)
  have hdn_R : (δ.toNat : ℝ) = ν * (a - b) := by
    rw [toNat_cast_real hδ_pos]; exact hδ
  have hdn_pos : 0 < δ.toNat := toNat_pos_of_pos hδ_pos
  -- N = (δ.toNat + 3*y_q)(2*δ.toNat + 3*y_q) in ℚ
  have hNq : (N : ℚ) = ((δ.toNat : ℚ) + 3 * y_q) * (2 * (δ.toNat : ℚ) + 3 * y_q) := by
    have hNR : (N : ℝ) = ((δ.toNat : ℝ) + 3 * (y_q : ℝ)) * (2 * (δ.toNat : ℝ) + 3 * (y_q : ℝ)) := by
      rw [hy_R, hdn_R, hNreal]; ring
    exact_mod_cast show ((N : ℚ) : ℝ) =
        (((δ.toNat : ℚ) + 3 * y_q) * (2 * (δ.toNat : ℚ) + 3 * y_q) : ℚ) by
      push_cast; linarith [hNR]
  subst hN15
  obtain ⟨hx, -⟩ := Erdos634.Draft.R8N15Arith.F4_form_15 δ.toNat hdn_pos (3 * y_q) (by positivity) hNq
  have := Int.toNat_of_nonneg hδ_pos.le
  omega

-- δ < 0: N = (-δ + 3νa)(2*(-δ) + 3νa), apply no_prime_F4_form with x=(-δ).toNat, y=3νa
private lemma f2_wQ_neg {N : ℕ} (hN15 : N = 15)
    {a b ν : ℝ} (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (hNreal : (N : ℝ) = ν ^ 2 * (a + 2 * b) * (2 * a + b))
    {δ : ℤ} (hδ : (δ : ℝ) = ν * (a - b)) (hδ_neg : δ < 0)
    (w_q : ℚ) (hw : (w_q : ℝ) = ν * (a + b)) : δ = -2 := by
  -- x_q = (w_q + δ)/2 = νa ∈ ℚ
  set x_q : ℚ := (w_q + (δ : ℚ)) / 2
  have hx_R : (x_q : ℝ) = ν * a := by
    have : (x_q : ℝ) * 2 = ν * a * 2 := by push_cast [x_q]; field_simp; linarith [hw, hδ]
    linarith
  have hx_pos : 0 < x_q := by
    have : (0 : ℝ) < (x_q : ℝ) := by rw [hx_R]; exact mul_pos hν ha
    exact_mod_cast this
  set δ' := -δ
  have hδ'_pos : 0 < δ' := by omega
  have hd'n_pos : 0 < δ'.toNat := toNat_pos_of_pos hδ'_pos
  have hd'n_R : (δ'.toNat : ℝ) = ν * (b - a) := by
    rw [toNat_cast_real hδ'_pos]
    simp only [δ']; push_cast; linarith [hδ]
  have hNq : (N : ℚ) = ((δ'.toNat : ℚ) + 3 * x_q) * (2 * (δ'.toNat : ℚ) + 3 * x_q) := by
    have hNR : (N : ℝ) = ((δ'.toNat : ℝ) + 3 * (x_q : ℝ)) * (2 * (δ'.toNat : ℝ) + 3 * (x_q : ℝ)) := by
      rw [hx_R, hd'n_R, hNreal]; ring
    exact_mod_cast show ((N : ℚ) : ℝ) =
        (((δ'.toNat : ℚ) + 3 * x_q) * (2 * (δ'.toNat : ℚ) + 3 * x_q) : ℚ) by
      push_cast; linarith [hNR]
  subst hN15
  obtain ⟨hx, -⟩ := Erdos634.Draft.R8N15Arith.F4_form_15 δ'.toNat hd'n_pos (3 * x_q) (by positivity) hNq
  have := Int.toNat_of_nonneg hδ'_pos.le
  simp only [δ'] at this hx
  omega

/-! ## Walk argument: δ ≠ 0 → ν(a+b) ∈ ℚ -/

-- When δ = ν(a−b) ≠ 0, the side-word walk on the target forces ν(a+b) ∈ ℚ.
-- δ < 0: use walk on target.oppLen(τ 0) = ν·a·(a+2b);  coefficient na+nb−δ > 0.
-- δ > 0: use walk on target.oppLen(τ 1) = ν·b·(2a+b);  coefficient na+nb+δ > 0.
-- Key algebraic identity (verified by ring): from na·u+nb·v+nc·z = u·(u+2v) (or v·(2u+v))
-- and u²+uv+v² = z², one derives (na+nb∓δ)·w = integer, giving w ∈ ℚ.
private lemma f2_w_rational {N : ℕ} (D : CongruentDissection N) {α a b c ν : ℝ}
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : D.target.F2Data α a b c ν)
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    {δ : ℤ} (hδ : (δ : ℝ) = ν * (a - b)) (hδ0 : δ ≠ 0)
    {z : ℤ} (hz : (z : ℝ) = ν * c) :
    ∃ w_q : ℚ, (w_q : ℝ) = ν * (a + b) := by
  obtain ⟨σ_m, -, hm_a, -, hm_b, -, hm_c⟩ := hm
  obtain ⟨-, hgrid⟩ := ht
  obtain ⟨τ, -, ht0, -, ht1, -, -⟩ := hgrid
  -- (νa)²+(νa)(νb)+(νb)² = (νc)² = z²
  have hc2_nuv : (ν * a) ^ 2 + (ν * a) * (ν * b) + (ν * b) ^ 2 = (z : ℝ) ^ 2 := by
    rw [hz]; linear_combination -ν ^ 2 * hc2
  -- δ = νa − νb
  have hδ_uv : (δ : ℝ) = ν * a - ν * b := by linarith [hδ]
  rcases lt_or_gt_of_ne (show (δ : ℝ) ≠ 0 by exact_mod_cast hδ0) with hδ_neg | hδ_pos
  · -- δ < 0: walk on target.oppLen(τ 0) = ν·a·(a+2b)
    obtain ⟨na, nb, nc, hwalk⟩ := D.side_word σ_m hm_a hm_b hm_c (τ 0)
    have hwalkR : (na : ℝ) * a + nb * b + nc * c = ν * (a * (a + 2 * b)) :=
      hwalk.symm.trans ht0
    -- Multiply by ν: na·(νa) + nb·(νb) + nc·(νc) = (νa)·((νa)+2(νb))
    have h5 : (na : ℝ) * (ν * a) + nb * (ν * b) + nc * (z : ℝ) =
        (ν * a) * (ν * a + 2 * (ν * b)) := by
      rw [hz]; linear_combination ν * hwalkR
    -- (na+nb−δ)·w = 2z²−δ²−(na−nb)·δ−2nc·z
    have hW_eq : ((na : ℝ) + nb - (δ : ℝ)) * (ν * (a + b)) =
        2 * (z : ℝ) ^ 2 - (δ : ℝ) ^ 2 - ((na : ℝ) - nb) * (δ : ℝ) - 2 * nc * (z : ℝ) := by
      rw [show ν * (a + b) = ν * a + ν * b from by ring, hδ_uv]
      linear_combination 2 * h5 + 2 * hc2_nuv
    have hδ_neg_int : δ < 0 := by exact_mod_cast hδ_neg
    have hden_pos : (0 : ℤ) < (na : ℤ) + nb - δ := by
      have h1 : (0 : ℤ) ≤ (na : ℤ) := Int.natCast_nonneg na
      have h2 : (0 : ℤ) ≤ (nb : ℤ) := Int.natCast_nonneg nb
      omega
    set num_z : ℤ := 2 * z ^ 2 - δ ^ 2 - ((na : ℤ) - nb) * δ - 2 * nc * z
    set den_z : ℤ := (na : ℤ) + nb - δ
    refine ⟨(num_z : ℚ) / (den_z : ℚ), ?_⟩
    have hden_ne_r : (den_z : ℝ) ≠ 0 := by exact_mod_cast hden_pos.ne'
    have hW' : (den_z : ℝ) * (ν * (a + b)) = (num_z : ℝ) := by
      simp only [den_z, num_z]; push_cast; linarith [hW_eq]
    simp only [Rat.cast_div, Rat.cast_intCast]
    rw [div_eq_iff hden_ne_r]; linear_combination -hW'
  · -- δ > 0: walk on target.oppLen(τ 1) = ν·b·(2a+b)
    obtain ⟨na, nb, nc, hwalk⟩ := D.side_word σ_m hm_a hm_b hm_c (τ 1)
    have hwalkR : (na : ℝ) * a + nb * b + nc * c = ν * (b * (2 * a + b)) :=
      hwalk.symm.trans ht1
    have h5 : (na : ℝ) * (ν * a) + nb * (ν * b) + nc * (z : ℝ) =
        (ν * b) * (2 * (ν * a) + (ν * b)) := by
      rw [hz]; linear_combination ν * hwalkR
    -- (na+nb+δ)·w = 2z²−δ²+(na−nb)·δ−2nc·z
    have hW_eq : ((na : ℝ) + nb + (δ : ℝ)) * (ν * (a + b)) =
        2 * (z : ℝ) ^ 2 - (δ : ℝ) ^ 2 - ((na : ℝ) - nb) * (δ : ℝ) - 2 * nc * (z : ℝ) := by
      rw [show ν * (a + b) = ν * a + ν * b from by ring, hδ_uv]
      linear_combination 2 * h5 + 2 * hc2_nuv
    have hδ_pos_int : (0 : ℤ) < δ := by exact_mod_cast hδ_pos
    have hden_pos : (0 : ℤ) < (na : ℤ) + nb + δ := by
      have h1 : (0 : ℤ) ≤ (na : ℤ) := Int.natCast_nonneg na
      have h2 : (0 : ℤ) ≤ (nb : ℤ) := Int.natCast_nonneg nb
      omega
    set num_z : ℤ := 2 * z ^ 2 - δ ^ 2 - ((na : ℤ) - nb) * δ - 2 * nc * z
    set den_z : ℤ := (na : ℤ) + nb + δ
    refine ⟨(num_z : ℚ) / (den_z : ℚ), ?_⟩
    have hden_ne_r : (den_z : ℝ) ≠ 0 := by exact_mod_cast hden_pos.ne'
    have hW' : (den_z : ℝ) * (ν * (a + b)) = (num_z : ℝ) := by
      simp only [den_z, num_z]; push_cast; linarith [hW_eq]
    simp only [Rat.cast_div, Rat.cast_intCast]
    rw [div_eq_iff hden_ne_r]; linear_combination -hW'

/-! ## Core: given δ=(ν(a-b):ℤ) and z=(νc:ℤ), derive False -/

private lemma f2_core {N : ℕ} (D : CongruentDissection N) {α a b c ν : ℝ}
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : D.target.F2Data α a b c ν)
    (hN15 : N = 15)
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hNreal : (N : ℝ) = ν ^ 2 * (a + 2 * b) * (2 * a + b))
    (δ : ℤ) (hδ : (δ : ℝ) = ν * (a - b))
    (z : ℤ) (hz : (z : ℝ) = ν * c) : False := by
  by_cases hδ0 : δ = 0
  · exact f2_delta_zero_False hN15 (by
      have hNeq : (N : ℤ) = 3 * z ^ 2 - δ ^ 2 := f2_N_eq hc2 hNreal hδ hz
      simp [hδ0] at hNeq; exact hNeq)
  · obtain ⟨w_q, hw⟩ := f2_w_rational D hm ht ha hb hν hc2 hδ hδ0 hz
    have hNeq : (N : ℤ) = 3 * z ^ 2 - δ ^ 2 := f2_N_eq hc2 hNreal hδ hz
    have h15 : (N : ℤ) = 15 := by exact_mod_cast hN15
    have hδ2 : δ ^ 2 = 4 := by
      rcases lt_trichotomy δ 0 with hn | h0 | hp
      · have := f2_wQ_neg hN15 ha hb hν hNreal hδ hn w_q hw; rw [this]; norm_num
      · exact absurd h0 hδ0
      · have := f2_wQ_pos hN15 ha hb hν hNreal hδ hp w_q hw; rw [this]; norm_num
    have h19 : (3 : ℤ) ∣ 19 := ⟨z ^ 2, by linarith⟩
    norm_num at h19

/-! ## Main theorem: 4 sign-cases for lemmaW -/

/-- No prime `N > 3` admits a 2π/3-model `CongruentDissection` with an F2Data target. -/
theorem f2_prime_contradiction {N : ℕ} (D : CongruentDissection N)
    {α a b c ν : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : D.target.F2Data α a b c ν)
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (hN15 : N = 15) : False := by
  obtain ⟨-, hc0, -, -⟩ := cos_alpha_of_TwoPiThree D.model hm
  have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := c_sq D.model hm
  have hNreal : (N : ℝ) = ν ^ 2 * (a + 2 * b) * (2 * a + b) :=
    F2_area_formula D hm ht ha hb hν
  obtain ⟨Mα, Mβ, hpar_α, hpar_β, hflux_α, hflux_β⟩ := Paper.cor_int D hα hm
  have hW_α := Row8.lemmaW_F2_alpha D.target hα ht
  have hW_β := Row8.lemmaW_F2_beta D.target hα ht
  have hdiv_α : 0 < c + a - b := divisor_alpha_pos hc2 ha hb hc0
  have hdiv_β : 0 < c + b - a := divisor_beta_pos hc2 ha hb hc0
  -- Abbreviate the common flux scalar
  set V : ℝ := ν * (c ^ 2 - a * (a + 2 * b) - b * (2 * a + b))
  have hV : V = -(3 * ν * a * b) := flux_eq_neg3ab hc2
  have hfact_α : ν * (a - b - c) * (c + a - b) = V := by rw [hV]; exact F2_factor_alpha hc2
  have hfact_β : -(ν * (a - b + c)) * (c + b - a) = V := by rw [hV]; exact F2_factor_beta hc2
  -- N odd
  have hN_odd : ¬ (2 : ℤ) ∣ (N : ℤ) := by
    have : (N : ℤ) = 15 := by exact_mod_cast hN15
    rw [this]; norm_num
  -- Mα and Mβ odd (from parity constraint in cor_int)
  have hMα_odd : ¬ (2 : ℤ) ∣ Mα := fun h => hN_odd (by
    have := Int.dvd_sub hpar_α h; simp at this; exact this)
  have hMβ_odd : ¬ (2 : ℤ) ∣ Mβ := fun h => hN_odd (by
    have := Int.dvd_sub hpar_β h; simp at this; exact this)
  -- Mα+Mβ and Mα-Mβ are even
  have hsum_even : (2 : ℤ) ∣ Mα + Mβ := by omega
  have hdiff_even : (2 : ℤ) ∣ Mα - Mβ := by omega
  obtain ⟨d, hd⟩ := hdiff_even  -- Mα - Mβ = 2d
  obtain ⟨s, hs⟩ := hsum_even   -- Mα + Mβ = 2s
  -- Dispatch on the 4 sign combinations from lemmaW
  rcases hW_α with hα_pos | hα_neg <;> rcases hW_β with hβ_pos | hβ_neg
  · -- (++) Mα = ν(a-b-c), Mβ = -(ν(a-b+c))
    -- flux_α = V, flux_β = V
    have hMα_eq : (Mα : ℝ) * (c + a - b) = ν * (a - b - c) * (c + a - b) := by
      have hV : (Mα : ℝ) * (c + a - b) = V := hflux_α.symm.trans hα_pos
      linarith [hfact_α]
    have hMβ_eq : (Mβ : ℝ) * (c + b - a) = -(ν * (a - b + c)) * (c + b - a) := by
      have hV : (Mβ : ℝ) * (c + b - a) = V := hflux_β.symm.trans hβ_pos
      linarith [hfact_β]
    have hMα_val : (Mα : ℝ) = ν * (a - b - c) := mul_right_cancel₀ hdiv_α.ne' hMα_eq
    have hMβ_val : (Mβ : ℝ) = -(ν * (a - b + c)) := mul_right_cancel₀ hdiv_β.ne' hMβ_eq
    -- Mα - Mβ = 2ν(a-b), Mα + Mβ = -2νc
    have h2d : (d : ℝ) = ν * (a - b) := by
      have : (Mα - Mβ : ℝ) = 2 * d := by exact_mod_cast hd
      rw [hMα_val, hMβ_val] at this; linarith
    have h2s : (-s : ℝ) = ν * c := by
      have : (Mα + Mβ : ℝ) = 2 * s := by exact_mod_cast hs
      rw [hMα_val, hMβ_val] at this; push_cast; linarith
    exact f2_core D hm ht hN15 ha hb hν hc2 hNreal d h2d (-s) (by push_cast; linarith [h2s])
  · -- (+-) Mα = ν(a-b-c), Mβ = ν(a-b+c)
    -- flux_α = V, flux_β = -V
    have hMα_eq : (Mα : ℝ) * (c + a - b) = ν * (a - b - c) * (c + a - b) := by
      have hV : (Mα : ℝ) * (c + a - b) = V := hflux_α.symm.trans hα_pos
      linarith [hfact_α]
    have hMβ_neg_eq : (Mβ : ℝ) * (c + b - a) = ν * (a - b + c) * (c + b - a) := by
      have hMβV : (Mβ : ℝ) * (c + b - a) = -V := hflux_β.symm.trans hβ_neg
      have hfact : ν * (a - b + c) * (c + b - a) = -V := by linarith [hfact_β]
      linarith [hMβV, hfact]
    have hMα_val : (Mα : ℝ) = ν * (a - b - c) := mul_right_cancel₀ hdiv_α.ne' hMα_eq
    have hMβ_val : (Mβ : ℝ) = ν * (a - b + c) := mul_right_cancel₀ hdiv_β.ne' hMβ_neg_eq
    -- Mα - Mβ = -2νc, Mα + Mβ = 2ν(a-b)
    have h2d : (-d : ℝ) = ν * c := by
      have : (Mα - Mβ : ℝ) = 2 * d := by exact_mod_cast hd
      rw [hMα_val, hMβ_val] at this; push_cast; linarith
    have h2s : (s : ℝ) = ν * (a - b) := by
      have : (Mα + Mβ : ℝ) = 2 * s := by exact_mod_cast hs
      rw [hMα_val, hMβ_val] at this; linarith
    exact f2_core D hm ht hN15 ha hb hν hc2 hNreal s h2s (-d) (by push_cast; linarith [h2d])
  · -- (-+) Mα = -(ν(a-b-c)), Mβ = -(ν(a-b+c))
    -- flux_α = -V, flux_β = V
    have hMα_neg_eq : (Mα : ℝ) * (c + a - b) = -(ν * (a - b - c)) * (c + a - b) := by
      have hMαV : (Mα : ℝ) * (c + a - b) = -V := hflux_α.symm.trans hα_neg
      have hfact : -(ν * (a - b - c)) * (c + a - b) = -V := by linarith [hfact_α]
      linarith [hMαV, hfact]
    have hMβ_eq : (Mβ : ℝ) * (c + b - a) = -(ν * (a - b + c)) * (c + b - a) := by
      have hV : (Mβ : ℝ) * (c + b - a) = V := hflux_β.symm.trans hβ_pos
      linarith [hfact_β]
    have hMα_val : (Mα : ℝ) = -(ν * (a - b - c)) := mul_right_cancel₀ hdiv_α.ne' hMα_neg_eq
    have hMβ_val : (Mβ : ℝ) = -(ν * (a - b + c)) := mul_right_cancel₀ hdiv_β.ne' hMβ_eq
    -- Mα - Mβ = 2νc, Mα + Mβ = -2ν(a-b)
    have h2d : (d : ℝ) = ν * c := by
      have : (Mα - Mβ : ℝ) = 2 * d := by exact_mod_cast hd
      rw [hMα_val, hMβ_val] at this; linarith
    have h2s : (-s : ℝ) = ν * (a - b) := by
      have : (Mα + Mβ : ℝ) = 2 * s := by exact_mod_cast hs
      rw [hMα_val, hMβ_val] at this; push_cast; linarith
    exact f2_core D hm ht hN15 ha hb hν hc2 hNreal (-s) (by push_cast; linarith [h2s]) d h2d
  · -- (--) Mα = -(ν(a-b-c)), Mβ = ν(a-b+c)
    -- flux_α = -V, flux_β = -V
    have hMα_neg_eq : (Mα : ℝ) * (c + a - b) = -(ν * (a - b - c)) * (c + a - b) := by
      have hMαV : (Mα : ℝ) * (c + a - b) = -V := hflux_α.symm.trans hα_neg
      have hfact : -(ν * (a - b - c)) * (c + a - b) = -V := by linarith [hfact_α]
      linarith [hMαV, hfact]
    have hMβ_neg_eq : (Mβ : ℝ) * (c + b - a) = ν * (a - b + c) * (c + b - a) := by
      have hMβV : (Mβ : ℝ) * (c + b - a) = -V := hflux_β.symm.trans hβ_neg
      have hfact : ν * (a - b + c) * (c + b - a) = -V := by linarith [hfact_β]
      linarith [hMβV, hfact]
    have hMα_val : (Mα : ℝ) = -(ν * (a - b - c)) := mul_right_cancel₀ hdiv_α.ne' hMα_neg_eq
    have hMβ_val : (Mβ : ℝ) = ν * (a - b + c) := mul_right_cancel₀ hdiv_β.ne' hMβ_neg_eq
    -- Mα - Mβ = -2ν(a-b), Mα + Mβ = 2νc
    have h2d : (-d : ℝ) = ν * (a - b) := by
      have : (Mα - Mβ : ℝ) = 2 * d := by exact_mod_cast hd
      rw [hMα_val, hMβ_val] at this; push_cast; linarith
    have h2s : (s : ℝ) = ν * c := by
      have : (Mα + Mβ : ℝ) = 2 * s := by exact_mod_cast hs
      rw [hMα_val, hMβ_val] at this; linarith
    exact f2_core D hm ht hN15 ha hb hν hc2 hNreal (-d) (by push_cast; linarith [h2d]) s h2s

#check @f2_prime_contradiction
#print axioms f2_prime_contradiction

end Erdos634.Draft.R8N15F2

#print axioms Erdos634.Draft.R8N15F2.f2_prime_contradiction
