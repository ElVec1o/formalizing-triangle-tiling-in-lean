-- Draft/F1N15.lean — Atom B of the GAPF1 route at N = 15: for an F1 tiling by 15 tiles, either `Ma = 1`
-- (the pin `c(N−1) = a(N+1) ∧ μ(c−a) = b`, discharged by `F1FreeProofM.f1_free_Ma1`) or `Ma = 3, Mb = 5, c = 4a`
-- (the open (3,5) branch).  Copy of `f1_pin_mu_of_prime` with the divisor step at N = 15.  UNAUDITED.
import Erdos634.Draft.F1AlgebraPin

open scoped Classical

namespace Erdos634.Draft.F1AlgebraPin

open Erdos634.Geometry
open Erdos634.F1AlgebraReal
open Erdos634.Draft.F1AreaIdentity

private lemma twoPiThree_c_sq'' (T : Tri) {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
  obtain ⟨σ, -, ha, -, hb, hγ, hc⟩ := h
  have hl := T.lawCos_perm σ
  rw [ha, hb, hc, hγ,
      show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three] at hl
  linarith

private lemma core15 {N : ℕ} (hN15 : N = 15) {Ma Mb : ℤ} {a b c μ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hμ : 0 < μ) (hca : a < c)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hN_b : (N : ℝ) * b = μ ^ 2 * (a + b))
    (hMa : (Ma : ℝ) * (c + a - b) = μ * (2 * a + b - c))
    (hMb : (Mb : ℝ) * (c + b - a) = μ * (2 * a + b + c)) :
    (c * ((N : ℝ) - 1) = a * ((N : ℝ) + 1) ∧ μ * (c - a) = b) ∨ c = 4 * a := by
  have hca_pos : 0 < c - a := by linarith
  have eMa : (Ma : ℝ) * b = μ * (c - a) := F1_Ma_real a b c μ Ma hc2 ha.ne' hMa
  have eMb : (Mb : ℝ) * b = μ * (c + a) := F1_Mb_real a b c μ Mb hc2 ha.ne' hMb
  have hMa_pos_R : 0 < (Ma : ℝ) := by
    have h : 0 < (Ma : ℝ) * b := by rw [eMa]; exact mul_pos hμ hca_pos
    rcases mul_pos_iff.mp h with ⟨h', _⟩ | ⟨_, h'⟩
    · exact h'
    · linarith
  have hMb_pos_R : 0 < (Mb : ℝ) := by
    have h : 0 < (Mb : ℝ) * b := by rw [eMb]; exact mul_pos hμ (by linarith)
    rcases mul_pos_iff.mp h with ⟨h', _⟩ | ⟨_, h'⟩
    · exact h'
    · linarith
  have hMa_Z : (0 : ℤ) < Ma := Int.cast_pos.mp hMa_pos_R
  have hMb_Z : (0 : ℤ) < Mb := Int.cast_pos.mp hMb_pos_R
  have hprod_R : (Ma : ℝ) * Mb = N :=
    F1_product_real a b c μ N Ma Mb hc2 ha.ne' hb.ne' hN_b hMa hMb
  have hprod_Z : Ma * Mb = (15 : ℤ) := by
    have : Ma * Mb = (N : ℤ) := by exact_mod_cast hprod_R
    rw [this, hN15]; norm_num
  have hratio : (Mb : ℝ) * (c - a) = (Ma : ℝ) * (c + a) :=
    F1_ratio_real a b c μ Ma Mb hc2 ha.ne' hb.ne' hMa hMb
  have hMa_le : Ma ≤ 15 := by nlinarith
  have hcases : (Ma = 1 ∧ Mb = 15) ∨ (Ma = 3 ∧ Mb = 5) ∨ (Ma = 5 ∧ Mb = 3) ∨ (Ma = 15 ∧ Mb = 1) := by
    interval_cases Ma <;> omega
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    subst h1 h2
    have hMa1 : ((1 : ℤ) : ℝ) = 1 := by norm_num
    have hMb15 : ((15 : ℤ) : ℝ) = 15 := by norm_num
    rw [hMa1] at eMa; rw [hMb15] at hratio; rw [hMa1] at hratio
    have hN' : (N : ℝ) = 15 := by exact_mod_cast hN15
    rw [hN']
    exact ⟨by linarith, by linarith⟩
  · right
    subst h1 h2
    have e3 : ((3 : ℤ) : ℝ) = 3 := by norm_num
    have e5 : ((5 : ℤ) : ℝ) = 5 := by norm_num
    rw [e3, e5] at hratio
    linarith
  · exfalso
    subst h1 h2
    have e5 : ((5 : ℤ) : ℝ) = 5 := by norm_num
    have e3 : ((3 : ℤ) : ℝ) = 3 := by norm_num
    rw [e3, e5] at hratio
    nlinarith
  · exfalso
    subst h1 h2
    have e1 : ((1 : ℤ) : ℝ) = 1 := by norm_num
    have e15 : ((15 : ℤ) : ℝ) = 15 := by norm_num
    rw [e1, e15] at hratio
    nlinarith


theorem f1_pin_mu_or_c4a_15 {N : ℕ} (D : CongruentDissection N) {α a b c μ : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hm : D.model.TwoPiThreeData α a b c)
    (hF1 : D.target.F1Data α a b c μ)
    (hμ : 0 < μ)
    (hN15 : N = 15) :
    (c * ((N : ℝ) - 1) = a * ((N : ℝ) + 1) ∧ μ * (c - a) = b) ∨ c = 4 * a := by
  obtain ⟨-, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := twoPiThree_c_sq'' D.model hm
  have hca : a < c := by
    have h2 : a ^ 2 < c ^ 2 := by nlinarith [mul_pos ha0 hb0]
    by_contra hle; push_neg at hle
    nlinarith [mul_le_mul hle hle hc0.le ha0.le]
  have hN_b : (N : ℝ) * b = μ ^ 2 * (a + b) := F1_area_identity D hm hF1 ha0 hb0 hμ
  obtain ⟨Mα, Mβ, -, -, hcor_α, hcor_β⟩ := Paper.cor_int D hα hm
  have hWα := Row7.lemmaW_alpha D.target hα hF1
  have hWβ := Row7.lemmaW_beta D.target hα hF1
  rcases hWα with hα1 | hα2 <;> rcases hWβ with hβ1 | hβ2
  · exact core15 hN15 ha0 hb0 hμ hca hc2 hN_b (Ma := Mα) (Mb := Mβ)
      (hcor_α.symm.trans hα1) (hcor_β.symm.trans hβ1) 
  · exact core15 hN15 ha0 hb0 hμ hca hc2 hN_b (Ma := Mα) (Mb := -Mβ)
      (hcor_α.symm.trans hα1) (by push_cast; linarith [hcor_β.symm.trans hβ2]) 
  · exact core15 hN15 ha0 hb0 hμ hca hc2 hN_b (Ma := -Mα) (Mb := Mβ)
      (by push_cast; linarith [hcor_α.symm.trans hα2]) (hcor_β.symm.trans hβ1) 
  · exact core15 hN15 ha0 hb0 hμ hca hc2 hN_b (Ma := -Mα) (Mb := -Mβ)
      (by push_cast; linarith [hcor_α.symm.trans hα2])
      (by push_cast; linarith [hcor_β.symm.trans hβ2]) 


end Erdos634.Draft.F1AlgebraPin

#print axioms Erdos634.Draft.F1AlgebraPin.f1_pin_mu_or_c4a_15
