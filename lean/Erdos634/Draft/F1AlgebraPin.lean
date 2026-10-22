-- Draft/F1AlgebraPin.lean — algebraic pinning for prop:F1free (Steps 1–2 of PROOF_F1free.md).
--
-- Proves `f1_pin_of_prime`: for a CongruentDissection with N prime, a 2π/3 model and an F1Data
-- target, the tile ratio is pinned: `c * ((N : ℝ) − 1) = a * ((N : ℝ) + 1)`.
--
-- Ingredients: Paper.cor_int (Mα,Mβ ∈ ℤ) + Row7.lemmaW_alpha/beta + F1AlgebraReal
--              + F1AreaIdentity.  No tile-placement layer; purely algebraic.
--
-- This is a COMPONENT of the full F1FreeStatement (C8 / prop:F1free); the geometric
-- Steps 3–5 (side-word separation, ℚ-independence of b, corner argument) are NOT here.
--
-- ZERO sorry.  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).

import Erdos634.Draft.FluxPaper
import Erdos634.Draft.FluxE2Pi3Row7
import Erdos634.Draft.F1AlgebraReal
import Erdos634.Draft.F1AreaIdentity
import Erdos634.Draft.ThmIsoShBridge

open scoped Classical

namespace Erdos634.Draft.F1AlgebraPin

open Erdos634.Geometry
open Erdos634.F1AlgebraReal
open Erdos634.Draft.F1AreaIdentity

/-! ## Auxiliary: c² = a²+ab+b² for TwoPiThreeData -/

private lemma twoPiThree_c_sq' (T : Tri) {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
  obtain ⟨σ, -, ha, -, hb, hγ, hc⟩ := h
  have hl := T.lawCos_perm σ
  rw [ha, hb, hc, hγ,
      show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three] at hl
  linarith

/-! ## Core helper: same-sign flux equations → pin -/

/-- From the SAME-sign flux equations (scale μ > 0 for both), derive `c*(N-1) = a*(N+1)`. -/
private lemma f1_pin_core {N : ℕ} {Ma Mb : ℤ} {a b c μ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hμ : 0 < μ) (hca : a < c)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hN_b : (N : ℝ) * b = μ ^ 2 * (a + b))
    (hMa : (Ma : ℝ) * (c + a - b) = μ * (2 * a + b - c))
    (hMb : (Mb : ℝ) * (c + b - a) = μ * (2 * a + b + c))
    (hN_prime : N.Prime) :
    c * ((N : ℝ) - 1) = a * ((N : ℝ) + 1) := by
  have hca_pos : 0 < c - a := by linarith
  -- c > 0 (from a > 0 and a < c)
  have hc_pos : 0 < c := by linarith
  -- Side equations from F1 algebra
  have eMa : (Ma : ℝ) * b = μ * (c - a) := F1_Ma_real a b c μ Ma hc2 ha.ne' hMa
  have eMb : (Mb : ℝ) * b = μ * (c + a) := F1_Mb_real a b c μ Mb hc2 ha.ne' hMb
  -- Positivity of Ma and Mb as reals
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
  -- Cast positivity to ℤ
  have hMa_Z : (0 : ℤ) < Ma := Int.cast_pos.mp hMa_pos_R
  have hMb_Z : (0 : ℤ) < Mb := Int.cast_pos.mp hMb_pos_R
  -- Product Ma * Mb = N (over ℝ, then ℤ)
  have hprod_R : (Ma : ℝ) * Mb = N :=
    F1_product_real a b c μ N Ma Mb hc2 ha.ne' hb.ne' hN_b hMa hMb
  have hprod_Z : Ma * Mb = ↑N := by exact_mod_cast hprod_R
  -- Ratio: Mb * (c-a) = Ma * (c+a)
  have hratio : (Mb : ℝ) * (c - a) = (Ma : ℝ) * (c + a) :=
    F1_ratio_real a b c μ Ma Mb hc2 ha.ne' hb.ne' hMa hMb
  -- Integer primality case split
  have hMa_toNat : (Ma.toNat : ℤ) = Ma := Int.toNat_of_nonneg (le_of_lt hMa_Z)
  have hMb_toNat : (Mb.toNat : ℤ) = Mb := Int.toNat_of_nonneg (le_of_lt hMb_Z)
  have hprod_Nat : Ma.toNat * Mb.toNat = N := by
    have h : (Ma.toNat : ℤ) * Mb.toNat = N := by rw [hMa_toNat, hMb_toNat]; exact hprod_Z
    exact_mod_cast h
  have hMa_dvd : Ma.toNat ∣ N := ⟨Mb.toNat, hprod_Nat.symm⟩
  rcases hN_prime.eq_one_or_self_of_dvd Ma.toNat hMa_dvd with h1 | hN_eq
  · -- Sub-case: Ma.toNat = 1 → Ma = 1, Mb = N
    have hMa1 : Ma = 1 := by
      have := hMa_toNat; rw [h1] at this; exact_mod_cast this.symm
    have hMbN : Mb = ↑N := by
      have : (1 : ℤ) * Mb = N := by rwa [hMa1] at hprod_Z
      omega
    -- N*(c-a) = c+a → c*(N-1) = a*(N+1)
    have hkey : (N : ℝ) * (c - a) = c + a := by
      have hMa1_R : (Ma : ℝ) = 1 := by exact_mod_cast hMa1
      have hMbN_R : (Mb : ℝ) = N := by exact_mod_cast hMbN
      calc (N : ℝ) * (c - a) = (Mb : ℝ) * (c - a) := by rw [hMbN_R]
        _ = (Ma : ℝ) * (c + a) := hratio
        _ = 1 * (c + a) := by rw [hMa1_R]
        _ = c + a := by ring
    linarith
  · -- Sub-case: Ma.toNat = N → Ma = N, Mb = 1 → c-a = N*(c+a), contradiction
    have hMaN : Ma = ↑N := by rw [← hMa_toNat, hN_eq]
    have hMb1_Nat : Mb.toNat = 1 :=
      Nat.eq_of_mul_eq_mul_left hN_prime.pos
        ((by have := hprod_Nat; rw [hN_eq] at this; exact this : N * Mb.toNat = N).trans
          (mul_one N).symm)
    have hMb1 : Mb = 1 := by
      have := hMb_toNat; rw [hMb1_Nat] at this; exact_mod_cast this.symm
    have hMaN_R : (Ma : ℝ) = N := by exact_mod_cast hMaN
    have hMb1_R : (Mb : ℝ) = 1 := by exact_mod_cast hMb1
    -- c-a = N*(c+a), but N ≥ 2 and c+a > c-a ≥ 0 — contradiction
    have hcontra : c - a = (N : ℝ) * (c + a) := by
      have hMaN_R : (Ma : ℝ) = N := by exact_mod_cast hMaN
      have hMb1_R' : (Mb : ℝ) = 1 := by exact_mod_cast hMb1
      calc c - a = 1 * (c - a) := by ring
        _ = (Mb : ℝ) * (c - a) := by rw [hMb1_R']
        _ = (Ma : ℝ) * (c + a) := hratio
        _ = (N : ℝ) * (c + a) := by rw [hMaN_R]
    have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN_prime.two_le
    nlinarith

/-! ## Main theorem -/

/-- For a prime `N`, a 2π/3 model, and an F1Data target with irrational `α`,
    the tile ratio is pinned: `c * (N − 1) = a * (N + 1)`.

    This is the algebraic half of `prop:F1free` (Steps 1–2 of PROOF_F1free.md). -/
theorem f1_pin_of_prime {N : ℕ} (D : CongruentDissection N) {α a b c μ : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hm : D.model.TwoPiThreeData α a b c)
    (hF1 : D.target.F1Data α a b c μ)
    (hμ : 0 < μ)
    (hN : N.Prime) :
    c * ((N : ℝ) - 1) = a * ((N : ℝ) + 1) := by
  -- Side positivity
  obtain ⟨-, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  -- c² = a²+ab+b²
  have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := twoPiThree_c_sq' D.model hm
  -- c > a
  have hca : a < c := by
    have h2 : a ^ 2 < c ^ 2 := by nlinarith [mul_pos ha0 hb0]
    by_contra hle
    push_neg at hle
    nlinarith [mul_le_mul hle hle hc0.le ha0.le]
  -- Area identity
  have hN_b : (N : ℝ) * b = μ ^ 2 * (a + b) := F1_area_identity D hm hF1 ha0 hb0 hμ
  -- Flux integers
  obtain ⟨Mα, Mβ, -, -, hcor_α, hcor_β⟩ := Paper.cor_int D hα hm
  -- Boundary flux from Row7
  have hWα := Row7.lemmaW_alpha D.target hα hF1
  have hWβ := Row7.lemmaW_beta D.target hα hF1
  -- Combine: flux equation from cor_int equals lemmaW value; four sign cases
  -- In each case Ma, Mb are chosen so that Ma*(c+a-b) = μ*(2a+b-c) (same sign μ)
  rcases hWα with hα1 | hα2 <;> rcases hWβ with hβ1 | hβ2
  · -- (++): Mα*(c+a-b) = μ*(2a+b-c), Mβ*(c+b-a) = μ*(2a+b+c)
    apply f1_pin_core ha0 hb0 hμ hca hc2 hN_b (Ma := Mα) (Mb := Mβ) _ _ hN
    · exact hcor_α.symm.trans hα1
    · exact hcor_β.symm.trans hβ1
  · -- (+-): use Ma=Mα, Mb=-Mβ so (-Mβ)*(c+b-a) = μ*(2a+b+c)
    apply f1_pin_core ha0 hb0 hμ hca hc2 hN_b (Ma := Mα) (Mb := -Mβ) _ _ hN
    · exact hcor_α.symm.trans hα1
    · have h : (Mβ : ℝ) * (c + b - a) = -(μ * (2 * a + b + c)) := hcor_β.symm.trans hβ2
      push_cast; linarith
  · -- (-+): use Ma=-Mα, Mb=Mβ so (-Mα)*(c+a-b) = μ*(2a+b-c)
    apply f1_pin_core ha0 hb0 hμ hca hc2 hN_b (Ma := -Mα) (Mb := Mβ) _ _ hN
    · have h : (Mα : ℝ) * (c + a - b) = -(μ * (2 * a + b - c)) := hcor_α.symm.trans hα2
      push_cast; linarith
    · exact hcor_β.symm.trans hβ1
  · -- (--): use Ma=-Mα, Mb=-Mβ
    apply f1_pin_core ha0 hb0 hμ hca hc2 hN_b (Ma := -Mα) (Mb := -Mβ) _ _ hN
    · have h : (Mα : ℝ) * (c + a - b) = -(μ * (2 * a + b - c)) := hcor_α.symm.trans hα2
      push_cast; linarith
    · have h : (Mβ : ℝ) * (c + b - a) = -(μ * (2 * a + b + c)) := hcor_β.symm.trans hβ2
      push_cast; linarith

#check @f1_pin_of_prime
#print axioms f1_pin_of_prime

/-! ## Strengthened version: also gives μ*(c-a) = b (Ma=1 conclusion) -/

/-- Like `f1_pin_core` but returns both `c*(N-1)=a*(N+1)` AND `μ*(c-a)=b` (Ma=1). -/
private lemma f1_pin_mu_core {N : ℕ} {Ma Mb : ℤ} {a b c μ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hμ : 0 < μ) (hca : a < c)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hN_b : (N : ℝ) * b = μ ^ 2 * (a + b))
    (hMa : (Ma : ℝ) * (c + a - b) = μ * (2 * a + b - c))
    (hMb : (Mb : ℝ) * (c + b - a) = μ * (2 * a + b + c))
    (hN_prime : N.Prime) :
    c * ((N : ℝ) - 1) = a * ((N : ℝ) + 1) ∧ μ * (c - a) = b := by
  have hca_pos : 0 < c - a := by linarith
  have hc_pos : 0 < c := by linarith
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
  have hprod_Z : Ma * Mb = ↑N := by exact_mod_cast hprod_R
  have hratio : (Mb : ℝ) * (c - a) = (Ma : ℝ) * (c + a) :=
    F1_ratio_real a b c μ Ma Mb hc2 ha.ne' hb.ne' hMa hMb
  have hMa_toNat : (Ma.toNat : ℤ) = Ma := Int.toNat_of_nonneg (le_of_lt hMa_Z)
  have hMb_toNat : (Mb.toNat : ℤ) = Mb := Int.toNat_of_nonneg (le_of_lt hMb_Z)
  have hprod_Nat : Ma.toNat * Mb.toNat = N := by
    have h : (Ma.toNat : ℤ) * Mb.toNat = N := by rw [hMa_toNat, hMb_toNat]; exact hprod_Z
    exact_mod_cast h
  have hMa_dvd : Ma.toNat ∣ N := ⟨Mb.toNat, hprod_Nat.symm⟩
  rcases hN_prime.eq_one_or_self_of_dvd Ma.toNat hMa_dvd with h1 | hN_eq
  · -- Ma.toNat = 1 → Ma = 1, Mb = N
    have hMa1 : Ma = 1 := by
      have := hMa_toNat; rw [h1] at this; exact_mod_cast this.symm
    have hMbN : Mb = ↑N := by
      have : (1 : ℤ) * Mb = N := by rwa [hMa1] at hprod_Z
      omega
    have hkey : (N : ℝ) * (c - a) = c + a := by
      have hMa1_R : (Ma : ℝ) = 1 := by exact_mod_cast hMa1
      have hMbN_R : (Mb : ℝ) = N := by exact_mod_cast hMbN
      calc (N : ℝ) * (c - a) = (Mb : ℝ) * (c - a) := by rw [hMbN_R]
        _ = (Ma : ℝ) * (c + a) := hratio
        _ = 1 * (c + a) := by rw [hMa1_R]
        _ = c + a := by ring
    have hmu : μ * (c - a) = b := by
      have hMa1_R : (Ma : ℝ) = 1 := by exact_mod_cast hMa1
      have := eMa; rw [hMa1_R, one_mul] at this; linarith
    exact ⟨by linarith, hmu⟩
  · -- Ma.toNat = N → contradiction
    exfalso
    have hMaN : Ma = ↑N := by rw [← hMa_toNat, hN_eq]
    have hMb1_Nat : Mb.toNat = 1 :=
      Nat.eq_of_mul_eq_mul_left hN_prime.pos
        ((by have := hprod_Nat; rw [hN_eq] at this; exact this : N * Mb.toNat = N).trans
          (mul_one N).symm)
    have hMb1 : Mb = 1 := by
      have := hMb_toNat; rw [hMb1_Nat] at this; exact_mod_cast this.symm
    have hMaN_R : (Ma : ℝ) = N := by exact_mod_cast hMaN
    have hMb1_R : (Mb : ℝ) = 1 := by exact_mod_cast hMb1
    have hcontra : c - a = (N : ℝ) * (c + a) := by
      calc c - a = 1 * (c - a) := by ring
        _ = (Mb : ℝ) * (c - a) := by rw [hMb1_R]
        _ = (Ma : ℝ) * (c + a) := hratio
        _ = (N : ℝ) * (c + a) := by rw [hMaN_R]
    have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN_prime.two_le
    nlinarith

/-- Like `f1_pin_of_prime` but also returns `μ*(c-a) = b` (the Ma=1 conclusion).
This is needed for F1SideWord steps 3–4 (PROOF_F1free.md). -/
theorem f1_pin_mu_of_prime {N : ℕ} (D : CongruentDissection N) {α a b c μ : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hm : D.model.TwoPiThreeData α a b c)
    (hF1 : D.target.F1Data α a b c μ)
    (hμ : 0 < μ)
    (hN : N.Prime) :
    c * ((N : ℝ) - 1) = a * ((N : ℝ) + 1) ∧ μ * (c - a) = b := by
  obtain ⟨-, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := twoPiThree_c_sq' D.model hm
  have hca : a < c := by
    have h2 : a ^ 2 < c ^ 2 := by nlinarith [mul_pos ha0 hb0]
    by_contra hle; push_neg at hle
    nlinarith [mul_le_mul hle hle hc0.le ha0.le]
  have hN_b : (N : ℝ) * b = μ ^ 2 * (a + b) := F1_area_identity D hm hF1 ha0 hb0 hμ
  obtain ⟨Mα, Mβ, -, -, hcor_α, hcor_β⟩ := Paper.cor_int D hα hm
  have hWα := Row7.lemmaW_alpha D.target hα hF1
  have hWβ := Row7.lemmaW_beta D.target hα hF1
  rcases hWα with hα1 | hα2 <;> rcases hWβ with hβ1 | hβ2
  · exact f1_pin_mu_core ha0 hb0 hμ hca hc2 hN_b (Ma := Mα) (Mb := Mβ)
      (hcor_α.symm.trans hα1) (hcor_β.symm.trans hβ1) hN
  · exact f1_pin_mu_core ha0 hb0 hμ hca hc2 hN_b (Ma := Mα) (Mb := -Mβ)
      (hcor_α.symm.trans hα1) (by push_cast; linarith [hcor_β.symm.trans hβ2]) hN
  · exact f1_pin_mu_core ha0 hb0 hμ hca hc2 hN_b (Ma := -Mα) (Mb := Mβ)
      (by push_cast; linarith [hcor_α.symm.trans hα2]) (hcor_β.symm.trans hβ1) hN
  · exact f1_pin_mu_core ha0 hb0 hμ hca hc2 hN_b (Ma := -Mα) (Mb := -Mβ)
      (by push_cast; linarith [hcor_α.symm.trans hα2])
      (by push_cast; linarith [hcor_β.symm.trans hβ2]) hN

#check @f1_pin_mu_of_prime

end Erdos634.Draft.F1AlgebraPin
