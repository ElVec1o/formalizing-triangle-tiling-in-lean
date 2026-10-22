-- Draft/R8F4PrimeContradiction.lean — No prime N admits a CongruentDissection with 2π/3 model
-- and F4PrimeData target.  (F4′ branch = F4 with a↔b.)
--
-- Proof route (PROOF_row8.md §3, F4′ case):
--   1. cor_int  →  Mα, Mβ ∈ ℤ with Mα ≡ Mβ ≡ N (mod 2)
--   2. lemmaW_F4prime_alpha/beta + F4prime_factor_alpha/beta
--      →  Mα = ∓ν(b+c), Mβ = ±ν(b−c)
--   3. Parity: N prime > 2 → N odd → Mα, Mβ odd → in all 4 sign cases,
--      yb := νb ∈ ℤ > 0;  zc := νc ∈ ℤ
--   4. F4prime_area_formula  →  (N : ℝ) = ν²(a+b)(a+2b) = (νb+νa)(2νb+νa)
--   5. y_q := (N − yb² − zc²)/(2yb) ∈ ℚ  (= νa > 0 using c²=a²+ab+b²)
--   6. no_prime_F4_form  →  N prime contradicts N = (yb + y_q)(2yb + y_q)  →  False.
--
-- ZERO sorry.  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).

import Erdos634.Draft.FluxPaper
import Erdos634.Draft.FluxE2Pi3Row8Mirrors
import Erdos634.Draft.FluxE2Pi3Row8Arith
import Erdos634.Draft.R8F4PrimeAreaFormula
import Erdos634.Draft.R8N15Arith
import Erdos634.Draft.R8CompositeArg
import Erdos634.Draft.ThmIsoShBridge

open scoped Classical

namespace Erdos634.Draft.R8N15F4Prime

open Erdos634.Geometry
open Erdos634.Row8Arith
open Erdos634.Draft.R8F4PrimeAreaFormula (F4prime_area_formula)
open Erdos634.Draft.R8CompositeArg (no_prime_F4_form)

/-! ## Auxiliary -/

private lemma c_sq (T : Tri) {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
  obtain ⟨σ, -, ha, -, hb, hγ, hc⟩ := h
  have hl := T.lawCos_perm σ
  rw [ha, hb, hc, hγ,
      show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three] at hl
  linarith

-- F4′ factor identities (analogues of F4_factor_alpha/beta but for the b-side extraction)
private lemma F4prime_factor_alpha {a b c : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (b + c) * (c + a - b) = a * (a + 2 * b + c) := by linear_combination hc2

private lemma F4prime_factor_beta {a b c : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (b - c) * (c + b - a) = a * (c - a - 2 * b) := by linear_combination -hc2

/-! ## Core: given integers yb = νb > 0 and zc = νc, derive False -/

private lemma f4prime_core
    {N : ℕ} (hN15 : N = 15)
    {a b c ν : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hNreal : (N : ℝ) = (ν * b + ν * a) * (2 * (ν * b) + ν * a))
    (yb : ℤ) (hyb_pos : 0 < yb) (hyb_R : (yb : ℝ) = ν * b)
    (zc : ℤ) (hzc_R : (zc : ℝ) = ν * c) : False := by
  -- N - yb² - zc² = 2*yb*(ν*a)  (using c²=a²+ab+b²)
  have hNid : (N : ℝ) - (yb : ℝ) ^ 2 - (zc : ℝ) ^ 2 = 2 * (yb : ℝ) * (ν * a) := by
    have hc2' : (ν * c) ^ 2 = (ν * b) ^ 2 + (ν * b) * (ν * a) + (ν * a) ^ 2 := by
      have h1 : (ν * c) ^ 2 = ν ^ 2 * c ^ 2 := by ring
      have h2 : (ν * b) ^ 2 = ν ^ 2 * b ^ 2 := by ring
      have h3 : (ν * a) ^ 2 = ν ^ 2 * a ^ 2 := by ring
      nlinarith [sq_nonneg ν, hc2]
    rw [hNreal, hyb_R, hzc_R]
    nlinarith [hc2']
  -- Define y_q ∈ ℚ = (N - yb² - zc²) / (2*yb)
  have hyb_ne_q : (yb : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (Int.ne_of_gt hyb_pos)
  set y_q : ℚ := ((N : ℚ) - (yb : ℚ) ^ 2 - (zc : ℚ) ^ 2) / (2 * (yb : ℚ))
  -- (y_q : ℝ) = ν * a
  have hy_R : (y_q : ℝ) = ν * a := by
    have h2yb_ne_q : (2 : ℚ) * yb ≠ 0 := mul_ne_zero two_ne_zero hyb_ne_q
    have h2yb_ne : (2 : ℝ) * (yb : ℝ) ≠ 0 :=
      mul_ne_zero two_ne_zero (Int.cast_ne_zero.mpr (Int.ne_of_gt hyb_pos))
    have hq_mul : y_q * (2 * (yb : ℚ)) = (N : ℚ) - yb ^ 2 - zc ^ 2 :=
      div_mul_cancel₀ _ h2yb_ne_q
    have hR_eq : (y_q : ℝ) * (2 * (yb : ℝ)) = (N : ℝ) - (yb : ℝ) ^ 2 - (zc : ℝ) ^ 2 := by
      exact_mod_cast hq_mul
    exact mul_right_cancel₀ h2yb_ne (by linarith [hNid])
  -- y_q > 0
  have hy_pos : 0 < y_q := by
    have : (0 : ℝ) < (y_q : ℝ) := by rw [hy_R]; exact mul_pos hν ha
    exact_mod_cast this
  -- yb.toNat > 0
  have hyb_nat_pos : 0 < yb.toNat := by
    have h : 0 < (yb.toNat : ℤ) := by rw [Int.toNat_of_nonneg hyb_pos.le]; exact hyb_pos
    exact_mod_cast h
  -- (yb.toNat : ℝ) = ν * b
  have hyb_nat_R : (yb.toNat : ℝ) = ν * b := by
    have h : (yb.toNat : ℤ) = yb := Int.toNat_of_nonneg hyb_pos.le
    have : (yb.toNat : ℝ) = (yb : ℝ) := by exact_mod_cast h
    rw [this, hyb_R]
  -- (N : ℚ) = (yb.toNat + y_q) * (2 * yb.toNat + y_q)
  have hNq : (N : ℚ) = ((yb.toNat : ℚ) + y_q) * (2 * (yb.toNat : ℚ) + y_q) := by
    have hNR : (N : ℝ) = ((yb.toNat : ℝ) + (y_q : ℝ)) * (2 * (yb.toNat : ℝ) + (y_q : ℝ)) := by
      rw [hyb_nat_R, hy_R]; linarith [hNreal]
    exact_mod_cast show ((N : ℚ) : ℝ) =
        (((yb.toNat : ℚ) + y_q) * (2 * (yb.toNat : ℚ) + y_q) : ℚ) by push_cast; linarith [hNR]
  subst hN15
  obtain ⟨hx2, hy1⟩ := Erdos634.Draft.R8N15Arith.F4_form_15 yb.toNat hyb_nat_pos y_q hy_pos hNq
  have hyb2 : (yb : ℝ) = 2 := by
    have hZ : yb = 2 := by have := Int.toNat_of_nonneg hyb_pos.le; omega
    rw [hZ]; norm_num
  have hya1 : ν * a = 1 := by rw [← hy_R, hy1]; norm_num
  have hzc7 : (zc : ℝ) ^ 2 = 7 := by
    have h := hNid
    rw [hyb2, hya1] at h
    push_cast at h
    nlinarith [h]
  have hzcZ : zc ^ 2 = 7 := by exact_mod_cast hzc7
  have h1 : zc ≤ 3 := by nlinarith
  have h2 : -3 ≤ zc := by nlinarith
  interval_cases zc <;> omega

/-! ## Main theorem -/

/-- No prime `N > 2` admits a `CongruentDissection` with a 2π/3 model and an F4PrimeData target. -/
theorem f4prime_prime_contradiction {N : ℕ} (D : CongruentDissection N)
    {α a b c ν : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : D.target.F4PrimeData α a b c ν)
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (hN15 : N = 15) : False := by
  obtain ⟨-, hc0, -, -⟩ := cos_alpha_of_TwoPiThree D.model hm
  have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := c_sq D.model hm
  have hcpos : 0 < c := hc0
  -- Area formula: N = ν²(a+b)(a+2b) = (νb+νa)(2νb+νa)
  have hNreal : (N : ℝ) = (ν * b + ν * a) * (2 * (ν * b) + ν * a) := by
    have h := F4prime_area_formula D hm ht ha hb hν; ring_nf at h ⊢; linarith
  -- cor_int
  obtain ⟨Mα, Mβ, hpar_α, hpar_β, hflux_α, hflux_β⟩ := Paper.cor_int D hα hm
  -- Lemma W for F4′
  have hW_α := Row8.lemmaW_F4prime_alpha D.target hα ht
  have hW_β := Row8.lemmaW_F4prime_beta D.target hα ht
  -- Divisor positivity
  have hdiv_α : 0 < c + a - b := divisor_alpha_pos hc2 ha hb hcpos
  have hdiv_β : 0 < c + b - a := divisor_beta_pos hc2 ha hb hcpos
  -- N is odd
  have hN_odd : ¬ (2 : ℤ) ∣ (N : ℤ) := by
    have : (N : ℤ) = 15 := by exact_mod_cast hN15
    rw [this]; norm_num
  -- Mα and Mβ are odd
  have hMα_odd : ¬ (2 : ℤ) ∣ Mα := fun h => hN_odd (by
    have := Int.dvd_sub hpar_α h; simp at this; exact this)
  have hMβ_odd : ¬ (2 : ℤ) ∣ Mβ := fun h => hN_odd (by
    have := Int.dvd_sub hpar_β h; simp at this; exact this)
  -- Mα + Mβ and Mβ - Mα are both even
  have hsum_even : (2 : ℤ) ∣ Mα + Mβ := by omega
  have hdiff_even : (2 : ℤ) ∣ Mβ - Mα := by omega
  -- Factor identities
  have hfact_α := F4prime_factor_alpha hc2   -- (b+c)*(c+a-b) = a*(a+2b+c)
  have hfact_β := F4prime_factor_beta hc2    -- (b-c)*(c+b-a) = a*(c-a-2b)
  -- Handle all 4 sign combinations
  rcases hW_α with hα_pos | hα_neg <;> rcases hW_β with hβ_pos | hβ_neg
  · -- (++): α-flux positive → Mα = -ν(b+c);  β-flux positive → Mβ = ν(b-c)
    have hMα_R : (Mα : ℝ) * (c + a - b) = ν * (b * c - a * (a + 2 * b) - c * (a + b)) :=
      hflux_α.symm.trans hα_pos
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = ν * (-(b * c) - a * (a + 2 * b) + c * (a + b)) :=
      hflux_β.symm.trans hβ_pos
    have hMα_val : (Mα : ℝ) = -(ν * (b + c)) := by
      have h : (Mα : ℝ) * (c + a - b) = -(ν * (b + c)) * (c + a - b) := by
        linear_combination hMα_R + ν * hfact_α
      exact mul_right_cancel₀ hdiv_α.ne' h
    have hMβ_val : (Mβ : ℝ) = ν * (b - c) := by
      have h : (Mβ : ℝ) * (c + b - a) = ν * (b - c) * (c + b - a) := by
        linear_combination hMβ_R - ν * hfact_β
      exact mul_right_cancel₀ hdiv_β.ne' h
    -- 2νb = Mβ - Mα; 2νc = -(Mα + Mβ)
    have h2νb : 2 * (ν * b) = (Mβ : ℝ) - Mα := by rw [hMα_val, hMβ_val]; ring
    have h2νc : 2 * (ν * c) = -((Mα : ℝ) + Mβ) := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨d, hd⟩ := hdiff_even   -- Mβ - Mα = 2*d
    obtain ⟨s, hs⟩ := hsum_even    -- Mα + Mβ = 2*s
    have hyb_R : (d : ℝ) = ν * b := by
      have : (Mβ - Mα : ℝ) = 2 * d := by exact_mod_cast hd
      linarith [h2νb]
    have hzc_R : (-s : ℝ) = ν * c := by
      have : (Mα + Mβ : ℝ) = 2 * s := by exact_mod_cast hs
      linarith [h2νc]
    have hd_pos : 0 < d := by
      have : (0 : ℝ) < d := by rw [hyb_R]; exact mul_pos hν hb
      exact_mod_cast this
    exact f4prime_core hN15 ha hb hν hc2 hNreal d hd_pos hyb_R (-s) (by exact_mod_cast hzc_R)
  · -- (+-): α-flux positive → Mα = -ν(b+c);  β-flux negative → Mβ = -(ν(b-c)) = ν(c-b)
    have hMα_R : (Mα : ℝ) * (c + a - b) = ν * (b * c - a * (a + 2 * b) - c * (a + b)) :=
      hflux_α.symm.trans hα_pos
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = -(ν * (-(b * c) - a * (a + 2 * b) + c * (a + b))) :=
      hflux_β.symm.trans hβ_neg
    have hMα_val : (Mα : ℝ) = -(ν * (b + c)) := by
      have h : (Mα : ℝ) * (c + a - b) = -(ν * (b + c)) * (c + a - b) := by
        linear_combination hMα_R + ν * hfact_α
      exact mul_right_cancel₀ hdiv_α.ne' h
    have hMβ_val : (Mβ : ℝ) = -(ν * (b - c)) := by
      have hsimp : -(ν * (-(b * c) - a * (a + 2 * b) + c * (a + b))) = -(ν * (b - c)) * (c + b - a) := by
        linear_combination -ν * hfact_β - 2 * ν * hc2
      have h := hMβ_R.trans hsimp
      exact mul_right_cancel₀ hdiv_β.ne' h
    -- 2νb = -(Mα + Mβ); 2νc = Mβ - Mα
    have h2νb : 2 * (ν * b) = -((Mα : ℝ) + Mβ) := by rw [hMα_val, hMβ_val]; ring
    have h2νc : 2 * (ν * c) = (Mβ : ℝ) - Mα := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨s, hs⟩ := hsum_even    -- Mα + Mβ = 2*s
    obtain ⟨d, hd⟩ := hdiff_even   -- Mβ - Mα = 2*d
    have hyb_R : (-s : ℝ) = ν * b := by
      have : (Mα + Mβ : ℝ) = 2 * s := by exact_mod_cast hs
      linarith [h2νb]
    have hzc_R : (d : ℝ) = ν * c := by
      have : (Mβ - Mα : ℝ) = 2 * d := by exact_mod_cast hd
      linarith [h2νc]
    have hms_pos : 0 < -s := by
      have : (0 : ℝ) < (-s : ℝ) := by rw [hyb_R]; exact mul_pos hν hb
      exact_mod_cast this
    exact f4prime_core hN15 ha hb hν hc2 hNreal (-s) hms_pos (by exact_mod_cast hyb_R) d
      (by exact_mod_cast hzc_R)
  · -- (-+): α-flux negative → Mα = ν(b+c);  β-flux positive → Mβ = ν(b-c)
    have hMα_R : (Mα : ℝ) * (c + a - b) = -(ν * (b * c - a * (a + 2 * b) - c * (a + b))) :=
      hflux_α.symm.trans hα_neg
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = ν * (-(b * c) - a * (a + 2 * b) + c * (a + b)) :=
      hflux_β.symm.trans hβ_pos
    have hMα_val : (Mα : ℝ) = ν * (b + c) := by
      have h : (Mα : ℝ) * (c + a - b) = ν * (b + c) * (c + a - b) := by
        calc (Mα : ℝ) * (c + a - b)
            = -(ν * (b * c - a * (a + 2 * b) - c * (a + b))) := hMα_R
          _ = ν * a * (a + 2 * b + c) := by ring
          _ = ν * (b + c) * (c + a - b) := by linear_combination -ν * hfact_α
      exact mul_right_cancel₀ hdiv_α.ne' h
    have hMβ_val : (Mβ : ℝ) = ν * (b - c) := by
      have h : (Mβ : ℝ) * (c + b - a) = ν * (b - c) * (c + b - a) := by
        linear_combination hMβ_R - ν * hfact_β
      exact mul_right_cancel₀ hdiv_β.ne' h
    -- 2νb = Mα + Mβ; 2νc = -(Mβ - Mα)
    have h2νb : 2 * (ν * b) = (Mα : ℝ) + Mβ := by rw [hMα_val, hMβ_val]; ring
    have h2νc : 2 * (ν * c) = -((Mβ : ℝ) - Mα) := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨s, hs⟩ := hsum_even    -- Mα + Mβ = 2*s
    obtain ⟨d, hd⟩ := hdiff_even   -- Mβ - Mα = 2*d
    have hyb_R : (s : ℝ) = ν * b := by
      have : (Mα + Mβ : ℝ) = 2 * s := by exact_mod_cast hs
      linarith [h2νb]
    have hzc_R : (-d : ℝ) = ν * c := by
      have : (Mβ - Mα : ℝ) = 2 * d := by exact_mod_cast hd
      linarith [h2νc]
    have hs_pos : 0 < s := by
      have : (0 : ℝ) < (s : ℝ) := by rw [hyb_R]; exact mul_pos hν hb
      exact_mod_cast this
    exact f4prime_core hN15 ha hb hν hc2 hNreal s hs_pos (by exact_mod_cast hyb_R) (-d)
      (by exact_mod_cast hzc_R)
  · -- (--): both negative → Mα = ν(b+c), Mβ = -(ν(b-c)) = ν(c-b)
    have hMα_R : (Mα : ℝ) * (c + a - b) = -(ν * (b * c - a * (a + 2 * b) - c * (a + b))) :=
      hflux_α.symm.trans hα_neg
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = -(ν * (-(b * c) - a * (a + 2 * b) + c * (a + b))) :=
      hflux_β.symm.trans hβ_neg
    have hMα_val : (Mα : ℝ) = ν * (b + c) := by
      have h : (Mα : ℝ) * (c + a - b) = ν * (b + c) * (c + a - b) := by
        calc (Mα : ℝ) * (c + a - b)
            = -(ν * (b * c - a * (a + 2 * b) - c * (a + b))) := hMα_R
          _ = ν * a * (a + 2 * b + c) := by ring
          _ = ν * (b + c) * (c + a - b) := by linear_combination -ν * hfact_α
      exact mul_right_cancel₀ hdiv_α.ne' h
    have hMβ_val : (Mβ : ℝ) = -(ν * (b - c)) := by
      have hsimp : -(ν * (-(b * c) - a * (a + 2 * b) + c * (a + b))) = -(ν * (b - c)) * (c + b - a) := by
        linear_combination -ν * hfact_β - 2 * ν * hc2
      have h := hMβ_R.trans hsimp
      exact mul_right_cancel₀ hdiv_β.ne' h
    -- 2νb = -(Mβ - Mα); 2νc = Mα + Mβ
    have h2νb : 2 * (ν * b) = -((Mβ : ℝ) - Mα) := by rw [hMα_val, hMβ_val]; ring
    have h2νc : 2 * (ν * c) = (Mα : ℝ) + Mβ := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨d, hd⟩ := hdiff_even   -- Mβ - Mα = 2*d
    obtain ⟨s, hs⟩ := hsum_even    -- Mα + Mβ = 2*s
    have hyb_R : (-d : ℝ) = ν * b := by
      have : (Mβ - Mα : ℝ) = 2 * d := by exact_mod_cast hd
      linarith [h2νb]
    have hzc_R : (s : ℝ) = ν * c := by
      have : (Mα + Mβ : ℝ) = 2 * s := by exact_mod_cast hs
      linarith [h2νc]
    have hmd_pos : 0 < -d := by
      have : (0 : ℝ) < (-d : ℝ) := by rw [hyb_R]; exact mul_pos hν hb
      exact_mod_cast this
    exact f4prime_core hN15 ha hb hν hc2 hNreal (-d) hmd_pos (by exact_mod_cast hyb_R) s
      (by exact_mod_cast hzc_R)

#check @f4prime_prime_contradiction

end Erdos634.Draft.R8N15F4Prime

#print axioms Erdos634.Draft.R8N15F4Prime.f4prime_prime_contradiction
