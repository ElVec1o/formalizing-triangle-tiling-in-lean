-- Draft/R8F4Contradiction.lean — No prime N admits a CongruentDissection with 2π/3 model
-- and F4Data target.
--
-- Proof route (PROOF_row8.md §3, F4 case):
--   1. cor_int  →  Mα, Mβ ∈ ℤ with Mα ≡ Mβ ≡ N (mod 2)
--   2. lemmaW_F4_alpha/beta + F4_factor_alpha/beta  →  Mα = ε₁·ν(c−a), Mβ = ε₂·ν(a+c)
--   3. Parity: N prime > 2 → N odd → Mα, Mβ odd → in all 4 sign cases, |Mβ ± Mα| = 2νa ∈ 2ℤ
--      → xa := νa ∈ ℤ > 0; similarly xc := νc ∈ ℤ
--   4. F4_area_formula  →  (N : ℝ) = ν²(a+b)(2a+b) = (xa + νb)(2xa + νb)
--   5. y_q := (N − xa² − xc²)/(2xa) ∈ ℚ (using N−xa²−xc² = 2*xa*νb from hc2)
--      → y_q = νb > 0
--   6. no_prime_F4_form  →  N prime contradicts N = (xa + y_q)(2xa + y_q)  →  False.
--
-- ZERO sorry.  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).

import Erdos634.Draft.FluxPaper
import Erdos634.Draft.FluxE2Pi3Row8F4
import Erdos634.Draft.FluxE2Pi3Row8Arith
import Erdos634.Draft.R8F4AreaFormula
import Erdos634.Draft.R8CompositeArg
import Erdos634.Draft.ThmIsoShBridge

open scoped Classical

namespace Erdos634.Draft.R8F4Contradiction

open Erdos634.Geometry
open Erdos634.Row8Arith
open Erdos634.Draft.R8F4AreaFormula (F4_area_formula)
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

/-! ## Core: given integers xa = νa > 0 and xc = νc, derive False -/

private lemma f4_core
    {N : ℕ} (hN : N.Prime)
    {a b c ν : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hNreal : (N : ℝ) = (ν * a + ν * b) * (2 * (ν * a) + ν * b))
    (xa : ℤ) (hxa_pos : 0 < xa) (hxa_R : (xa : ℝ) = ν * a)
    (xc : ℤ) (hxc_R : (xc : ℝ) = ν * c) : False := by
  -- Step 1: N - xa² - xc² = 2*xa*(ν*b)  (using c² = a²+ab+b²)
  have hNid : (N : ℝ) - (xa : ℝ) ^ 2 - (xc : ℝ) ^ 2 = 2 * (xa : ℝ) * (ν * b) := by
    have hc2' : (ν * c) ^ 2 = (ν * a) ^ 2 + (ν * a) * (ν * b) + (ν * b) ^ 2 := by
      have h1 : (ν * c) ^ 2 = ν ^ 2 * c ^ 2 := by ring
      have h2 : (ν * a) ^ 2 = ν ^ 2 * a ^ 2 := by ring
      have h3 : (ν * b) ^ 2 = ν ^ 2 * b ^ 2 := by ring
      nlinarith [sq_nonneg ν, hc2]
    rw [hNreal, hxa_R, hxc_R]
    nlinarith [hc2']
  -- Step 2: define y_q ∈ ℚ = (N - xa² - xc²) / (2*xa)
  have hxa_ne_q : (xa : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (Int.ne_of_gt hxa_pos)
  set y_q : ℚ := ((N : ℚ) - (xa : ℚ) ^ 2 - (xc : ℚ) ^ 2) / (2 * (xa : ℚ))
  -- Step 3: (y_q : ℝ) = ν * b
  have hy_R : (y_q : ℝ) = ν * b := by
    have h2xa_ne_q : (2 : ℚ) * xa ≠ 0 := mul_ne_zero two_ne_zero hxa_ne_q
    have h2xa_ne : (2 : ℝ) * (xa : ℝ) ≠ 0 :=
      mul_ne_zero two_ne_zero (Int.cast_ne_zero.mpr (Int.ne_of_gt hxa_pos))
    -- In ℚ: y_q * (2 * xa) = N - xa² - xc² (by definition of y_q)
    have hq_mul : y_q * (2 * (xa : ℚ)) = (N : ℚ) - xa ^ 2 - xc ^ 2 :=
      div_mul_cancel₀ _ h2xa_ne_q
    -- Cast to ℝ
    have hR_eq : (y_q : ℝ) * (2 * (xa : ℝ)) = (N : ℝ) - (xa : ℝ) ^ 2 - (xc : ℝ) ^ 2 := by
      exact_mod_cast hq_mul
    exact mul_right_cancel₀ h2xa_ne (by linarith [hNid])
  -- Step 4: y_q > 0
  have hy_pos : 0 < y_q := by
    have : (0 : ℝ) < (y_q : ℝ) := by rw [hy_R]; exact mul_pos hν hb
    exact_mod_cast this
  -- Step 5: xa.toNat > 0
  have hxa_nat_pos : 0 < xa.toNat := by
    have h : 0 < (xa.toNat : ℤ) := by
      rw [Int.toNat_of_nonneg hxa_pos.le]; exact hxa_pos
    exact_mod_cast h
  -- Step 6: (xa.toNat : ℝ) = ν * a
  have hxa_nat_R : (xa.toNat : ℝ) = ν * a := by
    have h : (xa.toNat : ℤ) = xa := Int.toNat_of_nonneg hxa_pos.le
    have : (xa.toNat : ℝ) = (xa : ℝ) := by exact_mod_cast h
    rw [this, hxa_R]
  -- Step 7: (N : ℚ) = (xa.toNat + y_q) * (2 * xa.toNat + y_q)
  have hNq : (N : ℚ) = ((xa.toNat : ℚ) + y_q) * (2 * (xa.toNat : ℚ) + y_q) := by
    have hNR : (N : ℝ) = ((xa.toNat : ℝ) + (y_q : ℝ)) * (2 * (xa.toNat : ℝ) + (y_q : ℝ)) := by
      rw [hxa_nat_R, hy_R]; linarith [hNreal]
    exact_mod_cast show ((N : ℚ) : ℝ) =
        (((xa.toNat : ℚ) + y_q) * (2 * (xa.toNat : ℚ) + y_q) : ℚ) by push_cast; linarith [hNR]
  -- Step 8: contradiction
  exact no_prime_F4_form N hN xa.toNat hxa_nat_pos y_q hy_pos hNq

/-! ## Extract integers from sign cases -/

-- In each sign case, extract xa : ℤ = νa and xc : ℤ = νc from Mα, Mβ and parity.
-- The four flux sign combinations (ε₁, ε₂ from lemmaW) give different formulas for xa, xc.


/-! ## Main theorem -/

/-- No prime `N > 2` admits a `CongruentDissection` with a 2π/3 model and an F4Data target. -/
theorem f4_prime_contradiction {N : ℕ} (D : CongruentDissection N)
    {α a b c ν : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : D.target.F4Data α a b c ν)
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (hN : N.Prime)
    (hN2 : 2 < N) : False := by
  -- Side positivity
  obtain ⟨-, hc0, -, -⟩ := cos_alpha_of_TwoPiThree D.model hm
  -- c² = a²+ab+b²
  have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := c_sq D.model hm
  -- c > 0
  have hcpos : 0 < c := hc0
  -- Area formula: N = ν²(a+b)(2a+b) = (νa + νb)(2νa + νb)
  have hNreal : (N : ℝ) = (ν * a + ν * b) * (2 * (ν * a) + ν * b) := by
    have h := F4_area_formula D hm ht ha hb hν; ring_nf at h ⊢; linarith
  -- cor_int: Mα, Mβ ∈ ℤ, parities, flux equations
  obtain ⟨Mα, Mβ, hpar_α, hpar_β, hflux_α, hflux_β⟩ := Paper.cor_int D hα hm
  -- Lemma W
  have hW_α := Row8.lemmaW_F4_alpha D.target hα ht
  have hW_β := Row8.lemmaW_F4_beta D.target hα ht
  -- Divisor positivity
  have hdiv_α : 0 < c + a - b := divisor_alpha_pos hc2 ha hb hcpos
  have hdiv_β : 0 < c + b - a := divisor_beta_pos hc2 ha hb hcpos
  -- Factor identities
  have hfact_α := F4_factor_alpha hc2  -- (a-c)*(c+a-b) = -b*(2a+b-c)
  have hfact_β := F4_factor_beta hc2   -- (a+c)*(c+b-a) = b*(2a+b+c)
  -- N is odd
  have hN_odd : ¬ (2 : ℤ) ∣ (N : ℤ) := by
    intro hdvd
    have : N = 2 := (hN.eq_one_or_self_of_dvd 2 (by exact_mod_cast hdvd) |>.resolve_left (by omega)).symm
    omega
  -- Mα and Mβ are odd
  have hMα_odd : ¬ (2 : ℤ) ∣ Mα := fun h => hN_odd (by
    have := Int.dvd_sub hpar_α h; simp at this; exact this)
  have hMβ_odd : ¬ (2 : ℤ) ∣ Mβ := fun h => hN_odd (by
    have := Int.dvd_sub hpar_β h; simp at this; exact this)
  -- Mα + Mβ and Mβ - Mα are both even
  have hsum_even : (2 : ℤ) ∣ Mα + Mβ := by omega
  have hdiff_even : (2 : ℤ) ∣ Mβ - Mα := by omega
  -- From each sign case, extract Mα = ε₁*ν(c-a) and Mβ = ε₂*ν(a+c), then call f4_core
  -- Helper to extract νa from a sum s where 2*s = ε*(Mβ ± Mα)
  -- We handle all 4 sign combos.
  rcases hW_α with hα_pos | hα_neg <;> rcases hW_β with hβ_pos | hβ_neg
  · -- (++): Mα*(c+a-b) = ν*b*(2a+b-c), Mβ*(c+b-a) = ν*b*(2a+b+c)
    -- → Mα = ν(c-a), Mβ = ν(a+c)
    -- → Mβ - Mα = 2νa, Mβ + Mα = 2νc
    have hMα_R : (Mα : ℝ) * (c + a - b) = ν * b * (2 * a + b - c) := hflux_α.symm.trans hα_pos
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = ν * b * (2 * a + b + c) := hflux_β.symm.trans hβ_pos
    -- Mα = ν(c-a) [from factor: (a-c)(c+a-b) = -b(2a+b-c) → b(2a+b-c) = (c-a)(c+a-b)]
    have hMα_val : (Mα : ℝ) = ν * (c - a) := by
      have : (Mα : ℝ) * (c + a - b) = ν * (c - a) * (c + a - b) := by
        linear_combination hMα_R + ν * hfact_α
      exact mul_right_cancel₀ hdiv_α.ne' this
    have hMβ_val : (Mβ : ℝ) = ν * (a + c) := by
      have : (Mβ : ℝ) * (c + b - a) = ν * (a + c) * (c + b - a) := by
        linear_combination hMβ_R - ν * hfact_β
      exact mul_right_cancel₀ hdiv_β.ne' this
    -- 2νa = Mβ - Mα (as reals)
    have h2νa : 2 * (ν * a) = (Mβ : ℝ) - Mα := by rw [hMα_val, hMβ_val]; ring
    -- 2νc = Mβ + Mα
    have h2νc : 2 * (ν * c) = (Mβ : ℝ) + Mα := by rw [hMα_val, hMβ_val]; ring
    -- Get integer xa = (Mβ - Mα)/2
    obtain ⟨d, hd⟩ := hdiff_even  -- Mβ - Mα = 2*d
    obtain ⟨s, hs⟩ := hsum_even   -- Mα + Mβ = 2*s → Mβ + Mα = 2*s
    have hxa_R : (d : ℝ) = ν * a := by
      have : (Mβ - Mα : ℝ) = 2 * d := by exact_mod_cast hd
      linarith [h2νa]
    have hxc_R : (s : ℝ) = ν * c := by
      have : (Mα + Mβ : ℝ) = 2 * s := by exact_mod_cast hs
      linarith [h2νc]
    have hd_pos : 0 < d := by
      have : (0 : ℝ) < d := by rw [hxa_R]; exact mul_pos hν ha
      exact_mod_cast this
    exact f4_core hN ha hb hν hc2 hNreal d hd_pos hxa_R s hxc_R
  · -- (+-): Mα*(c+a-b) = ν*b*(2a+b-c), Mβ*(c+b-a) = -ν*b*(2a+b+c)
    have hMα_R : (Mα : ℝ) * (c + a - b) = ν * b * (2 * a + b - c) := hflux_α.symm.trans hα_pos
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = -(ν * b * (2 * a + b + c)) := hflux_β.symm.trans hβ_neg
    have hMα_val : (Mα : ℝ) = ν * (c - a) := by
      have : (Mα : ℝ) * (c + a - b) = ν * (c - a) * (c + a - b) := by
        linear_combination hMα_R + ν * hfact_α
      exact mul_right_cancel₀ hdiv_α.ne' this
    have hMβ_val : (Mβ : ℝ) = -(ν * (a + c)) := by
      have : (Mβ : ℝ) * (c + b - a) = -(ν * (a + c)) * (c + b - a) := by
        linear_combination hMβ_R + ν * hfact_β
      exact mul_right_cancel₀ hdiv_β.ne' this
    -- 2νa = -(Mβ + Mα)
    have h2νa : 2 * (ν * a) = -((Mβ : ℝ) + Mα) := by rw [hMα_val, hMβ_val]; ring
    -- 2νc = Mα - Mβ
    have h2νc : 2 * (ν * c) = (Mα : ℝ) - Mβ := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨s, hs⟩ := hsum_even   -- Mα + Mβ = 2*s
    obtain ⟨d, hd⟩ := hdiff_even  -- Mβ - Mα = 2*d → Mα - Mβ = 2*(-d)
    -- xa = -s (since 2νa = -(Mβ+Mα) = -(2s) ... wait Mα+Mβ = 2s and Mβ+Mα = 2s)
    have hxa_R : (-s : ℝ) = ν * a := by
      have : (Mα + Mβ : ℝ) = 2 * s := by exact_mod_cast hs
      linarith [h2νa]
    have hxc_R : (-d : ℝ) = ν * c := by
      have : (Mβ - Mα : ℝ) = 2 * d := by exact_mod_cast hd
      linarith [h2νc]
    have hms_pos : 0 < -s := by
      have : (0 : ℝ) < (-s : ℝ) := by rw [hxa_R]; exact mul_pos hν ha
      exact_mod_cast this
    exact f4_core hN ha hb hν hc2 hNreal (-s) hms_pos (by exact_mod_cast hxa_R) (-d)
      (by exact_mod_cast hxc_R)
  · -- (-+): Mα*(c+a-b) = -ν*b*(2a+b-c), Mβ*(c+b-a) = ν*b*(2a+b+c)
    have hMα_R : (Mα : ℝ) * (c + a - b) = -(ν * b * (2 * a + b - c)) := hflux_α.symm.trans hα_neg
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = ν * b * (2 * a + b + c) := hflux_β.symm.trans hβ_pos
    have hMα_val : (Mα : ℝ) = -(ν * (c - a)) := by
      have : (Mα : ℝ) * (c + a - b) = -(ν * (c - a)) * (c + a - b) := by
        linear_combination hMα_R - ν * hfact_α
      exact mul_right_cancel₀ hdiv_α.ne' this
    have hMβ_val : (Mβ : ℝ) = ν * (a + c) := by
      have : (Mβ : ℝ) * (c + b - a) = ν * (a + c) * (c + b - a) := by
        linear_combination hMβ_R - ν * hfact_β
      exact mul_right_cancel₀ hdiv_β.ne' this
    have h2νa : 2 * (ν * a) = (Mβ : ℝ) + Mα := by rw [hMα_val, hMβ_val]; ring
    have h2νc : 2 * (ν * c) = (Mβ : ℝ) - Mα := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨s, hs⟩ := hsum_even
    obtain ⟨d, hd⟩ := hdiff_even
    have hxa_R : (s : ℝ) = ν * a := by
      have : (Mα + Mβ : ℝ) = 2 * s := by exact_mod_cast hs
      linarith [h2νa]
    have hxc_R : (d : ℝ) = ν * c := by
      have : (Mβ - Mα : ℝ) = 2 * d := by exact_mod_cast hd
      linarith [h2νc]
    have hs_pos : 0 < s := by
      have : (0 : ℝ) < (s : ℝ) := by rw [hxa_R]; exact mul_pos hν ha
      exact_mod_cast this
    exact f4_core hN ha hb hν hc2 hNreal s hs_pos (by exact_mod_cast hxa_R) d
      (by exact_mod_cast hxc_R)
  · -- (--): both negative
    have hMα_R : (Mα : ℝ) * (c + a - b) = -(ν * b * (2 * a + b - c)) := hflux_α.symm.trans hα_neg
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = -(ν * b * (2 * a + b + c)) := hflux_β.symm.trans hβ_neg
    have hMα_val : (Mα : ℝ) = -(ν * (c - a)) := by
      have : (Mα : ℝ) * (c + a - b) = -(ν * (c - a)) * (c + a - b) := by
        linear_combination hMα_R - ν * hfact_α
      exact mul_right_cancel₀ hdiv_α.ne' this
    have hMβ_val : (Mβ : ℝ) = -(ν * (a + c)) := by
      have : (Mβ : ℝ) * (c + b - a) = -(ν * (a + c)) * (c + b - a) := by
        linear_combination hMβ_R + ν * hfact_β
      exact mul_right_cancel₀ hdiv_β.ne' this
    have h2νa : 2 * (ν * a) = -((Mβ : ℝ) - Mα) := by rw [hMα_val, hMβ_val]; ring
    have h2νc : 2 * (ν * c) = -((Mβ : ℝ) + Mα) := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨s, hs⟩ := hsum_even
    obtain ⟨d, hd⟩ := hdiff_even
    have hxa_R : (-d : ℝ) = ν * a := by
      have : (Mβ - Mα : ℝ) = 2 * d := by exact_mod_cast hd
      linarith [h2νa]
    have hxc_R : (-s : ℝ) = ν * c := by
      have : (Mα + Mβ : ℝ) = 2 * s := by exact_mod_cast hs
      linarith [h2νc]
    have hmd_pos : 0 < -d := by
      have : (0 : ℝ) < (-d : ℝ) := by rw [hxa_R]; exact mul_pos hν ha
      exact_mod_cast this
    exact f4_core hN ha hb hν hc2 hNreal (-d) hmd_pos (by exact_mod_cast hxa_R) (-s)
      (by exact_mod_cast hxc_R)

#check @f4_prime_contradiction

/-- No prime `N ≠ 2` admits a `CongruentDissection` with a 2π/3 model and an F4Data target. -/
theorem f4_any_prime_contradiction {N : ℕ} (D : CongruentDissection N)
    {α a b c ν : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : D.target.F4Data α a b c ν)
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (hN : N.Prime) (hN2 : N ≠ 2) : False := by
  have hN2lt : 2 < N := by
    have h2le : 2 ≤ N := hN.two_le
    omega
  exact f4_prime_contradiction D hα hm ht ha hb hν hN hN2lt

#check @f4_any_prime_contradiction

end Erdos634.Draft.R8F4Contradiction
