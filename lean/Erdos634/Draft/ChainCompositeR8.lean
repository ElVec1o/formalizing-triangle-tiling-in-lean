/-
Draft/ChainCompositeR8.lean — `GapR8 N` PROVED (not assumed) for every N with  ¬ 3 ∣ N  and  NoF4 N  (no
`N = (x+y)(2x+y)`, x ∈ ℕ>0, y ∈ ℚ>0), in particular N = 38 and N = 86.  Generalisation of the N = 15 ports
R8N15F2/F3/F3Prime/F4/F4Prime + Chain15R8.gapR8_fifteen: the geometric/flux part is unchanged (parity Mα ≡ Mβ ≡ N
(mod 2) instead of "N odd"); the N = 15 arithmetic cores are replaced by (i) 3 ∤ N (F3, F3′: 3 ∣ k forces 3 ∣ 4N;
F2: δ = 0 gives N = 3z²) and (ii) NoF4 N (F2 δ ≠ 0, F4, F4′: N = (x+y)(2x+y)).
UNAUDITED.  Formalization debt, NOT /goal progress.  No sorry, no native_decide.
-/
import Erdos634.Draft.Chain15R8
import Erdos634.Draft.Chain38
import Erdos634.Draft.Chain86
import Erdos634.Draft.FluxDSideWord
import Erdos634.Draft.FluxE2Pi3Row8Arith
import Erdos634.Draft.FluxE2Pi3Row8F2
import Erdos634.Draft.FluxE2Pi3Row8F3
import Erdos634.Draft.FluxE2Pi3Row8F4
import Erdos634.Draft.FluxE2Pi3Row8Mirrors
import Erdos634.Draft.FluxPaper
import Erdos634.Draft.R8CompositeArg
import Erdos634.Draft.R8F2AreaFormula
import Erdos634.Draft.R8F2to4Bridge
import Erdos634.Draft.R8F3AreaFormula
import Erdos634.Draft.R8F3PrimeAreaFormula
import Erdos634.Draft.R8F4AreaFormula
import Erdos634.Draft.R8F4PrimeAreaFormula
import Erdos634.Draft.R8N15Arith
import Erdos634.Draft.ThmIsoShBridge

open scoped Classical

namespace Erdos634.Draft.R8Gen

/-- No `N = (x+y)(2x+y)` with `x ∈ ℕ>0`, `y ∈ ℚ>0`. -/
def NoF4 (N : ℕ) : Prop :=
  ∀ x : ℕ, 0 < x → ∀ y : ℚ, 0 < y → (N : ℚ) = (↑x + y) * (2 * ↑x + y) → False

/-- Integer reduction: `y ∈ ℚ>0` forces `y ∈ ℕ` (den | num², coprime). -/
theorem noF4_of_int (N : ℕ) (h : ∀ x r : ℕ, 0 < x → 0 < r → N ≠ (x + r) * (2 * x + r)) : NoF4 N := by
  intro x hx y hy heq
  have hnum_pos : 0 < y.num := Rat.num_pos.mpr hy
  have hden_pos : 0 < y.den := y.pos
  have hZ : (N : ℤ) * y.den ^ 2 = (↑x * ↑y.den + y.num) * (2 * ↑x * ↑y.den + y.num) := by
    have hd_ne : (y.den : ℚ) ≠ 0 := by exact_mod_cast hden_pos.ne'
    have hyd : y * (y.den : ℚ) = y.num := by exact_mod_cast Rat.mul_den_eq_num y
    have hQ : (N : ℚ) * y.den ^ 2 = (↑x * ↑y.den + y.num) * (2 * ↑x * ↑y.den + y.num) := by
      calc (N : ℚ) * y.den ^ 2
          = ((↑x + y) * (2 * ↑x + y)) * y.den ^ 2 := by rw [← heq]
        _ = (↑x * ↑y.den + y * ↑y.den) * (2 * ↑x * ↑y.den + y * ↑y.den) := by ring
        _ = (↑x * ↑y.den + ↑y.num) * (2 * ↑x * ↑y.den + ↑y.num) := by rw [hyd]
    exact_mod_cast hQ
  have hnn : (y.num.natAbs : ℤ) = y.num := Int.natAbs_of_nonneg (le_of_lt hnum_pos)
  have hNeq_nat : N * y.den ^ 2 = (x * y.den + y.num.natAbs) * (2 * x * y.den + y.num.natAbs) := by
    have hZ' : (N : ℤ) * y.den ^ 2 =
        (↑x * ↑y.den + ↑y.num.natAbs) * (2 * ↑x * ↑y.den + ↑y.num.natAbs) := by
      rw [hnn]; exact hZ
    exact_mod_cast hZ'
  set r := y.num.natAbs with hr
  set s := y.den with hs
  have hrpos : 0 < r := by simp [hr, Nat.pos_iff_ne_zero, ne_of_gt hnum_pos]
  have hcop : Nat.Coprime r s := y.reduced
  have hs_dvd_r2 : s ∣ r ^ 2 := by
    have hZ2 : (s : ℤ) ∣ (r : ℤ) ^ 2 := by
      have heqZ : (N : ℤ) * s ^ 2 = (x * s + r) * (2 * x * s + r) := by exact_mod_cast hNeq_nat
      have hdvd : (s : ℤ) ∣ (↑x * ↑s + ↑r) * (2 * ↑x * ↑s + ↑r) := by
        rw [← heqZ]; exact ⟨N * s, by ring⟩
      have heq2 : (↑x * ↑s + ↑r) * (2 * ↑x * ↑s + ↑r) =
          (r : ℤ) ^ 2 + s * (2 * x ^ 2 * s + 3 * x * r) := by ring
      rw [heq2] at hdvd
      have h2 : (s : ℤ) ∣ (s : ℤ) * (2 * x ^ 2 * s + 3 * x * r) := dvd_mul_right _ _
      have h3 := dvd_sub hdvd h2
      rwa [show (r : ℤ) ^ 2 + (s : ℤ) * (2 * ↑x ^ 2 * ↑s + 3 * ↑x * ↑r) -
          (s : ℤ) * (2 * ↑x ^ 2 * ↑s + 3 * ↑x * ↑r) = (r : ℤ) ^ 2 from by ring] at h3
    exact_mod_cast hZ2
  have hs1 : s = 1 := by
    have hcop2 : Nat.Coprime s (r ^ 2) := hcop.symm.pow_right 2
    have hs_dvd1 : s ∣ 1 := by
      have h := Nat.dvd_gcd (dvd_refl s) hs_dvd_r2
      rwa [hcop2] at h
    exact Nat.le_antisymm (Nat.le_of_dvd one_pos hs_dvd1) hden_pos
  rw [hs1] at hNeq_nat
  simp at hNeq_nat
  exact h x r hx hrpos hNeq_nat

theorem noF4_38 : NoF4 38 := by
  apply noF4_of_int
  intro x r hx hr h
  have hx7 : x ≤ 6 := by nlinarith
  have hr9 : r ≤ 9 := by nlinarith
  interval_cases x <;> interval_cases r <;> omega

theorem noF4_86 : NoF4 86 := by
  apply noF4_of_int
  intro x r hx hr h
  have hx7 : x ≤ 6 := by nlinarith
  have hr9 : r ≤ 9 := by nlinarith
  interval_cases x <;> interval_cases r <;> omega

end Erdos634.Draft.R8Gen


namespace Erdos634.Draft.R8Gen.F2

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

private lemma f2_delta_zero_False {N : ℕ} (h3 : ¬ (3 : ℤ) ∣ (N : ℤ))
    {z : ℤ} (hNeq : (N : ℤ) = 3 * z ^ 2) : False := by
  exact h3 ⟨z ^ 2, hNeq⟩
private lemma f2_unused_old (z : ℤ) (hNeq : (15 : ℤ) = 3 * z ^ 2) : False := by
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
private lemma f2_wQ_pos {N : ℕ} (hF4 : NoF4 N)
    {a b ν : ℝ} (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (hNreal : (N : ℝ) = ν ^ 2 * (a + 2 * b) * (2 * a + b))
    {δ : ℤ} (hδ : (δ : ℝ) = ν * (a - b)) (hδ_pos : 0 < δ)
    (w_q : ℚ) (hw : (w_q : ℝ) = ν * (a + b)) : False := by
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
  exact hF4 δ.toNat hdn_pos (3 * y_q) (by positivity) hNq

-- δ < 0: N = (-δ + 3νa)(2*(-δ) + 3νa), apply no_prime_F4_form with x=(-δ).toNat, y=3νa
private lemma f2_wQ_neg {N : ℕ} (hF4 : NoF4 N)
    {a b ν : ℝ} (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (hNreal : (N : ℝ) = ν ^ 2 * (a + 2 * b) * (2 * a + b))
    {δ : ℤ} (hδ : (δ : ℝ) = ν * (a - b)) (hδ_neg : δ < 0)
    (w_q : ℚ) (hw : (w_q : ℝ) = ν * (a + b)) : False := by
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
  exact hF4 δ'.toNat hd'n_pos (3 * x_q) (by positivity) hNq

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
    (h3 : ¬ (3 : ℤ) ∣ (N : ℤ)) (hF4 : NoF4 N)
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hNreal : (N : ℝ) = ν ^ 2 * (a + 2 * b) * (2 * a + b))
    (δ : ℤ) (hδ : (δ : ℝ) = ν * (a - b))
    (z : ℤ) (hz : (z : ℝ) = ν * c) : False := by
  by_cases hδ0 : δ = 0
  · exact f2_delta_zero_False h3 (by
      have hNeq : (N : ℤ) = 3 * z ^ 2 - δ ^ 2 := f2_N_eq hc2 hNreal hδ hz
      simp [hδ0] at hNeq; exact hNeq)
  · obtain ⟨w_q, hw⟩ := f2_w_rational D hm ht ha hb hν hc2 hδ hδ0 hz
    have hNeq : (N : ℤ) = 3 * z ^ 2 - δ ^ 2 := f2_N_eq hc2 hNreal hδ hz
    rcases lt_trichotomy δ 0 with hn | h0 | hp
    · exact f2_wQ_neg hF4 ha hb hν hNreal hδ hn w_q hw
    · exact absurd h0 hδ0
    · exact f2_wQ_pos hF4 ha hb hν hNreal hδ hp w_q hw

/-! ## Main theorem: 4 sign-cases for lemmaW -/

/-- No prime `N > 3` admits a 2π/3-model `CongruentDissection` with an F2Data target. -/
theorem f2_prime_contradiction {N : ℕ} (D : CongruentDissection N)
    {α a b c ν : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : D.target.F2Data α a b c ν)
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (h3 : ¬ (3 : ℤ) ∣ (N : ℤ)) (hF4 : NoF4 N) : False := by
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
    exact f2_core D hm ht h3 hF4 ha hb hν hc2 hNreal d h2d (-s) (by push_cast; linarith [h2s])
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
    exact f2_core D hm ht h3 hF4 ha hb hν hc2 hNreal s h2s (-d) (by push_cast; linarith [h2d])
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
    exact f2_core D hm ht h3 hF4 ha hb hν hc2 hNreal (-s) (by push_cast; linarith [h2s]) d h2d
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
    exact f2_core D hm ht h3 hF4 ha hb hν hc2 hNreal (-d) (by push_cast; linarith [h2d]) s h2s


end Erdos634.Draft.R8Gen.F2



namespace Erdos634.Draft.R8Gen.F3

open Erdos634.Geometry
open Erdos634.Row8Arith
open Erdos634.Draft.R8F3AreaFormula (F3_area_formula)

/-! ## Auxiliary -/

private lemma c_sq (T : Tri) {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
  obtain ⟨σ, -, ha, -, hb, hγ, hc⟩ := h
  have hl := T.lawCos_perm σ
  rw [ha, hb, hc, hγ,
      show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three] at hl
  linarith

-- F3 factor identities
private lemma F3_factor_alpha (ν : ℝ) {a b c : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ν * (-(c ^ 2) - c * (a + 2 * b) + 3 * b * (a + b)) = ν * (c - 2 * a - b) * (c + a - b) := by
  linear_combination -2 * ν * hc2

private lemma F3_factor_beta (ν : ℝ) {a b c : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ν * (c ^ 2 - c * (a + 2 * b) - 3 * b * (a + b)) = -(ν * (c + 2 * a + b) * (c + b - a)) := by
  linear_combination 2 * ν * hc2

/-! ## Core: given integers s = ν(2a+b) > 0 and z = νc > 0, derive False -/

private lemma f3_core
    {N : ℕ} (h3 : ¬ (3 : ℤ) ∣ (N : ℤ))
    {a b c ν : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hNreal : (N : ℝ) = 3 * ν ^ 2 * (a + b) * (a + 2 * b))
    (s : ℤ) (hs_pos : 0 < s) (hs_R : (s : ℝ) = ν * (2 * a + b))
    (z : ℤ) (hz_pos : 0 < z) (hz_R : (z : ℝ) = ν * c) : False := by
  -- Establish the key ℝ identities for the two factors
  have hA_R : (N : ℝ) + 3 * (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2 =
      6 * ν ^ 2 * (a + b) * (2 * a + b) := by
    rw [hs_R, hz_R, hNreal]; linear_combination -3 * ν ^ 2 * hc2
  have hB_R : (N : ℝ) + (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2 =
      2 * ν ^ 2 * (2 * a + b) * (a + 2 * b) := by
    rw [hs_R, hz_R, hNreal]; linear_combination -3 * ν ^ 2 * hc2
  -- The ℝ identity: N·4s² = (N+3s²−3z²)·(N+s²−3z²)
  have hR_eq : (N : ℝ) * 4 * (s : ℝ) ^ 2 =
      ((N : ℝ) + 3 * (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2) *
      ((N : ℝ) + (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2) := by
    rw [hA_R, hB_R, hNreal, hs_R]; ring
  -- Cast to ℤ
  have hZ_eq : (N : ℤ) * 4 * s ^ 2 =
      ((N : ℤ) + 3 * s ^ 2 - 3 * z ^ 2) * ((N : ℤ) + s ^ 2 - 3 * z ^ 2) := by
    have hRZ : ((N : ℤ) : ℝ) * 4 * (s : ℝ) ^ 2 =
        (((N : ℤ) : ℝ) + 3 * (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2) *
        (((N : ℤ) : ℝ) + (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2) := by
      push_cast; exact hR_eq
    exact_mod_cast hRZ
  -- Define M = N+2s²−3z², show M² = s²(s²+4N)
  set M : ℤ := (N : ℤ) + 2 * s ^ 2 - 3 * z ^ 2 with hM_def
  have hM_sq : M ^ 2 = s ^ 2 * (s ^ 2 + 4 * (N : ℤ)) := by linear_combination -hZ_eq
  -- s | M (from s² | M²)
  have hs_dvd : s ∣ M := by
    have hsq_dvd : s ^ 2 ∣ M ^ 2 := ⟨s ^ 2 + 4 * (N : ℤ), by linarith [hM_sq]⟩
    exact (IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).mp hsq_dvd
  -- Set m = M/s, derive m² = s²+4N
  obtain ⟨m, hm⟩ := hs_dvd   -- M = s * m
  have hm_sq : m ^ 2 = s ^ 2 + 4 * (N : ℤ) := by
    have : s ^ 2 * m ^ 2 = s ^ 2 * (s ^ 2 + 4 * (N : ℤ)) :=
      calc s ^ 2 * m ^ 2 = (s * m) ^ 2 := by ring
        _ = M ^ 2 := by rw [← hm]
        _ = s ^ 2 * (s ^ 2 + 4 * (N : ℤ)) := hM_sq
    exact Int.eq_of_mul_eq_mul_left (pow_ne_zero _ hs_pos.ne') this
  -- Set k = m − 2s; compute k·s = N − 3z²
  set k : ℤ := m - 2 * s
  have hks : k * s = (N : ℤ) - 3 * z ^ 2 := by
    have h1 : s * m = M := hm.symm ▸ rfl
    have h2 : M = (N : ℤ) + 2 * s ^ 2 - 3 * z ^ 2 := hM_def
    have h3 : m * s = (N : ℤ) + 2 * s ^ 2 - 3 * z ^ 2 := by linarith [mul_comm s m, h1, h2]
    nlinarith [h3]
  -- k² = 3(4z²−s²) via k² = m² − 4ms + 4s² = (s²+4N) − 4(N−3z²+2s²) + 4s²
  have hm_s : m * s = (N : ℤ) - 3 * z ^ 2 + 2 * s ^ 2 := by nlinarith [hks]
  have hk_sq : k ^ 2 = 3 * (4 * z ^ 2 - s ^ 2) := by nlinarith [hm_sq, hm_s]
  -- 4z² > s² (from ν²(2a+b)² < ν²·4c² under hc2)
  have h4z2s2_nn : 0 ≤ 4 * z ^ 2 - s ^ 2 := by
    have hineq : (s : ℝ) ^ 2 < 4 * (z : ℝ) ^ 2 := by
      rw [hs_R, hz_R]
      have : (2 * a + b) ^ 2 < 4 * c ^ 2 := by nlinarith [hc2, mul_pos ha hb]
      nlinarith [sq_pos_of_pos hν]
    have hZ : (s : ℤ) ^ 2 < 4 * z ^ 2 := by exact_mod_cast hineq
    linarith
  -- 3 | k (from 3 | k²)
  have h3_dvd_k_sq : (3 : ℤ) ∣ k ^ 2 := ⟨4 * z ^ 2 - s ^ 2, by linarith [hk_sq]⟩
  have h3_dvd_k : (3 : ℤ) ∣ k :=
    (by norm_num : Prime (3 : ℤ)).dvd_of_dvd_pow h3_dvd_k_sq
  obtain ⟨j, hj⟩ := h3_dvd_k   -- k = 3j
  have hmk : m = 3 * j + 2 * s := by simp only [k] at hj; linarith
  have h3N : (3 : ℤ) ∣ 4 * (N : ℤ) := ⟨3 * j ^ 2 + 4 * j * s + s ^ 2, by
    rw [hmk] at hm_sq; nlinarith [hm_sq]⟩
  exact h3 (by omega)

/-! ## Main theorem -/

/-- No prime `N > 3` admits a `CongruentDissection` with a 2π/3 model and an F3Data target. -/
theorem f3_prime_contradiction {N : ℕ} (D : CongruentDissection N)
    {α a b c ν : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : D.target.F3Data α a b c ν)
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (h3 : ¬ (3 : ℤ) ∣ (N : ℤ)) : False := by
  obtain ⟨-, hc0, -, -⟩ := cos_alpha_of_TwoPiThree D.model hm
  have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := c_sq D.model hm
  have hcpos : 0 < c := hc0
  -- Area formula
  have hNreal : (N : ℝ) = 3 * ν ^ 2 * (a + b) * (a + 2 * b) :=
    F3_area_formula D hm ht ha hb hν
  -- cor_int gives Mα, Mβ with flux equations
  obtain ⟨Mα, Mβ, hpar_α, hpar_β, hflux_α, hflux_β⟩ := Paper.cor_int D hα hm
  -- lemmaW_F3 gives the explicit flux values (two sign choices each)
  have hW_α := Row8.lemmaW_F3_alpha D.target hα ht
  have hW_β := Row8.lemmaW_F3_beta D.target hα ht
  -- Factor identities under hc2
  have hfact_α := F3_factor_alpha ν hc2
  have hfact_β := F3_factor_beta ν hc2
  -- Divisor positivity
  have hdiv_α : 0 < c + a - b := divisor_alpha_pos hc2 ha hb hcpos
  have hdiv_β : 0 < c + b - a := divisor_beta_pos hc2 ha hb hcpos
  -- Mα + Mβ and Mβ − Mα are both even
  have hsum_even : (2 : ℤ) ∣ Mα + Mβ := by omega
  have hdiff_even : (2 : ℤ) ∣ Mβ - Mα := by omega
  -- Handle all 4 sign combinations
  -- In each case: derive hMα_val and hMβ_val, extract s = ν(2a+b) and z = νc from
  -- the sum/difference of Mα, Mβ, then apply f3_core.
  rcases hW_α with hα_pos | hα_neg <;> rcases hW_β with hβ_pos | hβ_neg
  · -- (++): Mα*(c+a-b) = ν*(c-2a-b)*(c+a-b), Mβ*(c+b-a) = -ν*(c+2a+b)*(c+b-a)
    have hMα_R : (Mα : ℝ) * (c + a - b) = ν * (-(c ^ 2) - c * (a + 2 * b) + 3 * b * (a + b)) :=
      hflux_α.symm.trans hα_pos
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = ν * (c ^ 2 - c * (a + 2 * b) - 3 * b * (a + b)) :=
      hflux_β.symm.trans hβ_pos
    have hMα_val : (Mα : ℝ) = ν * (c - 2 * a - b) :=
      mul_right_cancel₀ hdiv_α.ne' (hMα_R.trans hfact_α)
    have hMβ_val : (Mβ : ℝ) = -(ν * (c + 2 * a + b)) :=
      mul_right_cancel₀ hdiv_β.ne' (by linear_combination hMβ_R.trans hfact_β)
    -- 2ν(2a+b) = -(Mα+Mβ); 2νc = -(Mβ-Mα)
    have h2s : 2 * (ν * (2 * a + b)) = -((Mα : ℝ) + Mβ) := by rw [hMα_val, hMβ_val]; ring
    have h2z : 2 * (ν * c) = -((Mβ : ℝ) - Mα) := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨p, hp⟩ := hsum_even
    obtain ⟨q, hq⟩ := hdiff_even
    have hs_R : (-p : ℝ) = ν * (2 * a + b) := by
      have : (Mα + Mβ : ℝ) = 2 * p := by exact_mod_cast hp
      linarith [h2s]
    have hz_R : (-q : ℝ) = ν * c := by
      have : (Mβ - Mα : ℝ) = 2 * q := by exact_mod_cast hq
      linarith [h2z]
    have hs_pos : 0 < -p := by
      exact_mod_cast (show (0 : ℝ) < -p by rw [hs_R]; exact mul_pos hν (by linarith))
    have hz_pos : 0 < -q := by
      exact_mod_cast (show (0 : ℝ) < -q by rw [hz_R]; exact mul_pos hν hcpos)
    exact f3_core h3 ha hb hν hc2 hNreal (-p) hs_pos (by exact_mod_cast hs_R)
      (-q) hz_pos (by exact_mod_cast hz_R)
  · -- (+-): Mα = ν(c-2a-b), Mβ = ν(c+2a+b)
    have hMα_R : (Mα : ℝ) * (c + a - b) = ν * (-(c ^ 2) - c * (a + 2 * b) + 3 * b * (a + b)) :=
      hflux_α.symm.trans hα_pos
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = -(ν * (c ^ 2 - c * (a + 2 * b) - 3 * b * (a + b))) :=
      hflux_β.symm.trans hβ_neg
    have hMα_val : (Mα : ℝ) = ν * (c - 2 * a - b) :=
      mul_right_cancel₀ hdiv_α.ne' (hMα_R.trans hfact_α)
    have hMβ_val : (Mβ : ℝ) = ν * (c + 2 * a + b) :=
      mul_right_cancel₀ hdiv_β.ne' (hMβ_R.trans (by linear_combination -hfact_β))
    -- 2ν(2a+b) = Mβ-Mα; 2νc = Mα+Mβ
    have h2s : 2 * (ν * (2 * a + b)) = (Mβ : ℝ) - Mα := by rw [hMα_val, hMβ_val]; ring
    have h2z : 2 * (ν * c) = (Mα : ℝ) + Mβ := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨q, hq⟩ := hdiff_even
    obtain ⟨p, hp⟩ := hsum_even
    have hs_R : (q : ℝ) = ν * (2 * a + b) := by
      have : (Mβ - Mα : ℝ) = 2 * q := by exact_mod_cast hq
      linarith [h2s]
    have hz_R : (p : ℝ) = ν * c := by
      have : (Mα + Mβ : ℝ) = 2 * p := by exact_mod_cast hp
      linarith [h2z]
    have hs_pos : 0 < q := by
      exact_mod_cast (show (0 : ℝ) < q by rw [hs_R]; exact mul_pos hν (by linarith))
    have hz_pos : 0 < p := by
      exact_mod_cast (show (0 : ℝ) < p by rw [hz_R]; exact mul_pos hν hcpos)
    exact f3_core h3 ha hb hν hc2 hNreal q hs_pos (by exact_mod_cast hs_R)
      p hz_pos (by exact_mod_cast hz_R)
  · -- (-+): Mα = -ν(c-2a-b), Mβ = -ν(c+2a+b)
    have hMα_R : (Mα : ℝ) * (c + a - b) = -(ν * (-(c ^ 2) - c * (a + 2 * b) + 3 * b * (a + b))) :=
      hflux_α.symm.trans hα_neg
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = ν * (c ^ 2 - c * (a + 2 * b) - 3 * b * (a + b)) :=
      hflux_β.symm.trans hβ_pos
    have hMα_val : (Mα : ℝ) = -(ν * (c - 2 * a - b)) :=
      mul_right_cancel₀ hdiv_α.ne' (hMα_R.trans (by linear_combination -hfact_α))
    have hMβ_val : (Mβ : ℝ) = -(ν * (c + 2 * a + b)) :=
      mul_right_cancel₀ hdiv_β.ne' (by linear_combination hMβ_R.trans hfact_β)
    -- 2ν(2a+b) = -(Mβ-Mα); 2νc = -(Mα+Mβ)
    have h2s : 2 * (ν * (2 * a + b)) = -((Mβ : ℝ) - Mα) := by rw [hMα_val, hMβ_val]; ring
    have h2z : 2 * (ν * c) = -((Mα : ℝ) + Mβ) := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨q, hq⟩ := hdiff_even
    obtain ⟨p, hp⟩ := hsum_even
    have hs_R : (-q : ℝ) = ν * (2 * a + b) := by
      have : (Mβ - Mα : ℝ) = 2 * q := by exact_mod_cast hq
      linarith [h2s]
    have hz_R : (-p : ℝ) = ν * c := by
      have : (Mα + Mβ : ℝ) = 2 * p := by exact_mod_cast hp
      linarith [h2z]
    have hs_pos : 0 < -q := by
      exact_mod_cast (show (0 : ℝ) < -q by rw [hs_R]; exact mul_pos hν (by linarith))
    have hz_pos : 0 < -p := by
      exact_mod_cast (show (0 : ℝ) < -p by rw [hz_R]; exact mul_pos hν hcpos)
    exact f3_core h3 ha hb hν hc2 hNreal (-q) hs_pos (by exact_mod_cast hs_R)
      (-p) hz_pos (by exact_mod_cast hz_R)
  · -- (--): Mα = -ν(c-2a-b), Mβ = ν(c+2a+b)
    have hMα_R : (Mα : ℝ) * (c + a - b) = -(ν * (-(c ^ 2) - c * (a + 2 * b) + 3 * b * (a + b))) :=
      hflux_α.symm.trans hα_neg
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = -(ν * (c ^ 2 - c * (a + 2 * b) - 3 * b * (a + b))) :=
      hflux_β.symm.trans hβ_neg
    have hMα_val : (Mα : ℝ) = -(ν * (c - 2 * a - b)) :=
      mul_right_cancel₀ hdiv_α.ne' (hMα_R.trans (by linear_combination -hfact_α))
    have hMβ_val : (Mβ : ℝ) = ν * (c + 2 * a + b) :=
      mul_right_cancel₀ hdiv_β.ne' (hMβ_R.trans (by linear_combination -hfact_β))
    -- 2ν(2a+b) = Mα+Mβ; 2νc = Mβ-Mα
    have h2s : 2 * (ν * (2 * a + b)) = (Mα : ℝ) + Mβ := by rw [hMα_val, hMβ_val]; ring
    have h2z : 2 * (ν * c) = (Mβ : ℝ) - Mα := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨p, hp⟩ := hsum_even
    obtain ⟨q, hq⟩ := hdiff_even
    have hs_R : (p : ℝ) = ν * (2 * a + b) := by
      have : (Mα + Mβ : ℝ) = 2 * p := by exact_mod_cast hp
      linarith [h2s]
    have hz_R : (q : ℝ) = ν * c := by
      have : (Mβ - Mα : ℝ) = 2 * q := by exact_mod_cast hq
      linarith [h2z]
    have hs_pos : 0 < p := by
      exact_mod_cast (show (0 : ℝ) < p by rw [hs_R]; exact mul_pos hν (by linarith))
    have hz_pos : 0 < q := by
      exact_mod_cast (show (0 : ℝ) < q by rw [hz_R]; exact mul_pos hν hcpos)
    exact f3_core h3 ha hb hν hc2 hNreal p hs_pos (by exact_mod_cast hs_R)
      q hz_pos (by exact_mod_cast hz_R)


end Erdos634.Draft.R8Gen.F3


namespace Erdos634.Draft.R8Gen.F3Prime

open Erdos634.Geometry
open Erdos634.Row8Arith
open Erdos634.Draft.R8F3PrimeAreaFormula (F3prime_area_formula)

/-! ## Auxiliary -/

private lemma c_sq (T : Tri) {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
  obtain ⟨σ, -, ha, -, hb, hγ, hc⟩ := h
  have hl := T.lawCos_perm σ
  rw [ha, hb, hc, hγ,
      show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three] at hl
  linarith

-- F3′ factor identities (a↔b of F3)
private lemma F3prime_factor_alpha (ν : ℝ) {a b c : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ν * (c ^ 2 - c * (2 * a + b) - 3 * a * (a + b)) = -(ν * (c + a + 2 * b) * (c + a - b)) := by
  linear_combination 2 * ν * hc2

private lemma F3prime_factor_beta (ν : ℝ) {a b c : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ν * (-(c ^ 2) - c * (2 * a + b) + 3 * a * (a + b)) = ν * (c - a - 2 * b) * (c + b - a) := by
  linear_combination -2 * ν * hc2

/-! ## Core: given integers s = ν(a+2b) > 0 and z = νc > 0, derive False -/

private lemma f3prime_core
    {N : ℕ} (h3 : ¬ (3 : ℤ) ∣ (N : ℤ))
    {a b c ν : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν) (hcpos : 0 < c)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hNreal : (N : ℝ) = 3 * ν ^ 2 * (a + b) * (2 * a + b))
    (s : ℤ) (hs_pos : 0 < s) (hs_R : (s : ℝ) = ν * (a + 2 * b))
    (z : ℤ) (hz_pos : 0 < z) (hz_R : (z : ℝ) = ν * c) : False := by
  have hA_R : (N : ℝ) + 3 * (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2 =
      6 * ν ^ 2 * (a + b) * (a + 2 * b) := by
    rw [hs_R, hz_R, hNreal]; linear_combination -3 * ν ^ 2 * hc2
  have hB_R : (N : ℝ) + (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2 =
      2 * ν ^ 2 * (2 * a + b) * (a + 2 * b) := by
    rw [hs_R, hz_R, hNreal]; linear_combination -3 * ν ^ 2 * hc2
  have hR_eq : (N : ℝ) * 4 * (s : ℝ) ^ 2 =
      ((N : ℝ) + 3 * (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2) *
      ((N : ℝ) + (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2) := by
    rw [hA_R, hB_R, hNreal, hs_R]; ring
  have hZ_eq : (N : ℤ) * 4 * s ^ 2 =
      ((N : ℤ) + 3 * s ^ 2 - 3 * z ^ 2) * ((N : ℤ) + s ^ 2 - 3 * z ^ 2) := by
    have hRZ : ((N : ℤ) : ℝ) * 4 * (s : ℝ) ^ 2 =
        (((N : ℤ) : ℝ) + 3 * (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2) *
        (((N : ℤ) : ℝ) + (s : ℝ) ^ 2 - 3 * (z : ℝ) ^ 2) := by
      push_cast; exact hR_eq
    exact_mod_cast hRZ
  set M : ℤ := (N : ℤ) + 2 * s ^ 2 - 3 * z ^ 2 with hM_def
  have hM_sq : M ^ 2 = s ^ 2 * (s ^ 2 + 4 * (N : ℤ)) := by linear_combination -hZ_eq
  have hs_dvd : s ∣ M := by
    have hsq_dvd : s ^ 2 ∣ M ^ 2 := ⟨s ^ 2 + 4 * (N : ℤ), by linarith [hM_sq]⟩
    exact (IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).mp hsq_dvd
  obtain ⟨m, hm⟩ := hs_dvd
  have hm_sq : m ^ 2 = s ^ 2 + 4 * (N : ℤ) := by
    have : s ^ 2 * m ^ 2 = s ^ 2 * (s ^ 2 + 4 * (N : ℤ)) :=
      calc s ^ 2 * m ^ 2 = (s * m) ^ 2 := by ring
        _ = M ^ 2 := by rw [← hm]
        _ = s ^ 2 * (s ^ 2 + 4 * (N : ℤ)) := hM_sq
    exact Int.eq_of_mul_eq_mul_left (pow_ne_zero _ hs_pos.ne') this
  set k : ℤ := m - 2 * s
  have hks : k * s = (N : ℤ) - 3 * z ^ 2 := by
    have h1 : s * m = M := hm.symm ▸ rfl
    have h2 : M = (N : ℤ) + 2 * s ^ 2 - 3 * z ^ 2 := hM_def
    have h3 : m * s = (N : ℤ) + 2 * s ^ 2 - 3 * z ^ 2 := by linarith [mul_comm s m, h1, h2]
    nlinarith [h3]
  have hm_s : m * s = (N : ℤ) - 3 * z ^ 2 + 2 * s ^ 2 := by nlinarith [hks]
  have hk_sq : k ^ 2 = 3 * (4 * z ^ 2 - s ^ 2) := by nlinarith [hm_sq, hm_s]
  have h4z2s2_nn : 0 ≤ 4 * z ^ 2 - s ^ 2 := by
    have hineq : (s : ℝ) ^ 2 < 4 * (z : ℝ) ^ 2 := by
      rw [hs_R, hz_R]
      have : (a + 2 * b) ^ 2 < 4 * c ^ 2 := by nlinarith [hc2, sq_pos_of_pos ha]
      nlinarith [sq_pos_of_pos hν]
    have hZ : (s : ℤ) ^ 2 < 4 * z ^ 2 := by exact_mod_cast hineq
    linarith
  have h3_dvd_k_sq : (3 : ℤ) ∣ k ^ 2 := ⟨4 * z ^ 2 - s ^ 2, by linarith [hk_sq]⟩
  have h3_dvd_k : (3 : ℤ) ∣ k :=
    (by norm_num : Prime (3 : ℤ)).dvd_of_dvd_pow h3_dvd_k_sq
  obtain ⟨j, hj⟩ := h3_dvd_k   -- k = 3j
  have hmk : m = 3 * j + 2 * s := by simp only [k] at hj; linarith
  have h3N : (3 : ℤ) ∣ 4 * (N : ℤ) := ⟨3 * j ^ 2 + 4 * j * s + s ^ 2, by
    rw [hmk] at hm_sq; nlinarith [hm_sq]⟩
  exact h3 (by omega)

/-! ## Main theorem -/

/-- No prime `N > 3` admits a `CongruentDissection` with a 2π/3 model and an F3PrimeData target. -/
theorem f3prime_contradiction {N : ℕ} (D : CongruentDissection N)
    {α a b c ν : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : D.target.F3PrimeData α a b c ν)
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (h3 : ¬ (3 : ℤ) ∣ (N : ℤ)) : False := by
  obtain ⟨-, hc0, -, -⟩ := cos_alpha_of_TwoPiThree D.model hm
  have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := c_sq D.model hm
  have hcpos : 0 < c := hc0
  have hNreal : (N : ℝ) = 3 * ν ^ 2 * (a + b) * (2 * a + b) :=
    F3prime_area_formula D hm ht ha hb hν
  obtain ⟨Mα, Mβ, hpar_α, hpar_β, hflux_α, hflux_β⟩ := Paper.cor_int D hα hm
  have hW_α := Row8.lemmaW_F3prime_alpha D.target hα ht
  have hW_β := Row8.lemmaW_F3prime_beta D.target hα ht
  have hfact_α := F3prime_factor_alpha ν hc2
  have hfact_β := F3prime_factor_beta ν hc2
  -- Divisors: α-divisor = (c+a-b), β-divisor = (c+b-a)
  have hdiv_α : 0 < c + a - b := divisor_alpha_pos hc2 ha hb hcpos
  have hdiv_β : 0 < c + b - a := divisor_beta_pos hc2 ha hb hcpos
  have hsum_even : (2 : ℤ) ∣ Mα + Mβ := by omega
  have hdiff_even : (2 : ℤ) ∣ Mβ - Mα := by omega
  rcases hW_α with hα_pos | hα_neg <;> rcases hW_β with hβ_pos | hβ_neg
  · -- (++): Mα = -(ν*(c+a+2b)), Mβ = ν*(c-a-2b)
    have hMα_R : (Mα : ℝ) * (c + a - b) = ν * (c ^ 2 - c * (2 * a + b) - 3 * a * (a + b)) :=
      hflux_α.symm.trans hα_pos
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = ν * (-(c ^ 2) - c * (2 * a + b) + 3 * a * (a + b)) :=
      hflux_β.symm.trans hβ_pos
    have hMα_val : (Mα : ℝ) = -(ν * (c + a + 2 * b)) :=
      mul_right_cancel₀ hdiv_α.ne' (by linear_combination hMα_R.trans hfact_α)
    have hMβ_val : (Mβ : ℝ) = ν * (c - a - 2 * b) :=
      mul_right_cancel₀ hdiv_β.ne' (hMβ_R.trans hfact_β)
    -- 2ν(a+2b) = -(Mα+Mβ); 2νc = Mβ-Mα
    have h2s : 2 * (ν * (a + 2 * b)) = -((Mα : ℝ) + Mβ) := by rw [hMα_val, hMβ_val]; ring
    have h2z : 2 * (ν * c) = (Mβ : ℝ) - Mα := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨p, hp⟩ := hsum_even
    obtain ⟨q, hq⟩ := hdiff_even
    have hs_R : (-p : ℝ) = ν * (a + 2 * b) := by
      have : (Mα + Mβ : ℝ) = 2 * p := by exact_mod_cast hp
      linarith [h2s]
    have hz_R : (q : ℝ) = ν * c := by
      have : (Mβ - Mα : ℝ) = 2 * q := by exact_mod_cast hq
      linarith [h2z]
    have hs_pos : 0 < -p := by
      exact_mod_cast (show (0 : ℝ) < -p by rw [hs_R]; exact mul_pos hν (by linarith))
    have hz_pos : 0 < q := by
      exact_mod_cast (show (0 : ℝ) < q by rw [hz_R]; exact mul_pos hν hcpos)
    exact f3prime_core h3 ha hb hν hcpos hc2 hNreal (-p) hs_pos (by exact_mod_cast hs_R)
      q hz_pos (by exact_mod_cast hz_R)
  · -- (+-): Mα = -(ν*(c+a+2b)), Mβ = -(ν*(c-a-2b))
    have hMα_R : (Mα : ℝ) * (c + a - b) = ν * (c ^ 2 - c * (2 * a + b) - 3 * a * (a + b)) :=
      hflux_α.symm.trans hα_pos
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = -(ν * (-(c ^ 2) - c * (2 * a + b) + 3 * a * (a + b))) :=
      hflux_β.symm.trans hβ_neg
    have hMα_val : (Mα : ℝ) = -(ν * (c + a + 2 * b)) :=
      mul_right_cancel₀ hdiv_α.ne' (by linear_combination hMα_R.trans hfact_α)
    have hMβ_val : (Mβ : ℝ) = -(ν * (c - a - 2 * b)) :=
      mul_right_cancel₀ hdiv_β.ne' (hMβ_R.trans (by linear_combination -hfact_β))
    -- 2ν(a+2b) = Mβ-Mα; 2νc = -(Mα+Mβ)
    have h2s : 2 * (ν * (a + 2 * b)) = (Mβ : ℝ) - Mα := by rw [hMα_val, hMβ_val]; ring
    have h2z : 2 * (ν * c) = -((Mα : ℝ) + Mβ) := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨q, hq⟩ := hdiff_even
    obtain ⟨p, hp⟩ := hsum_even
    have hs_R : (q : ℝ) = ν * (a + 2 * b) := by
      have : (Mβ - Mα : ℝ) = 2 * q := by exact_mod_cast hq
      linarith [h2s]
    have hz_R : (-p : ℝ) = ν * c := by
      have : (Mα + Mβ : ℝ) = 2 * p := by exact_mod_cast hp
      linarith [h2z]
    have hs_pos : 0 < q := by
      exact_mod_cast (show (0 : ℝ) < q by rw [hs_R]; exact mul_pos hν (by linarith))
    have hz_pos : 0 < -p := by
      exact_mod_cast (show (0 : ℝ) < -p by rw [hz_R]; exact mul_pos hν hcpos)
    exact f3prime_core h3 ha hb hν hcpos hc2 hNreal q hs_pos (by exact_mod_cast hs_R)
      (-p) hz_pos (by exact_mod_cast hz_R)
  · -- (-+): Mα = ν*(c+a+2b), Mβ = ν*(c-a-2b)
    have hMα_R : (Mα : ℝ) * (c + a - b) = -(ν * (c ^ 2 - c * (2 * a + b) - 3 * a * (a + b))) :=
      hflux_α.symm.trans hα_neg
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = ν * (-(c ^ 2) - c * (2 * a + b) + 3 * a * (a + b)) :=
      hflux_β.symm.trans hβ_pos
    have hMα_val : (Mα : ℝ) = ν * (c + a + 2 * b) :=
      mul_right_cancel₀ hdiv_α.ne' (hMα_R.trans (by linear_combination -hfact_α))
    have hMβ_val : (Mβ : ℝ) = ν * (c - a - 2 * b) :=
      mul_right_cancel₀ hdiv_β.ne' (hMβ_R.trans hfact_β)
    -- 2ν(a+2b) = -(Mβ-Mα); 2νc = Mα+Mβ
    have h2s : 2 * (ν * (a + 2 * b)) = -((Mβ : ℝ) - Mα) := by rw [hMα_val, hMβ_val]; ring
    have h2z : 2 * (ν * c) = (Mα : ℝ) + Mβ := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨q, hq⟩ := hdiff_even
    obtain ⟨p, hp⟩ := hsum_even
    have hs_R : (-q : ℝ) = ν * (a + 2 * b) := by
      have : (Mβ - Mα : ℝ) = 2 * q := by exact_mod_cast hq
      linarith [h2s]
    have hz_R : (p : ℝ) = ν * c := by
      have : (Mα + Mβ : ℝ) = 2 * p := by exact_mod_cast hp
      linarith [h2z]
    have hs_pos : 0 < -q := by
      exact_mod_cast (show (0 : ℝ) < -q by rw [hs_R]; exact mul_pos hν (by linarith))
    have hz_pos : 0 < p := by
      exact_mod_cast (show (0 : ℝ) < p by rw [hz_R]; exact mul_pos hν hcpos)
    exact f3prime_core h3 ha hb hν hcpos hc2 hNreal (-q) hs_pos (by exact_mod_cast hs_R)
      p hz_pos (by exact_mod_cast hz_R)
  · -- (--): Mα = ν*(c+a+2b), Mβ = -(ν*(c-a-2b))
    have hMα_R : (Mα : ℝ) * (c + a - b) = -(ν * (c ^ 2 - c * (2 * a + b) - 3 * a * (a + b))) :=
      hflux_α.symm.trans hα_neg
    have hMβ_R : (Mβ : ℝ) * (c + b - a) = -(ν * (-(c ^ 2) - c * (2 * a + b) + 3 * a * (a + b))) :=
      hflux_β.symm.trans hβ_neg
    have hMα_val : (Mα : ℝ) = ν * (c + a + 2 * b) :=
      mul_right_cancel₀ hdiv_α.ne' (hMα_R.trans (by linear_combination -hfact_α))
    have hMβ_val : (Mβ : ℝ) = -(ν * (c - a - 2 * b)) :=
      mul_right_cancel₀ hdiv_β.ne' (hMβ_R.trans (by linear_combination -hfact_β))
    -- 2ν(a+2b) = Mα+Mβ; 2νc = -(Mβ-Mα)
    have h2s : 2 * (ν * (a + 2 * b)) = (Mα : ℝ) + Mβ := by rw [hMα_val, hMβ_val]; ring
    have h2z : 2 * (ν * c) = -((Mβ : ℝ) - Mα) := by rw [hMα_val, hMβ_val]; ring
    obtain ⟨p, hp⟩ := hsum_even
    obtain ⟨q, hq⟩ := hdiff_even
    have hs_R : (p : ℝ) = ν * (a + 2 * b) := by
      have : (Mα + Mβ : ℝ) = 2 * p := by exact_mod_cast hp
      linarith [h2s]
    have hz_R : (-q : ℝ) = ν * c := by
      have : (Mβ - Mα : ℝ) = 2 * q := by exact_mod_cast hq
      linarith [h2z]
    have hs_pos : 0 < p := by
      exact_mod_cast (show (0 : ℝ) < p by rw [hs_R]; exact mul_pos hν (by linarith))
    have hz_pos : 0 < -q := by
      exact_mod_cast (show (0 : ℝ) < -q by rw [hz_R]; exact mul_pos hν hcpos)
    exact f3prime_core h3 ha hb hν hcpos hc2 hNreal p hs_pos (by exact_mod_cast hs_R)
      (-q) hz_pos (by exact_mod_cast hz_R)


end Erdos634.Draft.R8Gen.F3Prime



namespace Erdos634.Draft.R8Gen.F4

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
    {N : ℕ} (hF4 : NoF4 N)
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
  exact hF4 xa.toNat hxa_nat_pos y_q hy_pos hNq

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
    (hF4 : NoF4 N) : False := by
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
    exact f4_core hF4 ha hb hν hc2 hNreal d hd_pos hxa_R s hxc_R
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
    exact f4_core hF4 ha hb hν hc2 hNreal (-s) hms_pos (by exact_mod_cast hxa_R) (-d)
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
    exact f4_core hF4 ha hb hν hc2 hNreal s hs_pos (by exact_mod_cast hxa_R) d
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
    exact f4_core hF4 ha hb hν hc2 hNreal (-d) hmd_pos (by exact_mod_cast hxa_R) (-s)
      (by exact_mod_cast hxc_R)


end Erdos634.Draft.R8Gen.F4



namespace Erdos634.Draft.R8Gen.F4Prime

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
    {N : ℕ} (hF4 : NoF4 N)
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
  exact hF4 yb.toNat hyb_nat_pos y_q hy_pos hNq

/-! ## Main theorem -/

/-- No prime `N > 2` admits a `CongruentDissection` with a 2π/3 model and an F4PrimeData target. -/
theorem f4prime_prime_contradiction {N : ℕ} (D : CongruentDissection N)
    {α a b c ν : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hm : D.model.TwoPiThreeData α a b c)
    (ht : D.target.F4PrimeData α a b c ν)
    (ha : 0 < a) (hb : 0 < b) (hν : 0 < ν)
    (hF4 : NoF4 N) : False := by
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
    exact f4prime_core hF4 ha hb hν hc2 hNreal d hd_pos hyb_R (-s) (by exact_mod_cast hzc_R)
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
    exact f4prime_core hF4 ha hb hν hc2 hNreal (-s) hms_pos (by exact_mod_cast hyb_R) d
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
    exact f4prime_core hF4 ha hb hν hc2 hNreal s hs_pos (by exact_mod_cast hyb_R) (-d)
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
    exact f4prime_core hF4 ha hb hν hc2 hNreal (-d) hmd_pos (by exact_mod_cast hyb_R) s
      (by exact_mod_cast hzc_R)


end Erdos634.Draft.R8Gen.F4Prime


namespace Erdos634.Draft.R8Gen

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.R8F2to4Bridge

/-- **`GapR8 N`, proved, for `¬ 3 ∣ N` and `NoF4 N`.** -/
theorem gapR8_of_arith (N : ℕ) (h3 : ¬ (3 : ℤ) ∣ (N : ℤ)) (hF4 : NoF4 N) : Chain15.GapR8 N := by
  intro D α a b c hirr hm hshape
  obtain ⟨_, _, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  rcases hshape with hF2 | hF3 | hF3' | hF4s | hF4'
  · obtain ⟨ν, hνpos, hd⟩ := f2_data_of_shape D hm hF2
    exact F2.f2_prime_contradiction D hirr hm hd ha0 hb0 hνpos h3 hF4
  · obtain ⟨ν, hνpos, hd⟩ := f3_data_of_shape D hm hF3
    exact F3.f3_prime_contradiction D hirr hm hd ha0 hb0 hνpos h3
  · obtain ⟨ν, hνpos, hd⟩ := f3prime_data_of_shape D hm hF3'
    exact F3Prime.f3prime_contradiction D hirr hm hd ha0 hb0 hνpos h3
  · obtain ⟨ν, hνpos, hd⟩ := f4_data_of_shape D hm hF4s
    exact F4.f4_prime_contradiction D hirr hm hd ha0 hb0 hνpos hF4
  · obtain ⟨ν, hνpos, hd⟩ := f4prime_data_of_shape D hm hF4'
    exact F4Prime.f4prime_prime_contradiction D hirr hm hd ha0 hb0 hνpos hF4

theorem gapR8_38 : Chain15.GapR8 38 := gapR8_of_arith 38 (by decide) noF4_38
theorem gapR8_86 : Chain15.GapR8 86 := gapR8_of_arith 86 (by decide) noF4_86

/-- N = 38 modulo THREE named hypotheses (GapR8 now proved). -/
theorem chain_thirtyeight_R8 (gA : ChainComposite.GapAcomp 38) (gB : ChainComposite.HBSimilar 38)
    (gR : ChainComposite.H1Right 38) (D : CongruentDissection 38) : False :=
  Chain38.chain_thirtyeight gA gB gR gapR8_38 D

/-- N = 86 modulo THREE named hypotheses (GapR8 now proved). -/
theorem chain_eightysix_R8 (gA : ChainComposite.GapAcomp 86) (gB : ChainComposite.HBSimilar 86)
    (gR : ChainComposite.H1Right 86) (D : CongruentDissection 86) : False :=
  Chain86.chain_eightysix gA gB gR gapR8_86 D

end Erdos634.Draft.R8Gen

#print axioms Erdos634.Draft.R8Gen.gapR8_38
#print axioms Erdos634.Draft.R8Gen.gapR8_86
#print axioms Erdos634.Draft.R8Gen.chain_thirtyeight_R8
#print axioms Erdos634.Draft.R8Gen.chain_eightysix_R8
