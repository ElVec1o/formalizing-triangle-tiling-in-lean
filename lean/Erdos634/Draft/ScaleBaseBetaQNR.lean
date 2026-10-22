-- Draft/ScaleBaseBetaQNR.lean — S1 shape (β,β,3α) with an ODD-VALUATION / QUADRATIC-NON-RESIDUE hypothesis in
-- place of primality: if a prime ℓ divides N to an odd power and 3 is a non-residue mod ℓ (e.g. ℓ = 5, 7,
-- 17, 19, …; ℓ ≡ ±5 mod 12), the S1 configuration is impossible: N (p+q)² = M²(3q²−p²) with gcd(p,q)=1
-- gives v_ℓ(LHS) odd, v_ℓ(RHS) even.  Room ALLN / SCOPE_N15_L1 leaf S1.  Elementary parity device
-- (novelty_check: clear; not claimed as a result).  Conclusion is False (stronger than BaseBetaTiled).
-- Consistent with realizable N = 11 m² (3 is a residue mod 11).  UNAUDITED.
import Erdos634.Draft.ScaleBaseBetaFull

open scoped Classical

namespace Erdos634.Draft.ScaleBaseBetaQNR

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.BaseBetaTargetCoord
open Erdos634.Realizable Erdos634.Draft.TheoremPConditional


/-- 5-adic-type parity obstruction for `N (p+q)² = M² (3q²−p²)` (S1 shape): if a prime `ℓ` divides `N`
to an odd power and `3` is a non-residue mod `ℓ`, and `gcd(p,q)=1`, there is no solution. -/
theorem s1_no_sol {N ℓ : ℕ} (hℓ : ℓ.Prime) (hN0 : 0 < N) (hodd : Odd (padicValNat ℓ N))
    (hnr : ∀ x : ZMod ℓ, x ^ 2 ≠ 3) {p q M : ℤ} (hcop : IsCoprime p q) (hM : M ≠ 0)
    (hpq : p + q ≠ 0) (hY : 0 < 3 * q ^ 2 - p ^ 2)
    (heq : (N : ℤ) * (p + q) ^ 2 = M ^ 2 * (3 * q ^ 2 - p ^ 2)) : False := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  -- ℓ ∤ Y
  have hnd : ¬ ((ℓ : ℤ) ∣ 3 * q ^ 2 - p ^ 2) := by
    intro hd
    have h0 : ((3 * q ^ 2 - p ^ 2 : ℤ) : ZMod ℓ) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).mpr hd
    push_cast at h0
    by_cases hq : (q : ZMod ℓ) = 0
    · have hp : (p : ZMod ℓ) = 0 := by
        have : (p : ZMod ℓ) ^ 2 = 0 := by
          have : (p : ZMod ℓ) ^ 2 = 3 * (q : ZMod ℓ) ^ 2 := by linear_combination -h0
          rw [this, hq]; ring
        exact pow_eq_zero_iff (two_ne_zero) |>.mp this
      have hpd : (ℓ : ℤ) ∣ p := (ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).mp hp
      have hqd : (ℓ : ℤ) ∣ q := (ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).mp hq
      have hu : IsUnit (ℓ : ℤ) := hcop.isUnit_of_dvd' hpd hqd
      have := Int.isUnit_iff.mp hu
      have hl2 := hℓ.two_le
      omega
    · apply hnr ((p : ZMod ℓ) / q)
      field_simp
      linear_combination -h0
  -- natural-number version
  have hYn : (3 * q ^ 2 - p ^ 2).natAbs ≠ 0 := by omega
  have hnat : N * (p + q).natAbs ^ 2 = M.natAbs ^ 2 * (3 * q ^ 2 - p ^ 2).natAbs := by
    have := congrArg Int.natAbs heq
    simpa [Int.natAbs_mul, Int.natAbs_pow] using this
  have hval := congrArg (padicValNat ℓ) hnat
  have hne1 : (p + q).natAbs ≠ 0 := by omega
  have hne2 : M.natAbs ≠ 0 := by omega
  rw [padicValNat.mul (by omega) (pow_ne_zero 2 hne1), padicValNat.mul (pow_ne_zero 2 hne2) hYn,
    padicValNat.pow _ hne1, padicValNat.pow _ hne2] at hval
  have hY0 : padicValNat ℓ (3 * q ^ 2 - p ^ 2).natAbs = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro hd
    apply hnd
    exact Int.ofNat_dvd_left.mpr hd
  rw [hY0] at hval
  obtain ⟨k, hk⟩ := hodd
  omega


def S1QNRStatement : Prop :=
  ∀ (N : ℕ) (D : CongruentDissection N) (ℓ : ℕ), ℓ.Prime → Odd (padicValNat ℓ N) →
    (∀ x : ZMod ℓ, x ^ 2 ≠ 3) →
    ∀ (α β a b c : ℝ) (r : ℚ), IrrPi α → 3 * α + 2 * β = Real.pi →
      D.model.ThreeAlphaData α β a b c → a = (r : ℝ) * c → b = (1 - (r : ℝ) ^ 2) * c →
      TgtAngles D β β (3 * α) → False

open Erdos634.Draft.ScaleBaseBetaFull in
set_option maxHeartbeats 4000000 in
theorem scaleBaseBeta_qnr : S1QNRStatement := by
  intro N D ℓ hℓ hodd hnr α β a b c r hα hrel hmod har hbr htgt
  -- Step 0: relabel target so β at positions 0, 1
  obtain ⟨σ_t, ht0, ht1, _⟩ := htgt
  set D' := D.relabelTarget' σ_t
  have hD'_tgt_pts : ∀ k, D'.target.pts k = D.target.pts (σ_t k) := fun _ => rfl
  have hD'_tgt0 : D'.target.angleAt 0 = β :=
    (Row14AnyLabel.angleAt_of_pts σ_t hD'_tgt_pts 0).trans ht0
  have hD'_tgt1 : D'.target.angleAt 1 = β :=
    (Row14AnyLabel.angleAt_of_pts σ_t hD'_tgt_pts 1).trans ht1
  -- Step 1: Row12.setup (D'.model = D.model definitionally)
  obtain ⟨s, M, hs0, hs1, hc, ha_sc, hb_sc, hM2, _, hM0, _, hMleg, hYs, hquad⟩ :=
    Row12.setup D' hα hrel hmod hD'_tgt0 hD'_tgt1
  -- Step 2: s = r
  have hsr : s = (r : ℝ) := mul_right_cancel₀ hc.ne' (by rw [← ha_sc, ← har])
  -- p = r.num, q = r.den (as integers)
  set p_i := r.num
  set q_i : ℤ := (r.den : ℤ)
  have hq_pos : (0 : ℤ) < q_i := by
    show (0 : ℤ) < (r.den : ℤ); exact_mod_cast r.pos
  have hcop_pq : IsCoprime p_i q_i := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact_mod_cast r.reduced
  have hq_r : (q_i : ℝ) ≠ 0 := by exact_mod_cast hq_pos.ne'
  have hr_pq : (r : ℝ) = (p_i : ℝ) / (q_i : ℝ) := by
    have h1 : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := Rat.cast_def r
    simpa [p_i, q_i, Int.cast_natCast] using h1
  have hp_pos : (0 : ℤ) < p_i := by
    have hpR : (0 : ℝ) < (p_i : ℝ) := by
      have := hs0; rw [hsr, hr_pq] at this
      have hqR : (0 : ℝ) < (q_i : ℝ) := by exact_mod_cast hq_pos
      rcases div_pos_iff.mp this with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact h1
      · linarith
    exact_mod_cast hpR
  have hp_lt_q : p_i < q_i := by
    have := hs1; rw [hsr, hr_pq] at this
    exact_mod_cast (div_lt_one (by exact_mod_cast hq_pos)).mp this
  -- Step 3: quadratic as integers
  have hquad_int : (N : ℤ) * (p_i + q_i) ^ 2 = M ^ 2 * (3 * q_i ^ 2 - p_i ^ 2) := by
    have hkey := hquad; rw [hsr, hr_pq] at hkey
    have hkey2 : (q_i : ℝ) ^ 2 * (((N : ℝ) + (M : ℝ) ^ 2) * ((p_i : ℝ) / q_i) ^ 2 +
        2 * N * ((p_i : ℝ) / q_i) + ((N : ℝ) - 3 * (M : ℝ) ^ 2)) = 0 := by
      rw [hkey]; ring
    have hkey3 : (N : ℝ) * (p_i + q_i) ^ 2 = (M : ℝ) ^ 2 * (3 * q_i ^ 2 - p_i ^ 2) := by
      have hq2 : (q_i : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hq_r
      field_simp at hkey2 ⊢
      nlinarith [hkey2, sq_nonneg (p_i : ℝ), sq_nonneg (q_i : ℝ)]
    exact_mod_cast hkey3
  have hB_pos : (0 : ℤ) < 3 * q_i ^ 2 - p_i ^ 2 := by nlinarith [sq_nonneg p_i, sq_nonneg q_i]
  have hpq_ne : p_i + q_i ≠ 0 := by linarith [hp_pos, hq_pos]
  have hM_ne : M ≠ 0 := Int.ne_of_gt hM0
  exact s1_no_sol hℓ (by have := D.pos; omega) hodd hnr hcop_pq hM_ne hpq_ne hB_pos hquad_int

end Erdos634.Draft.ScaleBaseBetaQNR

#print axioms Erdos634.Draft.ScaleBaseBetaQNR.scaleBaseBeta_qnr

/-- N = 15: `ℓ = 5` divides 15 exactly once and 3 is a non-residue mod 5. -/
theorem qnr_five : ∀ x : ZMod 5, x ^ 2 ≠ 3 := by decide

theorem s1_excluded_fifteen : Odd (padicValNat 5 15) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : padicValNat 5 15 = 1 := by
    have h : padicValNat 5 15 = padicValNat 5 (5 * 3) := by norm_num
    rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat_self,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  rw [this]; exact odd_one
