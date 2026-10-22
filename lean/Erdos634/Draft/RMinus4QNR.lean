-- Draft/RMinus4QNR.lean — S2 shape (2α, α, 2β) (R-4) with an odd-valuation / non-residue hypothesis in place of
-- primality: if a prime ℓ divides N to an odd power and BOTH 2 and 3 are non-residues mod ℓ (ℓ ≡ ±5 mod 24
-- ... i.e. ℓ = 5, 29, 53, ...), then N R² = S²(2q²−p²)(3q²−p²) with gcd(p,q)=1 is impossible (ℓ ∤ either
-- factor, so valuations have opposite parity).  Room ALLN / SCOPE_N15_L1 leaf S2.  Elementary parity
-- device (novelty clear, not claimed as a result).  Conclusion False.  N = 15 via ℓ = 5.  UNAUDITED.
import Erdos634.Draft.RMinus4Full
import Erdos634.Draft.ScaleBaseBetaQNR

open scoped Classical

namespace Erdos634.Geometry

open Row14AnyLabel Erdos634.Draft.TheoremPConditional

/-- `ℓ` (prime) does not divide `c q² − p²` when `c` is a non-residue mod `ℓ` and `gcd(p,q) = 1`. -/
theorem not_dvd_qnr {ℓ : ℕ} (hℓ : ℓ.Prime) {c : ℤ} (hnr : ∀ x : ZMod ℓ, x ^ 2 ≠ (c : ZMod ℓ))
    {p q : ℤ} (hcop : IsCoprime p q) : ¬ ((ℓ : ℤ) ∣ c * q ^ 2 - p ^ 2) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  intro hd
  have h0 : ((c * q ^ 2 - p ^ 2 : ℤ) : ZMod ℓ) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).mpr hd
  push_cast at h0
  by_cases hq : (q : ZMod ℓ) = 0
  · have hp : (p : ZMod ℓ) = 0 := by
      have : (p : ZMod ℓ) ^ 2 = 0 := by
        have : (p : ZMod ℓ) ^ 2 = (c : ZMod ℓ) * (q : ZMod ℓ) ^ 2 := by linear_combination -h0
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

/-- Valuation-parity core: `N R² = S² Y`, `ℓ ∤ Y`, `v_ℓ(N)` odd is impossible. -/
theorem parity_core {N ℓ : ℕ} (hℓ : ℓ.Prime) (hN0 : 0 < N) (hodd : Odd (padicValNat ℓ N))
    {R S Y : ℤ} (hR : R ≠ 0) (hS : S ≠ 0) (hY : Y ≠ 0) (hnd : ¬ ((ℓ : ℤ) ∣ Y))
    (heq : (N : ℤ) * R ^ 2 = S ^ 2 * Y) : False := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hYn : Y.natAbs ≠ 0 := by omega
  have hnat : N * R.natAbs ^ 2 = S.natAbs ^ 2 * Y.natAbs := by
    have := congrArg Int.natAbs heq
    simpa [Int.natAbs_mul, Int.natAbs_pow] using this
  have hval := congrArg (padicValNat ℓ) hnat
  have hne1 : R.natAbs ≠ 0 := by omega
  have hne2 : S.natAbs ≠ 0 := by omega
  rw [padicValNat.mul (by omega) (pow_ne_zero 2 hne1), padicValNat.mul (pow_ne_zero 2 hne2) hYn,
    padicValNat.pow _ hne1, padicValNat.pow _ hne2] at hval
  have hY0 : padicValNat ℓ Y.natAbs = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro hd
    exact hnd (Int.ofNat_dvd_left.mpr hd)
  rw [hY0] at hval
  obtain ⟨k, hk⟩ := hodd
  omega

def S2QNRStatement : Prop :=
  ∀ (N : ℕ) (D : CongruentDissection N) (ℓ : ℕ), ℓ.Prime → Odd (padicValNat ℓ N) →
    (∀ x : ZMod ℓ, x ^ 2 ≠ 2) → (∀ x : ZMod ℓ, x ^ 2 ≠ 3) →
    ∀ (α β a b c : ℝ) (r : ℚ), IrrPi α → 3 * α + 2 * β = Real.pi →
      D.model.ThreeAlphaData α β a b c → a = (r : ℝ) * c → b = (1 - (r : ℝ) ^ 2) * c →
      TgtAngles D (2 * α) α (2 * β) → False

set_option maxHeartbeats 800000 in
theorem rMinus4_qnr : S2QNRStatement := by
  intro N D ℓ hℓ hodd hnr2 hnr3 α β a b c r hirr hrel hmod ha hb htgt
  -- Step 1: unpack TgtAngles to get the permutation σ placing 2α, α, 2β at 0, 1, 2
  obtain ⟨σ, hσ0, hσ1, hσ2⟩ := htgt
  -- Step 2: relabel target by σ so that target vertex k carries angle σ k
  set D' := D.relabelTarget' σ with hD'def
  have hT : ∀ k, D'.target.pts k = D.target.pts (σ k) := fun k => rfl
  -- Step 3: angle transfers via angleAt_of_pts
  have hP0 : D'.target.angleAt 0 = 2 * α := by
    rw [angleAt_of_pts σ hT 0, hσ0]
  have hP1 : D'.target.angleAt 1 = α := by
    rw [angleAt_of_pts σ hT 1, hσ1]
  have hP2 : D'.target.angleAt 2 = 2 * β := by
    rw [angleAt_of_pts σ hT 2, hσ2]
  -- Step 4: D'.model = D.model (rfl), so ThreeAlphaData transfers
  have hmod' : D'.model.ThreeAlphaData α β a b c := hmod
  -- Step 5: apply Row15.setup
  obtain ⟨s, S, hs0, hs1, hcpos, ha', _hb', _hX, _hZ, hSc, harea⟩ :=
    Row15.setup D' hirr hrel hmod' hP0 hP1 hP2
  -- Step 6: s = (r : ℝ)  (from ha' : a = s*c and ha : a = r*c and 0 < c)
  have hsr : s = (r : ℝ) := by
    have : s * c = (r : ℝ) * c := ha'.symm.trans ha
    exact mul_right_cancel₀ hcpos.ne' this
  -- Step 7: write r in lowest terms
  -- r.num and r.den are coprime natural/int
  -- Get positivity of r
  have hr_pos : 0 < (r : ℝ) := hsr ▸ hs0
  have hr_lt1 : (r : ℝ) < 1 := hsr ▸ hs1
  -- r.num > 0
  have hrnum_pos : 0 < r.num := Rat.num_pos.mpr (by exact_mod_cast hr_pos)
  -- r.den > 0
  have hrden_pos : (0 : ℤ) < r.den := by exact_mod_cast r.pos
  -- r.num < r.den: from (r:ℝ) < 1 and r = r.num / r.den
  have hrnum_lt_den : r.num < r.den := by
    have hd : (0 : ℝ) < r.den := by exact_mod_cast r.pos
    have hrcast : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by
      rw [Rat.cast_def]
    rw [hrcast, div_lt_one hd] at hr_lt1
    exact_mod_cast hr_lt1
  -- Coprimality: Rat.isCoprime_num_den gives IsCoprime r.num (r.den : ℤ)
  have hcop : IsCoprime r.num (r.den : ℤ) := Rat.isCoprime_num_den r
  -- Step 8: rewrite harea in terms of r
  -- harea : (N:ℝ) * ((1 - s) * (2 + s))^2 = (S:ℝ)^2 * ((2 - s^2) * (3 - s^2))
  -- substitute s = (r:ℝ)
  rw [hsr] at harea
  -- Step 9: lift to ℤ
  -- Set p = r.num (ℤ), q = r.den cast to ℤ
  set p : ℤ := r.num with hp_def
  set q : ℤ := (r.den : ℤ) with hq_def
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hrden_pos
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hrnum_pos
  have hrpq : (r : ℝ) = (p : ℝ) / (q : ℝ) := by
    simp [Rat.cast_def, hp_def, hq_def]
  -- Multiply harea by q^4 and rearrange
  -- LHS * q^4: N * ((1 - p/q)*(2 + p/q))^2 * q^4 = N * ((q-p)*(2q+p))^2
  -- RHS * q^4: S^2 * (2 - (p/q)^2) * (3 - (p/q)^2) * q^4 = S^2 * (2q^2 - p^2) * (3q^2 - p^2)
  have harea_int : (N : ℤ) * ((q - p) * (2 * q + p)) ^ 2 =
      S ^ 2 * (2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2) := by
    have hq4 : (q : ℝ) ^ 4 ≠ 0 := by positivity
    apply_fun (· * (q : ℝ) ^ 4) at harea
    have key : (N : ℝ) * ((q - p) * (2 * q + p)) ^ 2 =
        (S : ℝ) ^ 2 * (2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2) := by
      rw [hrpq] at harea
      field_simp at harea ⊢
      linarith
    exact_mod_cast key
  -- Step 10: apply chain_unconditional with e=p, f=q, R=(q-p)*(2q+p), M=S
  -- Need hM : S ≠ 0
  have hS_ne : S ≠ 0 := by
    intro hS0
    rw [hS0, Int.cast_zero, zero_mul] at hSc
    -- hSc : 0 = (1 - s) * (2 + s) * D'.target.oppLen 1
    -- (1-s) > 0, (2+s) > 0, oppLen > 0 → contradiction
    have h1s : 0 < 1 - s := by linarith
    have h2s : 0 < 2 + s := by linarith
    have hY : 0 < D'.target.oppLen 1 := D'.target.oppLen_pos 1
    have := mul_pos (mul_pos h1s h2s) hY
    linarith
  have hY1 : (0 : ℤ) < 2 * q ^ 2 - p ^ 2 := by nlinarith [sq_nonneg p, sq_nonneg q, hrnum_lt_den, hrnum_pos]
  have hY2 : (0 : ℤ) < 3 * q ^ 2 - p ^ 2 := by nlinarith [sq_nonneg p, sq_nonneg q, hrnum_lt_den, hrnum_pos]
  have hRne : (q - p) * (2 * q + p) ≠ 0 := by
    have h1 : (0 : ℤ) < q - p := by linarith [hrnum_lt_den]
    have h2 : (0 : ℤ) < 2 * q + p := by linarith [hrnum_pos, hrnum_lt_den]
    exact (mul_pos h1 h2).ne'
  have hnd1 : ¬ ((ℓ : ℤ) ∣ 2 * q ^ 2 - p ^ 2) :=
    not_dvd_qnr hℓ (c := 2) (by simpa using hnr2) hcop
  have hnd2 : ¬ ((ℓ : ℤ) ∣ 3 * q ^ 2 - p ^ 2) :=
    not_dvd_qnr hℓ (c := 3) (by simpa using hnr3) hcop
  have hpz : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  have hnd : ¬ ((ℓ : ℤ) ∣ (2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2)) := by
    intro h
    rcases hpz.dvd_or_dvd h with h | h
    · exact hnd1 h
    · exact hnd2 h
  exact parity_core hℓ (by have := D.pos; omega) hodd hRne hS_ne (mul_pos hY1 hY2).ne' hnd
    (by rw [harea_int]; ring)

/-- N = 15: 2 and 3 are non-residues mod 5. -/
theorem qnr_two_five : ∀ x : ZMod 5, x ^ 2 ≠ 2 := by decide

end Erdos634.Geometry

#print axioms Erdos634.Geometry.rMinus4_qnr
