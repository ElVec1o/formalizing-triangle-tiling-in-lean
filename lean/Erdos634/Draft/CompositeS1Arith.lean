/-
Draft/CompositeS1Arith.lean — S1 (target (β, β, 3α), tile with `ThreeAlphaData`) at N for which the QNR route
(`ScaleBaseBetaQNR.scaleBaseBeta_qnr`: prime ℓ, odd valuation, 3 a non-residue mod ℓ) is unavailable.
`S1Closed N` is exactly the conclusion of `scaleBaseBeta_qnr` at fixed N without ℓ; `S1Arith N` is the pure-integer core
(no coprime 0 < p < q, M ≠ 0 with  N (p+q)² = M² (3q²−p²)); `s1Closed_of_arith` = copy of the `scaleBaseBeta_qnr` front
end with its last step replaced.  `s1Arith_of_twoadic`: if N·(3q²−p²) is never a square mod 32 for p, q not both even
then S1Arith N (since `N (p+q)² = M² Y` ⇒ `(MY/(p+q))² = N Y`).
Holds (decide) for N = 22, 46, 78: N = 2n', n' ≡ 3 (mod 4).  FAILS for N = 66 (n' = 33 ≡ 1 mod 4) and, much more
sharply, `S1Arith 66` is FALSE: (p, q, M) = (3, 5, 8), 66·8² = 8²·66 (this is the base-β (3,5,1) instance).
UNAUDITED.  Formalization debt, NOT /goal progress.  No sorry, no native_decide.
-/
import Erdos634.Draft.ScaleBaseBetaQNR

set_option synthInstance.maxSize 1000
set_option synthInstance.maxHeartbeats 400000

namespace Erdos634.Draft.CompositeS1Arith

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.BaseBetaTargetCoord
open Erdos634.Realizable Erdos634.Draft.TheoremPConditional

/-- **S1Closed N**: shape (β, β, 3α) (3α+2β = π, α irrational, model `ThreeAlphaData`, `a = r c`, `b = (1−r²)c`,
`r ∈ ℚ`) is impossible.  Conclusion of `ScaleBaseBetaQNR.S1QNRStatement` at fixed `N`, without ℓ. -/
def S1Closed (N : ℕ) : Prop :=
  ∀ (D : CongruentDissection N) (α β a b c : ℝ) (r : ℚ), IrrPi α → 3 * α + 2 * β = Real.pi →
    D.model.ThreeAlphaData α β a b c → a = (r : ℝ) * c → b = (1 - (r : ℝ) ^ 2) * c →
    TgtAngles D β β (3 * α) → False

/-- Pure-integer core of S1. -/
def S1Arith (N : ℕ) : Prop :=
  ∀ p q M : ℤ, 0 < p → p < q → IsCoprime p q → M ≠ 0 →
    (N : ℤ) * (p + q) ^ 2 = M ^ 2 * (3 * q ^ 2 - p ^ 2) → False

open Erdos634.Draft.ScaleBaseBetaFull in
set_option maxHeartbeats 4000000 in
theorem s1Closed_of_arith (N : ℕ) (hA : S1Arith N) : S1Closed N := by
  intro D α β a b c r hα hrel hmod har hbr htgt
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
  exact hA p_i q_i M hp_pos hp_lt_q hcop_pq hM_ne hquad_int


/-- 2-adic obstruction ⇒ `S1Arith N`. -/
theorem s1Arith_of_twoadic (N : ℕ) (hN : 0 < N)
    (h : ∀ p q w : ZMod 32, ¬ (2 ∣ p.val ∧ 2 ∣ q.val) → w ^ 2 ≠ (N : ZMod 32) * (3 * q ^ 2 - p ^ 2)) :
    S1Arith N := by
  intro p q M hp hpq hcop hM heq
  have hq0 : 0 < q := by omega
  have hY : 0 < 3 * q ^ 2 - p ^ 2 := by nlinarith
  have hs : 0 < p + q := by omega
  set Y := 3 * q ^ 2 - p ^ 2 with hYdef
  have h1 : (N : ℤ) * Y * (p + q) ^ 2 = (M * Y) ^ 2 := by
    have : (N : ℤ) * Y * (p + q) ^ 2 = Y * ((N : ℤ) * (p + q) ^ 2) := by ring
    rw [this, heq]; ring
  have hdvd : (p + q) ^ 2 ∣ (M * Y) ^ 2 := ⟨(N : ℤ) * Y, by rw [← h1]; ring⟩
  obtain ⟨w, hw⟩ := (Int.pow_dvd_pow_iff (two_ne_zero)).mp hdvd
  have hw2 : w ^ 2 = (N : ℤ) * Y := by
    have : (p + q) ^ 2 * w ^ 2 = (p + q) ^ 2 * ((N : ℤ) * Y) := by
      calc (p + q) ^ 2 * w ^ 2 = ((p + q) * w) ^ 2 := by ring
        _ = (M * Y) ^ 2 := by rw [← hw]
        _ = (p + q) ^ 2 * ((N : ℤ) * Y) := by rw [← h1]; ring
    exact mul_left_cancel₀ (pow_ne_zero 2 hs.ne') this
  have hz : ((w : ZMod 32)) ^ 2 = (N : ZMod 32) * (3 * (q : ZMod 32) ^ 2 - (p : ZMod 32) ^ 2) := by
    have := congrArg (fun z : ℤ => (z : ZMod 32)) hw2
    simpa [hYdef] using this
  have hpar : ¬ (2 ∣ (p : ZMod 32).val ∧ 2 ∣ (q : ZMod 32).val) := by
    rintro ⟨h2p, h2q⟩
    have vp := ZMod.val_intCast (n := 32) p
    have vq := ZMod.val_intCast (n := 32) q
    have hp2 : (2 : ℤ) ∣ p := by omega
    have hq2 : (2 : ℤ) ∣ q := by omega
    have hu := hcop.isUnit_of_dvd' hp2 hq2
    have := Int.isUnit_iff.mp hu
    omega
  exact h _ _ _ hpar hz

theorem s1Arith_22 : S1Arith 22 := s1Arith_of_twoadic 22 (by norm_num) (by decide +kernel)
theorem s1Arith_46 : S1Arith 46 := s1Arith_of_twoadic 46 (by norm_num) (by decide +kernel)
theorem s1Arith_78 : S1Arith 78 := s1Arith_of_twoadic 78 (by norm_num) (by decide +kernel)

/-- Negative control: the 2-adic obstruction is FALSE at 66. -/
theorem twoadic_s1_fails_66 : ¬ (∀ p q w : ZMod 32, ¬ (2 ∣ p.val ∧ 2 ∣ q.val) →
    w ^ 2 ≠ ((66 : ℕ) : ZMod 32) * (3 * q ^ 2 - p ^ 2)) := by decide +kernel

/-- Sharper negative control: `S1Arith 66` is FALSE — (p, q, M) = (3, 5, 8). -/
theorem not_s1Arith_66 : ¬ S1Arith 66 := fun h =>
  h 3 5 8 (by norm_num) (by norm_num) (by rw [Int.isCoprime_iff_gcd_eq_one]; decide) (by norm_num) (by norm_num)

theorem s1Closed_22 : S1Closed 22 := s1Closed_of_arith 22 s1Arith_22
theorem s1Closed_46 : S1Closed 46 := s1Closed_of_arith 46 s1Arith_46
theorem s1Closed_78 : S1Closed 78 := s1Closed_of_arith 78 s1Arith_78

end Erdos634.Draft.CompositeS1Arith

#print axioms Erdos634.Draft.CompositeS1Arith.s1Closed_of_arith
#print axioms Erdos634.Draft.CompositeS1Arith.s1Closed_22
#print axioms Erdos634.Draft.CompositeS1Arith.s1Closed_46
#print axioms Erdos634.Draft.CompositeS1Arith.s1Closed_78
#print axioms Erdos634.Draft.CompositeS1Arith.twoadic_s1_fails_66
#print axioms Erdos634.Draft.CompositeS1Arith.not_s1Arith_66
