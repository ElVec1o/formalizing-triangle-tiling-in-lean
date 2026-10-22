/-
Draft/CompositeS2Arith.lean — S2 (target (2α, α, 2β)) at N for which the QNR route (`RMinus4QNR.rMinus4_qnr`:
2 AND 3 non-residues mod an odd-valuation prime) is unavailable.  Reduces `S2Closed N` to the pure-integer
statement `S2Arith N`:  no coprime 0 < p < q, S ≠ 0 with  N ((q−p)(2q+p))² = S² (2q²−p²)(3q²−p²)
(this is exactly `harea_int` of `RMinus4QNR.rMinus4_qnr`; the front end is a copy of that proof).
`s2Arith_of_twoadic`: if N·(2q²−p²)(3q²−p²) is never a square mod 32 for p, q not both even, then S2Arith N.
This 2-adic obstruction holds for N = 14 and N = 62 (checked by `decide`), FAILS for N = 42 and N = 70 (counts of
bad residue pairs mod 32: 128 each), and for 42 there is no local obstruction at 2, 3, 7 either (Python scan).
UNAUDITED.  Formalization debt, NOT /goal progress.  No sorry, no native_decide.
-/
import Erdos634.Draft.CompositeGen2

open scoped Classical

set_option synthInstance.maxSize 1000
set_option synthInstance.maxHeartbeats 400000

namespace Erdos634.Draft.CompositeS2Arith

open Erdos634.Geometry Erdos634.Draft.CompositeGen2 Row14AnyLabel Erdos634.Draft.TheoremPConditional

/-- Pure-integer core of S2. -/
def S2Arith (N : ℕ) : Prop :=
  ∀ p q S : ℤ, 0 < p → p < q → IsCoprime p q → S ≠ 0 →
    (N : ℤ) * ((q - p) * (2 * q + p)) ^ 2 = S ^ 2 * (2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2) → False

set_option maxHeartbeats 800000 in
theorem s2Closed_of_arith (N : ℕ) (hA : S2Arith N) : S2Closed N := by
  intro D α β a b c r hirr hrel hmod ha hb htgt
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
  have hpq : p < q := by
    have : r.num < (r.den : ℤ) := hrnum_lt_den
    simpa [hp_def, hq_def] using this
  exact hA p q S (by simpa [hp_def] using hrnum_pos) hpq (by simpa [hp_def, hq_def] using hcop) hS_ne harea_int

/-- 2-adic obstruction ⇒ `S2Arith N`. -/
theorem s2Arith_of_twoadic (N : ℕ) (hN : 0 < N)
    (h : ∀ p q w : ZMod 32, ¬ (2 ∣ p.val ∧ 2 ∣ q.val) → w ^ 2 ≠ (N : ZMod 32) * ((2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2))) :
    S2Arith N := by
  intro p q S hp hpq hcop hS heq
  have hq0 : 0 < q := by omega
  have hA : 0 < 2 * q ^ 2 - p ^ 2 := by nlinarith
  have hB : 0 < 3 * q ^ 2 - p ^ 2 := by nlinarith
  have hR : 0 < (q - p) * (2 * q + p) := mul_pos (by omega) (by omega)
  set R := (q - p) * (2 * q + p) with hRdef
  set Y := (2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2) with hYdef
  have hY : 0 < Y := mul_pos hA hB
  have heq' : (N : ℤ) * R ^ 2 = S ^ 2 * Y := by rw [heq, hYdef]; ring
  -- `N Y R² = (S Y)²`
  have h1 : (N : ℤ) * Y * R ^ 2 = (S * Y) ^ 2 := by
    have : (N : ℤ) * Y * R ^ 2 = Y * ((N : ℤ) * R ^ 2) := by ring
    rw [this, heq']; ring
  have hdvd : R ^ 2 ∣ (S * Y) ^ 2 := ⟨(N : ℤ) * Y, by rw [← h1]; ring⟩
  obtain ⟨w, hw⟩ := (Int.pow_dvd_pow_iff (two_ne_zero)).mp hdvd
  have hw2 : w ^ 2 = (N : ℤ) * Y := by
    have : R ^ 2 * w ^ 2 = R ^ 2 * ((N : ℤ) * Y) := by
      calc R ^ 2 * w ^ 2 = (R * w) ^ 2 := by ring
        _ = (S * Y) ^ 2 := by rw [← hw]
        _ = R ^ 2 * ((N : ℤ) * Y) := by rw [← h1]; ring
    exact mul_left_cancel₀ (pow_ne_zero 2 hR.ne') this
  -- cast to ZMod 32
  have hz : ((w : ZMod 32)) ^ 2 = (N : ZMod 32) * ((2 * (q : ZMod 32) ^ 2 - (p : ZMod 32) ^ 2) *
      (3 * (q : ZMod 32) ^ 2 - (p : ZMod 32) ^ 2)) := by
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


/-- Negative control: the 2-adic obstruction is FALSE at 42 and 70 (a bad residue triple exists). -/
theorem twoadic_fails_42 : ¬ (∀ p q w : ZMod 32, ¬ (2 ∣ p.val ∧ 2 ∣ q.val) →
    w ^ 2 ≠ ((42 : ℕ) : ZMod 32) * ((2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2))) := by decide +kernel

theorem twoadic_fails_70 : ¬ (∀ p q w : ZMod 32, ¬ (2 ∣ p.val ∧ 2 ∣ q.val) →
    w ^ 2 ≠ ((70 : ℕ) : ZMod 32) * ((2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2))) := by decide +kernel

theorem twoadic_14 : S2Arith 14 := s2Arith_of_twoadic 14 (by norm_num) (by decide +kernel)
theorem twoadic_62 : S2Arith 62 := s2Arith_of_twoadic 62 (by norm_num) (by decide +kernel)

end Erdos634.Draft.CompositeS2Arith

#print axioms Erdos634.Draft.CompositeS2Arith.s2Closed_of_arith
#print axioms Erdos634.Draft.CompositeS2Arith.twoadic_14
#print axioms Erdos634.Draft.CompositeS2Arith.twoadic_62
#print axioms Erdos634.Draft.CompositeS2Arith.twoadic_fails_42
#print axioms Erdos634.Draft.CompositeS2Arith.twoadic_fails_70
