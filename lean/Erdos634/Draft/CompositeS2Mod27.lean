/-
Draft/CompositeS2Mod27.lean — S2 (target (2α, α, 2β)) at N = 66 = 2·3·11 by a 3-ADIC obstruction (new; N = 66 is where
the 2-adic mod-32 closer of `CompositeS2Arith` fails and no odd-valuation prime ℓ has both 2 and 3 non-residues).
`s2Arith_of_mod27`: if N·(2q²−p²)(3q²−p²) is never a square mod 27 for p, q not both divisible by 3 (coprime p,q) then
`S2Arith N` (front end = `CompositeS2Arith.s2Arith_of_twoadic`, modulus 32 → 27).  Holds at N = 66 (`decide +kernel`).
Python scan (moduli ≤ 129 and 243, 256, 625, 729, 1331): at N = 22 there is NO local obstruction for S2, so `S2Closed 22`
stays a named hypothesis; at N = 66 the obstruction is exactly at 27, 54, 81, ... (3-adic), not at 2 or 11.
UNAUDITED.  Formalization debt, NOT /goal progress.  No sorry, no native_decide.
-/
import Erdos634.Draft.CompositeS2Arith

open scoped Classical

set_option synthInstance.maxSize 1000
set_option synthInstance.maxHeartbeats 400000

namespace Erdos634.Draft.CompositeS2Mod27

open Erdos634.Geometry Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeS2Arith

/-- 3-adic (mod 27) obstruction ⇒ `S2Arith N`. -/
theorem s2Arith_of_mod27 (N : ℕ) (hN : 0 < N)
    (h : ∀ p q w : ZMod 27, ¬ (3 ∣ p.val ∧ 3 ∣ q.val) → w ^ 2 ≠ (N : ZMod 27) * ((2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2))) :
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
  -- cast to ZMod 27
  have hz : ((w : ZMod 27)) ^ 2 = (N : ZMod 27) * ((2 * (q : ZMod 27) ^ 2 - (p : ZMod 27) ^ 2) *
      (3 * (q : ZMod 27) ^ 2 - (p : ZMod 27) ^ 2)) := by
    have := congrArg (fun z : ℤ => (z : ZMod 27)) hw2
    simpa [hYdef] using this
  have hpar : ¬ (3 ∣ (p : ZMod 27).val ∧ 3 ∣ (q : ZMod 27).val) := by
    rintro ⟨h2p, h2q⟩
    have vp := ZMod.val_intCast (n := 27) p
    have vq := ZMod.val_intCast (n := 27) q
    have hp2 : (3 : ℤ) ∣ p := by omega
    have hq2 : (3 : ℤ) ∣ q := by omega
    have hu := hcop.isUnit_of_dvd' hp2 hq2
    have := Int.isUnit_iff.mp hu
    omega
  exact h _ _ _ hpar hz


theorem s2Arith_66 : S2Arith 66 := s2Arith_of_mod27 66 (by norm_num) (by decide +kernel)

/-- Negative control: the mod-27 obstruction FAILS at N = 22 (a bad residue triple exists). -/
theorem mod27_fails_22 : ¬ (∀ p q w : ZMod 27, ¬ (3 ∣ p.val ∧ 3 ∣ q.val) →
    w ^ 2 ≠ ((22 : ℕ) : ZMod 27) * ((2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2))) := by decide +kernel

theorem s2Closed_66 : S2Closed 66 := s2Closed_of_arith 66 s2Arith_66

end Erdos634.Draft.CompositeS2Mod27

#print axioms Erdos634.Draft.CompositeS2Mod27.s2Closed_66
#print axioms Erdos634.Draft.CompositeS2Mod27.mod27_fails_22
