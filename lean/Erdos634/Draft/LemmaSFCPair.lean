/-
Lemma S, node A5: **FC-odd, the same-β pair step through G′** (PROOF_lemmaS.md §4, case
"|F| = 3, β_j = β_k ≠ β_l" and "|F| = 2, β_k = β_j"):

  N(a) applies for every primitive η mod m_I. This gives e_j η(γ_j) + e_k η(γ_k) = 0.
  By G′, either e_j = e_k = 0, or g := γ_j/γ_k ∈ Sp(m_I) with e_k = −(−1)^{τ(g)} e_j.

Class form (P1.2): x ≠ y full I-points with the same β (x ≡ y mod p^r); for full points
γ_x/γ_y ≡ x/y (mod m), represented by any integer z with z·y ≡ x (mod m).
Uses LemmaSGprime.lemmaG' (G′) — its first consumer.
Formalization debt, not /goal progress.
-/
import Mathlib
import Erdos634.Draft.LemmaSFC

open scoped BigOperators
open Finset

namespace Erdos634.LemmaSFCPair

open DirichletCharacter
open Erdos634.LemmaSC (bracket)
open Erdos634.LemmaSElim (classSum)
open Erdos634.LemmaSFC (fullPts PhiF fc_symm)
open Erdos634.LemmaSN (pred_dvd)
open Erdos634.LemmaSGprime (Sp tau lemmaG')

section Pair
variable {p r m : ℕ} [hp : Fact p.Prime] [NeZero m]

/-- **FC pair step** (§4 via G′). -/
theorem fc_pair (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (hm4 : m % 4 ≠ 2) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (x y : ℕ) (hx : x ∈ fullPts p m a) (hy : y ∈ fullPts p m a) (hxy : x ≠ y)
    (hβ : (y : ZMod (p ^ r)) = x)
    (hsep : ∀ w ∈ fullPts p m a, w ≠ x → w ≠ y → classSum a e w ≠ 0 →
      (w : ZMod (p ^ r)) ≠ x ∧ (w : ZMod (p ^ r)) ≠ -x)
    (hN : 2 * (fullPts p m a).card <
      (univ.filter (fun v : (ZMod (p ^ r))ˣ => ZMod.unitsMap (pred_dvd p r) v = 1)).card)
    (z : ℤ) (hz : z * y ≡ x [ZMOD m]) :
    (classSum a e x = 0 ∧ classSum a e y = 0) ∨
      (Sp m z ∧ classSum a e y = -(-1) ^ tau m z * classSum a e x) := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hxf := mem_filter.1 hx
  have hyf := mem_filter.1 hy
  have hxP : x.Coprime (p ^ r) :=
    Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hxf.2.1).symm
  set ux : (ZMod (p ^ r))ˣ := ZMod.unitOfCoprime x hxP
  have hux : (ux : ZMod (p ^ r)) = x := ZMod.coe_unitOfCoprime x hxP
  have hxx : (x : ZMod (p ^ r)) ≠ -x := by
    intro h
    have h2 : ((2 * x : ℕ) : ZMod (p ^ r)) = 0 := by push_cast; linear_combination h
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := (Nat.Prime.dvd_mul hp.out).1 (dvd_trans (dvd_pow_self p (by omega)) h2)
    rcases this with h | h
    · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
    · exact hxf.2.1 h
  -- the relation at every primitive η mod m
  have key : ∀ η : DirichletCharacter ℂ m, η.IsPrimitive →
      ((classSum a e x : ℚ) : ℂ) * η (x : ZMod m) + ((classSum a e y : ℚ) : ℂ) * η (y : ZMod m) = 0 := by
    intro η hη
    have hs := fc_symm hr hpm a e hP hη
      (lt_of_le_of_lt (Nat.mul_le_mul_left 2 card_image_le) hN) ux
    have h1 : PhiF p r m η a e ux =
        ((classSum a e x : ℚ) : ℂ) * η (x : ZMod m) + ((classSum a e y : ℚ) : ℂ) * η (y : ZMod m) := by
      unfold PhiF
      rw [sum_eq_add_of_mem x y hx hy hxy]
      · rw [if_pos hux, if_pos (by rw [hux, hβ])]
      · intro w hw ⟨hwx, hwy⟩
        by_cases hE : classSum a e w = 0
        · split_ifs <;> simp [hE]
        · rw [if_neg]; rw [hux]; exact fun h => (hsep w hw hwx hwy hE).1 h.symm
    have h2 : PhiF p r m η a e (-ux) = 0 := by
      unfold PhiF
      refine sum_eq_zero (fun w hw => ?_)
      rw [Units.val_neg, hux]
      by_cases hwx : w = x
      · subst hwx; rw [if_neg (fun h => hxx h.symm)]
      by_cases hwy : w = y
      · subst hwy; rw [if_neg (fun h => hxx (by rw [h, hβ]))]
      by_cases hE : classSum a e w = 0
      · split_ifs <;> simp [hE]
      · rw [if_neg]; exact fun h => (hsep w hw hwx hwy hE).2 h.symm
    rw [h1, h2, mul_zero] at hs
    exact hs
  obtain ⟨η0, hη0⟩ := Erdos634.LemmaSGprime.exists_primitive (NeZero.ne m) hm4
  set gx : (ZMod m)ˣ := ZMod.unitOfCoprime x hxf.2.2
  set gy : (ZMod m)ˣ := ZMod.unitOfCoprime y hyf.2.2
  have hgx : (gx : ZMod m) = x := ZMod.coe_unitOfCoprime x hxf.2.2
  have hgy : (gy : ZMod m) = y := ZMod.coe_unitOfCoprime y hyf.2.2
  by_cases hEx : classSum a e x = 0
  · left
    refine ⟨hEx, ?_⟩
    have := key η0 hη0
    rw [hEx, Rat.cast_zero, zero_mul, zero_add] at this
    have hηy : η0 (y : ZMod m) ≠ 0 := by
      rw [← hgy]; exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
    exact_mod_cast (mul_eq_zero.1 this).resolve_right hηy
  · right
    set g : (ZMod m)ˣ := gx * gy⁻¹
    have hzg : ((z : ℤ) : ZMod m) = g := by
      have h1 : ((z : ℤ) : ZMod m) * (y : ZMod m) = x := by
        have := (ZMod.intCast_eq_intCast_iff (z * y) x m).2 hz
        push_cast at this; exact this
      have hyy : (y : ZMod m) * ((gy⁻¹ : (ZMod m)ˣ) : ZMod m) = 1 := by
        rw [← hgy, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      calc ((z : ℤ) : ZMod m) = ((z : ℤ) : ZMod m) * (y : ZMod m) * ((gy⁻¹ : (ZMod m)ˣ) : ZMod m) := by
            rw [mul_assoc, hyy, mul_one]
        _ = _ := by rw [h1, ← hgx, ← Units.val_mul]
    have hval : ∀ η : DirichletCharacter ℂ m, η.IsPrimitive →
        η (g : ZMod m) = -((classSum a e y : ℚ) : ℂ) / ((classSum a e x : ℚ) : ℂ) := by
      intro η hη
      have hk := key η hη
      have hEx' : ((classSum a e x : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hEx
      have hηy : η (y : ZMod m) ≠ 0 := by
        rw [← hgy]; exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
      have hinv : η ((gy⁻¹ : (ZMod m)ˣ) : ZMod m) * η (y : ZMod m) = 1 := by
        rw [← hgy, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
      rw [eq_div_iff hEx']
      simp only [g, Units.val_mul, map_mul, hgx]
      calc η (x : ZMod m) * η ((gy⁻¹ : (ZMod m)ˣ) : ZMod m) * ((classSum a e x : ℚ) : ℂ)
          = (((classSum a e x : ℚ) : ℂ) * η (x : ZMod m)) * η ((gy⁻¹ : (ZMod m)ˣ) : ZMod m) := by ring
        _ = (-(((classSum a e y : ℚ) : ℂ) * η (y : ZMod m))) * η ((gy⁻¹ : (ZMod m)ˣ) : ZMod m) := by
            rw [show ((classSum a e x : ℚ) : ℂ) * η (x : ZMod m)
              = -(((classSum a e y : ℚ) : ℂ) * η (y : ZMod m)) by linear_combination hk]
        _ = -((classSum a e y : ℚ) : ℂ) := by linear_combination (-((classSum a e y : ℚ) : ℂ)) * hinv
    obtain ⟨G1, G2⟩ := lemmaG' (NeZero.ne m) hm4 g z hzg
    have hSp : Sp m z := G1.1 ⟨_, hval⟩
    refine ⟨hSp, ?_⟩
    have := G2 hSp η0 hη0
    rw [hval η0 hη0] at this
    have hEx' : ((classSum a e x : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hEx
    rw [div_eq_iff hEx'] at this
    have : ((classSum a e y : ℚ) : ℂ) = (((-(-1) ^ tau m z * classSum a e x : ℚ)) : ℂ) := by
      push_cast; linear_combination -this
    exact_mod_cast this

end Pair

/-! ## A genuine consequence at n = 63 = 7·9, a = (1, 8, 54), p = 7: the full I-points are 1 and 8
(54 is not prime to 9), 8 ≡ 1 (mod 7) (same β), g = 1/8 ≡ 8 (mod 9) and 8 ∉ Sp(9) (3² ∥ 9, so
g₃ = −1 is not allowed). Hence for EVERY e satisfying Lemma P's hypothesis, E₁ = E₈ = 0. -/
theorem consequence_63 (e : Fin 3 → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (7 ^ 1 * 9), χ.Odd → 7 ^ 1 ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ ((![1, 8, 54] : Fin 3 → ℕ) j) = 0) :
    classSum ![1, 8, 54] e 1 = 0 ∧ classSum ![1, 8, 54] e 8 = 0 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hfp : fullPts 7 9 (![1, 8, 54] : Fin 3 → ℕ) = {1, 8} := by decide
  have hN : 2 * (fullPts 7 9 (![1, 8, 54] : Fin 3 → ℕ)).card <
      (univ.filter (fun v : (ZMod (7 ^ 1))ˣ => ZMod.unitsMap (pred_dvd 7 1) v = 1)).card := by
    rw [Erdos634.LemmaSFC.card_N le_rfl, hfp]; decide
  rcases fc_pair (p := 7) (r := 1) (m := 9) (by norm_num) le_rfl (by norm_num) (by norm_num) _ e hP
    1 8 (by rw [hfp]; decide) (by rw [hfp]; decide) (by norm_num) (by decide)
    (fun w hw hw1 hw8 _ => by rw [hfp] at hw; simp at hw; omega) hN 8 (by decide) with h | ⟨hS, -⟩
  · exact h
  · exfalso
    have := (Erdos634.LemmaSGprime.Sp_pp (p := 3) (n := 2) Nat.prime_three (by norm_num) 8).1
      (by simpa using hS)
    rcases this with h | ⟨-, h, -⟩ | ⟨h, -⟩
    · exact absurd h (by decide)
    · exact absurd h (by norm_num)
    · exact absurd h (by norm_num)

#print axioms Erdos634.LemmaSFCPair.fc_pair
#print axioms Erdos634.LemmaSFCPair.consequence_63

end Erdos634.LemmaSFCPair
