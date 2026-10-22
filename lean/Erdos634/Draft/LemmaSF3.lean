/-
Lemma S, node A5: **FC-odd, |F| = 3 with β_j = β_k ≠ β_l**, including P1.4 ("the proof's R1F3 is
empty") (PROOF_lemmaS.md §4 and P1.4).

  Four points ±β, ±β_l, so N(a) applies for every primitive η mod m_I. This gives c_l = 0 (so e_l = 0)
  and e_jη(γ_j) + e_kη(γ_k) = 0. By G′, either e_j = e_k = 0, or g := γ_j/γ_k ∈ Sp(m_I) with
  e_k = −(−1)^{τ(g)} e_j. g = 1 means x_j = x_k. [P1.4] In R1F3, g ∈ Sp(m) ∖ {1}; the third point's
  m-part is −(1 + g)γ_k/m; if g₃ = −1 then 3 | 1 + g, if g₂ = 1 + 2^{v−1} then 2 | 1 + g; either way
  its order is below m, so l ∉ F — a contradiction.

Class form: three distinct full points x, y, l, y ≡ x (mod p^r), l ≢ ±x (mod p^r), x + y + l = n.
Conclusion: E_x = E_y = E_l = 0.
Formalization debt, not /goal progress.
-/
import Mathlib
import Erdos634.Draft.LemmaSR1p

open scoped BigOperators
open Finset

namespace Erdos634.LemmaSF3

open DirichletCharacter
open Erdos634.LemmaSC (bracket)
open Erdos634.LemmaSElim (classSum)
open Erdos634.LemmaSFC (fullPts card_N fc_isolated_img)
open Erdos634.LemmaSN (pred_dvd)
open Erdos634.LemmaSGprime (Sp tau)
open Erdos634.LemmaSGpp (SpPP)

section F3
variable {p r m : ℕ} [hp : Fact p.Prime] [NeZero m]

theorem lemmaF3same (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (hm4 : m % 4 ≠ 2)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (x y l : ℕ) (himg : univ.image a = {x, y, l}) (hsum : x + y + l = p ^ r * m)
    (hx : x ∈ fullPts p m a) (hy : y ∈ fullPts p m a) (hl : l ∈ fullPts p m a)
    (hxy : x ≠ y) (hxl : x ≠ l) (hyl : y ≠ l)
    (hβ : (y : ZMod (p ^ r)) = x) (hlβ : (l : ZMod (p ^ r)) ≠ x ∧ (l : ZMod (p ^ r)) ≠ -x) :
    classSum a e x = 0 ∧ classSum a e y = 0 ∧ classSum a e l = 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hxf := mem_filter.1 hx
  have hyf := mem_filter.1 hy
  have hlf := mem_filter.1 hl
  have hmem : ∀ w, w ∈ univ.image a ↔ w = x ∨ w = y ∨ w = l := by
    intro w; rw [himg]; simp
  have hsub : ∀ w ∈ fullPts p m a, w = x ∨ w = y ∨ w = l := fun w hw => (hmem w).1 (mem_filter.1 hw).1
  have hN : 2 * ((fullPts p m a).image (fun y : ℕ => (y : ZMod (p ^ r)))).card <
      (univ.filter (fun v : (ZMod (p ^ r))ˣ => ZMod.unitsMap (pred_dvd p r) v = 1)).card := by
    have hc : ((fullPts p m a).image (fun y : ℕ => (y : ZMod (p ^ r)))).card ≤ 2 := by
      refine (card_le_card (?_ : _ ⊆ ({(x : ZMod (p ^ r)), (l : ZMod (p ^ r))} : Finset _))).trans
        ((card_insert_le _ _).trans (by simp))
      intro u hu
      obtain ⟨w, hw, rfl⟩ := mem_image.1 hu
      rcases hsub w hw with rfl | rfl | rfl <;> simp [hβ]
    rw [card_N hr]; split_ifs <;> omega
  -- c_l = 0
  have hEl : classSum a e l = 0 := by
    refine fc_isolated_img hp7 hr hpm hm4 a e hP l hl (fun w hw hwl _ => ?_) hN
    rcases hsub w hw with rfl | rfl | rfl
    · exact ⟨fun h => hlβ.1 h.symm, fun h => hlβ.2 (by rw [h]; ring)⟩
    · rw [hβ]; exact ⟨fun h => hlβ.1 h.symm, fun h => hlβ.2 (by rw [h]; ring)⟩
    · exact absurd rfl hwl
  refine ⟨?_, ?_, hEl⟩ <;> [skip; skip]
  all_goals
    have hsep : ∀ w ∈ fullPts p m a, w ≠ x → w ≠ y → classSum a e w ≠ 0 →
        (w : ZMod (p ^ r)) ≠ x ∧ (w : ZMod (p ^ r)) ≠ -x := by
      intro w hw hwx hwy hE
      rcases hsub w hw with h | h | h
      · exact absurd h hwx
      · exact absurd h hwy
      · subst h; exact absurd hEl hE
    set z : ℤ := ((((x : ZMod m) * (y : ZMod m)⁻¹)).val : ℤ)
    have hzm : ((z : ℤ) : ZMod m) * (y : ZMod m) = x := by
      simp only [z, Int.cast_natCast, ZMod.natCast_zmod_val, mul_assoc]
      rw [mul_comm ((y : ZMod m))⁻¹, ZMod.coe_mul_inv_eq_one y hyf.2.2, mul_one]
    have hz : z * (1 * y) ≡ x [ZMOD m] := by
      rw [← ZMod.intCast_eq_intCast_iff]; push_cast; rw [one_mul]; exact hzm
    have hkey := Erdos634.LemmaSL.fc_key hp7 hr hpm a e hP x y hx hy hxy 1 (Or.inl rfl)
      (by rw [hβ]; push_cast; ring) hsep hN
    rcases Erdos634.LemmaSL.rel_Gprime hm4 _ _ x y hxf.2.2 hyf.2.2 1 (Or.inl rfl) z hz hkey with
      h | ⟨hSp, -⟩
    · first | exact h.1 | exact h.2
    exfalso
    -- g ≠ 1
    have hg1 : ¬ z ≡ 1 [ZMOD m] := by
      intro h1
      have hxym : ((x : ℕ) : ZMod m) = y := by
        have := (ZMod.intCast_eq_intCast_iff _ _ _).2 h1
        rw [Int.cast_one] at this; rw [← hzm, this, one_mul]
      rw [ZMod.natCast_eq_natCast_iff] at hxym
      have hxyP : x ≡ y [MOD p ^ r] := ((ZMod.natCast_eq_natCast_iff _ _ _).1 hβ).symm
      have hn := (Nat.modEq_and_modEq_iff_modEq_mul (Erdos634.LemmaSPhi.cop_pr hpm)).1 ⟨hxyP, hxym⟩
      have hl0 : 0 < l := Nat.pos_of_ne_zero (fun h => hlf.2.1 (h ▸ dvd_zero p))
      have hy0 : 0 < y := Nat.pos_of_ne_zero (fun h => hyf.2.1 (h ▸ dvd_zero p))
      have hx0 : 0 < x := Nat.pos_of_ne_zero (fun h => hxf.2.1 (h ▸ dvd_zero p))
      exact hxy (Nat.ModEq.eq_of_lt_of_lt hn (by omega) (by omega))
    obtain ⟨q, hq, hbad⟩ : ∃ q ∈ m.primeFactors, ¬ z ≡ 1 [ZMOD (q : ℤ) ^ m.factorization q] := by
      by_contra hno; push Not at hno
      exact hg1 (Erdos634.LemmaSR1p.modEq_of_components (NeZero.ne m) hno)
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hqm : q ∣ m := Nat.dvd_of_mem_primeFactors hq
    -- l ≡ −y(1 + g) (mod m)
    have hlm : ((l : ℕ) : ZMod m) = -(y : ZMod m) * (((z : ℤ) : ZMod m) + 1) := by
      have hs : ((x + y + l : ℕ) : ZMod m) = 0 := by
        rw [hsum, (ZMod.natCast_eq_zero_iff _ _).2 (dvd_mul_left _ _)]
      push_cast at hs; rw [← hzm] at hs; linear_combination hs
    have hzq : ((z : ℤ) : ZMod q) = -1 := by
      rcases hSp q hq with h | ⟨rfl, -, h⟩ | ⟨rfl, hv2, h⟩
      · exact absurd h hbad
      · have := (ZMod.intCast_eq_intCast_iff z (-1) 3).2 h; push_cast at this; exact this
      · have h2 : z ≡ 1 [ZMOD 2] := by
          refine h.of_dvd ?_ |>.trans ?_
          · exact dvd_pow_self 2 (by omega)
          · rw [Int.modEq_iff_dvd]
            have e : (1 : ℤ) - (1 + 2 ^ (m.factorization 2 - 1)) = -(2 ^ (m.factorization 2 - 1)) := by
              ring
            rw [e]; exact (dvd_pow_self (2 : ℤ) (by omega)).neg_right
        have := (ZMod.intCast_eq_intCast_iff z 1 2).2 h2
        rw [this]; push_cast; decide
    have hlq : ((l : ℕ) : ZMod q) = 0 := by
      have := congrArg (ZMod.castHom hqm (ZMod q)) hlm
      rw [map_natCast, map_mul, map_neg, map_natCast, map_add, map_intCast, map_one, hzq] at this
      rw [this]; ring
    rw [ZMod.natCast_eq_zero_iff] at hlq
    have := Nat.dvd_gcd hlq hqm
    rw [hlf.2.2.gcd_eq_one] at this
    exact hqp.one_lt.ne' (Nat.dvd_one.1 this)

end F3

/-! ## Consequence: n = 35 = 7·5, a = (1, 8, 26): three full points, 8 ≡ 1 (mod 7) (same β),
26 ≢ ±1 (mod 7). For EVERY e satisfying Lemma P's hypothesis all class sums vanish. -/
theorem consequence_F3_35 (e : Fin 3 → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (7 ^ 1 * 5), χ.Odd → 7 ^ 1 ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ ((![1, 8, 26] : Fin 3 → ℕ) j) = 0) :
    classSum ![1, 8, 26] e 1 = 0 ∧ classSum ![1, 8, 26] e 8 = 0 ∧ classSum ![1, 8, 26] e 26 = 0 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hfp : fullPts 7 5 (![1, 8, 26] : Fin 3 → ℕ) = {1, 8, 26} := by decide
  exact lemmaF3same (p := 7) (r := 1) (m := 5) (by norm_num) le_rfl (by norm_num) (by norm_num)
    _ e hP 1 8 26 (by decide) (by norm_num) (by rw [hfp]; decide) (by rw [hfp]; decide)
    (by rw [hfp]; decide) (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide)

#print axioms Erdos634.LemmaSF3.lemmaF3same
#print axioms Erdos634.LemmaSF3.consequence_F3_35

end Erdos634.LemmaSF3
