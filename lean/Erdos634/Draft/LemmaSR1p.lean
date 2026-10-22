/-
Lemma S, node A5: **class R1′ closed** (PROOF_lemmaS.md §4 "|F| = 2, β_k = −β_j" + Lemma L).

  |F| = 2, β_k = −β_j. This forces |I| = 2 (so I = F). N(a) gives c_j = η(−1)c_k, so
  g := −γ_j/γ_k ∈ Sp(m_I) and e_k = (−1)^{τ(g)} e_j. g = 1 would mean x_j = −x_k, i.e. x₃ = 0, which is
  impossible. So x₃ = −(x_j + x_k) ≠ 0 has order dividing 6: class R1′. Lemma L (with a prime
  q ∈ {2, 3} where g_q ≠ 1) then gives e_j = e_k = 0.

Class form: points x, y full with y ≡ −x (mod p^r), the third point t with p | t (not in I), all
positive with x + y + t = n. Proved: `lemmaR1prime` : E_x = E_y = 0. Also `modEq_of_components`:
if g ≡ 1 at every prime power q^v ∥ m then g ≡ 1 (mod m) (used for "g = 1 would mean …").
Formalization debt, not /goal progress.
-/
import Mathlib
import Erdos634.Draft.LemmaSR2a

open scoped BigOperators
open Finset

namespace Erdos634.LemmaSR1p

open DirichletCharacter
open Erdos634.LemmaSC (bracket)
open Erdos634.LemmaSElim (classSum)
open Erdos634.LemmaSFC (fullPts card_N)
open Erdos634.LemmaSN (pred_dvd)
open Erdos634.LemmaSGprime (Sp tau Sp_pp)
open Erdos634.LemmaSGpp (SpPP)

/-- If g ≡ 1 modulo every prime power exactly dividing m, then g ≡ 1 (mod m). -/
theorem modEq_of_components {m : ℕ} (hm : m ≠ 0) {z : ℤ}
    (h : ∀ q ∈ m.primeFactors, z ≡ 1 [ZMOD (q : ℤ) ^ m.factorization q]) : z ≡ 1 [ZMOD m] := by
  rw [Int.modEq_iff_dvd, Int.natCast_dvd]
  by_cases hN : (1 - z).natAbs = 0
  · rw [hN]; exact dvd_zero _
  rw [← Nat.factorization_le_iff_dvd hm hN, Finsupp.le_def]
  intro q
  by_cases hq : q ∈ m.primeFactors
  · have hqp := Nat.prime_of_mem_primeFactors hq
    have h1 := Int.ModEq.dvd (h q hq)
    rw [show ((q : ℤ) ^ m.factorization q) = ((q ^ m.factorization q : ℕ) : ℤ) by push_cast; rfl,
      Int.natCast_dvd] at h1
    exact (hqp.pow_dvd_iff_le_factorization hN).1 h1
  · rw [Finsupp.notMem_support_iff.1 (by rwa [Nat.support_factorization])]; exact Nat.zero_le _

section R1p
variable {p r m : ℕ} [hp : Fact p.Prime] [NeZero m]

/-- **Class R1′ closed** (§4 + Lemma L). -/
theorem lemmaR1prime (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (hm4 : m % 4 ≠ 2)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (x y t : ℕ) (himg : univ.image a = {x, y, t}) (hsum : x + y + t = p ^ r * m)
    (htpos : 0 < t) (hpx : ¬ p ∣ x) (hpy : ¬ p ∣ y) (hpt : p ∣ t) (hxm : x.Coprime m)
    (hym : y.Coprime m) (hxy : x ≠ y) (hβ : (y : ZMod (p ^ r)) = -(x : ZMod (p ^ r))) :
    classSum a e x = 0 ∧ classSum a e y = 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hmem : ∀ w, w ∈ univ.image a ↔ w = x ∨ w = y ∨ w = t := by
    intro w; rw [himg]; simp
  have hx : x ∈ fullPts p m a := mem_filter.2 ⟨(hmem x).2 (Or.inl rfl), hpx, hxm⟩
  have hy : y ∈ fullPts p m a := mem_filter.2 ⟨(hmem y).2 (Or.inr (Or.inl rfl)), hpy, hym⟩
  have hsub : ∀ w ∈ fullPts p m a, w = x ∨ w = y := by
    intro w hw
    have hwf := mem_filter.1 hw
    rcases (hmem w).1 hwf.1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · subst h; exact absurd hpt hwf.2.1
  have hsep : ∀ w ∈ fullPts p m a, w ≠ x → w ≠ y → classSum a e w ≠ 0 →
      (w : ZMod (p ^ r)) ≠ x ∧ (w : ZMod (p ^ r)) ≠ -x := by
    intro w hw hwx hwy; rcases hsub w hw with h | h <;> contradiction
  have hN : 2 * ((fullPts p m a).image (fun y : ℕ => (y : ZMod (p ^ r)))).card <
      (univ.filter (fun v : (ZMod (p ^ r))ˣ => ZMod.unitsMap (pred_dvd p r) v = 1)).card := by
    have hc : ((fullPts p m a).image (fun y : ℕ => (y : ZMod (p ^ r)))).card ≤ 2 := by
      refine (card_le_card (?_ : _ ⊆ ({(x : ZMod (p ^ r)), -(x : ZMod (p ^ r))} : Finset _))).trans
        ((card_insert_le _ _).trans (by simp))
      intro u hu
      obtain ⟨w, hw, rfl⟩ := mem_image.1 hu
      rcases hsub w hw with rfl | rfl <;> simp [hβ]
    rw [card_N hr]; split_ifs <;> omega
  have hdie : ∀ w ∈ univ.image a, w ≠ x → w ≠ y → ¬ p ∣ w → classSum a e w ≠ 0 → False := by
    intro w hw hwx hwy hpw _
    rcases (hmem w).1 hw with h | h | h
    · exact hwx h
    · exact hwy h
    · exact hpw (h ▸ hpt)
  -- g := x / (−y) mod m
  set z : ℤ := ((((x : ZMod m) * ((-1 : ZMod m) * (y : ZMod m))⁻¹)).val : ℤ)
  have hsyu : IsUnit ((-1 : ZMod m) * (y : ZMod m)) :=
    isUnit_one.neg.mul ((ZMod.isUnit_iff_coprime y m).2 hym)
  have hz : z * (-1 * y) ≡ x [ZMOD m] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    simp only [z, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val, Int.cast_neg, Int.cast_one]
    rw [mul_assoc, ZMod.inv_mul_of_unit _ hsyu, mul_one]
  have hkey := Erdos634.LemmaSL.fc_key hp7 hr hpm a e hP x y hx hy hxy (-1) (Or.inr rfl)
    (by rw [hβ]; push_cast; ring) hsep hN
  rcases Erdos634.LemmaSL.rel_Gprime hm4 _ _ x y hxm hym (-1) (Or.inr rfl) z hz hkey with h | ⟨hSp, -⟩
  · exact h
  -- g ≠ 1: some prime-power component is exceptional
  have hg1 : ¬ z ≡ 1 [ZMOD m] := by
    intro h1
    have hxy0 : ((x + y : ℕ) : ZMod m) = 0 := by
      have := (ZMod.intCast_eq_intCast_iff _ _ _).2 (h1.mul_right (-1 * (y : ℤ)) |>.symm.trans hz)
      push_cast at this; push_cast; linear_combination -this
    have hxyP : ((x + y : ℕ) : ZMod (p ^ r)) = 0 := by push_cast; rw [hβ]; ring
    rw [ZMod.natCast_eq_zero_iff] at hxy0 hxyP
    have hn : p ^ r * m ∣ x + y :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (Erdos634.LemmaSPhi.cop_pr hpm) hxyP hxy0
    have := Nat.le_of_dvd (by
      rcases Nat.eq_zero_or_pos x with h | h
      · exact absurd (h ▸ dvd_zero p) hpx
      · omega) hn
    omega
  obtain ⟨q, hq, hbad⟩ : ∃ q ∈ m.primeFactors, ¬ z ≡ 1 [ZMOD (q : ℤ) ^ m.factorization q] := by
    by_contra hno; push Not at hno
    exact hg1 (modEq_of_components (NeZero.ne m) hno)
  have hqp := Nat.prime_of_mem_primeFactors hq
  set v := m.factorization q
  have hv : 1 ≤ v := (hqp.dvd_iff_one_le_factorization (NeZero.ne m)).1 (Nat.dvd_of_mem_primeFactors hq)
  have hspp : SpPP q v z := hSp q hq
  set m' := m / q ^ v
  have hmm' : m = q ^ v * m' := (Nat.ordProj_mul_ordCompl_eq_self m q).symm
  have hqm' : ¬ q ∣ m' := Nat.not_dvd_ordCompl hqp (NeZero.ne m)
  rcases hspp with h | ⟨rfl, hv1, -⟩ | ⟨rfl, hv2, -⟩
  · exact absurd h hbad
  · exact Erdos634.LemmaSL.lemmaL hp7 hr hpm (q := 3) (v := v) (v' := 0) (m' := m') (Or.inr rfl) hv
      hqm' hmm' hm4 (Or.inl rfl) a e hP x y hx hy hxy (-1) (Or.inr rfl) (by rw [hβ]; push_cast; ring)
      hsep hN z hz hbad (fun w hw h1 h2 h3 h4 _ => hdie w hw h1 h2 h3 h4)
  · rcases Nat.lt_or_ge v 3 with h3 | h3
    · exact Erdos634.LemmaSL.lemmaL hp7 hr hpm (q := 2) (v := v) (v' := 0) (m' := m') (Or.inl rfl) hv
        hqm' hmm' hm4 (Or.inl rfl) a e hP x y hx hy hxy (-1) (Or.inr rfl)
        (by rw [hβ]; push_cast; ring) hsep hN z hz hbad (fun w hw h1 h2 h3 h4 _ => hdie w hw h1 h2 h3 h4)
    · exact Erdos634.LemmaSL.lemmaL hp7 hr hpm (q := 2) (v := v) (v' := v - 1) (m' := m') (Or.inl rfl)
        hv hqm' hmm' hm4 (Or.inr ⟨rfl, rfl, h3⟩) a e hP x y hx hy hxy (-1) (Or.inr rfl)
        (by rw [hβ]; push_cast; ring) hsep hN z hz hbad (fun w hw h1 h2 h3 h4 _ => hdie w hw h1 h2 h3 h4)

end R1p

/-! ## Consequence: n = 105, a = (2, 68, 35) (class R1′, from `lemmaR1prime` without supplying g). -/
theorem consequence_R1p_105 (e : Fin 3 → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (7 ^ 1 * 15), χ.Odd → 7 ^ 1 ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ ((![2, 68, 35] : Fin 3 → ℕ) j) = 0) :
    classSum ![2, 68, 35] e 2 = 0 ∧ classSum ![2, 68, 35] e 68 = 0 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact lemmaR1prime (p := 7) (r := 1) (m := 15) (by norm_num) le_rfl (by norm_num) (by norm_num)
    _ e hP 2 68 35 (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by decide)

#print axioms Erdos634.LemmaSR1p.modEq_of_components
#print axioms Erdos634.LemmaSR1p.lemmaR1prime
#print axioms Erdos634.LemmaSR1p.consequence_R1p_105

end Erdos634.LemmaSR1p
