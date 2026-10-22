/-
Lemma S, node A5: **R2b with f₂ = 3** (m = 12), the sub-case round 2 §4.6 settles by N±(iii):
  "If f₂ = 3 (m_I = 12), N±(iii) applies: support ⊆ {±1, ±½}, 4 < p − 1, so the element is odd and
  again A = B = 0."
The only primitive character mod 3 is odd, so the level-3 element Φ″ = A[1] − Aη̄(2)[½] + B[−½]
is ANTI-symmetric (N(c) for r = 1 with the support count 4 < p − 1; N(a) for r ≥ 2).
Proved: `level2_three_anti` (the level-3 step) and `lemmaR2b_12`.
Formalization debt, not /goal progress.
-/
import Mathlib
import Erdos634.Draft.LemmaSR3

open scoped BigOperators
open Finset

namespace Erdos634.LemmaSR2b12

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi (chi dm conductor_chi bracket_p_dvd bracket_unit sum_indicator)
open Erdos634.LemmaSElim (classSum regroup)
open Erdos634.LemmaSFC (fullPts dm_eq_iff card_val_le_one card_N)
open Erdos634.LemmaSN (pred_dvd lemmaN_a lemmaN_b)
open Erdos634.LemmaSIso (conductor_changeLevel_of_isPrimitive primChar_ne_zero)
open Erdos634.LemmaSR3 (Phi2 psi_Phi2 setup3 top_equal small_cop kX_ne)

section L3
variable {p r m : ℕ} [hp : Fact p.Prime] [NeZero m]

theorem level2_three_anti (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    {f : ℕ} [NeZero f] (hfm : f ∣ m) (hf3 : f = 3)
    {q : ℕ} (hq : q = 2 ∨ q = 3) (hE : eulerPrimes m f ⊆ {q})
    (x y t : ℕ) (hx : x ∈ fullPts p m a) (hy : y ∈ fullPts p m a) (hxy : x ≠ y)
    (hβ : (y : ZMod (p ^ r)) = x) (hxyf : x ≡ y [MOD f])
    (ht : t ∈ univ.image a) (hpt : ¬ p ∣ t) (hdt : dm m t = f) (htx : t ≠ x) (hty : t ≠ y)
    (hdie : ∀ w ∈ univ.image a, w ≠ x → w ≠ y → w ≠ t → ¬ p ∣ w → classSum a e w ≠ 0 →
      ¬ f ∣ dm m w)
    (hsep : let X := (x : ZMod (p ^ r)); let Q := (q : ZMod (p ^ r));
      let T := ((t / m.gcd t : ℕ) : ZMod (p ^ r));
      X * Q ≠ X ∧ X ≠ T ∧ -X ≠ X ∧ -X * Q ≠ X ∧ -X ≠ T ∧ T * Q ≠ X ∧ -T ≠ T ∧ -T * Q = X) :
    classSum a e t = 0 ∧ classSum a e x + classSum a e y = 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8⟩ := hsep
  set X : ZMod (p ^ r) := (x : ZMod (p ^ r))
  set Q : ZMod (p ^ r) := (q : ZMod (p ^ r))
  set bt := t / m.gcd t
  set T : ZMod (p ^ r) := (bt : ZMod (p ^ r))
  obtain ⟨η₀, hη₀⟩ := Erdos634.LemmaSGprime.exists_primitive (NeZero.ne f) (by rw [hf3]; norm_num)
  have hev : η₀ (-1) = -1 := by
    rcases η₀.even_or_odd with h | h
    · exfalso
      have hno := (Erdos634.LemmaSParity.exists_even_primitive_iff (d := f) (NeZero.ne f)
        (by rw [hf3]; norm_num)).1 ⟨η₀, hη₀, h⟩
      exact hno.1 hf3
    · exact h
  set η : DirichletCharacter ℂ m := changeLevel hfm η₀
  have hηc : η.conductor = f := conductor_changeLevel_of_isPrimitive hfm hη₀
  have hηev : η (-1) = -1 := by
    simp only [η, Erdos634.LemmaSG2.changeLevel_neg_one]; exact hev
  have hxf := mem_filter.1 hx
  have hyf := mem_filter.1 hy
  have hqP : q.Coprime (p ^ r) := Nat.Coprime.pow_right r
    ((Nat.coprime_primes (by rcases hq with rfl | rfl <;> norm_num) hp.out).2 (by omega))
  have hQu : IsUnit Q := (ZMod.isUnit_iff_coprime q _).2 hqP
  -- Euler factor as 1 − ψ⁻¹(q) c'
  set c' : ℂ := if q ∈ eulerPrimes m η.conductor then
    η.primitiveCharacter⁻¹ (q : ZMod η.conductor) else 0
  have hEul : ∀ ψ : DirichletCharacter ℂ (p ^ r),
      ∏ ℓ ∈ eulerPrimes m η.conductor,
        (1 - ψ⁻¹ (ℓ : ZMod (p ^ r)) * η.primitiveCharacter⁻¹ (ℓ : ZMod η.conductor))
        = 1 - ψ⁻¹ (q : ZMod (p ^ r)) * c' := by
    intro ψ
    have hE' : eulerPrimes m η.conductor ⊆ {q} := by rw [hηc]; exact hE
    rcases subset_singleton_iff.1 hE' with h0 | h1
    · rw [h0, prod_empty]; simp [c', h0]
    · rw [h1, prod_singleton]; simp [c', h1]
  -- the three surviving terms
  set wt : ℂ := (m.totient : ℂ) / (f.totient : ℂ)
  set A : ℂ := ((classSum a e x : ℚ) : ℂ) * η.primitiveCharacter (x : ZMod η.conductor) +
    ((classSum a e y : ℚ) : ℂ) * η.primitiveCharacter (y : ZMod η.conductor)
  set B : ℂ := ((classSum a e t : ℚ) : ℂ) * wt * η.primitiveCharacter (bt : ZMod η.conductor)
  have hcomp : ∀ ψ : DirichletCharacter ℂ (p ^ r), ψ.IsPrimitive → ψ (-1) = 1 →
      ∑ u : (ZMod (p ^ r))ˣ, ψ (u : ZMod (p ^ r)) * Phi2 A B c' X Q T u = 0 := by
    intro ψ hψ hψo
    have hodd : (chi ψ η).Odd := by
      show (chi ψ η) (-1) = -1
      rw [MulChar.coeToFun_mul, Pi.mul_apply,
        Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_right (p ^ r) m) ψ,
        Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_left m (p ^ r)) η, hψo, hηev, one_mul]
    have hsum := hP (chi ψ η) hodd (by rw [conductor_chi hpm hψ η]; exact Nat.dvd_mul_right _ _)
    rw [regroup, sum_coe_sort (univ.image a)
      (fun w => ((classSum a e w : ℚ) : ℂ) * bracket (chi ψ η) w)] at hsum
    have hsub : ({x, y, t} : Finset ℕ) ⊆ univ.image a := by
      intro w hw
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact hxf.1
      · exact hyf.1
      · exact ht
    rw [← sum_subset hsub (fun w hw hw' => by
      simp only [mem_insert, mem_singleton, not_or] at hw'
      obtain ⟨hwx, hwy, hwt⟩ := hw'
      by_cases hpw : p ∣ w
      · rw [bracket_p_dvd hr hpm hψ η w hpw, mul_zero]
      by_cases hEw : classSum a e w = 0
      · rw [hEw]; simp
      rw [bracket_unit hpm hψ η w hpw,
        if_neg (by rw [hηc]; exact hdie w hw hwx hwy hwt hpw hEw), mul_zero])] at hsum
    rw [sum_insert (by simp [hxy, htx.symm]), sum_insert (by simp [hty.symm]), sum_singleton]
      at hsum
    have hterm : ∀ s : ℕ, s ∈ fullPts p m a →
        bracket (chi ψ η) s = ψ (s : ZMod (p ^ r)) * η.primitiveCharacter (s : ZMod η.conductor) *
          (1 - ψ⁻¹ (q : ZMod (p ^ r)) * c') := by
      intro s hs
      have hsf := mem_filter.1 hs
      have hdm : dm m s = m := (dm_eq_iff s).2 hsf.2.2
      have hg : m.gcd s = 1 := Nat.coprime_comm.1 hsf.2.2
      rw [bracket_unit hpm hψ η s hsf.2.1, if_pos (by rw [hηc, hdm]; exact hfm), hg, Nat.div_one,
        hdm, hEul ψ,
        div_self (by exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne m))).ne'),
        one_mul]
    have htt : bracket (chi ψ η) t = wt * ψ T * η.primitiveCharacter (bt : ZMod η.conductor) := by
      rw [bracket_unit hpm hψ η t hpt, if_pos (by rw [hηc, hdt]), hdt]
      have hE0 : eulerPrimes f η.conductor = ∅ := by
        rw [hηc]; ext ℓ
        simp only [eulerPrimes, mem_filter, Nat.mem_primeFactors, Finset.notMem_empty, iff_false]
        rintro ⟨⟨-, h, -⟩, h'⟩; exact h' h
      rw [hE0, prod_empty, mul_one]
    rw [hterm x hx, hterm y hy, htt, hβ] at hsum
    rw [psi_Phi2 ψ A B c' X Q T hQu, MulChar.inv_apply_eq_inv' ψ] at *
    simp only [A, B]
    linear_combination hsum
  -- the antisymmetry Φ″ = −[−1]Φ″ (N±(iii) for r = 1, N(a) for r ≥ 2; η odd)
  obtain ⟨Qu, hQu'⟩ := id hQu
  have hY : ∀ w : ZMod (p ^ r), w * Q = X → w = -T := by
    intro w hw
    have : w * Q = -T * Q := by rw [hw, hs8]
    rw [← hQu'] at this
    exact (Units.mul_left_inj Qu).1 this
  have hsupp : ∀ v : (ZMod (p ^ r))ˣ, Phi2 A B c' X Q T v ≠ 0 →
      (v : ZMod (p ^ r)) = X ∨ (v : ZMod (p ^ r)) = -T ∨ (v : ZMod (p ^ r)) = T := by
    intro v hv
    by_contra hc; push Not at hc
    apply hv; unfold Phi2
    rw [if_neg hc.1, if_neg (fun h' => hc.2.1 (hY _ h')), if_neg hc.2.2]; ring
  set S4 : Finset (ZMod (p ^ r)) := {X, -T, T, -X}
  have h4 : S4.card ≤ 4 := by
    refine (card_insert_le _ _).trans ?_
    refine Nat.succ_le_succ ((card_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((card_insert_le _ _).trans ?_)
    simp
  have hmapS : ∀ v : (ZMod (p ^ r))ˣ, (Phi2 A B c' X Q T v ≠ 0 ∨ Phi2 A B c' X Q T (-v) ≠ 0) →
      (v : ZMod (p ^ r)) ∈ S4 := by
    intro v hv
    simp only [S4, mem_insert, mem_singleton]
    rcases hv with h | h
    · rcases hsupp v h with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr (Or.inl h1))
    · rcases hsupp (-v) h with h1 | h1 | h1 <;> simp only [Units.val_neg] at h1
      · right; right; right; rw [← h1, neg_neg]
      · right; right; left; rw [← neg_neg (v : ZMod (p ^ r)), h1, neg_neg]
      · right; left; rw [← h1, neg_neg]
  have hanti : ∀ u, Phi2 A B c' X Q T u = -Phi2 A B c' X Q T (-u) := by
    rcases Nat.lt_or_ge r 2 with h1 | h2
    · obtain rfl : r = 1 := by omega
      refine Erdos634.LemmaSN.lemmaN_c _ hcomp ?_
      refine lt_of_le_of_lt ?_ (show 4 < p - 1 by omega)
      refine le_trans (card_le_card_of_injOn (fun v : (ZMod (p ^ 1))ˣ => (v : ZMod (p ^ 1)))
        (t := S4) (fun v hv => ?_) (fun v _ w _ h => Units.ext h)) h4
      have hv' := (mem_filter.1 hv).2
      apply hmapS
      by_contra hc; push Not at hc; apply hv'; rw [hc.1, hc.2, add_zero]
    · intro u
      have := lemmaN_a hr (Phi2 A B c' X Q T) (Or.inl rfl) hcomp (fun u => ?_) u
      · rw [this]; ring
      rw [card_N hr, if_neg (by omega)]
      refine lt_of_le_of_lt ?_ (show 4 < p by omega)
      refine le_trans (card_le_card_of_injOn (fun v : (ZMod (p ^ r))ˣ => (v : ZMod (p ^ r)))
        (t := S4) (fun v hv => hmapS v (mem_filter.1 hv).2.2) (fun v _ w _ h => Units.ext h)) h4
  -- evaluations
  have hxP : x.Coprime (p ^ r) :=
    Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hxf.2.1).symm
  have hbtP : bt.Coprime (p ^ r) :=
    Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2
      (fun h => hpt (dvd_trans h (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right m t))))).symm
  set uX : (ZMod (p ^ r))ˣ := ZMod.unitOfCoprime x hxP
  set uT : (ZMod (p ^ r))ˣ := ZMod.unitOfCoprime bt hbtP
  have huX : (uX : ZMod (p ^ r)) = X := ZMod.coe_unitOfCoprime x hxP
  have huT : (uT : ZMod (p ^ r)) = T := ZMod.coe_unitOfCoprime bt hbtP
  have hA : A = 0 := by
    have h := hanti uX
    unfold Phi2 at h
    simp only [Units.val_neg, huX] at h
    rw [if_pos trivial, if_neg hs1, if_neg hs2, if_neg hs3, if_neg hs4, if_neg hs5] at h
    linear_combination h
  have hB : B = 0 := by
    have h := hanti uT
    unfold Phi2 at h
    simp only [Units.val_neg, huT, hA, zero_mul, zero_sub, mul_zero, neg_zero, zero_add] at h
    rw [if_pos trivial, if_neg hs7] at h
    linear_combination h
  -- read off E_t and E_x + E_y
  have hgpos : 0 < m.gcd t := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne m))
  have hbtf : bt.Coprime η.conductor := by
    rw [hηc, ← hdt]; exact (Nat.coprime_div_gcd_div_gcd hgpos).symm
  have hwt : wt ≠ 0 := div_ne_zero
    (by exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne m))).ne')
    (by exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne f))).ne')
  have hEt : classSum a e t = 0 := by
    have := (mul_eq_zero.1 hB).resolve_right (primChar_ne_zero η bt hbtf)
    exact_mod_cast (mul_eq_zero.1 this).resolve_right hwt
  have hxc : x.Coprime η.conductor := by rw [hηc]; exact hxf.2.2.coprime_dvd_right hfm
  have hxy' : (x : ZMod η.conductor) = (y : ZMod η.conductor) := by
    rw [ZMod.natCast_eq_natCast_iff, hηc]; exact hxyf
  simp only [A, ← hxy'] at hA
  have : ((classSum a e x + classSum a e y : ℚ) : ℂ) *
      η.primitiveCharacter (x : ZMod η.conductor) = 0 := by push_cast; linear_combination hA
  exact ⟨hEt, by exact_mod_cast (mul_eq_zero.1 this).resolve_right (primChar_ne_zero η x hxc)⟩

/-- **R2b, f₂ = 3** (m = 12): ⟹ e_j = e_k = e_l = 0. -/
theorem lemmaR2b_12 (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) {m' : ℕ} (hm : m = 4 * m')
    (hm'3 : m' = 3)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (x y t : ℕ) (himg : univ.image a = {x, y, t}) (hsum : x + y + t = p ^ r * m)
    (hpx : ¬ p ∣ x) (hpy : ¬ p ∣ y) (hpt : ¬ p ∣ t) (hxm : x.Coprime m) (hym : y.Coprime m)
    (hgt : m.gcd t = 4) (hxy : x ≠ y) (hβ : (y : ZMod (p ^ r)) = x)
    (hxym' : x ≡ y [MOD m']) (hxy4 : ¬ x ≡ y [MOD 4]) :
    classSum a e x = 0 ∧ classSum a e y = 0 ∧ classSum a e t = 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  haveI : Fact (1 < p ^ r) := ⟨Nat.one_lt_pow (by omega) (by omega)⟩
  have hm'odd : m' % 2 = 1 := by omega
  have hm'0 : m' ≠ 0 := by omega
  haveI : NeZero m' := ⟨hm'0⟩
  have htm : ¬ t.Coprime m := fun h => by rw [Nat.coprime_comm] at h; rw [h] at hgt; omega
  obtain ⟨hx, hy, hsep, hN, hdie⟩ := setup3 hp7 hr a e x y t himg hpx hpy hxm hym htm hβ
  have hEq := top_equal hp7 hr hpm (by omega) (q := 2) (v := 2) (m' := m') Nat.prime_two
    (by norm_num) (by rw [hm]; norm_num) (by omega) a e hP x y hx hy hxy hβ hsep hN hxym'
    (by norm_num; exact hxy4)
  have hdt : dm m t = m' := by
    rw [dm, hgt, hm, Nat.mul_div_cancel_left _ (by norm_num)]
  have htx : t ≠ x := fun h => by rw [h, Nat.Coprime.gcd_eq_one (Nat.coprime_comm.1 hxm)] at hgt; omega
  have hty : t ≠ y := fun h => by rw [h, Nat.Coprime.gcd_eq_one (Nat.coprime_comm.1 hym)] at hgt; omega
  have hE : eulerPrimes m m' ⊆ {2} := fun ℓ hl => mem_singleton.2
    (Erdos634.LemmaSL.euler_sub (v := 2) (v' := 0) Nat.prime_two
      (by rw [pow_zero, one_mul, show (2 : ℕ) ^ 2 * m' = m by rw [hm]; norm_num]; exact hl))
  have hX : IsUnit ((x : ℕ) : ZMod (p ^ r)) := (ZMod.isUnit_iff_coprime x _).2
    (Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hpx).symm)
  have hT : (x : ZMod (p ^ r)) + 2 * ((t / m.gcd t : ℕ) : ZMod (p ^ r)) = 0 := by
    have h4t : t / m.gcd t * 4 = t := by rw [hgt]; exact Nat.div_mul_cancel (hgt ▸ Nat.gcd_dvd_right m t)
    have hs : ((x + y + t : ℕ) : ZMod (p ^ r)) = 0 := by
      rw [hsum, Nat.cast_mul, ZMod.natCast_self, zero_mul]
    rw [← h4t] at hs; push_cast at hs; rw [hβ] at hs
    have h2 : IsUnit ((2 : ℕ) : ZMod (p ^ r)) :=
      (ZMod.isUnit_iff_coprime 2 _).2 (small_cop (by norm_num) (by norm_num) hp7)
    push_cast at h2
    exact (h2.mul_right_eq_zero).1 (by linear_combination hs)
  obtain ⟨hEt, hExy⟩ := level2_three_anti hp7 hr hpm a e hP (f := m') (by rw [hm]; exact Nat.dvd_mul_left _ _)
    hm'3 (Or.inl rfl) hE x y t hx hy hxy hβ hxym'
    ((by rw [himg]; simp)) hpt hdt htx hty (fun w hw h1 h2 h4 _ _ _ => (hdie w hw h1 h2 h4).elim)
    (by
      intro X Q T
      have c1 := kX_ne hX 1 (small_cop (by norm_num) (by norm_num) hp7)
      have c2 := kX_ne hX 2 (small_cop (by norm_num) (by norm_num) hp7)
      have c3 := kX_ne hX 3 (small_cop (by norm_num) (by norm_num) hp7)
      push_cast at c1 c2 c3
      refine ⟨fun h => c1 (by linear_combination h), fun h => c3 (by linear_combination 2 * h + hT),
        fun h => c2 (by linear_combination -h), fun h => c3 (by linear_combination -h),
        fun h => c1 (by linear_combination -hT - 2 * h), fun h => c2 (by linear_combination hT - h),
        fun h => c1 (by linear_combination hT + h), by linear_combination -hT⟩)
  have hx0 : classSum a e x = 0 := by linarith
  exact ⟨hx0, by linarith, hEt⟩

end L3

/-! ## Consequence: n = 84 = 7·12, a = (1, 43, 40): 43 ≡ 1 (mod 7) (same β), 1 ≡ 43 (mod 3),
1 ≢ 43 (mod 4), gcd(12, 40) = 4 (d_l = 3). Every e satisfying Lemma P's hypothesis has all class
sums zero. -/
theorem consequence_R2b_84 (e : Fin 3 → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (7 ^ 1 * 12), χ.Odd → 7 ^ 1 ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ ((![1, 43, 40] : Fin 3 → ℕ) j) = 0) :
    classSum ![1, 43, 40] e 1 = 0 ∧ classSum ![1, 43, 40] e 43 = 0 ∧
      classSum ![1, 43, 40] e 40 = 0 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact lemmaR2b_12 (p := 7) (r := 1) (m := 12) (m' := 3) (by norm_num) le_rfl (by norm_num)
    (by norm_num) rfl _ e hP 1 43 40 (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide)

#print axioms Erdos634.LemmaSR2b12.level2_three_anti
#print axioms Erdos634.LemmaSR2b12.lemmaR2b_12
#print axioms Erdos634.LemmaSR2b12.consequence_R2b_84

end Erdos634.LemmaSR2b12
