/-
Lemma S, node A5: **R3 and R2b** (round 2, PROOF_round2.md §4.6, class R1F2o), with the common
level-f₂ step.

  Setup. F = {j, k} with β_j = β_k = β, and l ∈ I∖F with β_l = −2β. The top level gives
  g = γ_j/γ_k ∈ Sp(m_I) with τ(g) = 1, and e_j = e_k.
  R3: q = 3, m_I odd, 3 ∥ m_I, g₃ = −1, d_l = m_I/3. f₂ = m_I/3; Φ″ = A(1 − η̄(3)[⅓])[1] + B[−⅔].
      S+ (η even; f₂ ≠ 3 since 3 ∤ f₂) or N±(i): coefficient at 1 is A, and −1 ∉ supp (p ≥ 7).
      So A = 0, then B = 0.
  R2b: q = 2, 4 ∥ m_I, g₂ = −1 mod 4, d_l = m_I/4. f₂ = m_I/4; Φ″ = A[1] − Aη̄(2)[½] + B[−½].
      S+ gives A = 0, then B = 0. [f₂ = 3 (m_I = 12) uses N±(iii) — NOT formalized here.]
  A = w(c_j + c_k) = w(e_j + e_k)η(γ_k) (g ≡ 1 mod f₂), B = w_l c_l. A = 0 gives e_j = −e_k,
  which with e_j = e_k gives e_j = e_k = 0. B = 0 gives e_l = 0.

Encoding (class form): the pair x ≠ y (full, y ≡ x mod p^r), the third point t (p ∤ t,
d_t = f₂); b_t = t / gcd(m, t) is its numerator; "S+" is N(b) for r = 1 and N(a) (6 points < p) for
r ≥ 2, with η even primitive mod f₂ (LemmaSParity). The generic step is `level2_three`; its
separation hypotheses are the "−1 ∉ supp" facts, checked for R3/R2b from 3T = −2X, 2T = −X.
Formalization debt, not /goal progress.
-/
import Mathlib
import Erdos634.Draft.LemmaSL

open scoped BigOperators
open Finset

namespace Erdos634.LemmaSR3

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi (chi dm conductor_chi bracket_p_dvd bracket_unit sum_indicator)
open Erdos634.LemmaSElim (classSum regroup)
open Erdos634.LemmaSFC (fullPts dm_eq_iff card_val_le_one card_N)
open Erdos634.LemmaSN (pred_dvd lemmaN_a lemmaN_b)
open Erdos634.LemmaSIso (conductor_changeLevel_of_isPrimitive primChar_ne_zero)

/-- Φ″ ∈ ℂ[𝒢]: A[X] − A c [X/Q] + B[T]. -/
noncomputable def Phi2 {P : ℕ} (A B c : ℂ) (X Q T : ZMod P) (u : (ZMod P)ˣ) : ℂ :=
  A * (if (u : ZMod P) = X then 1 else 0) - A * c * (if (u : ZMod P) * Q = X then 1 else 0) +
    B * (if (u : ZMod P) = T then 1 else 0)

theorem psi_Phi2 {P : ℕ} [NeZero P] (ψ : DirichletCharacter ℂ P) (A B c : ℂ) (X Q T : ZMod P)
    (hQ : IsUnit Q) :
    ∑ u : (ZMod P)ˣ, ψ (u : ZMod P) * Phi2 A B c X Q T u =
      A * ψ X - A * c * (ψ X * (ψ Q)⁻¹) + B * ψ T := by
  have h1 := sum_indicator ψ 1 X isUnit_one
  have hQ' := sum_indicator ψ Q X hQ
  have hT := sum_indicator ψ 1 T isUnit_one
  simp only [mul_one, map_one, inv_one] at h1 hT
  unfold Phi2
  simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
  rw [← hQ', ← h1, ← hT, mul_sum, mul_sum, mul_sum]
  congr 1; congr 1
  all_goals refine sum_congr rfl (fun u _ => by ring)

section L2
variable {p r m : ℕ} [hp : Fact p.Prime] [NeZero m]

/-- **The level-f₂ step** (R3/R2b): E_t = 0 and E_x + E_y = 0. -/
theorem level2_three (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    {f : ℕ} [NeZero f] (hfm : f ∣ m) (hf4 : f % 4 ≠ 2) (hf34 : f ≠ 3 ∧ f ≠ 4)
    {q : ℕ} (hq : q = 2 ∨ q = 3) (hE : eulerPrimes m f ⊆ {q})
    (x y t : ℕ) (hx : x ∈ fullPts p m a) (hy : y ∈ fullPts p m a) (hxy : x ≠ y)
    (hβ : (y : ZMod (p ^ r)) = x) (hxyf : x ≡ y [MOD f])
    (ht : t ∈ univ.image a) (hpt : ¬ p ∣ t) (hdt : dm m t = f) (htx : t ≠ x) (hty : t ≠ y)
    (hdie : ∀ w ∈ univ.image a, w ≠ x → w ≠ y → w ≠ t → ¬ p ∣ w → classSum a e w ≠ 0 →
      ¬ f ∣ dm m w)
    (hsep : let X := (x : ZMod (p ^ r)); let Q := (q : ZMod (p ^ r));
      let T := ((t / m.gcd t : ℕ) : ZMod (p ^ r));
      X * Q ≠ X ∧ X ≠ T ∧ -X ≠ X ∧ -X * Q ≠ X ∧ -X ≠ T ∧ T * Q ≠ X ∧ -T ≠ T) :
    classSum a e t = 0 ∧ classSum a e x + classSum a e y = 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hs7⟩ := hsep
  set X : ZMod (p ^ r) := (x : ZMod (p ^ r))
  set Q : ZMod (p ^ r) := (q : ZMod (p ^ r))
  set bt := t / m.gcd t
  set T : ZMod (p ^ r) := (bt : ZMod (p ^ r))
  obtain ⟨η₀, hη₀, hev⟩ := (Erdos634.LemmaSParity.exists_even_primitive_iff (NeZero.ne f) hf4).2 hf34
  set η : DirichletCharacter ℂ m := changeLevel hfm η₀
  have hηc : η.conductor = f := conductor_changeLevel_of_isPrimitive hfm hη₀
  have hηev : η (-1) = 1 := by
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
  have hcomp : ∀ ψ : DirichletCharacter ℂ (p ^ r), ψ.IsPrimitive → ψ (-1) = -1 →
      ∑ u : (ZMod (p ^ r))ˣ, ψ (u : ZMod (p ^ r)) * Phi2 A B c' X Q T u = 0 := by
    intro ψ hψ hψo
    have hodd : (chi ψ η).Odd := by
      show (chi ψ η) (-1) = -1
      rw [MulChar.coeToFun_mul, Pi.mul_apply,
        Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_right (p ^ r) m) ψ,
        Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_left m (p ^ r)) η, hψo, hηev, mul_one]
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
  -- the symmetry Φ″ = [−1]Φ″
  have hsym : ∀ u, Phi2 A B c' X Q T u = Phi2 A B c' X Q T (-u) := by
    rcases Nat.lt_or_ge r 2 with h1 | h2
    · obtain rfl : r = 1 := by omega
      exact lemmaN_b _ hcomp
    · intro u
      have := lemmaN_a hr (Phi2 A B c' X Q T) (Or.inr rfl) hcomp (fun u => ?_) u
      · rw [this]; ring
      rw [card_N hr, if_neg (by omega)]
      obtain ⟨Qu, hQu'⟩ := id hQu
      set Y : ZMod (p ^ r) := X * ((Qu⁻¹ : (ZMod (p ^ r))ˣ) : ZMod (p ^ r))
      have hY : ∀ w : ZMod (p ^ r), w * Q = X → w = Y := by
        intro w hw
        simp only [Y, ← hw, ← hQu', mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
      set S6 : Finset (ZMod (p ^ r)) := {X, Y, T, -X, -Y, -T}
      have h6 : S6.card ≤ 6 := by
        refine (card_insert_le _ _).trans ?_
        refine Nat.succ_le_succ ((card_insert_le _ _).trans ?_)
        refine Nat.succ_le_succ ((card_insert_le _ _).trans ?_)
        refine Nat.succ_le_succ ((card_insert_le _ _).trans ?_)
        refine Nat.succ_le_succ ((card_insert_le _ _).trans ?_)
        simp
      refine lt_of_le_of_lt ?_ (show 6 < p by omega)
      refine le_trans (card_le_card_of_injOn (fun v : (ZMod (p ^ r))ˣ => (v : ZMod (p ^ r)))
        (t := S6) (fun v hv => ?_) (fun v _ w _ h => Units.ext h)) h6
      have hv' := (mem_filter.1 hv).2.2
      simp only [S6, coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
      unfold Phi2 at hv'
      rcases hv' with h | h
      · by_contra hc; push Not at hc; apply h
        rw [if_neg hc.1, if_neg (fun h' => hc.2.1 (hY _ h')), if_neg hc.2.2.1]; ring
      · by_contra hc; push Not at hc; apply h
        simp only [Units.val_neg]
        rw [if_neg (fun h' => hc.2.2.2.1 (by rw [← h', neg_neg])),
          if_neg (fun h' => hc.2.2.2.2.1 (by rw [← hY _ h', neg_neg])),
          if_neg (fun h' => hc.2.2.2.2.2 (by rw [← h', neg_neg]))]; ring
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
    have h := hsym uX
    unfold Phi2 at h
    simp only [Units.val_neg, huX] at h
    rw [if_pos trivial, if_neg hs1, if_neg hs2, if_neg hs3, if_neg hs4, if_neg hs5] at h
    linear_combination h
  have hB : B = 0 := by
    have h := hsym uT
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

/-- τ vanishes when g ≡ 1. -/
theorem tau_eq_zero {d : ℕ} {z : ℤ} (hz : z ≡ 1 [ZMOD d]) : Erdos634.LemmaSGprime.tau d z = 0 := by
  classical
  unfold Erdos634.LemmaSGprime.tau
  rw [card_eq_zero, filter_eq_empty_iff]
  intro q _ h
  apply h
  exact hz.of_dvd (by exact_mod_cast Nat.ordProj_dvd d q)

/-- A unit times a small integer prime to p is nonzero mod p^r. -/
theorem kX_ne {P : ℕ} [Fact (1 < P)] {X : ZMod P} (hX : IsUnit X) (k : ℕ) (hk : k.Coprime P) :
    (k : ZMod P) * X ≠ 0 :=
  (((ZMod.isUnit_iff_coprime k P).2 hk).mul hX).ne_zero

/-- **The top level for R1F2o** (round 2 §4.6 Setup): g ∈ Sp(m) with τ(g) = 1 gives e_j = e_k. -/
theorem top_equal (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (hm4 : m % 4 ≠ 2)
    {q v m' : ℕ} (hq : q.Prime) (hv : 1 ≤ v) (hm : m = q ^ v * m') (hqm' : ¬ q ∣ m')
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (x y : ℕ) (hx : x ∈ fullPts p m a) (hy : y ∈ fullPts p m a) (hxy : x ≠ y)
    (hβ : (y : ZMod (p ^ r)) = x)
    (hsep : ∀ w ∈ fullPts p m a, w ≠ x → w ≠ y → classSum a e w ≠ 0 →
      (w : ZMod (p ^ r)) ≠ x ∧ (w : ZMod (p ^ r)) ≠ -x)
    (hN : 2 * ((fullPts p m a).image (fun y : ℕ => (y : ZMod (p ^ r)))).card <
      (univ.filter (fun v : (ZMod (p ^ r))ˣ => ZMod.unitsMap (pred_dvd p r) v = 1)).card)
    (hxym' : x ≡ y [MOD m']) (hxyq : ¬ x ≡ y [MOD q ^ v]) :
    classSum a e y = classSum a e x := by
  have hxf := mem_filter.1 hx
  have hyf := mem_filter.1 hy
  have hm'0 : m' ≠ 0 := by rintro rfl; rw [mul_zero] at hm; exact NeZero.ne m hm
  haveI : NeZero m' := ⟨hm'0⟩
  set z : ℤ := (((x : ZMod m) * (y : ZMod m)⁻¹).val : ℤ)
  have hzm : ((z : ℤ) : ZMod m) * (y : ZMod m) = x := by
    simp only [z, Int.cast_natCast, ZMod.natCast_zmod_val, mul_assoc]
    rw [mul_comm ((y : ZMod m))⁻¹, ZMod.coe_mul_inv_eq_one y hyf.2.2, mul_one]
  have hz : z * (1 * y) ≡ x [ZMOD m] := by
    rw [← ZMod.intCast_eq_intCast_iff]; push_cast; rw [one_mul]; exact hzm
  have hkey := Erdos634.LemmaSL.fc_key hp7 hr hpm a e hP x y hx hy hxy 1 (Or.inl rfl) (by rw [hβ]; push_cast; ring)
    hsep hN
  rcases Erdos634.LemmaSL.rel_Gprime hm4 _ _ x y hxf.2.2 hyf.2.2 1 (Or.inl rfl) z hz hkey with
    ⟨h1, h2⟩ | ⟨-, hrel⟩
  · rw [h1, h2]
  -- τ(g) = 1
  have hcop : (q ^ v).Coprime m' := Nat.Coprime.pow_left v ((Nat.Prime.coprime_iff_not_dvd hq).2 hqm')
  have hzq : ¬ z ≡ 1 [ZMOD (q : ℤ) ^ v] := by
    intro h
    apply hxyq
    have h1 : ((z : ℤ) : ZMod (q ^ v)) = 1 := by
      rw [← Int.cast_one, ZMod.intCast_eq_intCast_iff]; push_cast; exact h
    have h2 : ((z : ℤ) : ZMod (q ^ v)) * (y : ZMod (q ^ v)) = x := by
      have := congrArg (ZMod.castHom (show q ^ v ∣ m by rw [hm]; exact Nat.dvd_mul_right _ _)
        (ZMod (q ^ v))) hzm
      rwa [map_mul, map_intCast, map_natCast, map_natCast] at this
    rw [h1, one_mul] at h2
    exact ((ZMod.natCast_eq_natCast_iff _ _ _).1 h2).symm
  have hzm' : z ≡ 1 [ZMOD m'] := by
    have h2 : ((z : ℤ) : ZMod m') * (y : ZMod m') = x := by
      have := congrArg (ZMod.castHom (show m' ∣ m by rw [hm]; exact Nat.dvd_mul_left _ _)
        (ZMod m')) hzm
      rwa [map_mul, map_intCast, map_natCast, map_natCast] at this
    have hxy' : (x : ZMod m') = y := (ZMod.natCast_eq_natCast_iff _ _ _).2 hxym'
    rw [hxy'] at h2
    have hyu : IsUnit (y : ZMod m') :=
      (ZMod.isUnit_iff_coprime y m').2 (hyf.2.2.coprime_dvd_right (by rw [hm]; exact Nat.dvd_mul_left _ _))
    have : ((z : ℤ) : ZMod m') = 1 := by
      obtain ⟨u, hu⟩ := hyu
      rw [← hu] at h2
      have := congrArg (· * ((u⁻¹ : (ZMod m')ˣ) : ZMod m')) h2
      simpa [mul_assoc] using this
    rw [← ZMod.intCast_eq_intCast_iff, this, Int.cast_one]
  have htau : Erdos634.LemmaSGprime.tau m z = 1 := by
    rw [hm, Erdos634.LemmaSGprime.tau_mul hcop (pow_ne_zero _ hq.ne_zero) hm'0,
      Erdos634.LemmaSGprime.tau_pp hq (by omega), if_neg hzq, tau_eq_zero hzm']
  rw [hrel, htau]; push_cast; ring

/-- Common bookkeeping for a datum whose points are exactly x, y (full) and t (not full). -/
theorem setup3 (hp7 : 7 ≤ p) (hr : 1 ≤ r) {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ)
    (e : ι → ℚ) (x y t : ℕ) (himg : univ.image a = {x, y, t}) (hpx : ¬ p ∣ x) (hpy : ¬ p ∣ y)
    (hxm : x.Coprime m) (hym : y.Coprime m) (htm : ¬ t.Coprime m) (hβ : (y : ZMod (p ^ r)) = x) :
    x ∈ fullPts p m a ∧ y ∈ fullPts p m a ∧
    (∀ w ∈ fullPts p m a, w ≠ x → w ≠ y → classSum a e w ≠ 0 →
      (w : ZMod (p ^ r)) ≠ x ∧ (w : ZMod (p ^ r)) ≠ -x) ∧
    (2 * ((fullPts p m a).image (fun y : ℕ => (y : ZMod (p ^ r)))).card <
      (univ.filter (fun v : (ZMod (p ^ r))ˣ => ZMod.unitsMap (pred_dvd p r) v = 1)).card) ∧
    (∀ w ∈ univ.image a, w ≠ x → w ≠ y → w ≠ t → False) := by
  have hmem : ∀ w, w ∈ univ.image a ↔ w = x ∨ w = y ∨ w = t := by
    intro w; rw [himg]; simp
  have hsub : ∀ w ∈ fullPts p m a, w = x ∨ w = y := by
    intro w hw
    have hwf := mem_filter.1 hw
    rcases (hmem w).1 hwf.1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · subst h; exact absurd hwf.2.2 htm
  refine ⟨mem_filter.2 ⟨(hmem x).2 (Or.inl rfl), hpx, hxm⟩,
    mem_filter.2 ⟨(hmem y).2 (Or.inr (Or.inl rfl)), hpy, hym⟩, ?_, ?_, ?_⟩
  · intro w hw hwx hwy
    rcases hsub w hw with h | h <;> contradiction
  · have hc : ((fullPts p m a).image (fun y : ℕ => (y : ZMod (p ^ r)))).card ≤ 1 := by
      refine card_le_one.2 (fun u hu v hv => ?_)
      obtain ⟨w1, hw1, rfl⟩ := mem_image.1 hu
      obtain ⟨w2, hw2, rfl⟩ := mem_image.1 hv
      rcases hsub w1 hw1 with rfl | rfl <;> rcases hsub w2 hw2 with rfl | rfl <;>
        simp [hβ]
    rw [card_N hr]
    split_ifs <;> omega
  · intro w hw hwx hwy hwt
    rcases (hmem w).1 hw with h | h | h <;> contradiction

theorem small_cop {k : ℕ} (hk : 0 < k) (hk7 : k < 7) (hp7 : 7 ≤ p) : k.Coprime (p ^ r) :=
  Nat.Coprime.pow_right r (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2
    (fun h => by have := Nat.le_of_dvd hk h; omega)))

/-- **R3** (round 2 §4.6): q = 3, m odd, 3 ∥ m, g₃ = −1, d_l = m/3 ⟹ e_j = e_k = e_l = 0. -/
theorem lemmaR3 (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) {m' : ℕ} (hm : m = 3 * m')
    (h3 : ¬ 3 ∣ m') (hmodd : m % 2 = 1)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (x y t : ℕ) (himg : univ.image a = {x, y, t}) (hsum : x + y + t = p ^ r * m)
    (hpx : ¬ p ∣ x) (hpy : ¬ p ∣ y) (hpt : ¬ p ∣ t) (hxm : x.Coprime m) (hym : y.Coprime m)
    (hgt : m.gcd t = 3) (hxy : x ≠ y) (hβ : (y : ZMod (p ^ r)) = x)
    (hxym' : x ≡ y [MOD m']) (hxy3 : ¬ x ≡ y [MOD 3]) :
    classSum a e x = 0 ∧ classSum a e y = 0 ∧ classSum a e t = 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  haveI : Fact (1 < p ^ r) := ⟨Nat.one_lt_pow (by omega) (by omega)⟩
  have hm'0 : m' ≠ 0 := by rintro rfl; rw [mul_zero] at hm; exact NeZero.ne m hm
  haveI : NeZero m' := ⟨hm'0⟩
  have hm'odd : m' % 2 = 1 := by omega
  have htm : ¬ t.Coprime m := fun h => by rw [Nat.coprime_comm] at h; rw [h] at hgt; omega
  obtain ⟨hx, hy, hsep, hN, hdie⟩ := setup3 hp7 hr a e x y t himg hpx hpy hxm hym htm hβ
  have hEq := top_equal hp7 hr hpm (by omega) (q := 3) (v := 1) (m' := m') Nat.prime_three le_rfl
    (by rw [hm, pow_one]) h3 a e hP x y hx hy hxy hβ hsep hN hxym' (by rwa [pow_one])
  have hdt : dm m t = m' := by
    rw [dm, hgt, hm, Nat.mul_div_cancel_left _ (by norm_num)]
  have htx : t ≠ x := fun h => by rw [h, Nat.Coprime.gcd_eq_one (Nat.coprime_comm.1 hxm)] at hgt; omega
  have hty : t ≠ y := fun h => by rw [h, Nat.Coprime.gcd_eq_one (Nat.coprime_comm.1 hym)] at hgt; omega
  have hE : eulerPrimes m m' ⊆ {3} := fun ℓ hl => mem_singleton.2
    (Erdos634.LemmaSL.euler_sub (v := 1) (v' := 0) Nat.prime_three
      (by rwa [pow_one, pow_zero, one_mul, ← hm]))
  have hX : IsUnit ((x : ℕ) : ZMod (p ^ r)) := (ZMod.isUnit_iff_coprime x _).2
    (Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hpx).symm)
  have hT : (3 : ZMod (p ^ r)) * ((t / m.gcd t : ℕ) : ZMod (p ^ r)) + 2 * (x : ZMod (p ^ r)) = 0 := by
    have h3t : t / m.gcd t * 3 = t := by rw [hgt]; exact Nat.div_mul_cancel (hgt ▸ Nat.gcd_dvd_right m t)
    have hs : ((x + y + t : ℕ) : ZMod (p ^ r)) = 0 := by
      rw [hsum, Nat.cast_mul, ZMod.natCast_self, zero_mul]
    rw [← h3t] at hs; push_cast at hs; rw [hβ] at hs
    linear_combination hs
  obtain ⟨hEt, hExy⟩ := level2_three hp7 hr hpm a e hP (f := m') (by rw [hm]; exact Nat.dvd_mul_left _ _)
    (by omega) ⟨fun h => h3 (by rw [h]), by omega⟩ (Or.inr rfl) hE x y t hx hy hxy hβ hxym'
    ((by rw [himg]; simp)) hpt hdt htx hty (fun w hw h1 h2 h4 _ _ _ => (hdie w hw h1 h2 h4).elim)
    (by
      intro X Q T
      have c1 := kX_ne hX 1 (small_cop (by norm_num) (by norm_num) hp7)
      have c2 := kX_ne hX 2 (small_cop (by norm_num) (by norm_num) hp7)
      have c3 := kX_ne hX 3 (small_cop (by norm_num) (by norm_num) hp7)
      have c4 := kX_ne hX 4 (small_cop (by norm_num) (by norm_num) hp7)
      have c5 := kX_ne hX 5 (small_cop (by norm_num) (by norm_num) hp7)
      push_cast at c1 c2 c3 c4 c5
      refine ⟨fun h => c2 (by linear_combination h), fun h => c5 (by linear_combination 3 * h + hT),
        fun h => c2 (by linear_combination -h), fun h => c4 (by linear_combination -h),
        fun h => c1 (by linear_combination -hT - 3 * h), fun h => c3 (by linear_combination hT - h),
        fun h => c4 (by linear_combination 2 * hT + 3 * h)⟩)
  have hx0 : classSum a e x = 0 := by linarith
  exact ⟨hx0, by linarith, hEt⟩

/-- **R2b** (round 2 §4.6): q = 2, 4 ∥ m, g₂ ≡ −1 (mod 4), d_l = m/4, f₂ = m/4 ≠ 3
⟹ e_j = e_k = e_l = 0. (The f₂ = 3 sub-case, m = 12, uses N±(iii) and is NOT covered.) -/
theorem lemmaR2b (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) {m' : ℕ} (hm : m = 4 * m')
    (hm'odd : m' % 2 = 1) (hm'3 : m' ≠ 3)
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
  obtain ⟨hEt, hExy⟩ := level2_three hp7 hr hpm a e hP (f := m') (by rw [hm]; exact Nat.dvd_mul_left _ _)
    (by omega) ⟨hm'3, by omega⟩ (Or.inl rfl) hE x y t hx hy hxy hβ hxym'
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
        fun h => c1 (by linear_combination hT + h)⟩)
  have hx0 : classSum a e x = 0 := by linarith
  exact ⟨hx0, by linarith, hEt⟩

end L2

/-! ## Genuine consequences.
R3: n = 105 = 7·15, a = (1, 71, 33): 71 ≡ 1 (mod 7) (same β), 1 ≡ 71 (mod 5), 1 ≢ 71 (mod 3)
(g₃ = −1, τ = 1), gcd(15, 33) = 3 (d_l = 5). R2b: n = 140 = 7·20, a = (1, 71, 68):
71 ≡ 1 (mod 35), 1 ≢ 71 (mod 4), gcd(20, 68) = 4 (d_l = 5). In both, EVERY e satisfying
Lemma P's hypothesis has all class sums zero. -/
theorem consequence_R3_105 (e : Fin 3 → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (7 ^ 1 * 15), χ.Odd → 7 ^ 1 ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ ((![1, 71, 33] : Fin 3 → ℕ) j) = 0) :
    classSum ![1, 71, 33] e 1 = 0 ∧ classSum ![1, 71, 33] e 71 = 0 ∧
      classSum ![1, 71, 33] e 33 = 0 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact lemmaR3 (p := 7) (r := 1) (m := 15) (m' := 5) (by norm_num) le_rfl (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) _ e hP 1 71 33 (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide)

theorem consequence_R2b_140 (e : Fin 3 → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (7 ^ 1 * 20), χ.Odd → 7 ^ 1 ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ ((![1, 71, 68] : Fin 3 → ℕ) j) = 0) :
    classSum ![1, 71, 68] e 1 = 0 ∧ classSum ![1, 71, 68] e 71 = 0 ∧
      classSum ![1, 71, 68] e 68 = 0 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact lemmaR2b (p := 7) (r := 1) (m := 20) (m' := 5) (by norm_num) le_rfl (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) _ e hP 1 71 68 (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide)

#print axioms Erdos634.LemmaSR3.level2_three
#print axioms Erdos634.LemmaSR3.lemmaR3
#print axioms Erdos634.LemmaSR3.lemmaR2b
#print axioms Erdos634.LemmaSR3.consequence_R3_105
#print axioms Erdos634.LemmaSR3.consequence_R2b_140

end Erdos634.LemmaSR3
