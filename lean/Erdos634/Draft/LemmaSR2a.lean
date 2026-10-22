/-
Lemma S, node A5: **R2a** (round 2, PROOF_round2.md §4.6, class R1F2o with q = 2, 8 | m_I).

  1. Sum relation. γ_j + γ_k + 2γ_l ≡ 0 (mod m_I). Hence h := −γ_l/γ_k ≡ 1 + 2^{v−2}
     (mod 2^{v−1}), h ≡ 1 at odd primes. So h ∈ Sp(m_I/2) and η(h) = −1 for every primitive η mod m_I/2.
  2. Conductor m_I/2. No Euler factors (4 | m_I/2). Each ψ gives
     ψ(m_Iβ)·[(e_j + e_k)η(γ_k) + 2ε e_l η(γ_l)] = 0. So e_k = e_l·η(h) = −e_l.
  3. Conductor f₃ = m_I/4 (16 | m_I) or m_I/8 (8 ∥ m_I, with a common Euler factor at 2 removed by
     Lemma G). Now h ≡ g ≡ 1 (mod f₃), so the same equation gives e_k = e_l.
  4. Hence e_j = e_k = e_l = 0.

Encoding (class form, as LemmaSR3): the pair x ≠ y full, y ≡ x (mod p^r), g = x/y with
g₂ = 1 + 2^{v−1} (x ≡ y(1 + 2^{v−1}) mod 2^v) and g ≡ 1 at odd primes (x ≡ y mod m'), m = 2^v m',
v ≥ 3; the third point t with gcd(m, t) = 2 (d_l = m/2), T = t/2. Step 3 is run at f₃ = m' for every
v ≥ 3 (for 16 | m this is m/2^v rather than the paper's m/4; the Euler factor at 2 is then common to
all surviving terms and is removed by Lemma G exactly as in the 8 ∥ m case).
Formalization debt, not /goal progress.
-/
import Mathlib
import Erdos634.Draft.LemmaSR3

open scoped BigOperators
open Finset

namespace Erdos634.LemmaSR2a

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi (chi dm conductor_chi bracket_p_dvd bracket_unit)
open Erdos634.LemmaSElim (classSum regroup)
open Erdos634.LemmaSFC (fullPts dm_eq_iff)
open Erdos634.LemmaSN (pred_dvd)
open Erdos634.LemmaSIso (conductor_changeLevel_of_isPrimitive primChar_ne_zero)
open Erdos634.LemmaSL (exists_good_psi primChar_lift euler_sub)
open Erdos634.LemmaSR3 (setup3 top_equal small_cop kX_ne tau_eq_zero)
open Erdos634.LemmaSGprime (Sp tau lemmaG' Sp_mul tau_mul Sp_pp tau_pp)

section R2a
variable {p r m : ℕ} [hp : Fact p.Prime] [NeZero m]

/-- **The single equation at a lower conductor f** (steps 2 and 3): with T ≡ −x (mod p^r) and the
Euler sets of the full points and of t equal and inside {2}, for every primitive η₀ mod f,
E_x η₀(x) + E_y η₀(y) − η₀(−1)·w_t·E_t·η₀(T) = 0, w_t = φ(m)/φ(d_t). -/
theorem level_eq (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    {f : ℕ} [NeZero f] (hfm : f ∣ m) (hE2 : eulerPrimes m f ⊆ {2})
    (x y t : ℕ) (hx : x ∈ fullPts p m a) (hy : y ∈ fullPts p m a) (hxy : x ≠ y)
    (hβ : (y : ZMod (p ^ r)) = x)
    (ht : t ∈ univ.image a) (hpt : ¬ p ∣ t) (htx : t ≠ x) (hty : t ≠ y)
    (hfd : f ∣ dm m t) (hEul : eulerPrimes (dm m t) f = eulerPrimes m f)
    (hbt : (t / m.gcd t).Coprime m)
    (hTX : ((t / m.gcd t : ℕ) : ZMod (p ^ r)) = -(x : ZMod (p ^ r)))
    (hdie : ∀ w ∈ univ.image a, w ≠ x → w ≠ y → w ≠ t → False) :
    ∀ η₀ : DirichletCharacter ℂ f, η₀.IsPrimitive →
      ((classSum a e x : ℚ) : ℂ) * η₀ (x : ZMod f) + ((classSum a e y : ℚ) : ℂ) * η₀ (y : ZMod f)
        - η₀ (-1) * ((m.totient : ℂ) / ((dm m t).totient : ℂ)) * ((classSum a e t : ℚ) : ℂ) *
          η₀ ((t / m.gcd t : ℕ) : ZMod f) = 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  intro η₀ hη₀
  set η : DirichletCharacter ℂ m := changeLevel hfm η₀
  have hηc : η.conductor = f := conductor_changeLevel_of_isPrimitive hfm hη₀
  set ε : ℂ := -η (-1)
  have hε : ε = 1 ∨ ε = -1 := by
    rcases η.even_or_odd with h | h
    · right; simp only [ε, show η (-1) = 1 from h]
    · left; simp only [ε, show η (-1) = -1 from h, neg_neg]
  have hη2 : η (-1) * η (-1) = 1 := by
    rcases η.even_or_odd with h | h
    · rw [show η (-1) = 1 from h]; ring
    · rw [show η (-1) = -1 from h]; ring
  have hηm1 : η (-1) = η₀ (-1) := by simp only [η, Erdos634.LemmaSG2.changeLevel_neg_one]
  have hE' : eulerPrimes m η.conductor ⊆ {2} := by rw [hηc]; exact hE2
  obtain ⟨ψ, hψ, hψε, hEul0⟩ := exists_good_psi hp7 hr hε (Or.inl rfl) (eulerPrimes m η.conductor) hE'
    (fun ℓ => η.primitiveCharacter⁻¹ (ℓ : ZMod η.conductor))
  set Eul := ∏ ℓ ∈ eulerPrimes m η.conductor,
    (1 - ψ⁻¹ (ℓ : ZMod (p ^ r)) * η.primitiveCharacter⁻¹ (ℓ : ZMod η.conductor))
  have hodd : (chi ψ η).Odd := by
    show (chi ψ η) (-1) = -1
    rw [MulChar.coeToFun_mul, Pi.mul_apply,
      Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_right (p ^ r) m) ψ,
      Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_left m (p ^ r)) η, hψε]
    simp only [ε]; linear_combination -hη2
  have hsum := hP (chi ψ η) hodd (by rw [conductor_chi hpm hψ η]; exact Nat.dvd_mul_right _ _)
  rw [regroup, sum_coe_sort (univ.image a)
    (fun w => ((classSum a e w : ℚ) : ℂ) * bracket (chi ψ η) w)] at hsum
  have hxf := mem_filter.1 hx
  have hyf := mem_filter.1 hy
  have hsub : ({x, y, t} : Finset ℕ) ⊆ univ.image a := by
    intro w hw
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hxf.1
    · exact hyf.1
    · exact ht
  rw [← sum_subset hsub (fun w hw hw' => by
    simp only [mem_insert, mem_singleton, not_or] at hw'
    exact (hdie w hw hw'.1 hw'.2.1 hw'.2.2).elim)] at hsum
  rw [sum_insert (by simp [hxy, htx.symm]), sum_insert (by simp [hty.symm]), sum_singleton] at hsum
  have hterm : ∀ s : ℕ, s ∈ fullPts p m a →
      bracket (chi ψ η) s = ψ (s : ZMod (p ^ r)) * η₀ (s : ZMod f) * Eul := by
    intro s hs
    have hsf := mem_filter.1 hs
    have hdm : dm m s = m := (dm_eq_iff s).2 hsf.2.2
    have hg : m.gcd s = 1 := Nat.coprime_comm.1 hsf.2.2
    rw [bracket_unit hpm hψ η s hsf.2.1, if_pos (by rw [hηc, hdm]; exact hfm), hg, Nat.div_one, hdm,
      primChar_lift hfm η₀ s hsf.2.2,
      div_self (by exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne m))).ne'),
      one_mul]
  have htt : bracket (chi ψ η) t = ((m.totient : ℂ) / ((dm m t).totient : ℂ)) *
      ψ ((t / m.gcd t : ℕ) : ZMod (p ^ r)) * η₀ ((t / m.gcd t : ℕ) : ZMod f) * Eul := by
    have hEul' : eulerPrimes (dm m t) η.conductor = eulerPrimes m η.conductor := by
      rw [hηc]; exact hEul
    rw [bracket_unit hpm hψ η t hpt, if_pos (by rw [hηc]; exact hfd), hEul',
      primChar_lift hfm η₀ _ hbt]
  rw [hterm x hx, hterm y hy, htt, hβ, hTX] at hsum
  have hψx : ψ (x : ZMod (p ^ r)) ≠ 0 := by
    have hxP : x.Coprime (p ^ r) :=
      Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hxf.2.1).symm
    rw [← ZMod.coe_unitOfCoprime x hxP]; exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
  have hneg : ψ (-(x : ZMod (p ^ r))) = ε * ψ (x : ZMod (p ^ r)) := by
    rw [neg_eq_neg_one_mul, map_mul, hψε]
  rw [hneg] at hsum
  have hfac : ψ (x : ZMod (p ^ r)) * Eul *
      (((classSum a e x : ℚ) : ℂ) * η₀ (x : ZMod f) + ((classSum a e y : ℚ) : ℂ) * η₀ (y : ZMod f)
        - η₀ (-1) * ((m.totient : ℂ) / ((dm m t).totient : ℂ)) * ((classSum a e t : ℚ) : ℂ) *
          η₀ ((t / m.gcd t : ℕ) : ZMod f)) = 0 := by
    simp only [ε, hηm1] at hsum
    linear_combination hsum
  exact (mul_eq_zero.1 hfac).resolve_left (mul_ne_zero hψx hEul0)

theorem Sp_of_one {d : ℕ} {z : ℤ} (hz : z ≡ 1 [ZMOD d]) : Sp d z := by
  intro q _
  left
  exact hz.of_dvd (by exact_mod_cast Nat.ordProj_dvd d q)

theorem primeFactors_two_pow_mul {k m' : ℕ} (hk : 1 ≤ k) (hm' : m' ≠ 0) :
    (2 ^ k * m').primeFactors = {2} ∪ m'.primeFactors := by
  rw [Nat.primeFactors_mul (pow_ne_zero _ (by norm_num)) hm', Nat.primeFactors_prime_pow (by omega)
    Nat.prime_two]

/-- **R2a**, as written (class form). -/
theorem lemmaR2a (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) {v m' : ℕ} (hv : 3 ≤ v)
    (hm : m = 2 ^ v * m') (hm'odd : m' % 2 = 1)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (x y t : ℕ) (himg : univ.image a = {x, y, t}) (hsum : x + y + t = p ^ r * m)
    (hpx : ¬ p ∣ x) (hpy : ¬ p ∣ y) (hpt : ¬ p ∣ t) (hxm : x.Coprime m) (hym : y.Coprime m)
    (hgt : m.gcd t = 2) (hxy : x ≠ y) (hβ : (y : ZMod (p ^ r)) = x)
    (hxym' : x ≡ y [MOD m']) (hg2 : x ≡ y * (1 + 2 ^ (v - 1)) [MOD 2 ^ v]) :
    classSum a e x = 0 ∧ classSum a e y = 0 ∧ classSum a e t = 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  haveI : Fact (1 < p ^ r) := ⟨Nat.one_lt_pow (by omega) (by omega)⟩
  have hm'0 : m' ≠ 0 := by omega
  haveI : NeZero m' := ⟨hm'0⟩
  -- 2-adic bookkeeping
  have hv1 : v = (v - 1) + 1 := by omega
  have h2v : (2 : ℕ) ^ v = 2 * 2 ^ (v - 1) := by rw [hv1, pow_succ]; simp [mul_comm]
  set f1 := 2 ^ (v - 1) * m' with hf1
  haveI : NeZero f1 := ⟨Nat.mul_ne_zero (pow_ne_zero _ (by norm_num)) hm'0⟩
  have hmf1 : m = 2 * f1 := by rw [hm, h2v, hf1]; ring
  have h4f1 : 4 ∣ f1 := dvd_mul_of_dvd_left (by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]; exact Nat.pow_dvd_pow 2 (by omega)) _
  have h2f1 : 2 ∣ f1 := dvd_trans (by norm_num) h4f1
  have hm4 : m % 4 ≠ 2 := by rw [hmf1]; omega
  have h2m : 2 ∣ m := by rw [hmf1]; exact dvd_mul_right 2 f1
  have hxodd : ¬ 2 ∣ x := fun h => by
    have := Nat.dvd_gcd h h2m; rw [hxm.gcd_eq_one] at this; omega
  have hyodd : ¬ 2 ∣ y := fun h => by
    have := Nat.dvd_gcd h h2m; rw [hym.gcd_eq_one] at this; omega
  -- the point T = t / 2
  set T := t / m.gcd t with hTdef
  have ht2 : t = 2 * T := by
    rw [hTdef, hgt]; exact (Nat.mul_div_cancel' (hgt ▸ Nat.gcd_dvd_right m t)).symm
  have hTodd : ¬ 2 ∣ T := by
    intro h
    have h4t : 4 ∣ t := by rw [ht2]; exact Nat.mul_dvd_mul_left 2 h
    have h4m : 4 ∣ m := by rw [hmf1]; exact Nat.mul_dvd_mul_left 2 h2f1
    have := Nat.dvd_gcd h4m h4t; rw [hgt] at this; omega
  have hbt : T.Coprime m := by
    have hg1 : (m / 2).gcd (t / 2) = 1 := by
      rw [Nat.gcd_div h2m (hgt ▸ Nat.gcd_dvd_right m t), hgt]
    rw [hmf1, Nat.coprime_mul_iff_right]
    refine ⟨(Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hTodd)), ?_⟩
    rw [hmf1, Nat.mul_div_cancel_left _ (by norm_num), ← hgt, ← hTdef] at hg1
    · exact Nat.coprime_comm.1 hg1
  have htm : ¬ t.Coprime m := fun h => by rw [Nat.coprime_comm] at h; rw [h] at hgt; omega
  obtain ⟨hx, hy, hsep, hN, hdie⟩ := setup3 hp7 hr a e x y t himg hpx hpy hxm hym htm hβ
  have htx : t ≠ x := fun h => by rw [h, Nat.Coprime.gcd_eq_one (Nat.coprime_comm.1 hxm)] at hgt; omega
  have hty : t ≠ y := fun h => by rw [h, Nat.Coprime.gcd_eq_one (Nat.coprime_comm.1 hym)] at hgt; omega
  have hpt' : ¬ p ∣ t := hpt
  -- T ≡ −x (mod p^r)
  have hTX : ((T : ℕ) : ZMod (p ^ r)) = -(x : ZMod (p ^ r)) := by
    have hs : ((x + y + t : ℕ) : ZMod (p ^ r)) = 0 := by
      rw [hsum, Nat.cast_mul, ZMod.natCast_self, zero_mul]
    rw [ht2] at hs; push_cast at hs; rw [hβ] at hs
    have h2 : IsUnit ((2 : ℕ) : ZMod (p ^ r)) :=
      (ZMod.isUnit_iff_coprime 2 _).2 (small_cop (by norm_num) (by norm_num) hp7)
    push_cast at h2
    have := (h2.mul_right_eq_zero).1 (show (2 : ZMod (p ^ r)) * (T + x) = 0 by linear_combination hs)
    linear_combination this
  -- top level: e_j = e_k
  have hxyq : ¬ x ≡ y [MOD 2 ^ v] := by
    intro h
    have h1 := (h.symm.trans hg2)
    have hdvd : (2 : ℤ) ^ v ∣ (y : ℤ) * 2 ^ (v - 1) := by
      have := (Nat.modEq_iff_dvd.1 h1); push_cast at this
      have e : (y : ℤ) * (1 + 2 ^ (v - 1)) - y = y * 2 ^ (v - 1) := by ring
      rw [e] at this; exact this
    rw [show (2 : ℤ) ^ v = 2 ^ (v - 1) * 2 by rw [← pow_succ, ← hv1], mul_comm (y : ℤ)] at hdvd
    have := Int.dvd_of_mul_dvd_mul_left (pow_ne_zero _ (by norm_num)) hdvd
    exact hyodd (by exact_mod_cast this)
  have hEq := top_equal hp7 hr hpm hm4 (q := 2) (v := v) (m' := m') Nat.prime_two (by omega) hm
    (by omega) a e hP x y hx hy hxy hβ hsep hN hxym' hxyq
  -- dm and weights
  have hdt : dm m t = f1 := by
    rw [dm, hgt, hmf1, Nat.mul_div_cancel_left _ (by norm_num)]
  have hw : ((m.totient : ℂ) / ((dm m t).totient : ℂ)) = 2 := by
    rw [hdt, hmf1, Nat.totient_mul_of_prime_of_dvd Nat.prime_two h2f1]
    push_cast
    rw [mul_div_assoc, div_self (by exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero
      (NeZero.ne f1))).ne'), mul_one]
  -- x ≡ y (mod f1), (mod m'); T ≡ −x (mod m')
  have hxy2 : x ≡ y [MOD 2 ^ (v - 1)] := by
    have h1 : y * (1 + 2 ^ (v - 1)) ≡ y [MOD 2 ^ (v - 1)] := by
      rw [Nat.modEq_iff_dvd]; push_cast; exact ⟨-(y : ℤ), by ring⟩
    exact (hg2.of_dvd (by rw [h2v]; exact dvd_mul_left _ _)).trans h1
  have hcop2 : (2 ^ (v - 1)).Coprime m' :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega))
  have hxyf1 : x ≡ y [MOD f1] := (Nat.modEq_and_modEq_iff_modEq_mul hcop2).1 ⟨hxy2, hxym'⟩
  have hTm' : ((T : ℕ) : ZMod m') = -(x : ZMod m') := by
    have hs : ((x + y + t : ℕ) : ZMod m') = 0 := by
      rw [hsum, hm, (ZMod.natCast_eq_zero_iff _ _).2 (dvd_mul_of_dvd_right (dvd_mul_left _ _) _)]
    rw [ht2] at hs; push_cast at hs
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 hxym'.symm] at hs
    have h2 : IsUnit ((2 : ℕ) : ZMod m') := (ZMod.isUnit_iff_coprime 2 _).2
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega))
    push_cast at h2
    have := (h2.mul_right_eq_zero).1 (show (2 : ZMod m') * (T + x) = 0 by linear_combination hs)
    linear_combination this
  -- ### Step 2: conductor f1 = m/2
  have hfm1 : f1 ∣ m := by rw [hmf1]; exact dvd_mul_left _ _
  have hEm1 : eulerPrimes m f1 = ∅ := by
    ext ℓ
    simp only [eulerPrimes, mem_filter, Nat.mem_primeFactors, Finset.notMem_empty, iff_false]
    rintro ⟨⟨hl, hld, -⟩, hn⟩
    rw [hmf1] at hld
    rcases hl.dvd_mul.1 hld with h | h
    · rw [(Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 h] at hn; exact hn h2f1
    · exact hn h
  have hEf1 : eulerPrimes f1 f1 = ∅ := by
    ext ℓ
    simp only [eulerPrimes, mem_filter, Nat.mem_primeFactors, Finset.notMem_empty, iff_false]
    rintro ⟨⟨-, hld, -⟩, hn⟩; exact hn hld
  have heq1 := level_eq hp7 hr hpm a e hP (f := f1) hfm1 (by rw [hEm1]; exact empty_subset _)
    x y t hx hy hxy hβ (by rw [himg]; simp) hpt htx hty (by rw [hdt]) (by rw [hdt, hEf1, hEm1])
    hbt hTX (fun w hw h1 h2 h3 => hdie w hw h1 h2 h3)
  rw [hw] at heq1
  have hxf1 : x.Coprime f1 := hxm.coprime_dvd_right hfm1
  have hTf1 : T.Coprime f1 := hbt.coprime_dvd_right hfm1
  set zf : ZMod f1 := -(T : ZMod f1) * (x : ZMod f1)⁻¹
  set z : ℤ := (zf.val : ℤ)
  have hzx : ((z : ℤ) : ZMod f1) * (x : ZMod f1) = -(T : ZMod f1) := by
    simp only [z, Int.cast_natCast, ZMod.natCast_zmod_val, zf, mul_assoc]
    rw [mul_comm ((x : ZMod f1))⁻¹, ZMod.coe_mul_inv_eq_one x hxf1, mul_one]
  -- z ≡ 1 (mod m')
  have hm'f1 : m' ∣ f1 := dvd_mul_left _ _
  have c1 : z ≡ 1 [ZMOD m'] := by
    have h := congrArg (ZMod.castHom hm'f1 (ZMod m')) hzx
    rw [map_mul, map_intCast, map_natCast, map_neg, map_natCast, hTm', neg_neg] at h
    have hxu : IsUnit ((x : ℕ) : ZMod m') :=
      (ZMod.isUnit_iff_coprime x m').2 (hxm.coprime_dvd_right (by rw [hm]; exact dvd_mul_left _ _))
    obtain ⟨u, hu⟩ := hxu
    rw [← hu] at h
    have h1 : ((z : ℤ) : ZMod m') = 1 := by
      have := congrArg (· * ((u⁻¹ : (ZMod m')ˣ) : ZMod m')) h
      simpa [mul_assoc] using this
    rw [← ZMod.intCast_eq_intCast_iff, h1, Int.cast_one]
  -- z ≡ 1 + 2^(v−2) (mod 2^(v−1))
  set B : ℕ := 2 ^ (v - 2) with hB
  have hB1 : (2 : ℕ) ^ (v - 1) = 2 * B := by
    rw [hB, ← pow_succ']; congr 1; omega
  have hB2 : (2 : ℕ) ^ v = 4 * B := by rw [h2v, hB1]; ring
  have hint : ((2 * B : ℕ) : ℤ) ∣ (x : ℤ) * (1 + B) + T := by
    obtain ⟨k, hk⟩ : ((4 * B : ℕ) : ℤ) ∣ ((y * (1 + 2 ^ (v - 1)) : ℕ) : ℤ) - x := by
      rw [← hB2]; exact_mod_cast Nat.modEq_iff_dvd.1 hg2
    obtain ⟨s', hs'⟩ : ∃ s' : ℕ, x + y = 2 * s' := ⟨(x + y) / 2, by omega⟩
    have hsum' : ((x + y + t : ℕ) : ℤ) = ((p ^ r * (4 * B * m') : ℕ) : ℤ) := by
      rw [hsum, hm, hB2]
    refine ⟨s' - k + ((p ^ r : ℕ) : ℤ) * m', ?_⟩
    have ht2' : (t : ℤ) = 2 * T := by exact_mod_cast ht2
    have hs'' : (x : ℤ) + y = 2 * s' := by exact_mod_cast hs'
    rw [hB1] at hk
    push_cast at hk hsum' ⊢
    have h2 : (2 : ℤ) * ((x : ℤ) * (1 + B) + T) = 2 * (2 * B * (s' - k + (p : ℤ) ^ r * m')) := by
      linear_combination -hk + 2 * (B : ℤ) * hs'' + hsum' - ht2'
    exact mul_left_cancel₀ (two_ne_zero) h2
  have h2f1' : 2 ^ (v - 1) ∣ f1 := dvd_mul_right _ _
  have c2 : z ≡ 1 + 2 ^ (v - 1 - 1) [ZMOD 2 ^ (v - 1)] := by
    have h := congrArg (ZMod.castHom h2f1' (ZMod (2 ^ (v - 1)))) hzx
    rw [map_mul, map_intCast, map_natCast, map_neg, map_natCast] at h
    have hT2 : ((T : ℕ) : ZMod (2 ^ (v - 1))) = -((x : ZMod (2 ^ (v - 1))) * (1 + B)) := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (2 ^ (v - 1))).2 (hB1 ▸ hint)
      push_cast at this
      linear_combination this
    rw [hT2, neg_neg] at h
    have hxu : IsUnit ((x : ℕ) : ZMod (2 ^ (v - 1))) :=
      (ZMod.isUnit_iff_coprime x _).2 (Nat.Coprime.pow_right _
        (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hxodd)))
    obtain ⟨u, hu⟩ := hxu
    rw [← hu] at h
    have h1 : ((z : ℤ) : ZMod (2 ^ (v - 1))) = 1 + (B : ZMod (2 ^ (v - 1))) := by
      have := congrArg (· * ((u⁻¹ : (ZMod (2 ^ (v - 1)))ˣ) : ZMod (2 ^ (v - 1)))) h
      simp only [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one] at this
      have hu1 : (u : ZMod (2 ^ (v - 1))) * ((u⁻¹ : (ZMod (2 ^ (v - 1)))ˣ) : ZMod (2 ^ (v - 1))) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [this]; linear_combination ((B : ZMod (2 ^ (v - 1))) + 1) * hu1
    rw [show v - 1 - 1 = v - 2 by omega]
    have := (ZMod.intCast_eq_intCast_iff z (1 + (B : ℤ)) (2 ^ (v - 1))).1 (by push_cast; exact h1)
    push_cast at this; exact this
  have hzne : ¬ z ≡ 1 [ZMOD (2 : ℤ) ^ (v - 1)] := by
    intro h
    have h3 := c2.symm.trans h
    rw [Int.modEq_iff_dvd] at h3
    have : (2 : ℤ) ^ (v - 1) ∣ 2 ^ (v - 1 - 1) := by
      have e : (1 : ℤ) - (1 + 2 ^ (v - 1 - 1)) = -(2 ^ (v - 1 - 1)) := by ring
      rw [e] at h3; exact (dvd_neg).1 h3
    have := Int.le_of_dvd (by positivity) this
    have : (2 : ℤ) ^ (v - 1 - 1) < 2 ^ (v - 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
    omega
  have hcop2' : (2 ^ (v - 1)).Coprime m' := hcop2
  have hSp : Sp f1 z := by
    rw [hf1]
    refine (Sp_mul hcop2' (pow_ne_zero _ (by norm_num)) hm'0 z).2 ⟨?_, Sp_of_one c1⟩
    rw [Sp_pp Nat.prime_two (by omega)]
    right; right; exact ⟨rfl, by omega, by exact_mod_cast c2⟩
  have htau : tau f1 z = 1 := by
    rw [hf1, tau_mul hcop2' (pow_ne_zero _ (by norm_num)) hm'0, tau_pp Nat.prime_two (by omega),
      if_neg (by exact_mod_cast hzne), tau_eq_zero c1]
  have hgu : IsUnit ((z : ℤ) : ZMod f1) := by
    have hTu : IsUnit (-(T : ZMod f1)) := ((ZMod.isUnit_iff_coprime T f1).2 hTf1).neg
    rw [← hzx] at hTu
    exact isUnit_of_mul_isUnit_left hTu
  obtain ⟨-, G2⟩ := lemmaG' (NeZero.ne f1) (by omega) hgu.unit z hgu.unit_spec.symm
  obtain ⟨η₀, hη₀⟩ := Erdos634.LemmaSGprime.exists_primitive (NeZero.ne f1) (by omega)
  have hval := G2 hSp η₀ hη₀
  rw [htau, IsUnit.unit_spec, pow_one] at hval
  have hE1 := heq1 η₀ hη₀
  have hyx : ((y : ℕ) : ZMod f1) = x := ((ZMod.natCast_eq_natCast_iff _ _ _).2 hxyf1).symm
  have hmT : η₀ (-1) * η₀ ((T : ℕ) : ZMod f1) = -η₀ ((x : ℕ) : ZMod f1) := by
    rw [← map_mul, show (-1 : ZMod f1) * T = -(T : ZMod f1) by ring, ← hzx, map_mul, hval]; ring
  rw [hyx, hEq] at hE1
  have hηx : η₀ ((x : ℕ) : ZMod f1) ≠ 0 := by
    rw [← ZMod.coe_unitOfCoprime x hxf1]; exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
  have hA : ((classSum a e x + classSum a e t : ℚ) : ℂ) * η₀ ((x : ℕ) : ZMod f1) = 0 := by
    push_cast
    have : (2 : ℂ) * (((classSum a e x : ℚ) : ℂ) + ((classSum a e t : ℚ) : ℂ)) *
        η₀ ((x : ℕ) : ZMod f1) = 0 := by
      linear_combination hE1 + 2 * ((classSum a e t : ℚ) : ℂ) * hmT
    have h2 := (mul_eq_zero.1 this).resolve_right hηx
    rw [(mul_eq_zero.1 h2).resolve_left two_ne_zero, zero_mul]
  have hsum1 : classSum a e x + classSum a e t = 0 := by
    exact_mod_cast (mul_eq_zero.1 hA).resolve_right hηx
  -- ### Step 3: conductor m'
  have hm'm : m' ∣ m := by rw [hm]; exact dvd_mul_left _ _
  have hE2' : eulerPrimes m m' ⊆ {2} := fun ℓ hl => mem_singleton.2
    (euler_sub (v := v) (v' := 0) Nat.prime_two (by rwa [pow_zero, one_mul, ← hm]))
  have hEul2 : eulerPrimes (dm m t) m' = eulerPrimes m m' := by
    rw [hdt]; unfold eulerPrimes
    rw [hf1, hm, primeFactors_two_pow_mul (by omega) hm'0, primeFactors_two_pow_mul (by omega) hm'0]
  have heq2 := level_eq hp7 hr hpm a e hP (f := m') hm'm hE2' x y t hx hy hxy hβ
    (by rw [himg]; simp) hpt htx hty (by rw [hdt]; exact hm'f1) hEul2 hbt hTX
    (fun w hw h1 h2 h3 => hdie w hw h1 h2 h3)
  rw [hw] at heq2
  obtain ⟨η₁, hη₁⟩ := Erdos634.LemmaSGprime.exists_primitive hm'0 (by omega)
  have hE2 := heq2 η₁ hη₁
  have hyx' : ((y : ℕ) : ZMod m') = x := ((ZMod.natCast_eq_natCast_iff _ _ _).2 hxym').symm
  have hmT' : η₁ (-1) * η₁ ((T : ℕ) : ZMod m') = η₁ ((x : ℕ) : ZMod m') := by
    rw [← map_mul, hTm']; congr 1; ring
  rw [hyx', hEq] at hE2
  have hηx' : η₁ ((x : ℕ) : ZMod m') ≠ 0 := by
    rw [← ZMod.coe_unitOfCoprime x (hxm.coprime_dvd_right hm'm)]
    exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
  have hB' : ((classSum a e x - classSum a e t : ℚ) : ℂ) * η₁ ((x : ℕ) : ZMod m') = 0 := by
    push_cast
    have : (2 : ℂ) * (((classSum a e x : ℚ) : ℂ) - ((classSum a e t : ℚ) : ℂ)) *
        η₁ ((x : ℕ) : ZMod m') = 0 := by
      linear_combination hE2 + 2 * ((classSum a e t : ℚ) : ℂ) * hmT'
    have h2 := (mul_eq_zero.1 this).resolve_right hηx'
    rw [(mul_eq_zero.1 h2).resolve_left two_ne_zero, zero_mul]
  have hdiff : classSum a e x - classSum a e t = 0 := by
    exact_mod_cast (mul_eq_zero.1 hB').resolve_right hηx'
  have hx0 : classSum a e x = 0 := by linarith
  refine ⟨hx0, by rw [hEq, hx0], by linarith⟩

end R2a

/-! ## Genuine consequences (R2a): n = 56 = 7·8, a = (29, 1, 26): 29 ≡ 1 (mod 7) (same β),
29 ≡ 5·1 (mod 8) (g₂ = 1 + 2²), gcd(8, 26) = 2 (d_l = 4); and n = 112 = 7·16, a = (57, 1, 54):
57 ≡ 9·1 (mod 16) (g₂ = 1 + 2³), gcd(16, 54) = 2. For EVERY e satisfying Lemma P's hypothesis,
all class sums vanish. -/
theorem consequence_R2a_56 (e : Fin 3 → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (7 ^ 1 * 8), χ.Odd → 7 ^ 1 ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ ((![29, 1, 26] : Fin 3 → ℕ) j) = 0) :
    classSum ![29, 1, 26] e 29 = 0 ∧ classSum ![29, 1, 26] e 1 = 0 ∧
      classSum ![29, 1, 26] e 26 = 0 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact lemmaR2a (p := 7) (r := 1) (m := 8) (v := 3) (m' := 1) (by norm_num) le_rfl (by norm_num)
    le_rfl (by norm_num) (by norm_num) _ e hP 29 1 26 (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide)

theorem consequence_R2a_112 (e : Fin 3 → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (7 ^ 1 * 16), χ.Odd → 7 ^ 1 ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ ((![57, 1, 54] : Fin 3 → ℕ) j) = 0) :
    classSum ![57, 1, 54] e 57 = 0 ∧ classSum ![57, 1, 54] e 1 = 0 ∧
      classSum ![57, 1, 54] e 54 = 0 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact lemmaR2a (p := 7) (r := 1) (m := 16) (v := 4) (m' := 1) (by norm_num) le_rfl (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) _ e hP 57 1 54 (by decide) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide)

#print axioms Erdos634.LemmaSR2a.level_eq
#print axioms Erdos634.LemmaSR2a.lemmaR2a
#print axioms Erdos634.LemmaSR2a.consequence_R2a_56
#print axioms Erdos634.LemmaSR2a.consequence_R2a_112

end Erdos634.LemmaSR2a
