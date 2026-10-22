/-
Lemma S, node A5: **class R1F2 closed** (|F| = 2, β_k = β_j, |I| = 3), splitting into R1F2c
(Lemma L) and R1F2o (R3 / R2b / R2a) (PROOF_lemmaS.md §4 "|F| = 2, β_k = β_j", Lemma L step 6;
round 2 §4.6 "From x_j + x_k + x_l = 0, the only R1F2o shapes are …").

  |F| = 2, β_k = β_j: |I| = 3 and l ∈ I ∖ F. N(a) gives g = γ_j/γ_k ∈ Sp(m_I): class R1F2.
  g = 1 is the isosceles case (x_j = x_k). Otherwise pick the special prime q (q = 3 when τ(g) = 2,
  so that the third term dies). If the third term dies at f₂ (R1F2c) Lemma L applies; if not (R1F2o)
  its shape is R3 (q = 3, gcd(m, a_l) = 3), R2b (q = 2, 4 ∥ m, gcd = 4) or R2a (q = 2, 8 | m, gcd = 2).
  After e_j = e_k = 0, Iso kills the third class.

Class form: x ≠ y full, y ≡ x (mod p^r), a third I-point l that is not full, the three positive
values summing to n. (m = 12, R2b with f₂ = 3, goes through LemmaSR2b12.)
Conclusion: E_x = E_y = E_l = 0.
Formalization debt, not /goal progress.
-/
import Mathlib
import Erdos634.Draft.LemmaSF3
import Erdos634.Draft.LemmaSR2b12

open scoped BigOperators
open Finset

namespace Erdos634.LemmaSR1F2

open DirichletCharacter
open Erdos634.LemmaSC (bracket)
open Erdos634.LemmaSElim (classSum lemmaIso_class)
open Erdos634.LemmaSFC (fullPts card_N)
open Erdos634.LemmaSPhi (dm)
open Erdos634.LemmaSN (pred_dvd)
open Erdos634.LemmaSGprime (Sp tau)
open Erdos634.LemmaSGpp (SpPP)

/-- f | m/g ⟹ g | m/f (both mean f·g | m). -/
theorem dvd_div_swap {m f g : ℕ} (hm : m ≠ 0) (hf : f ∣ m) (hg : g ∣ m) (h : f ∣ m / g) :
    g ∣ m / f := by
  obtain ⟨k, hk⟩ := h
  have hg0 : g ≠ 0 := fun h0 => by rw [h0] at hg; exact hm (Nat.eq_zero_of_zero_dvd hg)
  have hf0 : f ≠ 0 := fun h0 => by rw [h0] at hf; exact hm (Nat.eq_zero_of_zero_dvd hf)
  have : m = f * (g * k) := by
    rw [← mul_assoc, mul_comm f g, mul_assoc, ← hk, Nat.mul_div_cancel' hg]
  exact ⟨k, by rw [this, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hf0)]⟩

section R1F2
variable {p r m : ℕ} [hp : Fact p.Prime] [NeZero m]

/-- g ≡ 1 at every prime of m' = m / q^v other than the special one ⟹ x ≡ y (mod m'). -/
theorem xy_mod_mprime {q : ℕ} (hq : q.Prime) {z : ℤ} (hSp : Sp m z)
    (h3 : q ≠ 3 → 3 ∣ m → z ≡ 1 [ZMOD 3 ^ m.factorization 3])
    (h2 : q ≠ 2 → ¬ 2 ∣ m) {x y : ℕ} (hz : z * (1 * y) ≡ x [ZMOD m]) :
    x ≡ y [MOD m / q ^ m.factorization q] := by
  have hm0 : m ≠ 0 := NeZero.ne m
  set m' := m / q ^ m.factorization q
  have hm'0 : m' ≠ 0 := by
    have := Nat.ordCompl_pos q hm0; omega
  have hm'm : m' ∣ m := Nat.ordCompl_dvd m q
  have hz1 : z ≡ 1 [ZMOD m'] := by
    refine Erdos634.LemmaSR1p.modEq_of_components hm'0 (fun ℓ hℓ => ?_)
    have hℓp := Nat.prime_of_mem_primeFactors hℓ
    have hℓm : ℓ ∈ m.primeFactors :=
      Nat.mem_primeFactors.2 ⟨hℓp, dvd_trans (Nat.dvd_of_mem_primeFactors hℓ) hm'm, hm0⟩
    have hℓq : ℓ ≠ q := by
      rintro rfl; exact Nat.not_dvd_ordCompl hq hm0 (Nat.dvd_of_mem_primeFactors hℓ)
    have hfac : m'.factorization ℓ = m.factorization ℓ := by
      simp only [m', Nat.factorization_ordCompl, Finsupp.erase_ne hℓq]
    rw [hfac]
    rcases hSp ℓ hℓm with h | ⟨rfl, hv1, -⟩ | ⟨rfl, -, -⟩
    · exact h
    · exact h3 (Ne.symm hℓq) (Nat.dvd_of_mem_primeFactors hℓm)
    · exact absurd (Nat.dvd_of_mem_primeFactors hℓm) (h2 (Ne.symm hℓq))
  have := (hz.of_dvd (by exact_mod_cast hm'm)).symm.trans ((hz1.mul_right (1 * (y : ℤ))))
  rw [one_mul, one_mul] at this
  exact Int.natCast_modEq_iff.1 this

/-- From z·y = x in ZMod m to ZMod d for d | m. -/
theorem cast_rel {d : ℕ} (hd : d ∣ m) {z : ℤ} {x y : ℕ}
    (h : ((z : ℤ) : ZMod m) * (y : ZMod m) = x) : ((z : ℤ) : ZMod d) * (y : ZMod d) = x := by
  have := congrArg (ZMod.castHom hd (ZMod d)) h
  rwa [map_mul, map_intCast, map_natCast, map_natCast] at this

/-- With y a unit mod d: x ≡ y (mod d) iff z ≡ 1 (mod d). -/
theorem xy_iff_z {d : ℕ} {z : ℤ} {x y : ℕ} (hy : y.Coprime d)
    (h : ((z : ℤ) : ZMod d) * (y : ZMod d) = x) : x ≡ y [MOD d] ↔ z ≡ 1 [ZMOD d] := by
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime y d).2 hy
  rw [← ZMod.natCast_eq_natCast_iff, ← ZMod.intCast_eq_intCast_iff, ← h, ← hu, Int.cast_one]
  constructor
  · intro h1
    have := congrArg (· * ((u⁻¹ : (ZMod d)ˣ) : ZMod d)) h1
    simpa [mul_assoc] using this
  · intro h1; rw [h1, one_mul]

/-- **Class R1F2 closed** (R1F2c by Lemma L, R1F2o by R3/R2b/R2a). -/
theorem lemmaR1F2 (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (hm4 : m % 4 ≠ 2)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (x y l : ℕ) (himg : univ.image a = {x, y, l}) (hsum : x + y + l = p ^ r * m)
    (hx : x ∈ fullPts p m a) (hy : y ∈ fullPts p m a) (hpl : ¬ p ∣ l) (hlm : ¬ l.Coprime m)
    (hxy : x ≠ y) (hβ : (y : ZMod (p ^ r)) = x) :
    classSum a e x = 0 ∧ classSum a e y = 0 ∧ classSum a e l = 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hm0 : m ≠ 0 := NeZero.ne m
  have hxf := mem_filter.1 hx
  have hyf := mem_filter.1 hy
  have hxm := hxf.2.2
  have hym := hyf.2.2
  have hmem : ∀ w, w ∈ univ.image a ↔ w = x ∨ w = y ∨ w = l := by
    intro w; rw [himg]; simp
  have hsub : ∀ w ∈ fullPts p m a, w = x ∨ w = y := by
    intro w hw
    have hwf := mem_filter.1 hw
    rcases (hmem w).1 hwf.1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · subst h; exact absurd hwf.2.2 hlm
  have hsep : ∀ w ∈ fullPts p m a, w ≠ x → w ≠ y → classSum a e w ≠ 0 →
      (w : ZMod (p ^ r)) ≠ x ∧ (w : ZMod (p ^ r)) ≠ -x := by
    intro w hw hwx hwy; rcases hsub w hw with h | h <;> contradiction
  have hN : 2 * ((fullPts p m a).image (fun y : ℕ => (y : ZMod (p ^ r)))).card <
      (univ.filter (fun v : (ZMod (p ^ r))ˣ => ZMod.unitsMap (pred_dvd p r) v = 1)).card := by
    have hc : ((fullPts p m a).image (fun y : ℕ => (y : ZMod (p ^ r)))).card ≤ 1 := by
      refine card_le_one.2 (fun u hu v hv => ?_)
      obtain ⟨w1, hw1, rfl⟩ := mem_image.1 hu
      obtain ⟨w2, hw2, rfl⟩ := mem_image.1 hv
      rcases hsub w1 hw1 with rfl | rfl <;> rcases hsub w2 hw2 with rfl | rfl <;> simp [hβ]
    rw [card_N hr]; split_ifs <;> omega
  have hlim : l ∈ univ.image a := (hmem l).2 (Or.inr (Or.inr rfl))
  have hEl_of : classSum a e x = 0 → classSum a e y = 0 → classSum a e l = 0 := by
    intro h1 h2
    refine lemmaIso_class hp7 hr hpm a e hP l hlim hpl (fun w hw hwl _ hE => ?_)
    rcases (hmem w).1 hw with rfl | rfl | rfl
    · exact absurd h1 hE
    · exact absurd h2 hE
    · exact absurd rfl hwl
  have finish : classSum a e x = 0 ∧ classSum a e y = 0 →
      classSum a e x = 0 ∧ classSum a e y = 0 ∧ classSum a e l = 0 :=
    fun h => ⟨h.1, h.2, hEl_of h.1 h.2⟩
  -- the top level
  set z : ℤ := ((((x : ZMod m) * (y : ZMod m)⁻¹)).val : ℤ)
  have hzm : ((z : ℤ) : ZMod m) * (y : ZMod m) = x := by
    simp only [z, Int.cast_natCast, ZMod.natCast_zmod_val, mul_assoc]
    rw [mul_comm ((y : ZMod m))⁻¹, ZMod.coe_mul_inv_eq_one y hym, mul_one]
  have hz : z * (1 * y) ≡ x [ZMOD m] := by
    rw [← ZMod.intCast_eq_intCast_iff]; push_cast; rw [one_mul]; exact hzm
  have hkey := Erdos634.LemmaSL.fc_key hp7 hr hpm a e hP x y hx hy hxy 1 (Or.inl rfl)
    (by rw [hβ]; push_cast; ring) hsep hN
  rcases Erdos634.LemmaSL.rel_Gprime hm4 _ _ x y hxm hym 1 (Or.inl rfl) z hz hkey with
    h | ⟨hSp, -⟩
  · exact finish h
  have hβ1 : (y : ZMod (p ^ r)) = ((1 : ℤ) : ZMod (p ^ r)) * x := by rw [hβ]; push_cast; ring
  -- l ≡ −y(1 + g)
  have hlrel : ((l : ℕ) : ZMod m) = -(y : ZMod m) * (((z : ℤ) : ZMod m) + 1) := by
    have hs : ((x + y + l : ℕ) : ZMod m) = 0 := by
      rw [hsum, (ZMod.natCast_eq_zero_iff _ _).2 (dvd_mul_left _ _)]
    push_cast at hs; rw [← hzm] at hs; linear_combination hs
  have hlreld : ∀ d, d ∣ m → ((l : ℕ) : ZMod d) = -(y : ZMod d) * (((z : ℤ) : ZMod d) + 1) := by
    intro d hd
    have := congrArg (ZMod.castHom hd (ZMod d)) hlrel
    rwa [map_natCast, map_mul, map_neg, map_natCast, map_add, map_intCast, map_one] at this
  have hdie_of : ∀ f : ℕ, f ∣ m → (¬ m.gcd l ∣ m / f) →
      ∀ w ∈ univ.image a, w ≠ x → w ≠ y → ¬ p ∣ w → classSum a e w ≠ 0 → ¬ f ∣ dm m w := by
    intro f hf hno w hw hwx hwy _ _ hfd
    rcases (hmem w).1 hw with h | h | rfl
    · exact hwx h
    · exact hwy h
    · exact hno (dvd_div_swap hm0 hf (Nat.gcd_dvd_left m w) hfd)
  have hgcd1 : m.gcd l ≠ 1 := fun h => hlm (Nat.coprime_comm.1 h)
  by_cases B3 : 3 ∣ m ∧ ¬ z ≡ 1 [ZMOD 3 ^ m.factorization 3]
  · -- q = 3
    have h3m : 3 ∈ m.primeFactors := Nat.mem_primeFactors.2 ⟨Nat.prime_three, B3.1, hm0⟩
    set v3 := m.factorization 3
    have hv3 : v3 = 1 := by
      rcases hSp 3 h3m with h | ⟨-, h, -⟩ | ⟨h, -, -⟩
      · exact absurd (by exact_mod_cast h) B3.2
      · exact h
      · norm_num at h
    set m' := m / 3 ^ v3
    have hmm' : m = 3 ^ v3 * m' := (Nat.ordProj_mul_ordCompl_eq_self m 3).symm
    have h3m' : ¬ 3 ∣ m' := Nat.not_dvd_ordCompl Nat.prime_three hm0
    have hm'm : m' ∣ m := Nat.ordCompl_dvd m 3
    by_cases hg3 : m.gcd l = 3
    · -- R3
      have hodd : m % 2 = 1 := by
        by_contra hev
        have h2m : 2 ∣ m := by omega
        have hy2 : y.Coprime 2 := hym.coprime_dvd_right h2m
        have hx2 : x.Coprime 2 := hxm.coprime_dvd_right h2m
        have hz2 : ((z : ℤ) : ZMod 2) = 1 := by
          have hr2 := cast_rel h2m hzm
          have hxo : ¬ 2 ∣ x := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 (Nat.coprime_comm.1 hx2)
          have hyo : ¬ 2 ∣ y := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 (Nat.coprime_comm.1 hy2)
          have hx1 : ((x : ℕ) : ZMod 2) = 1 := by
            rw [← ZMod.natCast_mod, show x % 2 = 1 by omega]; rfl
          have hy1 : ((y : ℕ) : ZMod 2) = 1 := by
            rw [← ZMod.natCast_mod, show y % 2 = 1 by omega]; rfl
          rw [hx1, hy1, mul_one] at hr2; exact hr2
        have hl2 := hlreld 2 h2m
        rw [hz2] at hl2
        have : ((l : ℕ) : ZMod 2) = 0 := by
          rw [hl2, show (1 + 1 : ZMod 2) = 0 by decide, mul_zero]
        rw [ZMod.natCast_eq_zero_iff] at this
        have := Nat.dvd_gcd h2m this
        rw [hg3] at this; omega
      have hxym' := xy_mod_mprime Nat.prime_three hSp (fun h => absurd rfl h)
        (fun _ h2 => by omega) hz
      have hxy3 : ¬ x ≡ y [MOD 3] := by
        intro h
        have := (xy_iff_z (hym.coprime_dvd_right B3.1) (cast_rel B3.1 hzm)).1 h
        apply B3.2; rw [hv3, pow_one]; exact this
      exact Erdos634.LemmaSR3.lemmaR3 hp7 hr hpm (m' := m') (by rw [hmm', hv3, pow_one]) h3m' hodd a e hP x y l himg
        hsum hxf.2.1 hyf.2.1 hpl hxm hym hg3 hxy hβ hxym' hxy3
    · -- R1F2c at f₂ = m/3
      refine finish (Erdos634.LemmaSL.lemmaL hp7 hr hpm (q := 3) (v := v3) (v' := 0) (m' := m')
        (Or.inr rfl) (by omega) h3m' hmm' hm4 (Or.inl rfl) a e hP x y hx hy hxy 1 (Or.inl rfl) hβ1
        hsep hN z hz (by exact_mod_cast B3.2) ?_)
      refine hdie_of _ (by rw [pow_zero, one_mul]; exact hm'm) (fun h => ?_)
      simp only [pow_zero, one_mul] at h
      rw [Nat.div_div_self (Nat.ordProj_dvd m 3) hm0, show m.factorization 3 = 1 from hv3,
        pow_one] at h
      rcases (Nat.dvd_prime Nat.prime_three).1 h with h | h
      · exact hgcd1 h
      · exact hg3 h
  · -- q = 2
    have hg1 : ¬ z ≡ 1 [ZMOD m] := by
      intro h1
      have hxym : x ≡ y [MOD m] := (xy_iff_z hym hzm).2 h1
      have hxyP : x ≡ y [MOD p ^ r] := ((ZMod.natCast_eq_natCast_iff _ _ _).1 hβ).symm
      have hn := (Nat.modEq_and_modEq_iff_modEq_mul (Erdos634.LemmaSPhi.cop_pr hpm)).1 ⟨hxyP, hxym⟩
      have hl0 : 0 < l := Nat.pos_of_ne_zero (fun h => hpl (h ▸ dvd_zero p))
      have hy0 : 0 < y := Nat.pos_of_ne_zero (fun h => hyf.2.1 (h ▸ dvd_zero p))
      have hx0 : 0 < x := Nat.pos_of_ne_zero (fun h => hxf.2.1 (h ▸ dvd_zero p))
      exact hxy (Nat.ModEq.eq_of_lt_of_lt hn (by omega) (by omega))
    obtain ⟨q, hq, hbad⟩ : ∃ q ∈ m.primeFactors, ¬ z ≡ 1 [ZMOD (q : ℤ) ^ m.factorization q] := by
      by_contra hno; push Not at hno
      exact hg1 (Erdos634.LemmaSR1p.modEq_of_components hm0 hno)
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hq2 : q = 2 ∧ 2 ≤ m.factorization q ∧
        z ≡ 1 + 2 ^ (m.factorization q - 1) [ZMOD 2 ^ m.factorization q] := by
      rcases hSp q hq with h | ⟨rfl, -, -⟩ | h
      · exact absurd h hbad
      · exact absurd ⟨Nat.dvd_of_mem_primeFactors hq, by exact_mod_cast hbad⟩ B3
      · exact h
    obtain ⟨rfl, hv2, hzv⟩ := hq2
    have h2m : 2 ∣ m := Nat.dvd_of_mem_primeFactors hq
    set v := m.factorization 2
    set m' := m / 2 ^ v
    have hmm' : m = 2 ^ v * m' := (Nat.ordProj_mul_ordCompl_eq_self m 2).symm
    have h2m' : ¬ 2 ∣ m' := Nat.not_dvd_ordCompl Nat.prime_two hm0
    have hm'm : m' ∣ m := Nat.ordCompl_dvd m 2
    have hxym' := xy_mod_mprime Nat.prime_two hSp
      (fun _ h3 => by
        by_contra hc; exact B3 ⟨h3, by exact_mod_cast hc⟩) (fun h => absurd rfl h) hz
    have hpv : 2 ^ v ∣ m := Nat.ordProj_dvd m 2
    rcases Nat.lt_or_ge v 3 with hv3 | hv3
    · have hv : v = 2 := by omega
      by_cases hg4 : m.gcd l = 4
      · -- R2b
        have hxy4 : ¬ x ≡ y [MOD 4] := by
          intro h
          have h4 : 4 ∣ m := by rw [show (4 : ℕ) = 2 ^ v by rw [hv]; norm_num]; exact hpv
          have := (xy_iff_z (hym.coprime_dvd_right h4) (cast_rel h4 hzm)).1 h
          apply hbad
          have e : ((2 : ℕ) : ℤ) ^ m.factorization 2 = ((4 : ℕ) : ℤ) := by
            rw [show m.factorization 2 = 2 from hv]; norm_num
          rw [e]; exact this
        by_cases hm'3 : m' = 3
        · exact Erdos634.LemmaSR2b12.lemmaR2b_12 hp7 hr hpm (m' := m') (by rw [hmm', hv]; norm_num)
            hm'3 a e hP x y l himg hsum hxf.2.1 hyf.2.1 hpl hxm hym hg4 hxy hβ hxym' hxy4
        · exact Erdos634.LemmaSR3.lemmaR2b hp7 hr hpm (m' := m') (by rw [hmm', hv]; norm_num) (by omega)
            hm'3 a e hP x y l himg hsum hxf.2.1 hyf.2.1 hpl hxm hym hg4 hxy hβ hxym' hxy4
      · refine finish (Erdos634.LemmaSL.lemmaL hp7 hr hpm (q := 2) (v := v) (v' := 0) (m' := m')
          (Or.inl rfl) (by omega) h2m' hmm' hm4 (Or.inl rfl) a e hP x y hx hy hxy 1 (Or.inl rfl) hβ1
          hsep hN z hz (by exact_mod_cast hbad) ?_)
        refine hdie_of _ (by rw [pow_zero, one_mul]; exact hm'm) (fun h => ?_)
        simp only [pow_zero, one_mul] at h
        rw [Nat.div_div_self hpv hm0, hv] at h
        obtain ⟨i, hi, hgi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h
        interval_cases i
        · exact hgcd1 (by simpa using hgi)
        · -- gcd = 2 is impossible: 4 | l
          have h4 : 4 ∣ m := by rw [show (4 : ℕ) = 2 ^ v by rw [hv]; norm_num]; exact hpv
          have hz4 : ((z : ℤ) : ZMod 4) = 3 := by
            have := (ZMod.intCast_eq_intCast_iff z (1 + 2 ^ (v - 1)) 4).2
              (by rw [show ((4 : ℕ) : ℤ) = 2 ^ v by rw [hv]; norm_num]; exact hzv)
            rw [this, hv]; push_cast; rfl
          have hl4 := hlreld 4 h4
          rw [hz4] at hl4
          have : ((l : ℕ) : ZMod 4) = 0 := by
            rw [hl4, show (3 + 1 : ZMod 4) = 0 by decide, mul_zero]
          rw [ZMod.natCast_eq_zero_iff] at this
          have := Nat.dvd_gcd h4 this
          rw [hgi] at this; norm_num at this
        · exact hg4 (by simpa using hgi)
    · by_cases hg2 : m.gcd l = 2
      · -- R2a
        have hg2' : x ≡ y * (1 + 2 ^ (v - 1)) [MOD 2 ^ v] := by
          have hr := cast_rel hpv hzm
          have hzz := (ZMod.intCast_eq_intCast_iff z (1 + 2 ^ (v - 1)) (2 ^ v)).2
            (by push_cast; exact hzv)
          rw [hzz] at hr
          rw [← ZMod.natCast_eq_natCast_iff, ← hr]; push_cast; ring
        exact Erdos634.LemmaSR2a.lemmaR2a hp7 hr hpm (v := v) (m' := m') hv3 hmm' (by omega) a e hP x y l himg hsum
          hxf.2.1 hyf.2.1 hpl hxm hym hg2 hxy hβ hxym' hg2'
      · refine finish (Erdos634.LemmaSL.lemmaL hp7 hr hpm (q := 2) (v := v) (v' := v - 1) (m' := m')
          (Or.inl rfl) (by omega) h2m' hmm' hm4 (Or.inr ⟨rfl, rfl, hv3⟩) a e hP x y hx hy hxy 1
          (Or.inl rfl) hβ1 hsep hN z hz (by exact_mod_cast hbad) ?_)
        have hf2 : 2 ^ (v - 1) * m' ∣ m := by
          rw [hmm']; exact Nat.mul_dvd_mul_right (Nat.pow_dvd_pow 2 (by omega)) _
        refine hdie_of _ hf2 (fun h => ?_)
        have hmf : m / (2 ^ (v - 1) * m') = 2 := by
          rw [hmm', show v = (v - 1) + 1 by omega, pow_succ]
          rw [show 2 ^ (v - 1) * 2 * m' = 2 * (2 ^ (v - 1) * m') by ring]
          exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num))
            (fun h0 => by rw [h0, mul_zero] at hmm'; exact hm0 hmm')))
        rw [hmf] at h
        rcases (Nat.dvd_prime Nat.prime_two).1 h with h | h
        · exact hgcd1 h
        · exact hg2 h

end R1F2

/-! ## Consequences through `lemmaR1F2` (the branch is found by the proof, not supplied):
* R1F2c (q = 3, third term dies): n = 168 = 7·24, a = (1, 113, 54): 113 ≡ 1 (mod 56), 113 ≢ 1
  (mod 3), gcd(24, 54) = 6.
* R1F2o/R2a: n = 56 = 7·8, a = (29, 1, 26). -/
theorem consequence_R1F2c_168 (e : Fin 3 → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (7 ^ 1 * 24), χ.Odd → 7 ^ 1 ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ ((![1, 113, 54] : Fin 3 → ℕ) j) = 0) :
    classSum ![1, 113, 54] e 1 = 0 ∧ classSum ![1, 113, 54] e 113 = 0 ∧
      classSum ![1, 113, 54] e 54 = 0 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hfp : fullPts 7 24 (![1, 113, 54] : Fin 3 → ℕ) = {1, 113} := by decide
  exact lemmaR1F2 (p := 7) (r := 1) (m := 24) (by norm_num) le_rfl (by norm_num) (by norm_num)
    _ e hP 1 113 54 (by decide) (by norm_num) (by rw [hfp]; decide)
    (by rw [hfp]; decide) (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem consequence_R1F2o_56 (e : Fin 3 → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (7 ^ 1 * 8), χ.Odd → 7 ^ 1 ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ ((![29, 1, 26] : Fin 3 → ℕ) j) = 0) :
    classSum ![29, 1, 26] e 29 = 0 ∧ classSum ![29, 1, 26] e 1 = 0 ∧
      classSum ![29, 1, 26] e 26 = 0 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hfp : fullPts 7 8 (![29, 1, 26] : Fin 3 → ℕ) = {29, 1} := by decide
  exact lemmaR1F2 (p := 7) (r := 1) (m := 8) (by norm_num) le_rfl (by norm_num) (by norm_num)
    _ e hP 29 1 26 (by decide) (by norm_num) (by rw [hfp]; decide)
    (by rw [hfp]; decide) (by norm_num) (by norm_num) (by norm_num) (by decide)

#print axioms Erdos634.LemmaSR1F2.lemmaR1F2
#print axioms Erdos634.LemmaSR1F2.consequence_R1F2c_168
#print axioms Erdos634.LemmaSR1F2.consequence_R1F2o_56

end Erdos634.LemmaSR1F2
