/-
Lemma S, node A5: **Lemma S on the EVEN branch** (n ≡ 2 mod 4), assembled
(round2/PROOF_round2.md §4.2–4.5, §4.7; PROOF_lemmaS.md P2).

  Lemma S: if a prime p ≥ 7 divides n, then R(a) = R₀(a).   [here: n = p^r m, m ≡ 2 (mod 4)]

Chain: e ∈ R(a) ⇒ Lemma P's hypothesis (Lemma C criterion, `mem_relSpace_iff_odd`) ⇒ for every
full I-point x (p ∤ x, gcd(x, m′) = 1, m = 2m′) E_x = 0 (`fullEven`: Theorem T at the top
conductor, then D1 for P1 and D2 for P2) ⇒ E_x = 0 for every I-point (Elim, `lemmaElim`, which is
stated for every m, with f(m) = m′) ⇒ R(a) = R₀(a) (Lemma R).
The only configurations the argument does not reach are r = 1, m′ = 3, p ∈ {7, 11}, i.e.
n ∈ {42, 66}; they are Corollary F (`LemmaS.lemmaS_finite`, a kernel-checked certificate).
Formalization debt, not /goal progress.
-/
import Mathlib
import Erdos634.Draft.LemmaSEvenD
import Erdos634.Draft.LemmaSR
import Erdos634.Draft.CaseACorF

open scoped BigOperators
open Finset

namespace Erdos634.LemmaSEven

open DirichletCharacter
open Erdos634.LemmaS (relSpace trivSpace)
open Erdos634.LemmaSC (bracket)
open Erdos634.LemmaSPhi (dm)
open Erdos634.LemmaSElim (classSum lemmaElim)
open Erdos634.LemmaSIso (fpc)
open Erdos634.LemmaSEvenT (Phi5)
open Erdos634.LemmaSEvenComp
open Erdos634.LemmaSEvenTop
open Erdos634.LemmaSEvenD

/-- Exactly two odd entries: indices i, j odd, k even. -/
theorem exists_ijk (a : Fin 3 → ℕ) (hs : (a 0 + a 1 + a 2) % 2 = 0)
    (h2 : ¬ (2 ∣ a 0 ∧ 2 ∣ a 1 ∧ 2 ∣ a 2)) :
    ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ a i % 2 = 1 ∧ a j % 2 = 1 ∧ a k % 2 = 0 := by
  rcases Nat.mod_two_eq_zero_or_one (a 0) with h0 | h0 <;>
  rcases Nat.mod_two_eq_zero_or_one (a 1) with h1 | h1 <;>
  rcases Nat.mod_two_eq_zero_or_one (a 2) with h3 | h3
  · exact absurd ⟨Nat.dvd_of_mod_eq_zero h0, Nat.dvd_of_mod_eq_zero h1, Nat.dvd_of_mod_eq_zero h3⟩ h2
  · omega
  · omega
  · exact ⟨1, 2, 0, by decide, by decide, by decide, h1, h3, h0⟩
  · omega
  · exact ⟨0, 2, 1, by decide, by decide, by decide, h0, h3, h1⟩
  · exact ⟨0, 1, 2, by decide, by decide, by decide, h0, h1, h3⟩
  · omega

theorem sum3q (f : Fin 3 → ℚ) (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∑ t, f t = f i + f j + f k := by
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals first
    | exact absurd rfl hij | exact absurd rfl hik | exact absurd rfl hjk
    | (simp [Fin.sum_univ_three]; done) | (simp [Fin.sum_univ_three]; ring)

theorem fin3_cover (t i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    t = i ∨ t = j ∨ t = k := by
  revert t i j k; decide

section Full
variable {p r m m' : ℕ} [hp : Fact p.Prime] [NeZero m] [NeZero m']

/-- **All full I-points vanish** (EVEN branch; outside r = 1, m′ = 3, p < 13). -/
theorem fullEven (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (hm : m = 2 * m')
    (hodd : m' % 2 = 1) (hexc : ¬ (r = 1 ∧ m' = 3 ∧ p < 13)) (a : Fin 3 → ℕ) (e : Fin 3 → ℚ)
    (hpos : ∀ t, 0 < a t) (hsum : a 0 + a 1 + a 2 = p ^ r * m)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (x : ℕ) (hx : x ∈ univ.image a) (hpx : ¬ p ∣ x) (hxm : x.Coprime m') :
    classSum a e x = 0 := by
  have hdvd : m' ∣ m := Dvd.intro_left 2 hm.symm
  have hs2 : (a 0 + a 1 + a 2) % 2 = 0 := by
    rw [hsum, hm]; simp [Nat.mul_mod]
  have h2 : ¬ (2 ∣ a 0 ∧ 2 ∣ a 1 ∧ 2 ∣ a 2) := by
    rintro ⟨h0, h1, h3⟩
    have := Nat.dvd_gcd h0 (Nat.dvd_gcd h1 h3)
    rw [hgcd] at this; omega
  obtain ⟨i, j, k, hij, hik, hjk, hi, hj, hk⟩ := exists_ijk a hs2 h2
  -- the top conductor, with a suitable η₀
  have hm'4 : m' % 4 ≠ 2 := by omega
  obtain ⟨η, hη, hcase⟩ : ∃ η : DirichletCharacter ℂ m', η.IsPrimitive ∧
      (2 ≤ r ∨ (r = 1 ∧ (η.Even ∨ ∃ P : Finset (ZMod (p ^ r)),
        (∀ v : ZMod (p ^ r), IsUnit v → (PhiTop p r m' η a e i j k v ≠ 0 ∨
          PhiTop p r m' η a e i j k (-v) ≠ 0) → v ∈ P) ∧ P.card < p - 1))) := by
    by_cases hr2 : 2 ≤ r
    · obtain ⟨η, hη⟩ := Erdos634.LemmaSGprime.exists_primitive (NeZero.ne m') hm'4
      exact ⟨η, hη, Or.inl hr2⟩
    have hr1 : r = 1 := by omega
    by_cases h3 : m' = 3
    · obtain ⟨η, hη⟩ := Erdos634.LemmaSGprime.exists_primitive (NeZero.ne m') hm'4
      have hp13 : 13 ≤ p := by
        by_contra hlt; exact hexc ⟨hr1, h3, by omega⟩
      refine ⟨η, hη, Or.inr ⟨hr1, Or.inr ⟨(
        [2 * ((2 : ZMod (p ^ r))⁻¹ * a i), -(2 * ((2 : ZMod (p ^ r))⁻¹ * a i)),
         (2 : ZMod (p ^ r))⁻¹ * a i, -((2 : ZMod (p ^ r))⁻¹ * a i),
         2 * ((2 : ZMod (p ^ r))⁻¹ * a j), -(2 * ((2 : ZMod (p ^ r))⁻¹ * a j)),
         (2 : ZMod (p ^ r))⁻¹ * a j, -((2 : ZMod (p ^ r))⁻¹ * a j),
         ((a k / 2 : ℕ) : ZMod (p ^ r)), -((a k / 2 : ℕ) : ZMod (p ^ r))]).toFinset, ?_, ?_⟩⟩⟩
      · intro v _ hv
        rw [List.mem_toFinset]
        rcases hv with hv | hv
        · rcases PhiTop_supp hp7 η a e i j k v hv with h1 | h1 | h1 | h1 | h1 <;> rw [h1] <;> simp
        · rcases PhiTop_supp hp7 η a e i j k (-v) hv with h1 | h1 | h1 | h1 | h1 <;>
            rw [← neg_neg v, h1] <;> simp
      · exact lt_of_le_of_lt (List.toFinset_card_le _) (by simp; omega)
    · obtain ⟨η, hη, hev⟩ := (Erdos634.LemmaSParity.exists_even_primitive_iff (NeZero.ne m')
        hm'4).2 ⟨h3, by omega⟩
      exact ⟨η, hη, Or.inr ⟨hr1, Or.inl hev⟩⟩
  have hsym := top_sym hp7 hr hpm hm hodd hdvd hη a e hP i j k hij hik hjk hi hj hk hcase
  obtain ⟨hk0, hT⟩ := top_T hp7 hr hpm hm hodd hdvd hη a e hsum i j k hij hik hjk hk hsym
  -- dictionary between cT and e on full indices
  have hηne : ∀ b : ℕ, b.Coprime m' → η (b : ZMod m') ≠ 0 := by
    intro b hb
    obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime b m').2 hb
    rw [← hu]; exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
  have hcodd : ∀ t, a t % 2 = 1 → ¬ p ∣ a t ∧ (a t).Coprime m' →
      cT p m' η a e t = (e t : ℂ) * η (a t : ZMod m') := by
    intro t ht hf; unfold cT; rw [if_pos hf, if_pos ht]
  have hcnf : ∀ t, ¬ (¬ p ∣ a t ∧ (a t).Coprime m') → cT p m' η a e t = 0 := by
    intro t hf; unfold cT; rw [if_neg hf]
  have hzero : ∀ t, a t % 2 = 1 → ¬ p ∣ a t ∧ (a t).Coprime m' → cT p m' η a e t = 0 →
      e t = 0 := by
    intro t ht hf h0
    rw [hcodd t ht hf] at h0
    exact_mod_cast (mul_eq_zero.1 h0).resolve_right (hηne _ hf.2)
  -- the class sum, index by index
  have hcs : classSum a e x = (if a i = x then e i else 0) + (if a j = x then e j else 0) +
      (if a k = x then e k else 0) := by
    unfold classSum; rw [sum_filter, sum3q _ i j k hij hik hjk]
  have hfx : ¬ p ∣ x ∧ x.Coprime m' := ⟨hpx, hxm⟩
  rw [hcs]
  by_cases hkx : a k = x
  · -- the even point
    have hix : a i ≠ x := fun h => by omega
    have hjx : a j ≠ x := fun h => by omega
    rw [if_neg hix, if_neg hjx, if_pos hkx]
    have hf : ¬ p ∣ a k ∧ (a k).Coprime m' := hkx ▸ hfx
    have hk' : ¬ a k % 2 = 1 := by omega
    unfold cT at hk0
    rw [if_pos hf, if_neg hk'] at hk0
    have hb : (a k / 2).Coprime m' :=
      Nat.Coprime.coprime_dvd_left (Dvd.intro_left 2 (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hk))) hf.2
    simp only [zero_add]
    exact_mod_cast (mul_eq_zero.1 hk0).resolve_right (hηne _ hb)
  rw [if_neg hkx, add_zero]
  by_cases hix : a i = x <;> by_cases hjx : a j = x
  · -- both odd indices carry x
    have hfi : ¬ p ∣ a i ∧ (a i).Coprime m' := hix ▸ hfx
    have hfj : ¬ p ∣ a j ∧ (a j).Coprime m' := hjx ▸ hfx
    rw [if_pos hix, if_pos hjx]
    have hij' : a i = a j := hix.trans hjx.symm
    rcases hT with ⟨h1, h2⟩ | ⟨-, h⟩ | ⟨h, -⟩
    · rw [hzero i hi hfi h1, hzero j hj hfj h2, add_zero]
    · rw [hcodd i hi hfi, hcodd j hj hfj, show (a j : ZMod m') = a i by rw [hij']] at h
      have : (((e i : ℚ) : ℂ) + (e j : ℚ)) * η (a i : ZMod m') = 0 := by linear_combination h
      exact_mod_cast (mul_eq_zero.1 this).resolve_right (hηne _ hfi.2)
    · exfalso
      rw [hij'] at h
      have h2u := isUnit_small (r := r) hp.out (k := 2) (by norm_num) (by norm_num) hp7
      haveI : Fact (1 < p ^ r) := ⟨Nat.one_lt_pow (by omega) hp.out.one_lt⟩
      have hju : IsUnit ((a j : ℕ) : ZMod (p ^ r)) := (ZMod.isUnit_iff_coprime _ _).2
        (Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hfj.1).symm)
      have : ((2 : ℕ) : ZMod (p ^ r)) * a j = 0 := by push_cast; linear_combination h
      exact (h2u.mul hju).ne_zero this
  · -- only i carries x
    have hfi : ¬ p ∣ a i ∧ (a i).Coprime m' := hix ▸ hfx
    rw [if_pos hix, if_neg hjx, add_zero]
    by_cases hfj : ¬ p ∣ a j ∧ (a j).Coprime m'
    · have hne : a i ≠ a j := fun h => hjx (h ▸ hix)
      rcases hT with ⟨h1, -⟩ | ⟨hβ, -⟩ | ⟨hβ, -⟩
      · exact hzero i hi hfi h1
      · exact (lemmaD1 hp7 hr hpm hm hodd hdvd a e hpos hsum hP i j k hij hik hjk hi hj hk hfi hfj
          hβ hne).1
      · exact (lemmaD2 hp7 hr hpm hm hodd hdvd a e hpos hsum hP i j k hij hik hjk hi hj hk hfi hfj
          hβ).1
    · have hcj := hcnf j hfj
      rcases hT with ⟨h1, -⟩ | ⟨-, h⟩ | ⟨-, h⟩
      · exact hzero i hi hfi h1
      · exact hzero i hi hfi (by rw [hcj, add_zero] at h; exact h)
      · exact hzero i hi hfi (by rw [hcj, mul_zero] at h; exact h)
  · -- only j carries x
    have hfj : ¬ p ∣ a j ∧ (a j).Coprime m' := hjx ▸ hfx
    rw [if_neg hix, if_pos hjx, zero_add]
    by_cases hfi : ¬ p ∣ a i ∧ (a i).Coprime m'
    · have hne : a i ≠ a j := fun h => hix (h ▸ hjx)
      rcases hT with ⟨-, h2⟩ | ⟨hβ, -⟩ | ⟨hβ, -⟩
      · exact hzero j hj hfj h2
      · exact (lemmaD1 hp7 hr hpm hm hodd hdvd a e hpos hsum hP i j k hij hik hjk hi hj hk hfi hfj
          hβ hne).2
      · exact (lemmaD2 hp7 hr hpm hm hodd hdvd a e hpos hsum hP i j k hij hik hjk hi hj hk hfi hfj
          hβ).2
    · have hci := hcnf i hfi
      have hη1 : η (-1) ≠ 0 := by
        rcases η.even_or_odd with h | h
        · rw [show η (-1) = 1 from h]; exact one_ne_zero
        · rw [show η (-1) = -1 from h]; norm_num
      rcases hT with ⟨-, h2⟩ | ⟨-, h⟩ | ⟨-, h⟩
      · exact hzero j hj hfj h2
      · exact hzero j hj hfj (by rw [hci, zero_add] at h; exact h)
      · rw [hci] at h
        exact hzero j hj hfj ((mul_eq_zero.1 h.symm).resolve_left hη1)
  · -- x is odd but neither odd index carries it: impossible
    exfalso
    obtain ⟨t, -, ht⟩ := mem_image.1 hx
    have : t = i ∨ t = j ∨ t = k := fin3_cover t i j k hij hik hjk
    rcases this with rfl | rfl | rfl
    · exact hix ht
    · exact hjx ht
    · exact hkx ht

end Full

/-- `fpc m ∣ dm m x` (x full at the odd part of m) forces gcd(x, m′) = 1 when m = 2m′. -/
theorem cop_of_fpc {m m' x : ℕ} (hm : m = 2 * m') (hodd : m' % 2 = 1) (hm'0 : 0 < m')
    (h : fpc m ∣ dm m x) : x.Coprime m' := by
  have hfpc : fpc m = m' := by
    unfold fpc; rw [if_pos (by omega), hm, Nat.mul_div_cancel_left m' (by norm_num)]
  rw [hfpc] at h
  have hg : m.gcd x ∣ m := Nat.gcd_dvd_left _ _
  obtain ⟨t, ht⟩ := h
  have h1 : m = m' * t * m.gcd x := by
    unfold dm at ht; rw [← ht, Nat.div_mul_cancel hg]
  have h2 : m.gcd x * t = 2 := by
    have : m' * (m.gcd x * t) = m' * 2 := by
      rw [show m' * (m.gcd x * t) = m' * t * m.gcd x by ring, ← h1, hm]; ring
    exact Nat.eq_of_mul_eq_mul_left hm'0 this
  have hg2 : m.gcd x ∣ 2 := Dvd.intro t h2
  have hdvd : m' ∣ m := Dvd.intro_left 2 hm.symm
  have hd1 : x.gcd m' ∣ m.gcd x :=
    Nat.dvd_gcd (dvd_trans (Nat.gcd_dvd_right x m') hdvd) (Nat.gcd_dvd_left x m')
  rcases (Nat.dvd_prime Nat.prime_two).1 (dvd_trans hd1 hg2) with h | h
  · exact h
  · have : 2 ∣ m' := h ▸ Nat.gcd_dvd_right x m'
    omega

/-- **Lemma S, EVEN branch, unconditional**: n = p^r m, p ≥ 7 prime, p ∤ m, m ≡ 2 (mod 4). -/
theorem lemmaS_even {p r m : ℕ} [hp : Fact p.Prime] [NeZero m] (hp7 : 7 ≤ p) (hr : 1 ≤ r)
    (hpm : ¬ p ∣ m) (hm4 : m % 4 = 2)
    (a : Fin 3 → ℕ) (hpos : ∀ i, 0 < a i) (hsum : ∑ i, a i = p ^ r * m)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) :
    relSpace (p ^ r * m) a = trivSpace (p ^ r * m) a := by
  haveI : NeZero (p ^ r * m) := ⟨Nat.mul_ne_zero (pow_ne_zero _ hp.out.ne_zero) (NeZero.ne m)⟩
  have hsum3 : a 0 + a 1 + a 2 = p ^ r * m := by rw [← hsum, Fin.sum_univ_three]
  by_cases hexc : r = 1 ∧ m / 2 = 3 ∧ p < 13
  · obtain ⟨rfl, h3, hp13⟩ := hexc
    have hm6 : m = 6 := by omega
    subst hm6
    have hp' : p = 7 ∨ p = 11 := by
      have := hp.out
      interval_cases p <;> first | (left; rfl) | (right; rfl) | (exfalso; revert this; decide)
    have hn : p ^ 1 * 6 = 21 ∨ p ^ 1 * 6 = 28 ∨ p ^ 1 * 6 = 42 ∨ p ^ 1 * 6 = 66 := by
      rcases hp' with rfl | rfl <;> norm_num
    exact Erdos634.LemmaS.lemmaS_finite hn a hpos hsum hgcd
  set m' := m / 2 with hm'_def
  have hm : m = 2 * m' := by omega
  have hodd : m' % 2 = 1 := by omega
  haveI : NeZero m' := ⟨by omega⟩
  have hgcd' : univ.gcd a = 1 := by
    apply Nat.eq_one_of_dvd_one
    rw [← hgcd]
    exact Nat.dvd_gcd (Finset.gcd_dvd (mem_univ 0))
      (Nat.dvd_gcd (Finset.gcd_dvd (mem_univ 1)) (Finset.gcd_dvd (mem_univ 2)))
  refine Erdos634.LemmaSR.lemmaR a hpos hsum hgcd hp.out
    (dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) m) (fun e he j hpj => ?_)
  have hcrit := (Erdos634.LemmaSC.mem_relSpace_iff_odd a e).1 he
  have hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0 := fun χ ho _ => hcrit χ ho
  have hall := lemmaElim hp7 hr hpm a e hsum3 hgcd' hP (fun x hx hpx hfull =>
    fullEven hp7 hr hpm hm hodd hexc a e hpos hsum3 hgcd hP x hx hpx
      (cop_of_fpc hm hodd (by omega) hfull)) (a j) (mem_image_of_mem a (mem_univ j)) hpj
  unfold classSum at hall
  rw [filter_filter]
  rw [← hall]
  refine sum_congr ?_ (fun _ _ => rfl)
  ext k
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨by rw [h]; exact hpj, h⟩

/-! ## Instances (derived from the chain, not computed by an engine). -/

/-- n = 70 = 7·10 (p = 7, r = 1, m = 10 ≡ 2 mod 4), tile (3, 33, 34). -/
theorem instance_70 : relSpace (7 ^ 1 * 10) ![3, 33, 34] = trivSpace (7 ^ 1 * 10) ![3, 33, 34] := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact lemmaS_even (p := 7) (r := 1) (m := 10) (by norm_num) le_rfl (by norm_num) (by norm_num)
    _ (by decide) (by decide) (by decide)

/-- n = 98 = 7²·2 (p = 7, r = 2: the N(a) per-group branch), tile (1, 3, 94). -/
theorem instance_98 : relSpace (7 ^ 2 * 2) ![1, 3, 94] = trivSpace (7 ^ 2 * 2) ![1, 3, 94] := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact lemmaS_even (p := 7) (r := 2) (m := 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) _ (by decide) (by decide) (by decide)

/-- **Non-vacuity of D2's hypotheses**: the pattern P2 occurs, n = 70, a = (3, 53, 14)
(53 ≡ −3 mod 7, 7 | 14, 3 and 53 prime to 5); e = 0 meets Lemma P's hypothesis. -/
theorem witness_D2 : ((fun _ => 0 : Fin 3 → ℚ) 0 = 0) ∧ ((fun _ => 0 : Fin 3 → ℚ) 1 = 0) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact lemmaD2 (p := 7) (r := 1) (m := 10) (m' := 5) (by norm_num) le_rfl (by norm_num) rfl rfl
    (by norm_num) ![3, 53, 14] (fun _ => 0) (by decide) (by decide) (fun χ _ _ => by simp)
    0 1 2 (by decide) (by decide) (by decide) rfl rfl rfl ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩ (by decide)

/-- **Non-vacuity of D1's hypotheses**: the pattern P1 with distinct values occurs, n = 70,
a = (1, 29, 40) (29 ≡ 1 mod 7, 1 ≠ 29, both prime to 35). -/
theorem witness_D1 : ((fun _ => 0 : Fin 3 → ℚ) 0 = 0) ∧ ((fun _ => 0 : Fin 3 → ℚ) 1 = 0) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact lemmaD1 (p := 7) (r := 1) (m := 10) (m' := 5) (by norm_num) le_rfl (by norm_num) rfl rfl
    (by norm_num) ![1, 29, 40] (fun _ => 0) (by decide) (by decide) (fun χ _ _ => by simp)
    0 1 2 (by decide) (by decide) (by decide) rfl rfl rfl ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩ (by decide) (by decide)

/-- **Non-vacuity of D1 in its substantive branch** (3 ∥ m′, so the descent to f₂ = m′/3 runs):
n = 7·30 = 210 (m = 30, m′ = 15), a = (1, 71, 138): 71 ≡ 1 (mod 35), 71 ≡ −1 (mod 3),
3 | 138, gcd(30, 138) = 6. -/
theorem witness_D1_descent :
    ((fun _ => 0 : Fin 3 → ℚ) 0 = 0) ∧ ((fun _ => 0 : Fin 3 → ℚ) 1 = 0) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact lemmaD1 (p := 7) (r := 1) (m := 30) (m' := 15) (by norm_num) le_rfl (by norm_num) rfl rfl
    (by norm_num) ![1, 71, 138] (fun _ => 0) (by decide) (by decide) (fun χ _ _ => by simp)
    0 1 2 (by decide) (by decide) (by decide) rfl rfl rfl ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩ (by decide) (by decide)

#print axioms Erdos634.LemmaSEven.fullEven
#print axioms Erdos634.LemmaSEven.lemmaS_even
#print axioms Erdos634.LemmaSEven.instance_70
#print axioms Erdos634.LemmaSEven.instance_98
#print axioms Erdos634.LemmaSEven.witness_D2
#print axioms Erdos634.LemmaSEven.witness_D1
#print axioms Erdos634.LemmaSEven.witness_D1_descent

end Erdos634.LemmaSEven
