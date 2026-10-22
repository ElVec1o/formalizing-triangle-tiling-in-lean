/-
Lemma S, node A5, class EVEN (n ≡ 2 mod 4): **Lemmas D1 and D2** (round2/PROOF_round2.md §4.3,
§4.4), the two patterns Theorem T leaves.

  D2 (pattern P2: both odd points full, a_j ≡ −a_i mod p^r, hence p | a_k).  The top relation for
  every primitive η mod m′ and G′ give g := a_i/(−a_j) ∈ Sp(m′); g ≢ 1 (else n | a_i + a_j), so
  3 ∥ m′, g₃ = −1, τ(g) = 1 and e_j = −e_i.  One conductor down, f₂ = m′/3 with η₂ even
  primitive mod f₂, the relation is (e_i − e_j)ψ(a_i)η₂(a_i)(1 − ψ̄(2)η̄₂(2))(1 − ψ̄(3)η̄₂(3)) = 0
  for every odd primitive ψ; Lemma G2 supplies ψ with both Euler factors nonzero, so e_i = e_j.
  Hence e_i = e_j = 0.

  D1 (pattern P1: both odd points full, a_i ≠ a_j, a_j ≡ a_i mod p^r).  Top relation + G′:
  g = a_i/a_j ∈ Sp(m′), g ≢ 1 (else a_i = a_j), so 3 ∥ m′, τ = 1 and e_j = e_i.  Then 3 | a_k,
  gcd(m, a_k) = 6 and a_k/6 ≡ −a_i/3 (mod p^r).  At f₂ = m′/3 (η₂ even) the element
  (e_i + e_j)η₂(a_i)([a_i] − η̄₂(2)[a_i/2] − η̄₂(3)[a_i/3] + η̄₂(6)[a_i/6]) + 2e_kη₂(a_k/6)[−a_i/3]
  is even (N(b) for r = 1, N(a) per-group for r ≥ 2); at the point a_i/2 only one term lives and
  −a_i/2 is not a support point, so e_i + e_j = 0.  Hence e_i = e_j = 0.
Formalization debt, not /goal progress.
-/
import Mathlib
import Erdos634.Draft.LemmaSEvenTop
import Erdos634.Draft.LemmaSG2Avoid
import Erdos634.Draft.LemmaSR1p

open scoped BigOperators
open Finset

namespace Erdos634.LemmaSEvenD

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi (chi dm conductor_chi bracket_p_dvd bracket_unit sum_indicator)
open Erdos634.LemmaSN (pred_dvd lemmaN_b)
open Erdos634.LemmaSIso (conductor_changeLevel_of_isPrimitive)
open Erdos634.LemmaSGprime (Sp tau)
open Erdos634.LemmaSEvenT (nek small_units)
open Erdos634.LemmaSEvenComp
open Erdos634.LemmaSEvenTop

/-- Sp(d) for odd d: a non-trivial special element is −1 at 3 (3 ∥ d) and 1 elsewhere. -/
theorem sp_odd {d : ℕ} (hd0 : d ≠ 0) (hd : d % 2 = 1) {z : ℤ} (hSp : Sp d z)
    (hz1 : ¬ z ≡ 1 [ZMOD d]) :
    d.factorization 3 = 1 ∧ z ≡ -1 [ZMOD 3] ∧ z ≡ 1 [ZMOD ((d / 3 : ℕ) : ℤ)] ∧ tau d z = 1 := by
  classical
  obtain ⟨q, hq, hbad⟩ : ∃ q ∈ d.primeFactors, ¬ z ≡ 1 [ZMOD (q : ℤ) ^ d.factorization q] := by
    by_contra hno; push Not at hno
    exact hz1 (Erdos634.LemmaSR1p.modEq_of_components hd0 hno)
  have h2d : ¬ 2 ∣ d := by omega
  obtain ⟨rfl, hv3, hz3⟩ : q = 3 ∧ d.factorization 3 = 1 ∧ z ≡ -1 [ZMOD 3] := by
    rcases hSp q hq with h | ⟨h1, h2, h3⟩ | ⟨h1, -, -⟩
    · exact absurd h hbad
    · subst h1; exact ⟨rfl, h2, h3⟩
    · subst h1; exact absurd (Nat.dvd_of_mem_primeFactors hq) h2d
  refine ⟨hv3, hz3, ?_, ?_⟩
  · have hd3 : d / 3 = d / 3 ^ d.factorization 3 := by rw [hv3, pow_one]
    rw [hd3]
    have hm'0 : d / 3 ^ d.factorization 3 ≠ 0 := (Nat.ordCompl_pos 3 hd0).ne'
    have hm'm : d / 3 ^ d.factorization 3 ∣ d := Nat.ordCompl_dvd d 3
    refine Erdos634.LemmaSR1p.modEq_of_components hm'0 (fun ℓ hℓ => ?_)
    have hℓp := Nat.prime_of_mem_primeFactors hℓ
    have hℓm : ℓ ∈ d.primeFactors :=
      Nat.mem_primeFactors.2 ⟨hℓp, dvd_trans (Nat.dvd_of_mem_primeFactors hℓ) hm'm, hd0⟩
    have hℓ3 : ℓ ≠ 3 := by
      rintro rfl; exact Nat.not_dvd_ordCompl Nat.prime_three hd0 (Nat.dvd_of_mem_primeFactors hℓ)
    have hfac : (d / 3 ^ d.factorization 3).factorization ℓ = d.factorization ℓ := by
      simp only [Nat.factorization_ordCompl, Finsupp.erase_ne hℓ3]
    rw [hfac]
    rcases hSp ℓ hℓm with h | ⟨h1, -, -⟩ | ⟨h1, -, -⟩
    · exact h
    · exact absurd h1 hℓ3
    · subst h1; exact absurd (Nat.dvd_of_mem_primeFactors hℓm) h2d
  · unfold tau
    rw [card_eq_one]
    refine ⟨3, ?_⟩
    ext q'
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hq', hb⟩
      rcases hSp q' hq' with h | ⟨h1, -, -⟩ | ⟨h1, -, -⟩
      · exact absurd h hb
      · exact h1
      · subst h1; exact absurd (Nat.dvd_of_mem_primeFactors hq') h2d
    · rintro rfl; exact ⟨hq, hbad⟩

/-- An integer representative of x/(σy) mod d. -/
theorem zrep {d : ℕ} [NeZero d] (x y : ℕ) (hy : y.Coprime d) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    ∃ z : ℤ, z * (σ * y) ≡ x [ZMOD d] := by
  set u : ZMod d := ((σ * y : ℤ) : ZMod d) with hu_def
  have hu : IsUnit u := by
    have hy' := (ZMod.isUnit_iff_coprime y d).2 hy
    rcases hσ with rfl | rfl
    · rw [hu_def]; push_cast; rw [one_mul]; exact hy'
    · rw [hu_def]; push_cast; rw [neg_one_mul]; exact hy'.neg
  refine ⟨(((x : ZMod d) * u⁻¹).val : ℤ), ?_⟩
  rw [← ZMod.intCast_eq_intCast_iff, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val,
    ← hu_def, Int.cast_natCast, mul_assoc, ZMod.inv_mul_of_unit _ hu, mul_one]

section D
variable {p r m m' : ℕ} [hp : Fact p.Prime] [NeZero m] [NeZero m']

/-- **One term one conductor down** (f₂ = m′/3): an odd point prime to m′. -/
theorem descent_term (hpm : ¬ p ∣ m) (hm : m = 2 * m') (hodd : m' % 2 = 1) {f : ℕ} [NeZero f]
    (hmf : m' = 3 * f) (h3f : ¬ 3 ∣ f) (hdvd : f ∣ m) {ψ : DirichletCharacter ℂ (p ^ r)}
    (hψ : ψ.IsPrimitive) {η : DirichletCharacter ℂ f} (hη : η.IsPrimitive) (a : ℕ)
    (hpa : ¬ p ∣ a) (ha : a % 2 = 1) (hcop : a.Coprime m') :
    bracket (chi ψ (changeLevel hdvd η)) a = ψ (a : ZMod (p ^ r)) * η (a : ZMod f) *
      (1 - ψ⁻¹ 2 * (η 2)⁻¹) * (1 - ψ⁻¹ 3 * (η 3)⁻¹) := by
  set η' := changeLevel hdvd η
  have hc : η'.conductor = f := conductor_changeLevel_of_isPrimitive hdvd hη
  rw [bracket_unit hpm hψ η' a hpa]
  have hfodd : f % 2 = 1 := by omega
  have h2f : (2 : ℕ).Coprime f := Nat.coprime_two_left.2 (Nat.odd_iff.2 hfodd)
  have h3f' : (3 : ℕ).Coprime f := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3f
  have haf : a.Coprime f := hcop.coprime_dvd_right (Dvd.intro_left 3 hmf.symm)
  have hg : m.gcd a = 1 := by
    rw [hm, Nat.gcd_comm]
    exact Nat.Coprime.mul_right (Nat.coprime_two_right.2 (Nat.odd_iff.2 ha)) hcop
  have hdm : dm m a = m := by simp [dm, hg]
  rw [if_pos (by rw [hc, hdm]; exact hdvd)]
  have hE : eulerPrimes (dm m a) η'.conductor = {2, 3} := by
    rw [hdm, hc]
    ext ℓ; simp only [eulerPrimes, mem_filter, Nat.mem_primeFactors, mem_insert, mem_singleton]
    constructor
    · rintro ⟨⟨hl, hlm, -⟩, hlf⟩
      rw [hm, hmf] at hlm
      rcases (Nat.Prime.dvd_mul hl).1 hlm with h2 | h2
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 h2)
      · rcases (Nat.Prime.dvd_mul hl).1 h2 with h3 | h3
        · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_three).1 h3)
        · exact absurd h3 hlf
    · rintro (rfl | rfl)
      · exact ⟨⟨Nat.prime_two, by rw [hm]; exact dvd_mul_right 2 m', NeZero.ne m⟩,
          fun h => by omega⟩
      · exact ⟨⟨Nat.prime_three, by rw [hm, hmf]; exact Dvd.intro_left (2 * f) (by ring),
          NeZero.ne m⟩, h3f⟩
  have hT : (m.totient : ℂ) / (dm m a).totient = 1 := by
    rw [hdm]; exact div_self (by exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne m))).ne')
  rw [hE, prod_insert (by decide), prod_singleton, hT, hg, Nat.div_one,
    primChar_lift' hdvd η a haf]
  simp only [MulChar.inv_apply_eq_inv']
  rw [primChar_lift' hdvd η 2 h2f, primChar_lift' hdvd η 3 h3f']
  simp only [Nat.cast_ofNat]
  ring

/-- **The even point one conductor down** (gcd(m, v) = 6, so d_v = f₂ and w(d_v) = 2). -/
theorem descent_term_six (hpm : ¬ p ∣ m) (hm : m = 2 * m') (hodd : m' % 2 = 1) {f : ℕ} [NeZero f]
    (hmf : m' = 3 * f) (h3f : ¬ 3 ∣ f) (hdvd : f ∣ m) {ψ : DirichletCharacter ℂ (p ^ r)}
    (hψ : ψ.IsPrimitive) {η : DirichletCharacter ℂ f} (hη : η.IsPrimitive) (v : ℕ)
    (hpv : ¬ p ∣ v) (hg : m.gcd v = 6) :
    bracket (chi ψ (changeLevel hdvd η)) v =
      2 * (ψ ((v / 6 : ℕ) : ZMod (p ^ r)) * η ((v / 6 : ℕ) : ZMod f)) := by
  set η' := changeLevel hdvd η
  have hc : η'.conductor = f := conductor_changeLevel_of_isPrimitive hdvd hη
  rw [bracket_unit hpm hψ η' v hpv]
  have hm6 : m = 6 * f := by rw [hm, hmf]; ring
  have hf0 : 0 < f := Nat.pos_of_ne_zero (NeZero.ne f)
  have hfodd : f % 2 = 1 := by omega
  have h6f : (6 : ℕ).Coprime f := by
    have h2f : (2 : ℕ).Coprime f := Nat.coprime_two_left.2 (Nat.odd_iff.2 hfodd)
    have h3f' : (3 : ℕ).Coprime f := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3f
    exact Nat.Coprime.mul_left h2f h3f'
  have hdm : dm m v = f := by
    unfold dm; rw [hg, hm6, Nat.mul_div_cancel_left f (by norm_num)]
  rw [if_pos (by rw [hc, hdm])]
  have hE : eulerPrimes (dm m v) η'.conductor = ∅ := by
    rw [hdm, hc]
    ext ℓ; simp only [eulerPrimes, mem_filter, Nat.mem_primeFactors, Finset.notMem_empty, iff_false]
    rintro ⟨⟨-, h, -⟩, h'⟩; exact h' h
  have hT : (m.totient : ℂ) / (dm m v).totient = 2 := by
    rw [hdm, hm6, Nat.totient_mul h6f]
    have : (Nat.totient 6 : ℂ) = 2 := by
      have : Nat.totient 6 = 2 := by decide
      rw [this]; norm_num
    rw [Nat.cast_mul, this]
    field_simp [(by exact_mod_cast (Nat.totient_pos.2 hf0).ne' : ((f.totient : ℕ) : ℂ) ≠ 0)]
  have hb : (v / 6).Coprime f := by
    have h6v : 6 ∣ v := hg ▸ Nat.gcd_dvd_right m v
    have hv : v = 6 * (v / 6) := (Nat.mul_div_cancel' h6v).symm
    have : m.gcd v = 6 * f.gcd (v / 6) := by rw [hm6, hv, Nat.gcd_mul_left, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [hg] at this
    have h1 : f.gcd (v / 6) = 1 := by omega
    exact Nat.coprime_comm.1 h1
  rw [hE, prod_empty, hT, hg, primChar_lift' hdvd η (v / 6) hb]
  ring

/-- The D1 element (points 6w, 3w, 2w, w, −2w). -/
noncomputable def PhiD1 {R : Type*} [CommRing R] [DecidableEq R] (A B b2 b3 : ℂ) (w : R)
    (u : R) : ℂ :=
  (if u = 6 * w then A else 0) + (if u = 3 * w then -b2 * A else 0) +
    (if u = 2 * w then -b3 * A else 0) + (if u = w then b2 * b3 * A else 0) +
    (if u = -2 * w then B else 0)

theorem psi_PhiD1 {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (A B b2 b3 : ℂ) (w : ZMod N) :
    ∑ u : (ZMod N)ˣ, ψ (u : ZMod N) * PhiD1 A B b2 b3 w (u : ZMod N) =
      A * ψ (6 * w) - b2 * A * ψ (3 * w) - b3 * A * ψ (2 * w) + b2 * b3 * A * ψ w +
        B * ψ (-2 * w) := by
  have key : ∀ (X : ZMod N) (c : ℂ),
      ∑ u : (ZMod N)ˣ, ψ (u : ZMod N) * (if (u : ZMod N) = X then c else 0) = c * ψ X := by
    intro X c
    have := sum_indicator ψ 1 X isUnit_one
    simp only [mul_one, map_one, inv_one] at this
    rw [← this, mul_sum]
    refine sum_congr rfl (fun u _ => ?_)
    split_ifs <;> ring
  unfold PhiD1
  simp only [mul_add, sum_add_distrib, key]
  ring

theorem PhiD1_supp {R : Type*} [CommRing R] [DecidableEq R] {A B b2 b3 : ℂ} {w u : R}
    (h : PhiD1 A B b2 b3 w u ≠ 0) :
    u = 6 * w ∨ u = 3 * w ∨ u = 2 * w ∨ u = w ∨ u = -2 * w := by
  by_contra hno
  push Not at hno
  apply h
  unfold PhiD1
  rw [if_neg hno.1, if_neg hno.2.1, if_neg hno.2.2.1, if_neg hno.2.2.2.1, if_neg hno.2.2.2.2]
  ring

end D

theorem f_facts {m' : ℕ} (hm'0 : m' ≠ 0) (hv3 : m'.factorization 3 = 1) :
    m' = 3 * (m' / 3) ∧ ¬ 3 ∣ m' / 3 := by
  have h3 : 3 ∣ m' := by have := Nat.ordProj_dvd m' 3; rw [hv3, pow_one] at this; exact this
  refine ⟨(Nat.mul_div_cancel' h3).symm, ?_⟩
  intro h9
  have h9' : 3 ^ 2 ∣ m' := by
    obtain ⟨t, ht⟩ := h9
    exact ⟨t, by rw [← Nat.mul_div_cancel' h3, ht]; ring⟩
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hm'0).1 h9'
  omega

theorem sum3_nat (a : Fin 3 → ℕ) (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    a i + a j + a k = a 0 + a 1 + a 2 := by
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals first
    | exact absurd rfl hij | exact absurd rfl hik | exact absurd rfl hjk
    | omega
    | (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> omega)

section D2
variable {p r m m' : ℕ} [hp : Fact p.Prime] [NeZero m] [NeZero m']

/-- n ∤ a_i + a_j (0 < a_i + a_j < n) when both odd: the sum cannot vanish mod p^r, mod m′ and
mod 2 at once. -/
theorem no_wrap (hpm : ¬ p ∣ m) (hm : m = 2 * m') (hodd : m' % 2 = 1) (a : Fin 3 → ℕ)
    (hpos : ∀ t, 0 < a t) (hsum : a 0 + a 1 + a 2 = p ^ r * m) (i j k : Fin 3) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (hpd : p ^ r ∣ a i + a j) (hm'd : m' ∣ a i + a j)
    (h2d : 2 ∣ a i + a j) : False := by
  have h2m' : (2 : ℕ).Coprime m' := Nat.coprime_two_left.2 (Nat.odd_iff.2 hodd)
  have hmd : m ∣ a i + a j := hm ▸ Nat.Coprime.mul_dvd_of_dvd_of_dvd h2m' h2d hm'd
  have hn : p ^ r * m ∣ a i + a j :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (Erdos634.LemmaSPhi.cop_pr hpm) hpd hmd
  have h3 := sum3_nat a i j k hij hik hjk
  have := Nat.le_of_dvd (by have := hpos i; omega) hn
  have := hpos k
  omega

/-- **Lemma D2** (pattern P2). -/
theorem lemmaD2 (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (hm : m = 2 * m')
    (hodd : m' % 2 = 1) (hdvd : m' ∣ m) (a : Fin 3 → ℕ) (e : Fin 3 → ℚ) (hpos : ∀ t, 0 < a t)
    (hsum : a 0 + a 1 + a 2 = p ^ r * m)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hi : a i % 2 = 1)
    (hj : a j % 2 = 1) (hk : a k % 2 = 0)
    (hfi : ¬ p ∣ a i ∧ (a i).Coprime m') (hfj : ¬ p ∣ a j ∧ (a j).Coprime m')
    (hβ : (a j : ZMod (p ^ r)) = -(a i : ZMod (p ^ r))) :
    e i = 0 ∧ e j = 0 := by
  have rel := top_rel_all hp7 hr hpm hm hodd hdvd a e hsum hP i j k hij hik hjk hi hj hk hfi hfj
    (-1) (Or.inr rfl) (by rw [hβ]; push_cast; ring)
  obtain ⟨z, hz⟩ := zrep (d := m') (a i) (a j) hfj.2 (-1) (Or.inr rfl)
  rcases Erdos634.LemmaSL.rel_Gprime (d := m') (by omega) (e i) (e j) (a i) (a j) hfi.2 hfj.2 (-1)
    (Or.inr rfl) z hz rel with h | ⟨hSp, hE⟩
  · exact h
  have hzm : ((z : ℤ) : ZMod m') * (-(a j : ZMod m')) = a i := by
    have := (ZMod.intCast_eq_intCast_iff _ _ _).2 hz
    push_cast at this; linear_combination this
  have hz1 : ¬ z ≡ 1 [ZMOD m'] := by
    intro h1
    have hz1' : ((z : ℤ) : ZMod m') = 1 := by
      have := (ZMod.intCast_eq_intCast_iff z 1 m').2 h1; simpa using this
    rw [hz1'] at hzm
    refine no_wrap hpm hm hodd a hpos hsum i j k hij hik hjk ?_ ?_ (by omega)
    · rw [← ZMod.natCast_eq_zero_iff]; push_cast; rw [hβ]; ring
    · rw [← ZMod.natCast_eq_zero_iff]; push_cast; linear_combination -hzm
  obtain ⟨hv3, hz3, hzf, htau⟩ := sp_odd (NeZero.ne m') hodd hSp hz1
  rw [htau] at hE
  have hE' : e j = -e i := by rw [hE]; push_cast; ring
  obtain ⟨hmf, h3f⟩ := f_facts (NeZero.ne m') hv3
  set f := m' / 3 with hf_def
  haveI : NeZero f := ⟨fun h0 => NeZero.ne m' (by omega)⟩
  have hfm' : f ∣ m' := Dvd.intro_left 3 hmf.symm
  have hfm : f ∣ m := dvd_trans hfm' hdvd
  have hfodd : f % 2 = 1 := by omega
  obtain ⟨η₂, hη₂, hev⟩ := (Erdos634.LemmaSParity.exists_even_primitive_iff (NeZero.ne f)
    (by omega)).2 ⟨fun h => h3f (by omega), by omega⟩
  have hunitf : ∀ b : ℕ, b.Coprime f → η₂ (b : ZMod f) ≠ 0 := by
    intro b hb
    obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime b f).2 hb
    rw [← hu]; exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
  have h2f : (2 : ℕ).Coprime f := Nat.coprime_two_left.2 (Nat.odd_iff.2 hfodd)
  have h3f' : (3 : ℕ).Coprime f := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3f
  have hη2 : η₂ 2 ≠ 0 := by have := hunitf 2 h2f; rwa [Nat.cast_ofNat] at this
  have hη3 : η₂ 3 ≠ 0 := by have := hunitf 3 h3f'; rwa [Nat.cast_ofNat] at this
  obtain ⟨ψ, hψ, hψodd, hψ2, hψ3⟩ :=
    Erdos634.LemmaSG2Avoid.lemmaG2 hp7 hr (η₂ 2)⁻¹ (η₂ 3)⁻¹ (inv_ne_zero hη2) (inv_ne_zero hη3)
  have hodd' : (chi ψ (changeLevel hfm η₂)).Odd := by
    show (chi ψ (changeLevel hfm η₂)) (-1) = -1
    rw [MulChar.coeToFun_mul, Pi.mul_apply,
      Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_right (p ^ r) m) ψ,
      Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_left m (p ^ r)) (changeLevel hfm η₂),
      Erdos634.LemmaSG2.changeLevel_neg_one hfm η₂, show ψ (-1) = -1 from hψodd,
      show η₂ (-1) = 1 from hev, mul_one]
  have hS := hP _ hodd' (by rw [conductor_chi hpm hψ]; exact Nat.dvd_mul_right _ _)
  rw [sum3 _ i j k hij hik hjk] at hS
  have hpk : p ∣ a k := by
    have h3 := sum3_zmod (m := m) a hsum i j k hij hik hjk
    rw [hβ] at h3
    have h0 : ((a k : ℕ) : ZMod (p ^ r)) = 0 := by linear_combination h3
    rw [ZMod.natCast_eq_zero_iff] at h0
    exact dvd_trans (dvd_pow_self p (by omega)) h0
  rw [bracket_p_dvd hr hpm hψ _ _ hpk,
    descent_term hpm hm hodd hmf h3f hfm hψ hη₂ (a i) hfi.1 hi hfi.2,
    descent_term hpm hm hodd hmf h3f hfm hψ hη₂ (a j) hfj.1 hj hfj.2] at hS
  have hψj : ψ (a j : ZMod (p ^ r)) = -ψ (a i : ZMod (p ^ r)) := by
    rw [hβ, show -(a i : ZMod (p ^ r)) = (-1) * a i by ring, map_mul, show ψ (-1) = -1 from hψodd]
    ring
  have hηj : η₂ (a j : ZMod f) = η₂ (a i : ZMod f) := by
    have hc := congrArg (ZMod.castHom hfm' (ZMod f)) hzm
    rw [map_mul, map_neg, map_intCast, map_natCast, map_natCast] at hc
    have hzf' : ((z : ℤ) : ZMod f) = 1 := by
      have := (ZMod.intCast_eq_intCast_iff z 1 f).2 hzf; simpa using this
    rw [hzf'] at hc
    rw [show (a j : ZMod f) = (-1) * a i by linear_combination -hc, map_mul,
      show η₂ (-1) = 1 from hev, one_mul]
  rw [hψj, hηj] at hS
  have hF2 : (1 - ψ⁻¹ 2 * (η₂ 2)⁻¹) ≠ 0 := by
    intro h0
    apply hψ2
    rw [MulChar.inv_apply_eq_inv'] at h0
    apply eq_inv_of_mul_eq_one_left
    have hψ2' : ψ 2 ≠ 0 := by
      have := isUnit_small (r := r) hp.out (k := 2) (by norm_num) (by norm_num) hp7
      rw [Nat.cast_ofNat] at this
      obtain ⟨u, hu⟩ := this; rw [← hu]; exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
    field_simp at h0
    linear_combination h0
  have hF3 : (1 - ψ⁻¹ 3 * (η₂ 3)⁻¹) ≠ 0 := by
    intro h0
    apply hψ3
    rw [MulChar.inv_apply_eq_inv'] at h0
    apply eq_inv_of_mul_eq_one_left
    have hψ3' : ψ 3 ≠ 0 := by
      have := isUnit_small (r := r) hp.out (k := 3) (by norm_num) (by norm_num) hp7
      rw [Nat.cast_ofNat] at this
      obtain ⟨u, hu⟩ := this; rw [← hu]; exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
    field_simp at h0
    linear_combination h0
  have hψi : ψ (a i : ZMod (p ^ r)) ≠ 0 := by
    haveI : Fact (1 < p ^ r) := ⟨Nat.one_lt_pow (by omega) hp.out.one_lt⟩
    obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime (a i) (p ^ r)).2
      (Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hfi.1).symm)
    rw [← hu]; exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
  have hηi : η₂ (a i : ZMod f) ≠ 0 := hunitf _ (hfi.2.coprime_dvd_right hfm')
  have hprod : ψ (a i : ZMod (p ^ r)) * η₂ (a i : ZMod f) * (1 - ψ⁻¹ 2 * (η₂ 2)⁻¹) *
      (1 - ψ⁻¹ 3 * (η₂ 3)⁻¹) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hψi hηi) hF2) hF3
  have key : (((e i : ℚ) : ℂ) - (e j : ℚ)) * (ψ (a i : ZMod (p ^ r)) * η₂ (a i : ZMod f) *
      (1 - ψ⁻¹ 2 * (η₂ 2)⁻¹) * (1 - ψ⁻¹ 3 * (η₂ 3)⁻¹)) = 0 := by linear_combination hS
  have heq : e i = e j := by
    have := (mul_eq_zero.1 key).resolve_right hprod
    exact_mod_cast sub_eq_zero.1 this
  constructor <;> linarith

end D2

section D1
variable {p r m m' : ℕ} [hp : Fact p.Prime] [NeZero m] [NeZero m']

set_option maxHeartbeats 1000000 in
/-- **Lemma D1** (pattern P1). -/
theorem lemmaD1 (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (hm : m = 2 * m')
    (hodd : m' % 2 = 1) (hdvd : m' ∣ m) (a : Fin 3 → ℕ) (e : Fin 3 → ℚ) (hpos : ∀ t, 0 < a t)
    (hsum : a 0 + a 1 + a 2 = p ^ r * m)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hi : a i % 2 = 1)
    (hj : a j % 2 = 1) (hk : a k % 2 = 0)
    (hfi : ¬ p ∣ a i ∧ (a i).Coprime m') (hfj : ¬ p ∣ a j ∧ (a j).Coprime m')
    (hβ : (a j : ZMod (p ^ r)) = (a i : ZMod (p ^ r))) (hne : a i ≠ a j) :
    e i = 0 ∧ e j = 0 := by
  haveI : Fact (1 < p ^ r) := ⟨Nat.one_lt_pow (by omega) hp.out.one_lt⟩
  have rel := top_rel_all hp7 hr hpm hm hodd hdvd a e hsum hP i j k hij hik hjk hi hj hk hfi hfj
    1 (Or.inl rfl) (by rw [hβ]; push_cast; ring)
  obtain ⟨z, hz⟩ := zrep (d := m') (a i) (a j) hfj.2 1 (Or.inl rfl)
  rcases Erdos634.LemmaSL.rel_Gprime (d := m') (by omega) (e i) (e j) (a i) (a j) hfi.2 hfj.2 1
    (Or.inl rfl) z hz rel with h | ⟨hSp, hE⟩
  · exact h
  have hzm : ((z : ℤ) : ZMod m') * (a j : ZMod m') = a i := by
    have := (ZMod.intCast_eq_intCast_iff _ _ _).2 hz
    push_cast at this; linear_combination this
  have h3n := sum3_nat a i j k hij hik hjk
  have hz1 : ¬ z ≡ 1 [ZMOD m'] := by
    intro h1
    have hz1' : ((z : ℤ) : ZMod m') = 1 := by
      have := (ZMod.intCast_eq_intCast_iff z 1 m').2 h1; simpa using this
    rw [hz1', one_mul] at hzm
    have h2m' : (2 : ℕ).Coprime m' := Nat.coprime_two_left.2 (Nat.odd_iff.2 hodd)
    have hA : a i ≡ a j [MOD 2] := by unfold Nat.ModEq; omega
    have hB : a i ≡ a j [MOD m'] := (ZMod.natCast_eq_natCast_iff _ _ _).1 hzm.symm
    have hC := (Nat.modEq_and_modEq_iff_modEq_mul h2m').1 ⟨hA, hB⟩
    have hD : a i ≡ a j [MOD p ^ r] := (ZMod.natCast_eq_natCast_iff _ _ _).1 hβ.symm
    have hF := (Nat.modEq_and_modEq_iff_modEq_mul
      (hm ▸ Erdos634.LemmaSPhi.cop_pr (r := r) hpm)).1 ⟨hD, hC⟩
    have := hpos i; have := hpos j; have := hpos k
    exact hne (Nat.ModEq.eq_of_lt_of_lt hF (by rw [← hm]; omega) (by rw [← hm]; omega))
  obtain ⟨hv3, hz3, hzf, htau⟩ := sp_odd (NeZero.ne m') hodd hSp hz1
  rw [htau] at hE
  have hE' : e j = e i := by rw [hE]; push_cast; ring
  obtain ⟨hmf, h3f⟩ := f_facts (NeZero.ne m') hv3
  set f := m' / 3 with hf_def
  haveI : NeZero f := ⟨fun h0 => NeZero.ne m' (by omega)⟩
  have hfm' : f ∣ m' := Dvd.intro_left 3 hmf.symm
  have hfm : f ∣ m := dvd_trans hfm' hdvd
  have h3m' : 3 ∣ m' := Dvd.intro f hmf.symm
  have hfodd : f % 2 = 1 := by omega
  have h2f : (2 : ℕ).Coprime f := Nat.coprime_two_left.2 (Nat.odd_iff.2 hfodd)
  have h3f' : (3 : ℕ).Coprime f := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3f
  -- the arithmetic of the third point
  have hijf : (a j : ZMod f) = a i := by
    have hc := congrArg (ZMod.castHom hfm' (ZMod f)) hzm
    rw [map_mul, map_intCast, map_natCast, map_natCast] at hc
    have hzf' : ((z : ℤ) : ZMod f) = 1 := by
      have := (ZMod.intCast_eq_intCast_iff z 1 f).2 hzf; simpa using this
    rw [hzf', one_mul] at hc; exact hc
  have hsumf : ∀ d : ℕ, d ∣ m → ((a i : ℕ) : ZMod d) + a j + a k = 0 := by
    intro d hd
    have : ((a i + a j + a k : ℕ) : ZMod d) = 0 := by
      rw [h3n, hsum, Nat.cast_mul, (ZMod.natCast_eq_zero_iff _ _).2 hd, mul_zero]
    push_cast at this; exact this
  have hk3 : 3 ∣ a k := by
    have hc := congrArg (ZMod.castHom h3m' (ZMod 3)) hzm
    rw [map_mul, map_intCast, map_natCast, map_natCast] at hc
    have hz3' : ((z : ℤ) : ZMod 3) = -1 := by
      have := (ZMod.intCast_eq_intCast_iff z (-1) 3).2 hz3; simpa using this
    rw [hz3'] at hc
    have hs3 := hsumf 3 (dvd_trans h3m' hdvd)
    rw [← ZMod.natCast_eq_zero_iff]; linear_combination hs3 + hc
  have hkf : (a k).Coprime f := by
    have hs := hsumf f hfm
    rw [hijf] at hs
    have hu : IsUnit ((a k : ℕ) : ZMod f) := by
      have hai : IsUnit ((a i : ℕ) : ZMod f) :=
        (ZMod.isUnit_iff_coprime _ _).2 (hfi.2.coprime_dvd_right hfm')
      have h2u : IsUnit ((2 : ℕ) : ZMod f) := (ZMod.isUnit_iff_coprime _ _).2 h2f
      rw [show ((a k : ℕ) : ZMod f) = -(((2 : ℕ) : ZMod f) * a i) by push_cast; linear_combination hs]
      exact (h2u.mul hai).neg
    exact (ZMod.isUnit_iff_coprime _ _).1 hu
  have hai : IsUnit ((a i : ℕ) : ZMod (p ^ r)) := (ZMod.isUnit_iff_coprime _ _).2
    (Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hfi.1).symm)
  have hsP := sum3_zmod (m := m) a hsum i j k hij hik hjk
  rw [hβ] at hsP
  have hkP : IsUnit ((a k : ℕ) : ZMod (p ^ r)) := by
    have h2u := isUnit_small (r := r) hp.out (k := 2) (by norm_num) (by norm_num) hp7
    rw [show ((a k : ℕ) : ZMod (p ^ r)) = -(((2 : ℕ) : ZMod (p ^ r)) * a i) by
      push_cast; linear_combination hsP]
    exact (h2u.mul hai).neg
  have hpk : ¬ p ∣ a k := by
    intro hd
    have hc := (ZMod.isUnit_iff_coprime _ _).1 hkP
    have : p ∣ Nat.gcd (a k) (p ^ r) := Nat.dvd_gcd hd (dvd_pow_self p (by omega))
    rw [Nat.Coprime.gcd_eq_one hc] at this; exact hp.out.one_lt.ne' (Nat.dvd_one.1 this)
  have h6k : 6 ∣ a k := by omega
  have hm6 : m = 6 * f := by rw [hm, hmf]; ring
  have h6f : (6 : ℕ).Coprime f := Nat.Coprime.mul_left h2f h3f'
  have hg6 : m.gcd (a k) = 6 := by
    rw [hm6, Nat.gcd_comm, Nat.Coprime.gcd_mul (a k) h6f, Nat.gcd_eq_right h6k,
      Nat.Coprime.gcd_eq_one hkf]
  obtain ⟨η₂, hη₂, hev⟩ := (Erdos634.LemmaSParity.exists_even_primitive_iff (NeZero.ne f)
    (by omega)).2 ⟨fun h => h3f (by omega), by omega⟩
  have hunitf : ∀ b : ℕ, b.Coprime f → η₂ (b : ZMod f) ≠ 0 := by
    intro b hb
    obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime b f).2 hb
    rw [← hu]; exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
  have hη2 : η₂ 2 ≠ 0 := by have := hunitf 2 h2f; rwa [Nat.cast_ofNat] at this
  have hη3 : η₂ 3 ≠ 0 := by have := hunitf 3 h3f'; rwa [Nat.cast_ofNat] at this
  have hηi : η₂ (a i : ZMod f) ≠ 0 := hunitf _ (hfi.2.coprime_dvd_right hfm')
  -- units of ZMod (p ^ r)
  have u2 : IsUnit (2 : ZMod (p ^ r)) := by
    have := isUnit_small (r := r) hp.out (k := 2) (by norm_num) (by norm_num) hp7
    rwa [Nat.cast_ofNat] at this
  have u3 : IsUnit (3 : ZMod (p ^ r)) := by
    have := isUnit_small (r := r) hp.out (k := 3) (by norm_num) (by norm_num) hp7
    rwa [Nat.cast_ofNat] at this
  have u5 : IsUnit (5 : ZMod (p ^ r)) := by
    have := isUnit_small (r := r) hp.out (k := 5) (by norm_num) (by norm_num) hp7
    rwa [Nat.cast_ofNat] at this
  obtain ⟨k4, k6, k8, k9, k10, k12⟩ := small_units u2 u3 u5
  have k2 := u2; have k3 := u3; have k5 := u5
  set w := (6 : ZMod (p ^ r))⁻¹ * (a i : ZMod (p ^ r)) with hw_def
  have h66 : (6 : ZMod (p ^ r)) * (6 : ZMod (p ^ r))⁻¹ = 1 := ZMod.mul_inv_of_unit _ k6
  have h6w : (6 : ZMod (p ^ r)) * w = a i := by rw [hw_def, ← mul_assoc, h66, one_mul]
  have hw : IsUnit w := (IsUnit.of_mul_eq_one_right _ h66).mul hai
  have hk6 : ((a k / 6 : ℕ) : ZMod (p ^ r)) = -2 * w := by
    apply k6.mul_left_cancel
    have : (6 : ZMod (p ^ r)) * ((a k / 6 : ℕ) : ZMod (p ^ r)) = a k := by
      rw [show (6 : ZMod (p ^ r)) = ((6 : ℕ) : ZMod (p ^ r)) by norm_num, ← Nat.cast_mul,
        Nat.mul_div_cancel' h6k]
    rw [this]; linear_combination hsP + 2 * h6w
  set A : ℂ := (((e i : ℚ) : ℂ) + (e j : ℚ)) * η₂ (a i : ZMod f) with hA
  set B : ℂ := 2 * ((e k : ℚ) : ℂ) * η₂ ((a k / 6 : ℕ) : ZMod f) with hB
  set b2 : ℂ := (η₂ 2)⁻¹
  set b3 : ℂ := (η₂ 3)⁻¹
  have hvanD : ∀ ψ : DirichletCharacter ℂ (p ^ r), ψ.IsPrimitive → ψ (-1) = -1 →
      ∑ u : (ZMod (p ^ r))ˣ, ψ (u : ZMod (p ^ r)) * PhiD1 A B b2 b3 w (u : ZMod (p ^ r)) = 0 := by
    intro ψ hψ hψodd
    have hodd' : (chi ψ (changeLevel hfm η₂)).Odd := by
      show (chi ψ (changeLevel hfm η₂)) (-1) = -1
      rw [MulChar.coeToFun_mul, Pi.mul_apply,
        Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_right (p ^ r) m) ψ,
        Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_left m (p ^ r)) (changeLevel hfm η₂),
        Erdos634.LemmaSG2.changeLevel_neg_one hfm η₂, hψodd, show η₂ (-1) = 1 from hev, mul_one]
    have hS := hP _ hodd' (by rw [conductor_chi hpm hψ]; exact Nat.dvd_mul_right _ _)
    rw [sum3 _ i j k hij hik hjk,
      descent_term hpm hm hodd hmf h3f hfm hψ hη₂ (a i) hfi.1 hi hfi.2,
      descent_term hpm hm hodd hmf h3f hfm hψ hη₂ (a j) hfj.1 hj hfj.2,
      descent_term_six hpm hm hodd hmf h3f hfm hψ hη₂ (a k) hpk hg6, hβ, hijf] at hS
    rw [psi_PhiD1]
    have hψ2 : ψ 2 ≠ 0 := by obtain ⟨u, hu⟩ := u2; rw [← hu]; exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
    have hψ3 : ψ 3 ≠ 0 := by obtain ⟨u, hu⟩ := u3; rw [← hu]; exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
    have e6 : ψ (6 * w) = ψ (a i : ZMod (p ^ r)) := by rw [h6w]
    have e3 : ψ (3 * w) = ψ (a i : ZMod (p ^ r)) * ψ⁻¹ 2 := by
      rw [MulChar.inv_apply_eq_inv', ← h6w, show (6 : ZMod (p ^ r)) * w = 2 * (3 * w) by ring,
        map_mul ψ 2 (3 * w)]; field_simp
    have e2 : ψ (2 * w) = ψ (a i : ZMod (p ^ r)) * ψ⁻¹ 3 := by
      rw [MulChar.inv_apply_eq_inv', ← h6w, show (6 : ZMod (p ^ r)) * w = 3 * (2 * w) by ring,
        map_mul ψ 3 (2 * w)]; field_simp
    have e1 : ψ w = ψ (a i : ZMod (p ^ r)) * ψ⁻¹ 2 * ψ⁻¹ 3 := by
      rw [MulChar.inv_apply_eq_inv', MulChar.inv_apply_eq_inv', ← h6w,
        show (6 : ZMod (p ^ r)) * w = 2 * (3 * w) by ring, map_mul ψ 2 (3 * w), map_mul ψ 3 w]
      field_simp
    have em : ψ (-2 * w) = ψ ((a k / 6 : ℕ) : ZMod (p ^ r)) := by rw [hk6]
    rw [e6, e3, e2, e1, em]
    linear_combination hS
  set Φ : (ZMod (p ^ r))ˣ → ℂ := fun v => PhiD1 A B b2 b3 w (v : ZMod (p ^ r)) with hΦ
  have hsymD : ∀ v : (ZMod (p ^ r))ˣ, Φ v = Φ (-v) := by
    rcases Nat.lt_or_ge r 2 with hr1 | hr2
    · obtain rfl : r = 1 := by omega
      exact lemmaN_b Φ hvanD
    · let T : Fin 2 → Finset (ZMod (p ^ r)) := ![G w [6, -6, 3, -3, 2, -2], G w [1, -1]]
      have hsupp : ∀ v : (ZMod (p ^ r))ˣ, Φ v ≠ 0 ∨ Φ (-v) ≠ 0 →
          ∃ t, (v : ZMod (p ^ r)) ∈ T t := by
        intro v hv
        rcases hv with hv | hv
        · rcases PhiD1_supp hv with h1 | h1 | h1 | h1 | h1
          · exact ⟨0, mem_G 6 (by simp) (by rw [h1]; push_cast; ring)⟩
          · exact ⟨0, mem_G 3 (by simp) (by rw [h1]; push_cast; ring)⟩
          · exact ⟨0, mem_G 2 (by simp) (by rw [h1]; push_cast; ring)⟩
          · exact ⟨1, mem_G 1 (by simp) (by rw [h1]; push_cast; ring)⟩
          · exact ⟨0, mem_G (-2) (by simp) (by rw [h1]; push_cast; ring)⟩
        · simp only [Φ, Units.val_neg] at hv
          rcases PhiD1_supp hv with h1 | h1 | h1 | h1 | h1
          · exact ⟨0, mem_G (-6) (by simp) (by rw [← neg_neg (v : ZMod (p ^ r)), h1]; push_cast; ring)⟩
          · exact ⟨0, mem_G (-3) (by simp) (by rw [← neg_neg (v : ZMod (p ^ r)), h1]; push_cast; ring)⟩
          · exact ⟨0, mem_G (-2) (by simp) (by rw [← neg_neg (v : ZMod (p ^ r)), h1]; push_cast; ring)⟩
          · exact ⟨1, mem_G (-1) (by simp) (by rw [← neg_neg (v : ZMod (p ^ r)), h1]; push_cast; ring)⟩
          · exact ⟨0, mem_G 2 (by simp) (by rw [← neg_neg (v : ZMod (p ^ r)), h1]; push_cast; ring)⟩
      have hinj : ∀ t, ∀ x ∈ T t, ∀ y ∈ T t, IsUnit x → IsUnit y →
          ZMod.castHom (dvd_pow_self p (by omega : r ≠ 0)) (ZMod p) x =
            ZMod.castHom (dvd_pow_self p (by omega : r ≠ 0)) (ZMod p) y → x = y := by
        intro t
        fin_cases t
        · exact inj_group hp7 (by omega) [6, -6, 3, -3, 2, -2] (by decide) w
        · exact inj_group hp7 (by omega) [1, -1] (by decide) w
      intro v
      have := lemmaN_groups hr2 Φ (ε := -1) (Or.inr rfl) hvanD (k := 2) (by omega) T hsupp hinj v
      rw [this]; ring
  obtain ⟨U, hU⟩ := u3.mul hw
  have E := hsymD U
  simp only [Φ, Units.val_neg, hU] at E
  simp (disch := first | ring1 | ne_tac | assumption) only [PhiD1, if_pos, if_neg, ↓reduceIte] at E
  have hA0 : A = 0 := by
    have : b2 * A = 0 := by linear_combination -E
    exact (mul_eq_zero.1 this).resolve_left (inv_ne_zero hη2)
  have hsum0 : (((e i : ℚ) : ℂ) + (e j : ℚ)) = 0 := (mul_eq_zero.1 hA0).resolve_right hηi
  have : e i + e j = 0 := by exact_mod_cast hsum0
  constructor <;> linarith

end D1

end Erdos634.LemmaSEvenD

#print axioms Erdos634.LemmaSEvenD.sp_odd
#print axioms Erdos634.LemmaSEvenD.lemmaD1
#print axioms Erdos634.LemmaSEvenD.lemmaD2
