/-
Lemma S, node A5, class EVEN (n ≡ 2 mod 4): **the top-conductor component formula and the parity
N± at odd level** (round2/PROOF_round2.md §2 "Halving", "Top element", §4.1 N±).

Setting: n = p^r·m with m = 2m′, m′ odd, p ≥ 7 prime, p ∤ m.  Instead of passing to level n′
through Lemma H, we work at level n directly (Lemma C already carries the Euler factor at 2):
for η primitive mod m′ (raised to level m) and ψ primitive mod p^r, a full I-point a (p ∤ a,
gcd(a, m′) = 1) contributes
  a odd :  ψ(a)η(a)(1 − ψ̄(2)η̄(2))        [the paper's η(2)[2β] − [β] after halving],
  a even:  ψ(a/2)η(a/2),
and a non-full or non-I point contributes 0.  So Σ_j e_j[x_j]_χ = ψ(Φ) with Φ the five-point element
`LemmaSEvenT.Phi5` (points a_i, a_i/2, a_j, a_j/2, a_k/2 for the odd indices i, j and the even
index k).  Then N±:
  * r ≥ 2: Φ = η(−1)[−1]Φ, by N(a) with the per-index count (the points of one index,
    ±a, ±a/2, are pairwise incongruent mod p; 3 indices < p);
  * r = 1, η even: N(b);
  * r = 1, η odd: N(c), when the support of Φ + [−1]Φ has fewer than p − 1 points.
Proved here: `primChar_lift'`, `top_term`, `psi_Phi5`, `top_formula`, `top_vanish`,
`lemmaN_groups`, `inj_group` (N± itself is `LemmaSEvenTop.top_sym`).
Formalization debt, not /goal progress.
-/
import Mathlib
import Erdos634.Draft.LemmaSL
import Erdos634.Draft.LemmaSEvenT

open scoped BigOperators
open Finset

namespace Erdos634.LemmaSEvenComp

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi (chi dm conductor_chi bracket_p_dvd bracket_unit sum_indicator)
open Erdos634.LemmaSN (pred_dvd lemmaN_a lemmaN_b lemmaN_c)
open Erdos634.LemmaSIso (conductor_changeLevel_of_isPrimitive)
open Erdos634.LemmaSEvenT (Phi5)

/-- The primitive part of a raised character, at any residue prime to the lower level. -/
theorem primChar_lift' {f m : ℕ} [NeZero f] [NeZero m] (h : f ∣ m) (η₀ : DirichletCharacter ℂ f)
    (b : ℕ) (hb : b.Coprime f) :
    (changeLevel h η₀).primitiveCharacter (b : ZMod (changeLevel h η₀).conductor) = η₀ (b : ZMod f) := by
  obtain ⟨U, hU⟩ := ZMod.unitsMap_surjective h (ZMod.unitOfCoprime b hb)
  set c := (U : ZMod m).val
  have hc : c.Coprime m := ZMod.val_coe_unit_coprime U
  have hcb : (c : ZMod f) = (b : ZMod f) := by
    have := congrArg Units.val hU
    rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime] at this
    rw [← this]; simp only [c]; rw [ZMod.natCast_val]
  have hcond : (changeLevel h η₀).conductor ∣ f := conductor_dvd_of_mem_conductorSet _ ⟨h, η₀, rfl⟩
  have h1 : ((c : ℕ) : ZMod (changeLevel h η₀).conductor) = (b : ZMod _) := by
    rw [ZMod.natCast_eq_natCast_iff] at hcb ⊢; exact hcb.of_dvd hcond
  rw [← h1, Erdos634.LemmaSL.primChar_lift h η₀ c hc, hcb]

theorem small_cop {p r k : ℕ} (hp : p.Prime) (hk : 0 < k) (hk7 : k < 7) (hp7 : 7 ≤ p) :
    k.Coprime (p ^ r) :=
  Nat.Coprime.pow_right r (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2
    (fun h => by have := Nat.le_of_dvd hk h; omega)))

theorem isUnit_small {p r k : ℕ} (hp : p.Prime) (hk : 0 < k) (hk7 : k < 7) (hp7 : 7 ≤ p) :
    IsUnit ((k : ℕ) : ZMod (p ^ r)) :=
  (ZMod.isUnit_iff_coprime k (p ^ r)).2 (small_cop hp hk hk7 hp7)

section Top
variable {p r m m' : ℕ} [hp : Fact p.Prime] [NeZero m] [NeZero m']

/-- **One term at the top conductor** (η primitive mod m′, raised to m = 2m′). -/
theorem top_term (hpm : ¬ p ∣ m) (hm : m = 2 * m') (hodd : m' % 2 = 1) (hdvd : m' ∣ m)
    {ψ : DirichletCharacter ℂ (p ^ r)} (hψ : ψ.IsPrimitive) {η : DirichletCharacter ℂ m'}
    (hη : η.IsPrimitive) (a : ℕ) (hpa : ¬ p ∣ a) :
    bracket (chi ψ (changeLevel hdvd η)) a =
      if a.Coprime m' then
        (if a % 2 = 1 then ψ (a : ZMod (p ^ r)) * η (a : ZMod m') * (1 - ψ⁻¹ 2 * (η 2)⁻¹)
          else ψ ((a / 2 : ℕ) : ZMod (p ^ r)) * η ((a / 2 : ℕ) : ZMod m'))
      else 0 := by
  set η' := changeLevel hdvd η
  have hc : η'.conductor = m' := conductor_changeLevel_of_isPrimitive hdvd hη
  rw [bracket_unit hpm hψ η' a hpa]
  have hm'0 : 0 < m' := Nat.pos_of_ne_zero (NeZero.ne m')
  have h2m' : (2 : ℕ).Coprime m' := Nat.coprime_two_left.2 (Nat.odd_iff.2 hodd)
  by_cases hcop : a.Coprime m'
  · rw [if_pos hcop]
    by_cases ha : a % 2 = 1
    · rw [if_pos ha]
      have hg : m.gcd a = 1 := by
        rw [hm, Nat.gcd_comm]
        exact Nat.Coprime.mul_right (Nat.coprime_two_right.2 (Nat.odd_iff.2 ha)) hcop
      have hdm : dm m a = m := by simp [dm, hg]
      rw [if_pos (by rw [hc, hdm, hm]; exact Dvd.intro_left 2 rfl)]
      have hE : eulerPrimes (dm m a) η'.conductor = {2} := by
        rw [hdm, hc]
        ext ℓ; simp only [eulerPrimes, mem_filter, Nat.mem_primeFactors, mem_singleton]
        constructor
        · rintro ⟨⟨hl, hlm, -⟩, hlm'⟩
          rw [hm] at hlm
          rcases (Nat.Prime.dvd_mul hl).1 hlm with h2 | h2
          · exact (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 h2
          · exact absurd h2 hlm'
        · rintro rfl
          exact ⟨⟨Nat.prime_two, by rw [hm]; exact dvd_mul_right 2 m', NeZero.ne m⟩,
            fun h => by omega⟩
      have hT : (m.totient : ℂ) / (dm m a).totient = 1 := by
        rw [hdm]; exact div_self (by exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne m))).ne')
      rw [hE, prod_singleton, hT, hg, Nat.div_one, primChar_lift' hdvd η a hcop,
        MulChar.inv_apply_eq_inv' η'.primitiveCharacter, primChar_lift' hdvd η 2 h2m']
      simp only [Nat.cast_ofNat, MulChar.inv_apply_eq_inv']
      ring
    · rw [if_neg ha]
      have ha2 : a = 2 * (a / 2) := by omega
      have hb : (a / 2).Coprime m' := Nat.Coprime.coprime_dvd_left (Dvd.intro_left 2 ha2.symm) hcop
      have hg : m.gcd a = 2 := by
        rw [hm, ha2, Nat.gcd_mul_left, Nat.coprime_comm.1 hb, mul_one]
      have hdm : dm m a = m' := by unfold dm; rw [hg, hm, Nat.mul_div_cancel_left m' (by norm_num)]
      rw [if_pos (by rw [hc, hdm])]
      have hE : eulerPrimes (dm m a) η'.conductor = ∅ := by
        rw [hdm, hc]
        ext ℓ; simp only [eulerPrimes, mem_filter, Nat.mem_primeFactors, Finset.notMem_empty,
          iff_false]
        rintro ⟨⟨-, h, -⟩, h'⟩; exact h' h
      have hT : (m.totient : ℂ) / (dm m a).totient = 1 := by
        rw [hdm, hm, Nat.totient_mul h2m', Nat.totient_two, one_mul]
        exact div_self (by exact_mod_cast (Nat.totient_pos.2 hm'0).ne')
      rw [hE, prod_empty, hT, hg, primChar_lift' hdvd η (a / 2) hb]
      ring
  · rw [if_neg hcop, if_neg]
    rw [hc]
    intro hd
    apply hcop
    have hg : m.gcd a ∣ m := Nat.gcd_dvd_left _ _
    obtain ⟨t, ht⟩ := hd
    have h1 : m = m' * t * m.gcd a := by
      unfold dm at ht; rw [← ht, Nat.div_mul_cancel hg]
    have h2 : m.gcd a * t = 2 := by
      have : m' * (m.gcd a * t) = m' * 2 := by
        rw [show m' * (m.gcd a * t) = m' * t * m.gcd a by ring, ← h1, hm]; ring
      exact Nat.eq_of_mul_eq_mul_left hm'0 this
    have hg2 : m.gcd a ∣ 2 := Dvd.intro t h2
    have hd1 : a.gcd m' ∣ m.gcd a :=
      Nat.dvd_gcd (dvd_trans (Nat.gcd_dvd_right a m') hdvd) (Nat.gcd_dvd_left a m')
    have hd2 : a.gcd m' ∣ 2 := dvd_trans hd1 hg2
    rcases (Nat.dvd_prime Nat.prime_two).1 hd2 with h | h
    · exact h
    · have : 2 ∣ m' := h ▸ Nat.gcd_dvd_right a m'
      omega

/-- ψ applied to the five-point element. -/
theorem psi_Phi5 {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (c1 c2 c3 z : ℂ)
    (w y y' V : ZMod N) :
    ∑ u : (ZMod N)ˣ, ψ (u : ZMod N) * Phi5 c1 c2 c3 z w y y' V (u : ZMod N) =
      c1 * ψ (2 * w) - z * c1 * ψ w + c2 * ψ y - z * c2 * ψ y' + c3 * ψ V := by
  have key : ∀ (X : ZMod N) (c : ℂ),
      ∑ u : (ZMod N)ˣ, ψ (u : ZMod N) * (if (u : ZMod N) = X then c else 0) = c * ψ X := by
    intro X c
    have := sum_indicator ψ 1 X isUnit_one
    simp only [mul_one, map_one, inv_one] at this
    rw [← this, mul_sum]
    refine sum_congr rfl (fun u _ => ?_)
    split_ifs <;> ring
  unfold Phi5
  simp only [mul_add, sum_add_distrib, key]
  ring

theorem sum3 (f : Fin 3 → ℂ) (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∑ t, f t = f i + f j + f k := by
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals first
    | exact absurd rfl hij | exact absurd rfl hik | exact absurd rfl hjk
    | (simp [Fin.sum_univ_three]; done) | (simp [Fin.sum_univ_three]; ring)

/-- The top-level coefficient of index t: e_t η(b_t) for a full I-point, else 0. -/
noncomputable def cT (p m' : ℕ) (η : DirichletCharacter ℂ m') (a : Fin 3 → ℕ) (e : Fin 3 → ℚ)
    (t : Fin 3) : ℂ :=
  if ¬ p ∣ a t ∧ (a t).Coprime m' then
    (e t : ℂ) * (if a t % 2 = 1 then η (a t : ZMod m') else η ((a t / 2 : ℕ) : ZMod m'))
  else 0

theorem two_mul_half (hp7 : 7 ≤ p) : (2 : ZMod (p ^ r)) * (2 : ZMod (p ^ r))⁻¹ = 1 := by
  have := isUnit_small (r := r) hp.out (k := 2) (by norm_num) (by norm_num) hp7
  rw [Nat.cast_ofNat] at this
  exact ZMod.mul_inv_of_unit _ this

/-- **The top component** = ψ(Φ) for the five-point Φ. -/
theorem top_formula (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (hm : m = 2 * m')
    (hodd : m' % 2 = 1) (hdvd : m' ∣ m) {ψ : DirichletCharacter ℂ (p ^ r)} (hψ : ψ.IsPrimitive)
    {η : DirichletCharacter ℂ m'} (hη : η.IsPrimitive) (a : Fin 3 → ℕ) (e : Fin 3 → ℚ)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hi : a i % 2 = 1)
    (hj : a j % 2 = 1) (hk : a k % 2 = 0) :
    ∑ t, (e t : ℂ) * bracket (chi ψ (changeLevel hdvd η)) (a t) =
      ∑ u : (ZMod (p ^ r))ˣ, ψ (u : ZMod (p ^ r)) *
        Phi5 (cT p m' η a e i) (cT p m' η a e j) (cT p m' η a e k) (η 2)⁻¹
          ((2 : ZMod (p ^ r))⁻¹ * a i) (a j) ((2 : ZMod (p ^ r))⁻¹ * a j)
          ((a k / 2 : ℕ) : ZMod (p ^ r)) (u : ZMod (p ^ r)) := by
  rw [psi_Phi5, sum3 _ i j k hij hik hjk]
  set h := (2 : ZMod (p ^ r))⁻¹
  have hh := two_mul_half (r := r) hp7
  have hψh : ψ h = ψ⁻¹ 2 := by
    rw [MulChar.inv_apply_eq_inv']
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, mul_comm, hh, map_one]
  have h2 : ∀ x : ZMod (p ^ r), 2 * (h * x) = x := fun x => by rw [← mul_assoc, hh, one_mul]
  have hodd_t : ∀ t, a t % 2 = 1 → (e t : ℂ) * bracket (chi ψ (changeLevel hdvd η)) (a t) =
      cT p m' η a e t * ψ (2 * (h * a t)) - (η 2)⁻¹ * cT p m' η a e t * ψ (h * a t) := by
    intro t ht
    unfold cT
    by_cases hpa : p ∣ a t
    · rw [bracket_p_dvd hr hpm hψ _ _ hpa, if_neg (fun h' => h'.1 hpa)]; ring
    rw [top_term hpm hm hodd hdvd hψ hη _ hpa, h2, map_mul, hψh]
    simp only [ht, hpa, not_false_eq_true, true_and, ↓reduceIte]
    split_ifs <;> first | ring | (exfalso; contradiction)
  have heven : (e k : ℂ) * bracket (chi ψ (changeLevel hdvd η)) (a k) =
      cT p m' η a e k * ψ ((a k / 2 : ℕ) : ZMod (p ^ r)) := by
    unfold cT
    by_cases hpa : p ∣ a k
    · rw [bracket_p_dvd hr hpm hψ _ _ hpa, if_neg (fun h' => h'.1 hpa)]; ring
    rw [top_term hpm hm hodd hdvd hψ hη _ hpa]
    simp only [hk, hpa, not_false_eq_true, true_and, zero_ne_one, ↓reduceIte]
    split_ifs <;> first | ring | (exfalso; contradiction)
  rw [hodd_t i hi, hodd_t j hj, heven, h2, h2]
  ring

/-- The parity of χ = ψη and Lemma P's hypothesis give ψ(Φ) = 0 for every primitive ψ with
ψ(−1) = −η(−1). -/
theorem top_vanish (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) (hm : m = 2 * m')
    (hodd : m' % 2 = 1) (hdvd : m' ∣ m) {η : DirichletCharacter ℂ m'} (hη : η.IsPrimitive)
    (a : Fin 3 → ℕ) (e : Fin 3 → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hi : a i % 2 = 1)
    (hj : a j % 2 = 1) (hk : a k % 2 = 0) :
    ∀ ψ : DirichletCharacter ℂ (p ^ r), ψ.IsPrimitive → ψ (-1) = -η (-1) →
      ∑ u : (ZMod (p ^ r))ˣ, ψ (u : ZMod (p ^ r)) *
        Phi5 (cT p m' η a e i) (cT p m' η a e j) (cT p m' η a e k) (η 2)⁻¹
          ((2 : ZMod (p ^ r))⁻¹ * a i) (a j) ((2 : ZMod (p ^ r))⁻¹ * a j)
          ((a k / 2 : ℕ) : ZMod (p ^ r)) (u : ZMod (p ^ r)) = 0 := by
  intro ψ hψ hψε
  rw [← top_formula hp7 hr hpm hm hodd hdvd hψ hη a e i j k hij hik hjk hi hj hk]
  have hη2 : η (-1) * η (-1) = 1 := by
    rcases η.even_or_odd with h | h
    · rw [show η (-1) = 1 from h]; ring
    · rw [show η (-1) = -1 from h]; ring
  have hodd' : (chi ψ (changeLevel hdvd η)).Odd := by
    show (chi ψ (changeLevel hdvd η)) (-1) = -1
    rw [MulChar.coeToFun_mul, Pi.mul_apply,
      Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_right (p ^ r) m) ψ,
      Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_left m (p ^ r)) (changeLevel hdvd η),
      Erdos634.LemmaSG2.changeLevel_neg_one hdvd η, hψε]
    linear_combination -hη2
  exact hP _ hodd' (by rw [conductor_chi hpm hψ]; exact Nat.dvd_mul_right _ _)

end Top

/-! ## N(a) with a per-group count (r ≥ 2) -/

theorem cast_p_of_unitsMap {p r : ℕ} [hp : Fact p.Prime] (hr : 2 ≤ r) (v w : (ZMod (p ^ r))ˣ)
    (h : ZMod.unitsMap (pred_dvd p r) v = ZMod.unitsMap (pred_dvd p r) w) :
    ZMod.castHom (dvd_pow_self p (by omega : r ≠ 0)) (ZMod p) (v : ZMod (p ^ r)) =
      ZMod.castHom (dvd_pow_self p (by omega : r ≠ 0)) (ZMod p) (w : ZMod (p ^ r)) := by
  have h1 := congrArg Units.val h
  rw [ZMod.unitsMap_val, ZMod.unitsMap_val] at h1
  have hp1 : p ∣ p ^ (r - 1) := dvd_pow_self p (by omega)
  have hc := ZMod.castHom_comp hp1 (pred_dvd p r)
  have e1 := RingHom.congr_fun hc (v : ZMod (p ^ r))
  have e2 := RingHom.congr_fun hc (w : ZMod (p ^ r))
  simp only [RingHom.comp_apply, ZMod.castHom_apply] at e1 e2
  simp only [ZMod.castHom_apply]
  rw [← e1, ← e2, h1]

/-- **N(a), per-group form** (r ≥ 2): if the support of Φ ∪ −Φ is covered by k < p groups, each
injective mod p on units, then Φ = −ε[−1]Φ. -/
theorem lemmaN_groups {p r : ℕ} [hp : Fact p.Prime] (hr : 2 ≤ r) (Φ : (ZMod (p ^ r))ˣ → ℂ)
    {ε : ℂ} (hε : ε = 1 ∨ ε = -1)
    (h : ∀ ψ : DirichletCharacter ℂ (p ^ r), ψ.IsPrimitive → ψ (-1) = ε →
      ∑ u : (ZMod (p ^ r))ˣ, ψ (u : ZMod (p ^ r)) * Φ u = 0)
    {k : ℕ} (hk : k < p) (T : Fin k → Finset (ZMod (p ^ r)))
    (hsupp : ∀ v : (ZMod (p ^ r))ˣ, Φ v ≠ 0 ∨ Φ (-v) ≠ 0 → ∃ i, (v : ZMod (p ^ r)) ∈ T i)
    (hinj : ∀ i, ∀ a ∈ T i, ∀ b ∈ T i, IsUnit a → IsUnit b →
      ZMod.castHom (dvd_pow_self p (by omega : r ≠ 0)) (ZMod p) a =
        ZMod.castHom (dvd_pow_self p (by omega : r ≠ 0)) (ZMod p) b → a = b) :
    ∀ u, Φ u = -ε * Φ (-u) := by
  classical
  refine lemmaN_a (by omega) Φ hε h (fun u => ?_)
  rw [Erdos634.LemmaSFC.card_N (by omega), if_neg (by omega)]
  refine lt_of_le_of_lt ?_ hk
  calc _ ≤ (univ.biUnion (fun i : Fin k => univ.filter (fun v : (ZMod (p ^ r))ˣ =>
          ZMod.unitsMap (pred_dvd p r) v = ZMod.unitsMap (pred_dvd p r) u ∧
            (v : ZMod (p ^ r)) ∈ T i))).card := by
        refine card_le_card (fun v hv => ?_)
        obtain ⟨-, hvu, hs⟩ := mem_filter.1 hv
        obtain ⟨i, hi⟩ := hsupp v hs
        exact mem_biUnion.2 ⟨i, mem_univ _, mem_filter.2 ⟨mem_univ _, hvu, hi⟩⟩
    _ ≤ ∑ i : Fin k, 1 := by
        refine card_biUnion_le.trans (sum_le_sum (fun i _ => card_le_one.2 (fun v hv w hw => ?_)))
        obtain ⟨-, hv1, hv2⟩ := mem_filter.1 hv
        obtain ⟨-, hw1, hw2⟩ := mem_filter.1 hw
        exact Units.ext (hinj i _ hv2 _ hw2 v.isUnit w.isUnit
          (cast_p_of_unitsMap hr v w (hv1.trans hw1.symm)))
    _ = k := by simp

/-- A group of points k·x (k in an integer list with pairwise differences free of primes ≥ 7) is
injective mod p on units. -/
theorem inj_group {p r : ℕ} [hp : Fact p.Prime] (hp7 : 7 ≤ p) (hr : r ≠ 0) (L : List ℤ)
    (hL : ∀ a ∈ L, ∀ b ∈ L, a ≠ b →
      (a - b).natAbs ∈ ({1, 2, 3, 4, 5, 6, 8, 9, 10, 12} : Finset ℕ)) (x : ZMod (p ^ r)) :
    ∀ a ∈ (L.map (fun k : ℤ => (k : ZMod (p ^ r)) * x)).toFinset,
    ∀ b ∈ (L.map (fun k : ℤ => (k : ZMod (p ^ r)) * x)).toFinset, IsUnit a → IsUnit b →
      ZMod.castHom (dvd_pow_self p hr) (ZMod p) a = ZMod.castHom (dvd_pow_self p hr) (ZMod p) b →
        a = b := by
  intro a ha b hb hua _ hab
  simp only [List.mem_toFinset, List.mem_map] at ha hb
  obtain ⟨k1, hk1, rfl⟩ := ha
  obtain ⟨k2, hk2, rfl⟩ := hb
  by_cases hk : k1 = k2
  · rw [hk]
  exfalso
  have hxu : IsUnit x := isUnit_of_mul_isUnit_right hua
  have hX : ZMod.castHom (dvd_pow_self p hr) (ZMod p) x ≠ 0 :=
    (hxu.map (ZMod.castHom (dvd_pow_self p hr) (ZMod p))).ne_zero
  rw [map_mul, map_mul, map_intCast, map_intCast] at hab
  have h0 : (((k1 - k2 : ℤ)) : ZMod p) = 0 := by
    have : ((k1 : ZMod p) - k2) * ZMod.castHom (dvd_pow_self p hr) (ZMod p) x = 0 := by
      rw [sub_mul, hab, sub_self]
    push_cast
    exact (mul_eq_zero.1 this).resolve_right hX
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
  have hd : p ∣ (k1 - k2).natAbs := Int.natCast_dvd.1 h0
  have hmem := hL k1 hk1 k2 hk2 hk
  have hpos : 0 < (k1 - k2).natAbs := Int.natAbs_pos.2 (sub_ne_zero.2 hk)
  have hle := Nat.le_of_dvd hpos hd
  have hpr := hp.out
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h <;> rw [h] at hd hle <;>
    first
    | omega
    | (interval_cases p <;> revert hd hpr <;> decide)

/-- The support of the five-point element. -/
theorem Phi5_supp {R : Type*} [CommRing R] [DecidableEq R] {c1 c2 c3 z : ℂ} {w y y' V u : R}
    (h : Phi5 c1 c2 c3 z w y y' V u ≠ 0) :
    (c1 ≠ 0 ∧ (u = 2 * w ∨ u = w)) ∨ (c2 ≠ 0 ∧ (u = y ∨ u = y')) ∨ (c3 ≠ 0 ∧ u = V) := by
  by_contra hno
  push Not at hno
  apply h
  unfold Phi5
  obtain ⟨h1, h2, h3⟩ := hno
  by_cases hc1 : c1 = 0
  · by_cases hc2 : c2 = 0
    · by_cases hc3 : c3 = 0
      · subst hc1 hc2 hc3; simp
      · rw [if_neg (h3 hc3)]; subst hc1 hc2; simp
    · rw [if_neg (h2 hc2).1, if_neg (h2 hc2).2]
      by_cases hc3 : c3 = 0
      · subst hc1 hc3; simp
      · rw [if_neg (h3 hc3)]; subst hc1; simp
  · rw [if_neg (h1 hc1).1, if_neg (h1 hc1).2]
    by_cases hc2 : c2 = 0
    · by_cases hc3 : c3 = 0
      · subst hc2 hc3; simp
      · rw [if_neg (h3 hc3)]; subst hc2; simp
    · rw [if_neg (h2 hc2).1, if_neg (h2 hc2).2]
      by_cases hc3 : c3 = 0
      · subst hc3; simp
      · rw [if_neg (h3 hc3)]; simp

end Erdos634.LemmaSEvenComp

#print axioms Erdos634.LemmaSEvenComp.top_formula
#print axioms Erdos634.LemmaSEvenComp.top_vanish
#print axioms Erdos634.LemmaSEvenComp.lemmaN_groups
#print axioms Erdos634.LemmaSEvenComp.inj_group
#print axioms Erdos634.LemmaSEvenComp.primChar_lift'
