/-
Lemma S, node A5: **parity of primitive characters** (PROOF_lemmaS.md §4 "choose η even. This is
possible iff m_I ∉ {3, 4} (the only moduli ≢ 2 (mod 4) whose primitive characters are all odd)";
round 2 §4.3–4.6 "η even primitive mod f₂ … exists because 3 ∤ f₂"; P1.6 "D2's odd primitive η mod f
exists because 3 ∥ f").

For d ≠ 0, d ≢ 2 (mod 4):
* an EVEN primitive character mod d exists  ⟺  d ∉ {3, 4};
* an ODD  primitive character mod d exists  ⟺  d ∉ {1, 12}.
Prime powers by counting (Σ_{χ primitive} χ(−1) = φ(q^v)[q^v | 2] − φ(q^{v−1})[q^{v−1} | 2], from
LemmaSGpp.sum_prim), then the coprime product (parities multiply, DirichletCRT).
Formalization debt, not /goal progress.
-/
import Mathlib
import Erdos634.Draft.LemmaSGprime
import Erdos634.Draft.LemmaSG2

open scoped BigOperators
open Finset

namespace Erdos634.LemmaSParity

open DirichletCharacter
open Erdos634.LemmaSGpp (sum_prim card_prim)
open Erdos634.LemmaSN (pred_dvd)
open Erdos634.DirichletCRT (isPrimitive_iff decomp)

theorem neg_one_eq_one_iff {N : ℕ} : (-1 : ZMod N) = 1 ↔ N ∣ 2 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  constructor
  · intro h; linear_combination -h
  · intro h; linear_combination -h

/-- An even (resp. odd) primitive character mod d. -/
def EP (d : ℕ) : Prop := ∃ χ : DirichletCharacter ℂ d, χ.IsPrimitive ∧ χ (-1) = 1
def OP (d : ℕ) : Prop := ∃ χ : DirichletCharacter ℂ d, χ.IsPrimitive ∧ χ (-1) = -1

section PP
variable {q v : ℕ} [hq : Fact q.Prime]

theorem pp_counts (hv : 1 ≤ v) :
    ∃ E O : ℕ, (0 < E ↔ EP (q ^ v)) ∧ (0 < O ↔ OP (q ^ v)) ∧
      E + O + (q ^ (v - 1)).totient = (q ^ v).totient ∧
      (E : ℂ) - O = (if q ^ v ∣ 2 then ((q ^ v).totient : ℂ) else 0) -
        (if q ^ (v - 1) ∣ 2 then ((q ^ (v - 1)).totient : ℂ) else 0) := by
  classical
  haveI : NeZero (q ^ v) := ⟨pow_ne_zero _ hq.out.ne_zero⟩
  set Pr := univ.filter (fun χ : DirichletCharacter ℂ (q ^ v) => χ.IsPrimitive)
  set Ev := Pr.filter (fun χ => χ (-1) = 1)
  set Od := Pr.filter (fun χ => ¬ χ (-1) = 1)
  have hsplit := filter_card_add_filter_neg_card_eq_card (s := Pr) (fun χ => χ (-1) = 1)
  have hodd : ∀ χ ∈ Od, χ (-1) = -1 := by
    intro χ hχ
    exact (Erdos634.LemmaSG.val_neg_one χ).resolve_left (mem_filter.1 hχ).2
  refine ⟨Ev.card, Od.card, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro h; obtain ⟨χ, hχ⟩ := card_pos.1 h
      exact ⟨χ, (mem_filter.1 (mem_filter.1 hχ).1).2, (mem_filter.1 hχ).2⟩
    · rintro ⟨χ, hp, he⟩
      exact card_pos.2 ⟨χ, mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, hp⟩, he⟩⟩
  · constructor
    · intro h; obtain ⟨χ, hχ⟩ := card_pos.1 h
      exact ⟨χ, (mem_filter.1 (mem_filter.1 hχ).1).2, hodd χ hχ⟩
    · rintro ⟨χ, hp, ho⟩
      refine card_pos.2 ⟨χ, mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, hp⟩, ?_⟩⟩
      rw [ho]; norm_num
  · rw [hsplit]; exact card_prim hv
  · have hS := sum_prim hv (-1 : (ZMod (q ^ v))ˣ)
    rw [← sum_filter_add_sum_filter_not Pr (fun χ => χ (-1) = 1)] at hS
    simp only [Units.val_neg, Units.val_one] at hS
    rw [sum_congr rfl (fun χ hχ => (mem_filter.1 hχ).2),
      sum_congr rfl (fun χ hχ => hodd χ hχ), sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul] at hS
    simp only [ZMod.cast_neg (pred_dvd q v), ZMod.cast_one (pred_dvd q v), neg_one_eq_one_iff] at hS
    linear_combination hS

theorem pp_parity (hv : 1 ≤ v) (h2 : q ^ v ≠ 2) :
    (EP (q ^ v) ↔ q ^ v ≠ 3 ∧ q ^ v ≠ 4) ∧ OP (q ^ v) := by
  obtain ⟨E, O, hE, hO, hsum, hdiff⟩ := pp_counts (q := q) hv
  have hq2 := hq.out.two_le
  have hqv : 2 ≤ q ^ v := le_trans hq2 (Nat.le_self_pow (by omega) q)
  rw [if_neg (fun h => h2 (le_antisymm (Nat.le_of_dvd (by norm_num) h) hqv))] at hdiff
  have hpow : q ^ v = q ^ (v - 1) * q := by rw [← pow_succ]; congr 1; omega
  have htot : (q ^ v).totient = q ^ (v - 1) * (q - 1) := by
    rw [Nat.totient_prime_pow hq.out (by omega)]
  by_cases hd2 : q ^ (v - 1) ∣ 2
  · rw [if_pos hd2] at hdiff
    have hN : q ^ (v - 1) = 1 ∨ q ^ (v - 1) = 2 := by
      have := Nat.le_of_dvd (by norm_num) hd2
      have := Nat.pos_of_ne_zero (pow_ne_zero (v - 1) hq.out.ne_zero)
      omega
    have hD : (q ^ (v - 1)).totient = 1 := by
      rcases hN with h | h <;> rw [h] <;> decide
    rw [hD] at hdiff hsum
    have hEO : E + 1 = O := by
      have : ((E + 1 : ℕ) : ℂ) = O := by push_cast; linear_combination hdiff
      exact_mod_cast this
    refine ⟨?_, hO.1 (by omega)⟩
    rw [← hE]
    rcases hN with h | h
    · rw [h, one_mul] at hpow htot
      rw [hpow]
      constructor
      · intro hE0; constructor <;> omega
      · rintro ⟨h3, h4⟩; omega
    · have hq2' : q = 2 := by
        have hv1 : 1 ≤ v - 1 := by
          by_contra hc; have : v - 1 = 0 := by omega
          rw [this, pow_zero] at h; omega
        have : q ∣ 2 := h ▸ dvd_pow_self q (by omega)
        exact (Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_two).1 this
      subst hq2'
      rw [h] at hpow htot
      rw [hpow]
      constructor
      · intro hE0; omega
      · rintro ⟨-, h4⟩; exact absurd rfl h4
  · rw [if_neg hd2, sub_zero] at hdiff
    have hEO : E = O := by exact_mod_cast (sub_eq_zero.1 hdiff)
    have hD0 : 0 < (q ^ (v - 1)).totient := Nat.totient_pos.2 (pow_pos hq.out.pos _)
    have hlt := Erdos634.LemmaSGpp.totient_lt (q := q) hv h2
    have hpos : 0 < E := by omega
    refine ⟨⟨fun _ => ⟨?_, ?_⟩, fun _ => hE.1 hpos⟩, hO.1 (by omega)⟩
    · intro h3
      have hq3 : q = 3 := (Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_three).1
        (h3 ▸ dvd_pow_self q (by omega))
      subst hq3
      have hv1 : v = 1 := Nat.pow_right_injective (by norm_num : 2 ≤ 3)
        (show 3 ^ v = 3 ^ 1 by rw [h3])
      subst hv1; exact hd2 (by simp)
    · intro h4
      have hq2' : q = 2 := by
        have : q ∣ 2 ^ 2 := by
          rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← h4]; exact dvd_pow_self q (by omega)
        exact (Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_two).1 (hq.out.dvd_of_dvd_pow this)
      subst hq2'
      have hv2 : v = 2 := Nat.pow_right_injective (le_refl 2)
        (show 2 ^ v = 2 ^ 2 by rw [h4])
      subst hv2; exact hd2 (by norm_num)

end PP

/-! ### Products -/

theorem prod_neg_one {m₁ m₂ : ℕ} [NeZero m₁] [NeZero m₂] (ψ : DirichletCharacter ℂ m₁)
    (η : DirichletCharacter ℂ m₂) :
    (changeLevel (Nat.dvd_mul_right m₁ m₂) ψ * changeLevel (Nat.dvd_mul_left m₂ m₁) η) (-1) =
      ψ (-1) * η (-1) := by
  haveI : NeZero (m₁ * m₂) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  rw [MulChar.coeToFun_mul, Pi.mul_apply, Erdos634.LemmaSG2.changeLevel_neg_one,
    Erdos634.LemmaSG2.changeLevel_neg_one]

theorem EP_mul {a b : ℕ} [NeZero a] [NeZero b] (h : a.Coprime b) :
    EP (a * b) ↔ (EP a ∧ EP b) ∨ (OP a ∧ OP b) := by
  haveI : NeZero (a * b) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  constructor
  · rintro ⟨χ, hp, he⟩
    have e := decomp h χ
    obtain ⟨p1, p2⟩ := (isPrimitive_iff h e).1 hp
    rw [e, prod_neg_one] at he
    rcases Erdos634.LemmaSG.val_neg_one (Erdos634.DirichletCRT.comp₁ h χ) with h1 | h1 <;>
      rcases Erdos634.LemmaSG.val_neg_one (Erdos634.DirichletCRT.comp₂ h χ) with h2 | h2 <;>
      rw [h1, h2] at he <;> norm_num at he
    · exact Or.inl ⟨⟨_, p1, h1⟩, ⟨_, p2, h2⟩⟩
    · exact Or.inr ⟨⟨_, p1, h1⟩, ⟨_, p2, h2⟩⟩
  · rintro (⟨⟨ψ, hψ, h1⟩, ⟨η, hη, h2⟩⟩ | ⟨⟨ψ, hψ, h1⟩, ⟨η, hη, h2⟩⟩)
    · exact ⟨_, (isPrimitive_iff h rfl).2 ⟨hψ, hη⟩, by rw [prod_neg_one, h1, h2, one_mul]⟩
    · exact ⟨_, (isPrimitive_iff h rfl).2 ⟨hψ, hη⟩, by rw [prod_neg_one, h1, h2]; norm_num⟩

theorem OP_mul {a b : ℕ} [NeZero a] [NeZero b] (h : a.Coprime b) :
    OP (a * b) ↔ (EP a ∧ OP b) ∨ (OP a ∧ EP b) := by
  haveI : NeZero (a * b) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  constructor
  · rintro ⟨χ, hp, ho⟩
    have e := decomp h χ
    obtain ⟨p1, p2⟩ := (isPrimitive_iff h e).1 hp
    rw [e, prod_neg_one] at ho
    rcases Erdos634.LemmaSG.val_neg_one (Erdos634.DirichletCRT.comp₁ h χ) with h1 | h1 <;>
      rcases Erdos634.LemmaSG.val_neg_one (Erdos634.DirichletCRT.comp₂ h χ) with h2 | h2 <;>
      rw [h1, h2] at ho <;> norm_num at ho
    · exact Or.inl ⟨⟨_, p1, h1⟩, ⟨_, p2, h2⟩⟩
    · exact Or.inr ⟨⟨_, p1, h1⟩, ⟨_, p2, h2⟩⟩
  · rintro (⟨⟨ψ, hψ, h1⟩, ⟨η, hη, h2⟩⟩ | ⟨⟨ψ, hψ, h1⟩, ⟨η, hη, h2⟩⟩)
    · exact ⟨_, (isPrimitive_iff h rfl).2 ⟨hψ, hη⟩, by rw [prod_neg_one, h1, h2, one_mul]⟩
    · exact ⟨_, (isPrimitive_iff h rfl).2 ⟨hψ, hη⟩, by rw [prod_neg_one, h1, h2, mul_one]⟩

theorem ne_twelve_of_pp {p n : ℕ} (hp : p.Prime) : p ^ n ≠ 12 := by
  intro h
  have h3 : 3 ∣ p := Nat.prime_three.dvd_of_dvd_pow (show 3 ∣ p ^ n by rw [h]; norm_num)
  have hp3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h3
  subst hp3
  have : 2 ∣ 3 := Nat.prime_two.dvd_of_dvd_pow (show 2 ∣ 3 ^ n by rw [h]; norm_num)
  norm_num at this

/-- The induction statement. -/
def Stmt (d : ℕ) : Prop :=
  d ≠ 0 → d % 4 ≠ 2 → (EP d ↔ d ≠ 3 ∧ d ≠ 4) ∧ (OP d ↔ d ≠ 1 ∧ d ≠ 12)

theorem mod4_left {a b : ℕ} (h : a.Coprime b) (hab : (a * b) % 4 ≠ 2) : a % 4 ≠ 2 :=
  Erdos634.LemmaSGprime.mod4_left h hab

theorem stmt_all (d : ℕ) : Stmt d := by
  induction d using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; exact absurd rfl h
  | one =>
    intro _ _
    have h1 : ∀ χ : DirichletCharacter ℂ 1, χ (-1) = 1 := by
      intro χ; rw [show (-1 : ZMod 1) = 1 from Subsingleton.elim _ _, map_one]
    refine ⟨⟨fun _ => by norm_num, fun _ => ⟨1, isPrimitive_one_level_one, h1 1⟩⟩, ?_⟩
    constructor
    · rintro ⟨χ, -, h⟩; rw [h1 χ] at h; norm_num at h
    · rintro ⟨h, -⟩; exact absurd rfl h
  | prime_pow p n hp hn =>
    intro _ h4
    haveI : Fact p.Prime := ⟨hp⟩
    have h2 : p ^ n ≠ 2 := fun e => h4 (by rw [e])
    obtain ⟨hE, hO⟩ := pp_parity (q := p) (v := n) hn h2
    refine ⟨hE, ⟨fun _ => ⟨?_, ne_twelve_of_pp hp⟩, fun _ => hO⟩⟩
    exact (Nat.one_lt_pow hn.ne' hp.one_lt).ne'
  | coprime a b ha hb h IHa IHb =>
    intro _ h4
    haveI : NeZero a := ⟨by omega⟩
    haveI : NeZero b := ⟨by omega⟩
    obtain ⟨Ea, Oa⟩ := IHa (by omega) (mod4_left h h4)
    obtain ⟨Eb, Ob⟩ := IHb (by omega) (mod4_left h.symm (by rwa [mul_comm]))
    rw [EP_mul h, OP_mul h, Ea, Oa, Eb, Ob]
    have hcop : Nat.gcd a b = 1 := h
    have h6 : 6 ≤ a * b := by
      rcases Nat.lt_or_ge a 3 with h' | h'
      · obtain rfl : a = 2 := by omega
        rcases Nat.lt_or_ge b 3 with h'' | h''
        · obtain rfl : b = 2 := by omega
          norm_num at hcop
        · omega
      · nlinarith
    have k12 : a * b = 12 → (a = 3 ∧ b = 4) ∨ (a = 4 ∧ b = 3) := by
      intro h12
      have ha12 : a ≤ 12 := Nat.le_of_dvd (by norm_num) ⟨b, h12.symm⟩
      have hb12 : b ≤ 12 := Nat.le_of_dvd (by norm_num) ⟨a, by rw [mul_comm]; exact h12.symm⟩
      interval_cases a <;> interval_cases b <;> first | omega | (norm_num at hcop)
    constructor
    · have hne : a * b ≠ 3 ∧ a * b ≠ 4 := by omega
      refine ⟨fun _ => hne, fun _ => ?_⟩
      by_cases ha : a = 3 ∨ a = 4
      · right; refine ⟨⟨by omega, by omega⟩, ⟨by omega, ?_⟩⟩
        rintro rfl; rcases ha with rfl | rfl <;> norm_num at hcop
      · by_cases hb' : b = 3 ∨ b = 4
        · right; refine ⟨⟨by omega, ?_⟩, ⟨by omega, by omega⟩⟩
          rintro rfl; rcases hb' with rfl | rfl <;> norm_num at hcop
        · left; omega
    · by_cases h12 : a * b = 12
      · rcases k12 h12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
      · refine ⟨fun _ => ⟨by omega, h12⟩, fun _ => ?_⟩
        by_cases ha : a = 3 ∨ a = 4
        · right; refine ⟨⟨by omega, by omega⟩, ?_⟩
          by_contra hb'
          have hb34 : b = 3 ∨ b = 4 := by omega
          apply h12
          rcases ha with rfl | rfl <;> rcases hb34 with rfl | rfl <;>
            first | (exfalso; norm_num at hcop; done) | norm_num
        · by_cases hb12 : b = 12
          · right; subst hb12; refine ⟨⟨by omega, ?_⟩, by omega⟩
            rintro rfl; norm_num at hcop
          · left; omega

/-- **Even primitive characters exist mod d (d ≢ 2 mod 4) iff d ∉ {3, 4}.** -/
theorem exists_even_primitive_iff {d : ℕ} (hd0 : d ≠ 0) (hd : d % 4 ≠ 2) :
    (∃ χ : DirichletCharacter ℂ d, χ.IsPrimitive ∧ χ.Even) ↔ d ≠ 3 ∧ d ≠ 4 :=
  (stmt_all d hd0 hd).1

/-- **Odd primitive characters exist mod d (d ≢ 2 mod 4) iff d ∉ {1, 12}.** -/
theorem exists_odd_primitive_iff {d : ℕ} (hd0 : d ≠ 0) (hd : d % 4 ≠ 2) :
    (∃ χ : DirichletCharacter ℂ d, χ.IsPrimitive ∧ χ.Odd) ↔ d ≠ 1 ∧ d ≠ 12 :=
  (stmt_all d hd0 hd).2

/-! ## Witnesses / controls: mod 5 an even primitive character exists; mod 3 and mod 4 none
(the §4 exceptions); mod 12 no odd primitive one. -/
theorem witness_even5 : ∃ χ : DirichletCharacter ℂ 5, χ.IsPrimitive ∧ χ.Even :=
  (exists_even_primitive_iff (by norm_num) (by norm_num)).2 (by norm_num)
theorem control_even3 : ¬ ∃ χ : DirichletCharacter ℂ 3, χ.IsPrimitive ∧ χ.Even := by
  rw [exists_even_primitive_iff (by norm_num) (by norm_num)]; norm_num
theorem control_even4 : ¬ ∃ χ : DirichletCharacter ℂ 4, χ.IsPrimitive ∧ χ.Even := by
  rw [exists_even_primitive_iff (by norm_num) (by norm_num)]; norm_num
theorem control_odd12 : ¬ ∃ χ : DirichletCharacter ℂ 12, χ.IsPrimitive ∧ χ.Odd := by
  rw [exists_odd_primitive_iff (by norm_num) (by norm_num)]; norm_num

#print axioms Erdos634.LemmaSParity.exists_even_primitive_iff
#print axioms Erdos634.LemmaSParity.exists_odd_primitive_iff
#print axioms Erdos634.LemmaSParity.control_even3

end Erdos634.LemmaSParity
