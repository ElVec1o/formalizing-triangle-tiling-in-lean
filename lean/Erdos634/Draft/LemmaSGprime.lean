/-
Lemma S, node A5: **Lemma G′** as written (PROOF_lemmaS.md §3.2 and P2).

  Lemma G′ (d ≥ 1 with d ≢ 2 (mod 4); g ∈ (ℤ/d)^×). η(g) takes one value over all primitive η mod d
  iff g ∈ Sp(d), and the value is then (−1)^{τ(g)}.

Sp(d) = {g : g_q = 1 for every q^v ∥ d, except possibly g₃ = −1 (when 3 ∥ d) and
g₂ = 1 + 2^{v−1} (when 2^v ∥ d, v ≥ 2)}; τ(g) = number of exceptional components. Here g_q is g
mod q^v, read off an integer representative z of g (`Sp d z`, `tau d z`).

Also: existence of a primitive character mod every d ≢ 2 (mod 4) (`exists_primitive`).
Proof: induction over the coprime factorisation (Nat.recOnPosPrimePosCoprime), prime powers from
LemmaSGpp, product step DirichletCRT.const_iff.
Formalization debt, not /goal progress.
-/
import Mathlib
import Erdos634.Draft.LemmaSGpp
import Erdos634.Draft.DirichletCRT

open scoped BigOperators
open Finset

namespace Erdos634.LemmaSGprime

open Erdos634.LemmaSGpp (SpPP lemmaGpp exists_primitive_pp)
open Erdos634.DirichletCRT (unitsCRT unitsCRT_fst unitsCRT_snd const_iff decomp prod_unit
  isPrimitive_iff)

/-- Sp(d), on an integer representative z of g. -/
def Sp (d : ℕ) (z : ℤ) : Prop := ∀ q ∈ d.primeFactors, SpPP q (d.factorization q) z

/-- τ(g): the number of prime powers q^v ∥ d at which g_q ≠ 1. -/
noncomputable def tau (d : ℕ) (z : ℤ) : ℕ := by
  classical
  exact (d.primeFactors.filter (fun q : ℕ => ¬ z ≡ 1 [ZMOD (q : ℤ) ^ d.factorization q])).card

theorem Sp_pp {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (z : ℤ) : Sp (p ^ n) z ↔ SpPP p n z := by
  simp [Sp, Nat.primeFactors_prime_pow hn hp, hp.factorization_self]

theorem tau_pp {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (z : ℤ) :
    tau (p ^ n) z = if z ≡ 1 [ZMOD (p : ℤ) ^ n] then 0 else 1 := by
  classical
  unfold tau
  rw [Nat.primeFactors_prime_pow hn hp, filter_singleton, Nat.factorization_pow_self hp]
  split_ifs <;> simp_all

section Mul
variable {a b : ℕ} (h : a.Coprime b) (ha : a ≠ 0) (hb : b ≠ 0)
include h ha hb

omit ha hb in
theorem fact_left {q : ℕ} (hq : q ∈ a.primeFactors) : (a * b).factorization q = a.factorization q :=
  Nat.factorization_eq_of_coprime_left h (Nat.mem_primeFactors_iff_mem_primeFactorsList.1 hq)

omit ha hb in
theorem fact_right {q : ℕ} (hq : q ∈ b.primeFactors) : (a * b).factorization q = b.factorization q :=
  Nat.factorization_eq_of_coprime_right h (Nat.mem_primeFactors_iff_mem_primeFactorsList.1 hq)

theorem Sp_mul (z : ℤ) : Sp (a * b) z ↔ Sp a z ∧ Sp b z := by
  unfold Sp
  rw [Nat.primeFactors_mul ha hb]
  constructor
  · intro H
    refine ⟨fun q hq => ?_, fun q hq => ?_⟩
    · have := H q (mem_union_left _ hq); rwa [fact_left h hq] at this
    · have := H q (mem_union_right _ hq); rwa [fact_right h hq] at this
  · rintro ⟨Ha, Hb⟩ q hq
    rcases mem_union.1 hq with hq | hq
    · rw [fact_left h hq]; exact Ha q hq
    · rw [fact_right h hq]; exact Hb q hq

theorem tau_mul (z : ℤ) : tau (a * b) z = tau a z + tau b z := by
  classical
  unfold tau
  rw [Nat.primeFactors_mul ha hb, filter_union, card_union_of_disjoint
    (disjoint_filter_filter h.disjoint_primeFactors)]
  congr 1
  · congr 1; apply filter_congr; intro q hq; rw [fact_left h hq]
  · congr 1; apply filter_congr; intro q hq; rw [fact_right h hq]

end Mul

/-- The induction statement. -/
def Stmt (d : ℕ) : Prop :=
  d ≠ 0 → d % 4 ≠ 2 → (∃ χ : DirichletCharacter ℂ d, χ.IsPrimitive) ∧
    ∀ (g : (ZMod d)ˣ) (z : ℤ), ((z : ℤ) : ZMod d) = g →
      ((∃ c : ℂ, ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive → χ (g : ZMod d) = c) ↔ Sp d z) ∧
      (Sp d z → ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive → χ (g : ZMod d) = (-1) ^ tau d z)

theorem mod4_left {a b : ℕ} (h : a.Coprime b) (hab : (a * b) % 4 ≠ 2) : a % 4 ≠ 2 := by
  intro ha
  have h2a : 2 ∣ a := by omega
  have hb : ¬ 2 ∣ b := fun h2b => by
    have := Nat.dvd_gcd h2a h2b; rw [h.gcd_eq_one] at this; omega
  apply hab
  rw [Nat.mul_mod, ha]
  have : b % 4 = 1 ∨ b % 4 = 3 := by omega
  rcases this with e | e <;> rw [e]

theorem stmt_all (d : ℕ) : Stmt d := by
  induction d using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; exact absurd rfl h
  | one =>
    intro _ _
    refine ⟨⟨1, DirichletCharacter.isPrimitive_one_level_one⟩, fun g z _ => ?_⟩
    have hg : (g : ZMod 1) = 1 := Subsingleton.elim _ _
    have hS : Sp 1 z := by simp [Sp]
    have ht : tau 1 z = 0 := by simp [tau]
    refine ⟨⟨fun _ => hS, fun _ => ⟨1, fun χ _ => by rw [hg, map_one]⟩⟩, fun _ χ _ => ?_⟩
    rw [hg, map_one, ht, pow_zero]
  | prime_pow p n hp hn =>
    intro _ h4
    haveI : Fact p.Prime := ⟨hp⟩
    have h2 : p ^ n ≠ 2 := fun e => h4 (by rw [e])
    refine ⟨exists_primitive_pp hn h2, fun g z hz => ?_⟩
    obtain ⟨H1, H2⟩ := lemmaGpp hn h2 g z hz
    rw [Sp_pp hp hn.ne' z, tau_pp hp hn.ne' z]
    refine ⟨H1, fun hs χ hχ => ?_⟩
    rw [H2 hs χ hχ]
    split_ifs <;> simp
  | coprime a b ha hb h IHa IHb =>
    intro _ h4
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    haveI : NeZero a := ⟨ha0⟩
    haveI : NeZero b := ⟨hb0⟩
    have h4a := mod4_left h h4
    have h4b : b % 4 ≠ 2 := mod4_left h.symm (by rwa [mul_comm])
    obtain ⟨⟨ψ, hψ⟩, Ga⟩ := IHa ha0 h4a
    obtain ⟨⟨η, hη⟩, Gb⟩ := IHb hb0 h4b
    refine ⟨⟨_, (isPrimitive_iff h rfl).2 ⟨hψ, hη⟩⟩, fun g z hz => ?_⟩
    have hz₁ : ((z : ℤ) : ZMod a) = ((unitsCRT h g).1 : ZMod a) := by
      rw [unitsCRT_fst, ZMod.unitsMap_val, ← hz, ZMod.cast_intCast (Nat.dvd_mul_right a b)]
    have hz₂ : ((z : ℤ) : ZMod b) = ((unitsCRT h g).2 : ZMod b) := by
      rw [unitsCRT_snd, ZMod.unitsMap_val, ← hz, ZMod.cast_intCast (Nat.dvd_mul_left b a)]
    obtain ⟨A1, A2⟩ := Ga _ z hz₁
    obtain ⟨B1, B2⟩ := Gb _ z hz₂
    refine ⟨?_, fun hs χ hχ => ?_⟩
    · rw [const_iff h g ⟨ψ, hψ⟩ ⟨η, hη⟩, A1, B1, Sp_mul h ha0 hb0]
    · obtain ⟨sa, sb⟩ := (Sp_mul h ha0 hb0 z).1 hs
      have e := decomp h χ
      obtain ⟨p1, p2⟩ := (isPrimitive_iff h e).1 hχ
      rw [e, prod_unit h, A2 sa _ p1, B2 sb _ p2, ← pow_add, tau_mul h ha0 hb0]

/-- **Existence of primitive characters** mod every d ≢ 2 (mod 4), d ≠ 0. -/
theorem exists_primitive {d : ℕ} (hd0 : d ≠ 0) (hd : d % 4 ≠ 2) :
    ∃ χ : DirichletCharacter ℂ d, χ.IsPrimitive := (stmt_all d hd0 hd).1

/-- **Lemma G′**, as written: for d ≢ 2 (mod 4) and g ∈ (ℤ/d)^× (z any integer representative),
χ(g) takes one value over all primitive χ mod d iff g ∈ Sp(d), and the value is then (−1)^{τ(g)}. -/
theorem lemmaG' {d : ℕ} (hd0 : d ≠ 0) (hd : d % 4 ≠ 2) (g : (ZMod d)ˣ) (z : ℤ)
    (hz : ((z : ℤ) : ZMod d) = g) :
    ((∃ c : ℂ, ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive → χ (g : ZMod d) = c) ↔ Sp d z) ∧
    (Sp d z → ∀ χ : DirichletCharacter ℂ d, χ.IsPrimitive → χ (g : ZMod d) = (-1) ^ tau d z) :=
  (stmt_all d hd0 hd).2 g z hz

/-! ## Witnesses and controls -/

/-- Witness (2-adic exception, d = 8): g = 5 = 1 + 2² lies in Sp(8), so every primitive χ mod 8
has χ(5) = −1; and primitive characters mod 8 exist, so this is not vacuous. -/
theorem witness_mod8 : (∃ χ : DirichletCharacter ℂ (2 ^ 3), χ.IsPrimitive) ∧
    ∀ χ : DirichletCharacter ℂ (2 ^ 3), χ.IsPrimitive → χ 5 = -1 := by
  refine ⟨exists_primitive (by norm_num) (by norm_num), fun χ hχ => ?_⟩
  have hu : IsUnit (5 : ZMod (2 ^ 3)) := by decide
  have hS : Sp (2 ^ 3) 5 := (Sp_pp Nat.prime_two (by norm_num) 5).2
    (Or.inr (Or.inr ⟨rfl, by norm_num, by decide⟩))
  have := (lemmaG' (by norm_num) (by norm_num) hu.unit 5 (by simp)).2 hS χ hχ
  rw [IsUnit.unit_spec] at this
  rw [this, tau_pp Nat.prime_two (by norm_num), if_neg (by decide)]; norm_num

/-- Negative control (d = 8): g = 3 is not in Sp(8), so χ(3) is NOT constant over primitive χ. -/
theorem control_mod8 : ¬ ∃ c : ℂ, ∀ χ : DirichletCharacter ℂ (2 ^ 3), χ.IsPrimitive → χ 3 = c := by
  have hu : IsUnit (3 : ZMod (2 ^ 3)) := by decide
  have := (lemmaG' (by norm_num) (by norm_num) hu.unit 3 (by simp)).1
  rw [IsUnit.unit_spec] at this
  rw [this, Sp_pp Nat.prime_two (by norm_num)]
  rintro (h | ⟨h, -⟩ | ⟨-, -, h⟩)
  · exact absurd h (by decide)
  · exact absurd h (by norm_num)
  · exact absurd h (by decide)

/-- Witness (composite, d = 12 = 3 · 4): g = 11 has g₃ = −1 and g₂ = 3 = 1 + 2¹, so g ∈ Sp(12)
with τ = 2, and every primitive χ mod 12 has χ(11) = +1. -/
theorem witness_mod12 : (∃ χ : DirichletCharacter ℂ (3 ^ 1 * 2 ^ 2), χ.IsPrimitive) ∧
    ∀ χ : DirichletCharacter ℂ (3 ^ 1 * 2 ^ 2), χ.IsPrimitive → χ 11 = 1 := by
  have hc : (3 ^ 1).Coprime (2 ^ 2) := by decide
  refine ⟨exists_primitive (by norm_num) (by norm_num), fun χ hχ => ?_⟩
  have hu : IsUnit (11 : ZMod (3 ^ 1 * 2 ^ 2)) := by decide
  have hS : Sp (3 ^ 1 * 2 ^ 2) 11 := (Sp_mul hc (by norm_num) (by norm_num) 11).2
    ⟨(Sp_pp Nat.prime_three one_ne_zero 11).2 (Or.inr (Or.inl ⟨rfl, rfl, by decide⟩)),
     (Sp_pp Nat.prime_two (by norm_num) 11).2 (Or.inr (Or.inr ⟨rfl, le_rfl, by decide⟩))⟩
  have := (lemmaG' (by norm_num) (by norm_num) hu.unit 11 (by simp)).2 hS χ hχ
  rw [IsUnit.unit_spec] at this
  rw [this, tau_mul hc (by norm_num) (by norm_num), tau_pp Nat.prime_three one_ne_zero,
    tau_pp Nat.prime_two (by norm_num), if_neg (by decide), if_neg (by decide)]; norm_num

end Erdos634.LemmaSGprime

#print axioms Erdos634.LemmaSGprime.lemmaG'
#print axioms Erdos634.LemmaSGprime.exists_primitive
#print axioms Erdos634.LemmaSGprime.witness_mod8
#print axioms Erdos634.LemmaSGprime.control_mod8
#print axioms Erdos634.LemmaSGprime.witness_mod12
