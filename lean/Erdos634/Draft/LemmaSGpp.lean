/-
Lemma S, node A5: Lemma G′ at a single prime power, and existence of primitive characters.

Source: (private working notes, not included) §3.2 (G′, "Per prime power") and P2.

* `sum_prim` : Σ_{χ primitive mod q^v} χ(g) = φ(q^v)[g = 1] − φ(q^{v−1})[g ≡ 1 mod q^{v−1}].
* `card_prim` : #primitive characters mod q^v = φ(q^v) − φ(q^{v−1}).
* `exists_primitive_pp` : for q prime, v ≥ 1, q^v ≠ 2, a primitive character mod q^v exists.
* `lemmaGpp` : g unit mod q^v, z ∈ ℤ representing g. The value χ(g) is constant over primitive χ
  iff `SpPP q v z` (g ≡ 1, or q^v = 3 and g ≡ −1, or q = 2, v ≥ 2 and g ≡ 1 + 2^{v−1}); and then
  the value is 1 if g ≡ 1 and −1 otherwise.

The proof is uniform (one character sum), covering the paper's three sub-cases q^v ∈ {3,4},
q ≥ 5 with v = 1, and v ≥ 2 (incl. the 2-adic exception) at once.
Formalization debt, not /goal progress.
-/
import Mathlib
import Erdos634.Draft.LemmaSN

open scoped BigOperators
open Finset
open scoped Classical

namespace Erdos634.LemmaSGpp

open Erdos634.LemmaSN (pred_dvd isPrimitive_iff_not_factorsThrough)

/-- The paper's per-prime-power special set, on an integer representative z of g_q. -/
def SpPP (q k : ℕ) (z : ℤ) : Prop :=
  z ≡ 1 [ZMOD (q : ℤ) ^ k] ∨ (q = 3 ∧ k = 1 ∧ z ≡ -1 [ZMOD 3]) ∨
    (q = 2 ∧ 2 ≤ k ∧ z ≡ 1 + 2 ^ (k - 1) [ZMOD 2 ^ k])

section PP
variable {q v : ℕ} [hq : Fact q.Prime]

/-- The primitive/non-primitive split of the full character sum at a unit. -/
theorem sum_prim (hv : 1 ≤ v) (g : (ZMod (q ^ v))ˣ) :
    ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ (q ^ v) => χ.IsPrimitive), χ (g : ZMod (q ^ v))
      = (if (g : ZMod (q ^ v)) = 1 then (((q ^ v).totient : ℕ) : ℂ) else 0) -
        (if ((g : ZMod (q ^ v)).cast : ZMod (q ^ (v - 1))) = 1
          then (((q ^ (v - 1)).totient : ℕ) : ℂ) else 0) := by
  classical
  haveI : NeZero (q ^ v) := ⟨pow_ne_zero _ hq.out.ne_zero⟩
  haveI : NeZero (q ^ (v - 1)) := ⟨pow_ne_zero _ hq.out.ne_zero⟩
  have hd := pred_dvd q v
  have hall := DirichletCharacter.sum_characters_eq ℂ (g : ZMod (q ^ v))
  have hall' := DirichletCharacter.sum_characters_eq ℂ
    (((g : ZMod (q ^ v)).cast : ZMod (q ^ (v - 1))))
  rw [← sum_filter_add_sum_filter_not univ (fun χ : DirichletCharacter ℂ (q ^ v) => χ.IsPrimitive)]
    at hall
  have hY : univ.filter (fun χ : DirichletCharacter ℂ (q ^ v) => ¬ χ.IsPrimitive)
      = univ.map ⟨DirichletCharacter.changeLevel hd, DirichletCharacter.changeLevel_injective hd⟩ := by
    ext ψ
    simp only [mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
    constructor
    · intro hnp
      have hf : ψ.FactorsThrough (q ^ (v - 1)) :=
        not_not.1 (fun h' => hnp ((isPrimitive_iff_not_factorsThrough hv ψ).2 h'))
      exact ⟨hf.χ₀, hf.eq_changeLevel.symm⟩
    · rintro ⟨ψ', rfl⟩ hprim
      exact (isPrimitive_iff_not_factorsThrough hv _).1 hprim ⟨hd, ψ', rfl⟩
  rw [hY, sum_map] at hall
  simp only [Function.Embedding.coeFn_mk, DirichletCharacter.changeLevel_eq_cast_of_dvd] at hall
  rw [hall'] at hall
  linear_combination hall

theorem totient_lt (hv : 1 ≤ v) (h2 : q ^ v ≠ 2) : (q ^ (v - 1)).totient < (q ^ v).totient := by
  have hq2 := hq.out.two_le
  rcases Nat.lt_or_ge v 2 with h | h
  · obtain rfl : v = 1 := by omega
    simp only [pow_one, Nat.sub_self, pow_zero, Nat.totient_one] at h2 ⊢
    rw [Nat.totient_prime hq.out]; omega
  · have htot : (q ^ v).totient = q * (q ^ (v - 1)).totient := by
      rw [show q ^ v = q * q ^ (v - 1) by rw [← pow_succ']; congr 1; omega]
      exact Nat.totient_mul_of_prime_of_dvd hq.out (dvd_pow_self q (by omega))
    have : 0 < (q ^ (v - 1)).totient := Nat.totient_pos.2 (by positivity)
    rw [htot]; nlinarith

/-- Number of primitive characters mod q^v. -/
theorem card_prim (hv : 1 ≤ v) :
    (univ.filter (fun χ : DirichletCharacter ℂ (q ^ v) => χ.IsPrimitive)).card +
      (q ^ (v - 1)).totient = (q ^ v).totient := by
  classical
  have h := sum_prim hv (1 : (ZMod (q ^ v))ˣ)
  haveI : NeZero (q ^ v) := ⟨pow_ne_zero _ hq.out.ne_zero⟩
  rw [if_pos Units.val_one, if_pos (by rw [Units.val_one]; exact ZMod.cast_one (pred_dvd q v))] at h
  simp only [Units.val_one, MulChar.map_one, sum_const, nsmul_eq_mul, mul_one] at h
  exact_mod_cast (show (((univ.filter (fun χ : DirichletCharacter ℂ (q ^ v) => χ.IsPrimitive)).card
    + (q ^ (v - 1)).totient : ℕ) : ℂ) = (q ^ v).totient by push_cast; rw [h]; ring)

/-- **Existence of primitive characters mod q^v, q^v ≠ 2** (task (1), prime-power case). -/
theorem exists_primitive_pp (hv : 1 ≤ v) (h2 : q ^ v ≠ 2) :
    ∃ χ : DirichletCharacter ℂ (q ^ v), χ.IsPrimitive := by
  classical
  have hc := card_prim (q := q) hv
  have hl := totient_lt (q := q) hv h2
  obtain ⟨χ, hχ⟩ := card_pos.1 (show 0 < (univ.filter
    (fun χ : DirichletCharacter ℂ (q ^ v) => χ.IsPrimitive)).card by omega)
  exact ⟨χ, (mem_filter.1 hχ).2⟩

/-- Unit complex numbers summing to −(count) are all −1. -/
theorem all_neg_one {ι : Type*} (s : Finset ι) (w : ι → ℂ) (hn : ∀ i ∈ s, ‖w i‖ = 1)
    (hs : ∑ i ∈ s, w i = -(s.card : ℂ)) : ∀ i ∈ s, w i = -1 := by
  have hre : ∑ i ∈ s, (1 + (w i).re) = 0 := by
    have := congrArg Complex.re hs
    rw [Complex.re_sum] at this
    simp only [Complex.neg_re, Complex.natCast_re] at this
    rw [sum_add_distrib, this]; simp
  have hnn : ∀ i ∈ s, 0 ≤ 1 + (w i).re := by
    intro i hi
    have := Complex.abs_re_le_norm (w i)
    rw [hn i hi] at this
    linarith [neg_abs_le (w i).re]
  intro i hi
  have h1 := (sum_eq_zero_iff_of_nonneg hnn).1 hre i hi
  have hsq := Complex.sq_norm (w i)
  rw [hn i hi, Complex.normSq_apply] at hsq
  have hr : (w i).re = -1 := by linarith
  have him : (w i).im = 0 := by nlinarith
  exact Complex.ext (by simp [hr]) (by simp [him])

/-- **Lemma G′ at a prime power** (paper §3.2, all three sub-cases at once). -/
theorem lemmaGpp (hv : 1 ≤ v) (h2 : q ^ v ≠ 2) (g : (ZMod (q ^ v))ˣ) (z : ℤ)
    (hz : ((z : ℤ) : ZMod (q ^ v)) = g) :
    ((∃ c : ℂ, ∀ χ : DirichletCharacter ℂ (q ^ v), χ.IsPrimitive → χ (g : ZMod (q ^ v)) = c) ↔
      SpPP q v z) ∧
    (SpPP q v z → ∀ χ : DirichletCharacter ℂ (q ^ v), χ.IsPrimitive →
      χ (g : ZMod (q ^ v)) = if z ≡ 1 [ZMOD (q : ℤ) ^ v] then 1 else -1) := by
  classical
  haveI : NeZero (q ^ v) := ⟨pow_ne_zero _ hq.out.ne_zero⟩
  have hq2 := hq.out.two_le
  have hS := sum_prim hv g
  have hcard := card_prim (q := q) hv
  have hlt := totient_lt (q := q) hv h2
  set Pr := univ.filter (fun χ : DirichletCharacter ℂ (q ^ v) => χ.IsPrimitive) with hPr
  set T := (q ^ v).totient
  set D := (q ^ (v - 1)).totient
  -- translating the two conditions into congruences on z
  have e1 : (g : ZMod (q ^ v)) = 1 ↔ z ≡ 1 [ZMOD (q : ℤ) ^ v] := by
    rw [← hz, ← Int.cast_one, ZMod.intCast_eq_intCast_iff]; push_cast; rfl
  have e0 : ((g : ZMod (q ^ v)).cast : ZMod (q ^ (v - 1))) = 1 ↔
      z ≡ 1 [ZMOD (q : ℤ) ^ (v - 1)] := by
    rw [← hz, ZMod.cast_intCast (pred_dvd q v), ← Int.cast_one, ZMod.intCast_eq_intCast_iff]
    push_cast; rfl
  -- T = 2D exactly in the exceptional cases
  have hT2 : T = 2 * D ↔ (q = 2 ∧ 2 ≤ v) ∨ (q = 3 ∧ v = 1) := by
    rcases Nat.lt_or_ge v 2 with h | h
    · obtain rfl : v = 1 := by omega
      show (q ^ 1).totient = 2 * (q ^ 0).totient ↔ _
      rw [pow_zero, pow_one, Nat.totient_one, Nat.totient_prime hq.out]
      omega
    · have htot : T = q * D := by
        simp only [T, D]
        rw [show q ^ v = q * q ^ (v - 1) by rw [← pow_succ']; congr 1; omega]
        exact Nat.totient_mul_of_prime_of_dvd hq.out (dvd_pow_self q (by omega))
      have : 0 < D := Nat.totient_pos.2 (by positivity)
      rw [htot]
      constructor
      · intro e; left; exact ⟨Nat.eq_of_mul_eq_mul_right this (by linarith), h⟩
      · rintro (⟨rfl, -⟩ | ⟨-, h'⟩)
        · rfl
        · omega
  have hnorm : ∀ χ ∈ Pr, ‖χ (g : ZMod (q ^ v))‖ = 1 := fun χ _ => χ.unit_norm_eq_one g
  -- the exceptional direction, shared by (→) and (←)
  have hexc : SpPP q v z → ¬ z ≡ 1 [ZMOD (q : ℤ) ^ v] →
      z ≡ 1 [ZMOD (q : ℤ) ^ (v - 1)] ∧ T = 2 * D := by
    rintro (h | ⟨rfl, rfl, h⟩ | ⟨rfl, hk, h⟩) hn
    · exact absurd h hn
    · exact ⟨by simp [Int.modEq_one], hT2.2 (Or.inr ⟨rfl, rfl⟩)⟩
    · refine ⟨?_, hT2.2 (Or.inl ⟨rfl, hk⟩)⟩
      have hp : (2 : ℤ) ^ v = 2 ^ (v - 1) * 2 := by rw [← pow_succ]; congr 1; omega
      have hdv : (2 : ℤ) ^ (v - 1) ∣ 2 ^ v := ⟨2, hp⟩
      have h' := h.of_dvd hdv
      show z ≡ 1 [ZMOD ((2 : ℕ) : ℤ) ^ (v - 1)]
      push_cast
      refine h'.trans ?_
      rw [Int.modEq_iff_dvd]; exact ⟨-1, by ring⟩
  have hval : SpPP q v z → ∀ χ : DirichletCharacter ℂ (q ^ v), χ.IsPrimitive →
      χ (g : ZMod (q ^ v)) = if z ≡ 1 [ZMOD (q : ℤ) ^ v] then 1 else -1 := by
    intro hsp χ hχ
    by_cases h1 : z ≡ 1 [ZMOD (q : ℤ) ^ v]
    · rw [if_pos h1, e1.2 h1, map_one]
    · rw [if_neg h1]
      obtain ⟨h0, hT⟩ := hexc hsp h1
      rw [if_neg (fun h => h1 (e1.1 h)), if_pos (e0.2 h0), zero_sub] at hS
      refine all_neg_one Pr _ hnorm ?_ χ (mem_filter.2 ⟨mem_univ _, hχ⟩)
      rw [hS]; congr 1; exact_mod_cast (show D = Pr.card by omega)
  refine ⟨⟨?_, ?_⟩, hval⟩
  · rintro ⟨c, hc⟩
    by_cases h1 : z ≡ 1 [ZMOD (q : ℤ) ^ v]
    · exact Or.inl h1
    obtain ⟨χ0, hχ0⟩ := card_pos.1 (show 0 < Pr.card by omega)
    have hcn : ‖c‖ = 1 := by rw [← hc χ0 (mem_filter.1 hχ0).2]; exact hnorm χ0 hχ0
    rw [sum_congr rfl (fun χ hχ => hc χ (mem_filter.1 hχ).2), sum_const, nsmul_eq_mul,
      if_neg (fun h => h1 (e1.1 h)), zero_sub] at hS
    by_cases h0 : z ≡ 1 [ZMOD (q : ℤ) ^ (v - 1)]
    · rw [if_pos (e0.2 h0)] at hS
      have hPD : Pr.card = D := by
        have := congrArg norm hS
        rw [norm_mul, hcn, mul_one, norm_neg] at this
        simp only [Complex.norm_natCast] at this
        exact_mod_cast this
      have hT : T = 2 * D := by omega
      rcases hT2.1 hT with ⟨rfl, hk⟩ | ⟨rfl, rfl⟩
      · right; right; refine ⟨rfl, hk, ?_⟩
        have hp : (2 : ℤ) ^ v = 2 ^ (v - 1) * 2 := by rw [← pow_succ]; congr 1; omega
        push_cast at h0 h1
        obtain ⟨k, hk'⟩ := (Int.modEq_iff_dvd.1 h0)
        rcases Int.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
        · exact absurd (Int.modEq_iff_dvd.2 ⟨j, by rw [hp]; linear_combination hk'⟩) h1
        · rw [Int.modEq_iff_dvd]; exact ⟨j + 1, by rw [hp]; linear_combination hk'⟩
      · right; left; refine ⟨rfl, rfl, ?_⟩
        have hu : (z : ZMod 3) ≠ 0 := by
          rw [show ((z : ℤ) : ZMod 3) = (g : ZMod (3 ^ 1)) from hz]; exact g.ne_zero
        rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd] at hu
        simp only [Int.ModEq, pow_one, Nat.cast_ofNat] at h1 ⊢
        push_cast at hu
        omega
    · rw [if_neg (fun h => h0 (e0.1 h)), neg_zero] at hS
      have : (Pr.card : ℂ) ≠ 0 := by exact_mod_cast (show Pr.card ≠ 0 by omega)
      rcases mul_eq_zero.1 hS with h | h
      · exact absurd h this
      · rw [h, norm_zero] at hcn; exact absurd hcn zero_ne_one
  · intro hsp; exact ⟨_, hval hsp⟩

end PP

end Erdos634.LemmaSGpp

#print axioms Erdos634.LemmaSGpp.lemmaGpp
#print axioms Erdos634.LemmaSGpp.exists_primitive_pp
