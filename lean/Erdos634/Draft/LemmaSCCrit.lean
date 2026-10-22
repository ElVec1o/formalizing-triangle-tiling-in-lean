/-
# Lemma S, Lemma C's Consequence (T1): the odd-character criterion for R(a)

Source: (private working notes, not included) P2, Lemma C, "Consequence (T1)":

  e ∈ R(a) ⟺ Σ_j e_j [x_j]_χ = 0 for every odd χ mod n,
  where [x]_χ is the right side of Lemma C without the factor B_{1,χ̄*}.

This is the step that turns a relation in R(a) into character-sum vanishing; it combines
`LemmaSC.lemmaC` (the character formula), `LemmaSB1H.B1` (B_{1,ω} ≠ 0 for odd primitive ω),
Fourier inversion on (ℤ/n)^× and the oddness of the sawtooth (even χ give nothing).

Formalization debt only (Lemma S is PROVED at paper level); NOT /goal progress.
-/
import Mathlib
import Erdos634.Draft.LemmaSC

open scoped BigOperators
open Finset

namespace Erdos634.LemmaSC

open Erdos634.LemmaS (saw relSpace mem_relSpace)

/-! ## Oddness of the sawtooth -/

theorem saw_neg (t : ℚ) : saw (-t) = -saw t := by
  unfold saw
  by_cases h : Int.fract t = 0
  · rw [if_pos (Int.fract_neg_eq_zero.2 h), if_pos h, neg_zero]
  · rw [if_neg (fun h' => h (Int.fract_neg_eq_zero.1 h')), if_neg h, Int.fract_neg h]
    ring

theorem sN_neg {M x y : ℕ} (hM : 0 < M) (h : M ∣ x + y) : sN M y = -sN M x := by
  obtain ⟨m, hm⟩ := h
  unfold sN
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hy : (y : ℚ) / M = -((x : ℚ) / M) + (m : ℕ) := by
    have : (y : ℚ) = M * m - x := by
      have h2 : ((x + y : ℕ) : ℚ) = ((M * m : ℕ) : ℚ) := by rw [hm]
      push_cast at h2; linarith
    rw [this]; field_simp; ring
  rw [hy, saw_add_nat, saw_neg]
  push_cast; ring

/-! ## Fourier inversion on (ℤ/n)^× -/

theorem fourier_zero {n : ℕ} [NeZero n] (F : (ZMod n)ˣ → ℂ)
    (h : ∀ χ : DirichletCharacter ℂ n, ∑ k : (ZMod n)ˣ, χ⁻¹ (k : ZMod n) * F k = 0)
    (k0 : (ZMod n)ˣ) : F k0 = 0 := by
  have h1 : ∑ χ : DirichletCharacter ℂ n, χ (k0 : ZMod n) *
      ∑ k : (ZMod n)ˣ, χ⁻¹ (k : ZMod n) * F k = 0 := by simp [h]
  simp_rw [mul_sum] at h1
  rw [sum_comm] at h1
  have h2 : ∀ k : (ZMod n)ˣ, ∑ χ : DirichletCharacter ℂ n, χ (k0 : ZMod n) * (χ⁻¹ (k : ZMod n) * F k)
      = (if (k : ZMod n) = k0 then (n.totient : ℂ) else 0) * F k := by
    intro k
    rw [← DirichletCharacter.sum_char_inv_mul_char_eq ℂ (Units.isUnit k) (k0 : ZMod n), sum_mul]
    refine sum_congr rfl (fun χ _ => ?_)
    rw [MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]
    ring
  rw [sum_congr rfl (fun k _ => h2 k)] at h1
  simp_rw [Units.val_inj] at h1
  rw [sum_eq_single k0 (fun k _ hk => by rw [if_neg hk, zero_mul])
    (fun h => absurd (mem_univ k0) h), if_pos rfl] at h1
  have hφ : (n.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne n))).ne'
  exact (mul_eq_zero.1 h1).resolve_left hφ

/-! ## The bracket [x]_χ and B ≠ 0 -/

/-- `[x]_χ` for x = a/n: the right side of Lemma C without the factor `B_{1,χ̄*}`. -/
noncomputable def bracket {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) (a : ℕ) : ℂ :=
  if χ.conductor ∣ n / n.gcd a then
    ((n.totient : ℂ) / (n / n.gcd a).totient)
      * χ.primitiveCharacter ((a / n.gcd a : ℕ) : ZMod χ.conductor)
      * ∏ ℓ ∈ eulerPrimes (n / n.gcd a) χ.conductor,
          (1 - χ.primitiveCharacter⁻¹ (ℓ : ZMod χ.conductor))
  else 0

/-- Left side of Lemma C, `Σ_k χ̄(k)((k a/n))`. -/
noncomputable def LHSC {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) (a : ℕ) : ℂ :=
  ∑ k : (ZMod n)ˣ, χ⁻¹ (k : ZMod n) * sN n ((k : ZMod n).val * a)

theorem LHSC_eq {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) (a : ℕ) :
    LHSC χ a = B χ.primitiveCharacter⁻¹ * bracket χ a := by
  have := lemmaC χ a
  unfold LHSC bracket
  change ∑ k : (ZMod n)ˣ, χ⁻¹ (k : ZMod n) * ((saw ((((k : ZMod n).val * a : ℕ) : ℚ) / n) : ℚ) : ℂ) = _
  rw [this]
  split_ifs <;> ring

theorem primitiveCharacter_odd {n : ℕ} [NeZero n] {χ : DirichletCharacter ℂ n} (ho : χ.Odd) :
    χ.primitiveCharacter.Odd := by
  have h := DirichletCharacter.changeLevel_eq_cast_of_dvd χ.primitiveCharacter
    χ.conductor_dvd_level (-1)
  rw [DirichletCharacter.changeLevel_primitiveCharacter] at h
  simp only [Units.val_neg, Units.val_one] at h
  rw [ZMod.cast_neg χ.conductor_dvd_level, ZMod.cast_one χ.conductor_dvd_level] at h
  show χ.primitiveCharacter (-1) = -1
  rw [← h]; exact ho

/-- `B_{1,χ̄*} ≠ 0` for odd χ (any level): this is `B1` at the primitive character `χ̄*`. -/
theorem B_ne_zero {n : ℕ} [NeZero n] {χ : DirichletCharacter ℂ n} (ho : χ.Odd) :
    B χ.primitiveCharacter⁻¹ ≠ 0 := by
  have hp : (χ.primitiveCharacter⁻¹).IsPrimitive := by
    show (χ.primitiveCharacter⁻¹).conductor = χ.conductor
    rw [DirichletCharacter.conductor_inv]
    exact DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hodd : (χ.primitiveCharacter⁻¹).Odd :=
    Erdos634.LemmaSB1.inv_odd (primitiveCharacter_odd ho)
  exact Erdos634.LemmaSB1H.B1 hp hodd

theorem even_sum_zero {n : ℕ} [NeZero n] {χ : DirichletCharacter ℂ n} (he : χ.Even) (a : ℕ) :
    LHSC χ a = 0 := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hinv : ∀ k : (ZMod n)ˣ, χ⁻¹ ((-k : (ZMod n)ˣ) : ZMod n) = χ⁻¹ (k : ZMod n) := by
    intro k
    have hev : χ (-(k : ZMod n)) = χ (k : ZMod n) := DirichletCharacter.Even.to_fun he (k : ZMod n)
    rw [Units.val_neg, MulChar.inv_apply_eq_inv', MulChar.inv_apply_eq_inv', hev]
  have hs : ∀ k : (ZMod n)ˣ, sN n (((-k : (ZMod n)ˣ) : ZMod n).val * a)
      = -sN n ((k : ZMod n).val * a) := by
    intro k
    apply sN_neg hn
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    simp only [ZMod.natCast_zmod_val, Units.val_neg]; ring
  set S := LHSC χ a with hS
  have hSS : S = -S := by
    rw [hS]; unfold LHSC
    conv_lhs => rw [← Equiv.sum_comp (Equiv.neg (ZMod n)ˣ)]
    rw [← sum_neg_distrib]
    refine sum_congr rfl (fun k _ => ?_)
    simp only [Equiv.neg_apply, hinv, hs]; ring
  have : (2 : ℂ) * S = 0 := by linear_combination hSS
  exact (mul_eq_zero.1 this).resolve_left two_ne_zero

/-! ## The criterion -/

theorem key_sum {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) (a : Fin 3 → ℕ) (e : Fin 3 → ℚ) :
    ∑ i, (e i : ℂ) * LHSC χ (a i)
      = ∑ k : (ZMod n)ˣ, χ⁻¹ (k : ZMod n) * ∑ i, (e i : ℂ) * sN n ((k : ZMod n).val * a i) := by
  unfold LHSC
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl (fun k _ => sum_congr rfl (fun i _ => by ring))

theorem inner_cast {n : ℕ} (k : ℕ) (a : Fin 3 → ℕ) (e : Fin 3 → ℚ) :
    (((∑ i, saw ((k * a i : ℕ) / (n : ℚ)) * e i : ℚ)) : ℂ) = ∑ i, (e i : ℂ) * sN n (k * a i) := by
  rw [Rat.cast_sum]
  refine sum_congr rfl (fun i _ => ?_)
  rw [Rat.cast_mul, mul_comm]; rfl

/-- **Consequence (T1) of Lemma C.** `e ∈ R(a)` iff `Σ_j e_j [x_j]_χ = 0` for every odd χ mod n. -/
theorem mem_relSpace_iff_odd {n : ℕ} [NeZero n] (a : Fin 3 → ℕ) (e : Fin 3 → ℚ) :
    e ∈ relSpace n a ↔
      ∀ χ : DirichletCharacter ℂ n, χ.Odd → ∑ i, (e i : ℂ) * bracket χ (a i) = 0 := by
  constructor
  · intro he χ ho
    have hin : ∀ k : (ZMod n)ˣ, ∑ i, (e i : ℂ) * sN n ((k : ZMod n).val * a i) = 0 := by
      intro k
      rw [← inner_cast, (mem_relSpace.1 he) _ (ZMod.val_coe_unit_coprime k), Rat.cast_zero]
    have h1 := key_sum χ a e
    simp only [hin, mul_zero, sum_const_zero, LHSC_eq] at h1
    have h2 : B χ.primitiveCharacter⁻¹ * ∑ i, (e i : ℂ) * bracket χ (a i) = 0 := by
      rw [mul_sum, ← h1]; refine sum_congr rfl (fun i _ => by ring)
    exact (mul_eq_zero.1 h2).resolve_left (B_ne_zero ho)
  · intro h
    set F : (ZMod n)ˣ → ℂ := fun k => ∑ i, (e i : ℂ) * sN n ((k : ZMod n).val * a i) with hF
    have hall : ∀ χ : DirichletCharacter ℂ n, ∑ k : (ZMod n)ˣ, χ⁻¹ (k : ZMod n) * F k = 0 := by
      intro χ
      simp only [hF]
      rw [← key_sum]
      rcases χ.even_or_odd with he | ho
      · simp [even_sum_zero he]
      · simp_rw [LHSC_eq]
        have : ∑ i, (e i : ℂ) * (B χ.primitiveCharacter⁻¹ * bracket χ (a i))
            = B χ.primitiveCharacter⁻¹ * ∑ i, (e i : ℂ) * bracket χ (a i) := by
          rw [mul_sum]; exact sum_congr rfl (fun i _ => by ring)
        rw [this, h χ ho, mul_zero]
    rw [mem_relSpace]
    intro k hk
    have hF0 := fourier_zero F hall (ZMod.unitOfCoprime k hk)
    have : (((∑ i, saw ((k * a i : ℕ) / (n : ℚ)) * e i : ℚ)) : ℂ) = 0 := by
      rw [inner_cast, ← hF0]
      refine sum_congr rfl (fun i _ => ?_)
      congr 1
      apply sN_congr
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.coe_unitOfCoprime]
    exact_mod_cast this

/-! ## Witness: the criterion fires on the paper's non-vacuity tile (2,5,7)/14 -/

/-- From `e₃ ∈ R(2,5,7)` (the right-angle relation, x₃ = ½) the criterion yields, for EVERY odd
character χ mod 14, `[7/14]_χ = 0`: a genuine consequence drawn through Lemma C and B1. -/
theorem crit_witness_14 : ∀ χ : DirichletCharacter ℂ 14, χ.Odd → bracket χ 7 = 0 := by
  intro χ ho
  have hmem : (Pi.single 2 1 : Fin 3 → ℚ) ∈ relSpace 14 ![2, 5, 7] := by
    have := Erdos634.LemmaS.half_mem (n := 14) (a := ![2, 5, 7]) (i := 2) (by rfl) 1
    rw [one_smul] at this
    exact Erdos634.LemmaS.trivSpace_le _ _ this
  have := (mem_relSpace_iff_odd ![2, 5, 7] _).1 hmem χ ho
  simpa [Fin.sum_univ_three] using this

#print axioms Erdos634.LemmaSC.crit_witness_14

end Erdos634.LemmaSC

#print axioms Erdos634.LemmaSC.fourier_zero
#print axioms Erdos634.LemmaSC.B_ne_zero
#print axioms Erdos634.LemmaSC.even_sum_zero
#print axioms Erdos634.LemmaSC.mem_relSpace_iff_odd
