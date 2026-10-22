/-
# Lemma S, Lemma C (the character formula with Euler factors)

Source: (private working notes, not included), P2 "Level-2 statements", Lemma C
(and §3.1 for the proof):

  (n ≥ 1; x ∈ (1/n)ℤ/ℤ of order n_x, b_x = n_x·x; χ a Dirichlet character mod n with conductor f
  and primitive χ*)
  Σ_{k∈(ℤ/n)^×} χ̄(k)((kx)) = [f | n_x]·(φ(n)/φ(n_x))·χ*(b_x)·B_{1,χ̄*}·∏_{ℓ | n_x, ℓ ∤ f}(1 − χ̄*(ℓ)),
  with B_{1,ω} := Σ_{y mod f_ω} ω(y)((y/f_ω)).

Encoding (each item is the paper's object, not a variant):
* x = a/n with a : ℕ; its order in ℚ/ℤ is n_x = n / gcd(n,a) (= `addOrderOf (a : ZMod n)`,
  see `lemmaC_addOrderOf`); "b_x = n_x·x" is the numerator of x in lowest terms, b_x = a / gcd(n,a)
  (read mod n_x; the proof uses exactly this: ((kx)) = ((k b_x / n_x))).
* χ̄ is the conjugate character, which on (ℤ/n)^× is χ⁻¹ (`MulChar` inverse).
* χ* = `χ.primitiveCharacter` (level `χ.conductor`), χ̄* = `χ.primitiveCharacter⁻¹`.
* B_{1,ω} = `LemmaSC.B ω` = Σ_{y : ZMod f} ω y · ((y.val/f)), literally the sum in `LemmaSB1Hurwitz.B1`.
* the Euler primes {ℓ prime : ℓ | n_x, ℓ ∤ f} = `eulerPrimes n_x f`.

Formalization debt only (Lemma S is PROVED at paper level; Lemma C is standard, Washington ch. 4);
NOT /goal progress.
-/
import Mathlib
import Erdos634.Draft.LemmaSCDist
import Erdos634.Draft.LemmaSB1Hurwitz

open scoped BigOperators
open Finset

namespace Erdos634.LemmaSC

open Erdos634.LemmaS (saw)

instance conductor_neZero {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) : NeZero χ.conductor :=
  ⟨χ.conductor_ne_zero⟩

theorem sN_congr {M x y : ℕ} (h : (x : ZMod M) = (y : ZMod M)) : sN M x = sN M y := by
  rw [sN_mod, (ZMod.natCast_eq_natCast_iff' x y M).1 h, ← sN_mod]

/-- Summing `F ∘ π` over a finite group, `π` a surjective hom: every fiber has the size of the kernel. -/
theorem sum_comp_surj {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H] [DecidableEq H]
    (π : G →* H) (hπ : Function.Surjective π) (F : H → ℂ) :
    ∑ g, F (π g) = ((Finset.univ.filter (fun g => π g = 1)).card : ℂ) * ∑ h, F h := by
  rw [← Finset.sum_fiberwise Finset.univ π (fun g => F (π g)), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [Finset.sum_congr rfl (fun g hg => congrArg F (Finset.mem_filter.1 hg).2), Finset.sum_const,
    nsmul_eq_mul]
  obtain ⟨g0, rfl⟩ := hπ h
  rw [MonoidHom.card_fiber_eq_of_mem_range π ⟨g0, rfl⟩ ⟨1, map_one π⟩]

theorem fiber_card {n d : ℕ} [NeZero n] [NeZero d] (hd : d ∣ n) :
    (((Finset.univ.filter (fun g => ZMod.unitsMap hd g = 1)).card : ℕ) : ℂ)
      = (n.totient : ℂ) / d.totient := by
  have h := sum_comp_surj (ZMod.unitsMap hd) (ZMod.unitsMap_surjective hd) (fun _ => (1 : ℂ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    ZMod.card_units_eq_totient] at h
  have hφ : (d.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne d))).ne'
  rw [eq_div_iff hφ, ← h]

/-- **Lemma C** (PROOF_lemmaS.md P2), with x = a/n, n_x = n / gcd(n,a), b_x = a / gcd(n,a). -/
theorem lemmaC {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) (a : ℕ) :
    ∑ k : (ZMod n)ˣ, χ⁻¹ (k : ZMod n) * ((saw ((((k : ZMod n).val * a : ℕ) : ℚ) / n) : ℚ) : ℂ)
      = if χ.conductor ∣ n / n.gcd a then
          ((n.totient : ℂ) / (n / n.gcd a).totient)
            * χ.primitiveCharacter ((a / n.gcd a : ℕ) : ZMod χ.conductor)
            * B χ.primitiveCharacter⁻¹
            * ∏ ℓ ∈ eulerPrimes (n / n.gcd a) χ.conductor,
                (1 - χ.primitiveCharacter⁻¹ (ℓ : ZMod χ.conductor))
        else 0 := by
  -- notation
  set g := n.gcd a with hg
  set nx := n / g with hnxdef
  set b := a / g with hbdef
  set f := χ.conductor with hfdef
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left a hn
  have hn_eq : n = g * nx := (Nat.mul_div_cancel' (Nat.gcd_dvd_left n a)).symm
  have ha_eq : a = g * b := (Nat.mul_div_cancel' (Nat.gcd_dvd_right n a)).symm
  have hnx0 : 0 < nx := Nat.div_pos (Nat.le_of_dvd hn (Nat.gcd_dvd_left n a)) hg0
  haveI : NeZero nx := ⟨hnx0.ne'⟩
  have hnx : nx ∣ n := ⟨g, by rw [hn_eq, mul_comm]⟩
  have hcop : b.Coprime nx := by
    have := Nat.coprime_div_gcd_div_gcd (m := a) (n := n) (by rw [Nat.gcd_comm]; exact hg0)
    rw [Nat.gcd_comm] at this; exact this
  set π := ZMod.unitsMap hnx with hπ
  set H : (ZMod nx)ˣ → ℂ := fun u => sN nx ((u : ZMod nx).val * b) with hH
  -- Step 1: ((k x)) = ((k b / n_x)), a function of k mod n_x
  have step1 : ∀ k : (ZMod n)ˣ,
      ((saw ((((k : ZMod n).val * a : ℕ) : ℚ) / n) : ℚ) : ℂ) = H (π k) := by
    intro k
    change sN n ((k : ZMod n).val * a) = sN nx (((π k : (ZMod nx)ˣ) : ZMod nx).val * b)
    have e1 : sN n ((k : ZMod n).val * a) = sN nx ((k : ZMod n).val * b) := by
      have h1 := sN_mul hg0 nx ((k : ZMod n).val * b)
      rw [← hn_eq] at h1
      rw [show (k : ZMod n).val * a = g * ((k : ZMod n).val * b) by rw [ha_eq]; ring]
      exact h1
    rw [e1]
    apply sN_congr
    rw [ZMod.unitsMap_val, ZMod.cast_eq_val]
    push_cast
    rw [ZMod.natCast_zmod_val]
  simp_rw [step1]
  by_cases hdiv : f ∣ nx
  · -- Case f | n_x : χ factors through n_x
    rw [if_pos hdiv]
    set χs := χ.primitiveCharacter with hχs
    set χ₁ := DirichletCharacter.changeLevel hdiv χs with hχ₁
    have hχ : χ = DirichletCharacter.changeLevel hnx χ₁ := by
      rw [hχ₁, ← DirichletCharacter.changeLevel_trans]
      exact (DirichletCharacter.changeLevel_primitiveCharacter χ).symm
    have hval : ∀ k : (ZMod n)ˣ, χ⁻¹ (k : ZMod n) = χ₁⁻¹ ((π k : (ZMod nx)ˣ) : ZMod nx) := by
      intro k
      rw [hχ, ← map_inv, DirichletCharacter.changeLevel_eq_cast_of_dvd, ZMod.unitsMap_val]
    simp_rw [hval]
    rw [sum_comp_surj π (ZMod.unitsMap_surjective hnx) (fun u => χ₁⁻¹ (u : ZMod nx) * H u),
      fiber_card hnx]
    -- Step 2: substitute u = v β⁻¹, β the unit b mod n_x
    set β : (ZMod nx)ˣ := ZMod.unitOfCoprime b hcop with hβ
    have hβv : (β : ZMod nx) = (b : ZMod nx) := ZMod.coe_unitOfCoprime b hcop
    have hsub : ∑ u : (ZMod nx)ˣ, χ₁⁻¹ (u : ZMod nx) * H u
        = χ₁ (β : ZMod nx) * ∑ v : (ZMod nx)ˣ, χ₁⁻¹ (v : ZMod nx) * sN nx (v : ZMod nx).val := by
      rw [← Equiv.sum_comp (Equiv.mulRight β⁻¹), Finset.mul_sum]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      simp only [Equiv.coe_mulRight, Units.val_mul]
      have hH' : H (v * β⁻¹) = sN nx (v : ZMod nx).val := by
        change sN nx (((v * β⁻¹ : (ZMod nx)ˣ) : ZMod nx).val * b) = _
        apply sN_congr
        push_cast
        simp only [ZMod.natCast_zmod_val, ← hβv, Units.val_mul, Units.inv_mul_cancel_right]
      have hinv : χ₁⁻¹ ((β⁻¹ : (ZMod nx)ˣ) : ZMod nx) = χ₁ (β : ZMod nx) := by
        rw [MulChar.inv_apply, Ring.inverse_unit, inv_inv]
      rw [map_mul, hH', hinv]; ring
    rw [hsub]
    -- Step 3–4: the sieve at level n_x with ω = χ̄*
    have hω : χ₁⁻¹ = DirichletCharacter.changeLevel hdiv χs⁻¹ := by rw [hχ₁, map_inv]
    have hT := sum_units_changeLevel χs⁻¹ hdiv
    rw [← hω] at hT
    rw [hT]
    have hb : χ₁ (β : ZMod nx) = χs ((b : ℕ) : ZMod f) := by
      rw [hχ₁, DirichletCharacter.changeLevel_eq_cast_of_dvd, hβv, ZMod.cast_natCast hdiv]
    rw [hb]; ring
  · -- Case f ∤ n_x : the sum vanishes
    rw [if_neg hdiv]
    have hnot : ¬ DirichletCharacter.FactorsThrough χ nx := by
      intro h
      exact hdiv ((DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ hnx).1 h)
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (χ := χ) hnx] at hnot
    obtain ⟨k0, hk0, hk0'⟩ := SetLike.not_le_iff_exists.1 hnot
    have hk0π : π k0 = 1 := hk0
    have hχk0 : χ (k0 : ZMod n) ≠ 1 := by
      intro h; apply hk0'
      change χ.toUnitHom k0 = 1
      exact Units.ext (by rw [MulChar.coe_toUnitHom, h]; rfl)
    have hprod : χ⁻¹ (k0 : ZMod n) * χ (k0 : ZMod n) = 1 := by
      have h2 : (χ⁻¹ * χ) (k0 : ZMod n) = χ⁻¹ (k0 : ZMod n) * χ (k0 : ZMod n) := rfl
      rw [← h2, inv_mul_cancel, MulChar.one_apply_coe]
    have hne : χ⁻¹ (k0 : ZMod n) ≠ 1 := by
      intro h; rw [h, one_mul] at hprod; exact hχk0 hprod
    set S := ∑ k : (ZMod n)ˣ, χ⁻¹ (k : ZMod n) * H (π k) with hS
    have hSS : S = χ⁻¹ (k0 : ZMod n) * S := by
      rw [hS]
      conv_lhs => rw [← Equiv.sum_comp (Equiv.mulLeft k0)]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [Equiv.coe_mulLeft, Units.val_mul, map_mul, hk0π, one_mul]
      ring
    have : (1 - χ⁻¹ (k0 : ZMod n)) * S = 0 := by rw [sub_mul, one_mul, ← hSS, sub_self]
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h).symm hne
    · exact h

/-- Lemma C with the order of x written as the paper writes it, `n_x = addOrderOf x`. -/
theorem lemmaC_addOrderOf {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n) (a : ℕ) :
    ∑ k : (ZMod n)ˣ, χ⁻¹ (k : ZMod n) * ((saw ((((k : ZMod n).val * a : ℕ) : ℚ) / n) : ℚ) : ℂ)
      = if χ.conductor ∣ addOrderOf (a : ZMod n) then
          ((n.totient : ℂ) / (addOrderOf (a : ZMod n)).totient)
            * χ.primitiveCharacter ((a / n.gcd a : ℕ) : ZMod χ.conductor)
            * B χ.primitiveCharacter⁻¹
            * ∏ ℓ ∈ eulerPrimes (addOrderOf (a : ZMod n)) χ.conductor,
                (1 - χ.primitiveCharacter⁻¹ (ℓ : ZMod χ.conductor))
        else 0 := by
  rw [ZMod.addOrderOf_coe a (NeZero.ne n)]
  exact lemmaC χ a

/-! ## Witnesses (non-vacuity) -/

/-- Joint witness on a real odd primitive character mod 3 (from `LemmaSB1`), a = 1:
Lemma C fires and its "f | n_x" branch is the one taken. -/
theorem lemmaC_witness_mod3 : ∃ χ : DirichletCharacter ℂ 3, χ.IsPrimitive ∧ χ.Odd ∧
    χ.conductor ∣ 3 / Nat.gcd 3 1 ∧
    ∑ k : (ZMod 3)ˣ, χ⁻¹ (k : ZMod 3) * ((saw ((((k : ZMod 3).val * 1 : ℕ) : ℚ) / ((3 : ℕ) : ℚ)) : ℚ) : ℂ)
      = ((Nat.totient 3 : ℂ) / (3 / Nat.gcd 3 1).totient)
            * χ.primitiveCharacter ((1 / Nat.gcd 3 1 : ℕ) : ZMod χ.conductor)
            * B χ.primitiveCharacter⁻¹
            * ∏ ℓ ∈ eulerPrimes (3 / Nat.gcd 3 1) χ.conductor,
                (1 - χ.primitiveCharacter⁻¹ (ℓ : ZMod χ.conductor)) := by
  obtain ⟨χ, hp, ho⟩ := Erdos634.LemmaSB1.exists_odd_primitive_mod3
  have hc : χ.conductor = 3 := hp
  have hdiv : χ.conductor ∣ 3 / Nat.gcd 3 1 := by rw [hc]; norm_num
  refine ⟨χ, hp, ho, hdiv, ?_⟩
  rw [lemmaC χ 1, if_pos hdiv]

/-- Negative control for the branch `f ∤ n_x`: at n = 3, a = 3 (x = 0, n_x = 1) and χ odd
primitive mod 3, Lemma C says the sum is 0 (consistent: ((k·0)) = 0). -/
theorem lemmaC_control_zero : ∃ χ : DirichletCharacter ℂ 3, χ.Odd ∧ ¬ χ.conductor ∣ 3 / Nat.gcd 3 3 ∧
    ∑ k : (ZMod 3)ˣ, χ⁻¹ (k : ZMod 3) * ((saw ((((k : ZMod 3).val * 3 : ℕ) : ℚ) / ((3 : ℕ) : ℚ)) : ℚ) : ℂ) = 0 := by
  obtain ⟨χ, hp, ho⟩ := Erdos634.LemmaSB1.exists_odd_primitive_mod3
  have hc : χ.conductor = 3 := hp
  have hnd : ¬ χ.conductor ∣ 3 / Nat.gcd 3 3 := by rw [hc]; norm_num
  refine ⟨χ, ho, hnd, ?_⟩
  rw [lemmaC χ 3, if_neg hnd]

end Erdos634.LemmaSC

#print axioms Erdos634.LemmaSC.T_eq
#print axioms Erdos634.LemmaSC.sum_units_changeLevel
#print axioms Erdos634.LemmaSC.lemmaC
#print axioms Erdos634.LemmaSC.lemmaC_addOrderOf
#print axioms Erdos634.LemmaSC.lemmaC_witness_mod3
#print axioms Erdos634.LemmaSC.lemmaC_control_zero
