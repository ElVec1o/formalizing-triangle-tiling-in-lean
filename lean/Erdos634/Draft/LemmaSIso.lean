/-
Lemma S, node A5: **Lemma Iso** (PROOF_lemmaS.md §3.4, P2).

  Iso (Lemma P's hypothesis; p ≥ 7). j ∈ I, and f(d_j) ∤ d_k for every other k ∈ I with e_k ≠ 0
  ⟹ e_j = 0.
  Proof: take η primitive mod f(d_j), of either parity. Only term j survives; its component is
  e_j w ψ(β_j d_j) η(γ_j)(1 − ψ̄(2)η̄(2))^{[2∥d_j]}. If e_j ≠ 0 then ψ(2) = η̄(2) for every ψ ∈ X_ε,
  contradicting G, since 2 ≢ ±1 (mod p).

Lemma P's hypothesis, as written: Σ_j e_j[x_j]_χ = 0 for every odd χ mod n whose conductor is
divisible by p^r (n = p^r m, p ∤ m). f(d) = d if d ≢ 2 (mod 4), d/2 otherwise (`fpc`).
Also: the conductor of a level-raised primitive character (`conductor_changeLevel_of_isPrimitive`).
Formalization debt, not /goal progress.
-/
import Mathlib
import Erdos634.Draft.LemmaSPhi
import Erdos634.Draft.LemmaSGprime
import Erdos634.Draft.LemmaSG2

open scoped BigOperators
open Finset

namespace Erdos634.LemmaSIso

open DirichletCharacter
open Erdos634.LemmaSC (bracket eulerPrimes)
open Erdos634.LemmaSPhi (chi dm conductor_chi bracket_p_dvd bracket_unit cop_pr)

/-- f(d): the largest divisor of d that is a primitive conductor with the same odd radical. -/
def fpc (d : ℕ) : ℕ := if d % 4 = 2 then d / 2 else d

theorem fpc_dvd (d : ℕ) : fpc d ∣ d := by
  unfold fpc; split_ifs with h
  · exact Nat.div_dvd_of_dvd (by omega)
  · exact dvd_rfl

theorem fpc_mod4 (d : ℕ) : fpc d % 4 ≠ 2 := by unfold fpc; split_ifs <;> omega

theorem fpc_ne_zero {d : ℕ} (hd : d ≠ 0) : fpc d ≠ 0 := by unfold fpc; split_ifs <;> omega

theorem euler_fpc {d ℓ : ℕ} (hl : ℓ ∈ eulerPrimes d (fpc d)) : ℓ = 2 := by
  simp only [eulerPrimes, mem_filter, Nat.mem_primeFactors] at hl
  obtain ⟨⟨hl, hld, -⟩, hn⟩ := hl
  unfold fpc at hn
  split_ifs at hn with h
  · have h2 : d = 2 * (d / 2) := by omega
    rw [h2] at hld
    rcases hl.dvd_mul.1 hld with h' | h'
    · exact (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 h'
    · exact absurd h' hn
  · exact absurd hld hn

/-- The conductor of a primitive character raised to a higher level is unchanged. -/
theorem conductor_changeLevel_of_isPrimitive {f m : ℕ} [NeZero m] [NeZero f] (h : f ∣ m)
    {η₀ : DirichletCharacter ℂ f} (hη₀ : η₀.IsPrimitive) : (changeLevel h η₀).conductor = f := by
  set η := changeLevel h η₀
  have hcf : η.conductor ∣ f := conductor_dvd_of_mem_conductorSet η ⟨h, η₀, rfl⟩
  refine Nat.dvd_antisymm hcf ?_
  have hft : η₀.FactorsThrough η.conductor := by
    rw [factorsThrough_iff_ker_unitsMap hcf]
    intro u hu
    obtain ⟨v, rfl⟩ := ZMod.unitsMap_surjective h u
    have hv : v ∈ (ZMod.unitsMap (dvd_trans hcf h)).ker := by
      rw [MonoidHom.mem_ker, ← ZMod.unitsMap_comp hcf h, MonoidHom.comp_apply]
      exact hu
    have := (factorsThrough_iff_ker_unitsMap (dvd_trans hcf h)).1 (factorsThrough_conductor η) hv
    rw [MonoidHom.mem_ker] at this ⊢
    rwa [changeLevel_toUnitHom, MonoidHom.comp_apply] at this
  have := conductor_dvd_of_mem_conductorSet η₀ hft
  rwa [show η₀.conductor = f from hη₀] at this

theorem primChar_ne_zero {N : ℕ} [NeZero N] (η : DirichletCharacter ℂ N) (b : ℕ)
    (hb : b.Coprime η.conductor) : η.primitiveCharacter (b : ZMod η.conductor) ≠ 0 := by
  haveI : NeZero η.conductor := ⟨conductor_ne_zero η⟩
  rw [← ZMod.coe_unitOfCoprime b hb]
  exact Erdos634.DirichletCRT.unit_val_ne_zero _ _

theorem two_ne_pm_one {P : ℕ} (hP : 7 ≤ P) :
    ((2 : ℕ) : ZMod P) ≠ 1 ∧ ((2 : ℕ) : ZMod P) ≠ -1 := by
  constructor
  · intro h
    rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff] at h
    unfold Nat.ModEq at h
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
    omega
  · intro h
    have h3 : ((3 : ℕ) : ZMod P) = 0 := by
      rw [show (3 : ℕ) = 2 + 1 by rfl, Nat.cast_add, h, Nat.cast_one]; ring
    rw [ZMod.natCast_eq_zero_iff] at h3
    exact absurd (Nat.le_of_dvd (by norm_num) h3) (by omega)

section Iso
variable {p r m : ℕ} [hp : Fact p.Prime] [NeZero m]

/-- **Lemma Iso**, as written. -/
theorem lemmaIso (hp7 : 7 ≤ p) (hr : 1 ≤ r) (hpm : ¬ p ∣ m) {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (e : ι → ℚ)
    (hP : ∀ χ : DirichletCharacter ℂ (p ^ r * m), χ.Odd → p ^ r ∣ χ.conductor →
      ∑ j, (e j : ℂ) * bracket χ (a j) = 0)
    (j : ι) (hj : ¬ p ∣ a j)
    (hiso : ∀ k, k ≠ j → ¬ p ∣ a k → e k ≠ 0 → ¬ fpc (dm m (a j)) ∣ dm m (a k)) :
    e j = 0 := by
  by_contra hej
  have hP7 : 7 ≤ p ^ r := le_trans hp7 (Nat.le_self_pow (by omega) p)
  set d := dm m (a j) with hd
  set f := fpc d with hf
  have hdm : d ∣ m := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left m (a j))
  have hd0 : d ≠ 0 := by
    intro h0
    have := Nat.div_mul_cancel (Nat.gcd_dvd_left m (a j))
    rw [show m / m.gcd (a j) = 0 from h0, zero_mul] at this
    exact NeZero.ne m this.symm
  have hfd : f ∣ d := fpc_dvd d
  have hfm : f ∣ m := dvd_trans hfd hdm
  haveI : NeZero f := ⟨fpc_ne_zero hd0⟩
  obtain ⟨η₀, hη₀⟩ := Erdos634.LemmaSGprime.exists_primitive (fpc_ne_zero hd0) (fpc_mod4 d)
  set η : DirichletCharacter ℂ m := changeLevel hfm η₀
  have hηc : η.conductor = f := conductor_changeLevel_of_isPrimitive hfm hη₀
  set ε : ℂ := -η (-1)
  have hε : ε = 1 ∨ ε = -1 := by
    rcases η.even_or_odd with h | h
    · right; simp only [ε, show η (-1) = 1 from h]
    · left; simp only [ε, show η (-1) = -1 from h, neg_neg]
  -- the surviving term
  set b := a j / m.gcd (a j)
  have hgpos : 0 < m.gcd (a j) := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne m))
  have hbd : d.Coprime b := Nat.coprime_div_gcd_div_gcd hgpos
  have hbf : b.Coprime η.conductor := by rw [hηc]; exact (hbd.coprime_dvd_left hfd).symm
  have hbP : b.Coprime (p ^ r) := by
    refine Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hp.out).2 ?_).symm
    exact fun h => hj (dvd_trans h (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right m (a j))))
  have key : ∀ ψ : DirichletCharacter ℂ (p ^ r), ψ.IsPrimitive → ψ (-1) = ε →
      ∏ ℓ ∈ eulerPrimes d η.conductor,
        (1 - ψ⁻¹ (ℓ : ZMod (p ^ r)) * η.primitiveCharacter⁻¹ (ℓ : ZMod η.conductor)) = 0 := by
    intro ψ hψ hψε
    have hη2 : η (-1) * η (-1) = 1 := by
      rcases η.even_or_odd with h | h
      · rw [show η (-1) = 1 from h]; ring
      · rw [show η (-1) = -1 from h]; ring
    have hodd : (chi ψ η).Odd := by
      show (chi ψ η) (-1) = -1
      rw [MulChar.coeToFun_mul, Pi.mul_apply,
        Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_right (p ^ r) m) ψ,
        Erdos634.LemmaSG2.changeLevel_neg_one (Nat.dvd_mul_left m (p ^ r)) η, hψε]
      simp only [ε]
      linear_combination -hη2
    have hsum := hP (chi ψ η) hodd (by rw [conductor_chi hpm hψ η]; exact Nat.dvd_mul_right _ _)
    rw [sum_eq_single j] at hsum
    · rw [bracket_unit hpm hψ η (a j) hj, if_pos (by rw [hηc]; exact hfd)] at hsum
      have hw : (m.totient : ℂ) / (dm m (a j)).totient ≠ 0 :=
        div_ne_zero (by exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne m))).ne')
          (by exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero hd0)).ne')
      have hψb : ψ (b : ZMod (p ^ r)) ≠ 0 := by
        rw [← ZMod.coe_unitOfCoprime b hbP]; exact Erdos634.DirichletCRT.unit_val_ne_zero _ _
      have hηb := primChar_ne_zero η b hbf
      have he : (e j : ℂ) ≠ 0 := by exact_mod_cast hej
      rcases mul_eq_zero.1 hsum with h | h
      · exact absurd h he
      rcases mul_eq_zero.1 h with h | h
      · rcases mul_eq_zero.1 h with h | h
        · rcases mul_eq_zero.1 h with h | h
          · exact absurd h hw
          · exact absurd h hψb
        · exact absurd h hηb
      · exact h
    · intro k _ hk
      by_cases hpk : p ∣ a k
      · rw [bracket_p_dvd hr hpm hψ η _ hpk, mul_zero]
      by_cases hek : e k = 0
      · rw [hek]; simp
      rw [bracket_unit hpm hψ η (a k) hpk, if_neg (by rw [hηc]; exact hiso k hk hpk hek), mul_zero]
    · intro h; exact absurd (mem_univ j) h
  -- conclude with Lemma G at g = 2
  have hc2 : (2 : ℕ).Coprime (p ^ r) :=
    Nat.Coprime.pow_right r ((Nat.coprime_primes Nat.prime_two hp.out).2 (by omega))
  set g2 : (ZMod (p ^ r))ˣ := ZMod.unitOfCoprime 2 hc2
  have hg2 : (g2 : ZMod (p ^ r)) = ((2 : ℕ) : ZMod (p ^ r)) := ZMod.coe_unitOfCoprime 2 hc2
  have hE : eulerPrimes d η.conductor ⊆ {2} := by
    intro ℓ hl; rw [hηc] at hl; exact mem_singleton.2 (euler_fpc hl)
  obtain ⟨h21, h2m1⟩ := two_ne_pm_one hP7
  rcases subset_singleton_iff.1 hE with h0 | h2
  · have := Erdos634.LemmaSG2.lemmaG hp7 hr hε g2 0 (fun ψ hψ hψε => by
      have := key ψ hψ hψε
      rw [h0, prod_empty] at this
      exact absurd this one_ne_zero)
    rw [hg2] at this
    rcases this with h | h
    · exact h21 h
    · exact h2m1 h
  · set c' := η.primitiveCharacter⁻¹ ((2 : ℕ) : ZMod η.conductor)
    have := Erdos634.LemmaSG2.lemmaG hp7 hr hε g2 c' (fun ψ hψ hψε => by
      have h := key ψ hψ hψε
      rw [h2, prod_singleton] at h
      have hψ2 : ψ (g2 : ZMod (p ^ r)) ≠ 0 := Erdos634.DirichletCRT.unit_val_ne_zero _ _
      rw [hg2] at hψ2 ⊢
      rw [MulChar.inv_apply_eq_inv'] at h
      have h' : (ψ ((2 : ℕ) : ZMod (p ^ r)))⁻¹ * c' = 1 := by linear_combination -h
      calc ψ ((2 : ℕ) : ZMod (p ^ r))
          = ψ ((2 : ℕ) : ZMod (p ^ r)) * ((ψ ((2 : ℕ) : ZMod (p ^ r)))⁻¹ * c') := by rw [h', mul_one]
        _ = c' := by rw [← mul_assoc, mul_inv_cancel₀ hψ2, one_mul])
    rw [hg2] at this
    rcases this with h | h
    · exact h21 h
    · exact h2m1 h

end Iso

/-! ## Witness: every hypothesis of `lemmaIso` realised with e ≠ 0.
n = 14 = 7·2, a = (2, 5, 7) (the (2,5,7)/14 tile), e = (0, 0, 1) — the right-angle relation
(x₃ = ½), which lies in R(a), so Lemma P's hypothesis holds (through Lemma C + B1, `crit_witness_14`).
j = 1st index (a = 2, 7 ∤ 2); the Iso side condition holds; conclusion e₁ = 0. -/
theorem witness_iso : (![0, 0, 1] : Fin 3 → ℚ) 0 = 0 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine lemmaIso (p := 7) (r := 1) (m := 2) (by norm_num) le_rfl (by norm_num) ![2, 5, 7]
    ![0, 0, 1] ?_ 0 (by decide) ?_
  · intro χ ho _
    have := Erdos634.LemmaSC.crit_witness_14 χ ho
    simp [Fin.sum_univ_three, this]
  · intro k hk hpk hek
    fin_cases k
    · exact absurd rfl hk
    · exact absurd rfl hek
    · exact absurd (by decide) hpk

#print axioms Erdos634.LemmaSIso.lemmaIso
#print axioms Erdos634.LemmaSIso.conductor_changeLevel_of_isPrimitive
#print axioms Erdos634.LemmaSIso.witness_iso

end Erdos634.LemmaSIso
