-- Draft/LemmaSG.lean — CASE A, node A5 (Lemma S), **Lemma G** in the case r = 1
-- ((private working notes, not included) §3.2):
--   p ≥ 7 prime, ε = ±1, g ∈ (Z/p)^×: if ψ(g) is constant over X_ε, then g = ±1,
-- where for r = 1, X_− = all odd characters mod p and X_+ = all nontrivial even characters mod p
-- (every nontrivial character mod a prime is primitive).
-- Route: orthogonality (`DirichletCharacter.sum_characters_eq`) weighted by (1 + ε χ(−1)); the count
-- of even characters is read off the same identity at g = 1 (no bijection needed).
-- The general-level statements (`lemmaG_odd_general`, `lemmaG_even_general`) hold for any n with
-- −1 ≠ 1 (resp. φ(n) ≥ 6) over ALL odd / all nontrivial even characters mod n; for r ≥ 2 the
-- paper's X_ε (primitive characters only) is a different set and is NOT covered here.
-- Formalization debt on a paper-level PROVED node; NOT progress on the /goal. Imported into All.lean (All.lean:639).
import Mathlib

open scoped BigOperators
open DirichletCharacter

namespace Erdos634.LemmaSG

variable {n : ℕ} [NeZero n]

theorem val_neg_one (χ : DirichletCharacter ℂ n) : χ (-1) = 1 ∨ χ (-1) = -1 :=
  χ.even_or_odd

/-- Parity-weighted orthogonality. -/
theorem parity_sum (ε : ℂ) (hε : ε = 1 ∨ ε = -1) (g : ZMod n) :
    ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ n => χ (-1) = ε), 2 * χ g =
      (∑ χ : DirichletCharacter ℂ n, χ g) + ε * ∑ χ : DirichletCharacter ℂ n, χ (-g) := by
  rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun χ _ => ?_
  have hm : χ (-g) = χ (-1) * χ g := by rw [← map_mul]; ring_nf
  rw [hm]
  rcases val_neg_one χ with h | h <;> rcases hε with rfl | rfl <;> simp [h]
  all_goals first | (intro hh; norm_num at hh) | ring

theorem S_zero {g : ZMod n} (hg : g ≠ 1) : ∑ χ : DirichletCharacter ℂ n, χ g = 0 :=
  sum_characters_eq_zero ℂ hg

/-- **Lemma G, ε = −1, any level with −1 ≠ 1**: constancy over all odd characters forces g = ±1. -/
theorem lemmaG_odd_general (h3 : (-1 : ZMod n) ≠ 1) {g : ZMod n} (hg : IsUnit g) (c : ℂ)
    (hc : ∀ χ : DirichletCharacter ℂ n, χ.Odd → χ g = c) : g = 1 ∨ g = -1 := by
  by_contra hne
  push_neg at hne
  have h1 : -g ≠ 1 := fun h => hne.2 (by rw [← neg_neg g, h])
  have hs := parity_sum (-1) (Or.inr rfl) g
  rw [S_zero hne.1, S_zero h1, mul_zero, add_zero] at hs
  obtain ⟨χ₀, hχ₀⟩ := exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ h3
  have ho : χ₀ (-1) = -1 := (val_neg_one χ₀).resolve_left hχ₀
  have hc0 : c ≠ 0 := by
    rw [← hc χ₀ ho]
    intro h0
    have := χ₀.unit_norm_eq_one hg.unit
    rw [IsUnit.unit_spec, h0, norm_zero] at this
    exact zero_ne_one this
  rw [Finset.sum_congr rfl (fun χ hχ => by rw [hc χ (Finset.mem_filter.mp hχ).2]),
    Finset.sum_const, nsmul_eq_mul] at hs
  have hmem : χ₀ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ n => χ (-1) = -1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, ho⟩
  have hcard : ((Finset.univ.filter (fun χ : DirichletCharacter ℂ n => χ (-1) = -1)).card : ℂ) ≠ 0 :=
    by exact_mod_cast (Finset.card_pos.mpr ⟨χ₀, hmem⟩).ne'
  exact mul_ne_zero hcard (mul_ne_zero two_ne_zero hc0) hs

/-- **Lemma G, ε = +1, any level with −1 ≠ 1 and φ(n) ≥ 6**: constancy over all nontrivial even
characters forces g = ±1. -/
theorem lemmaG_even_general (h3 : (-1 : ZMod n) ≠ 1) (hφ : 6 ≤ n.totient) {g : ZMod n}
    (hg : IsUnit g) (c : ℂ) (hc : ∀ χ : DirichletCharacter ℂ n, χ.Even → χ ≠ 1 → χ g = c) :
    g = 1 ∨ g = -1 := by
  by_contra hne
  push_neg at hne
  have h1 : -g ≠ 1 := fun h => hne.2 (by rw [← neg_neg g, h])
  set E := Finset.univ.filter (fun χ : DirichletCharacter ℂ n => χ (-1) = 1) with hE
  -- count: 2|E| = φ(n)
  have hcount := parity_sum 1 (Or.inl rfl) (1 : ZMod n)
  rw [← hE, sum_characters_eq, S_zero (by rwa [ne_eq] : -(1 : ZMod n) ≠ 1)] at hcount
  simp only [map_one, mul_one, if_true, Finset.sum_const, nsmul_eq_mul] at hcount
  -- the sum at g
  have hs := parity_sum 1 (Or.inl rfl) g
  rw [← hE, S_zero hne.1, S_zero h1, mul_zero, add_zero, ← Finset.mul_sum] at hs
  have hs' : ∑ χ ∈ E, χ g = 0 := by
    rcases mul_eq_zero.mp hs with h | h
    · norm_num at h
    · exact h
  have h1E : (1 : DirichletCharacter ℂ n) ∈ E :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, MulChar.one_apply isUnit_one.neg⟩
  rw [← Finset.add_sum_erase _ _ h1E, MulChar.one_apply hg,
    Finset.sum_congr rfl (fun χ hχ => by
      rw [hc χ (Finset.mem_filter.mp (Finset.mem_of_mem_erase hχ)).2
        (Finset.ne_of_mem_erase hχ)]),
    Finset.sum_const, nsmul_eq_mul] at hs'
  -- |E| ≥ 3
  have hEcard : 3 ≤ E.card := by
    have : ((2 * E.card : ℕ) : ℂ) = (n.totient : ℂ) := by push_cast; linear_combination hcount
    have := Nat.cast_injective this
    omega
  have hEr : 2 ≤ (E.erase 1).card := by rw [Finset.card_erase_of_mem h1E]; omega
  obtain ⟨χ₁, hχ₁⟩ := Finset.card_pos.mp (by omega : 0 < (E.erase 1).card)
  have hnc : ‖c‖ = 1 := by
    rw [← hc χ₁ (Finset.mem_filter.mp (Finset.mem_of_mem_erase hχ₁)).2 (Finset.ne_of_mem_erase hχ₁)]
    have := χ₁.unit_norm_eq_one hg.unit
    rwa [IsUnit.unit_spec] at this
  have heq : ((E.erase 1).card : ℂ) * c = -1 := by linear_combination hs'
  have hn := congrArg norm heq
  rw [norm_mul, hnc, mul_one, norm_neg, norm_one, Complex.norm_natCast] at hn
  have : ((E.erase 1).card : ℝ) ≥ 2 := by exact_mod_cast hEr
  linarith

/-- **Lemma G (r = 1), ε = −1**, as in PROOF_lemmaS.md §3.2: p ≥ 7 prime (here p ≥ 3 suffices). -/
theorem lemmaG_prime_odd {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p) {g : ZMod p} (hg : IsUnit g) (c : ℂ)
    (hc : ∀ χ : DirichletCharacter ℂ p, χ.Odd → χ g = c) : g = 1 ∨ g = -1 := by
  refine lemmaG_odd_general ?_ hg c hc
  intro h
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by
    have : (1 : ZMod p) + 1 = 0 := by
        calc (1 : ZMod p) + 1 = -1 + 1 := by rw [h]
          _ = 0 := by ring
    rw [Nat.cast_ofNat]; linear_combination this
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

/-- **Lemma G (r = 1), ε = +1**: p ≥ 7 prime. -/
theorem lemmaG_prime_even {p : ℕ} [hpp : Fact p.Prime] (hp : 7 ≤ p) {g : ZMod p} (hg : IsUnit g)
    (c : ℂ) (hc : ∀ χ : DirichletCharacter ℂ p, χ.Even → χ ≠ 1 → χ g = c) : g = 1 ∨ g = -1 := by
  refine lemmaG_even_general ?_ ?_ hg c hc
  · intro h
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      have : (1 : ZMod p) + 1 = 0 := by
        calc (1 : ZMod p) + 1 = -1 + 1 := by rw [h]
          _ = 0 := by ring
      rw [Nat.cast_ofNat]; linear_combination this
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  · rw [Nat.totient_prime hpp.out]; omega

/-! ## Controls -/

/-- Negative control: the ε = +1 statement FAILS at p = 5 (this is why the paper needs p ≥ 7):
mod 5 there is exactly one nontrivial even character, so any g is "constant" on X_+;
g = 2 ≠ ±1 is a unit. -/
theorem control_p5 : IsUnit (2 : ZMod 5) ∧ (2 : ZMod 5) ≠ 1 ∧ (2 : ZMod 5) ≠ -1 := by
  refine ⟨?_, by decide, by decide⟩
  exact isUnit_iff_exists_inv.mpr ⟨3, by decide⟩

/-- Positive witness: the hypotheses of `lemmaG_prime_odd` hold at p = 7, g = 1 (c = 1). -/
theorem witness_p7 : (1 : ZMod 7) = 1 ∨ (1 : ZMod 7) = -1 :=
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  lemmaG_prime_odd (le_refl 7) isUnit_one 1 (fun χ _ => map_one χ)

end Erdos634.LemmaSG

#print axioms Erdos634.LemmaSG.lemmaG_prime_odd
#print axioms Erdos634.LemmaSG.lemmaG_prime_even
#print axioms Erdos634.LemmaSG.witness_p7
