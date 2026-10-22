/-
# Lemma S, Lemma N (parity/kernel invariance in the group ring of (ℤ/p^r)^×)

Source: (private working notes, not included) P2 (as repaired by P1.1 / R-a):

  **Lemma N** (p odd prime; r ≥ 1; Φ ∈ ℂ[𝒢]; ε ∈ {±1}; ψ(Φ) = 0 for every primitive ψ with
  ψ(−1) = ε). Φ^ε := Φ + ε[−1]Φ is N-invariant. Hence:
  (a) if every coset of N contains fewer than |N| points of supp Φ ∪ −supp Φ, then Φ = −ε[−1]Φ;
  (b) if r = 1 and ε = −1 (η even), then Φ = [−1]Φ, with no support condition;
  (c) (R-a) if r = 1 and ε = +1 (η odd), then Φ + [−1]Φ is constant on 𝒢. So Φ = −[−1]Φ as soon as
      |supp(Φ + [−1]Φ)| < p − 1.

Encoding: 𝒢 = (ZMod (p^r))ˣ; Φ : 𝒢 → ℂ; ([−1]Φ)(u) = Φ(−u); ψ(Φ) = Σ_u ψ(u) Φ(u);
N = ker(𝒢 → (ZMod (p^(r−1)))ˣ) (`ZMod.unitsMap`). "ψ primitive" is `ψ.IsPrimitive` (conductor = p^r).
(p odd is not needed by the proof; p prime suffices.)

Formalization debt only (Lemma S is PROVED at paper level); NOT /goal progress.
-/
import Mathlib
import Erdos634.Draft.LemmaSCCrit

open scoped BigOperators
open Finset

namespace Erdos634.LemmaSN

theorem pred_dvd (p r : ℕ) : p ^ (r - 1) ∣ p ^ r := pow_dvd_pow p (Nat.sub_le r 1)

/-- A character mod p^r (r ≥ 1) is primitive iff it does not factor through p^(r−1). -/
theorem isPrimitive_iff_not_factorsThrough {p r : ℕ} [hp : Fact p.Prime] (hr : 1 ≤ r)
    (ψ : DirichletCharacter ℂ (p ^ r)) :
    ψ.IsPrimitive ↔ ¬ ψ.FactorsThrough (p ^ (r - 1)) := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hlt : p ^ (r - 1) < p ^ r := Nat.pow_lt_pow_right hp.out.one_lt (by omega)
  constructor
  · intro hprim hf
    have h1 := (DirichletCharacter.mem_conductorSet_iff_conductor_dvd ψ (pred_dvd p r)).1 hf
    rw [show ψ.conductor = p ^ r from hprim] at h1
    exact absurd (Nat.le_of_dvd (pow_pos hp.out.pos _) h1) (not_le.2 hlt)
  · intro hnf
    show ψ.conductor = p ^ r
    obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow hp.out).1 ψ.conductor_dvd_level
    by_contra hne
    have hir : i ≤ r - 1 := by
      rcases Nat.lt_or_ge i r with h | h
      · omega
      · exact absurd (by rw [hci, show i = r by omega]) hne
    apply hnf
    exact (DirichletCharacter.mem_conductorSet_iff_conductor_dvd ψ (pred_dvd p r)).2
      (by rw [hci]; exact pow_dvd_pow p hir)

/-- **Lemma N (core).** Φ^ε := Φ + ε[−1]Φ is invariant under N. -/
theorem lemmaN {p r : ℕ} [hp : Fact p.Prime] (hr : 1 ≤ r) (Φ : (ZMod (p ^ r))ˣ → ℂ) {ε : ℂ}
    (hε : ε = 1 ∨ ε = -1)
    (h : ∀ ψ : DirichletCharacter ℂ (p ^ r), ψ.IsPrimitive → ψ (-1) = ε →
      ∑ u : (ZMod (p ^ r))ˣ, ψ (u : ZMod (p ^ r)) * Φ u = 0)
    (u n0 : (ZMod (p ^ r))ˣ) (hn0 : ZMod.unitsMap (pred_dvd p r) n0 = 1) :
    Φ (u * n0) + ε * Φ (-(u * n0)) = Φ u + ε * Φ (-u) := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  set Ψ : (ZMod (p ^ r))ˣ → ℂ := fun v => Φ v + ε * Φ (-v) with hΨ
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hann : ∀ ω : DirichletCharacter ℂ (p ^ r), ω.IsPrimitive →
      ∑ v : (ZMod (p ^ r))ˣ, ω (v : ZMod (p ^ r)) * Ψ v = 0 := by
    intro ω hω
    have hneg : ∑ v : (ZMod (p ^ r))ˣ, ω (v : ZMod (p ^ r)) * Φ (-v)
        = ω (-1) * ∑ v : (ZMod (p ^ r))ˣ, ω (v : ZMod (p ^ r)) * Φ v := by
      rw [← Equiv.sum_comp (Equiv.neg _), mul_sum]
      refine sum_congr rfl (fun v _ => ?_)
      simp only [Equiv.neg_apply, neg_neg, Units.val_neg]
      rw [neg_eq_neg_one_mul (v : ZMod (p ^ r)), map_mul]; ring
    have hsplit : ∑ v : (ZMod (p ^ r))ˣ, ω (v : ZMod (p ^ r)) * Ψ v
        = (1 + ε * ω (-1)) * ∑ v : (ZMod (p ^ r))ˣ, ω (v : ZMod (p ^ r)) * Φ v := by
      simp only [hΨ, mul_add, sum_add_distrib]
      rw [show ∑ v : (ZMod (p ^ r))ˣ, ω (v : ZMod (p ^ r)) * (ε * Φ (-v))
          = ε * ∑ v : (ZMod (p ^ r))ˣ, ω (v : ZMod (p ^ r)) * Φ (-v) by
            rw [mul_sum]; exact sum_congr rfl (fun v _ => by ring), hneg]
      ring
    rw [hsplit]
    by_cases hpar : ω (-1) = ε
    · rw [h ω hω hpar, mul_zero]
    · have hm : ω (-1) = -ε := by
        rcases ω.even_or_odd with h1 | h1 <;> rcases hε with rfl | rfl
        · exact absurd h1 hpar
        · exact (by rw [show ω (-1) = 1 from h1]; try norm_num)
        · exact (by rw [show ω (-1) = -1 from h1]; try norm_num)
        · exact absurd h1 hpar
      rw [hm, show 1 + ε * -ε = 1 - ε * ε by ring, hε2, sub_self, zero_mul]
  have hall : ∀ ψ : DirichletCharacter ℂ (p ^ r),
      ∑ v : (ZMod (p ^ r))ˣ, ψ⁻¹ (v : ZMod (p ^ r)) * (Ψ (v * n0) - Ψ v) = 0 := by
    intro ψ
    set ω := ψ⁻¹ with hωdef
    have hshift : ∑ v : (ZMod (p ^ r))ˣ, ω (v : ZMod (p ^ r)) * Ψ (v * n0)
        = ω ((n0⁻¹ : (ZMod (p ^ r))ˣ) : ZMod (p ^ r)) *
            ∑ v : (ZMod (p ^ r))ˣ, ω (v : ZMod (p ^ r)) * Ψ v := by
      rw [← Equiv.sum_comp (Equiv.mulRight n0⁻¹), mul_sum]
      refine sum_congr rfl (fun v _ => ?_)
      simp only [Equiv.coe_mulRight, Units.val_mul, map_mul, inv_mul_cancel_right]
      ring
    have hdiff : ∑ v : (ZMod (p ^ r))ˣ, ω (v : ZMod (p ^ r)) * (Ψ (v * n0) - Ψ v)
        = (ω ((n0⁻¹ : (ZMod (p ^ r))ˣ) : ZMod (p ^ r)) - 1) *
            ∑ v : (ZMod (p ^ r))ˣ, ω (v : ZMod (p ^ r)) * Ψ v := by
      rw [sub_mul, one_mul, ← hshift, ← sum_sub_distrib]
      exact sum_congr rfl (fun v _ => by ring)
    rw [hdiff]
    by_cases hω : ω.IsPrimitive
    · rw [hann ω hω, mul_zero]
    · have hf : ω.FactorsThrough (p ^ (r - 1)) :=
        not_not.1 (fun h' => hω ((isPrimitive_iff_not_factorsThrough hr ω).2 h'))
      rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap (χ := ω) (pred_dvd p r)] at hf
      have hmem : n0⁻¹ ∈ (ZMod.unitsMap (pred_dvd p r)).ker := by
        rw [MonoidHom.mem_ker, map_inv, hn0, inv_one]
      have h1 := hf hmem
      rw [MonoidHom.mem_ker] at h1
      have h2 : ω ((n0⁻¹ : (ZMod (p ^ r))ˣ) : ZMod (p ^ r)) = 1 := by
        rw [← MulChar.coe_toUnitHom, h1, Units.val_one]
      rw [h2, sub_self, zero_mul]
  have := Erdos634.LemmaSC.fourier_zero (fun v => Ψ (v * n0) - Ψ v) hall u
  simp only [hΨ] at this
  linear_combination this

/-- **Lemma N (a).** If every N-coset holds fewer than |N| points of supp Φ ∪ −supp Φ,
then Φ = −ε[−1]Φ. -/
theorem lemmaN_a {p r : ℕ} [hp : Fact p.Prime] (hr : 1 ≤ r) (Φ : (ZMod (p ^ r))ˣ → ℂ) {ε : ℂ}
    (hε : ε = 1 ∨ ε = -1)
    (h : ∀ ψ : DirichletCharacter ℂ (p ^ r), ψ.IsPrimitive → ψ (-1) = ε →
      ∑ u : (ZMod (p ^ r))ˣ, ψ (u : ZMod (p ^ r)) * Φ u = 0)
    (hcount : ∀ u : (ZMod (p ^ r))ˣ,
      (univ.filter (fun v => ZMod.unitsMap (pred_dvd p r) v = ZMod.unitsMap (pred_dvd p r) u ∧
        (Φ v ≠ 0 ∨ Φ (-v) ≠ 0))).card
        < (univ.filter (fun v => ZMod.unitsMap (pred_dvd p r) v = 1)).card) :
    ∀ u, Φ u = -ε * Φ (-u) := by
  intro u
  by_contra hne
  have hΨ : Φ u + ε * Φ (-u) ≠ 0 := fun h0 => hne (by linear_combination h0)
  apply absurd (hcount u)
  apply not_lt.2
  apply Finset.card_le_card_of_injOn (fun n => u * n)
  · intro n hn
    have hn' := (mem_filter.1 hn).2
    refine mem_filter.2 ⟨mem_univ _, ?_, ?_⟩
    · rw [map_mul, hn', mul_one]
    · have hinv := lemmaN hr Φ hε h u n hn'
      by_contra hboth
      push Not at hboth
      apply hΨ
      rw [← hinv, hboth.1, hboth.2, mul_zero, add_zero]
  · intro x _ y _ hxy
    exact mul_left_cancel hxy

theorem unitsMap_one_trivial {p : ℕ} (n0 : (ZMod (p ^ 1))ˣ) : ZMod.unitsMap (pred_dvd p 1) n0 = 1 := by
  apply Units.ext
  show (_ : ZMod 1) = _
  exact Subsingleton.elim _ _

/-- **Lemma N (b).** r = 1, ε = −1: Φ = [−1]Φ, no support condition. -/
theorem lemmaN_b {p : ℕ} [hp : Fact p.Prime] (Φ : (ZMod (p ^ 1))ˣ → ℂ)
    (h : ∀ ψ : DirichletCharacter ℂ (p ^ 1), ψ.IsPrimitive → ψ (-1) = -1 →
      ∑ u : (ZMod (p ^ 1))ˣ, ψ (u : ZMod (p ^ 1)) * Φ u = 0) :
    ∀ u, Φ u = Φ (-u) := by
  intro u
  have h1 := lemmaN le_rfl Φ (Or.inr rfl) h u (-1) (unitsMap_one_trivial _)
  rw [mul_neg_one, neg_neg] at h1
  linear_combination (-1/2 : ℂ) * h1

/-- **Lemma N (c)** (repaired form R-a). r = 1, ε = +1: Φ + [−1]Φ is constant; hence
Φ = −[−1]Φ as soon as |supp(Φ + [−1]Φ)| < p − 1. -/
theorem lemmaN_c_const {p : ℕ} [hp : Fact p.Prime] (Φ : (ZMod (p ^ 1))ˣ → ℂ)
    (h : ∀ ψ : DirichletCharacter ℂ (p ^ 1), ψ.IsPrimitive → ψ (-1) = 1 →
      ∑ u : (ZMod (p ^ 1))ˣ, ψ (u : ZMod (p ^ 1)) * Φ u = 0) :
    ∀ u, Φ u + Φ (-u) = Φ 1 + Φ (-1) := by
  intro u
  have h1 := lemmaN le_rfl Φ (Or.inl rfl) h 1 u (unitsMap_one_trivial _)
  rw [one_mul, one_mul] at h1
  linear_combination h1

theorem lemmaN_c {p : ℕ} [hp : Fact p.Prime] (Φ : (ZMod (p ^ 1))ˣ → ℂ)
    (h : ∀ ψ : DirichletCharacter ℂ (p ^ 1), ψ.IsPrimitive → ψ (-1) = 1 →
      ∑ u : (ZMod (p ^ 1))ˣ, ψ (u : ZMod (p ^ 1)) * Φ u = 0)
    (hcard : (univ.filter (fun v : (ZMod (p ^ 1))ˣ => Φ v + Φ (-v) ≠ 0)).card < p - 1) :
    ∀ u, Φ u = -Φ (-u) := by
  haveI : NeZero (p ^ 1) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hc := lemmaN_c_const Φ h
  have hzero : Φ 1 + Φ (-1) = 0 := by
    by_contra hne
    have hall : univ.filter (fun v : (ZMod (p ^ 1))ˣ => Φ v + Φ (-v) ≠ 0) = univ := by
      ext v; simp only [mem_filter, mem_univ, true_and, iff_true]; rw [hc v]; exact hne
    rw [hall, card_univ, ZMod.card_units_eq_totient, pow_one, Nat.totient_prime hp.out] at hcard
    exact lt_irrefl _ hcard
  intro u
  have := hc u
  rw [hzero] at this
  linear_combination this

/-! ## Witness and negative control for (c) at p = 7 -/

instance fact7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem ne_one_of_primitive7 {ψ : DirichletCharacter ℂ (7 ^ 1)} (hψ : ψ.IsPrimitive) : ψ ≠ 1 := by
  rintro rfl
  have : (1 : DirichletCharacter ℂ (7 ^ 1)).conductor = 7 ^ 1 := hψ
  rw [DirichletCharacter.conductor_one] at this
  norm_num at this

theorem sum_units_eq_zero7 {χ : DirichletCharacter ℂ (7 ^ 1)} (hχ : χ ≠ 1) :
    ∑ u : (ZMod (7 ^ 1))ˣ, χ (u : ZMod (7 ^ 1)) = 0 := by
  have := Erdos634.LemmaSC.sum_units_eq_sum χ (fun _ => (1 : ℂ))
  simp only [mul_one] at this
  rw [this]
  exact MulChar.sum_eq_zero_of_ne_one hχ

/-- Witness: Φ = the values of an odd character χ mod 7 (nonzero) satisfies the hypotheses of (c)
(every even primitive ψ kills it, and Φ + [−1]Φ ≡ 0), and the conclusion holds. -/
theorem lemmaN_c_witness : ∃ Φ : (ZMod (7 ^ 1))ˣ → ℂ, Φ 1 ≠ 0 ∧
    (∀ ψ : DirichletCharacter ℂ (7 ^ 1), ψ.IsPrimitive → ψ (-1) = 1 →
      ∑ u : (ZMod (7 ^ 1))ˣ, ψ (u : ZMod (7 ^ 1)) * Φ u = 0) ∧
    (univ.filter (fun v : (ZMod (7 ^ 1))ˣ => Φ v + Φ (-v) ≠ 0)).card < 7 - 1 := by
  have hm1 : (-1 : ZMod (7 ^ 1)) ≠ 1 := by decide
  obtain ⟨χ, hχ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ hm1
  have ho : χ (-1) = -1 := χ.even_or_odd.resolve_left hχ
  refine ⟨fun u => χ (u : ZMod (7 ^ 1)), by simp, ?_, ?_⟩
  · intro ψ _ hψe
    have hne : ψ * χ ≠ 1 := by
      intro h1
      have := congrArg (fun φ : DirichletCharacter ℂ (7 ^ 1) => φ (-1)) h1
      simp only [MulChar.coeToFun_mul, Pi.mul_apply, hψe, ho] at this
      rw [MulChar.one_apply (isUnit_one.neg)] at this
      norm_num at this
    have := sum_units_eq_zero7 hne
    simpa only [MulChar.coeToFun_mul, Pi.mul_apply] using this
  · have : univ.filter (fun v : (ZMod (7 ^ 1))ˣ =>
        χ (v : ZMod (7 ^ 1)) + χ ((-v : (ZMod (7 ^ 1))ˣ) : ZMod (7 ^ 1)) ≠ 0) = ∅ := by
      ext v
      simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_not]
      rw [Units.val_neg, neg_eq_neg_one_mul (v : ZMod (7 ^ 1)), map_mul, ho]; ring
    rw [this]; simp

/-- Negative control: Φ ≡ 1 satisfies the character hypothesis of (c) but NOT the conclusion,
and the support hypothesis fails (card = 6 = p − 1); so `hcard` cannot be dropped. -/
theorem lemmaN_c_control :
    (∀ ψ : DirichletCharacter ℂ (7 ^ 1), ψ.IsPrimitive → ψ (-1) = 1 →
      ∑ u : (ZMod (7 ^ 1))ˣ, ψ (u : ZMod (7 ^ 1)) * (fun _ => (1 : ℂ)) u = 0) ∧
    ¬ (∀ u : (ZMod (7 ^ 1))ˣ, (fun _ => (1 : ℂ)) u = -(fun _ => (1 : ℂ)) (-u)) := by
  refine ⟨fun ψ hψ _ => ?_, fun hall => ?_⟩
  · simp only [mul_one]; exact sum_units_eq_zero7 (ne_one_of_primitive7 hψ)
  · have := hall 1; norm_num at this

/-! ## Witness for (a) at p = 7, r = 2, ε = +1: Φ = δ₁ − δ₋₁ (support 2 points, |N| = 7). -/

theorem card_N_49 : (univ.filter (fun v : (ZMod (7 ^ 2))ˣ =>
    ZMod.unitsMap (pred_dvd 7 2) v = 1)).card = 7 := by
  haveI : NeZero (7 ^ (2 - 1)) := ⟨by norm_num⟩
  have h := Erdos634.LemmaSC.fiber_card (n := 7 ^ 2) (d := 7 ^ (2 - 1)) (pred_dvd 7 2)
  have ht1 : (7 ^ 2 : ℕ).totient = 42 := by
    rw [Nat.totient_prime_pow (by norm_num) (by norm_num)]; norm_num
  have ht2 : (7 ^ (2 - 1) : ℕ).totient = 6 := by
    rw [show 2 - 1 = 1 from rfl, pow_one, Nat.totient_prime (by norm_num)]
  rw [ht1, ht2] at h
  have : ((univ.filter (fun v : (ZMod (7 ^ 2))ˣ => ZMod.unitsMap (pred_dvd 7 2) v = 1)).card : ℂ)
      = ((7 : ℕ) : ℂ) := by rw [h]; norm_num
  exact_mod_cast this

theorem lemmaN_a_witness : ∃ Φ : (ZMod (7 ^ 2))ˣ → ℂ, Φ 1 ≠ 0 ∧
    (∀ ψ : DirichletCharacter ℂ (7 ^ 2), ψ.IsPrimitive → ψ (-1) = 1 →
      ∑ u : (ZMod (7 ^ 2))ˣ, ψ (u : ZMod (7 ^ 2)) * Φ u = 0) ∧
    (∀ u : (ZMod (7 ^ 2))ˣ,
      (univ.filter (fun v => ZMod.unitsMap (pred_dvd 7 2) v = ZMod.unitsMap (pred_dvd 7 2) u ∧
        (Φ v ≠ 0 ∨ Φ (-v) ≠ 0))).card
        < (univ.filter (fun v => ZMod.unitsMap (pred_dvd 7 2) v = 1)).card) := by
  have h1m : (1 : (ZMod (7 ^ 2))ˣ) ≠ -1 := by decide
  refine ⟨fun u => (if u = 1 then 1 else 0) - (if u = -1 then 1 else 0), ?_, ?_, ?_⟩
  · simp [h1m]
  · intro ψ _ hψ
    simp only [mul_sub, mul_ite, mul_one, mul_zero, sum_sub_distrib, sum_ite_eq', mem_univ,
      if_true, Units.val_one, Units.val_neg, MulChar.map_one, hψ, sub_self]
  · intro u
    rw [card_N_49]
    have hsub : univ.filter (fun v : (ZMod (7 ^ 2))ˣ =>
        ZMod.unitsMap (pred_dvd 7 2) v = ZMod.unitsMap (pred_dvd 7 2) u ∧
        (((if v = 1 then (1 : ℂ) else 0) - (if v = -1 then 1 else 0)) ≠ 0 ∨
         ((if -v = 1 then (1 : ℂ) else 0) - (if -v = -1 then 1 else 0)) ≠ 0))
        ⊆ {1, -1} := by
      intro v hv
      rw [mem_filter] at hv
      rw [mem_insert, mem_singleton]
      by_contra hne
      push Not at hne
      have h1 : -v ≠ 1 := fun h => hne.2 (by rw [← h, neg_neg])
      have h2 : -v ≠ -1 := fun h => hne.1 (neg_injective h)
      simp [hne.1, hne.2, h1, h2] at hv
    calc _ ≤ ({1, -1} : Finset (ZMod (7 ^ 2))ˣ).card := card_le_card hsub
      _ ≤ 2 := card_le_two
      _ < 7 := by norm_num

#print axioms Erdos634.LemmaSN.lemmaN_a_witness

end Erdos634.LemmaSN

#print axioms Erdos634.LemmaSN.isPrimitive_iff_not_factorsThrough
#print axioms Erdos634.LemmaSN.lemmaN
#print axioms Erdos634.LemmaSN.lemmaN_a
#print axioms Erdos634.LemmaSN.lemmaN_b
#print axioms Erdos634.LemmaSN.lemmaN_c
#print axioms Erdos634.LemmaSN.lemmaN_c_witness
#print axioms Erdos634.LemmaSN.lemmaN_c_control
