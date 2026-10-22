/-
# Lemma S, Lemma G for every r ≥ 1 (the r ≥ 2 case is new here; r = 1 is `LemmaSG`)

Source: (private working notes, not included) P2:

  **Lemma G** (p ≥ 7 prime; r ≥ 1; ε ∈ {±1}; g ∈ 𝒢). If ψ(g) takes one value over all primitive ψ
  with ψ(−1) = ε, then g = ±1.

(§3.2, r ≥ 2: summing over parity-ε characters minus those trivial on N.)  The Lean route for
r ≥ 2 is that sum identity at g and at 1, followed by a norm estimate (|c| = 1 forces
(p−1)·φ(p^{r−1}) ≤ 2·φ(p^{r−1}), impossible for p ≥ 7) — the paper's two sub-cases g ∉ ±N and
g ∈ ±N∖{±1} are merged into this single inequality.  r = 1 is reduced to `LemmaSG`'s
general-level statements (at prime level every nontrivial character is primitive).

Formalization debt only (Lemma S is PROVED at paper level); NOT /goal progress.
-/
import Mathlib
import Erdos634.Draft.LemmaSG
import Erdos634.Draft.LemmaSN

open scoped BigOperators
open Finset

namespace Erdos634.LemmaSG2

open Erdos634.LemmaSN (pred_dvd isPrimitive_iff_not_factorsThrough)

theorem changeLevel_neg_one {m n : ℕ} [NeZero n] (h : m ∣ n) (ψ : DirichletCharacter ℂ m) :
    DirichletCharacter.changeLevel h ψ (-1) = ψ (-1) := by
  have h1 := DirichletCharacter.changeLevel_eq_cast_of_dvd ψ h (-1)
  simp only [Units.val_neg, Units.val_one] at h1
  rw [h1, ZMod.cast_neg h, ZMod.cast_one h]

/-- **Lemma G, r ≥ 2.** -/
theorem lemmaG_pow {p r : ℕ} [hp : Fact p.Prime] (hp7 : 7 ≤ p) (hr : 2 ≤ r) {ε : ℂ}
    (hε : ε = 1 ∨ ε = -1) (g : (ZMod (p ^ r))ˣ) (c : ℂ)
    (hc : ∀ ψ : DirichletCharacter ℂ (p ^ r), ψ.IsPrimitive → ψ (-1) = ε →
      ψ (g : ZMod (p ^ r)) = c) :
    (g : ZMod (p ^ r)) = 1 ∨ (g : ZMod (p ^ r)) = -1 := by
  classical
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  haveI : NeZero (p ^ (r - 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hq'7 : 7 ≤ p ^ (r - 1) := le_trans hp7 (Nat.le_self_pow (by omega) p)
  have hq7 : 7 ≤ p ^ r := le_trans hp7 (Nat.le_self_pow (by omega) p)
  haveI : Fact (2 < p ^ (r - 1)) := ⟨by omega⟩
  haveI : Fact (2 < p ^ r) := ⟨by omega⟩
  have hm1 : (-1 : ZMod (p ^ r)) ≠ 1 := ZMod.neg_one_ne_one
  have hm1' : (-1 : ZMod (p ^ (r - 1))) ≠ 1 := ZMod.neg_one_ne_one
  have hd := pred_dvd p r
  -- totient relation φ(p^r) = p·φ(p^(r−1))
  have htot : (p ^ r).totient = p * (p ^ (r - 1)).totient := by
    rw [show p ^ r = p * p ^ (r - 1) by rw [← pow_succ']; congr 1; omega]
    exact Nat.totient_mul_of_prime_of_dvd hp.out (dvd_pow_self p (by omega))
  have hT0 : 0 < (p ^ (r - 1)).totient := Nat.totient_pos.2 (by positivity)
  by_contra hne
  push Not at hne
  set X := univ.filter (fun ψ : DirichletCharacter ℂ (p ^ r) => ψ (-1) = ε) with hX
  set X' := univ.filter (fun ψ : DirichletCharacter ℂ (p ^ (r - 1)) => ψ (-1) = ε) with hX'
  set Xp := X.filter (fun ψ => ψ.IsPrimitive) with hXp
  have hsplit : ∀ F : DirichletCharacter ℂ (p ^ r) → ℂ,
      ∑ ψ ∈ X, F ψ = ∑ ψ ∈ Xp, F ψ + ∑ ψ' ∈ X', F (DirichletCharacter.changeLevel hd ψ') := by
    intro F
    rw [← sum_filter_add_sum_filter_not X (fun ψ => ψ.IsPrimitive) F]
    congr 1
    have hY : X.filter (fun ψ => ¬ ψ.IsPrimitive)
        = X'.map ⟨DirichletCharacter.changeLevel hd, DirichletCharacter.changeLevel_injective hd⟩ := by
      ext ψ
      simp only [hX, hX', mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨hpar, hnp⟩
        have hf : ψ.FactorsThrough (p ^ (r - 1)) :=
          not_not.1 (fun h' => hnp ((isPrimitive_iff_not_factorsThrough (by omega) ψ).2 h'))
        have heq := hf.eq_changeLevel
        refine ⟨hf.χ₀, ?_, heq.symm⟩
        rw [← changeLevel_neg_one hd, ← heq]; exact hpar
      · rintro ⟨ψ', hpar, rfl⟩
        refine ⟨by rw [changeLevel_neg_one]; exact hpar, fun hprim => ?_⟩
        exact (isPrimitive_iff_not_factorsThrough (by omega) _).1 hprim ⟨hd, ψ', rfl⟩
    rw [hY, sum_map]
    rfl
  have hval : ∀ (ψ' : DirichletCharacter ℂ (p ^ (r - 1))) (u : (ZMod (p ^ r))ˣ),
      DirichletCharacter.changeLevel hd ψ' (u : ZMod (p ^ r))
        = ψ' ((ZMod.unitsMap hd u : (ZMod (p ^ (r - 1)))ˣ) : ZMod (p ^ (r - 1))) := by
    intro ψ' u
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, ZMod.unitsMap_val]
  have hXpval : ∀ u : (ZMod (p ^ r))ˣ, (∀ ψ ∈ Xp, ψ (u : ZMod (p ^ r)) = c) →
      ∑ ψ ∈ Xp, 2 * ψ (u : ZMod (p ^ r)) = 2 * (Xp.card : ℂ) * c := by
    intro u hu
    rw [sum_congr rfl (fun ψ hψ => by rw [hu ψ hψ]), sum_const, nsmul_eq_mul]; ring
  have hcXp : ∀ ψ ∈ Xp, ψ (g : ZMod (p ^ r)) = c := by
    intro ψ hψ
    obtain ⟨h1, h2⟩ := mem_filter.1 hψ
    exact hc ψ h2 (mem_filter.1 h1).2
  -- the identity at 1
  have hP1 := Erdos634.LemmaSG.parity_sum ε hε (1 : ZMod (p ^ r))
  rw [DirichletCharacter.sum_characters_eq ℂ, DirichletCharacter.sum_characters_eq ℂ, if_pos rfl,
    if_neg hm1, mul_zero, add_zero] at hP1
  rw [← hX, hsplit (fun ψ => 2 * ψ 1)] at hP1
  simp only [MulChar.map_one, mul_one, sum_const, nsmul_eq_mul] at hP1
  have hP1' := Erdos634.LemmaSG.parity_sum ε hε (1 : ZMod (p ^ (r - 1)))
  rw [DirichletCharacter.sum_characters_eq ℂ, DirichletCharacter.sum_characters_eq ℂ, if_pos rfl,
    if_neg hm1', mul_zero, add_zero] at hP1'
  rw [← hX'] at hP1'
  simp only [MulChar.map_one, mul_one, sum_const, nsmul_eq_mul] at hP1'
  -- 2|Xp| + φ(p^(r−1)) = φ(p^r)  (in ℕ)
  have hcount : 2 * Xp.card + (p ^ (r - 1)).totient = (p ^ r).totient := by
    have : ((2 * Xp.card + (p ^ (r - 1)).totient : ℕ) : ℂ) = ((p ^ r).totient : ℂ) := by
      push_cast; rw [← hP1, ← hP1']; ring
    exact_mod_cast this
  -- the identity at g
  have hPg := Erdos634.LemmaSG.parity_sum ε hε (g : ZMod (p ^ r))
  rw [DirichletCharacter.sum_characters_eq ℂ, DirichletCharacter.sum_characters_eq ℂ, if_neg hne.1,
    if_neg (fun h => hne.2 (by rw [← neg_neg (g : ZMod (p ^ r)), h])), mul_zero, add_zero] at hPg
  rw [← hX, hsplit (fun ψ => 2 * ψ (g : ZMod (p ^ r))), hXpval g hcXp] at hPg
  simp only [hval] at hPg
  set gb : ZMod (p ^ (r - 1)) := ((ZMod.unitsMap hd g : (ZMod (p ^ (r - 1)))ˣ) : ZMod (p ^ (r - 1)))
  have hPg' := Erdos634.LemmaSG.parity_sum ε hε gb
  rw [← hX'] at hPg'
  rw [hPg', DirichletCharacter.sum_characters_eq ℂ, DirichletCharacter.sum_characters_eq ℂ] at hPg
  -- norms
  have hXpos : 0 < Xp.card := by
    have : 0 < 2 * Xp.card := by
      have h2 := htot; nlinarith [hcount, hT0, hp7]
    omega
  obtain ⟨ψ0, hψ0⟩ := card_pos.1 hXpos
  have hcn : ‖c‖ = 1 := by rw [← hcXp ψ0 hψ0]; exact ψ0.unit_norm_eq_one g
  have hεn : ‖ε‖ = 1 := by rcases hε with rfl | rfl <;> simp
  have hind : ∀ x : ZMod (p ^ (r - 1)),
      ‖(if x = 1 then (((p ^ (r - 1)).totient : ℕ) : ℂ) else 0)‖ ≤ (p ^ (r - 1)).totient := by
    intro x; split_ifs <;> simp
  have hnorm : ((2 * Xp.card : ℕ) : ℝ) ≤ 2 * (p ^ (r - 1)).totient := by
    have heq : 2 * (Xp.card : ℂ) * c = -((if gb = 1 then (((p ^ (r - 1)).totient : ℕ) : ℂ) else 0)
        + ε * (if -gb = 1 then (((p ^ (r - 1)).totient : ℕ) : ℂ) else 0)) := by
      linear_combination hPg
    have := congrArg norm heq
    rw [norm_neg, norm_mul, norm_mul, hcn, mul_one] at this
    have hle := norm_add_le (if gb = 1 then (((p ^ (r - 1)).totient : ℕ) : ℂ) else 0)
      (ε * (if -gb = 1 then (((p ^ (r - 1)).totient : ℕ) : ℂ) else 0))
    rw [norm_mul, hεn, one_mul] at hle
    have h1 := hind gb
    have h2 := hind (-gb)
    push_cast
    have : ‖(2 : ℂ)‖ * ‖(Xp.card : ℂ)‖ = 2 * (Xp.card : ℝ) := by simp
    linarith
  have hnat : 2 * Xp.card ≤ 2 * (p ^ (r - 1)).totient := by exact_mod_cast hnorm
  -- (p − 1)·T ≤ 2·T with T > 0 forces p ≤ 3
  have : p * (p ^ (r - 1)).totient ≤ 3 * (p ^ (r - 1)).totient := by rw [← htot]; omega
  have := Nat.le_of_mul_le_mul_right this hT0
  omega

/-- At a prime level every nontrivial character is primitive. -/
theorem isPrimitive_of_ne_one {p : ℕ} [hp : Fact p.Prime] {ψ : DirichletCharacter ℂ (p ^ 1)}
    (h : ψ ≠ 1) : ψ.IsPrimitive := by
  refine (isPrimitive_iff_not_factorsThrough le_rfl ψ).2 (fun hf => h ?_)
  haveI : NeZero (p ^ 1) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  exact (DirichletCharacter.factorsThrough_one_iff ψ).1 hf

/-- **Lemma G** (all r ≥ 1), exactly as in P2. -/
theorem lemmaG {p r : ℕ} [hp : Fact p.Prime] (hp7 : 7 ≤ p) (hr : 1 ≤ r) {ε : ℂ}
    (hε : ε = 1 ∨ ε = -1) (g : (ZMod (p ^ r))ˣ) (c : ℂ)
    (hc : ∀ ψ : DirichletCharacter ℂ (p ^ r), ψ.IsPrimitive → ψ (-1) = ε →
      ψ (g : ZMod (p ^ r)) = c) :
    (g : ZMod (p ^ r)) = 1 ∨ (g : ZMod (p ^ r)) = -1 := by
  rcases Nat.lt_or_ge r 2 with h | h
  · obtain rfl : r = 1 := by omega
    haveI : NeZero (p ^ 1) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    haveI : Fact (2 < p ^ 1) := ⟨by rw [pow_one]; omega⟩
    have hm1 : (-1 : ZMod (p ^ 1)) ≠ 1 := ZMod.neg_one_ne_one
    rcases hε with rfl | rfl
    · refine Erdos634.LemmaSG.lemmaG_even_general hm1 ?_ g.isUnit c
        (fun χ he hne => hc χ (isPrimitive_of_ne_one hne) he)
      rw [pow_one, Nat.totient_prime hp.out]; omega
    · exact Erdos634.LemmaSG.lemmaG_odd_general hm1 g.isUnit c
        (fun χ ho => hc χ (isPrimitive_of_ne_one (Erdos634.LemmaSB1.ne_one_of_odd ho)) ho)
  · exact lemmaG_pow hp7 h hε g c hc

/-! ## Witness and control -/

/-- Witness (r = 2, p = 7): the hypothesis bundle of `lemmaG` is satisfiable (at g = 1 every ψ
takes the value c = 1), so the statement is not vacuous; the p = 5 failure of the r = 1 case is
`LemmaSG.control_p5`. -/
theorem lemmaG_witness : ∀ ψ : DirichletCharacter ℂ (7 ^ 2), ψ.IsPrimitive → ψ (-1) = 1 →
    ψ ((1 : (ZMod (7 ^ 2))ˣ) : ZMod (7 ^ 2)) = 1 := by
  intro ψ _ _; simp

end Erdos634.LemmaSG2

#print axioms Erdos634.LemmaSG2.lemmaG_pow
#print axioms Erdos634.LemmaSG2.lemmaG
