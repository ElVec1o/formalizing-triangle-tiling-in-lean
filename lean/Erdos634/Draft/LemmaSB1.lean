-- Draft/LemmaSB1.lean — CASE A, node A5 (Lemma S), blocker **B1**: B_{1,χ} ≠ 0 for odd primitive χ.
-- ((private working notes, not included) §3.1 "Consequence": "For odd primitive χ*,
--  B_{1,χ̄*} ≠ 0, because it is a nonzero multiple of L(1, χ*) (Dirichlet).")
--
-- What is proved here, unconditionally (Mathlib only, no sorry):
--   * `gaussSum_ne_zero`        : τ(χ) ≠ 0 for primitive χ (via Fourier inversion `ZMod.dft_dft`).
--   * `LFunction_zero_ne_zero`  : L(0, χ) ≠ 0 for odd primitive χ (functional equation
--                                 `IsPrimitive.completedLFunction_one_sub` at s = 1, Γℝ(1) = 1,
--                                 Γℝ(2) ≠ 0, and Mathlib's `LFunction_apply_one_ne_zero` for χ⁻¹).
--   * `LFunction_zero_eq`       : L(0, χ) = Σ_j χ(j) · hurwitzZetaOdd (j/N) 0.
-- What is proved CONDITIONALLY:
--   * `B1_of_hurwitzOddZero`    : Σ_j χ(j)·((j/N)) ≠ 0, assuming `HurwitzOddZero`, i.e.
--       hurwitzZetaOdd x 0 = 1/2 − x   for 0 < x < 1.
--     This is the k = 0 case of Mathlib's `HurwitzZeta.hurwitzZeta_neg_nat`, which Mathlib states
--     only for k ≠ 0 and marks "TODO: This formula is also correct for k = 0; but our current proof
--     does not work in this case." (HurwitzZetaValues.lean).  It is TRUE (classical), NOT in Mathlib,
--     and NOT proved in this file (the conditional is superseded since 2026-10-01: Draft/LemmaSB1Hurwitz.lean,
--     imported into All.lean, proves `hurwitzOddZero` with no hypothesis; note added 2026-10-03); it is proved in Draft/LemmaSB1Hurwitz.lean (`hurwitzOddZero`).
--
-- Formalization debt on a paper-level PROVED node; NOT progress on the three /goal outcomes.
-- Reuses `Erdos634.LemmaS.saw` from Draft/CaseACorF.lean (not redefined).  Imported into All.lean (All.lean:637).
import Mathlib
import Erdos634.Draft.CaseACorF

open scoped BigOperators
open Complex DirichletCharacter HurwitzZeta

namespace Erdos634.LemmaSB1

variable {N : ℕ} [NeZero N]

/-- Gauss sums of primitive characters are nonzero. -/
theorem gaussSum_ne_zero {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    gaussSum χ ZMod.stdAddChar ≠ 0 := by
  intro h
  have h0 : ZMod.dft (χ : ZMod N → ℂ) = 0 := funext fun k => by
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum, h, mul_zero]; rfl
  have := congr_fun (ZMod.dft_dft (χ : ZMod N → ℂ)) (-1)
  rw [h0, map_zero, neg_neg, MulChar.map_one] at this
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  simp only [Pi.zero_apply, smul_eq_mul, mul_one] at this
  exact hN this.symm

/-- An odd character has level ≠ 1. -/
theorem level_ne_one_of_odd {χ : DirichletCharacter ℂ N} (ho : χ.Odd) : N ≠ 1 := by
  rintro rfl
  have h1 : (-1 : ZMod 1) = 1 := Subsingleton.elim _ _
  have : χ (-1) = -1 := ho
  rw [h1, MulChar.map_one] at this
  norm_num at this

theorem ne_one_of_odd {χ : DirichletCharacter ℂ N} (ho : χ.Odd) : χ ≠ 1 := by
  rintro rfl
  have : (1 : DirichletCharacter ℂ N) (-1) = -1 := ho
  rw [MulChar.one_apply (isUnit_one.neg)] at this
  norm_num at this

theorem inv_odd {χ : DirichletCharacter ℂ N} (ho : χ.Odd) : χ⁻¹.Odd := by
  show χ⁻¹ (-1) = -1
  rw [MulChar.inv_apply_eq_inv', ho]; norm_num

/-- **L(0, χ) ≠ 0 for odd primitive χ** (unconditional). -/
theorem LFunction_zero_ne_zero {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) (ho : χ.Odd) :
    LFunction χ 0 ≠ 0 := by
  have hN := level_ne_one_of_odd ho
  rw [LFunction_eq_completed_div_gammaFactor χ 0 (Or.inr hN), ho.gammaFactor_def, zero_add,
    Gammaℝ_one, div_one]
  have hfe := hp.completedLFunction_one_sub 1
  rw [sub_self] at hfe
  rw [hfe]
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hcp : ∀ w : ℂ, (N : ℂ) ^ w ≠ 0 := fun w => by
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  refine mul_ne_zero (mul_ne_zero (hcp _) ?_) ?_
  · unfold rootNumber
    exact div_ne_zero (div_ne_zero (gaussSum_ne_zero hp) (pow_ne_zero _ I_ne_zero)) (hcp _)
  · intro h0
    have hL := LFunction_eq_completed_div_gammaFactor χ⁻¹ 1 (Or.inl one_ne_zero)
    rw [(inv_odd ho).gammaFactor_def, h0, zero_div] at hL
    exact LFunction_apply_one_ne_zero (inv_ne_one.mpr (ne_one_of_odd ho)) hL

/-- L(0, χ) as a finite sum of odd Hurwitz zeta values at 0. -/
theorem LFunction_zero_eq {χ : DirichletCharacter ℂ N} (ho : χ.Odd) :
    LFunction χ 0 = ∑ j : ZMod N, χ j * hurwitzZetaOdd (ZMod.toAddCircle j) 0 := by
  have := ZMod.LFunction_def_odd ho.to_fun 0
  rw [neg_zero, cpow_zero, one_mul] at this
  exact this

/-- The missing Mathlib fact (k = 0 case of `hurwitzZeta_neg_nat`, a Mathlib TODO):
`hurwitzZetaOdd x 0 = 1/2 − x` for `0 < x < 1`. TRUE classically; not proved in THIS file — it is proved
in `Draft/LemmaSB1Hurwitz.lean` as `hurwitzOddZero` (updated 2026-10-01). -/
def HurwitzOddZero : Prop :=
  ∀ x : ℝ, 0 < x → x < 1 → hurwitzZetaOdd (x : UnitAddCircle) 0 = 1 / 2 - (x : ℂ)

theorem saw_val {j : ZMod N} (hj : j ≠ 0) :
    ((Erdos634.LemmaS.saw ((j.val : ℚ) / N) : ℚ) : ℂ) = (j.val : ℂ) / N - 1 / 2 := by
  have hv : j.val ≠ 0 := (ZMod.val_ne_zero j).mpr hj
  have hlt : j.val < N := ZMod.val_lt j
  have hNq : (0 : ℚ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hf : Int.fract ((j.val : ℚ) / N) = (j.val : ℚ) / N := by
    rw [Int.fract_eq_self]
    exact ⟨by positivity, (div_lt_one hNq).mpr (by exact_mod_cast hlt)⟩
  have hne : (j.val : ℚ) / N ≠ 0 := div_ne_zero (by exact_mod_cast hv) hNq.ne'
  unfold Erdos634.LemmaS.saw
  rw [hf, if_neg hne]
  push_cast; ring

/-- **B1, conditional on `HurwitzOddZero`**: for χ odd primitive mod N,
`Σ_{j mod N} χ(j)·((j/N)) ≠ 0` (this sum is B_{1,χ}). -/
theorem B1_of_hurwitzOddZero (H : HurwitzOddZero) {χ : DirichletCharacter ℂ N}
    (hp : χ.IsPrimitive) (ho : χ.Odd) :
    ∑ j : ZMod N, χ j * ((Erdos634.LemmaS.saw ((j.val : ℚ) / N) : ℚ) : ℂ) ≠ 0 := by
  have hN := level_ne_one_of_odd ho
  have key : ∀ j : ZMod N, χ j * hurwitzZetaOdd (ZMod.toAddCircle j) 0 =
      -(χ j * ((Erdos634.LemmaS.saw ((j.val : ℚ) / N) : ℚ) : ℂ)) := by
    intro j
    by_cases hj : j = 0
    · subst hj; rw [χ.map_zero' hN]; simp
    · have hv : j.val ≠ 0 := (ZMod.val_ne_zero j).mpr hj
      have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
      rw [ZMod.toAddCircle_apply, H _ (by positivity)
        ((div_lt_one hNr).mpr (by exact_mod_cast ZMod.val_lt j)), saw_val hj]
      push_cast; ring
  intro hsum
  apply LFunction_zero_ne_zero hp ho
  rw [LFunction_zero_eq ho, Finset.sum_congr rfl (fun j _ => key j), Finset.sum_neg_distrib, hsum,
    neg_zero]

/-! ## Witnesses: every hypothesis except `HurwitzOddZero` is satisfiable. -/

/-- Nontrivial characters of prime level are primitive. -/
theorem isPrimitive_of_prime {p : ℕ} [NeZero p] (hp : p.Prime) {χ : DirichletCharacter ℂ p}
    (h : χ ≠ 1) : χ.IsPrimitive := by
  rw [isPrimitive_def]
  rcases hp.eq_one_or_self_of_dvd _ (conductor_dvd_level χ) with h1 | h1
  · exact absurd (eq_one_iff_conductor_eq_one.mpr h1) h
  · exact h1

/-- Witness: an odd primitive character mod 3 exists. -/
theorem exists_odd_primitive_mod3 : ∃ χ : DirichletCharacter ℂ 3, χ.IsPrimitive ∧ χ.Odd := by
  have hne : (-1 : ZMod 3) ≠ 1 := by decide
  obtain ⟨χ, hχ⟩ := exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ hne
  have hsq : χ (-1) * χ (-1) = 1 := by rw [← map_mul]; norm_num
  have hodd : χ (-1) = -1 := by
    have : (χ (-1) - 1) * (χ (-1) + 1) = 0 := by ring_nf; rw [sq, hsq]; ring
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) hχ
    · exact eq_neg_of_add_eq_zero_left h
  exact ⟨χ, isPrimitive_of_prime Nat.prime_three (ne_one_of_odd hodd), hodd⟩

/-- Joint witness: the unconditional conclusion fires on a real character. -/
theorem witness_L0_mod3 : ∃ χ : DirichletCharacter ℂ 3, LFunction χ 0 ≠ 0 := by
  obtain ⟨χ, hp, ho⟩ := exists_odd_primitive_mod3
  exact ⟨χ, LFunction_zero_ne_zero hp ho⟩

end Erdos634.LemmaSB1

#print axioms Erdos634.LemmaSB1.LFunction_zero_ne_zero
#print axioms Erdos634.LemmaSB1.B1_of_hurwitzOddZero
#print axioms Erdos634.LemmaSB1.witness_L0_mod3
