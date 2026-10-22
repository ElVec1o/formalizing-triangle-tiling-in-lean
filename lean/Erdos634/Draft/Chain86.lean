/-
Draft/Chain86.lean — the honest conditional chain for the composite N = 86 = 2·43 (squarefree, 86 % 4 = 2).
UNAUDITED.  *** NOT a proof that 86 is not a tile count: `chain_eightysix` is conditional on FOUR named residual
hypotheses (below).  *** Formalization debt, NOT /goal progress.  No `sorry`, no `native_decide`.

Discharged at 86 by existing Lean (each cited leaf is actually applied):
  S1 (β,β,3α)       `ScaleBaseBetaQNR.scaleBaseBeta_qnr`, ℓ = 43 (v₄₃(86) = 1, 3 a non-residue mod 43)
  S2 (2α,α,2β)      `RMinus4QNR.rMinus4_qnr`, ℓ = 43 (2 and 3 non-residues mod 43)
  S3 (α,α,α+2β)     `Row11IsoQ.excluded_isoQ_any_label`, `IsoQDvd 86` (decide)
  S4, S5            `RWSquarefree.rwStatement_sqfree`, `RASquarefree.raStatement_sqfree` (Squarefree 86) → I6
                    (`BaseBetaFullUnc.basebeta_full_unc` via `not_baseBetaTiled`)
  IsoTP             `ThmIsoH9.thmIso_H9`, `IsoH9 86` (the only candidate a+2b = 43 has no integer c)
  π/3 tile          `LemmaPProof.lemmaP_general` + `Row5.theoremE_sixty` parity (m₁m₂ = 114, both even)
  2π/3 equilateral  `Row5.theoremE_twoPiThree` parity (st = 114, both even)
  F1/F1′            `Paper.cor_int` + `Row7.lemmaW_*` + `F1_product_real` parity (MαMβ = ±86, both even)
  γ = 2α            `Row4.not_two_mod_four` (R4(iii))
  Case-C split      `LemmaCFinal.lemmaC_general`;  Case A uses `LemmaSAll.lemmaS` as its premise
NOT discharged (named hypotheses, see (private working notes, not included)):
  GapAcomp 86   Case A at composite N                     (Lean: Lemma S only)
  HBSimilar 86  similar-tile N-form: N a sum of two squares  [cited BeesonI/SWW]
  H1Right 86    right-tile N-form: N/2 a sum of two squares  [cited BeesonI Thm 4(v)]
  GapR8 86      2π/3 tile with F2-F4′ targets (min N0 = 88/143/264, so N < 88 dies)  [paper-level]
-/
import Erdos634.Draft.ChainComposite

open scoped Classical

namespace Erdos634.Draft.Chain86

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite

theorem sqfree_86 : Squarefree (86 : ℕ) := by decide +kernel

theorem qnr2_43 : ∀ x : ZMod 43, x ^ 2 ≠ 2 := by decide
theorem qnr3_43 : ∀ x : ZMod 43, x ^ 2 ≠ 3 := by decide

theorem val43_86 : Odd (padicValNat 43 86) := by
  haveI : Fact (Nat.Prime 43) := ⟨by norm_num⟩
  have : padicValNat 43 86 = 1 := by
    have h : padicValNat 43 86 = padicValNat 43 (43 * 2) := by norm_num
    rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat_self,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  rw [this]; exact odd_one

theorem IsoQDvd_86 : IsoQDvd 86 := by
  intro e d he hd _ hdvd
  have hle : e ^ 2 + 4 * e * d + 2 * d ^ 2 ≤ 86 := Nat.le_of_dvd (by norm_num) hdvd
  have he6 : e ≤ 9 := by nlinarith
  have hd4 : d ≤ 6 := by nlinarith
  interval_cases e <;> interval_cases d <;> simp_all <;> omega

theorem IsoH9_86 : IsoH9 86 := by
  intro a b c ha hb hc hcc h3 hdvd
  obtain ⟨k, hk⟩ := hdvd
  have hk' : (86 : ℤ) = (a + 2 * b) * k := by exact_mod_cast hk
  have hpos : 0 < a + 2 * b := by linarith
  have hk1 : 0 < k := by
    by_contra h; push Not at h
    nlinarith [mul_nonneg hpos.le (neg_nonneg.mpr h)]
  have hk12 : k ≤ 28 := by
    by_contra h; push Not at h
    have h13 : (29 : ℤ) ≤ k := by omega
    nlinarith [mul_le_mul h3 h13 (by norm_num) hpos.le]
  interval_cases k <;> try omega
  -- k = 2 : a + 2b = 43
  exfalso
  have hb9 : b ≤ 21 := by omega
  have ha' : a = 43 - 2 * b := by omega
  subst ha'
  have hc20 : c ≤ 43 := by nlinarith
  interval_cases b <;> interval_cases c <;> omega

theorem not_sumsq_86 : ¬ ∃ x y : ℕ, 86 = x ^ 2 + y ^ 2 := by
  rintro ⟨x, y, h⟩
  have hx : x ≤ 9 := by nlinarith
  have hy : y ≤ 9 := by nlinarith
  interval_cases x <;> interval_cases y <;> omega

theorem not_sumsq_half_86 : ¬ ∃ x y : ℕ, 86 = 2 * (x ^ 2 + y ^ 2) := by
  rintro ⟨x, y, h⟩
  have hx : x ≤ 6 := by nlinarith
  have hy : y ≤ 6 := by nlinarith
  interval_cases x <;> interval_cases y <;> omega

/-- Non-vacuity controls for the cited N-forms: the conclusions are TRUE at N where real tilings exist
(N = 10: `10 = 2(1²+2²)`; N = 5, `5 = 1²+2²`), so `HBSimilar`/`H1Right` are not unsatisfiable-by-form. -/
theorem H1_form_ten : ∃ x y : ℕ, 10 = 2 * (x ^ 2 + y ^ 2) := ⟨1, 2, by norm_num⟩
theorem HB_form_five : ∃ x y : ℕ, 5 = x ^ 2 + y ^ 2 := ⟨1, 2, by norm_num⟩

/-- **N = 86 modulo four named hypotheses.** -/
theorem chain_eightysix (gA : GapAcomp 86) (gB : HBSimilar 86) (gR : H1Right 86) (gR8 : GapR8 86)
    (D : CongruentDissection 86) : False :=
  chain_conditional_gen 86 sqfree_86 43 (by norm_num) val43_86 qnr2_43 qnr3_43 IsoQDvd_86 IsoH9_86
    gA (caseB_of_sumsq 86 gB not_sumsq_86) (caseR_of_H1 86 gR not_sumsq_half_86)
    (caseG_of_mod4_two 86 (by norm_num)) (gapE60_of_mod4_two 86 (by norm_num))
    (gapE120_of_mod4_two 86 (by norm_num)) (gapF1_of_mod4_two 86 (by norm_num)) gR8 D

end Erdos634.Draft.Chain86

#print axioms Erdos634.Draft.Chain86.chain_eightysix
