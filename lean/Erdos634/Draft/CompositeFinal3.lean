/-
Draft/CompositeFinal3.lean — the 38/86/14/42/62/70 chain re-done for N = 22, 46, 66, 78 (squarefree, N ≡ 2 mod 4), the four
N at which `IsoH9 N` is FALSE (proper-divisor 120° candidates), using `ThmIsoH9b.thmIso_H9b` / `CompositeIsoB`.
*** CONDITIONAL theorems, NOT exclusions of 22/46/66/78.  UNAUDITED.  Formalization debt, NOT /goal progress. ***
No sorry, no native_decide (`decide +kernel` on closed finite statements only).

Residual named hypotheses of each `chain_N_final` (everything else is proved from existing Lean):
  22 : H1Right 22, S2Closed 22
  46 : H1Right 46
  66 : H1Right 66, S1Closed 66, GapR8 66
  78 : H1Right 78, GapR8F23 78                       (F4, F4' shapes of GapR8 proved via NoF4 78; F2, F3, F3' need 3 ∤ N)
Why: see (private working notes, not included)
-/
import Erdos634.Draft.CompositeFinal2
import Erdos634.Draft.CompositeS1Arith
import Erdos634.Draft.CompositeS2Mod27
import Erdos634.Draft.CompositeIsoB

open scoped Classical

set_option synthInstance.maxSize 1000
set_option synthInstance.maxHeartbeats 400000

namespace Erdos634.Draft.CompositeFinal3

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.CompositeS1Arith Erdos634.Draft.CompositeIsoB Erdos634.Draft.CompositeFinal2
open Erdos634.Geometry.CaseA.LemmaH (HArith harith_of_bound)

/-- The dispatch of `chain_conditional_gen` with S1, S2, S3 abstracted and `IsoH9 N` replaced by `IsoH9b N`. -/
theorem chain_gen3 (N : ℕ)
    (hsq : Squarefree N)
    (gS1 : S1Closed N) (gS2 : S2Closed N) (gS3 : S3Closed N) (hH : IsoH9b N)
    (gA : GapAcomp N) (gB : CaseBClosed N) (gR : CaseRClosed N) (gG : CaseGClosed N)
    (gE60 : GapE60 N) (gE120 : GapE120 N) (gF1 : GapF1 N) (gR8 : GapR8 N)
    (D : CongruentDissection N) : False := by
  -- Case A (Lemma S is proved, N-free, and supplied)
  by_cases hA : ∀ k, ∃ q : ℚ, D.model.angleAt k = q * Real.pi
  · exact gA Erdos634.LemmaSAll.lemmaS D hA
  have hirr : ∃ k, IrrPi (D.model.angleAt k) := by
    by_contra hc
    exact hA fun k => by_contra fun hk => hc ⟨k, hk⟩
  -- Case B
  by_cases hB : SimilarTM D
  · obtain ⟨μ, τ, hs⟩ := hB
    exact gB D μ τ hs
  -- Case C
  rcases Erdos634.Draft.LemmaCFinal.lemmaC_general D hirr hB with hR | hT | hS | hTP | h32
  · exact gR D hR
  · obtain ⟨α, a, b, c, hα, hd, i, j, hij, hi, hj⟩ := hT
    exact gG D α a b c hα hd i j hij hi hj
  · obtain ⟨α, a, b, c, hα, hd⟩ := hS
    exact gE60 D α a b c hα hd (Erdos634.Draft.LemmaPProof.lemmaP_general D α a b c hα hd hB)
  · obtain ⟨α, a, b, c, hα, hd, hsh⟩ := hTP
    rcases hsh with he | hi | hf | hr
    · exact gE120 D α a b c hα hd he
    · exact Erdos634.Draft.ThmIsoH9b.thmIso_H9b N D hH α a b c hα hd hi
    · exact gF1 D α a b c hα hd hf
    · exact gR8 D α a b c hα hd hr
  · obtain ⟨α, β, a, b, c, hα, hrel, hd, hsh⟩ := h32
    obtain ⟨σ, m0, o0, m1, o1, m2, o2⟩ := id hd
    have s01 : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
    have s20 : σ 2 ≠ σ 0 := σ.injective.ne (by decide)
    have s21 : σ 2 ≠ σ 1 := σ.injective.ne (by decide)
    rcases hsh with ⟨τ, t0, t1, t2⟩ | ⟨τ, t0, t1, t2⟩ | ⟨τ, t0, t1, t2⟩ | ⟨τ, t0, t1, t2⟩ |
        ⟨τ, t0, t1, t2⟩
    · obtain ⟨r, hr, hb⟩ := Row12.rational_any_label D hα hrel hd
        (τ.injective.ne (by decide : (0 : Fin 3) ≠ 1)) t0 t1
      exact gS1 D α β a b c r hα hrel hd hr hb ⟨τ, t0, t1, t2⟩
    · obtain ⟨r, hr, hb⟩ := Row13.rational_any_label D hα hrel hd
        (τ.injective.ne (by decide : (0 : Fin 3) ≠ 1)) t0 t1
      exact not_baseBetaTiled (Erdos634.Draft.RASquarefree.raStatement_sqfree N D hsq α β a b c r hα hrel hd hr hb
        ⟨τ, t0, t1, t2⟩)
    · obtain ⟨r, hr⟩ := Row14.rational_any_label D α β hα hrel s01 s20 s21 m0 m1
        (τ.injective.ne (by decide : (0 : Fin 3) ≠ 1)) t0 t1
      rw [o0, o2] at hr
      exact not_baseBetaTiled (Erdos634.Draft.RWSquarefree.rwStatement_sqfree N D hsq α β a b c r hα hrel hd hr
        (Rows11_13AnyLabel.b_of_rational hrel hd hr) ⟨τ, t0, t1, t2⟩)
    · obtain ⟨r, hr, -⟩ := Row15.rational_any_label D α β hα hrel s01 s20 s21 m0 m1
        (τ.injective.ne (by decide : (0 : Fin 3) ≠ 1)) t0 t1
      rw [o0, o2] at hr
      exact gS2 D α β a b c r hα hrel hd hr
        (Rows11_13AnyLabel.b_of_rational hrel hd hr) ⟨τ, t0, t1, t2⟩
    · exact gS3 D α β a b c hα hrel hd (τ 0) (τ 1)
        (τ.injective.ne (by decide : (0 : Fin 3) ≠ 1)) t0 t1


/-! ## Arithmetic leaves -/

theorem sqfree_22 : Squarefree (22 : ℕ) := by decide +kernel
theorem sqfree_46 : Squarefree (46 : ℕ) := by decide +kernel
theorem sqfree_66 : Squarefree (66 : ℕ) := by decide +kernel
theorem sqfree_78 : Squarefree (78 : ℕ) := by decide +kernel

theorem hari22 : HArith 22 := harith_of_bound (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem hari46 : HArith 46 := harith_of_bound (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem hari66 : HArith 66 := harith_of_bound (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem hari78 : HArith 78 := harith_of_bound (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem nsq22 : ¬ ∃ x y : ℕ, 22 = x ^ 2 + y ^ 2 := nsq 22 (by norm_num) (by decide)
theorem nsq46 : ¬ ∃ x y : ℕ, 46 = x ^ 2 + y ^ 2 := nsq 46 (by norm_num) (by decide)
theorem nsq66 : ¬ ∃ x y : ℕ, 66 = x ^ 2 + y ^ 2 := nsq 66 (by norm_num) (by decide)
theorem nsq78 : ¬ ∃ x y : ℕ, 78 = x ^ 2 + y ^ 2 := nsq 78 (by norm_num) (by decide)
theorem nsqh22 : ¬ ∃ x y : ℕ, 22 = 2 * (x ^ 2 + y ^ 2) := nsq_half 22 (by norm_num) (by decide)
theorem nsqh46 : ¬ ∃ x y : ℕ, 46 = 2 * (x ^ 2 + y ^ 2) := nsq_half 46 (by norm_num) (by decide)
theorem nsqh66 : ¬ ∃ x y : ℕ, 66 = 2 * (x ^ 2 + y ^ 2) := nsq_half 66 (by norm_num) (by decide)
theorem nsqh78 : ¬ ∃ x y : ℕ, 78 = 2 * (x ^ 2 + y ^ 2) := nsq_half 78 (by norm_num) (by decide)

theorem isoQRef_22 : IsoQRef 22 := isoQRef_of_check 22 (by norm_num) (by norm_num) (by decide +kernel)
theorem isoQRef_46 : IsoQRef 46 := isoQRef_of_check 46 (by norm_num) (by norm_num) (by decide +kernel)
theorem isoQRef_66 : IsoQRef 66 := isoQRef_of_check 66 (by norm_num) (by norm_num) (by decide +kernel)
theorem isoQRef_78 : IsoQRef 78 := isoQRef_of_check 78 (by norm_num) (by norm_num) (by decide +kernel)

theorem noF4_22 : Erdos634.Draft.R8Gen.NoF4 22 := noF4_of_bound 22 (by norm_num) (by decide)
theorem noF4_46 : Erdos634.Draft.R8Gen.NoF4 46 := noF4_of_bound 46 (by norm_num) (by decide)
theorem noF4_78 : Erdos634.Draft.R8Gen.NoF4 78 := noF4_of_bound 78 (by norm_num) (by decide)
/-- Negative control: `NoF4` FAILS at 66 (66 = (5+1)(10+1)), so `gapR8_of_arith` cannot apply (and 3 ∣ 66). -/
theorem not_noF4_66 : ¬ Erdos634.Draft.R8Gen.NoF4 66 := fun h => h 5 (by norm_num) 1 (by norm_num) (by norm_num)

theorem gapR8_22 : GapR8 22 := Erdos634.Draft.R8Gen.gapR8_of_arith 22 (by decide) noF4_22
theorem gapR8_46 : GapR8 46 := Erdos634.Draft.R8Gen.gapR8_of_arith 46 (by decide) noF4_46

/-- **GapR8F23 N**: `GapR8 N` restricted to the F2, F3, F3′ shapes (those whose Lean proofs need `3 ∤ N`;
F4, F4′ are proved from `NoF4 N`).  Used at N = 78 (3 ∣ 78, `NoF4 78`).  STATUS: paper-level (min N0 = 88/143/264
for primitive 120° triples, so N = 78 < 88 dies); no Lean at this N. -/
def GapR8F23 (N : ℕ) : Prop :=
  ∀ (D : CongruentDissection N) (α a b c : ℝ), IrrPi α → D.model.TwoPiThreeData α a b c →
    (TgtAngles D (2 * α) (2 * (Real.pi / 3 - α)) (α + (Real.pi / 3 - α)) ∨
     TgtAngles D α (2 * α) (3 * (Real.pi / 3 - α)) ∨
     TgtAngles D (Real.pi / 3 - α) (2 * (Real.pi / 3 - α)) (3 * α)) → False

theorem gapR8_of_f23 (N : ℕ) (hF4 : Erdos634.Draft.R8Gen.NoF4 N) (g : GapR8F23 N) : GapR8 N := by
  intro D α a b c hirr hm hshape
  obtain ⟨_, _, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  rcases hshape with hF2 | hF3 | hF3' | hF4s | hF4'
  · exact g D α a b c hirr hm (Or.inl hF2)
  · exact g D α a b c hirr hm (Or.inr (Or.inl hF3))
  · exact g D α a b c hirr hm (Or.inr (Or.inr hF3'))
  · obtain ⟨ν, hνpos, hd⟩ := Erdos634.Draft.R8F2to4Bridge.f4_data_of_shape D hm hF4s
    exact Erdos634.Draft.R8Gen.F4.f4_prime_contradiction D hirr hm hd ha0 hb0 hνpos hF4
  · obtain ⟨ν, hνpos, hd⟩ := Erdos634.Draft.R8F2to4Bridge.f4prime_data_of_shape D hm hF4'
    exact Erdos634.Draft.R8Gen.F4Prime.f4prime_prime_contradiction D hirr hm hd ha0 hb0 hνpos hF4

/-! ## Case A and Case B -/

theorem gapAcomp_22 : GapAcomp 22 := fun hS =>
  Erdos634.CaseA.RComposite.gapA_of_ell hS sqfree_22 (by norm_num) nsq22 hari22
    (ℓ := 11) (by norm_num) (by norm_num) (notEven_of_odd (val_one (p := 11) (k := 2) (by norm_num) (by norm_num) (by norm_num)))
theorem gapAcomp_46 : GapAcomp 46 := fun hS =>
  Erdos634.CaseA.RComposite.gapA_of_ell hS sqfree_46 (by norm_num) nsq46 hari46
    (ℓ := 23) (by norm_num) (by norm_num) (notEven_of_odd (val_one (p := 23) (k := 2) (by norm_num) (by norm_num) (by norm_num)))
theorem gapAcomp_66 : GapAcomp 66 := fun hS =>
  Erdos634.CaseA.RComposite.gapA_of_ell hS sqfree_66 (by norm_num) nsq66 hari66
    (ℓ := 11) (by norm_num) (by norm_num) (notEven_of_odd (val_one (p := 11) (k := 6) (by norm_num) (by norm_num) (by norm_num)))
theorem gapAcomp_78 : GapAcomp 78 := fun hS =>
  Erdos634.CaseA.RComposite.gapA_of_ell hS sqfree_78 (by norm_num) nsq78 hari78
    (ℓ := 13) (by norm_num) (by norm_num) (notEven_of_odd (val_one (p := 13) (k := 6) (by norm_num) (by norm_num) (by norm_num)))

theorem hbSimilar_22 : HBSimilar 22 := Erdos634.CaseA.RComposite.hbSimilar_of_sqfree17 sqfree_22 (by norm_num)
theorem hbSimilar_46 : HBSimilar 46 := Erdos634.CaseA.RComposite.hbSimilar_of_sqfree17 sqfree_46 (by norm_num)
theorem hbSimilar_66 : HBSimilar 66 := Erdos634.CaseA.RComposite.hbSimilar_of_sqfree17 sqfree_66 (by norm_num)
theorem hbSimilar_78 : HBSimilar 78 := Erdos634.CaseA.RComposite.hbSimilar_of_sqfree17 sqfree_78 (by norm_num)

/-! ## S2 -/
theorem s2Closed_46 : S2Closed 46 := s2Closed_of_arith 46 (s2Arith_of_twoadic 46 (by norm_num) (by decide +kernel))
theorem s2Closed_78 : S2Closed 78 := s2Closed_of_arith 78 (s2Arith_of_twoadic 78 (by norm_num) (by decide +kernel))
/-- Negative control: the 2-adic S2 obstruction FAILS at 22 and 66. -/
theorem twoadic_s2_fails_22 : ¬ (∀ p q w : ZMod 32, ¬ (2 ∣ p.val ∧ 2 ∣ q.val) →
    w ^ 2 ≠ ((22 : ℕ) : ZMod 32) * ((2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2))) := by decide +kernel
theorem twoadic_s2_fails_66 : ¬ (∀ p q w : ZMod 32, ¬ (2 ∣ p.val ∧ 2 ∣ q.val) →
    w ^ 2 ≠ ((66 : ℕ) : ZMod 32) * ((2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2))) := by decide +kernel

/-! ## The four final theorems -/

/-- **N = 22, modulo `H1Right 22` and `S2Closed 22`.** -/
theorem chain_22_final (gR : H1Right 22) (gS2 : S2Closed 22) (D : CongruentDissection 22) : False :=
  chain_gen3 22 sqfree_22 s1Closed_22 gS2 (s3Closed_of_isoQRef 22 isoQRef_22) isoH9b_22
    gapAcomp_22 (caseB_of_sumsq 22 hbSimilar_22 nsq22) (caseR_of_H1 22 gR nsqh22)
    (caseG_of_mod4_two 22 (by norm_num)) (gapE60_of_mod4_two 22 (by norm_num))
    (gapE120_of_mod4_two 22 (by norm_num)) (gapF1_of_mod4_two 22 (by norm_num)) gapR8_22 D

/-- **N = 46, modulo `H1Right 46` only.** -/
theorem chain_46_final (gR : H1Right 46) (D : CongruentDissection 46) : False :=
  chain_gen3 46 sqfree_46 s1Closed_46 s2Closed_46 (s3Closed_of_isoQRef 46 isoQRef_46) isoH9b_46
    gapAcomp_46 (caseB_of_sumsq 46 hbSimilar_46 nsq46) (caseR_of_H1 46 gR nsqh46)
    (caseG_of_mod4_two 46 (by norm_num)) (gapE60_of_mod4_two 46 (by norm_num))
    (gapE120_of_mod4_two 46 (by norm_num)) (gapF1_of_mod4_two 46 (by norm_num)) gapR8_46 D

/-- **N = 66, modulo `H1Right 66`, `S1Closed 66`, `GapR8 66`.**  (E60 / equilateral: see the module comment of
`COMPOSITE_GAPS_22_46_66_78.md` — closed here by `gapE60_of_mod4_two`, i.e. `Row5.theoremE_sixty` parity.) -/
theorem chain_66_final (gR : H1Right 66) (gS1 : S1Closed 66) (gR8 : GapR8 66) (D : CongruentDissection 66) :
    False :=
  chain_gen3 66 sqfree_66 gS1 Erdos634.Draft.CompositeS2Mod27.s2Closed_66
    (s3Closed_of_isoQRef 66 isoQRef_66) isoH9b_66
    gapAcomp_66 (caseB_of_sumsq 66 hbSimilar_66 nsq66) (caseR_of_H1 66 gR nsqh66)
    (caseG_of_mod4_two 66 (by norm_num)) (gapE60_of_mod4_two 66 (by norm_num))
    (gapE120_of_mod4_two 66 (by norm_num)) (gapF1_of_mod4_two 66 (by norm_num)) gR8 D

/-- **N = 78, modulo `H1Right 78` and `GapR8F23 78`.** -/
theorem chain_78_final (gR : H1Right 78) (gR8 : GapR8F23 78) (D : CongruentDissection 78) : False :=
  chain_gen3 78 sqfree_78 s1Closed_78 s2Closed_78 (s3Closed_of_isoQRef 78 isoQRef_78) isoH9b_78
    gapAcomp_78 (caseB_of_sumsq 78 hbSimilar_78 nsq78) (caseR_of_H1 78 gR nsqh78)
    (caseG_of_mod4_two 78 (by norm_num)) (gapE60_of_mod4_two 78 (by norm_num))
    (gapE120_of_mod4_two 78 (by norm_num)) (gapF1_of_mod4_two 78 (by norm_num))
    (gapR8_of_f23 78 noF4_78 gR8) D

end Erdos634.Draft.CompositeFinal3

#print axioms Erdos634.Draft.CompositeFinal3.chain_gen3
#print axioms Erdos634.Draft.CompositeFinal3.chain_22_final
#print axioms Erdos634.Draft.CompositeFinal3.chain_46_final
#print axioms Erdos634.Draft.CompositeFinal3.chain_66_final
#print axioms Erdos634.Draft.CompositeFinal3.chain_78_final
#print axioms Erdos634.Draft.CompositeFinal3.not_noF4_66
#print axioms Erdos634.Draft.CompositeFinal3.twoadic_s2_fails_22
