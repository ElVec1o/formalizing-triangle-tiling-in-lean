/-
Draft/CompositeFinal2.lean — N = 14, 42, 62, 70 (all squarefree, N ≡ 2 mod 4): the 38/86 template
(`ChainComposite` dispatch + `CompositeFinal`), re-done with the leaves that are N-specific.
*** CONDITIONAL theorems, NOT exclusions of 14/42/62/70.  UNAUDITED.  Formalization debt, NOT /goal progress. ***
No sorry, no native_decide (`decide +kernel` on closed finite statements only).

Residual named hypotheses of each `chain_N_final` (everything else is proved from existing Lean):
  14 : H1Right 14                                   (cited BeesonI Thm 4(v))
  62 : H1Right 62                                   (cited)
  42 : H1Right 42, S2Closed 42, GapR8 42
  70 : H1Right 70, S3Closed 70, GapR8Rest70         (F2, F4, F4' shapes of GapR8; F3, F3' are proved)
Why: see (private working notes, not included)
-/
import Erdos634.Draft.CompositeGen2
import Erdos634.Draft.CompositeArith
import Erdos634.Draft.CompositeS2Arith
import Erdos634.Draft.CaseACompositeE
import Erdos634.Draft.CaseAComposite
import Erdos634.Draft.ChainCompositeR8

open scoped Classical

set_option synthInstance.maxSize 1000
set_option synthInstance.maxHeartbeats 400000

namespace Erdos634.Draft.CompositeFinal2

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Geometry.CaseA.LemmaH (HArith harith_of_bound)

/-! ## Shared arithmetic helpers -/

theorem val_one {p k : ℕ} (hp : p.Prime) (hk : ¬ p ∣ k) (hk0 : k ≠ 0) : Odd (padicValNat p (p * k)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have : padicValNat p (p * k) = 1 := by
    rw [padicValNat.mul hp.ne_zero hk0, padicValNat_self, padicValNat.eq_zero_of_not_dvd hk]
  rw [this]; exact odd_one

theorem notEven_of_odd {n : ℕ} (h : Odd n) : ¬ Even n := Nat.not_even_iff_odd.mpr h

/-- `IsoH9 N` by bounded check: no `a + 2b = k` (3 ≤ k < N, k ∣ N) with `a²+ab+b²` a perfect square. -/
theorem isoH9_of_check (N : ℕ) (hN : 0 < N)
    (hchk : ∀ a : ℕ, a < N → ∀ b : ℕ, b < N → 0 < a → 0 < b → a + 2 * b < N → 3 ≤ a + 2 * b →
      a + 2 * b ∣ N → Nat.sqrt (a ^ 2 + a * b + b ^ 2) * Nat.sqrt (a ^ 2 + a * b + b ^ 2) ≠ a ^ 2 + a * b + b ^ 2) :
    IsoH9 N := by
  intro a b c ha hb hc hcc h3 hdvd
  have hk : a + 2 * b ≤ (N : ℤ) := Int.le_of_dvd (by exact_mod_cast hN) hdvd
  by_contra hne
  have hlt : a + 2 * b < (N : ℤ) := lt_of_le_of_ne hk hne
  lift a to ℕ using ha.le
  lift b to ℕ using hb.le
  lift c to ℕ using hc.le
  have hdvd' : a + 2 * b ∣ N := by exact_mod_cast hdvd
  have hcc' : c ^ 2 = a ^ 2 + a * b + b ^ 2 := by exact_mod_cast hcc
  have h := hchk a (by omega) b (by omega) (by omega) (by omega) (by omega) (by omega) hdvd'
  apply h
  rw [← hcc', Nat.sqrt_eq']; ring

theorem isoH9_14 : IsoH9 14 := isoH9_of_check 14 (by norm_num) (by decide +kernel)
theorem isoH9_42 : IsoH9 42 := isoH9_of_check 42 (by norm_num) (by decide +kernel)
theorem isoH9_62 : IsoH9 62 := isoH9_of_check 62 (by norm_num) (by decide +kernel)
theorem isoH9_70 : IsoH9 70 := isoH9_of_check 70 (by norm_num) (by decide +kernel)

theorem sqfree_14 : Squarefree (14 : ℕ) := by decide +kernel
theorem sqfree_42 : Squarefree (42 : ℕ) := by decide +kernel
theorem sqfree_62 : Squarefree (62 : ℕ) := by decide +kernel
theorem sqfree_70 : Squarefree (70 : ℕ) := by decide +kernel

theorem hari14 : HArith 14 := harith_of_bound (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem hari42 : HArith 42 := harith_of_bound (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem hari62 : HArith 62 := harith_of_bound (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem hari70 : HArith 70 := harith_of_bound (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem nsq (N : ℕ) (hN : N ≤ 100) (h : ∀ x : ℕ, x < 11 → ∀ y : ℕ, y < 11 → N ≠ x ^ 2 + y ^ 2) :
    ¬ ∃ x y : ℕ, N = x ^ 2 + y ^ 2 := by
  rintro ⟨x, y, hxy⟩
  exact h x (by nlinarith) y (by nlinarith) hxy

theorem nsq_half (N : ℕ) (hN : N ≤ 100) (h : ∀ x : ℕ, x < 11 → ∀ y : ℕ, y < 11 → N ≠ 2 * (x ^ 2 + y ^ 2)) :
    ¬ ∃ x y : ℕ, N = 2 * (x ^ 2 + y ^ 2) := by
  rintro ⟨x, y, hxy⟩
  exact h x (by nlinarith) y (by nlinarith) hxy

theorem nsq14 : ¬ ∃ x y : ℕ, 14 = x ^ 2 + y ^ 2 := nsq 14 (by norm_num) (by decide)
theorem nsq42 : ¬ ∃ x y : ℕ, 42 = x ^ 2 + y ^ 2 := nsq 42 (by norm_num) (by decide)
theorem nsq62 : ¬ ∃ x y : ℕ, 62 = x ^ 2 + y ^ 2 := nsq 62 (by norm_num) (by decide)
theorem nsq70 : ¬ ∃ x y : ℕ, 70 = x ^ 2 + y ^ 2 := nsq 70 (by norm_num) (by decide)
theorem nsqh14 : ¬ ∃ x y : ℕ, 14 = 2 * (x ^ 2 + y ^ 2) := nsq_half 14 (by norm_num) (by decide)
theorem nsqh42 : ¬ ∃ x y : ℕ, 42 = 2 * (x ^ 2 + y ^ 2) := nsq_half 42 (by norm_num) (by decide)
theorem nsqh62 : ¬ ∃ x y : ℕ, 62 = 2 * (x ^ 2 + y ^ 2) := nsq_half 62 (by norm_num) (by decide)
theorem nsqh70 : ¬ ∃ x y : ℕ, 70 = 2 * (x ^ 2 + y ^ 2) := nsq_half 70 (by norm_num) (by decide)

theorem noF4_of_bound (N : ℕ) (hN : N ≤ 100)
    (h : ∀ x : ℕ, x < 8 → ∀ r : ℕ, r < 11 → 0 < x → 0 < r → N ≠ (x + r) * (2 * x + r)) : Erdos634.Draft.R8Gen.NoF4 N := by
  apply Erdos634.Draft.R8Gen.noF4_of_int
  intro x r hx hr hxr
  exact h x (by nlinarith) r (by nlinarith) hx hr hxr

theorem noF4_14 : Erdos634.Draft.R8Gen.NoF4 14 := noF4_of_bound 14 (by norm_num) (by decide)
theorem noF4_62 : Erdos634.Draft.R8Gen.NoF4 62 := noF4_of_bound 62 (by norm_num) (by decide)

/-- Negative controls: `NoF4` FAILS at 42 and 70 (so `gapR8_of_arith` does not apply). -/
theorem not_noF4_42 : ¬ Erdos634.Draft.R8Gen.NoF4 42 := fun h => h 1 (by norm_num) 5 (by norm_num) (by norm_num)
theorem not_noF4_70 : ¬ Erdos634.Draft.R8Gen.NoF4 70 := fun h => h 3 (by norm_num) 4 (by norm_num) (by norm_num)

theorem gapR8_14 : GapR8 14 := Erdos634.Draft.R8Gen.gapR8_of_arith 14 (by decide) noF4_14
theorem gapR8_62 : GapR8 62 := Erdos634.Draft.R8Gen.gapR8_of_arith 62 (by decide) noF4_62

/-! ## Quadratic non-residues -/
theorem qnr3_7 : ∀ x : ZMod 7, x ^ 2 ≠ 3 := by decide
theorem qnr3_31 : ∀ x : ZMod 31, x ^ 2 ≠ 3 := by decide
theorem qnr2_5 : ∀ x : ZMod 5, x ^ 2 ≠ 2 := by decide
theorem qnr3_5 : ∀ x : ZMod 5, x ^ 2 ≠ 3 := by decide

/-! ## Case A and Case B -/

theorem gapAcomp_14 : GapAcomp 14 := fun hS =>
  Erdos634.CaseA.RCompositeE.gapA_of_ellE hS sqfree_14 (by norm_num) (Or.inr (by norm_num)) nsq14 hari14
    (ℓ := 7) (by norm_num) le_rfl (notEven_of_odd (val_one (p := 7) (k := 2) (by norm_num) (by norm_num) (by norm_num)))

theorem gapAcomp_42 : GapAcomp 42 := fun hS =>
  Erdos634.CaseA.RComposite.gapA_of_ell hS sqfree_42 (by norm_num) nsq42 hari42
    (ℓ := 7) (by norm_num) le_rfl (notEven_of_odd (val_one (p := 7) (k := 6) (by norm_num) (by norm_num) (by norm_num)))

theorem gapAcomp_62 : GapAcomp 62 := fun hS =>
  Erdos634.CaseA.RComposite.gapA_of_ell hS sqfree_62 (by norm_num) nsq62 hari62
    (ℓ := 31) (by norm_num) (by norm_num) (notEven_of_odd (val_one (p := 31) (k := 2) (by norm_num) (by norm_num) (by norm_num)))

theorem gapAcomp_70 : GapAcomp 70 := fun hS =>
  Erdos634.CaseA.RComposite.gapA_of_ell hS sqfree_70 (by norm_num) nsq70 hari70
    (ℓ := 7) (by norm_num) le_rfl (notEven_of_odd (val_one (p := 7) (k := 10) (by norm_num) (by norm_num) (by norm_num)))

/-- Case B at 14: the cited `HBSimilar 14` is a THEOREM (Lemma Q variant, `Row2.theoremS_perm_sqfreeE`). -/
theorem hbSimilar_14 : HBSimilar 14 :=
  fun D μ τ hs => Row2.theoremS_perm_sqfreeE D μ τ hs sqfree_14 (by norm_num) (Or.inr (by norm_num))
theorem hbSimilar_42 : HBSimilar 42 := Erdos634.CaseA.RComposite.hbSimilar_of_sqfree17 sqfree_42 (by norm_num)
theorem hbSimilar_62 : HBSimilar 62 := Erdos634.CaseA.RComposite.hbSimilar_of_sqfree17 sqfree_62 (by norm_num)
theorem hbSimilar_70 : HBSimilar 70 := Erdos634.CaseA.RComposite.hbSimilar_of_sqfree17 sqfree_70 (by norm_num)

/-! ## Residual named hypotheses beyond `H1Right`, `S2Closed`, `S3Closed` -/

/-- **GapR8Rest70**: the F2, F4, F4′ shapes of `GapR8 70` (shapes F3, F3′ are proved: `3 ∤ 70`).  Residual because
`NoF4 70` is FALSE (`70 = (3+4)(6+4)`), so `R8Gen.F2/F4/F4Prime.*_contradiction` do not apply.  STATUS: paper-level
(min N0 = 88 for primitive 120° triples, so N = 70 < 88 dies) — no Lean for this N. -/
def GapR8Rest70 : Prop :=
  ∀ (D : CongruentDissection 70) (α a b c : ℝ), IrrPi α → D.model.TwoPiThreeData α a b c →
    (TgtAngles D (2 * α) (2 * (Real.pi / 3 - α)) (α + (Real.pi / 3 - α)) ∨
     TgtAngles D α (2 * (Real.pi / 3 - α)) (2 * α + (Real.pi / 3 - α)) ∨
     TgtAngles D (Real.pi / 3 - α) (2 * α) (α + 2 * (Real.pi / 3 - α))) → False

theorem gapR8_of_rest70 (g : GapR8Rest70) : GapR8 70 := by
  intro D α a b c hirr hm hshape
  obtain ⟨_, _, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  rcases hshape with hF2 | hF3 | hF3' | hF4s | hF4'
  · exact g D α a b c hirr hm (Or.inl hF2)
  · obtain ⟨ν, hνpos, hd⟩ := Erdos634.Draft.R8F2to4Bridge.f3_data_of_shape D hm hF3
    exact Erdos634.Draft.R8Gen.F3.f3_prime_contradiction D hirr hm hd ha0 hb0 hνpos (by decide)
  · obtain ⟨ν, hνpos, hd⟩ := Erdos634.Draft.R8F2to4Bridge.f3prime_data_of_shape D hm hF3'
    exact Erdos634.Draft.R8Gen.F3Prime.f3prime_contradiction D hirr hm hd ha0 hb0 hνpos (by decide)
  · exact g D α a b c hirr hm (Or.inr (Or.inl hF4s))
  · exact g D α a b c hirr hm (Or.inr (Or.inr hF4'))

/-! ## The four final theorems -/

/-- **N = 14, modulo `H1Right 14` only.** -/
theorem chain_14_final (gR : H1Right 14) (D : CongruentDissection 14) : False :=
  chain_gen2 14 sqfree_14 7 (by norm_num) (val_one (p := 7) (k := 2) (by norm_num) (by norm_num) (by norm_num))
    qnr3_7 (s2Closed_of_arith 14 twoadic_14) (s3Closed_of_isoQRef 14 isoQRef_14) isoH9_14
    gapAcomp_14 (caseB_of_sumsq 14 hbSimilar_14 nsq14) (caseR_of_H1 14 gR nsqh14)
    (caseG_of_mod4_two 14 (by norm_num)) (gapE60_of_mod4_two 14 (by norm_num))
    (gapE120_of_mod4_two 14 (by norm_num)) (gapF1_of_mod4_two 14 (by norm_num)) gapR8_14 D

/-- **N = 62, modulo `H1Right 62` only.** -/
theorem chain_62_final (gR : H1Right 62) (D : CongruentDissection 62) : False :=
  chain_gen2 62 sqfree_62 31 (by norm_num) (val_one (p := 31) (k := 2) (by norm_num) (by norm_num) (by norm_num))
    qnr3_31 (s2Closed_of_arith 62 twoadic_62) (s3Closed_of_isoQRef 62 isoQRef_62) isoH9_62
    gapAcomp_62 (caseB_of_sumsq 62 hbSimilar_62 nsq62) (caseR_of_H1 62 gR nsqh62)
    (caseG_of_mod4_two 62 (by norm_num)) (gapE60_of_mod4_two 62 (by norm_num))
    (gapE120_of_mod4_two 62 (by norm_num)) (gapF1_of_mod4_two 62 (by norm_num)) gapR8_62 D

/-- **N = 42, modulo `H1Right 42`, `S2Closed 42`, `GapR8 42`.** -/
theorem chain_42_final (gR : H1Right 42) (gS2 : S2Closed 42) (gR8 : GapR8 42) (D : CongruentDissection 42) : False :=
  chain_gen2 42 sqfree_42 7 (by norm_num) (val_one (p := 7) (k := 6) (by norm_num) (by norm_num) (by norm_num))
    qnr3_7 gS2 (s3Closed_of_isoQRef 42 isoQRef_42) isoH9_42
    gapAcomp_42 (caseB_of_sumsq 42 hbSimilar_42 nsq42) (caseR_of_H1 42 gR nsqh42)
    (caseG_of_mod4_two 42 (by norm_num)) (gapE60_of_mod4_two 42 (by norm_num))
    (gapE120_of_mod4_two 42 (by norm_num)) (gapF1_of_mod4_two 42 (by norm_num)) gR8 D

/-- **N = 70, modulo `H1Right 70`, `S3Closed 70`, `GapR8Rest70`.**  S2 is closed by the QNR leaf with ℓ = 5. -/
theorem chain_70_final (gR : H1Right 70) (gS3 : S3Closed 70) (gR8 : GapR8Rest70) (D : CongruentDissection 70) :
    False :=
  chain_gen2 70 sqfree_70 7 (by norm_num) (val_one (p := 7) (k := 10) (by norm_num) (by norm_num) (by norm_num))
    qnr3_7
    (s2Closed_of_qnr 70 5 (by norm_num) (val_one (p := 5) (k := 14) (by norm_num) (by norm_num) (by norm_num))
      qnr2_5 qnr3_5)
    gS3 isoH9_70
    gapAcomp_70 (caseB_of_sumsq 70 hbSimilar_70 nsq70) (caseR_of_H1 70 gR nsqh70)
    (caseG_of_mod4_two 70 (by norm_num)) (gapE60_of_mod4_two 70 (by norm_num))
    (gapE120_of_mod4_two 70 (by norm_num)) (gapF1_of_mod4_two 70 (by norm_num)) (gapR8_of_rest70 gR8) D

end Erdos634.Draft.CompositeFinal2

#print axioms Erdos634.Draft.CompositeFinal2.chain_14_final
#print axioms Erdos634.Draft.CompositeFinal2.chain_62_final
#print axioms Erdos634.Draft.CompositeFinal2.chain_42_final
#print axioms Erdos634.Draft.CompositeFinal2.chain_70_final
#print axioms Erdos634.Draft.CompositeFinal2.hbSimilar_14
#print axioms Erdos634.Draft.CompositeFinal2.not_noF4_42
#print axioms Erdos634.Draft.CompositeFinal2.not_noF4_70
