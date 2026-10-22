/-
Draft/CompositeFinal6.lean — arithmetic leaves and conditional dispatch for the ODD composites N = 35, 39, 51, 55, 87
(all squarefree, N ≡ 3 (mod 4)).  Uses `CompositeFinal3.chain_gen3` (S1, S2, S3 abstracted, `IsoH9b`).
*** CONDITIONAL theorems, NOT exclusions of any of the five N.  UNAUDITED.  Formalization debt, NOT /goal progress. ***
No sorry, no native_decide (`decide +kernel` on closed finite Nat/ZMod statements only).

What is proved here, per branch (see (private working notes, not included)):
  Case A      `GapAcomp N`    via `gapA_of_ell` (ℓ = 7, 13, 17, 11, 29; `HArith N`, N not a sum of two squares).
  Case B      `CaseBClosed N` via `caseB_of_mod4_three` (`Row2.theoremS_perm_sqfree`: N % 4 ≠ 3) — N ≡ 3 (mod 4) squarefree.
  Right tile  `CaseRClosed N` via `caseR_of_odd` (`row3_RP_even_any_label`: N odd ⇒ branch empty).  No `H1Right`.
  γ = 2α      `CaseGClosed N` via `caseG_of_M1Div` at 35, 55 (M1Div true); NOT at 39, 51, 87 (M = 3 pair).
  S1          QNR (ℓ = 5, 17, 5, 29) at 35, 51, 55, 87;  at 39 by the base-β route (`s1_arith_39` ⇒ M = p + q ⇒ I6).
  S2          QNR (ℓ = 5, 5, 29) at 35, 55, 87;  at 39, 51 by the global A ∣ 4N argument (`CompositeS2Global.s2_dvd`).
  S3          `IsoQRef N` (bounded check) at all five.
  IsoH9       `IsoH9b N` (bounded check) at all five.
  R8          `GapR8 N` (`gapR8_of_arith2`; NoF2/NoF3/NoF4z finite arithmetic) at all five.
Residual: `GapE60 N`, `GapE120 N`, `GapF1 N` (all five), `GammaTwoAlphaClosed N` (39, 51, 87).
-/
import Erdos634.Draft.CompositeFinal4
import Erdos634.Draft.CompositeS2Global

set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.CompositeFinal6

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.CompositeS1Arith Erdos634.Draft.CompositeIsoB Erdos634.Draft.CompositeFinal2
open Erdos634.Draft.CompositeFinal3
open Erdos634.Geometry.CaseA.LemmaH (HArith harith_of_bound)

/-! ## Arithmetic leaves -/

theorem sqfree_35 : Squarefree (35 : ℕ) := by decide +kernel
theorem sqfree_39 : Squarefree (39 : ℕ) := by decide +kernel
theorem sqfree_51 : Squarefree (51 : ℕ) := by decide +kernel
theorem sqfree_55 : Squarefree (55 : ℕ) := by decide +kernel
theorem sqfree_87 : Squarefree (87 : ℕ) := by decide +kernel

theorem hari35 : HArith 35 := harith_of_bound (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem hari39 : HArith 39 := harith_of_bound (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem hari51 : HArith 51 := harith_of_bound (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem hari55 : HArith 55 := harith_of_bound (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem hari87 : HArith 87 := harith_of_bound (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem nsq35 : ¬ ∃ x y : ℕ, 35 = x ^ 2 + y ^ 2 := nsq 35 (by norm_num) (by decide)
theorem nsq39 : ¬ ∃ x y : ℕ, 39 = x ^ 2 + y ^ 2 := nsq 39 (by norm_num) (by decide)
theorem nsq51 : ¬ ∃ x y : ℕ, 51 = x ^ 2 + y ^ 2 := nsq 51 (by norm_num) (by decide)
theorem nsq55 : ¬ ∃ x y : ℕ, 55 = x ^ 2 + y ^ 2 := nsq 55 (by norm_num) (by decide)
theorem nsq87 : ¬ ∃ x y : ℕ, 87 = x ^ 2 + y ^ 2 := nsq 87 (by norm_num) (by decide)

theorem isoQRef_35 : IsoQRef 35 := isoQRef_of_check 35 (by norm_num) (by norm_num) (by decide +kernel)
theorem isoQRef_39 : IsoQRef 39 := isoQRef_of_check 39 (by norm_num) (by norm_num) (by decide +kernel)
theorem isoQRef_51 : IsoQRef 51 := isoQRef_of_check 51 (by norm_num) (by norm_num) (by decide +kernel)
theorem isoQRef_55 : IsoQRef 55 := isoQRef_of_check 55 (by norm_num) (by norm_num) (by decide +kernel)
theorem isoQRef_87 : IsoQRef 87 := isoQRef_of_check 87 (by norm_num) (by norm_num) (by decide +kernel)

theorem isoH9b_35 : IsoH9b 35 := isoH9b_of_check 35 (by norm_num) (by decide +kernel)
theorem isoH9b_39 : IsoH9b 39 := isoH9b_of_check 39 (by norm_num) (by decide +kernel)
theorem isoH9b_51 : IsoH9b 51 := isoH9b_of_check 51 (by norm_num) (by decide +kernel)
theorem isoH9b_55 : IsoH9b 55 := isoH9b_of_check 55 (by norm_num) (by decide +kernel)
theorem isoH9b_87 : IsoH9b 87 := isoH9b_of_check 87 (by norm_num) (by decide +kernel)

/-! ## Case A (`gapA_of_ell`) -/

theorem gapAcomp_35 : GapAcomp 35 := fun hS =>
  Erdos634.CaseA.RComposite.gapA_of_ell hS sqfree_35 (by norm_num) nsq35 hari35
    (ℓ := 7) (by norm_num) (by norm_num) (notEven_of_odd (val_one (p := 7) (k := 5) (by norm_num) (by norm_num) (by norm_num)))
theorem gapAcomp_39 : GapAcomp 39 := fun hS =>
  Erdos634.CaseA.RComposite.gapA_of_ell hS sqfree_39 (by norm_num) nsq39 hari39
    (ℓ := 13) (by norm_num) (by norm_num) (notEven_of_odd (val_one (p := 13) (k := 3) (by norm_num) (by norm_num) (by norm_num)))
theorem gapAcomp_51 : GapAcomp 51 := fun hS =>
  Erdos634.CaseA.RComposite.gapA_of_ell hS sqfree_51 (by norm_num) nsq51 hari51
    (ℓ := 17) (by norm_num) (by norm_num) (notEven_of_odd (val_one (p := 17) (k := 3) (by norm_num) (by norm_num) (by norm_num)))
theorem gapAcomp_55 : GapAcomp 55 := fun hS =>
  Erdos634.CaseA.RComposite.gapA_of_ell hS sqfree_55 (by norm_num) nsq55 hari55
    (ℓ := 11) (by norm_num) (by norm_num) (notEven_of_odd (val_one (p := 11) (k := 5) (by norm_num) (by norm_num) (by norm_num)))
theorem gapAcomp_87 : GapAcomp 87 := fun hS =>
  Erdos634.CaseA.RComposite.gapA_of_ell hS sqfree_87 (by norm_num) nsq87 hari87
    (ℓ := 29) (by norm_num) (by norm_num) (notEven_of_odd (val_one (p := 29) (k := 3) (by norm_num) (by norm_num) (by norm_num)))

/-! ## Case B and right tile (both N-form-free at N ≡ 3 mod 4 odd) -/

theorem caseB_35 : CaseBClosed 35 := caseB_of_mod4_three 35 sqfree_35 (by norm_num) (by norm_num)
theorem caseB_39 : CaseBClosed 39 := caseB_of_mod4_three 39 sqfree_39 (by norm_num) (by norm_num)
theorem caseB_51 : CaseBClosed 51 := caseB_of_mod4_three 51 sqfree_51 (by norm_num) (by norm_num)
theorem caseB_55 : CaseBClosed 55 := caseB_of_mod4_three 55 sqfree_55 (by norm_num) (by norm_num)
theorem caseB_87 : CaseBClosed 87 := caseB_of_mod4_three 87 sqfree_87 (by norm_num) (by norm_num)

theorem caseR_35 : CaseRClosed 35 := caseR_of_odd 35 (by norm_num)
theorem caseR_39 : CaseRClosed 39 := caseR_of_odd 39 (by norm_num)
theorem caseR_51 : CaseRClosed 51 := caseR_of_odd 51 (by norm_num)
theorem caseR_55 : CaseRClosed 55 := caseR_of_odd 55 (by norm_num)
theorem caseR_87 : CaseRClosed 87 := caseR_of_odd 87 (by norm_num)

/-! ## γ = 2α -/

/-- **`GammaTwoAlphaClosed N`** (the atom GB.G2A): the `γ = 2α` tile with isosceles target (base angles α) is impossible.
Definitionally `ChainComposite.CaseGClosed N`.  Lean has it for `M1Div N` (`Row4.not_M1_any_label`); at N = 39, 51, 87
`M1Div N` is FALSE (m = 3: 27 < N, 3 ∣ N), and the surviving P5 pair is `(M, M') = (3, N/3)`. -/
def GammaTwoAlphaClosed (N : ℕ) : Prop := CaseGClosed N

theorem M1Div_35 : M1Div 35 := by
  intro m hm h3
  have : m ≤ 35 := Nat.le_of_dvd (by norm_num) hm
  interval_cases m <;> simp_all <;> omega
theorem M1Div_55 : M1Div 55 := by
  intro m hm h3
  have : m ≤ 55 := Nat.le_of_dvd (by norm_num) hm
  interval_cases m <;> simp_all <;> omega

theorem not_M1Div_39 : ¬ M1Div 39 := fun h => by have := h 3 (by norm_num) (by norm_num); omega
theorem not_M1Div_51 : ¬ M1Div 51 := fun h => by have := h 3 (by norm_num) (by norm_num); omega
theorem not_M1Div_87 : ¬ M1Div 87 := fun h => by have := h 3 (by norm_num) (by norm_num); omega

theorem gamma_35 : GammaTwoAlphaClosed 35 := caseG_of_M1Div 35 M1Div_35
theorem gamma_55 : GammaTwoAlphaClosed 55 := caseG_of_M1Div 55 M1Div_55

/-- The `P5` pairs `(M, M')` (`N = M M'`, `M ≡ M' ≡ N (2)`, `3 M < M'`) at N = 39, 51, 87 are exactly `M ∈ {1, 3}`:
`M = 1` is closed by `Row4.not_M1`'s mechanism, `M = 3` is the open atom. -/
theorem p5_pairs_39 : ∀ M M' : ℤ, 0 < M → (39 : ℤ) = M * M' → 3 * M < M' → M = 1 ∨ M = 3 := by
  intro M M' hM h hlt
  have hM1 : M ≤ 39 := by nlinarith
  interval_cases M <;> omega
theorem p5_pairs_51 : ∀ M M' : ℤ, 0 < M → (51 : ℤ) = M * M' → 3 * M < M' → M = 1 ∨ M = 3 := by
  intro M M' hM h hlt
  have hM1 : M ≤ 51 := by nlinarith
  interval_cases M <;> omega
theorem p5_pairs_87 : ∀ M M' : ℤ, 0 < M → (87 : ℤ) = M * M' → 3 * M < M' → M = 1 ∨ M = 3 := by
  intro M M' hM h hlt
  have hM1 : M ≤ 87 := by nlinarith
  interval_cases M <;> omega

/-! ## S1 -/

theorem qnr3_17 : ∀ x : ZMod 17, x ^ 2 ≠ 3 := by decide
theorem qnr3_29 : ∀ x : ZMod 29, x ^ 2 ≠ 3 := by decide
theorem qnr2_29 : ∀ x : ZMod 29, x ^ 2 ≠ 2 := by decide

theorem s1Closed_of_qnr (N : ℕ) (ℓ : ℕ) (hℓ : ℓ.Prime) (hval : Odd (padicValNat ℓ N))
    (hq3 : ∀ x : ZMod ℓ, x ^ 2 ≠ 3) : S1Closed N :=
  fun D α β a b c r hα hrel hd hr hb htg =>
    Erdos634.Draft.ScaleBaseBetaQNR.scaleBaseBeta_qnr N D ℓ hℓ hval hq3 α β a b c r hα hrel hd hr hb htg

theorem s1Closed_35 : S1Closed 35 :=
  s1Closed_of_qnr 35 5 (by norm_num) (val_one (p := 5) (k := 7) (by norm_num) (by norm_num) (by norm_num)) qnr3_5
theorem s1Closed_51 : S1Closed 51 :=
  s1Closed_of_qnr 51 17 (by norm_num) (val_one (p := 17) (k := 3) (by norm_num) (by norm_num) (by norm_num)) qnr3_17
theorem s1Closed_55 : S1Closed 55 :=
  s1Closed_of_qnr 55 5 (by norm_num) (val_one (p := 5) (k := 11) (by norm_num) (by norm_num) (by norm_num)) qnr3_5
theorem s1Closed_87 : S1Closed 87 :=
  s1Closed_of_qnr 87 29 (by norm_num) (val_one (p := 29) (k := 3) (by norm_num) (by norm_num) (by norm_num)) qnr3_29

/-- N = 39: `S1Arith 39` is FALSE ((p,q,M) = (3,4,7), the base-β instance (e,f) = (3,4), 3·16 − 9 = 39); every coprime
solution has `M = p + q`. -/
theorem not_s1Arith_39 : ¬ S1Arith 39 := fun h =>
  h 3 4 7 (by norm_num) (by norm_num) (by rw [Int.isCoprime_iff_gcd_eq_one]; decide) (by norm_num) (by norm_num)

theorem s1_arith_39 : ∀ p q M : ℤ, 0 < p → p < q → IsCoprime p q → 0 < M →
    (39 : ℕ) * (p + q) ^ 2 = M ^ 2 * (3 * q ^ 2 - p ^ 2) → M = p + q := by
  intro p q M hp hpq hcop hM heq
  push_cast at heq
  have hq0 : 0 < q := by omega
  have hY : 0 < 3 * q ^ 2 - p ^ 2 := by nlinarith
  have hs : 0 < p + q := by omega
  have h1 : (39 : ℤ) * (3 * q ^ 2 - p ^ 2) * (p + q) ^ 2 = (M * (3 * q ^ 2 - p ^ 2)) ^ 2 := by
    have : (39 : ℤ) * (3 * q ^ 2 - p ^ 2) * (p + q) ^ 2 = (3 * q ^ 2 - p ^ 2) * (39 * (p + q) ^ 2) := by ring
    rw [this, heq]; ring
  have hdvd : (p + q) ^ 2 ∣ (M * (3 * q ^ 2 - p ^ 2)) ^ 2 :=
    ⟨39 * (3 * q ^ 2 - p ^ 2), by rw [← h1]; ring⟩
  obtain ⟨w, hw⟩ := (Int.pow_dvd_pow_iff (two_ne_zero)).mp hdvd
  have hw2 : w ^ 2 = 39 * (3 * q ^ 2 - p ^ 2) := by
    have : (p + q) ^ 2 * w ^ 2 = (p + q) ^ 2 * (39 * (3 * q ^ 2 - p ^ 2)) := by
      calc (p + q) ^ 2 * w ^ 2 = ((p + q) * w) ^ 2 := by ring
        _ = (M * (3 * q ^ 2 - p ^ 2)) ^ 2 := by rw [← hw]
        _ = (p + q) ^ 2 * (39 * (3 * q ^ 2 - p ^ 2)) := by rw [← h1]; ring
    exact mul_left_cancel₀ (pow_ne_zero 2 hs.ne') this
  have h3 : (3 : ℤ) ∣ w := Int.prime_three.dvd_of_dvd_pow (n := 2) ⟨13 * (3 * q ^ 2 - p ^ 2), by rw [hw2]; ring⟩
  have h13 : (13 : ℤ) ∣ w := (Int.prime_iff_natAbs_prime.mpr (by norm_num : Nat.Prime (Int.natAbs 13))).dvd_of_dvd_pow (n := 2)
    ⟨3 * (3 * q ^ 2 - p ^ 2), by rw [hw2]; ring⟩
  have h39 : (39 : ℤ) ∣ w := by omega
  obtain ⟨u, hu⟩ := h39
  have hYu : 3 * q ^ 2 - p ^ 2 = 39 * u ^ 2 := by
    have : (39 : ℤ) * (3 * q ^ 2 - p ^ 2) = 39 * (39 * u ^ 2) := by rw [← hw2, hu]; ring
    exact mul_left_cancel₀ (by norm_num) this
  have hu0 : u ≠ 0 := by
    rintro rfl; nlinarith
  have hMu : M * u = p + q := by
    have h4 : (39 * u) * (M * u) = (39 * u) * (p + q) := by
      have : M * (3 * q ^ 2 - p ^ 2) = (p + q) * w := hw
      rw [hYu, hu] at this; linear_combination this
    exact mul_left_cancel₀ (by intro h; apply hu0; omega) h4
  have hupos : 0 < u := by
    by_contra hc
    nlinarith
  have hcop_s : IsCoprime (p + q) p := Erdos634.Draft.CompositeFinal4.isCoprime_sum_left' hcop
  have hcop_up : IsCoprime u p := hcop_s.of_isCoprime_of_dvd_left ⟨M, by rw [← hMu]; ring⟩
  have hu_dvd : u ∣ 2 * p ^ 2 := ⟨39 * u - 3 * (q - p) * M, by linear_combination hYu + 3 * (q - p) * hMu⟩
  have hu2 : u ∣ 2 := (hcop_up.pow_right (n := 2)).dvd_of_dvd_mul_right hu_dvd
  have hule : u ≤ 2 := Int.le_of_dvd (by norm_num) hu2
  have hu12 : u = 1 ∨ u = 2 := by omega
  rcases hu12 with rfl | rfl
  · linarith
  · exfalso
    have hq11 : q ≤ 11 := by nlinarith
    have hg := Int.isCoprime_iff_gcd_eq_one.mp hcop
    have hp10 : p ≤ 10 := by omega
    interval_cases q <;> interval_cases p <;> first | omega | (norm_num at hg)

theorem s1Closed_39 : S1Closed 39 := by
  intro D α β a b c r hα hrel hmod har hbr htgt
  exact not_baseBetaTiled
    (Erdos634.Draft.CompositeFinal4.s1_baseBetaTiled_of_arith 39 s1_arith_39 D α β a b c r hα hrel hmod har hbr htgt)

/-! ## S2 -/

theorem s2Closed_35 : S2Closed 35 :=
  s2Closed_of_qnr 35 5 (by norm_num) (val_one (p := 5) (k := 7) (by norm_num) (by norm_num) (by norm_num)) qnr2_5 qnr3_5
theorem s2Closed_55 : S2Closed 55 :=
  s2Closed_of_qnr 55 5 (by norm_num) (val_one (p := 5) (k := 11) (by norm_num) (by norm_num) (by norm_num)) qnr2_5 qnr3_5
theorem s2Closed_87 : S2Closed 87 :=
  s2Closed_of_qnr 87 29 (by norm_num) (val_one (p := 29) (k := 3) (by norm_num) (by norm_num) (by norm_num)) qnr2_29 qnr3_29

theorem s2Arith_39 : S2Arith 39 := by
  refine Erdos634.Draft.CompositeS2Global.s2Arith_of_dvd 39 (by norm_num) ?_
  intro p q hp hpq hq hd S heq
  have hq1 : 1 < q := by omega
  have hq' : q ≤ 12 := by push_cast at hq; by_contra h; push Not at h; nlinarith
  interval_cases q <;> interval_cases p <;>
    first | (revert hd; norm_num; done) | (revert heq; generalize S ^ 2 = T; norm_num; omega)

theorem s2Arith_51 : S2Arith 51 := by
  refine Erdos634.Draft.CompositeS2Global.s2Arith_of_dvd 51 (by norm_num) ?_
  intro p q hp hpq hq hd S heq
  have hq1 : 1 < q := by omega
  have hq' : q ≤ 14 := by push_cast at hq; by_contra h; push Not at h; nlinarith
  interval_cases q <;> interval_cases p <;>
    first | (revert hd; norm_num; done) | (revert heq; generalize S ^ 2 = T; norm_num; omega)

theorem s2Closed_39 : S2Closed 39 := s2Closed_of_arith 39 s2Arith_39
theorem s2Closed_51 : S2Closed 51 := s2Closed_of_arith 51 s2Arith_51

/-! ## R8 (`GapR8`): finite arithmetic via `gapR8_of_arith2` -/

open Erdos634.Draft.R8Gen2 in
theorem noF3_odd (N : ℕ) (hN : N ≤ 90) (h : ∀ s j : ℤ, 0 < j → j < s → s ≤ 12 → j ≤ 4 → 4 * (N : ℤ) ≠ 3 * (s + j) * (s + 3 * j)) :
    NoF3 N := by
  intro s j hj hjs hh
  have h1 : j ≤ 4 := by
    have : (N : ℤ) ≤ 90 := by exact_mod_cast hN
    nlinarith
  have h2 : s ≤ 12 := by
    have : (N : ℤ) ≤ 90 := by exact_mod_cast hN
    nlinarith
  exact h s j hj hjs h2 h1 hh

end Erdos634.Draft.CompositeFinal6
