/-
Draft/CompositeFinal11.lean — arithmetic leaves, S1/S2, R8 and conditional dispatch for the odd squarefree composites
N = 21, 33, 57, 69  (all N ≡ 1 (mod 4), 3 ∣ N, not a sum of two squares).  Recipe of CompositeFinal6/7 (N ≡ 3 mod 4) adapted:
  Case A   `gapA_of_ell` with ℓ = 7, 11, 19, 23.
  Case B   `caseB_of_sumsq`: `HBSimilar N` is the THEOREM `hbSimilar_of_sqfree17` (squarefree, N ≥ 17) and N is not a sum of two
           squares (3 appears to an odd power) — this replaces `caseB_of_mod4_three`, whose hypothesis `N % 4 = 3` is false here.
  Right    `caseR_of_odd`.      γ = 2α   `caseG_of_squarefree` (`Row4.not_squarefree`).
  S1       QNR (3 non-residue) at ℓ = 7 (N = 21), 19 (N = 57); at N = 33, 69 (3 is a QR mod 11, mod 23) the base-β route:
           `s1_arith_gen` (squarefree N, no solution of 3q²−p² = 4N) ⇒ M = p+q ⇒ I6 (`not_baseBetaTiled`).
  S2       QNR (2 and 3 non-residues) at ℓ = 19 (N = 57); at N = 21, 33, 69 the global `A ∣ 4N` argument (`s2Arith_of_dvd`).
  S3       `IsoQRef N` (bounded check) at N = 33, 57, 69.  **FAILS at N = 21**: (e, d, m) = (1, 1, 1), Q = 7, 21·1 = 1²·3·7
           (the base-α member (2,3,4) on the target (12,12,21)); `S3Closed 21` stays a named hypothesis.
  IsoH9b   bounded check at N = 21, 57, 69.  **FAILS at N = 33**: (a,b,c,k,nA) = (5,3,7,3,−1), e = 11 ∣ 33
           (the sporadic 2π/3 tile (5,3,7) on the target (21,21,33)); the `IsoTP` leaf at 33 stays a named hypothesis.
  R8       `gapR8_of_arith2` (NoF2/NoF3/NoF4z by finite arithmetic).
*** UNAUDITED.  Formalization debt, NOT /goal progress.  No sorry, no native_decide. ***
-/
import Erdos634.Draft.CompositeFinal10

set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.CompositeFinal11

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.CompositeS1Arith Erdos634.Draft.CompositeIsoB Erdos634.Draft.CompositeFinal2
open Erdos634.Draft.CompositeFinal3 Erdos634.Draft.CompositeFinal6
open Erdos634.Draft.R8Gen2
open Erdos634.Geometry.CaseA.LemmaH (HArith harith_of_bound)

theorem qnr3_7_f11 : ∀ x : ZMod 7, x ^ 2 ≠ 3 := by decide
theorem qnr2_19_f11 : ∀ x : ZMod 19, x ^ 2 ≠ 2 := by decide
theorem qnr3_19_f11 : ∀ x : ZMod 19, x ^ 2 ≠ 3 := by decide

/-! ## N = 21 -/
theorem sqfree_21 : Squarefree (21 : ℕ) := by decide +kernel
theorem hari21 : HArith 21 := harith_of_bound (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem nsq21 : ¬ ∃ x y : ℕ, 21 = x ^ 2 + y ^ 2 := nsq 21 (by norm_num) (by decide)
theorem gapAcomp_21 : GapAcomp 21 := fun hS =>
  Erdos634.CaseA.RComposite.gapA_of_ell hS sqfree_21 (by norm_num) nsq21 hari21
    (ℓ := 7) (by norm_num) (by norm_num) (notEven_of_odd (val_one (p := 7) (k := 3) (by norm_num) (by norm_num) (by norm_num)))
theorem hbSimilar_21 : HBSimilar 21 := Erdos634.CaseA.RComposite.hbSimilar_of_sqfree17 sqfree_21 (by norm_num)
theorem caseB_21 : CaseBClosed 21 := caseB_of_sumsq 21 hbSimilar_21 nsq21
theorem caseR_21 : CaseRClosed 21 := caseR_of_odd 21 (by norm_num)
theorem gamma_21 : GammaTwoAlphaClosed 21 := Erdos634.Draft.CompositeFinal10.caseG_of_squarefree 21 sqfree_21

theorem noF3_21 : NoF3 21 := by
  intro s j hj hjs h
  push_cast at h
  have h1 : j ≤ 4 := by nlinarith
  have h2 : s ≤ 12 := by nlinarith
  interval_cases j <;> interval_cases s <;> omega

theorem noF2_21 : NoF2 21 := by
  apply noF2_of_int
  · intro z hz
    push_cast at hz
    have h1 : z ≤ 6 := by nlinarith
    have h2 : -6 ≤ z := by nlinarith
    interval_cases z <;> omega
  · intro x r hx hr h z hz
    push_cast at hz
    have hx7 : x ≤ 6 := by nlinarith
    have hr9 : r ≤ 9 := by nlinarith
    interval_cases x <;> interval_cases r <;>
      first
      | omega
      | (norm_num at hz
         have h1 : z ≤ 9 := by nlinarith
         have h2 : -9 ≤ z := by nlinarith
         interval_cases z <;> omega)

theorem noF4z_21 : NoF4z 21 := by
  apply noF4z_of_int
  intro x r hx hr h z hz
  have hx7 : x ≤ 6 := by nlinarith
  have hr9 : r ≤ 9 := by nlinarith
  interval_cases x <;> interval_cases r <;>
    first
    | omega
    | (norm_num at hz
       have h1 : z ≤ 9 := by nlinarith
       have h2 : -9 ≤ z := by nlinarith
       interval_cases z <;> omega)

theorem gapR8_21 : GapR8 21 := gapR8_of_arith2 21 noF2_21 noF3_21 noF4z_21

/-! ## N = 33 -/
theorem sqfree_33 : Squarefree (33 : ℕ) := by decide +kernel
theorem hari33 : HArith 33 := harith_of_bound (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem nsq33 : ¬ ∃ x y : ℕ, 33 = x ^ 2 + y ^ 2 := nsq 33 (by norm_num) (by decide)
theorem gapAcomp_33 : GapAcomp 33 := fun hS =>
  Erdos634.CaseA.RComposite.gapA_of_ell hS sqfree_33 (by norm_num) nsq33 hari33
    (ℓ := 11) (by norm_num) (by norm_num) (notEven_of_odd (val_one (p := 11) (k := 3) (by norm_num) (by norm_num) (by norm_num)))
theorem hbSimilar_33 : HBSimilar 33 := Erdos634.CaseA.RComposite.hbSimilar_of_sqfree17 sqfree_33 (by norm_num)
theorem caseB_33 : CaseBClosed 33 := caseB_of_sumsq 33 hbSimilar_33 nsq33
theorem caseR_33 : CaseRClosed 33 := caseR_of_odd 33 (by norm_num)
theorem gamma_33 : GammaTwoAlphaClosed 33 := Erdos634.Draft.CompositeFinal10.caseG_of_squarefree 33 sqfree_33

theorem noF3_33 : NoF3 33 := by
  intro s j hj hjs h
  push_cast at h
  have h1 : j ≤ 4 := by nlinarith
  have h2 : s ≤ 12 := by nlinarith
  interval_cases j <;> interval_cases s <;> omega

theorem noF2_33 : NoF2 33 := by
  apply noF2_of_int
  · intro z hz
    push_cast at hz
    have h1 : z ≤ 6 := by nlinarith
    have h2 : -6 ≤ z := by nlinarith
    interval_cases z <;> omega
  · intro x r hx hr h z hz
    push_cast at hz
    have hx7 : x ≤ 6 := by nlinarith
    have hr9 : r ≤ 9 := by nlinarith
    interval_cases x <;> interval_cases r <;>
      first
      | omega
      | (norm_num at hz
         have h1 : z ≤ 9 := by nlinarith
         have h2 : -9 ≤ z := by nlinarith
         interval_cases z <;> omega)

theorem noF4z_33 : NoF4z 33 := by
  apply noF4z_of_int
  intro x r hx hr h z hz
  have hx7 : x ≤ 6 := by nlinarith
  have hr9 : r ≤ 9 := by nlinarith
  interval_cases x <;> interval_cases r <;>
    first
    | omega
    | (norm_num at hz
       have h1 : z ≤ 9 := by nlinarith
       have h2 : -9 ≤ z := by nlinarith
       interval_cases z <;> omega)

theorem gapR8_33 : GapR8 33 := gapR8_of_arith2 33 noF2_33 noF3_33 noF4z_33

/-! ## N = 57 -/
theorem sqfree_57 : Squarefree (57 : ℕ) := by decide +kernel
theorem hari57 : HArith 57 := harith_of_bound (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem nsq57 : ¬ ∃ x y : ℕ, 57 = x ^ 2 + y ^ 2 := nsq 57 (by norm_num) (by decide)
theorem gapAcomp_57 : GapAcomp 57 := fun hS =>
  Erdos634.CaseA.RComposite.gapA_of_ell hS sqfree_57 (by norm_num) nsq57 hari57
    (ℓ := 19) (by norm_num) (by norm_num) (notEven_of_odd (val_one (p := 19) (k := 3) (by norm_num) (by norm_num) (by norm_num)))
theorem hbSimilar_57 : HBSimilar 57 := Erdos634.CaseA.RComposite.hbSimilar_of_sqfree17 sqfree_57 (by norm_num)
theorem caseB_57 : CaseBClosed 57 := caseB_of_sumsq 57 hbSimilar_57 nsq57
theorem caseR_57 : CaseRClosed 57 := caseR_of_odd 57 (by norm_num)
theorem gamma_57 : GammaTwoAlphaClosed 57 := Erdos634.Draft.CompositeFinal10.caseG_of_squarefree 57 sqfree_57

theorem noF3_57 : NoF3 57 := by
  intro s j hj hjs h
  push_cast at h
  have h1 : j ≤ 4 := by nlinarith
  have h2 : s ≤ 12 := by nlinarith
  interval_cases j <;> interval_cases s <;> omega

theorem noF2_57 : NoF2 57 := by
  apply noF2_of_int
  · intro z hz
    push_cast at hz
    have h1 : z ≤ 6 := by nlinarith
    have h2 : -6 ≤ z := by nlinarith
    interval_cases z <;> omega
  · intro x r hx hr h z hz
    push_cast at hz
    have hx7 : x ≤ 6 := by nlinarith
    have hr9 : r ≤ 9 := by nlinarith
    interval_cases x <;> interval_cases r <;>
      first
      | omega
      | (norm_num at hz
         have h1 : z ≤ 9 := by nlinarith
         have h2 : -9 ≤ z := by nlinarith
         interval_cases z <;> omega)

theorem noF4z_57 : NoF4z 57 := by
  apply noF4z_of_int
  intro x r hx hr h z hz
  have hx7 : x ≤ 6 := by nlinarith
  have hr9 : r ≤ 9 := by nlinarith
  interval_cases x <;> interval_cases r <;>
    first
    | omega
    | (norm_num at hz
       have h1 : z ≤ 9 := by nlinarith
       have h2 : -9 ≤ z := by nlinarith
       interval_cases z <;> omega)

theorem gapR8_57 : GapR8 57 := gapR8_of_arith2 57 noF2_57 noF3_57 noF4z_57

/-! ## N = 69 -/
theorem sqfree_69 : Squarefree (69 : ℕ) := by decide +kernel
theorem hari69 : HArith 69 := harith_of_bound (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem nsq69 : ¬ ∃ x y : ℕ, 69 = x ^ 2 + y ^ 2 := nsq 69 (by norm_num) (by decide)
theorem gapAcomp_69 : GapAcomp 69 := fun hS =>
  Erdos634.CaseA.RComposite.gapA_of_ell hS sqfree_69 (by norm_num) nsq69 hari69
    (ℓ := 23) (by norm_num) (by norm_num) (notEven_of_odd (val_one (p := 23) (k := 3) (by norm_num) (by norm_num) (by norm_num)))
theorem hbSimilar_69 : HBSimilar 69 := Erdos634.CaseA.RComposite.hbSimilar_of_sqfree17 sqfree_69 (by norm_num)
theorem caseB_69 : CaseBClosed 69 := caseB_of_sumsq 69 hbSimilar_69 nsq69
theorem caseR_69 : CaseRClosed 69 := caseR_of_odd 69 (by norm_num)
theorem gamma_69 : GammaTwoAlphaClosed 69 := Erdos634.Draft.CompositeFinal10.caseG_of_squarefree 69 sqfree_69

theorem noF3_69 : NoF3 69 := by
  intro s j hj hjs h
  push_cast at h
  have h1 : j ≤ 4 := by nlinarith
  have h2 : s ≤ 12 := by nlinarith
  interval_cases j <;> interval_cases s <;> omega

theorem noF2_69 : NoF2 69 := by
  apply noF2_of_int
  · intro z hz
    push_cast at hz
    have h1 : z ≤ 6 := by nlinarith
    have h2 : -6 ≤ z := by nlinarith
    interval_cases z <;> omega
  · intro x r hx hr h z hz
    push_cast at hz
    have hx7 : x ≤ 6 := by nlinarith
    have hr9 : r ≤ 9 := by nlinarith
    interval_cases x <;> interval_cases r <;>
      first
      | omega
      | (norm_num at hz
         have h1 : z ≤ 9 := by nlinarith
         have h2 : -9 ≤ z := by nlinarith
         interval_cases z <;> omega)

theorem noF4z_69 : NoF4z 69 := by
  apply noF4z_of_int
  intro x r hx hr h z hz
  have hx7 : x ≤ 6 := by nlinarith
  have hr9 : r ≤ 9 := by nlinarith
  interval_cases x <;> interval_cases r <;>
    first
    | omega
    | (norm_num at hz
       have h1 : z ≤ 9 := by nlinarith
       have h2 : -9 ≤ z := by nlinarith
       interval_cases z <;> omega)

theorem gapR8_69 : GapR8 69 := gapR8_of_arith2 69 noF2_69 noF3_69 noF4z_69

/-! ## S1 at N = 33, 69: the base-β route, N-uniform for squarefree N -/

/-- For squarefree `N`, every coprime solution of `N (p+q)² = M² (3q²−p²)` has `M = p+q`, provided `3q²−p² = 4N` has no
coprime solution with `0 < p < q`. -/
theorem s1_arith_gen (N : ℕ) (hsq : Squarefree N) (hN0 : 0 < N)
    (hfin : ∀ p q : ℤ, 0 < p → p < q → IsCoprime p q → 3 * q ^ 2 - p ^ 2 = 4 * (N : ℤ) → False) :
    ∀ p q M : ℤ, 0 < p → p < q → IsCoprime p q → 0 < M →
    (N : ℤ) * (p + q) ^ 2 = M ^ 2 * (3 * q ^ 2 - p ^ 2) → M = p + q := by
  intro p q M hp hpq hcop hM heq
  have hq0 : 0 < q := by omega
  have hY : 0 < 3 * q ^ 2 - p ^ 2 := by nlinarith
  have hs : 0 < p + q := by omega
  have hNz : (0 : ℤ) < N := by exact_mod_cast hN0
  have h1 : (N : ℤ) * (3 * q ^ 2 - p ^ 2) * (p + q) ^ 2 = (M * (3 * q ^ 2 - p ^ 2)) ^ 2 := by
    have : (N : ℤ) * (3 * q ^ 2 - p ^ 2) * (p + q) ^ 2 = (3 * q ^ 2 - p ^ 2) * ((N : ℤ) * (p + q) ^ 2) := by ring
    rw [this, heq]; ring
  have hdvd : (p + q) ^ 2 ∣ (M * (3 * q ^ 2 - p ^ 2)) ^ 2 :=
    ⟨N * (3 * q ^ 2 - p ^ 2), by rw [← h1]; ring⟩
  obtain ⟨w, hw⟩ := (Int.pow_dvd_pow_iff (two_ne_zero)).mp hdvd
  have hw2 : w ^ 2 = N * (3 * q ^ 2 - p ^ 2) := by
    have : (p + q) ^ 2 * w ^ 2 = (p + q) ^ 2 * (N * (3 * q ^ 2 - p ^ 2)) := by
      calc (p + q) ^ 2 * w ^ 2 = ((p + q) * w) ^ 2 := by ring
        _ = (M * (3 * q ^ 2 - p ^ 2)) ^ 2 := by rw [← hw]
        _ = (p + q) ^ 2 * (N * (3 * q ^ 2 - p ^ 2)) := by rw [← h1]; ring
    exact mul_left_cancel₀ (pow_ne_zero 2 hs.ne') this
  have hsqZ : Squarefree (N : ℤ) := Int.squarefree_natCast.mpr hsq
  have hNw : (N : ℤ) ∣ w :=
    (hsqZ.dvd_pow_iff_dvd two_ne_zero).mp ⟨3 * q ^ 2 - p ^ 2, by rw [hw2]⟩
  obtain ⟨u, hu⟩ := hNw
  have hYu : 3 * q ^ 2 - p ^ 2 = N * u ^ 2 := by
    have : (N : ℤ) * (3 * q ^ 2 - p ^ 2) = N * (N * u ^ 2) := by rw [← hw2, hu]; ring
    exact mul_left_cancel₀ hNz.ne' this
  have hu0 : u ≠ 0 := by
    rintro rfl; nlinarith
  have hMu : M * u = p + q := by
    have h4 : (N * u) * (M * u) = (N * u) * (p + q) := by
      have : M * (3 * q ^ 2 - p ^ 2) = (p + q) * w := hw
      rw [hYu, hu] at this; linear_combination this
    exact mul_left_cancel₀ (by intro h; rcases mul_eq_zero.mp h with h | h <;> [exact hNz.ne' h; exact hu0 h]) h4
  have hupos : 0 < u := by
    by_contra hc
    nlinarith
  have hcop_s : IsCoprime (p + q) p := Erdos634.Draft.CompositeFinal4.isCoprime_sum_left' hcop
  have hcop_up : IsCoprime u p := hcop_s.of_isCoprime_of_dvd_left ⟨M, by rw [← hMu]; ring⟩
  have hu_dvd : u ∣ 2 * p ^ 2 := ⟨N * u - 3 * (q - p) * M, by linear_combination hYu + 3 * (q - p) * hMu⟩
  have hu2 : u ∣ 2 := (hcop_up.pow_right (n := 2)).dvd_of_dvd_mul_right hu_dvd
  have hule : u ≤ 2 := Int.le_of_dvd (by norm_num) hu2
  have hu12 : u = 1 ∨ u = 2 := by omega
  rcases hu12 with rfl | rfl
  · linarith
  · exfalso
    exact hfin p q hp hpq hcop (by linarith)

theorem s1fin_33 : ∀ p q : ℤ, 0 < p → p < q → IsCoprime p q → 3 * q ^ 2 - p ^ 2 = 4 * ((33:ℕ) : ℤ) → False := by
  intro p q hp hpq hcop h
  push_cast at h
  have hq1 : 2 ≤ q := by omega
  have hq : q ≤ 9 := by nlinarith
  have hg := Int.isCoprime_iff_gcd_eq_one.mp hcop
  interval_cases q <;> interval_cases p <;> first | omega | (norm_num at hg)

theorem s1Closed_33 : S1Closed 33 := by
  intro D α β a b c r hα hrel hmod har hbr htgt
  exact not_baseBetaTiled
    (Erdos634.Draft.CompositeFinal4.s1_baseBetaTiled_of_arith 33 (s1_arith_gen 33 sqfree_33 (by norm_num) s1fin_33) D α β a b c r hα hrel hmod har hbr htgt)

theorem s1fin_69 : ∀ p q : ℤ, 0 < p → p < q → IsCoprime p q → 3 * q ^ 2 - p ^ 2 = 4 * ((69:ℕ) : ℤ) → False := by
  intro p q hp hpq hcop h
  push_cast at h
  have hq1 : 2 ≤ q := by omega
  have hq : q ≤ 12 := by nlinarith
  have hg := Int.isCoprime_iff_gcd_eq_one.mp hcop
  interval_cases q <;> interval_cases p <;> first | omega | (norm_num at hg)

theorem s1Closed_69 : S1Closed 69 := by
  intro D α β a b c r hα hrel hmod har hbr htgt
  exact not_baseBetaTiled
    (Erdos634.Draft.CompositeFinal4.s1_baseBetaTiled_of_arith 69 (s1_arith_gen 69 sqfree_69 (by norm_num) s1fin_69) D α β a b c r hα hrel hmod har hbr htgt)

theorem s1Closed_21 : S1Closed 21 :=
  s1Closed_of_qnr 21 7 (by norm_num) (val_one (p := 7) (k := 3) (by norm_num) (by norm_num) (by norm_num)) qnr3_7_f11
theorem s1Closed_57 : S1Closed 57 :=
  s1Closed_of_qnr 57 19 (by norm_num) (val_one (p := 19) (k := 3) (by norm_num) (by norm_num) (by norm_num)) qnr3_19_f11

/-! ## S2 -/
theorem s2Closed_57 : S2Closed 57 :=
  s2Closed_of_qnr 57 19 (by norm_num) (val_one (p := 19) (k := 3) (by norm_num) (by norm_num) (by norm_num)) qnr2_19_f11 qnr3_19_f11
theorem s2Arith_21 : S2Arith 21 := by
  refine Erdos634.Draft.CompositeS2Global.s2Arith_of_dvd 21 (by norm_num) ?_
  intro p q hp hpq hq hd S heq
  have hq1 : 1 < q := by omega
  have hq' : q ≤ 9 := by push_cast at hq; by_contra h; push Not at h; nlinarith
  interval_cases q <;> interval_cases p <;>
    first | (revert hd; norm_num; done) | (revert heq; generalize S ^ 2 = T; norm_num; omega)
theorem s2Closed_21 : S2Closed 21 := s2Closed_of_arith 21 s2Arith_21

theorem s2Arith_33 : S2Arith 33 := by
  refine Erdos634.Draft.CompositeS2Global.s2Arith_of_dvd 33 (by norm_num) ?_
  intro p q hp hpq hq hd S heq
  have hq1 : 1 < q := by omega
  have hq' : q ≤ 11 := by push_cast at hq; by_contra h; push Not at h; nlinarith
  interval_cases q <;> interval_cases p <;>
    first | (revert hd; norm_num; done) | (revert heq; generalize S ^ 2 = T; norm_num; omega)
theorem s2Closed_33 : S2Closed 33 := s2Closed_of_arith 33 s2Arith_33

theorem s2Arith_69 : S2Arith 69 := by
  refine Erdos634.Draft.CompositeS2Global.s2Arith_of_dvd 69 (by norm_num) ?_
  intro p q hp hpq hq hd S heq
  have hq1 : 1 < q := by omega
  have hq' : q ≤ 16 := by push_cast at hq; by_contra h; push Not at h; nlinarith
  interval_cases q <;> interval_cases p <;>
    first | (revert hd; norm_num; done) | (revert heq; generalize S ^ 2 = T; norm_num; omega)
theorem s2Closed_69 : S2Closed 69 := s2Closed_of_arith 69 s2Arith_69

theorem isoQRef_33 : IsoQRef 33 := isoQRef_of_check 33 (by norm_num) (by norm_num) (by decide +kernel)
theorem isoQRef_57 : IsoQRef 57 := isoQRef_of_check 57 (by norm_num) (by norm_num) (by decide +kernel)
theorem isoQRef_69 : IsoQRef 69 := isoQRef_of_check 69 (by norm_num) (by norm_num) (by decide +kernel)
theorem isoH9b_21 : IsoH9b 21 := isoH9b_of_check 21 (by norm_num) (by decide +kernel)
theorem isoH9b_57 : IsoH9b 57 := isoH9b_of_check 57 (by norm_num) (by decide +kernel)
theorem isoH9b_69 : IsoH9b 69 := isoH9b_of_check 69 (by norm_num) (by decide +kernel)

/-- N = 21: the reduced Row-11 equation HAS an arithmetic solution `(e, d, m) = (1, 1, 1)`, `Q = 7`, `21·1 = 1²·3·7`
(the base-α member `(2,3,4)` on the target `(12,12,21)`); `IsoQRef 21` is FALSE. -/
theorem not_isoQRef_21 : ¬ IsoQRef 21 := fun h => h 1 1 1 (by norm_num) (by norm_num) (by decide) (by norm_num)

/-- N = 33: `IsoH9b 33` is FALSE: `(a, b, c, k, nA) = (5, 3, 7, 3, −1)`, `e = a+2b = 11 ∣ 33`, `b·33 = 9·11`,
`3·(7−5−3) = −1·3`, `−1 ≡ 33 (mod 2)` (the sporadic 2π/3 tile `(5,3,7)` on the target `(21,21,33)`). -/
theorem not_isoH9b_33 : ¬ IsoH9b 33 := fun h =>
  h 5 3 7 3 (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [Int.isCoprime_iff_gcd_eq_one]; decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ## Conditional dispatch -/

/-- **N = 21, modulo `S3Closed 21`, `GapE60 21`, `GapE120 21`, `GapF1 21`.** -/
theorem chain_cond_21 (gS3 : S3Closed 21) (gE60 : GapE60 21) (gE120 : GapE120 21) (gF1 : GapF1 21) (D : CongruentDissection 21) : False :=
  chain_gen3 21 sqfree_21 s1Closed_21 s2Closed_21 gS3 isoH9b_21 gapAcomp_21 caseB_21 caseR_21 gamma_21 gE60 gE120 gF1 gapR8_21 D
/-- **N = 57, modulo `GapE60 57`, `GapE120 57`, `GapF1 57`.** -/
theorem chain_cond_57 (gE60 : GapE60 57) (gE120 : GapE120 57) (gF1 : GapF1 57) (D : CongruentDissection 57) : False :=
  chain_gen3 57 sqfree_57 s1Closed_57 s2Closed_57 (s3Closed_of_isoQRef 57 isoQRef_57) isoH9b_57 gapAcomp_57 caseB_57 caseR_57 gamma_57 gE60 gE120 gF1 gapR8_57 D
/-- **N = 69, modulo `GapE60 69`, `GapE120 69`, `GapF1 69`.** -/
theorem chain_cond_69 (gE60 : GapE60 69) (gE120 : GapE120 69) (gF1 : GapF1 69) (D : CongruentDissection 69) : False :=
  chain_gen3 69 sqfree_69 s1Closed_69 s2Closed_69 (s3Closed_of_isoQRef 69 isoQRef_69) isoH9b_69 gapAcomp_69 caseB_69 caseR_69 gamma_69 gE60 gE120 gF1 gapR8_69 D

end Erdos634.Draft.CompositeFinal11
#print axioms Erdos634.Draft.CompositeFinal11.sqfree_21
#print axioms Erdos634.Draft.CompositeFinal11.hari33
#print axioms Erdos634.Draft.CompositeFinal11.gapAcomp_69
#print axioms Erdos634.Draft.CompositeFinal11.gamma_57
#print axioms Erdos634.Draft.CompositeFinal11.gapR8_21
#print axioms Erdos634.Draft.CompositeFinal11.gapR8_33
#print axioms Erdos634.Draft.CompositeFinal11.gapR8_57
#print axioms Erdos634.Draft.CompositeFinal11.gapR8_69
#print axioms Erdos634.Draft.CompositeFinal11.s1Closed_33
#print axioms Erdos634.Draft.CompositeFinal11.s1Closed_69
#print axioms Erdos634.Draft.CompositeFinal11.s2Closed_21
#print axioms Erdos634.Draft.CompositeFinal11.s2Closed_33
#print axioms Erdos634.Draft.CompositeFinal11.s2Closed_69
#print axioms Erdos634.Draft.CompositeFinal11.isoQRef_33
#print axioms Erdos634.Draft.CompositeFinal11.isoH9b_57
#print axioms Erdos634.Draft.CompositeFinal11.chain_cond_21
#print axioms Erdos634.Draft.CompositeFinal11.chain_cond_57
#print axioms Erdos634.Draft.CompositeFinal11.chain_cond_69
#print axioms Erdos634.Draft.CompositeFinal11.not_isoQRef_21
#print axioms Erdos634.Draft.CompositeFinal11.not_isoH9b_33
