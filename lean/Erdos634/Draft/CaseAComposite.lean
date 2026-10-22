-- Draft/CaseAComposite.lean — Case A (all angles in ℚπ) at COMPOSITE tile count N: `GapAcomp 38`, `GapAcomp 86`.
-- UNAUDITED.  Formalization debt; NOT progress on the three /goal outcomes.  No `sorry`, no `native_decide`.
--
-- Generalisation of `CaseAN15.r0c_core15` (N = 15) to squarefree N ≥ 17 with an odd-valuation prime ℓ ≥ 7.
-- What used primality of N / N ≡ 3 (mod 4) in `CaseAR0c.r0c_core`, and what replaces it here:
--   * Lemma V `lemmaV_prime` (N ∣ n, prime N)       → general `LemmaV.lemmaV` (v_ℓ(N) even for prime ℓ ∤ 2n):
--                                                    ℓ with odd v_ℓ(N) divides n.  (a) N-free argument.
--   * Lemma S with p = N                             → p = ℓ (ℓ ∣ n, ℓ ≥ 7).  (a)
--   * Similar exit `Row2.theoremS_perm` (N prime)    → `Row2.theoremS_perm_sqfree17` (NEW, FluxERow2Sqfree17):
--                                                    squarefree N ≥ 17 ⇒ N = x²+y²; then N ≠ x²+y² at 38, 86.  (a)
--   * Lemma H exit `lemmaH` (N prime ≥ 5)            → `LemmaH.lemmaH_N` (NEW, CaseALemmaHN) with `HArith N`,
--                                                    six bounded non-solution checks, `decide` at 38, 86.  (b)
-- No residual hypothesis remains except Lemma S itself (`LemmaSStatement`, the premise of `GapAcomp`, proved in
-- Lean as `LemmaSAll.lemmaS`).
import Erdos634.Draft.CaseAN15
import Erdos634.Draft.CaseALemmaHN
import Erdos634.Draft.FluxERow2Sqfree17
import Erdos634.Draft.ChainComposite

open scoped BigOperators

namespace Erdos634.CaseA.RComposite

open Erdos634.Geometry Erdos634.LemmaS Erdos634.LemmaKStar Erdos634.LemmaF Erdos634.KConj
open Erdos634.CaseA.R0c
open Erdos634.Geometry.CaseA.LemmaV (lemmaV nat_bounds angle_pos angle_lt_pi)
open Erdos634.Geometry.CaseA.LemmaH (HArith lemmaH_N harith_38 harith_86)

variable {N : ℕ}

/-- `r0c_core15` generalised: Lemma S at `(n, a)` (via a prime ≥ 7 dividing n), N squarefree ≥ 17 not a sum of two
squares, `HArith N`  ⇒  False. -/
theorem r0c_coreC (D : CongruentDissection N) (hsqf : Squarefree N) (h17 : 17 ≤ N)
    (hns : ¬ ∃ x y : ℕ, N = x ^ 2 + y ^ 2) (hAr : HArith N)
    {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n)
    (hSn : relSpace n a = trivSpace n a) (hn7 : 7 ≤ n) : False := by
  obtain ⟨idx, hidx⟩ := exists_idx D a ha
  obtain ⟨hf, hK⟩ := lemmaK D hn a ha idx hidx
  set f := fig D idx
  have hsum := sum_of_angles hn ha
  have hsu := sum_of_angles hn hf
  have ha1 : ∀ i, 1 ≤ a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  have hu1 : ∀ j, 1 ≤ uu a f j := fun j =>
    (nat_bounds hn (hf j) (angle_pos _ j) (angle_lt_pi _ j)).1
  have hfne : ∀ j, f j ≠ 0 := by
    intro j h
    have := hu1 j
    rw [uu, h] at this; simp at this
  have hshape := shapes_of_K (by omega) ha1 hsum hfne hsu hSn hK
  rcases hshape with hsim | ⟨k, l, hk, hlk, j₁, j₂, hj, h1, h2⟩
  · obtain ⟨τ, hτ⟩ := perm_of_counts (uu a f) a hsim
    have hang : ∀ j, D.target.angleAt j = D.model.angleAt (τ j) := by
      intro j; rw [hf j, ha (τ j), hτ j]
    set μ := A1Field.circD D.target / A1Field.circD D.model
    have hcm := (A1Field.circD_pos D.model).ne'
    have hsim' : ∀ j, D.target.angleAt j = D.model.angleAt (τ j) ∧
        D.target.oppLen j = μ * D.model.oppLen (τ j) := by
      intro j
      refine ⟨hang j, ?_⟩
      rw [A1Field.oppLen_eq D.target j, A1Field.oppLen_eq D.model (τ j), hang j]
      simp only [μ]; field_simp
    exact hns (Row2.theoremS_perm_sqfree17 D μ τ hsim' hsqf h17)
  · have hlt : 2 * a l < n := by
      rw [Fin.sum_univ_three] at hsum
      have := ha1 0; have := ha1 1; have := ha1 2
      fin_cases k <;> fin_cases l <;> simp at hk hlk ⊢ <;> omega
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hθ0 : 0 < (a l : ℝ) * Real.pi / n := by
      have : (0 : ℝ) < a l := by exact_mod_cast ha1 l
      positivity
    have hθ2 : (a l : ℝ) * Real.pi / n < Real.pi / 2 := by
      rw [div_lt_div_iff₀ hn' (by norm_num : (0 : ℝ) < 2)]
      have : (2 * a l : ℝ) < n := by exact_mod_cast hlt
      nlinarith [Real.pi_pos]
    have hq : ∃ q : ℚ, (a l : ℝ) * Real.pi / n = q * Real.pi :=
      ⟨(a l : ℚ) / n, by push_cast; ring⟩
    have hmk : D.model.angleAt k = Real.pi / 2 := by
      rw [ha k]
      have : (2 * a k : ℝ) = n := by exact_mod_cast hk
      field_simp; linarith
    have hi : D.target.angleAt j₁ = (a l : ℝ) * Real.pi / n := by rw [hf j₁, h1]
    have hj' : D.target.angleAt j₂ = (a l : ℝ) * Real.pi / n := by rw [hf j₂, h2]
    exact lemmaH_N hAr D hq hθ0 hθ2 hlk (ha l) hmk hj hi hj'

/-- Case A at squarefree `N ≥ 17`, not a sum of two squares, `HArith N`, with a prime `ℓ ≥ 7` of odd valuation in
`N`: given Lemma S, every dissection with rational-angle tile is impossible. -/
theorem gapA_of_ell (hS : LemmaSStatement) (hsqf : Squarefree N) (h17 : 17 ≤ N)
    (hns : ¬ ∃ x y : ℕ, N = x ^ 2 + y ^ 2) (hAr : HArith N)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ7 : 7 ≤ ℓ) (hodd : ¬ Even (padicValNat ℓ N)) :
    Erdos634.Draft.Chain15.GapA N := by
  intro D hrat
  obtain ⟨n₀, hn₀, a₀, ha₀⟩ := exists_nat_angles D.model hrat
  obtain ⟨n, hn, a, hgcd, ha⟩ := exists_primitive D.model hn₀ a₀ ha₀
  have hsum := sum_of_angles hn ha
  have hpos : ∀ i, 0 < a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  have hℓn : ℓ ∣ n := by
    have h2n : ℓ ∣ 2 * n := by
      by_contra h
      exact hodd (lemmaV D hn a ha hℓ h)
    rcases (Nat.Prime.dvd_mul hℓ).mp h2n with h | h
    · have := Nat.le_of_dvd (by norm_num) h; omega
    · exact h
  exact r0c_coreC D hsqf h17 hns hAr hn a ha (hS n a hpos hsum hgcd ℓ hℓ hℓ7 hℓn)
    (hℓ7.trans (Nat.le_of_dvd hn hℓn))

/-- The paper's similar-tile N-form `HBSimilar N` for squarefree `N ≥ 17`
(`Row2.theoremS_perm_sqfree17`). -/
theorem hbSimilar_of_sqfree17 (hsqf : Squarefree N) (h17 : 17 ≤ N) :
    Erdos634.Draft.ChainComposite.HBSimilar N :=
  fun D μ τ hs => Row2.theoremS_perm_sqfree17 D μ τ hs hsqf h17

/-! ## N = 38 and N = 86 -/

theorem sqfree_38' : Squarefree (38 : ℕ) := by decide +kernel
theorem sqfree_86' : Squarefree (86 : ℕ) := by decide +kernel

theorem not_sumsq_38' : ¬ ∃ x y : ℕ, 38 = x ^ 2 + y ^ 2 := by
  rintro ⟨x, y, h⟩
  have hx : x ≤ 6 := by nlinarith
  have hy : y ≤ 6 := by nlinarith
  interval_cases x <;> interval_cases y <;> omega

theorem not_sumsq_86' : ¬ ∃ x y : ℕ, 86 = x ^ 2 + y ^ 2 := by
  rintro ⟨x, y, h⟩
  have hx : x ≤ 9 := by nlinarith
  have hy : y ≤ 9 := by nlinarith
  interval_cases x <;> interval_cases y <;> omega

theorem notEven_val19_38 : ¬ Even (padicValNat 19 38) := by
  haveI : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  have : padicValNat 19 38 = 1 := by
    have h : padicValNat 19 38 = padicValNat 19 (19 * 2) := by norm_num
    rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat_self,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  rw [this]; exact Nat.not_even_one

theorem notEven_val43_86 : ¬ Even (padicValNat 43 86) := by
  haveI : Fact (Nat.Prime 43) := ⟨by norm_num⟩
  have : padicValNat 43 86 = 1 := by
    have h : padicValNat 43 86 = padicValNat 43 (43 * 2) := by norm_num
    rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat_self,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  rw [this]; exact Nat.not_even_one

/-- **Case A at N = 38** (the premise `LemmaSStatement` is Lean-proved: `LemmaSAll.lemmaS`). -/
theorem gapAcomp_38 : Erdos634.Draft.ChainComposite.GapAcomp 38 := fun hS =>
  gapA_of_ell hS sqfree_38' (by norm_num) not_sumsq_38' harith_38 (by norm_num) (by norm_num) notEven_val19_38

/-- **Case A at N = 86.** -/
theorem gapAcomp_86 : Erdos634.Draft.ChainComposite.GapAcomp 86 := fun hS =>
  gapA_of_ell hS sqfree_86' (by norm_num) not_sumsq_86' harith_86 (by norm_num) (by norm_num) notEven_val43_86

/-- Unconditional form (Lemma S supplied from `LemmaSAll.lemmaS`). -/
theorem gapA_38 : Erdos634.Draft.Chain15.GapA 38 := gapAcomp_38 Erdos634.LemmaSAll.lemmaS
theorem gapA_86 : Erdos634.Draft.Chain15.GapA 86 := gapAcomp_86 Erdos634.LemmaSAll.lemmaS

/-- Bonus: the cited `HBSimilar` is a THEOREM at 38 and 86. -/
theorem hbSimilar_38 : Erdos634.Draft.ChainComposite.HBSimilar 38 :=
  hbSimilar_of_sqfree17 sqfree_38' (by norm_num)
theorem hbSimilar_86 : Erdos634.Draft.ChainComposite.HBSimilar 86 :=
  hbSimilar_of_sqfree17 sqfree_86' (by norm_num)

end Erdos634.CaseA.RComposite

#print axioms Erdos634.CaseA.RComposite.r0c_coreC
#print axioms Erdos634.CaseA.RComposite.gapA_of_ell
#print axioms Erdos634.CaseA.RComposite.gapAcomp_38
#print axioms Erdos634.CaseA.RComposite.gapAcomp_86
#print axioms Erdos634.CaseA.RComposite.gapA_38
#print axioms Erdos634.CaseA.RComposite.gapA_86
#print axioms Erdos634.CaseA.RComposite.hbSimilar_38
#print axioms Erdos634.CaseA.RComposite.hbSimilar_86
