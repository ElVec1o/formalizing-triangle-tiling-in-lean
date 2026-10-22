-- Draft/CaseACompositeE.lean — Case A at composite N for squarefree N with `7 ≤ N ∧ (17 ≤ N ∨ N % 4 = 2)`: copy of
-- `CaseAComposite.r0c_coreC / gapA_of_ell` with the Similar exit supplied by `Row2.theoremS_perm_sqfreeE` (covers N = 14).
-- UNAUDITED.  Formalization debt; NOT progress on the three /goal outcomes.  No sorry, no native_decide.
import Erdos634.Draft.CaseAComposite
import Erdos634.Draft.FluxERow2SqfreeEven

open scoped BigOperators

namespace Erdos634.CaseA.RCompositeE

open Erdos634.Geometry Erdos634.LemmaS Erdos634.LemmaKStar Erdos634.LemmaF Erdos634.KConj
open Erdos634.CaseA.R0c
open Erdos634.Geometry.CaseA.LemmaV (lemmaV nat_bounds angle_pos angle_lt_pi)
open Erdos634.Geometry.CaseA.LemmaH (HArith lemmaH_N harith_38 harith_86)

variable {N : ℕ}

/-- `r0c_core15` generalised: Lemma S at `(n, a)` (via a prime ≥ 7 dividing n), N squarefree ≥ 17 not a sum of two
squares, `HArith N`  ⇒  False. -/
theorem r0c_coreE (D : CongruentDissection N) (hsqf : Squarefree N) (h7 : 7 ≤ N) (h17 : 17 ≤ N ∨ N % 4 = 2)
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
    exact hns (Row2.theoremS_perm_sqfreeE D μ τ hsim' hsqf h7 h17)
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
theorem gapA_of_ellE (hS : LemmaSStatement) (hsqf : Squarefree N) (h7 : 7 ≤ N) (h17 : 17 ≤ N ∨ N % 4 = 2)
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
  exact r0c_coreE D hsqf h7 h17 hns hAr hn a ha (hS n a hpos hsum hgcd ℓ hℓ hℓ7 hℓn)
    (hℓ7.trans (Nat.le_of_dvd hn hℓn))


end Erdos634.CaseA.RCompositeE

#print axioms Erdos634.CaseA.RCompositeE.r0c_coreE
#print axioms Erdos634.CaseA.RCompositeE.gapA_of_ellE
