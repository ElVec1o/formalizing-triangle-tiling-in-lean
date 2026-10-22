-- Draft/CaseAN15.lean — GapA at N = 15, step A1: Case A with n having a prime factor ≥ 7 (Lemma S applies) at N = 15,
-- conditional on `LemmaH15` (the half-isosceles exit, being ported separately as `lemmaH_15`).  Copy of
-- CaseAR0c.r0c_core with: no Lemma V/primality; similar exit by `Row2.theoremS_perm_sqfree`.  The residual
-- `GapA2` (all prime factors of n are 2, 3, 5) is the OPEN 5-smooth case (Lemma S').  UNAUDITED.
import Erdos634.Draft.CaseAR0c
import Erdos634.Draft.LemmaSAll
import Erdos634.Draft.FluxERow2Sqfree
import Erdos634.Draft.Chain15F1

open scoped BigOperators

namespace Erdos634.CaseA.R0c15

open Erdos634.Geometry Erdos634.LemmaS Erdos634.LemmaKStar Erdos634.LemmaF Erdos634.KConj
open Erdos634.CaseA.R0c
open Erdos634.Geometry.CaseA.LemmaV (lemmaV_prime nat_bounds angle_pos angle_lt_pi)

variable {N : ℕ}

/-- The half-isosceles exit at N = 15 (statement of `CaseA.LemmaH.lemmaH` at N = 15 with conclusion False). -/
def LemmaH15 : Prop :=
  ∀ (D : CongruentDissection 15) {θ : ℝ}, (∃ q : ℚ, θ = q * Real.pi) → 0 < θ → θ < Real.pi / 2 →
    ∀ {p q : Fin 3}, p ≠ q → D.model.angleAt p = θ → D.model.angleAt q = Real.pi / 2 →
      ∀ {i j : Fin 3}, i ≠ j → D.target.angleAt i = θ → D.target.angleAt j = θ → False

/-- The 5-smooth residue of Case A at N = 15: every prime factor of the exact angle denominator is ≤ 5. -/
def GapA2 : Prop :=
  ∀ (D : CongruentDissection 15) (n : ℕ) (a : Fin 3 → ℕ), 0 < n →
    Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → (∀ k, D.model.angleAt k = a k * Real.pi / n) →
    (∀ p : ℕ, p.Prime → p ∣ n → p < 7) → False

theorem r0c_core15 (D : CongruentDissection N) (hN : N = 15) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n)
    (hSn : relSpace n a = trivSpace n a) (hn7 : 7 ≤ n) (hH : LemmaH15) : False := by
  have hsqf : Squarefree N := by rw [hN]; decide +kernel
  have h7N : 7 ≤ N := by omega
  have h4N : N % 4 = 3 := by omega
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
  · -- ABC ~ T: row 2's Theorem S
    obtain ⟨τ, hτ⟩ := perm_of_counts (uu a f) a hsim
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
    have := Row2.theoremS_perm_sqfree D μ τ hsim' hsqf h7N
    omega
  · -- half-isosceles: Lemma H
    have hlt : 2 * a l < n := by
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
    subst hN
    exact hH D hq hθ0 hθ2 hlk (ha l) hmk hj hi hj'


theorem gapA_fifteen_of_A2 (hH : LemmaH15) (A2 : GapA2) : Erdos634.Draft.Chain15.GapA 15 := by
  intro D hrat
  obtain ⟨n₀, hn₀, a₀, ha₀⟩ := exists_nat_angles D.model hrat
  obtain ⟨n, hn, a, hgcd, ha⟩ := exists_primitive D.model hn₀ a₀ ha₀
  have hsum := sum_of_angles hn ha
  have hpos : ∀ i, 0 < a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  by_cases hp : ∃ p : ℕ, p.Prime ∧ 7 ≤ p ∧ p ∣ n
  · obtain ⟨p, hpp, hp7, hpn⟩ := hp
    exact r0c_core15 D rfl hn a ha (Erdos634.LemmaSAll.lemmaS n a hpos hsum hgcd p hpp hp7 hpn)
      (hp7.trans (Nat.le_of_dvd hn hpn)) hH
  · push Not at hp
    exact A2 D n a hn hgcd ha (fun p hpp hpn => by
      by_contra hlt; push Not at hlt; exact absurd hpn (hp p hpp hlt))

end Erdos634.CaseA.R0c15

#print axioms Erdos634.CaseA.R0c15.gapA_fifteen_of_A2
