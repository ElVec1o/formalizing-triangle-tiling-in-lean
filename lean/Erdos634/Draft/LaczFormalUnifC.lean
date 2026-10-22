-- Draft/LaczFormalUnifC.lean -- THE TOTAL CLASSIFICATION.  `l9_uniform` (L9 for every n > 200 whose prime factors are <= 5, no certificates) and
-- `classify_total`: for ANY tile with angles a_k pi/n (gcd 1, any n >= 1), any N, reflections allowed: SimilarTM, or right tile + isosceles target with an acute tile angle as
-- base angle, or one of the three valid n = 6 shapes.  Coverage: n with a prime factor >= 7 (`l9_generic`), 5-smooth n <= 200 (certificates and exceptional tables of
-- `LaczFormalClassifyFinal3`), 5-smooth n > 200 (`shapes_of_K_uniform`).  UNAUDITED (NOTE).
-- Credit: Laczkovich (Discrete Math 140 (1995) Thm 5.1/5.3, Lemma 5.2; DCG 48 (2012) Thm 3.3), Beeson-Rosu, Beeson, Beeson-Zhang.
import Erdos634.Draft.LaczFormalClassifyFinal3
import Erdos634.Draft.LaczFormalUnifB

open scoped BigOperators Classical
open Erdos634.Geometry Erdos634.LemmaS Erdos634.LemmaKStar Erdos634.LemmaF Erdos634.KConj
  Erdos634.CaseA.R0c Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
open Erdos634.Geometry.CaseA.LemmaV (lemmaV_prime nat_bounds angle_pos angle_lt_pi)

namespace Erdos634.Draft.LaczFormal

/-- **L9 for large smooth n, uniformly.** -/
theorem l9_uniform {N : ℕ} (D : CongruentDissection N) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (h200 : 200 < n) (hsm : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ℓ ≤ 5) :
    SimilarTM D ∨
      ∃ k l : Fin 3, l ≠ k ∧ D.model.angleAt k = Real.pi / 2 ∧
        ∃ j₁ j₂ : Fin 3, j₁ ≠ j₂ ∧ D.target.angleAt j₁ = D.model.angleAt l ∧
          D.target.angleAt j₂ = D.model.angleAt l := by
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
  rcases shapes_of_K_uniform h200 hsm ha1 hsum hgcd hfne hsu hK with hsim | ⟨k, l, hk, hlk, j₁, j₂, hj, h1, h2⟩
  · left
    obtain ⟨τ, hτ⟩ := perm_of_counts (uu a f) a hsim
    have hang : ∀ j, D.target.angleAt j = D.model.angleAt (τ j) := by
      intro j; rw [hf j, ha (τ j), hτ j]
    set μ := A1Field.circD D.target / A1Field.circD D.model
    have hcm := (A1Field.circD_pos D.model).ne'
    refine ⟨μ, τ, fun j => ⟨hang j, ?_⟩⟩
    rw [A1Field.oppLen_eq D.target j, A1Field.oppLen_eq D.model (τ j), hang j]
    simp only [μ]; field_simp
  · right
    have hmk : D.model.angleAt k = Real.pi / 2 := by
      rw [ha k]
      have : (2 * a k : ℝ) = n := by exact_mod_cast hk
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp; linarith
    refine ⟨k, l, hlk, hmk, j₁, j₂, hj, ?_, ?_⟩
    · rw [hf j₁, h1, ha l]
    · rw [hf j₂, h2, ha l]

theorem covered3_of_smooth_le200 {n : ℕ} (h3 : 3 ≤ n) (h200 : n ≤ 200) (hsm : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ℓ ≤ 5) :
    Covered3 n := by
  have hmem := smooth_le200 (n := n) (by omega) h3 (fun ℓ hℓ hd => by
    have := hsm ℓ (primes7_prime ℓ hℓ) hd
    simp only [primes7, List.mem_cons, List.not_mem_nil, or_false] at hℓ
    omega)
  simp only [smoothList, List.mem_cons, List.not_mem_nil, or_false] at hmem
  have := hmem
  unfold Covered3 Covered CertN2 CertN CertN3
  rcases this with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h <;> simp

/-- **TOTAL CLASSIFICATION of tilings with commensurable-angle tiles** (any denominator `n`). -/
theorem classify_total {N : ℕ} (D : CongruentDissection N) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) :
    SimilarTM D ∨ (∃ k l : Fin 3, l ≠ k ∧ D.model.angleAt k = Real.pi / 2 ∧
        ∃ j₁ j₂ : Fin 3, j₁ ≠ j₂ ∧ D.target.angleAt j₁ = D.model.angleAt l ∧
          D.target.angleAt j₂ = D.model.angleAt l) ∨ ExcPair3 D := by
  have hsum := Erdos634.CaseA.R0c.sum_of_angles hn ha
  have ha1 : ∀ i, 1 ≤ a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  have hn3 : 3 ≤ n := by
    rw [Fin.sum_univ_three] at hsum
    have := ha1 0; have := ha1 1; have := ha1 2; omega
  by_cases hsm : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ℓ ≤ 5
  · by_cases h200 : n ≤ 200
    · exact classify_commensurable_final3 D hn a ha hgcd (covered3_of_smooth_le200 hn3 h200 hsm)
    · push_neg at h200
      rcases l9_uniform D hn a ha hgcd h200 hsm with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  · push_neg at hsm
    obtain ⟨ℓ, hℓ, hdl, h5⟩ := hsm
    have h7 : 7 ≤ ℓ := by
      by_contra h
      have : ℓ = 6 := by have := hℓ.two_le; omega
      subst this; exact absurd hℓ (by norm_num)
    exact classify_commensurable_final3 D hn a ha hgcd (Or.inl (Or.inl ⟨ℓ, hℓ, h7, hdl⟩))

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.l9_uniform
#print axioms Erdos634.Draft.LaczFormal.classify_total
