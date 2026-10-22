-- Draft/LaczFormalR2.lean -- stage R2 (part 2): `l9_of_S` (the body of `l9_generic` with `relSpace n a = trivSpace n a` as hypothesis) and its instances
-- for the 5-smooth n certified in `LaczFormalR2Cert`.  UNAUDITED.  Credit: Laczkovich (1995, Thm 5.1/5.3), Beeson-Rosu Thm 4.
import Erdos634.Draft.LaczFormalR2Cert
import Erdos634.Draft.LaczFormalL9Gen

open scoped BigOperators Classical
open Erdos634.Geometry Erdos634.LemmaS Erdos634.LemmaKStar Erdos634.LemmaF Erdos634.KConj
  Erdos634.CaseA.R0c Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
open Erdos634.Geometry.CaseA.LemmaV (lemmaV_prime nat_bounds angle_pos angle_lt_pi)

namespace Erdos634.Draft.LaczFormal

/-- **L9 from Lemma S's conclusion as a hypothesis** (`relSpace n a = trivSpace n a`): any `n` for which that holds, e.g. by `LemmaSAll.lemmaS`
(prime >= 7 divides n) or by the kernel certificates `allCert n` (`LaczFormalR2Cert`). -/
theorem l9_of_S {N : ℕ} (D : CongruentDissection N) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (hS : relSpace n a = trivSpace n a) :
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
  have hn3 : 3 ≤ n := by
    rw [Fin.sum_univ_three] at hsum
    have := ha1 0; have := ha1 1; have := ha1 2; omega
  rcases shapes_of_K hn3 ha1 hsum hfne hsu hS hK with hsim | ⟨k, l, hk, hlk, j₁, j₂, hj, h1, h2⟩
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


/-- Certified smooth denominators. -/
def CertN (n : ℕ) : Prop := n = 9 ∨ n = 15 ∨ n = 16 ∨ n = 20 ∨ n = 25 ∨ n = 27 ∨ n = 32 ∨ n = 36 ∨ n = 40 ∨
  n = 45 ∨ n = 48 ∨ n = 50 ∨ n = 54 ∨ n = 64 ∨ n = 72 ∨ n = 75

theorem lemmaS_smooth {n : ℕ} (hn : CertN n) (a : Fin 3 → ℕ) (hpos : ∀ i, 0 < a i) (hsum : ∑ i, a i = n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) : relSpace n a = trivSpace n a := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact of_allCert allCert_9 a hpos hsum hgcd
  · exact of_allCert allCert_15 a hpos hsum hgcd
  · exact of_allCert allCert_16 a hpos hsum hgcd
  · exact of_allCert allCert_20 a hpos hsum hgcd
  · exact of_allCert allCert_25 a hpos hsum hgcd
  · exact of_allCert allCert_27 a hpos hsum hgcd
  · exact of_allCert allCert_32 a hpos hsum hgcd
  · exact of_allCert allCert_36 a hpos hsum hgcd
  · exact of_allCert allCert_40 a hpos hsum hgcd
  · exact of_allCert allCert_45 a hpos hsum hgcd
  · exact of_allCert allCert_48 a hpos hsum hgcd
  · exact of_allCert allCert_50 a hpos hsum hgcd
  · exact of_allCert allCert_54 a hpos hsum hgcd
  · exact of_allCert allCert_64 a hpos hsum hgcd
  · exact of_allCert allCert_72 a hpos hsum hgcd
  · exact of_allCert allCert_75 a hpos hsum hgcd

/-- **L9 at certified smooth denominators:** same conclusion as `l9_generic`, for `n` in `CertN`. -/
theorem l9_smooth {N : ℕ} (D : CongruentDissection N) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) (hC : CertN n) :
    SimilarTM D ∨
      ∃ k l : Fin 3, l ≠ k ∧ D.model.angleAt k = Real.pi / 2 ∧
        ∃ j₁ j₂ : Fin 3, j₁ ≠ j₂ ∧ D.target.angleAt j₁ = D.model.angleAt l ∧
          D.target.angleAt j₂ = D.model.angleAt l := by
  have ha1 : ∀ i, 0 < a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  exact l9_of_S D hn a ha hgcd (lemmaS_smooth hC a ha1 (sum_of_angles hn ha) hgcd)

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.l9_of_S
#print axioms Erdos634.Draft.LaczFormal.l9_smooth
