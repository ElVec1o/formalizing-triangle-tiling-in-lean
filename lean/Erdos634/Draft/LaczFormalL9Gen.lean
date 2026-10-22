-- Draft/LaczFormalL9Gen.lean -- atom L9, GENERIC PART: Laczkovich 1995 Thm 5.1 (i)/(ii) [= Beeson-Rosu Thm 4's dichotomy] for a congruent
-- dissection whose tile has rational angles with exact denominator n divisible by a prime p >= 7, ANY N.
-- Statement: either the target is similar to the tile, or the tile is a right triangle and two target angles equal the same acute tile angle
-- (target isosceles with a base angle of the tile).  So a NON-ISOSCELES target is similar to the tile (Thm 5.3's conclusion c(T) = 1 in this region).
-- Proof: assembled from our own conjugate-tiling chain `KConj.lemmaK` (K1, K2 for all units) + `LemmaSAll.lemmaS` (R(a) = R0(a)) +
-- `LemmaF.shapes_of_K`; it is the body of `CaseA.R0c.r0c_core` with the primality-specific steps (N | n, Row2.theoremS, Lemma H) removed.
-- NOT covered: n with all prime factors in {2,3,5} (Laczkovich's Lemma 5.2 region; see PLAN_L9_L7.md).  UNAUDITED.
-- Credit: Laczkovich (1995, Thm 5.1, 5.3; conjugate tilings of Combinatorica 1990), Beeson-Rosu Thm 4.
import Erdos634.Draft.CaseAR0c
import Erdos634.Draft.LemmaSAll
import Erdos634.Draft.LaczFormalBase

open scoped BigOperators Classical
open Erdos634.Geometry Erdos634.LemmaS Erdos634.LemmaKStar Erdos634.LemmaF Erdos634.KConj
  Erdos634.CaseA.R0c Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
open Erdos634.Geometry.CaseA.LemmaV (lemmaV_prime nat_bounds angle_pos angle_lt_pi)

namespace Erdos634.Draft.LaczFormal

/-- **L9 generic region.** -/
theorem l9_generic {N : ℕ} (D : CongruentDissection N) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hpn : p ∣ n) :
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
  have hS : relSpace n a = trivSpace n a :=
    Erdos634.LemmaSAll.lemmaS n a (fun i => ha1 i) hsum hgcd p hp hp7 hpn
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

/-- **L9 (Laczkovich 1995 Thm 5.3 / Beeson-Rosu Thm 4), generic region:** a non-isosceles target of a congruent dissection by a tile with
rational angles (exact denominator divisible by a prime `>= 7`) is similar to the tile. -/
theorem l9_generic_nonisosceles {N : ℕ} (D : CongruentDissection N) {n : ℕ} (hn : 0 < n)
    (a : Fin 3 → ℕ) (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hpn : p ∣ n)
    (hni : ∀ i j : Fin 3, i ≠ j → D.target.angleAt i ≠ D.target.angleAt j) : SimilarTM D := by
  rcases l9_generic D hn a ha hgcd hp hp7 hpn with h | ⟨k, l, hlk, hk, j₁, j₂, hj, h1, h2⟩
  · exact h
  · exact absurd (h1.trans h2.symm) (hni j₁ j₂ hj)

end Erdos634.Draft.LaczFormal

#print axioms Erdos634.Draft.LaczFormal.l9_generic
#print axioms Erdos634.Draft.LaczFormal.l9_generic_nonisosceles
