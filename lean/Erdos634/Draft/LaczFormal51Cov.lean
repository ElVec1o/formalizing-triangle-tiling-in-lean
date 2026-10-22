import Erdos634.Draft.LaczFormalClassifyFinal
import Erdos634.Draft.BeesonH1

/-!
# Laczkovich Thm 5.1 for the tile `(alpha, beta, 2 alpha + beta)`, restricted to COVERED denominators

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) Thm 5.1; Combinatorica 10 (1990)), Beeson, Beeson-Zhang.
Formalization debt, not progress on the /goal outcomes.

`BeesonH1.Lacz51` (the only hypothesis left in `lemma1_of_lacz51`) is the family case of Thm 5.1.  The project already has the
conjugate-tiling geometry (`KConj.lemmaK`: coordinates in `Q(zeta_4n)`, conjugate dissection, orientation rule, K1/K2) and the
classification `LaczFormal.classify_commensurable_final` for the `Covered n` denominators (prime factor >= 7, `CertN2`, or n in
{3,4,6,8,10,12,18,24,30,60}).  Here: `Lacz51` with the extra premise that the tile angles are `a_i pi / n` (gcd 1) with `Covered n` is a
THEOREM (`lacz51_cov`).  What is NOT covered: n 5-smooth outside the lists (e.g. 1000).
-/

namespace Erdos634.Lacz51Cov

open Erdos634 Erdos634.Geometry Erdos634.BeesonColoring Erdos634.BeesonH1 Erdos634.Draft.LaczFormal Erdos634.Draft.TheoremPConditional

open scoped Classical

theorem triple3_perm (v : Fin 3 → ℝ) (ρ : Equiv.Perm (Fin 3)) :
    Triple3 (v (ρ 0)) (v (ρ 1)) (v (ρ 2)) (v 0) (v 1) (v 2) := by
  have key : ∀ ρ : Equiv.Perm (Fin 3),
      (ρ 0 = 0 ∧ ρ 1 = 1 ∧ ρ 2 = 2) ∨ (ρ 0 = 0 ∧ ρ 1 = 2 ∧ ρ 2 = 1) ∨ (ρ 0 = 1 ∧ ρ 1 = 0 ∧ ρ 2 = 2) ∨
      (ρ 0 = 1 ∧ ρ 1 = 2 ∧ ρ 2 = 0) ∨ (ρ 0 = 2 ∧ ρ 1 = 0 ∧ ρ 2 = 1) ∨ (ρ 0 = 2 ∧ ρ 1 = 1 ∧ ρ 2 = 0) := by
    decide
  rcases key ρ with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;>
    rw [h0, h1, h2] <;> unfold Triple3 <;> simp

/-- The six permutations as explicit triples (for case analysis). -/
theorem perm_cases (ρ : Equiv.Perm (Fin 3)) :
    (ρ 0 = 0 ∧ ρ 1 = 1 ∧ ρ 2 = 2) ∨ (ρ 0 = 0 ∧ ρ 1 = 2 ∧ ρ 2 = 1) ∨ (ρ 0 = 1 ∧ ρ 1 = 0 ∧ ρ 2 = 2) ∨
      (ρ 0 = 1 ∧ ρ 1 = 2 ∧ ρ 2 = 0) ∨ (ρ 0 = 2 ∧ ρ 1 = 0 ∧ ρ 2 = 1) ∨ (ρ 0 = 2 ∧ ρ 1 = 1 ∧ ρ 2 = 0) := by
  revert ρ; decide


/-- `Lacz51` restricted to tile angles `a_i pi / n` (gcd of the `a_i` equal to 1) with a COVERED denominator `n`. -/
def Lacz51Cov : Prop :=
  ∀ {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ} (x y z : ℚ) (n a0 a1 a2 : ℕ),
    0 < n → Covered n → Nat.gcd a0 (Nat.gcd a1 a2) = 1 →
    x = (a0 : ℚ) / n → y = (a1 : ℚ) / n → z = (a2 : ℚ) / n →
    D.model.ThreeAlphaData α β a b c →
    α = (x : ℝ) * Real.pi → β = (y : ℝ) * Real.pi → 2 * α + β = (z : ℝ) * Real.pi →
    ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β) →
    (x = 1/2 ∨ y = 1/2 ∨ z = 1/2) ∨ InLaczList x y z

theorem lacz51_cov : Lacz51Cov := by
  intro N D α β a b c x y z n a0 a1 a2 hn hcov hg hx hy hz hdata hα hβ hγ hns
  have hpi := Real.pi_pos
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := id hdata
  set vals : Fin 3 → ℝ := ![α, β, 2 * α + β] with hvals
  have hm : ∀ m, D.model.angleAt m = vals (σ.symm m) := by
    intro m
    obtain ⟨k, rfl⟩ := σ.surjective m
    rw [Equiv.symm_apply_apply]
    fin_cases k
    · simpa [hvals] using h0
    · simpa [hvals] using h1
    · simpa [hvals] using h2
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hvq : ∀ k, vals k = (![a0, a1, a2] k : ℕ) * Real.pi / n := by
    intro k
    fin_cases k
    · simp only [hvals]; simp; rw [hα, hx]; push_cast; ring
    · simp only [hvals]; simp; rw [hβ, hy]; push_cast; ring
    · simp only [hvals]; simp; rw [hγ, hz]; push_cast; ring
  set a' : Fin 3 → ℕ := fun m => ![a0, a1, a2] (σ.symm m) with ha'
  have ha : ∀ k, D.model.angleAt k = a' k * Real.pi / n := fun k => by rw [hm, hvq]
  have hgcd : Nat.gcd (a' 0) (Nat.gcd (a' 1) (a' 2)) = 1 := by
    set g := Nat.gcd (a' 0) (Nat.gcd (a' 1) (a' 2))
    have hd : ∀ k, g ∣ a' k := by
      intro k; fin_cases k
      · exact Nat.gcd_dvd_left _ _
      · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
      · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
    have e : ∀ i : Fin 3, g ∣ ![a0, a1, a2] i := fun i => by
      have := hd (σ i); simpa [ha'] using this
    have : g ∣ Nat.gcd a0 (Nat.gcd a1 a2) :=
      Nat.dvd_gcd (e 0) (Nat.dvd_gcd (e 1) (e 2))
    rw [hg] at this; exact Nat.dvd_one.mp this
  have hrel : 3 * α + 2 * β = Real.pi := by
    have hs := D.model.angleAt_sum
    rw [hm 0, hm 1, hm 2] at hs
    rcases perm_cases σ.symm with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ |
      ⟨e0, e1, e2⟩ <;> rw [e0, e1, e2] at hs <;> simp [hvals] at hs <;> linarith
  have hq : ∀ w : ℚ, (w : ℝ) * Real.pi = Real.pi / 2 → w = 1 / 2 := by
    intro w hw
    have : (w : ℝ) = 1 / 2 := by
      apply mul_right_cancel₀ hpi.ne'
      rw [hw]; ring
    exact Rat.cast_injective (α := ℝ) (by push_cast; exact this)
  have hright : ∀ k, vals k = Real.pi / 2 → (x = 1 / 2 ∨ y = 1 / 2 ∨ z = 1 / 2) := by
    intro k hk
    fin_cases k
    · left; apply hq; rw [← hα]; simpa [hvals] using hk
    · right; left; apply hq; rw [← hβ]; simpa [hvals] using hk
    · right; right; apply hq; rw [← hγ]; simpa [hvals] using hk
  have tile : ∀ t0 t1 t2 : ℝ, TileAngles D t0 t1 t2 →
      ∃ ρ : Equiv.Perm (Fin 3), vals (ρ 0) = t0 ∧ vals (ρ 1) = t1 ∧ vals (ρ 2) = t2 := by
    rintro t0 t1 t2 ⟨σ', e0, e1, e2⟩
    exact ⟨σ'.trans σ.symm, by rw [← e0, hm]; rfl, by rw [← e1, hm]; rfl, by rw [← e2, hm]; rfl⟩
  rcases classify_commensurable_final D hn a' ha hgcd hcov with hsim | hr | hex
  · exfalso
    obtain ⟨μ, τ, h⟩ := hsim
    apply hns
    have e : ∀ k, D.target.angleAt k = vals ((τ.trans σ.symm) k) := fun k => by
      rw [(h k).1, hm]; rfl
    rw [e 0, e 1, e 2]
    simpa [hvals] using triple3_perm vals (τ.trans σ.symm)
  · obtain ⟨k, l, -, hk, -⟩ := hr
    left
    apply hright (σ.symm k); rw [← hm]; exact hk
  · left
    rcases hex with ⟨hT, -⟩ | ⟨hT, -⟩ | ⟨hT, -⟩ <;>
    (obtain ⟨ρ, r0, r1, r2⟩ := tile _ _ _ hT
     rcases perm_cases ρ with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ |
       ⟨e0, e1, e2⟩ <;>
     (rw [e0] at r0; rw [e1] at r1; rw [e2] at r2; simp only [hvals] at r0 r1 r2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons] at r0 r1 r2
      first
      | (exfalso; linarith)
      | (apply hright 0; simp only [hvals]; simp; linarith)
      | (apply hright 1; simp only [hvals]; simp; linarith)
      | (apply hright 2; simp only [hvals]; simp; linarith)))

end Erdos634.Lacz51Cov

#print axioms Erdos634.Lacz51Cov.lacz51_cov
