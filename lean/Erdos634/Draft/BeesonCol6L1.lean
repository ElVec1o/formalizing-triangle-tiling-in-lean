import Mathlib
import Erdos634.Draft.LaczFormal51Lemma1

/-!
# Beeson (arXiv 1206.2229 v4) Lemma 1, full printed statement

NOTE, UNAUDITED.  Credit: Michael Beeson (arXiv 1206.2229 v4, Lemma 1), Laczkovich (Discrete Math. 140 (1995) Thm 5.1, 5.3),
Beeson-Zhang.  Formalization debt.  `BeesonH1.lemma1_unconditional` gives "alpha is not a rational multiple of pi" for any
`CongruentDissection` of a triangle not similar to the tile; the printed Lemma 1 also asserts the same for `beta` and that
every rational linear relation between `pi, alpha, beta` is a rational multiple of `3 alpha + 2 beta = pi`.  Those two
sentences are pure algebra from `alpha ∉ Q pi` and are proved here (`lemma1_beta`, `lemma1_relations`); `lemma1_full` is the
conjunction with the tiling hypotheses of `lemma1_unconditional`.
-/

namespace Erdos634.BeesonCol6

open Erdos634 Erdos634.Geometry Erdos634.BeesonColoring

theorem lemma1_beta {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) :
    ¬ ∃ r : ℚ, β = (r : ℝ) * Real.pi := by
  rintro ⟨r, hr⟩
  apply hα
  refine ⟨(1 - 2 * r) / 3, ?_⟩
  push_cast
  linarith

/-- every rational relation `x pi + y alpha + z beta = 0` is a rational multiple of `(-1, 3, 2)`, i.e. of `3 alpha + 2 beta - pi = 0`. -/
theorem lemma1_relations {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (x y z : ℚ) (h : (x : ℝ) * Real.pi + y * α + z * β = 0) :
    ∃ t : ℚ, x = -t ∧ y = 3 * t ∧ z = 2 * t := by
  have hz : (y : ℝ) - 3 * z / 2 = 0 := by
    by_contra hne
    apply hα
    refine ⟨-(x + z / 2) / (y - 3 * z / 2), ?_⟩
    have hβ : β = (Real.pi - 3 * α) / 2 := by linarith
    rw [hβ] at h
    have key : ((y : ℝ) - 3 * z / 2) * α = -((x : ℝ) + z / 2) * Real.pi := by linarith
    push_cast
    rw [div_mul_eq_mul_div, eq_div_iff hne]
    linear_combination key
  have hy : y = 3 * z / 2 := by
    have : (y : ℝ) = 3 * z / 2 := by linarith
    exact_mod_cast this
  have hpi : (x : ℝ) + z / 2 = 0 := by
    have hβ : β = (Real.pi - 3 * α) / 2 := by linarith
    rw [hβ] at h
    have : ((x : ℝ) + z / 2) * Real.pi + ((y : ℝ) - 3 * z / 2) * α = 0 := by linarith
    rw [hz] at this
    have hp := Real.pi_pos
    nlinarith
  refine ⟨z / 2, ?_, ?_, ?_⟩
  · have : (x : ℝ) = -(z / 2) := by linarith
    exact_mod_cast this
  · rw [hy]; ring
  · ring

/-- **Lemma 1** (printed statement) for a `CongruentDissection` of a triangle not similar to the tile. -/
theorem lemma1_full {N : ℕ} (D : CongruentDissection N)
    {α β a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (h : D.model.ThreeAlphaData α β a b c)
    (hns : ¬ Triple3 (D.target.angleAt 0) (D.target.angleAt 1) (D.target.angleAt 2) α β (2 * α + β)) :
    (¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) ∧ (¬ ∃ r : ℚ, β = (r : ℝ) * Real.pi) ∧
      ∀ x y z : ℚ, (x : ℝ) * Real.pi + y * α + z * β = 0 → ∃ t : ℚ, x = -t ∧ y = 3 * t ∧ z = 2 * t := by
  have h1 := BeesonH1.lemma1_unconditional D hrel h hns
  exact ⟨h1, lemma1_beta hrel h1, fun x y z hh => lemma1_relations hrel h1 x y z hh⟩

end Erdos634.BeesonCol6

#print axioms Erdos634.BeesonCol6.lemma1_beta
#print axioms Erdos634.BeesonCol6.lemma1_relations
#print axioms Erdos634.BeesonCol6.lemma1_full
