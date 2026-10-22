import Erdos634.Draft.LaczFormal9w

/-!
# Laczkovich DM 140 (1995), Theorem 2.6: infinitely many isosceles triangles with `c(T) ≥ 6`

NOTE, UNAUDITED.  Credit: Laczkovich (Discrete Math. 140 (1995) 79-94, Theorem 2.6), Beeson, Beeson-Zhang.  Formalization debt, not /goal progress.

Printed Thm 2.6: there are infinitely many isosceles triangles `T` with `c(T) ≥ 6`, where `c(T)` is the number of non-similar triangles `Δ` such that
`T` is a union of finitely many congruent copies of triangles similar to `Δ`.  Lean (`thm26`): an infinite set `S` of base angles `α ∈ (0, π/12)`
(`α = 6 arcsin((r² - 3)/(r² + 3))`, `r ∈ ℚ ∩ (7/4, 44/25)`, i.e. `sin(α/6)` and `√3 cos(α/6)` rational as in the printed proof) such that for every
`α ∈ S` an isosceles triangle with angles `(α, α, π - 2α)` exists and every such triangle satisfies `SixShapes` (six pairwise non-permutation angle triples,
each realized by a dissection of `T` into congruent triangles with that angle triple).  The cardinality `c(T)` is not defined; `SixShapes T` is the
statement `c(T) ≥ 6` (six pairwise non-similar shapes).  Differences from the printed proof: the six triples are separated by comparing their largest
entries, which needs the base angle in `(0, π/12)` (the printed proof uses the irrationality of `α/π`, Conway-Jones, for any admissible `α`).
-/

open scoped Classical
open Erdos634.Geometry Erdos634.LaczL35 EuclideanGeometry

namespace Erdos634.Laczkovich9x

open Erdos634.Laczkovich9v Erdos634.Laczkovich9u Erdos634.Laczkovich9w

def sQ (r : ℚ) : ℚ := (r ^ 2 - 3) / (r ^ 2 + 3)
def uQ (r : ℚ) : ℚ := 6 * r / (r ^ 2 + 3)

noncomputable def alphaOf (r : ℚ) : ℝ := 6 * Real.arcsin ((sQ r : ℚ) : ℝ)

section family
variable {r : ℚ} (h1 : (7 : ℚ) / 4 < r) (h2 : r < 44 / 25)
include h1 h2

theorem sQ_pos : 0 < sQ r := by
  unfold sQ
  have : (0 : ℚ) < r := by linarith
  have h3 : (3 : ℚ) < r ^ 2 := by nlinarith
  apply div_pos <;> nlinarith

theorem sQ_lt : sQ r < 1 / 36 := by
  unfold sQ
  have : (0 : ℚ) < r := by linarith
  have h3 : r ^ 2 < 31714 / 10000 := by nlinarith
  rw [div_lt_div_iff₀ (by nlinarith) (by norm_num)]
  nlinarith

theorem x_facts : 0 < Real.arcsin ((sQ r : ℚ) : ℝ) ∧ Real.arcsin ((sQ r : ℚ) : ℝ) < Real.pi / 72 ∧
    Real.sin (Real.arcsin ((sQ r : ℚ) : ℝ)) = (sQ r : ℚ) ∧
    Real.sqrt 3 * Real.cos (Real.arcsin ((sQ r : ℚ) : ℝ)) = (uQ r : ℚ) := by
  have hpi := Real.pi_pos
  have hs0 : (0 : ℝ) < (sQ r : ℚ) := by exact_mod_cast sQ_pos h1 h2
  have hs1 : ((sQ r : ℚ) : ℝ) < 1 / 36 := by
    have := sQ_lt h1 h2
    have h' : ((sQ r : ℚ) : ℝ) < (((1 : ℚ) / 36 : ℚ) : ℝ) := by exact_mod_cast this
    push_cast at h'; exact h'
  have hsin : Real.sin (Real.arcsin ((sQ r : ℚ) : ℝ)) = (sQ r : ℚ) :=
    Real.sin_arcsin (by linarith) (by linarith)
  refine ⟨Real.arcsin_pos.mpr hs0, ?_, hsin, ?_⟩
  · by_contra hge
    push_neg at hge
    have hle := Real.arcsin_le_pi_div_two ((sQ r : ℚ) : ℝ)
    have := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hle hge
    rw [hsin] at this
    have hj := Real.mul_le_sin (x := Real.pi / 72) (by positivity) (by linarith)
    have e : 2 / Real.pi * (Real.pi / 72) = 1 / 36 := by field_simp; ring
    linarith
  · have hr : (0 : ℝ) < r := by have : (0 : ℚ) < r := by linarith
                                exact_mod_cast this
    have hr3 : (3 : ℝ) < (r : ℝ) ^ 2 := by
      have : (3 : ℚ) < r ^ 2 := by nlinarith
      exact_mod_cast this
    have hcos : 0 ≤ Real.cos (Real.arcsin ((sQ r : ℚ) : ℝ)) := Real.cos_arcsin_nonneg _
    have hsq : (Real.sqrt 3 * Real.cos (Real.arcsin ((sQ r : ℚ) : ℝ))) ^ 2 = ((uQ r : ℚ) : ℝ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]
      have := Real.sin_sq_add_cos_sq (Real.arcsin ((sQ r : ℚ) : ℝ))
      rw [hsin] at this
      have e : Real.cos (Real.arcsin ((sQ r : ℚ) : ℝ)) ^ 2 = 1 - ((sQ r : ℚ) : ℝ) ^ 2 := by linarith
      rw [e]
      unfold sQ uQ; push_cast
      have : (r : ℝ) ^ 2 + 3 ≠ 0 := by positivity
      field_simp; ring
    have hu0 : (0 : ℝ) ≤ ((uQ r : ℚ) : ℝ) := by
      unfold uQ; push_cast; positivity
    exact (sq_eq_sq₀ (by positivity) hu0).mp hsq

end family

theorem alphaOf_inj : Set.InjOn alphaOf (Set.Ioo ((7 : ℚ) / 4) (44 / 25)) := by
  intro r hr r' hr' h
  have e : Real.arcsin ((sQ r : ℚ) : ℝ) = Real.arcsin ((sQ r' : ℚ) : ℝ) := by
    unfold alphaOf at h; linarith
  obtain ⟨-, -, hs, -⟩ := x_facts hr.1 hr.2
  obtain ⟨-, -, hs', -⟩ := x_facts hr'.1 hr'.2
  have : ((sQ r : ℚ) : ℝ) = ((sQ r' : ℚ) : ℝ) := by rw [← hs, ← hs', e]
  have hq : sQ r = sQ r' := by exact_mod_cast this
  unfold sQ at hq
  have p : (0 : ℚ) < r := by linarith [hr.1]
  have p' : (0 : ℚ) < r' := by linarith [hr'.1]
  rw [div_eq_div_iff (by positivity) (by positivity)] at hq
  have : r ^ 2 = r' ^ 2 := by nlinarith
  nlinarith [sq_nonneg (r - r'), sq_nonneg (r + r')]

/-- **Laczkovich DM 140 (1995), Theorem 2.6.** -/
theorem thm26 : ∃ S : Set ℝ, S.Infinite ∧ ∀ α ∈ S, 0 < α ∧ α < Real.pi / 12 ∧
    (∃ T : Tri, HasAngles T α α (Real.pi - 2 * α)) ∧
    ∀ T : Tri, HasAngles T α α (Real.pi - 2 * α) → SixShapes T := by
  refine ⟨alphaOf '' Set.Ioo ((7 : ℚ) / 4) (44 / 25),
    Set.Infinite.image alphaOf_inj (Set.Ioo_infinite (by norm_num)), ?_⟩
  rintro α ⟨r, hr, rfl⟩
  obtain ⟨hx0, hx1, hs, hu⟩ := x_facts hr.1 hr.2
  have hpi := Real.pi_pos
  have h0 : 0 < alphaOf r := by unfold alphaOf; linarith
  have h1 : alphaOf r < Real.pi / 12 := by unfold alphaOf; linarith
  refine ⟨h0, h1, ?_, fun T hT => ?_⟩
  · have h13 : alphaOf r < Real.pi / 3 := by linarith
    obtain ⟨q, hq⟩ := rat_cos6 (Real.arcsin ((sQ r : ℚ) : ℝ)) (sQ r) hs
    obtain ⟨R, k, hk1, hk2, hB, hC, r0, r1, r2⟩ := tile23 (alphaOf r) h0 h13 q hq
    obtain ⟨T, q', hq', M, C, -, -, ha0, ha1⟩ :=
      Erdos634.Laczkovich9t.thm23_first R k hk1 hk2 hB hC
    have v0 : vang T 0 = alphaOf r := ha0.trans r0
    have v1 : vang T 1 = alphaOf r := ha1.trans r0
    have v2 : vang T 2 = Real.pi - 2 * alphaOf r := by
      have := vang_sum T; linarith
    exact ⟨T, 1, v0, v1, v2⟩
  · exact core26 _ hx0 hx1 (sQ r) (uQ r) hs hu T hT

end Erdos634.Laczkovich9x

#print axioms Erdos634.Laczkovich9x.thm26
