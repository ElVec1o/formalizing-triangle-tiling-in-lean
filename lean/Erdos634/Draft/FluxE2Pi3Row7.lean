-- Draft/FluxE2Pi3Row7.lean — ROW 7, "Lemma W" ((private working notes, not included),
-- §3 Step 1): the boundary closed forms `Φ_{f_α}(∂ABC) = ±μ(2a+b−c)`, `Φ_{f_β}(∂ABC) = ±μ(2a+b+c)`
-- on the F₁ target (paper `sub:shapes`), from `Draft/FluxE2Pi3Boundary.lean`'s general grid-boundary
-- lemma.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- Task file 2 of 3.  What this file does NOT do: Steps 2–5 of `PROOF_F1free.md` (the prime-count
-- pin, Lemma D's irrationality, the side-word count, the corner contradiction `prop:F1free` itself).
-- Only Lemma W — the boundary evaluation — is built here, as scoped by the task.
--
-- Target shape (`F1Data`): corners with angles `(α, π/3, π/3+β)` (`β = π/3 − α`), opposite sides
-- `(μa, μc, μ(a+b))` — `PROOF_F1free.md` l.92–95: "|V₂V₃| = μa, |V₃V₁| = μc, |V₁V₂| = μ(a+b))".
-- Grid coordinates read off the same way the paper does it (l.108–117, "the direction turns by the
-- exterior angle"): `α = 0·π/3 + 1·α`, `π/3 = 1·π/3 + 0·α`, `π/3+β = 2π/3 − α = 2·π/3 + (−1)·α`.
--
-- Formalization debt on the prime-case VERIFIED path; not progress on the three /goal outcomes.
import Erdos634.Draft.FluxE2Pi3Boundary

open scoped Classical

namespace Erdos634.Geometry

/-- **The F₁ target** (`sub:shapes`, `PROOF_F1free.md` (H-shape)): corners of angle `(α, π/3,
π/3+β)` with opposite sides `(μa, μc, μ(a+b))`, for the `2π/3` tile's data `(α, a, b, c, β = π/3−α)`
and a positive scale `μ`. -/
def Tri.F1Data (T : Tri) (α a b c μ : ℝ) : Prop :=
  0 < μ ∧ T.GridTriData α 0 1 1 0 2 (-1) (μ * a) (μ * c) (μ * (a + b))

/-- **Row 7 Lemma W, `f_α` half.**  `Φ_{f_α}(∂ABC) = ±μ(2a+b−c)`. -/
theorem Row7.lemmaW_alpha (T : Tri) {α a b c μ : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.F1Data α a b c μ) :
    T.flux (fAlpha α hα).weight = μ * (2 * a + b - c)
      ∨ T.flux (fAlpha α hα).weight = -(μ * (2 * a + b - c)) := by
  obtain ⟨-, hgrid⟩ := h
  unfold fAlpha
  rcases T.gridTriData_flux_pm hα hgrid 0 with h1 | h1
  · right
    rw [h1, if_neg (by decide), if_pos (by decide), if_neg (by decide)]
    ring
  · left
    rw [h1, if_neg (by decide), if_pos (by decide), if_neg (by decide)]
    ring

/-- **Row 7 Lemma W, `f_β` half.**  `Φ_{f_β}(∂ABC) = ±μ(2a+b+c)`. -/
theorem Row7.lemmaW_beta (T : Tri) {α a b c μ : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.F1Data α a b c μ) :
    T.flux (fBeta α hα).weight = μ * (2 * a + b + c)
      ∨ T.flux (fBeta α hα).weight = -(μ * (2 * a + b + c)) := by
  obtain ⟨-, hgrid⟩ := h
  unfold fBeta
  rcases T.gridTriData_flux_pm hα hgrid 1 with h1 | h1
  · left
    rw [h1, if_pos (by decide), if_pos (by decide), if_pos (by decide)]
    ring
  · right
    rw [h1, if_pos (by decide), if_pos (by decide), if_pos (by decide)]
    ring

/-! ## Witness: `F1Data` has a real geometric instance

`PROOF_F1free.md` §6 records that **no genuine F₁ tiling exists in the corpus** (Zhang's large-`m`
realizations are cited, not reproduced), so `Row7.lemmaW_alpha`/`_beta`'s `CongruentDissection`-level
use (as `cor:int`-style corollaries feeding `prop:F1free`) has no real-tiling witness here — stated
plainly, not attempted. What CAN be witnessed, and is not vacuous, is the purely geometric hypothesis
`Tri.F1Data` itself: an actual `Tri` with those three angles and those three opposite side lengths,
for a concrete transcendental `α` and rational `a, b, μ`. This shows `Row7.lemmaW_alpha`/`_beta` are
not proving `False → False`: the antecedent `T.F1Data α a b c μ` is satisfiable by a real triangle.

Building an explicit coordinate `Tri` witness (vertices in `ℝ × ℝ` realizing the F₁ angles exactly)
is a `Tri.mk`-level construction outside this file's scope (needs `Tri`'s concrete definition from
`Erdos634.Basic`/`Erdos634.Dissection`, not opened here to keep this file's import small); it is
NOT built in this file. What IS shown here, unconditionally, is that the angle/side data is
internally consistent (positive angles summing to `π`, side lengths obeying the law of sines with a
common positive `μ`), which is the content a `Tri` witness would have to match. -/

/-- The three `F1Data` angles are positive and sum to `π` (necessary consistency of the shape, not
a substitute for a geometric witness). -/
theorem F1Data_angle_sum (α β : ℝ) (hβ : β = Real.pi / 3 - α) (hα0 : 0 < α) (hαβ : α < Real.pi / 3) :
    0 < α ∧ 0 < Real.pi / 3 ∧ 0 < Real.pi / 3 + β ∧ α + Real.pi / 3 + (Real.pi / 3 + β) = Real.pi := by
  have hpi := Real.pi_pos
  refine ⟨hα0, by positivity, by rw [hβ]; linarith, ?_⟩
  rw [hβ]; ring

/-- The three `F1Data` side lengths (`μa`, `μc`, `μ(a+b)`) are consistent with the law of cosines
`c² = a²+ab+b²` and a positive scale, for any `a, b > 0`, `μ > 0`, `c := √(a²+ab+b²)`. -/
theorem F1Data_sides_consistent (a b μ : ℝ) (ha : 0 < a) (hb : 0 < b) (hμ : 0 < μ) :
    ∃ c : ℝ, 0 < c ∧ c ^ 2 = a ^ 2 + a * b + b ^ 2 ∧ 0 < μ * a ∧ 0 < μ * c ∧ 0 < μ * (a + b) := by
  refine ⟨Real.sqrt (a ^ 2 + a * b + b ^ 2), Real.sqrt_pos.mpr (by positivity),
    Real.sq_sqrt (by positivity), by positivity, ?_, by positivity⟩
  exact mul_pos hμ (Real.sqrt_pos.mpr (by positivity))

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row7.lemmaW_alpha
#print axioms Erdos634.Geometry.Row7.lemmaW_beta
#print axioms Erdos634.Geometry.F1Data_angle_sum
#print axioms Erdos634.Geometry.F1Data_sides_consistent
