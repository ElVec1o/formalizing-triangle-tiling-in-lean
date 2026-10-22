-- Draft/FluxE2Pi3Row8F4.lean — ROW 8, "Lemma W for F4" ((private working notes, not included),
-- §3): the boundary closed forms `Φ_{f_α}(∂F4) = ±νb(2a+b−c)`, `Φ_{f_β}(∂F4) = ±νb(2a+b+c)`
-- on the F4 target (shape (α, 2β, 2α+β), paper `sub:shapes`), from
-- `Draft/FluxE2Pi3Boundary.lean`'s general grid-boundary lemma.  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
--
-- F4 angle / side correspondence (law of sines; PROOF_row8.md §3):
--   angle α (j=0, k=1) ↔ opposite side ν·ac
--   angle 2β (j=2, k=−2) ↔ opposite side ν·b(2a+b)
--   angle 2α+β = α+π/3 (j=1, k=1) ↔ opposite side ν·c(a+b)
-- where x = √ν·a, y = √ν·b, z = √ν·c (ν = μ² > 0).
--
-- Flux closed forms (b′ = 0, i.e. fAlpha):
--   coefficients: −1 (vertex 0), −1 (vertex 1), +1 (vertex 2)
--   sum: −νac − νb(2a+b) + νc(a+b) = νb(c − 2a − b) = −νb(2a+b−c)
-- Flux closed forms (b′ = 1, i.e. fBeta):
--   coefficients: +1 (vertex 0), −1 (vertex 1), −1 (vertex 2)
--   sum: νac − νb(2a+b) − νc(a+b) = ν(−2ab − b² − bc) = −νb(2a+b+c)
--
-- Rationality corollary (PROOF_row8.md §3, F4 paragraph):
--   M_α = ±√ν·(a−c) and M_β = ±√ν·(a+c) are integers (from cor:int);
--   x = (M_α + M_β)/2 = ±√ν·a ∈ ℚ,  z = (M_β − M_α)/2 = ±√ν·c ∈ ℚ,
--   then y = (N − x² − z²)/(2x) ∈ ℚ.
--   The rationality conclusion itself is NOT proved in this file (it needs cor:int at
--   the dissection level, which requires the tile-placement layer);  Lemma W is the
--   boundary evaluation step only.
--
-- Task file for Row 8 (F4 case only; F2 and F3 require separate files with their own
-- closed forms).  Formalization debt on the prime-case VERIFIED path; not progress on
-- the three /goal outcomes.
import Erdos634.Draft.FluxE2Pi3Boundary

open scoped Classical

namespace Erdos634.Geometry

/-- **The F4 target** (`sub:shapes`, `PROOF_row8.md` §3): angles (α, 2β, α+π/3 = 2α+β) with
opposite sides (ν·ac, ν·b(2a+b), ν·c(a+b)), for the `2π/3`-tile's data `(α, a, b, c, β = π/3−α)`
and a positive scale `ν`.  The grid coordinates read from the exterior-angle rule:
  α = 0·(π/3) + 1·α   →  (j₀, k₀) = (0, 1)
  2β = 2π/3 − 2α       →  (j₁, k₁) = (2, −2)
  α+π/3 = 1·(π/3)+1·α →  (j₂, k₂) = (1, 1). -/
def Tri.F4Data (T : Tri) (α a b c ν : ℝ) : Prop :=
  0 < ν ∧ T.GridTriData α 0 1 2 (-2) 1 1 (ν * (a * c)) (ν * (b * (2 * a + b))) (ν * (c * (a + b)))

/-- **Row 8 Lemma W for F4, `f_α` half.**  `Φ_{f_α}(∂F4) = ±νb(2a+b−c)`. -/
theorem Row8.lemmaW_F4_alpha (T : Tri) {α a b c ν : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.F4Data α a b c ν) :
    T.flux (fAlpha α hα).weight = ν * b * (2 * a + b - c)
      ∨ T.flux (fAlpha α hα).weight = -(ν * b * (2 * a + b - c)) := by
  obtain ⟨-, hgrid⟩ := h
  unfold fAlpha
  rcases T.gridTriData_flux_pm hα hgrid 0 with h1 | h1
  · right
    rw [h1, if_neg (by decide), if_neg (by decide), if_pos (by decide)]
    ring
  · left
    rw [h1, if_neg (by decide), if_neg (by decide), if_pos (by decide)]
    ring

/-- **Row 8 Lemma W for F4, `f_β` half.**  `Φ_{f_β}(∂F4) = ±νb(2a+b+c)`. -/
theorem Row8.lemmaW_F4_beta (T : Tri) {α a b c ν : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.F4Data α a b c ν) :
    T.flux (fBeta α hα).weight = ν * b * (2 * a + b + c)
      ∨ T.flux (fBeta α hα).weight = -(ν * b * (2 * a + b + c)) := by
  obtain ⟨-, hgrid⟩ := h
  unfold fBeta
  rcases T.gridTriData_flux_pm hα hgrid 1 with h1 | h1
  · right
    rw [h1, if_pos (by decide), if_neg (by decide), if_neg (by decide)]
    ring
  · left
    rw [h1, if_pos (by decide), if_neg (by decide), if_neg (by decide)]
    ring

/-! ## Consistency check: `F4Data` angles are positive and sum to `π` -/

/-- The three F4 angles are positive and sum to `π`, confirming the shape is non-degenerate. -/
theorem F4Data_angle_sum (α β : ℝ) (hβ : β = Real.pi / 3 - α) (hα0 : 0 < α)
    (hαβ : α < Real.pi / 3) :
    0 < α ∧ 0 < 2 * β ∧ 0 < α + Real.pi / 3 ∧
    α + 2 * β + (α + Real.pi / 3) = Real.pi := by
  have hpi := Real.pi_pos
  refine ⟨hα0, by rw [hβ]; linarith, by linarith, ?_⟩
  rw [hβ]; ring

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row8.lemmaW_F4_alpha
#print axioms Erdos634.Geometry.Row8.lemmaW_F4_beta
