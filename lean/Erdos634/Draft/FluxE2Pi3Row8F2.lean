-- Draft/FluxE2Pi3Row8F2.lean — ROW 8, "Lemma W for F2" ((private working notes, not included),
-- §3): the boundary closed forms `Φ_{f_α}(∂F2) = ±ν(c²−a(a+2b)−b(2a+b))`,
-- `Φ_{f_β}(∂F2) = ±ν(c²−a(a+2b)−b(2a+b))` (same expression for both characters) on the F2
-- target (shape (2α, 2β, π/3), paper `sub:shapes`), from `Draft/FluxE2Pi3Boundary.lean`.
-- Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
--
-- Note: the expression c²−a(a+2b)−b(2a+b) = c²−a²−4ab−b² equals −3ab only when
-- c²=a²+ab+b² (the 120°-tile identity).  The lemmas here state the raw form to avoid
-- importing that geometric identity into the boundary-evaluation layer.
--
-- F2 angle / side correspondence (law of sines; PROOF_row8.md §3):
--   angle 2α    (j=0, k=2)  ↔ opposite side ν·a(a+2b)
--   angle 2β    (j=2, k=−2) ↔ opposite side ν·b(2a+b)
--   angle π/3   (j=1, k=0)  ↔ opposite side ν·c²
-- where x = √ν·a, y = √ν·b, z = √ν·c (ν = μ² > 0).
--
-- Both characters give the same closed form because all k-coordinates are even
-- (k0=2, k1=−2, k2=0 → −k ≡ 0 mod 2 for all vertices):
--   vertex 0: (3−0) mod 2 + b′·(−2 mod 2) = 1 + 0 = 1 ≠ 0 → coefficient −1
--   vertex 1: (3−2) mod 2 + b′·(2 mod 2)  = 1 + 0 = 1 ≠ 0 → coefficient −1
--   vertex 2: (3−1) mod 2 + b′·(0 mod 2)  = 0 + 0 = 0     → coefficient +1
--   the_sum = −s₀ − s₁ + s₂ = ν(c²−a(a+2b)−b(2a+b)).
--
-- Formalization debt on the prime-case VERIFIED path; not progress on the three /goal outcomes.
import Erdos634.Draft.FluxE2Pi3Boundary

open scoped Classical

namespace Erdos634.Geometry

/-- **The F2 target** (`sub:shapes`, `PROOF_row8.md` §3): angles (2α, 2β, π/3) with
opposite sides (ν·a(a+2b), ν·b(2a+b), ν·c²), for the `2π/3`-tile's data `(α, a, b, c, β = π/3−α)`
and positive scale `ν`.  Grid coordinates:
  2α = 0·(π/3) + 2·α         →  (j₀, k₀) = (0, 2)
  2β = 2·(π/3) + (−2)·α      →  (j₁, k₁) = (2, −2)
  π/3 = 1·(π/3) + 0·α        →  (j₂, k₂) = (1, 0). -/
def Tri.F2Data (T : Tri) (α a b c ν : ℝ) : Prop :=
  0 < ν ∧ T.GridTriData α 0 2 2 (-2) 1 0 (ν * (a * (a + 2 * b))) (ν * (b * (2 * a + b))) (ν * c ^ 2)

/-- **Row 8 Lemma W for F2, `f_α` half.**
`Φ_{f_α}(∂F2) = ±ν(c²−a(a+2b)−b(2a+b))`.
When c²=a²+ab+b² this equals ±(−3νab). -/
theorem Row8.lemmaW_F2_alpha (T : Tri) {α a b c ν : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.F2Data α a b c ν) :
    T.flux (fAlpha α hα).weight = ν * (c ^ 2 - a * (a + 2 * b) - b * (2 * a + b))
      ∨ T.flux (fAlpha α hα).weight = -(ν * (c ^ 2 - a * (a + 2 * b) - b * (2 * a + b))) := by
  obtain ⟨-, hgrid⟩ := h
  unfold fAlpha
  rcases T.gridTriData_flux_pm hα hgrid 0 with h1 | h1
  · left
    rw [h1, if_neg (by decide), if_neg (by decide), if_pos (by decide)]
    ring
  · right
    rw [h1, if_neg (by decide), if_neg (by decide), if_pos (by decide)]
    ring

/-- **Row 8 Lemma W for F2, `f_β` half.**
`Φ_{f_β}(∂F2) = ±ν(c²−a(a+2b)−b(2a+b))`.
Since all k-coordinates of F2 are even, f_β gives the same closed form as f_α.
The integers M_α and M_β (cor:int) differ because they use divisors (c+a−b) vs (c+b−a). -/
theorem Row8.lemmaW_F2_beta (T : Tri) {α a b c ν : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.F2Data α a b c ν) :
    T.flux (fBeta α hα).weight = ν * (c ^ 2 - a * (a + 2 * b) - b * (2 * a + b))
      ∨ T.flux (fBeta α hα).weight = -(ν * (c ^ 2 - a * (a + 2 * b) - b * (2 * a + b))) := by
  obtain ⟨-, hgrid⟩ := h
  unfold fBeta
  rcases T.gridTriData_flux_pm hα hgrid 1 with h1 | h1
  · left
    rw [h1, if_neg (by decide), if_neg (by decide), if_pos (by decide)]
    ring
  · right
    rw [h1, if_neg (by decide), if_neg (by decide), if_pos (by decide)]
    ring

/-! ## Simplification lemma under the 120°-tile identity -/

/-- Under the 120°-tile identity c²=a²+ab+b², the F2 closed form equals −3νab. -/
theorem Row8.F2_flux_eq_neg3ab {a b c ν : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ν * (c ^ 2 - a * (a + 2 * b) - b * (2 * a + b)) = -(3 * ν * a * b) := by
  linear_combination ν * hc2

/-! ## Consistency check -/

/-- F2 angles are positive and sum to `π`. -/
theorem F2Data_angle_sum (α β : ℝ) (hβ : β = Real.pi / 3 - α) (hα0 : 0 < α)
    (hαβ : α < Real.pi / 3) :
    0 < 2 * α ∧ 0 < 2 * β ∧ 0 < Real.pi / 3 ∧
    2 * α + 2 * β + Real.pi / 3 = Real.pi := by
  have hpi := Real.pi_pos
  refine ⟨by linarith, by rw [hβ]; linarith, by linarith, ?_⟩
  rw [hβ]; ring

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row8.lemmaW_F2_alpha
#print axioms Erdos634.Geometry.Row8.lemmaW_F2_beta
#print axioms Erdos634.Geometry.Row8.F2_flux_eq_neg3ab
