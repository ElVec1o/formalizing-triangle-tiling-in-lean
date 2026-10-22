-- Draft/FluxE2Pi3Row8F3.lean — ROW 8, "Lemma W for F3" ((private working notes, not included),
-- §3): the boundary closed forms on the F3 target (shape (α, 2α, 3β), paper `sub:shapes`),
-- from `Draft/FluxE2Pi3Boundary.lean`.  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
--
-- F3 angle / side correspondence (law of sines; PROOF_row8.md §3):
--   angle α    (j=0, k=1)  ↔ opposite side ν·c²
--   angle 2α   (j=0, k=2)  ↔ opposite side ν·c(a+2b)
--   angle 3β   (j=3, k=−3) ↔ opposite side 3ν·b(a+b)
-- where x = √ν·a, y = √ν·b, z = √ν·c (ν > 0).
-- (3β = π−3α, so j=3·(π/3)/(π/3) = 3 and k = −3.)
--
-- Flux closed forms:
--   fAlpha (b′=0): (3−j) mod 2 + b′·(−k mod 2) conditions:
--     vertex 0 (j=0,k=1): (3−0) mod 2 = 1 → −1
--     vertex 1 (j=0,k=2): (3−0) mod 2 = 1 → −1
--     vertex 2 (j=3,k=−3): (3−3) mod 2 = 0 → +1
--     the_sum = −νc² − νc(a+2b) + 3νb(a+b) = ν(−c²−c(a+2b)+3b(a+b))
--
--   fBeta (b′=1): adds b′·(−k mod 2):
--     vertex 0 (k=1): −k=−1≡1 mod 2  → (3−0 mod 2) + 1 = 1+1 = 2 = 0 → +1
--     vertex 1 (k=2): −k=−2≡0 mod 2  → (3−0 mod 2) + 0 = 1 ≠ 0 → −1
--     vertex 2 (k=−3): −k=3≡1 mod 2  → (3−3 mod 2) + 1 = 0+1 = 1 ≠ 0 → −1
--     the_sum = +νc² − νc(a+2b) − 3νb(a+b) = ν(c²−c(a+2b)−3b(a+b))
--
-- Note: under c²=a²+ab+b² (tile identity), the_sum for fAlpha = ν(−3ab−2bc−ac+3ab+3b²−b²)
-- ... (simplification requires the identity; stated without it here, as for F2).
--
-- Formalization debt on the prime-case VERIFIED path; not progress on the three /goal outcomes.
import Erdos634.Draft.FluxE2Pi3Boundary

open scoped Classical

namespace Erdos634.Geometry

/-- **The F3 target** (`sub:shapes`, `PROOF_row8.md` §3): angles (α, 2α, 3β = π−3α) with
opposite sides (ν·c², ν·c(a+2b), 3ν·b(a+b)), for the `2π/3`-tile's data `(α, a, b, c, β = π/3−α)`
and positive scale `ν`.  Grid coordinates:
  α   = 0·(π/3) + 1·α         →  (j₀, k₀) = (0, 1)
  2α  = 0·(π/3) + 2·α         →  (j₁, k₁) = (0, 2)
  3β = 3·(π/3) + (−3)·α       →  (j₂, k₂) = (3, −3). -/
def Tri.F3Data (T : Tri) (α a b c ν : ℝ) : Prop :=
  0 < ν ∧ T.GridTriData α 0 1 0 2 3 (-3) (ν * c ^ 2) (ν * (c * (a + 2 * b))) (3 * ν * (b * (a + b)))

/-- **Row 8 Lemma W for F3, `f_α` half.**
`Φ_{f_α}(∂F3) = ±ν(−c²−c(a+2b)+3b(a+b))`. -/
theorem Row8.lemmaW_F3_alpha (T : Tri) {α a b c ν : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.F3Data α a b c ν) :
    T.flux (fAlpha α hα).weight = ν * (-(c ^ 2) - c * (a + 2 * b) + 3 * b * (a + b))
      ∨ T.flux (fAlpha α hα).weight = -(ν * (-(c ^ 2) - c * (a + 2 * b) + 3 * b * (a + b))) := by
  obtain ⟨-, hgrid⟩ := h
  unfold fAlpha
  rcases T.gridTriData_flux_pm hα hgrid 0 with h1 | h1
  · left
    rw [h1, if_neg (by decide), if_neg (by decide), if_pos (by decide)]
    ring
  · right
    rw [h1, if_neg (by decide), if_neg (by decide), if_pos (by decide)]
    ring

/-- **Row 8 Lemma W for F3, `f_β` half.**
`Φ_{f_β}(∂F3) = ±ν(c²−c(a+2b)−3b(a+b))`. -/
theorem Row8.lemmaW_F3_beta (T : Tri) {α a b c ν : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.F3Data α a b c ν) :
    T.flux (fBeta α hα).weight = ν * (c ^ 2 - c * (a + 2 * b) - 3 * b * (a + b))
      ∨ T.flux (fBeta α hα).weight = -(ν * (c ^ 2 - c * (a + 2 * b) - 3 * b * (a + b))) := by
  obtain ⟨-, hgrid⟩ := h
  unfold fBeta
  rcases T.gridTriData_flux_pm hα hgrid 1 with h1 | h1
  · left
    rw [h1, if_pos (by decide), if_neg (by decide), if_neg (by decide)]
    ring
  · right
    rw [h1, if_pos (by decide), if_neg (by decide), if_neg (by decide)]
    ring

/-! ## Simplification under the 120°-tile identity -/

/-- Under c²=a²+ab+b², the F3 fAlpha closed form equals ν(z−2x−y)·(c+a−b)/something.
Concretely: −c²−c(a+2b)+3b(a+b) = −(c+a)(c+2b)+(3b+c)(a+b) simplifies to
(a²+ab+b²)·(−1)−c(a+2b)+3b(a+b).  Under the identity: = −(a+2b)(c−b)+... tracked in paper. -/
theorem Row8.F3_flux_alpha_simplified {a b c ν : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ν * (-(c ^ 2) - c * (a + 2 * b) + 3 * b * (a + b)) =
    ν * (-(a ^ 2) + 2 * a * b + 2 * b ^ 2 - c * (a + 2 * b)) := by
  linear_combination -ν * hc2

/-- Under c²=a²+ab+b², the F3 fBeta closed form:
c²−c(a+2b)−3b(a+b) = (a²+ab+b²)−c(a+2b)−3ab−3b² = a²−2ab−2b²−c(a+2b). -/
theorem Row8.F3_flux_beta_simplified {a b c ν : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ν * (c ^ 2 - c * (a + 2 * b) - 3 * b * (a + b)) =
    ν * (a ^ 2 - 2 * a * b - 2 * b ^ 2 - c * (a + 2 * b)) := by
  linear_combination ν * hc2

/-! ## Consistency check -/

/-- F3 angles are positive and sum to `π`. -/
theorem F3Data_angle_sum (α β : ℝ) (hβ : β = Real.pi / 3 - α) (hα0 : 0 < α)
    (hαβ : α < Real.pi / 3) :
    0 < α ∧ 0 < 2 * α ∧ 0 < 3 * β ∧
    α + 2 * α + 3 * β = Real.pi := by
  have hpi := Real.pi_pos
  refine ⟨hα0, by linarith, by rw [hβ]; linarith, ?_⟩
  rw [hβ]; ring

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row8.lemmaW_F3_alpha
#print axioms Erdos634.Geometry.Row8.lemmaW_F3_beta
