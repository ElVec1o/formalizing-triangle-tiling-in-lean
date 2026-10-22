-- Draft/FluxE2Pi3Row8Mirrors.lean — ROW 8, "Lemma W for F3′ and F4′"
-- ((private working notes, not included) §3, "The mirrors F3′ and F4′ are the same
-- with x and y swapped").  Imported via AllNew8.lean → All.lean:853 (stale "NOT imported" header corrected 2026-10-04).
--
-- F3′ = (β, 2β, 3α) — F3 with α↔β (a↔b in the side formulæ):
--   angle β    = 1·(π/3) + (−1)·α  →  (j₀, k₀) = (1, −1)
--   angle 2β   = 2·(π/3) + (−2)·α  →  (j₁, k₁) = (2, −2)
--   angle 3α   = 0·(π/3) +  3·α    →  (j₂, k₂) = (0,  3)
--   sides opposite: ν·c², ν·c(2a+b), 3ν·a(a+b)  [F3 sides with a↔b]
--
-- F4′ = (β, 2α, α+2β) — F4 with α↔β (a↔b in the side formulæ):
--   angle β      = 1·(π/3) + (−1)·α  →  (j₀, k₀) = (1, −1)
--   angle 2α     = 0·(π/3) +  2·α    →  (j₁, k₁) = (0,  2)
--   angle α+2β   = 2·(π/3) + (−1)·α  →  (j₂, k₂) = (2, −1)
--   sides opposite: ν·bc, ν·a(a+2b), ν·c(a+b)  [F4 sides with a↔b]
--
-- Flux ZMod 2 conditions (notation: v = (3−j) mod 2 + b′·(−k mod 2)):
--   F3′ fAlpha (b′=0): v₀=0→+1, v₁=1→−1, v₂=1→−1; sum = +s₀−s₁−s₂
--   F3′ fBeta  (b′=1): v₀=0+1=1→−1, v₁=1+0=1→−1, v₂=1+1=0→+1; sum = −s₀−s₁+s₂
--   F4′ fAlpha (b′=0): v₀=0→+1, v₁=1→−1, v₂=1→−1; sum = +s₀−s₁−s₂
--   F4′ fBeta  (b′=1): v₀=0+1=1→−1, v₁=1+0=1→−1, v₂=1+1=0→+1; sum = −s₀−s₁+s₂
--
-- Formalization debt on the prime-case VERIFIED path; not progress on the three /goal outcomes.
import Erdos634.Draft.FluxE2Pi3Boundary

open scoped Classical

namespace Erdos634.Geometry

/-! ## F3′ = (β, 2β, 3α) -/

/-- **The F3′ target**: angles (β, 2β, 3α) with opposite sides (ν·c², ν·c(2a+b), 3ν·a(a+b)). -/
def Tri.F3PrimeData (T : Tri) (α a b c ν : ℝ) : Prop :=
  0 < ν ∧ T.GridTriData α 1 (-1) 2 (-2) 0 3
    (ν * c ^ 2) (ν * (c * (2 * a + b))) (3 * ν * (a * (a + b)))

/-- **Row 8 Lemma W for F3′, `f_α` half.**
`Φ_{f_α}(∂F3′) = ±ν(c²−c(2a+b)−3a(a+b))`. -/
theorem Row8.lemmaW_F3prime_alpha (T : Tri) {α a b c ν : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.F3PrimeData α a b c ν) :
    T.flux (fAlpha α hα).weight = ν * (c ^ 2 - c * (2 * a + b) - 3 * a * (a + b))
      ∨ T.flux (fAlpha α hα).weight = -(ν * (c ^ 2 - c * (2 * a + b) - 3 * a * (a + b))) := by
  obtain ⟨-, hgrid⟩ := h
  unfold fAlpha
  rcases T.gridTriData_flux_pm hα hgrid 0 with h1 | h1
  · left
    rw [h1, if_pos (by decide), if_neg (by decide), if_neg (by decide)]
    ring
  · right
    rw [h1, if_pos (by decide), if_neg (by decide), if_neg (by decide)]
    ring

/-- **Row 8 Lemma W for F3′, `f_β` half.**
`Φ_{f_β}(∂F3′) = ±ν(−c²−c(2a+b)+3a(a+b))`. -/
theorem Row8.lemmaW_F3prime_beta (T : Tri) {α a b c ν : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.F3PrimeData α a b c ν) :
    T.flux (fBeta α hα).weight = ν * (-(c ^ 2) - c * (2 * a + b) + 3 * a * (a + b))
      ∨ T.flux (fBeta α hα).weight = -(ν * (-(c ^ 2) - c * (2 * a + b) + 3 * a * (a + b))) := by
  obtain ⟨-, hgrid⟩ := h
  unfold fBeta
  rcases T.gridTriData_flux_pm hα hgrid 1 with h1 | h1
  · left
    rw [h1, if_neg (by decide), if_neg (by decide), if_pos (by decide)]
    ring
  · right
    rw [h1, if_neg (by decide), if_neg (by decide), if_pos (by decide)]
    ring

/-! ## F4′ = (β, 2α, α+2β) -/

/-- **The F4′ target**: angles (β, 2α, α+2β = 2π/3−α) with opposite sides
(ν·bc, ν·a(a+2b), ν·c(a+b)). -/
def Tri.F4PrimeData (T : Tri) (α a b c ν : ℝ) : Prop :=
  0 < ν ∧ T.GridTriData α 1 (-1) 0 2 2 (-1)
    (ν * (b * c)) (ν * (a * (a + 2 * b))) (ν * (c * (a + b)))

/-- **Row 8 Lemma W for F4′, `f_α` half.**
`Φ_{f_α}(∂F4′) = ±ν(bc−a(a+2b)−c(a+b))`. -/
theorem Row8.lemmaW_F4prime_alpha (T : Tri) {α a b c ν : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.F4PrimeData α a b c ν) :
    T.flux (fAlpha α hα).weight = ν * (b * c - a * (a + 2 * b) - c * (a + b))
      ∨ T.flux (fAlpha α hα).weight = -(ν * (b * c - a * (a + 2 * b) - c * (a + b))) := by
  obtain ⟨-, hgrid⟩ := h
  unfold fAlpha
  rcases T.gridTriData_flux_pm hα hgrid 0 with h1 | h1
  · left
    rw [h1, if_pos (by decide), if_neg (by decide), if_neg (by decide)]
    ring
  · right
    rw [h1, if_pos (by decide), if_neg (by decide), if_neg (by decide)]
    ring

/-- **Row 8 Lemma W for F4′, `f_β` half.**
`Φ_{f_β}(∂F4′) = ±ν(−bc−a(a+2b)+c(a+b))`. -/
theorem Row8.lemmaW_F4prime_beta (T : Tri) {α a b c ν : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.F4PrimeData α a b c ν) :
    T.flux (fBeta α hα).weight = ν * (-(b * c) - a * (a + 2 * b) + c * (a + b))
      ∨ T.flux (fBeta α hα).weight = -(ν * (-(b * c) - a * (a + 2 * b) + c * (a + b))) := by
  obtain ⟨-, hgrid⟩ := h
  unfold fBeta
  rcases T.gridTriData_flux_pm hα hgrid 1 with h1 | h1
  · left
    rw [h1, if_neg (by decide), if_neg (by decide), if_pos (by decide)]
    ring
  · right
    rw [h1, if_neg (by decide), if_neg (by decide), if_pos (by decide)]
    ring

/-! ## Simplification under the 120°-tile identity -/

/-- Under c²=a²+ab+b², F3′ fAlpha closed form = ν(−a²+2ab−2b²+bc) ... wait, let me track:
c²−c(2a+b)−3a(a+b) = (a²+ab+b²)−2ac−bc−3a²−3ab = −2a²−2ab+b²−c(2a+b). -/
theorem Row8.F3prime_flux_alpha_simplified {a b c ν : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ν * (c ^ 2 - c * (2 * a + b) - 3 * a * (a + b)) =
    ν * (-(2 * a ^ 2) - 2 * a * b + b ^ 2 - c * (2 * a + b)) := by
  linear_combination ν * hc2

/-- Under c²=a²+ab+b², F3′ fBeta closed form:
−c²−c(2a+b)+3a(a+b) = −(a²+ab+b²)−2ac−bc+3a²+3ab = 2a²+2ab−b²−c(2a+b). -/
theorem Row8.F3prime_flux_beta_simplified {a b c ν : ℝ} (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ν * (-(c ^ 2) - c * (2 * a + b) + 3 * a * (a + b)) =
    ν * (2 * a ^ 2 + 2 * a * b - b ^ 2 - c * (2 * a + b)) := by
  linear_combination -ν * hc2

/-- Under c²=a²+ab+b², F4′ fAlpha:
bc−a(a+2b)−c(a+b) = bc−a²−2ab−ac−bc = −a²−2ab−ac = −a(a+2b+c). -/
theorem Row8.F4prime_flux_alpha_simplified {a b c ν : ℝ} :
    ν * (b * c - a * (a + 2 * b) - c * (a + b)) = -(ν * a * (a + 2 * b + c)) := by
  ring

/-- F4′ fBeta closed form simplifies without c²=a²+ab+b²:
−bc−a(a+2b)+c(a+b) = a(c−a−2b). -/
theorem Row8.F4prime_flux_beta_simplified {a b c ν : ℝ} :
    ν * (-(b * c) - a * (a + 2 * b) + c * (a + b)) = ν * a * (c - a - 2 * b) := by
  ring

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row8.lemmaW_F3prime_alpha
#print axioms Erdos634.Geometry.Row8.lemmaW_F3prime_beta
#print axioms Erdos634.Geometry.Row8.lemmaW_F4prime_alpha
#print axioms Erdos634.Geometry.Row8.lemmaW_F4prime_beta
