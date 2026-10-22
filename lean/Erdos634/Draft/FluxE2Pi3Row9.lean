-- Draft/FluxE2Pi3Row9.lean — ROW 9, "Lemma CF" ((private working notes, not included),
-- §3.B Step 2): the boundary closed forms `Φ_{f_α} = ±μ(a+2b−2c)`, `Φ_{f_β} = ±μ(a+2b+2c)` on the
-- base-α isosceles target, from `Draft/FluxE2Pi3Boundary.lean`'s general grid-boundary lemma; then
-- composed with `Draft/FluxERow9Arith.lean`'s `Row9.iso_arith_core` as far as the geometry here
-- reaches.
--
-- Task file 3 of 3.  What this file does NOT do: Step 1 (Lemma Sh, that an isosceles non-equilateral
-- 2π/3 target IS base-α or base-β — a corner-filling argument, not a flux computation); Step 3
-- (`prop:rationality`, that the tile is rational); the base-β twin (relabelling α↔β, a↔b, per
-- `PROOF_thmiso.md` l.115–118, "it suffices to treat base-α").  Only Lemma CF and its composition
-- with the arithmetic core are built here, as scoped by the task.
--
-- Target shape (`BaseAlphaData`): corners `A, B` of angle `α` (opposite sides `μc` each) and apex
-- `C` of angle `π−2α` (opposite side `μ(a+2b)`) — `PROOF_thmiso.md` l.160 "base-α target as A, B
-- (angle α) and apex C (angle π − 2α)", l.163 "sides are μ(a+2b) for AB and μc for BC and CA".
-- Grid coordinates by the same vertex-angle technique as Row 7 (not the paper's own edge-direction
-- route l.164–165, which needs an edge-to-corner correspondence not built here — see the note below
-- the closed-form theorems): `α = 0·π/3 + 1·α`, `π−2α = 3·π/3 + (−2)·α`.
--
-- Formalization debt on the prime-case VERIFIED path; not progress on the three /goal outcomes.
import Erdos634.Draft.FluxE2Pi3Boundary
import Erdos634.Draft.FluxERow9Arith

open scoped Classical

namespace Erdos634.Geometry

/-- **The base-α isosceles target** (`PROOF_thmiso.md` §3.A/§3.B): two corners of angle `α`
(opposite sides `μc`) and an apex of angle `π − 2α` (opposite side `μ(a+2b)`), for the `2π/3` tile's
data `(α, a, b, c)` and a positive scale `μ`. -/
def Tri.BaseAlphaData (T : Tri) (α a b c μ : ℝ) : Prop :=
  0 < μ ∧ T.GridTriData α 0 1 0 1 3 (-2) (μ * c) (μ * c) (μ * (a + 2 * b))

/-- **Row 9 Lemma CF, `f_α` half.**  `Φ_{f_α}(∂ABC) = ±μ(a+2b−2c)`. -/
theorem Row9.lemmaCF_alpha (T : Tri) {α a b c μ : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.BaseAlphaData α a b c μ) :
    T.flux (fAlpha α hα).weight = μ * (a + 2 * b - 2 * c)
      ∨ T.flux (fAlpha α hα).weight = -(μ * (a + 2 * b - 2 * c)) := by
  obtain ⟨-, hgrid⟩ := h
  unfold fAlpha
  rcases T.gridTriData_flux_pm hα hgrid 0 with h1 | h1
  · left
    rw [h1, if_neg (by decide), if_pos (by decide)]
    ring
  · right
    rw [h1, if_neg (by decide), if_pos (by decide)]
    ring

/-- **Row 9 Lemma CF, `f_β` half.**  `Φ_{f_β}(∂ABC) = ±μ(a+2b+2c)`. -/
theorem Row9.lemmaCF_beta (T : Tri) {α a b c μ : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.BaseAlphaData α a b c μ) :
    T.flux (fBeta α hα).weight = μ * (a + 2 * b + 2 * c)
      ∨ T.flux (fBeta α hα).weight = -(μ * (a + 2 * b + 2 * c)) := by
  obtain ⟨-, hgrid⟩ := h
  unfold fBeta
  rcases T.gridTriData_flux_pm hα hgrid 1 with h1 | h1
  · left
    rw [h1, if_pos (by decide), if_pos (by decide)]
    ring
  · right
    rw [h1, if_pos (by decide), if_pos (by decide)]
    ring

/-! ## Composition with the arithmetic core: exactly how far this reaches

`Row9.iso_arith_core` (`Draft/FluxERow9Arith.lean`) needs, as REAL-VALUED hypotheses on a primitive
integer triple `a b c k M : ℤ`, `N : ℕ`:
`c² = a²+ab+b²`, `IsCoprime a c`, `N.Prime`, `a+2b ≥ 3`, `IsCoprime b (a+2b)`,
`b·N = k²·(a+2b)`, and `k·M = c−a−b`.

`Row9.lemmaCF_alpha`/`_beta` give the REAL closed forms `Φ_{f_α} = ±μ(a+2b−2c)`,
`Φ_{f_β} = ±μ(a+2b+2c)` for a `BaseAlphaData` target. `PROOF_thmiso.md` Steps 3–4 (§3.C "the tile
is rational", §3.D "the scale is an integer, and k² = b") are the bridge from these real closed
forms to the integer hypotheses `b·N = k²(a+2b)` and `k·M = c−a−b` that `iso_arith_core` consumes:
they need `prop:rationality` (rationalizing `a/b`, `c/b` from `cor:int`'s integers `M_α, M_β`),
scaling to a primitive triple, and Lemma P's Bezout step to produce `k` — NONE of which is built in
this file. **So this file does not compose `lemmaCF_alpha`/`_beta` with `iso_arith_core`**: the
composition needs Steps 3–4 as a genuine bridge, not a direct substitution, and building that bridge
is out of this task's scope (it is `prop:rationality` and Lemma P's Bezout step, each nontrivial,
neither attempted here). This is stated plainly rather than forced: attempting a direct `rw` from
`lemmaCF_alpha`/`_beta`'s real `Φ_{f_α}` into `iso_arith_core`'s integer `b·N = k²(a+2b)` would be a
type error (`ℝ` vs `ℤ`) papered over by an unjustified cast, which is exactly the vacuous-conditional
failure mode (private working notes, not included) warns against. -/

/-! ## Witness: `BaseAlphaData` has a real geometric instance (angle/side consistency only)

As with Row 7's `F1Data`, `PROOF_thmiso.md` §3 records real tilings only for the (H-prime)-violating
case (Herdt's `N = 2673`, review 2's four realized instances, all composite `N`); **no isosceles
`2π/3` target tiled by a PRIME number of tiles is known to exist** (`PROOF_thmiso.md` row (H-irr):
"I know no isosceles, non-equilateral target tiled by a prime number of copies of a rational-angle
2π/3 tile... necessity open"). So `Row9.lemmaCF_alpha`/`_beta` composed with a prime-`N`
`CongruentDissection` have no real-tiling witness — stated plainly. The geometric hypothesis
`Tri.BaseAlphaData` itself is not vacuous: it is satisfiable by a real triangle for any `a, b, μ > 0`
and `c := √(a²+ab+b²)`, shown below (angle sum, positivity — not a coordinate `Tri.mk`, for the same
reason given in `FluxE2Pi3Row7.lean`). -/

theorem BaseAlphaData_angle_sum (α : ℝ) (hα0 : 0 < α) (hαlt : α < Real.pi / 2) :
    0 < α ∧ 0 < Real.pi - 2 * α ∧ α + α + (Real.pi - 2 * α) = Real.pi := by
  exact ⟨hα0, by linarith, by ring⟩

theorem BaseAlphaData_sides_consistent (a b μ : ℝ) (ha : 0 < a) (hb : 0 < b) (hμ : 0 < μ) :
    ∃ c : ℝ, 0 < c ∧ c ^ 2 = a ^ 2 + a * b + b ^ 2 ∧ 0 < μ * c ∧ 0 < μ * (a + 2 * b) := by
  refine ⟨Real.sqrt (a ^ 2 + a * b + b ^ 2), Real.sqrt_pos.mpr (by positivity),
    Real.sq_sqrt (by positivity), by positivity, by positivity⟩

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Row9.lemmaCF_alpha
#print axioms Erdos634.Geometry.Row9.lemmaCF_beta
#print axioms Erdos634.Geometry.BaseAlphaData_angle_sum
#print axioms Erdos634.Geometry.BaseAlphaData_sides_consistent
