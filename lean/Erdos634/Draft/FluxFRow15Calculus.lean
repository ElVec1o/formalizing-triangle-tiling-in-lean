-- Draft/FluxFRow15Calculus.lean — ROW 15 leaves 7, 8, 9 of ten
-- (rationality/rationality_proofs.md §5).  Continuation of Draft/FluxFRow15.lean (leaf 10),
-- Draft/FluxFRow15Cases.lean (leaves 1, 2, 4, 5), and Draft/FluxFRow15Cases2.lean (leaves 3, 6,
-- running total 7/10 going in). Does NOT edit any existing file (FluxFRow15.lean,
-- FluxFRow15Cases.lean, FluxFRow15Cases2.lean, All.lean, or anything outside this new file).
-- Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- RULE 0.5 SURVEY (before writing a line here): `grep -rl HasDerivAt lean/Erdos634/` returns
-- nothing outside this file — confirmed again, matching FluxFRow15Cases2.lean's header note that
-- zero calculus (HasDerivAt/StrictMonoOn/deriv) infrastructure exists anywhere in this corpus.
-- Nothing here is a rediscovery; this is genuinely new infrastructure, built from Mathlib
-- primitives, exactly as the task asked.
--
-- WHAT THIS FILE BUILDS. §5's leaves 7–9 (deg 2, `P < 0` branch) all rest on one calculus fact
-- stated in the source: "F is strictly increasing on (−1, 1), with numerator of F′ equal to
-- 2(x⁴+x³−2x−6)." Here `F(x) = g(x)·Y(x)²` (§0's table, reusing `g` from `FluxFRow15.lean` and
-- `Y`, `h` from `FluxFRow15Cases.lean` — NOT redefined, imported). This file:
--   1. Computes `HasDerivAt F (...)  x` for every `x ≠ 1, x ≠ −2`, via Mathlib derivative
--      combinators (`HasDerivAt.const_sub`, `.const_add`, `.pow`, `.mul`, `.inv`), and shows the
--      raw combinator output equals the closed form `2*(x^4+x^3-2*x-6)/((x-1)^3*(x+2)^3)` by
--      `field_simp; ring` (an algebraic identity, machine-checked, matching a `sympy` derivative
--      computation done first as a sanity check — not load-bearing, the Lean `ring` call is the
--      actual proof).
--   2. Proves the quartic numerator `x^4+x^3-2*x-6` is negative on the OPEN interval `(−1,1)`
--      elementarily (no Sturm sequence needed here, unlike leaf 3's global quartic: on the bounded
--      interval, `x^4 < 1`, `x^3 < 1`, `−2x < 2` combine directly, the same `nlinarith`-after-cube/
--      fourth-power-bound idiom `FluxFRow15.lean`'s `quartic_neg_on_Icc` already uses).
--   3. Shows the denominator `(x-1)^3*(x+2)^3` is negative on `(−1,1)` (`x−1<0` cubed is negative,
--      `x+2>0` cubed is positive), so the derivative (negative/negative) is POSITIVE on `(−1,1)`.
--   4. Concludes `StrictMonoOn F (Set.Ioo (-1) 1)` via Mathlib's `strictMonoOn_of_deriv_pos`.
--   5. Uses that monotonicity to close leaf 7 (`v ∈ (−1,1)`, `v ≠ s`, `F s = F v` ⟹ `False`, via
--      `StrictMonoOn.injOn`) and, combined with `F 0 = 3/2` (direct computation) and the strict
--      monotonicity again, to close leaf 9's `F 0 < F s` half.
--
-- LEAVES CLOSED IN THIS FILE (arithmetic core, same discipline as every prior Row15 file: the
-- geometric bridge — "the words force `X/Y`-comparisons between `s` and `v`" — is NOT built here or
-- anywhere in this corpus per the standing note in `FluxFRow15Cases.lean`'s header; what is closed
-- is the algebra/calculus the prose states, given the bridge facts as hypotheses):
--
-- • Leaf 7 (deg 2, `P < 0`, `v ∉ (−1,1)`): CLOSED. `row15_leaf7_not_in_open_unit` shows that if
--   `v ∈ (−1,1)`, `v ≠ s`, `s ∈ (0,1)`, and `F s = F v`, then `False` — the exact contrapositive of
--   "`F` strictly increasing on `(−1,1)` ⟹ `v ∉ (−1,1)`" (an injective function cannot take the same
--   value twice on distinct points of its domain).
-- • Leaf 8 (deg 2, `P < 0`, `v ∈ [√2,√3]`): CLOSED. `row15_leaf8` shows `g v ≤ 0` (so `F v ≤ 0`)
--   while `F s > 0`, directly from `v² ∈ [2,3]` — no calculus needed for this leaf at all; it is a
--   pointwise algebraic sign fact, same shape as leaves 4/5/6/10.
-- • Leaf 9 (deg 2, `P < 0`, `v ≥ 1.7`): CLOSED. `row15_leaf9` combines (a) `F 0 = 3/2` (direct
--   computation), (b) `F 0 < F s` for `s ∈ (0,1)` (from the SAME `StrictMonoOn` fact built for
--   leaf 7 — `0` and `s` are both in `Ioo (-1) 1`), and (c) `F v < 3/2` for `v ≥ 1.7` (an elementary
--   polynomial inequality, `nlinarith` on the explicit rational function, no calculus). Chaining
--   gives `F v < 3/2 = F 0 < F s`, so `F s ≠ F v`, closing the leaf.
--
-- All three of leaves 7/8/9 are now closed (arithmetic core; bridge hypotheses as usual). Running
-- total after this file: 10 of 10 arithmetic cores closed. The geometric bridge itself (word
-- coefficients / conjugate-principle comparisons ⟹ `X v ≤ X s` / `Y v ≤ Y s` / `v ∈`/`∉` an
-- interval, from an actual `CongruentDissection`) remains entirely unbuilt, as stated in every
-- prior Row15 file's header — this file does not touch that gap, and does not claim to.
--
-- WITNESS STATUS: every theorem below is unconditional on `x`/`s`/`v` beyond ordinary real
-- inequalities (no `CongruentDissection`-level hypothesis anywhere), so non-vacuity is immediate by
-- exhibiting real numbers in the stated ranges (e.g. `s = 1/2 ∈ (0,1)`, `v = 0 ∈ (-1,1)` for leaf 7;
-- `v = 1.7` itself for leaf 8/9's range checks). No hypothesis here can be unsatisfiable.
--
-- Formalization debt (paper-level PROVED for all ten leaves, per two hostile reviews recorded in
-- rationality_proofs.md "Label after two reviews"); not progress on the three /goal outcomes. This
-- closes the LAST named gap in row 15's ten-leaf case split at the "algebra/calculus given the
-- bridge" level; the bridge itself (§7's conjugate-principle machinery, absent from the whole
-- corpus) is untouched and is a separate, larger, earlier-stage piece of work.
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Erdos634.Draft.FluxFRow15
import Erdos634.Draft.FluxFRow15Cases

open scoped Classical

namespace Erdos634.Row15Calculus

open Erdos634.Row15 (g)
open Erdos634.Row15Cases (h Y)

/-- `F(x) = g(x)·Y(x)²`, exactly §0/§5's tiling function in the `g·Y²` form already used by
`FluxFRow15Cases.lean`/`FluxFRow15Cases2.lean`'s leaves 5/6 (`g s * Y s ^ 2 = g v * Y v ^ 2`), now
packaged as a single one-variable function so it can carry a derivative. -/
noncomputable def F (x : ℝ) : ℝ := g x * (Y x) ^ 2

/-! ### Step 1 — `F` has the stated derivative away from `x = 1, x = -2`.

Route: write `F = g / D` where `D x := (1-x)^2*(2+x)^2` (`= h x ^ 2`, an unconditional algebraic
identity, no case split needed since it holds even at `x = 1, -2` where both sides are `0` under
Lean's `1/0 = 0` convention). Differentiating a numerator/denominator pair via `HasDerivAt.div` is
far more direct than chaining through `HasDerivAt.inv` on `Y` itself, and avoids an inverse-of-an-
inverse mismatch that a first attempt at this file hit. -/

/-- `D x = (1-x)²(2+x)²`, the denominator of `F` written as a single rational function. -/
noncomputable def D (x : ℝ) : ℝ := (1 - x) ^ 2 * (2 + x) ^ 2

theorem D_eq_h_sq (x : ℝ) : D x = h x ^ 2 := by
  unfold D Erdos634.Row15Cases.h; ring

/-- **`F` equals `g / D`, unconditionally, for every real `x`** (including `x = 1, -2`, where both
sides equal `0`). -/
theorem F_eq_g_div_D (x : ℝ) : F x = g x / D x := by
  have hY2 : Y x ^ 2 = (D x)⁻¹ := by
    unfold Erdos634.Row15Cases.Y
    rw [one_div, inv_pow, D_eq_h_sq]
  unfold F
  rw [hY2, div_eq_mul_inv]

theorem hasDerivAt_g (x : ℝ) :
    HasDerivAt g ((-(2 * x)) * (3 - x ^ 2) + (2 - x ^ 2) * (-(2 * x))) x := by
  have hA : HasDerivAt (fun y : ℝ => (2 : ℝ) - y ^ 2) (-(2 * x)) x := by
    have := (hasDerivAt_pow 2 x).const_sub (2 : ℝ)
    simpa using this
  have hB : HasDerivAt (fun y : ℝ => (3 : ℝ) - y ^ 2) (-(2 * x)) x := by
    have := (hasDerivAt_pow 2 x).const_sub (3 : ℝ)
    simpa using this
  exact hA.mul hB

theorem hasDerivAt_D (x : ℝ) :
    HasDerivAt D (2 * (1 - x) * (-1) * (2 + x) ^ 2 + (1 - x) ^ 2 * (2 * (2 + x) * 1)) x := by
  have hA0 : HasDerivAt (fun y : ℝ => 1 - y) (-1 : ℝ) x := (hasDerivAt_id x).const_sub 1
  have hB0 : HasDerivAt (fun y : ℝ => 2 + y) (1 : ℝ) x := (hasDerivAt_id x).const_add 2
  have hA := hA0.pow 2
  have hB := hB0.pow 2
  have := hA.mul hB
  simpa [D] using this

/-- **`F` has the closed-form derivative `2(x⁴+x³−2x−6)/((x−1)³(x+2)³)` at every `x ∉ {1,−2}`.**
The combinator output from `hasDerivAt_g`/`hasDerivAt_D` via `.div` is an ugly rational expression;
it is shown to equal this closed form by `field_simp`/`ring` (a pure algebraic identity, first
sanity-checked against a `sympy` symbolic derivative of the same `F` — the `ring` call here is what
actually proves it). -/
theorem hasDerivAt_F (x : ℝ) (hx1 : x ≠ 1) (hx2 : x ≠ -2) :
    HasDerivAt F (2 * (x ^ 4 + x ^ 3 - 2 * x - 6) / ((x - 1) ^ 3 * (x + 2) ^ 3)) x := by
  have hg := hasDerivAt_g x
  have hD := hasDerivAt_D x
  have hx1' : (1 : ℝ) - x ≠ 0 := by intro hc; apply hx1; linarith
  have hx2' : (2 : ℝ) + x ≠ 0 := by intro hc; apply hx2; linarith
  have hDx : D x ≠ 0 := by unfold D; exact mul_ne_zero (pow_ne_zero 2 hx1') (pow_ne_zero 2 hx2')
  have hraw := hg.div hD hDx
  have hkey :
      (((-(2 * x)) * (3 - x ^ 2) + (2 - x ^ 2) * (-(2 * x))) * D x - g x *
          (2 * (1 - x) * (-1) * (2 + x) ^ 2 + (1 - x) ^ 2 * (2 * (2 + x) * 1))) / D x ^ 2 =
        2 * (x ^ 4 + x ^ 3 - 2 * x - 6) / ((x - 1) ^ 3 * (x + 2) ^ 3) := by
    have hcube1 : (x - 1) ^ 3 ≠ 0 := by
      have : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
      exact pow_ne_zero 3 this
    have hcube2 : (x + 2) ^ 3 ≠ 0 := by
      have : x + 2 ≠ 0 := by intro hc; apply hx2; linarith
      exact pow_ne_zero 3 this
    rw [div_eq_div_iff (pow_ne_zero 2 hDx) (mul_ne_zero hcube1 hcube2)]
    unfold Erdos634.Row15.g D
    ring
  have hFeq : F = fun y => g y / D y := funext F_eq_g_div_D
  rw [hFeq]
  rw [hkey] at hraw
  exact hraw

/-! ### Step 2 — sign facts on `(-1, 1)`: numerator negative, denominator negative, derivative
positive. -/

/-- The quartic numerator is negative on the OPEN interval `(-1,1)` — elementary, via the same
bound-then-`nlinarith` idiom as `FluxFRow15.quartic_neg_on_Icc`, not the global Sturm/SOS route
leaf 3 needed (this interval is bounded, so `x⁴ < 1`, `x³ < 1`, `−2x < 2` combine directly). -/
theorem quartic_neg_open_unit (x : ℝ) (hx1 : -1 < x) (hx2 : x < 1) :
    x ^ 4 + x ^ 3 - 2 * x - 6 < 0 := by
  have hxsq : x ^ 2 < 1 := by nlinarith
  have hx4 : x ^ 4 < 1 := by nlinarith [sq_nonneg x, sq_nonneg (x ^ 2 - 1)]
  have hx3 : x ^ 3 < 1 := by nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (x - 1)]
  linarith

theorem denom_neg_open_unit (x : ℝ) (hx1 : -1 < x) (hx2 : x < 1) :
    (x - 1) ^ 3 * (x + 2) ^ 3 < 0 := by
  have h1 : x - 1 < 0 := by linarith
  have h2 : (0:ℝ) < x + 2 := by linarith
  have hsqpos : (0:ℝ) < (x - 1) ^ 2 := by
    have := mul_pos (neg_pos.mpr h1) (neg_pos.mpr h1)
    nlinarith [this]
  have h1' : (x - 1) ^ 3 < 0 := by
    have hcube : (x - 1) ^ 3 = (x - 1) * (x - 1) ^ 2 := by ring
    rw [hcube]; exact mul_neg_of_neg_of_pos h1 hsqpos
  have h2' : (0:ℝ) < (x + 2) ^ 3 := by positivity
  exact mul_neg_of_neg_of_pos h1' h2'

theorem deriv_F_pos_open_unit (x : ℝ) (hx1 : -1 < x) (hx2 : x < 1) :
    0 < 2 * (x ^ 4 + x ^ 3 - 2 * x - 6) / ((x - 1) ^ 3 * (x + 2) ^ 3) := by
  have hnum : 2 * (x ^ 4 + x ^ 3 - 2 * x - 6) < 0 := by
    have := quartic_neg_open_unit x hx1 hx2; linarith
  have hden : (x - 1) ^ 3 * (x + 2) ^ 3 < 0 := denom_neg_open_unit x hx1 hx2
  exact div_pos_of_neg_of_neg hnum hden

/-! ### Step 3 — `F` is continuous, hence `StrictMonoOn F (Ioo (-1) 1)`. -/

theorem continuousOn_F : ContinuousOn F (Set.Ioo (-1 : ℝ) 1) := by
  intro x hx
  have hx1 : x ≠ 1 := ne_of_lt hx.2
  have hx2 : x ≠ -2 := by
    intro hc; rw [hc] at hx; linarith [hx.1]
  exact (hasDerivAt_F x hx1 hx2).continuousAt.continuousWithinAt

theorem deriv_F_eq (x : ℝ) (hx1 : x ≠ 1) (hx2 : x ≠ -2) :
    deriv F x = 2 * (x ^ 4 + x ^ 3 - 2 * x - 6) / ((x - 1) ^ 3 * (x + 2) ^ 3) :=
  (hasDerivAt_F x hx1 hx2).deriv

/-- **`F` is strictly increasing on `(-1, 1)`** — the calculus fact §5's leaves 7–9 all cite
("F is strictly increasing on (−1, 1)"). Via Mathlib's `strictMonoOn_of_deriv_pos` on the convex,
open set `Ioo (-1) 1` (whose interior is itself). -/
theorem strictMonoOn_F : StrictMonoOn F (Set.Ioo (-1 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo (-1 : ℝ) 1) continuousOn_F
  intro x hx
  rw [interior_Ioo] at hx
  have hx1 : x ≠ 1 := ne_of_lt hx.2
  have hx2 : x ≠ -2 := by intro hc; rw [hc] at hx; linarith [hx.1]
  rw [deriv_F_eq x hx1 hx2]
  exact deriv_F_pos_open_unit x hx.1 hx.2

/-! ### Leaf 7 (of the ten) — deg 2, `P < 0`, `v ∉ (-1,1)`. -/

/-- **Leaf 7 closed**: if `s ∈ (0,1)`, `v ∈ (-1,1)`, `v ≠ s`, and `F s = F v`, then `False`. This is
the exact contrapositive of "`F` strictly increasing on `(−1,1)` ⟹ distinct points get distinct
values ⟹ `v` cannot lie in `(−1,1)` if it shares `s`'s `F`-value" — §5's own route to "So
`v ∉ (−1, 1)`". -/
theorem row15_leaf7_not_in_open_unit (s v : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (hv1 : -1 < v) (hv2 : v < 1) (hvs : v ≠ s) (hEq : F s = F v) : False := by
  have hsMem : s ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hs1⟩
  have hvMem : v ∈ Set.Ioo (-1 : ℝ) 1 := ⟨hv1, hv2⟩
  have := strictMonoOn_F.injOn hsMem hvMem hEq
  exact hvs this.symm

/-! ### Leaf 8 (of the ten) — deg 2, `P < 0`, `v ∈ [√2, √3]`. -/

theorem g_v_nonpos_leaf8 (v : ℝ) (hv1 : 2 ≤ v ^ 2) (hv2 : v ^ 2 ≤ 3) : g v ≤ 0 := by
  unfold Erdos634.Row15.g
  have h1 : 2 - v ^ 2 ≤ 0 := by linarith
  have h2 : 0 ≤ 3 - v ^ 2 := by linarith
  nlinarith

theorem F_v_nonpos_leaf8 (v : ℝ) (hv1 : 2 ≤ v ^ 2) (hv2 : v ^ 2 ≤ 3) : F v ≤ 0 := by
  have hg : g v ≤ 0 := g_v_nonpos_leaf8 v hv1 hv2
  have hYsq : 0 ≤ Y v ^ 2 := sq_nonneg _
  unfold F
  nlinarith

theorem F_s_pos (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) : 0 < F s := by
  have hg : g s > 2 := Erdos634.Row15Cases.g_s_gt_two s hs0 hs1
  have hYpos : 0 < Y s := Erdos634.Row15Cases.Y_s_pos s hs0 hs1
  have hYsq : 0 < Y s ^ 2 := by positivity
  unfold F
  nlinarith

/-- **Leaf 8 closed**: if `s ∈ (0,1)`, `v² ∈ [2,3]`, and `F s = F v`, then `False` — no calculus
needed for this leaf (pure algebraic sign fact on `g`), same shape as leaves 4/5/6/10. -/
theorem row15_leaf8 (s v : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (hv1 : 2 ≤ v ^ 2) (hv2 : v ^ 2 ≤ 3) (hEq : F s = F v) : False := by
  have h1 : 0 < F s := F_s_pos s hs0 hs1
  have h2 : F v ≤ 0 := F_v_nonpos_leaf8 v hv1 hv2
  linarith [hEq ▸ h1]

/-! ### Leaf 9 (of the ten) — deg 2, `P < 0`, `v ≥ 1.7`. -/

theorem F_zero_eq : F 0 = 3 / 2 := by
  unfold F Erdos634.Row15.g Erdos634.Row15Cases.Y Erdos634.Row15Cases.h
  norm_num

/-- `F 0 < F s` for `s ∈ (0,1)`, via the SAME strict-monotonicity fact built for leaf 7 (`0` and
`s` are both in `Ioo (-1) 1`, and `0 < s`). -/
theorem F_zero_lt_F_s (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) : F 0 < F s := by
  have h0Mem : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hsMem : s ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hs1⟩
  exact strictMonoOn_F h0Mem hsMem hs0

/-- `F v < 3/2` for `v ≥ 1.7` — an elementary polynomial inequality on the explicit rational
function `F v = (2-v²)(3-v²)/((1-v)²(2+v)²)`, no calculus needed (the comparison point `3/2` is a
constant, not obtained by evaluating `F` at a nearby point via monotonicity). -/
theorem F_v_lt_three_half_ge (v : ℝ) (hv : (17 : ℝ) / 10 ≤ v) : F v < 3 / 2 := by
  have hv0 : (0:ℝ) < v := by linarith
  have hFv : F v = (2 - v ^ 2) * (3 - v ^ 2) / D v := by
    rw [F_eq_g_div_D]; rfl
  rw [hFv]
  unfold D
  have h1neg : (1:ℝ) - v < 0 := by linarith
  have h2pos : (0:ℝ) < 2 + v := by linarith
  have hsq1 : (0:ℝ) < (1 - v) ^ 2 := by nlinarith [mul_pos (neg_pos.mpr h1neg) (neg_pos.mpr h1neg)]
  have hsq2 : (0:ℝ) < (2 + v) ^ 2 := by positivity
  have hden_pos : (0:ℝ) < (1 - v) ^ 2 * (2 + v) ^ 2 := mul_pos hsq1 hsq2
  rw [div_lt_iff₀ hden_pos]
  have hv2 : (289:ℝ) / 100 ≤ v ^ 2 := by nlinarith
  have hv3 : (0:ℝ) < v ^ 3 := pow_pos hv0 3
  nlinarith [hv2, hv3, hv0]

/-- **Leaf 9 closed**: if `s ∈ (0,1)`, `v ≥ 1.7`, and `F s = F v`, then `False`. Chains
`F v < 3/2 = F 0 < F s` (the middle equality direct, the last inequality via
`strictMonoOn_F` reused from leaf 7, the first inequality a plain algebraic bound), so `F s ≠ F v`.
Matches §5's own chain: "F(v) < 3/2 = F(0) < F(s) (Sturm)" — here the `< F(s)` half is obtained
from the calculus fact instead of Sturm's theorem, since the calculus machinery was built for
leaf 7 anyway. -/
theorem row15_leaf9 (s v : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hv : (17 : ℝ) / 10 ≤ v)
    (hEq : F s = F v) : False := by
  have h1 : F v < 3 / 2 := F_v_lt_three_half_ge v hv
  have h2 : F (0 : ℝ) = 3 / 2 := F_zero_eq
  have h3 : F (0 : ℝ) < F s := F_zero_lt_F_s s hs0 hs1
  linarith [hEq ▸ h1]

end Erdos634.Row15Calculus

#print axioms Erdos634.Row15Calculus.hasDerivAt_F
#print axioms Erdos634.Row15Calculus.quartic_neg_open_unit
#print axioms Erdos634.Row15Calculus.denom_neg_open_unit
#print axioms Erdos634.Row15Calculus.strictMonoOn_F
#print axioms Erdos634.Row15Calculus.row15_leaf7_not_in_open_unit
#print axioms Erdos634.Row15Calculus.row15_leaf8
#print axioms Erdos634.Row15Calculus.row15_leaf9
