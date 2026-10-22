-- Draft/FluxFRow15.lean — ROW 15 (rationality/rationality_proofs.md §5, PROVED after two hostile
-- reviews): on the target `(2α, α, 2β)`, an `N`-tiling (any `N`, reflections allowed, not
-- necessarily edge-to-edge) by the `3α + 2β = π` tile with `α ∉ ℚπ` has a rational tile,
-- `s := a/c ∈ ℚ`.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- HEADLINE FINDING (Rule 0.5 survey; see Draft/FluxFRow14.lean's header for the full argument):
-- grepped `lean/Erdos634/Draft/Flux*.lean` for "Row14", "Row15" before writing a line here — no
-- hits (rows 11/12/13 only). rationality_proofs.md §5's route is pure algebra over the field
-- `Q(s)` (degree / conjugate case split), never touching the flux functional, GridChar, or
-- fAlpha/fBeta, so there is nothing to reuse from that machinery for this row either. Not a
-- rediscovery.
--
-- THE TASK'S OWN DEMAND: nail the factorization identity down and machine-verify it BEFORE
-- building anything on it. That identity, review 2a's repair 3 (rationality_proofs.md, "Review 2
-- record" section, `k − 4/3 = (x−1)(3x⁴+6x³−9x²−24x−10)/(3(2+x))`, REPLACING the file's original,
-- flawed "k is unimodal on [0,1]" claim), is `k_minus_four_thirds` below: `ring`-checked, EXIT-0,
-- no `sorry`. `k` is defined exactly as the file defines it at line ~228: "k = g·(1+x)/(2+x)"
-- where `g(x) = (2−x²)(3−x²)` (line 82's table: `F = g·Y², g(x) = (2−x²)(3−x²)`).
--
-- SANITY CHECK (not load-bearing, recorded for the reader): at `x = 0`, `k(0) = 2·3·1/2 = 3`, so
-- `k(0) − 4/3 = 5/3`; the RHS is `(0−1)·(0+0−0−0−10)/(3·2) = (−1)·(−10)/6 = 10/6 = 5/3`. Matches.
-- (§5's text independently records `k(0) = 3`.)
--
-- SCOPE OF WHAT IS CLOSED (honest; matches the row-14 / row-3 / row-5 partial-completion style).
-- CLOSED, UNCONDITIONAL: `k_minus_four_thirds` (the identity itself, over all `x ≠ −2`, no
-- hypothesis on `x` beyond that) and `quartic_neg_on_Icc` (the quartic factor
-- `3x⁴+6x³−9x²−24x−10` is `< 0` for every `x ∈ [0, 3/2]`, review 2a's parenthetical "whose
-- quartic factor is negative on [0, 3/2]" — proved here by the same bounding argument as the
-- review's own repair, `x⁴ ≤ (3/2)²x²` and `x³ ≤ (3/2)x²` on `[0, 3/2]`, reducing to a single
-- quadratic bound closed by `nlinarith`). `k_gt_four_thirds_on_unit` / `k_lt_four_thirds_gt_one`
-- compose these into the two half-inequalities the row-15 leaf ("v ∈ (1, √2)") actually consumes:
-- `k(s) > 4/3` for `s ∈ (0,1)` and `k(v) < 4/3` for `v ∈ (1, 3/2]` (the review's `v ∈ (1, √2)` is
-- covered since `√2 < 3/2`).
--
-- NOT FORMALIZED, stated plainly (this is most of §5; do not read the above as "row 15 is done").
-- Only ONE of §5's ten case-split leaves ("deg 2, P < 0, v ∈ (1, √2)") is even addressed, and only
-- its arithmetic core (the `k − 4/3` sign facts) — NOT the geometric machinery around it: the
-- identification `k(v) ≥ k(s)` FROM "Y needs `(v−1)²(v+1)(v+2) ≥ (1−s)²(1+s)(2+s)`" and
-- `F(s) = F(v)` (§5's own derivation of "this becomes `k(v) ≥ k(s)`") is NOT formalized — it needs
-- `F`, `g`, `h`, `Y` as defined at the top of §5 and their relation to `k`, none of which is built
-- here. The other nine leaves (deg 4; `q = 1`; deg 3; the three `P ≥ 0` sub-intervals; the three
-- other `P < 0` sub-cases `v ∉ (−1,1)`, `v ∈ [√2,√3]`, `v ≥ 1.7`) are UNTOUCHED — no Lean for any
-- of them exists here or, per the survey above, anywhere in the corpus. There is also no
-- `CongruentDissection`-level statement of row 15 in this file (same precedent as rows 4/11/13/14:
-- algebra only, no tiling witness attempted).
--
-- WITNESS. `k_minus_four_thirds` needs only `x ≠ −2`, witnessed trivially (e.g. `x = 0`, checked
-- above) — it is a rational-function identity, true for every real `x ≠ −2`, so non-vacuity is
-- immediate and not worth a separate lemma. `quartic_neg_on_Icc`'s hypothesis `x ∈ [0, 3/2]` is
-- witnessed the same way (e.g. `x = 1`, checked in the corpus's own text: "k(1) = 4/3"). Per the
-- paper's own record (rationality_proofs.md, "P8. Remaining external inputs" / "5. Non-vacuity
-- witnesses"), rows 11 and 13 have NO real tiling witness in the corpus; row 15 DOES — the
-- certified `Tiling77` (`s = 1/2`, `M = 5`) — but that witness realizes the RATIONAL branch
-- (`s = 1/2 ∈ Q`, so `NotRat s` is false there and none of this file's irrational-branch lemmas
-- apply to it); no witness of the irrational branch's geometric hypotheses (an actual `Y`, `F`,
-- `v ∈ (1, √2)` from a real dissection) exists, consistent with "no real tiling can exercise an
-- irrational branch" (rationality_proofs.md, Review 2 "New controls" section).
--
-- Formalization debt (paper-level PROVED, one un-Lean'd elementary+algebraic argument, only one
-- leaf of ten addressed); not progress on the three /goal outcomes.
import Mathlib.Tactic

open scoped Classical

namespace Erdos634.Row15

/-- `g(x) = (2 − x²)(3 − x²)`, the row-15 tiling-function factor (§0's sine table /
`F = g·Y²`, §5's opening line). -/
noncomputable def g (x : ℝ) : ℝ := (2 - x ^ 2) * (3 - x ^ 2)

/-- `k(x) = g(x)·(1 + x)/(2 + x)`, exactly as §5 defines it ("k(v) ≥ k(s), where
`k = g·(1+x)/(2+x)`"). -/
noncomputable def k (x : ℝ) : ℝ := g x * (1 + x) / (2 + x)

/-- **The factorization identity** (review 2a's repair 3, REPLACING the file's original flawed
"k is unimodal" claim): `k(x) − 4/3 = (x−1)(3x⁴+6x³−9x²−24x−10) / (3(2+x))` for every `x ≠ −2`.
Nailed down and machine-checked BEFORE anything is built on it, per the task's own discipline
("trustworthy before use") and this project's standing rule against unverified identities
((private working notes, not included)). -/
theorem k_minus_four_thirds (x : ℝ) (hx : x ≠ -2) :
    k x - 4 / 3 = (x - 1) * (3 * x ^ 4 + 6 * x ^ 3 - 9 * x ^ 2 - 24 * x - 10) / (3 * (2 + x)) := by
  unfold k g
  have h2 : (2 : ℝ) + x ≠ 0 := by intro h; apply hx; linarith
  field_simp
  ring

/-- **The quartic factor is negative on `[0, 3/2]`** (review 2a's parenthetical, "whose quartic
factor is negative on [0, 3/2]"). Proved by the same bounding argument the repair implicitly uses:
on `[0, 3/2]`, `x⁴ ≤ (3/2)²x²` and `x³ ≤ (3/2)x²`, so the quartic is `≤ (27/4)x² − 24x − 10`, a
quadratic that is itself `≤ −10 < 0` on `[0, 3/2]` (it is decreasing there). -/
theorem quartic_neg_on_Icc (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 3 / 2) :
    3 * x ^ 4 + 6 * x ^ 3 - 9 * x ^ 2 - 24 * x - 10 < 0 := by
  nlinarith [sq_nonneg x, sq_nonneg (x - 3/2), mul_nonneg hx0 hx0,
    mul_nonneg (mul_nonneg hx0 hx0) hx0, mul_nonneg (mul_nonneg hx0 hx0) (mul_nonneg hx0 hx0),
    mul_nonneg hx0 (sub_nonneg.mpr hx1), mul_nonneg (mul_nonneg hx0 hx0) (sub_nonneg.mpr hx1)]

/-- **`k(s) > 4/3` for `s ∈ (0, 1)`**: the half of §5's "v ∈ (1, √2)" leaf applied at `s`. Since
`s ∈ (0,1) ⊂ [0, 3/2]`, `s − 1 < 0` and the quartic factor is negative, so their product is
positive; `3(2+s) > 0`; hence `k(s) − 4/3 > 0`. -/
theorem k_gt_four_thirds_on_unit (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) : k s > 4 / 3 := by
  have hs2 : s ≠ -2 := by linarith
  have hid := k_minus_four_thirds s hs2
  have hq : 3 * s ^ 4 + 6 * s ^ 3 - 9 * s ^ 2 - 24 * s - 10 < 0 :=
    quartic_neg_on_Icc s hs0.le (by linarith)
  have hnum : (s - 1) * (3 * s ^ 4 + 6 * s ^ 3 - 9 * s ^ 2 - 24 * s - 10) > 0 :=
    mul_pos_of_neg_of_neg (by linarith) hq
  have hden : (3:ℝ) * (2 + s) > 0 := by linarith
  have : (s - 1) * (3 * s ^ 4 + 6 * s ^ 3 - 9 * s ^ 2 - 24 * s - 10) / (3 * (2 + s)) > 0 :=
    div_pos hnum hden
  linarith [hid ▸ this]

/-- **`k(v) < 4/3` for `v ∈ (1, 3/2]`** (the review's `v ∈ (1, √2)` is contained here, since
`√2 < 3/2`): now `v − 1 > 0` and the quartic factor is still negative on `[1, 3/2] ⊆ [0, 3/2]`, so
the product is negative, giving `k(v) − 4/3 < 0`. -/
theorem k_lt_four_thirds_gt_one (v : ℝ) (hv1 : 1 < v) (hv2 : v ≤ 3 / 2) : k v < 4 / 3 := by
  have hv2' : v ≠ -2 := by linarith
  have hid := k_minus_four_thirds v hv2'
  have hq : 3 * v ^ 4 + 6 * v ^ 3 - 9 * v ^ 2 - 24 * v - 10 < 0 :=
    quartic_neg_on_Icc v (by linarith) hv2
  have hnum : (v - 1) * (3 * v ^ 4 + 6 * v ^ 3 - 9 * v ^ 2 - 24 * v - 10) < 0 :=
    mul_neg_of_pos_of_neg (by linarith) hq
  have hden : (3:ℝ) * (2 + v) > 0 := by linarith
  have : (v - 1) * (3 * v ^ 4 + 6 * v ^ 3 - 9 * v ^ 2 - 24 * v - 10) / (3 * (2 + v)) < 0 :=
    div_neg_of_neg_of_pos hnum hden
  linarith [hid ▸ this]

/-- **The contradiction §5's leaf needs**: for `s ∈ (0,1)` and `v ∈ (1, 3/2]`, `k(s) ≠ k(v)`
(in fact `k(v) < 4/3 < k(s)`). This is the arithmetic half of "k(v) < 4/3 < k(s). Contradiction" —
the geometric half (that the leaf's hypotheses FORCE `k(v) ≥ k(s)`, so this lemma applies to
derive `False`) is not built here; see the header's "NOT FORMALIZED" note. -/
theorem k_s_ne_k_v (s v : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hv1 : 1 < v) (hv2 : v ≤ 3 / 2) :
    k v < k s := by
  have h1 := k_gt_four_thirds_on_unit s hs0 hs1
  have h2 := k_lt_four_thirds_gt_one v hv1 hv2
  linarith

end Erdos634.Row15

#print axioms Erdos634.Row15.k_minus_four_thirds
#print axioms Erdos634.Row15.quartic_neg_on_Icc
#print axioms Erdos634.Row15.k_gt_four_thirds_on_unit
#print axioms Erdos634.Row15.k_lt_four_thirds_gt_one
#print axioms Erdos634.Row15.k_s_ne_k_v
