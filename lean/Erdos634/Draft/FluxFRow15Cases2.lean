-- Draft/FluxFRow15Cases2.lean — ROW 15 leaves 3 and 6 of ten
-- (rationality/rationality_proofs.md §5).  Continuation of Draft/FluxFRow15.lean (leaf 10,
-- `k_s_ne_k_v`) and Draft/FluxFRow15Cases.lean (leaves 1, 2, 4, 5, bringing the running total to
-- 5 of 10). Does NOT edit FluxFRow15.lean, FluxFRow15Cases.lean, or any other existing file.
-- Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- RULE 0.5 SURVEY (before writing a line here): grepped `lean/Erdos634` for "Row15", "quartic",
-- "no real root", "HasDerivAt", "StrictMonoOn", "deriv " — no hits outside the two Row15 files
-- above (which do not touch leaves 3/6/7/8/9) and a handful of unrelated files whose "deriv" hit
-- is the English word "derived"/"derive", not `Mathlib`'s `deriv`/`HasDerivAt`/`StrictMonoOn`
-- (confirmed: `grep -rl HasDerivAt lean/Erdos634/` returns nothing at all, including
-- `EquilateralConic.lean`, which the task suggested checking). So there is no calculus
-- (derivative-sign / monotonicity) infrastructure anywhere in this corpus to reuse for leaves
-- 7–9, and no quartic-root-freeness lemma anywhere to reuse for leaf 3. Nothing here is a
-- rediscovery.
--
-- LEAVES CLOSED IN THIS FILE:
--
-- Leaf 3 (deg 3): CLOSED, by an ELEMENTARY route the header of FluxFRow15Cases.lean explicitly
-- doubted was available ("a Sturm-sequence or sum-of-squares certificate for positivity/
-- negativity of a degree-4 polynomial on all of ℝ ... That is a strictly harder shape ... unbounded
-- x does not admit that [interval-bounding] trick"). The doubt about the *interval*-bounding trick
-- was correct; a genuinely different, exact sum-of-squares certificate for the specific quartic
-- §5 names (`r⁴+r³−4r²−2r+5`, the numerator of `n_a`'s quartic-in-r formula) exists and was found
-- by hand (completing the square twice against a numerically-located near-minimizer, then
-- `sympy`-verified as an EXACT polynomial identity before being typed into Lean — the identity
-- itself, not the numerics, is what `ring` checks below):
--   r⁴ + r³ − 4r² − 2r + 5 = (r² + r/2 − 11/5)² + (3/20)(r + 2/3)² + 7/75.
-- Every term on the right is a square (nonneg) or a positive constant, so the quartic is
-- POSITIVE FOR EVERY REAL r — the exact global root-freeness leaf 3 needs, with no interval
-- restriction and no Sturm sequence. (Numerical sanity check, not load-bearing: a 2,000,001-point
-- scan of r ∈ [−10, 10] gives a minimum of ≈0.2678 at r ≈ −1.736, consistent with the identity's
-- floor of 7/75 ≈ 0.0933 plus the two nonneg square terms — the identity is the actual proof, the
-- scan is only what suggested where to center the squares.) This closes leaf 3's arithmetic core
-- exactly as leaves 1 (`row15_deg4_impossible`, FluxFRow15Cases.lean) and 2 close theirs: the
-- geometric identification of the quartic's numerator with the actual word-coefficient `n_a` (via
-- §5's "Y's coordinates in {1,s,s²,s³}" / the degree-3 case's rational-root reduction) is taken as
-- a hypothesis, in the same style as `row15_deg4_impossible`'s `hna` and consistent with the file
-- header's standing note that the word/conjugate bridge itself is not built anywhere in this
-- corpus.
--
-- Leaf 6 (deg 2, P ≥ 0, −1 < v ≤ −s): CLOSED, including the equality-case exclusion the leaf
-- needs beyond leaves 4/5's pattern. §5's own text: "v² ≥ s², so g(v) ≤ g(s). Also Y(s) ≥ Y(v) > 0,
-- and equality would force v = −s and 1+s+v = 0, which is impossible." The equality case is
-- resolved more directly than the prose's own phrasing: `Y(s) = Y(v)` means `h(s) = h(v)`
-- (same denominator, both nonzero), i.e. `(v−s)(1+v+s) = 0` (a `ring`-checked identity); since
-- `v ≤ −s < 0 < s` forces `v ≠ s`, this gives `1 + v + s = 0`, i.e. `v = −1 − s`; but `s > 0`
-- (hypothesis `hs0`) makes `v < −1`, contradicting `hv1 : −1 < v`. So the equality case is
-- impossible outright and only the strict case `Y(v) < Y(s)` survives, closed the same way as
-- leaf 5.
--
-- LEAVES LEFT OPEN, stated plainly (do not round up):
--
-- Leaves 7, 8, 9 (deg 2, P < 0: `v ∉ (−1,1)`; `v ∈ [√2,√3]`; `v ≥ 1.7`) are NOT closed. Per the
-- source, all three ultimately rest on ONE global fact: "F is strictly increasing on (−1,1), with
-- numerator of F′ equal to 2(x⁴+x³−2x−6)" — a genuine calculus claim (a derivative computed and
-- sign-checked on an open interval, then converted to strict monotonicity, then used to compare
-- F at two points). This is a different SHAPE of problem from leaf 3 (which was a pointwise
-- algebraic positivity fact with no derivative anywhere) and from leaves 4/5/6/10 (algebraic sign
-- chases on explicit rational functions). It needs, at minimum: (a) `F` defined as a function of
-- one real variable exactly as §0/§5 set it up (`F = g·Y²` composed with `h`, not yet even stated
-- as a single-variable function anywhere in this corpus outside the `g`/`Y`/`h`/`X`/`rho`
-- primitives in `FluxFRow15.lean`/`FluxFRow15Cases.lean`); (b) computing `HasDerivAt F (2*(x^4+x^3
-- -2*x-6)/(...)) x` for `x ∈ (−1,1)` via Mathlib's derivative combinators (`HasDerivAt.div`,
-- `.mul`, `.pow`, chain rule through `h`), a nontrivial multi-step computation nowhere modeled in
-- this corpus (confirmed by the grep above: zero `HasDerivAt` occurrences anywhere in
-- `lean/Erdos634/`, so there is no local pattern to copy, unlike leaves 1–6/10 which all reuse the
-- `nlinarith`/`div_pos`/`field_simp` idiom already established in `FluxFRow15.lean`); (c) then
-- `StrictMonoOn` from a derivative-sign fact via `StrictMonoOn_of_deriv_pos` or
-- `strictMonoOn_of_hasDerivWithinAt_pos`, and finally comparing `F` at the specific points each of
-- leaves 7–9 names. Each of these three sub-steps is itself routine Mathlib usage in isolation,
-- but chaining all three for the specific composite `F` here, from a zero-derivative-infrastructure
-- starting point, is materially more work than an `nlinarith` call and was not completed within
-- this pass — reported precisely rather than attempted and left half-built (the standing rule
-- against reporting unfinished machinery as progress). This is exactly the P65/P66/P71-style
-- "real infrastructure gap" the task asked to recognize and move past rather than stall on:
-- leaves 7–9 need calculus infrastructure this corpus does not have, not a harder `nlinarith`
-- call. No partial/vacuous lemma is stated for them.
--
-- Formalization debt (paper-level PROVED for all ten leaves, per two hostile reviews recorded in
-- rationality_proofs.md "Label after two reviews"); not progress on the three /goal outcomes.
-- Two of the five previously-open leaves (3 and 6) are now closed by this file, bringing the
-- running total to 7 of 10 arithmetic cores closed (leaves 7, 8, 9 remain open, for the calculus
-- reason above).
import Mathlib.Tactic
import Erdos634.Draft.FluxFRow15
import Erdos634.Draft.FluxFRow15Cases

open scoped Classical

namespace Erdos634.Row15Cases2

open Erdos634.Row15 (g)
open Erdos634.Row15Cases (h Y)

/-! ### Leaf 3 (of the ten) — degree 3: the quartic `r⁴+r³−4r²−2r+5` has no real root. -/

/-- **The exact sum-of-squares identity**, found by centering two squares on a numerically located
near-minimizer and then verifying the polynomial identity symbolically (see file header) — the
identity itself, checked here by `ring`, is what carries the proof; the numerics only located it. -/
theorem quartic_sos (r : ℝ) :
    r ^ 4 + r ^ 3 - 4 * r ^ 2 - 2 * r + 5 =
      (r ^ 2 + r / 2 - 11 / 5) ^ 2 + (3 / 20) * (r + 2 / 3) ^ 2 + 7 / 75 := by
  ring

/-- **The quartic is positive for every real `r`** (global, no interval restriction — exactly what
leaf 3 needs and what the file header of `FluxFRow15Cases.lean` doubted was available by
elementary means). -/
theorem quartic_pos (r : ℝ) : 0 < r ^ 4 + r ^ 3 - 4 * r ^ 2 - 2 * r + 5 := by
  rw [quartic_sos]
  have h1 : (0:ℝ) ≤ (r ^ 2 + r / 2 - 11 / 5) ^ 2 := sq_nonneg _
  have h2 : (0:ℝ) ≤ (3 / 20) * (r + 2 / 3) ^ 2 := by positivity
  linarith

/-- **Leaf 3 (deg 3) closed**: if `M ≥ 1`, `r ≠ 1`, `r ≠ −2`, and the s-coordinate `n_a` of `Y`'s
word equals `−M·(r⁴+r³−4r²−2r+5)/((r−1)²(r+2)²)` exactly as §5 computes for the degree-3 case,
then `n_a` cannot be a non-negative integer (`F3`). Same shape as leaf 1
(`row15_deg4_impossible`, `FluxFRow15Cases.lean`): the word-coefficient identification is a
hypothesis (`hna`), the arithmetic contradiction is what is proved. -/
theorem row15_deg3_impossible (M : ℤ) (r : ℝ) (hM : 1 ≤ M) (hr1 : r ≠ 1) (hr2 : r ≠ -2)
    (na : ℤ) (hna_nonneg : 0 ≤ na)
    (hna : (na : ℝ) = -(M : ℝ) * (r ^ 4 + r ^ 3 - 4 * r ^ 2 - 2 * r + 5) /
      ((r - 1) ^ 2 * (r + 2) ^ 2)) : False := by
  have hMr : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hquart : 0 < r ^ 4 + r ^ 3 - 4 * r ^ 2 - 2 * r + 5 := quartic_pos r
  have hr1' : r - 1 ≠ 0 := sub_ne_zero.mpr hr1
  have hr2' : r + 2 ≠ 0 := by intro hcon; apply hr2; linarith
  have h1sq : (0:ℝ) < (r - 1) ^ 2 := by
    rcases lt_or_gt_of_ne hr1' with hlt1 | hlt1
    · nlinarith
    · nlinarith
  have h2sq : (0:ℝ) < (r + 2) ^ 2 := by
    rcases lt_or_gt_of_ne hr2' with hlt2 | hlt2
    · nlinarith
    · nlinarith
  have hden : (0:ℝ) < (r - 1) ^ 2 * (r + 2) ^ 2 := mul_pos h1sq h2sq
  have hnum : (0:ℝ) < (M : ℝ) * (r ^ 4 + r ^ 3 - 4 * r ^ 2 - 2 * r + 5) :=
    mul_pos (by linarith) hquart
  have hlt : (na : ℝ) < 0 := by
    rw [hna]
    exact div_neg_of_neg_of_pos (by linarith) hden
  have hge : (0 : ℝ) ≤ (na : ℝ) := by exact_mod_cast hna_nonneg
  linarith

/-! ### Leaf 6 (of the ten) — degree 2, `P ≥ 0`, `−1 < v ≤ −s`. -/

theorem g_v_le_g_s_leaf6 (s v : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hv1 : -1 < v) (hv2 : v ≤ -s) :
    g v ≤ g s := by
  unfold g
  have hvs : s ≤ -v := by linarith
  have hv0 : 0 ≤ -v := by linarith
  have hsqle : s ^ 2 ≤ v ^ 2 := by nlinarith [mul_le_mul hvs hvs hs0.le hv0]
  have hsum_lt2 : s ^ 2 + v ^ 2 < 2 := by nlinarith
  -- g(v) - g(s) = (v²-s²) * ((v²+s²) - 5), and (v²+s²) - 5 < -3 < 0, v²-s² ≥ 0
  nlinarith [mul_nonneg (sub_nonneg.mpr hsqle) (by linarith : (0:ℝ) ≤ 5 - (v ^ 2 + s ^ 2))]

theorem h_v_pos_leaf6 (v : ℝ) (hv1 : -1 < v) (hv2 : v < 1) : 0 < h v := by
  unfold Erdos634.Row15Cases.h; nlinarith

theorem h_s_pos_leaf6 (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) : 0 < h s := by
  unfold Erdos634.Row15Cases.h; nlinarith

/-- **The equality case is impossible**: if `Y s = Y v` (with `s ∈ (0,1)`, `v ∈ (−1,−s]`), then
`False`. This is the sub-argument leaf 6 needs beyond leaves 4/5's pattern (§5: "equality would
force `v = −s` and `1+s+v = 0`, which is impossible") — resolved directly here via `h s = h v`. -/
theorem row15_leaf6_no_equality (s v : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (hv1 : -1 < v) (hv2 : v ≤ -s) (hYeq : Y s = Y v) : False := by
  have hs2 : v < 1 := by linarith
  have hhs : 0 < h s := h_s_pos_leaf6 s hs0 hs1
  have hhv : 0 < h v := h_v_pos_leaf6 v hv1 hs2
  have hYeq' : (1:ℝ) / h s = 1 / h v := by
    unfold Erdos634.Row15Cases.Y at hYeq; exact hYeq
  have hheq : h s = h v := by
    have hcross := (div_eq_div_iff hhs.ne' hhv.ne').mp hYeq'
    linarith [hcross]
  have hfact : (v - s) * (1 + v + s) = 0 := by
    have hid : (v - s) * (1 + v + s) = h s - h v := by unfold Erdos634.Row15Cases.h; ring
    rw [hid, hheq]; ring
  have hvs : v - s ≠ 0 := by
    intro hc
    have : v = s := by linarith
    rw [this] at hv2
    linarith
  have hsum : 1 + v + s = 0 := by
    rcases mul_eq_zero.mp hfact with h1 | h1
    · exact absurd h1 hvs
    · exact h1
  linarith

/-- **Leaf 6 (deg 2, `P ≥ 0`, `−1 < v ≤ −s`) closed** (its arithmetic core; the bridge `Y v ≤ Y s`
is a hypothesis, as in leaves 4/5, see `FluxFRow15Cases.lean`'s header): if `s ∈ (0,1)`,
`v ∈ (−1,−s]`, `Y v ≤ Y s`, and `F(s) = F(v)` in the `g·Y²` form, then `False`. -/
theorem row15_Pge0_v_in_neg1_negs (s v : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (hv1 : -1 < v) (hv2 : v ≤ -s) (hYle : Y v ≤ Y s)
    (hEq : g s * Y s ^ 2 = g v * Y v ^ 2) : False := by
  have hs2 : v < 1 := by linarith
  have hYv0 : 0 < Y v := by
    unfold Erdos634.Row15Cases.Y; exact div_pos one_pos (h_v_pos_leaf6 v hv1 hs2)
  have hYs0 : 0 < Y s := by
    unfold Erdos634.Row15Cases.Y; exact div_pos one_pos (h_s_pos_leaf6 s hs0 hs1)
  have hg : g v ≤ g s := g_v_le_g_s_leaf6 s v hs0 hs1 hv1 hv2
  have hgs2 : g s > 2 := Erdos634.Row15Cases.g_s_gt_two s hs0 hs1
  rcases hYle.lt_or_eq with hlt | heq
  · -- strict case: same chain as leaves 4/5
    have hsq : Y v ^ 2 < Y s ^ 2 := by nlinarith
    have hchain1 : g s * Y v ^ 2 < g s * Y s ^ 2 := by nlinarith
    have hchain2 : g v * Y v ^ 2 ≤ g s * Y v ^ 2 := by nlinarith [mul_nonneg hYv0.le hYv0.le]
    nlinarith
  · -- equality case: impossible outright
    exact row15_leaf6_no_equality s v hs0 hs1 hv1 hv2 heq.symm

end Erdos634.Row15Cases2

#print axioms Erdos634.Row15Cases2.quartic_sos
#print axioms Erdos634.Row15Cases2.quartic_pos
#print axioms Erdos634.Row15Cases2.row15_deg3_impossible
#print axioms Erdos634.Row15Cases2.g_v_le_g_s_leaf6
#print axioms Erdos634.Row15Cases2.h_v_pos_leaf6
#print axioms Erdos634.Row15Cases2.h_s_pos_leaf6
#print axioms Erdos634.Row15Cases2.row15_leaf6_no_equality
#print axioms Erdos634.Row15Cases2.row15_Pge0_v_in_neg1_negs
