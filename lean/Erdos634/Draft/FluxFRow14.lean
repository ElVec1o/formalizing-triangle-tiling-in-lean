-- Draft/FluxFRow14.lean — ROW 14 (rationality/rationality_proofs.md §2, PROVED after two hostile
-- reviews): on the scalene target `(2α, β, α+β)`, an `N`-tiling (any `N`, reflections allowed, not
-- necessarily edge-to-edge) by the `3α + 2β = π` tile with `α ∉ ℚπ` has a rational tile,
-- `s := a/c ∈ ℚ`.  Imported directly by All.lean (stale "NOT imported" header corrected 2026-10-04).
--
-- HEADLINE FINDING (Rule 0.5 survey, done before writing a line of this file).  Grepped
-- `lean/Erdos634/Draft/Flux*.lean` for "Row14", "Row15", "rationality": no hits anywhere in the
-- corpus before this file (the only Draft files matching are FluxDRow11*.lean, FluxDRow12*.lean,
-- FluxDRow13.lean/Witness — rows 11/12/13, not 14/15). So row 14 (this file) and row 15
-- (Draft/FluxFRow15.lean) are NOT rediscoveries.
--
-- Rows 11–13's Draft files reproduce their row via a DIFFERENT, flux/GridChar-based "second proof"
-- (ROW11_RATIONALITY.md's route: a direction character on the tile's edges, summed via
-- `Dissection.flux_cancel`, gives the boundary identity that rationality_proofs.md's Theorem 1
-- gets from a 2-colouring instead — see FluxDRow13.lean's header, "ROUTE (named; differs from
-- §1's)"). rationality_proofs.md's OWN §2 (row 14) and §5 (row 15) routes are pure algebra over
-- ℚ(s) — a coefficient-matching / linear-independence argument plus F4's pigeonhole — and never
-- touch Theorem 1's colouring integer, the flux functional, GridChar, or fAlpha/fBeta at all (see
-- §2's proof: it uses only F2's word for a single side, plus (B)'s irrationality of α). There is
-- also no recorded "second flux proof" of row 14 or row 15 anywhere in (private working notes, not included) (grep of
-- `../row11/ROW11_RATIONALITY.md`, which supplies the rows-11-13 flux route, covers only rows
-- 11–13 by its own text: "a second proof of rationality_proofs.md §1"). So there is nothing to
-- reuse from `GridChar`/`Tri.flux`/`Dissection.flux_cancel` for THIS row's argument; this file
-- formalizes rationality_proofs.md §2 directly, in its own native algebraic form, exactly as §2
-- itself is written (not as a flux reproduction).
--
-- SCOPE OF WHAT IS CLOSED (honest, matching the row-3/row-5 partial-completion style, P54/P55).
-- UNCONDITIONAL: `rat_coeff_unique` (the `{1,s}`-independence step, §2 step 2) and
-- `nonneg_sum_forces_zero` (elementary nonnegativity, part of §2 step 4) are proved in full and
-- need no witness — they are general algebraic facts.
-- CONDITIONAL, at the algebraic level only (exactly like row 13's `Row13.boundary` and Beeson III
-- Thm 1 upstream): `row14_word_to_std_form` packages the tiling word equation
-- `n_a·s + n_b·(1−t) + n_c = M·(1−t)/t·s` (§2 step 1's `t = s² = 2/(q+1)`, step 3's `Y`) into the
-- `r·s + c0 = 0` shape that `rat_coeff_unique` consumes; `row14_rational` composes everything into
-- §2 steps 1–5 in full: word equation + F4 (`nc ≥ 1`, "every side carries a c-edge") ⇒ `s ∈ ℚ`.
-- NOT FORMALIZED, stated plainly: the derivation that `t = 2/(q+1)` IS `s²` under Theorem 1 + the
-- area identity (§2 step 1 itself, upstream algebra shared with rows 11–13's tiling-equation
-- table, `q = N/M²`); the geometric content of F2 (why the corner-angle multiset forces a side
-- with THIS word) and F4 (why every side has a `c`-edge, Beeson III Lemma 5) are taken as
-- hypotheses `hF4`/the shape of `hword`, not derived from a `CongruentDissection`. No
-- `CongruentDissection`-level statement of row 14 exists in this file (no witness of that kind is
-- claimed; see rows 4/11/13 in the corpus for the established precedent of algebra-only closure).
--
-- WITNESS. `rat_coeff_unique` and `nonneg_sum_forces_zero` are unconditional (no hypothesis to
-- witness). `row14_rational`'s hypotheses ARE jointly satisfiable: `row14_witness_s_half` below
-- exhibits `s = 1/2` (so `NotRat s` is FALSE, i.e. the theorem's conclusion `¬ NotRat s`
-- holds trivially there) together with an integer word `(n_a,n_b,n_c) = (1,0,1)`, `M = T = 1`
-- satisfying `hword` and `hF4` exactly, confirming `hword`'s shape is non-vacuous (real numbers,
-- not `False → False`). This matches the paper's own record: rationality_proofs.md §0's model
-- `s = 1/√2` (irrational) has words WITHOUT a c-edge on this side (`nc = 0`), i.e. F4's failure
-- there is exactly what makes the naive model fail — consistent with `row14_rational`'s
-- contrapositive shape (F4 holding + irrational s is exactly what is impossible).
--
-- Formalization debt (paper-level PROVED, one un-Lean'd elementary argument); not progress on the
-- three /goal outcomes (2 and 3 of `/goal` are untouched by this file).
import Mathlib.Tactic


open scoped Classical

namespace Erdos634.Row14

/-- Local stand-in for Mathlib's `Irrational` (written when that `.olean` was not prebuilt in the scratch
environment; Mathlib's `Irrational` is available in the current build, 2026-10-01): `s` is not the image
of any rational. Same content, different name. -/
def NotRat (s : ℝ) : Prop := ¬ ∃ q : ℚ, s = (q : ℝ)

/-- **`{1, s}`-independence when `s` is irrational** (§2 step 2, "Suppose `s ∉ Q`. Then `1` and
`s` are `Q`-independent"). If `r·s + c0 = 0` with `r, c0 : ℚ` and `s` is irrational, then
`r = 0` and `c0 = 0`. -/
theorem rat_coeff_unique {s : ℝ} (hs : NotRat s) (r c0 : ℚ)
    (heq : (r : ℝ) * s + (c0 : ℝ) = 0) : r = 0 ∧ c0 = 0 := by
  by_cases hr : r = 0
  · refine ⟨hr, ?_⟩
    subst hr
    have h0 : (c0 : ℝ) = 0 := by simpa using heq
    exact_mod_cast h0
  · exfalso
    apply hs
    have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr
    have hsr : s * (r : ℝ) = -(c0 : ℝ) := by nlinarith [heq]
    refine ⟨-c0 / r, ?_⟩
    have hseq : s = -(c0 : ℝ) / (r : ℝ) := by
      rw [eq_div_iff hr']; linarith [hsr]
    rw [hseq]; push_cast; ring

/-- **Elementary nonnegativity** (part of §2 step 4): if `b > 0` and `nb·b + nc = 0` with
`nb, nc : ℕ`, then `nb = 0` and `nc = 0`. -/
theorem nonneg_sum_forces_zero {b : ℝ} (hb : 0 < b) (nb nc : ℕ)
    (heq : (nb : ℝ) * b + (nc : ℝ) = 0) : nb = 0 ∧ nc = 0 := by
  have hnb0 : (0:ℝ) ≤ (nb : ℝ) * b := mul_nonneg (Nat.cast_nonneg _) hb.le
  have hnc0 : (0:ℝ) ≤ (nc : ℝ) := Nat.cast_nonneg _
  have h1 : (nb : ℝ) * b = 0 := by linarith
  have h2 : (nc : ℝ) = 0 := by linarith
  have hnb : (nb : ℝ) = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h hb.ne'
  exact ⟨by exact_mod_cast hnb, by exact_mod_cast h2⟩

/-- The `r`-coefficient of the word equation packaged into `ℚ` (see `row14_word_to_std_form`). -/
def rCoeff (na M : ℤ) (T : ℚ) : ℚ := (na : ℚ) - (M : ℚ) * (1 - T) / T

/-- The constant coefficient of the word equation packaged into `ℚ`. -/
def c0Coeff (nb nc : ℕ) (T : ℚ) : ℚ := (nb : ℚ) * (1 - T) + (nc : ℚ)

/-- **The word equation, in `r·s + c0 = 0` form** (§2 steps 1, 3–4). The side `Y` opposite the
single-tile `β` corner carries word `n_a·a + n_b·b + n_c·c` (`F3`); with `a = s, b = 1 − t, c = 1`
(`t = s²`) and `Y = M·(1−t)/t · s` (the tiling equation, `t = 2/(q+1) ∈ Q`, here packaged as the
rational number `T`), this is `r·s + c0 = 0` with `r = n_a − M·(1−T)/T` and
`c0 = n_b·(1−T) + n_c`, both manifestly rational since `n_a, n_b, n_c, M ∈ ℤ` and `T ∈ ℚ`. -/
theorem row14_word_to_std_form (s t : ℝ) (T : ℚ) (ht : t = (T : ℝ)) (ht0 : T ≠ 0)
    (na M : ℤ) (nb nc : ℕ)
    (hword : (na : ℝ) * s + (nb : ℝ) * (1 - t) + (nc : ℝ) = (M : ℝ) * (1 - t) / t * s) :
    (rCoeff na M T : ℝ) * s + (c0Coeff nb nc T : ℝ) = 0 := by
  have hT0 : (T : ℝ) ≠ 0 := by exact_mod_cast ht0
  have key : ((na : ℝ) - (M : ℝ) * (1 - t) / t) * s + ((nb : ℝ) * (1 - t) + (nc : ℝ)) = 0 := by
    linear_combination hword
  have hcast : (rCoeff na M T : ℝ) = (na : ℝ) - (M : ℝ) * (1 - t) / t := by
    unfold rCoeff; rw [ht]; push_cast; ring
  have hcast0 : (c0Coeff nb nc T : ℝ) = (nb : ℝ) * (1 - t) + (nc : ℝ) := by
    unfold c0Coeff; rw [ht]; push_cast; ring
  rw [hcast, hcast0]; exact key

/-- **Row 14's F4 contradiction, assembled** (rationality_proofs.md §2 steps 1–5 in full): if `s`
is irrational, the word equation holds (`t = s²` rational, packaged as `T`), and `F4` holds on
this side (`1 ≤ nc`, "the side carries a `c`-edge"), then `False`. Equivalently, contrapositive:
under the word equation and F4, `s` cannot be irrational, i.e. `s ∈ ℚ`. -/
theorem row14_rational (s t : ℝ) (T : ℚ) (ht : t = (T : ℝ)) (ht0 : T ≠ 0)
    (ht1 : (0:ℝ) < 1 - t) (na M : ℤ) (nb nc : ℕ)
    (hword : (na : ℝ) * s + (nb : ℝ) * (1 - t) + (nc : ℝ) = (M : ℝ) * (1 - t) / t * s)
    (hF4 : 1 ≤ nc) : ¬ NotRat s := by
  intro hs
  have hstd := row14_word_to_std_form s t T ht ht0 na M nb nc hword
  obtain ⟨_, hc0⟩ := rat_coeff_unique hs (rCoeff na M T) (c0Coeff nb nc T) hstd
  have ht1' : (0:ℝ) < 1 - (T:ℝ) := ht ▸ ht1
  have hc0' : (nb : ℝ) * (1 - (T:ℝ)) + (nc : ℝ) = 0 := by
    have : (c0Coeff nb nc T : ℝ) = 0 := by exact_mod_cast hc0
    unfold c0Coeff at this; push_cast at this; linarith
  have hz := nonneg_sum_forces_zero (b := (1 - (T:ℝ))) ht1' nb nc hc0'
  omega

/-- **Non-vacuity witness**: the hypothesis bundle of `row14_rational` (word equation + `F4`) is
satisfiable — at `s = 1/2` (`NotRat s` false, so the conclusion is trivial there, but the
*hypotheses* are real numbers satisfying real equations, not `False → False`): `t = T = 1/4`,
`(n_a, n_b, n_c) = (1, 0, 1)`, `M = 1` satisfy `n_a·s + n_b·(1−t) + n_c = M·(1−t)/t·s`
(`1·(1/2) + 0 + 1 = 3/2 = 1·(3/4)/(1/4)·(1/2)`) and `F4` (`nc = 1 ≥ 1`). -/
theorem row14_witness_s_half :
    ((1:ℤ) : ℝ) * (1/2 : ℝ) + ((0:ℕ):ℝ) * (1 - (1/4:ℝ)) + ((1:ℕ):ℝ)
        = ((1:ℤ):ℝ) * (1 - (1/4:ℝ)) / (1/4:ℝ) * (1/2 : ℝ)
    ∧ (1:ℕ) ≤ (1:ℕ) := by
  constructor
  · norm_num
  · exact le_refl 1

end Erdos634.Row14

#print axioms Erdos634.Row14.rat_coeff_unique
#print axioms Erdos634.Row14.nonneg_sum_forces_zero
#print axioms Erdos634.Row14.row14_word_to_std_form
#print axioms Erdos634.Row14.row14_rational
#print axioms Erdos634.Row14.row14_witness_s_half
