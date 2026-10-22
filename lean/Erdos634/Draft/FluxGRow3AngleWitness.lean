-- Draft/FluxGRow3AngleWitness.lean — concrete `Irrational (α / π)` witness for row 3's
-- `hairr` hypothesis (`FluxGRow3Step5.witness_step5`, `FluxGRow3TargetDirs`, `FluxGRow3Weight`,
-- `FluxGRow3Placement.flux_gauss_direct_instance`, `FluxGRow3Cancel.gaussWeightA_shift`), following
-- the `α456_irr` / Niven pattern already used for row 4 (`FluxRow4Witness.lean`).
--
-- SURVEY (P88/Rule 0.5, run before writing):
--   - Existence check: `ls -la lean/Erdos634/Draft/FluxGRow3AngleWitness.lean` -> "No such file or
--     directory" (confirmed absent). `grep -n "FluxGRow3AngleWitness" lean/Erdos634/All.lean` -> no
--     output (confirmed not integrated; this file is NOT appended to All.lean, per the task).
--   - (private working notes, not included) (593 lines, read in full this session): Proposition RP
--     is stated for a FAMILY of angles ("If ABC has angles (α, α, π−2α)... N is even", with the sole
--     standing requirement `α ∉ ℚπ`, `0 < α < π/2`); it does NOT pin a particular numeric α. Every
--     concrete α appearing in the paper/PROOF.md's own worked checks (`tan α = 1/2`, Pythagorean
--     (5,12,13), `tan α = 1/3`, and the negative control `α = π/4`) is used there only to spot-check
--     the tile-value/cancellation arithmetic, NOT as a distinguished witness value the Lean theorems
--     require — the Lean theorems (`targetIso_flux_gauss`, `witness_step5`, `gaussWeightA_shift`,
--     `flux_gauss_direct_instance`, row3's grid lemmas) are literally universally quantified over
--     `α`, `lam` subject only to `0 < α`, `α < π/2`, `0 < lam`, `Irrational (α/π)`. So ANY concrete α
--     satisfying those three real constraints is a fully valid witness for these theorems' purposes;
--     the specific value does not matter, only that it is exhibited and irrational-over-π.
--   - `FluxGRow3Step5.lean:66-77,208-211` states explicitly: the corpus's only worked numeric example
--     for row 3, `α = π/4`, FAILS `hairr` (`π/4 / π = 1/4 ∈ ℚ`), and no concrete α with a *proved*
--     `Irrational (α/π)` exists anywhere in the Draft corpus for row 3. `FluxGRow3.lean`'s own
--     `grid_unique_witness` (`α = √2·π`, so `α/π = √2`) discharges `Irrational (α/π)` but is NOT a
--     valid row-3 angle: `α = √2·π ≈ 4.44 > π/2`, failing `hα2`. So it witnesses `grid_unique`'s
--     bare hypothesis (which does not carry `0 < α < π/2`) but not `witness_step5`'s three geometric
--     constraints together.
--   - `FluxRow4Witness.lean:43-57` (`α456`, `T456.angleAt 0` of the real `(4,5,6)` triangle,
--     `cos α456 = 3/4`) already proves `α456_irr : ¬ ∃ r : ℚ, α456 = r * π` via Mathlib's Niven
--     theorem (`niven`, imported through `FluxPaperWitness`), with a witness value that happens to
--     also satisfy `0 < α456 < π/2` (shown below, reusing `cos_α456` — NOT reproved from scratch).
--   - `right_parity_check.py` / `FluxGRow3Witness.lean` (P74): no `N=2`-control or other concrete
--     numeric example with a PROVED irrational `α/π` was found there either; that file's witnesses
--     (per its own header) are for `hgridBC`-style grid membership, not `hairr`.
--   - Niven's theorem in Mathlib: `Mathlib.NumberTheory.Niven` (cosine-based: rational multiples of
--     π have cosine in a fixed 5-element rational set). The row 3 examples with rational TANGENT
--     (`tan α = 1/2`, `1/3`) are not directly Niven-amenable this way (their cosines, e.g. `2/√5`,
--     are irrational, so Niven's cosine criterion does not apply to them at all — neither proving nor
--     disproving `α ∈ ℚπ` for those values by this route). Reusing `α456` (rational COSINE `3/4`,
--     the same shape Niven needs) sidesteps that gap entirely rather than attempting a new
--     irrationality proof for a tangent-parametrised angle.
--
-- CONCLUSION: `α456` is a full, ready-made, non-vacuous witness for row 3's `hairr` (plus its `hα`,
-- `hα2`) — no new irrationality lemma is needed, only the two order facts below (`0 < α456`,
-- `α456 < π/2`), proved here for the first time by reusing `cos_α456` and `cornerAngle_mem'`
-- (both already proved in `FluxRow4Witness.lean`/`FluxPaperWitness.lean`, not reproved). This
-- concretely instantiates `FluxGRow3Step5.witness_step5` end to end, discharging every one of its
-- hypotheses including `hairr`.
import Erdos634.Draft.FluxGRow3Step5
import Erdos634.Draft.FluxRow4Witness

open scoped Classical

namespace Erdos634.Geometry.Row3

open Erdos634.Draft.FluxRow4Witness Erdos634.Draft.FluxPaperWitness

/-- `α456` (row 4's real `(4,5,6)`-tile angle, `cos α456 = 3/4`) is strictly positive: if it were
`0`, `cos α456` would be `cos 0 = 1`, contradicting `cos_α456 : Real.cos α456 = 3/4`. -/
theorem α456_pos : 0 < α456 := by
  have h0 : 0 ≤ α456 := (cornerAngle_mem' _ _ _).1
  rcases h0.lt_or_eq with h | h
  · exact h
  · exfalso
    have hc := cos_α456
    rw [← h, Real.cos_zero] at hc
    norm_num at hc

/-- `α456 < π/2`: `cos` is strictly decreasing on `[0, π]` (`Real.cos_lt_cos_of_nonneg_of_le_pi`);
`cos α456 = 3/4 > 0 = cos(π/2)`, so `α456 < π/2` (else `cos α456 < cos(π/2) = 0`, contradicting
`3/4 > 0`). Reuses the identical argument already carried out inline in
`FluxRow4Witness.angle2_456`'s proof (`hle`), not reproved from scratch. -/
theorem α456_lt_pi_div_two : α456 < Real.pi / 2 := by
  by_contra h
  push Not at h
  have hαπ : α456 ≤ Real.pi := (cornerAngle_mem' _ _ _).2
  rcases h.lt_or_eq with h' | h'
  · have := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity : (0:ℝ) ≤ Real.pi / 2) hαπ h'
    rw [Real.cos_pi_div_two, cos_α456] at this
    norm_num at this
  · have hc := cos_α456
    rw [← h', Real.cos_pi_div_two] at hc
    norm_num at hc

/-- `α456_irr` (`FluxRow4Witness.lean`) is stated as `¬∃ r : ℚ, α456 = r * π`; row 3's theorems want
`Irrational (α456 / π)`. The two are equivalent (`π ≠ 0`); this converts, without reproving the
underlying Niven argument. -/
theorem α456_div_pi_irr : Irrational (α456 / Real.pi) := by
  rintro ⟨r, hr⟩
  apply α456_irr
  refine ⟨r, ?_⟩
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp at hr
  linarith [hr]

/-- **The concrete row-3 witness.** `α456` satisfies every real-valued hypothesis of
`FluxGRow3Step5.witness_step5` (`0 < α456`, `α456 < π/2`, `Irrational (α456 / π)` via
`α456_irr`), so, at `lam := 1`, the theorem applies outright at every grid degree `X`: this is the
FIRST fully concrete, non-hypothetical instance of row 3's target-side flux computation with its
irrationality hypothesis genuinely discharged (not vacuous, not `α = π/4`). -/
theorem witness_step5_concrete (X : ℤ) :
    (targetIso α456 1 α456_pos α456_lt_pi_div_two one_pos).flux
        (gaussWeight α456
          ((targetIso α456 1 α456_pos α456_lt_pi_div_two one_pos).leftUnit 0).angle.toReal X)
      = (Complex.I : ℂ) ^
          (gridJ α456
            ((targetIso α456 1 α456_pos α456_lt_pi_div_two one_pos).leftUnit 0).angle.toReal
            ((targetIso α456 1 α456_pos α456_lt_pi_div_two one_pos).leftUnit 0).angle) *
        ((if gridK α456
              ((targetIso α456 1 α456_pos α456_lt_pi_div_two one_pos).leftUnit 0).angle.toReal
              ((targetIso α456 1 α456_pos α456_lt_pi_div_two one_pos).leftUnit 0).angle = X
            then (2 * (1:ℝ) * Real.cos α456 : ℂ) else 0)
          - (if gridK α456
                ((targetIso α456 1 α456_pos α456_lt_pi_div_two one_pos).leftUnit 0).angle.toReal
                ((targetIso α456 1 α456_pos α456_lt_pi_div_two one_pos).leftUnit 0).angle - 1 = X
              then ((1:ℝ) : ℂ) else 0)
          - (if gridK α456
                ((targetIso α456 1 α456_pos α456_lt_pi_div_two one_pos).leftUnit 0).angle.toReal
                ((targetIso α456 1 α456_pos α456_lt_pi_div_two one_pos).leftUnit 0).angle + 1 = X
              then ((1:ℝ) : ℂ) else 0)) :=
  witness_step5 α456 1 α456_pos α456_lt_pi_div_two one_pos α456_div_pi_irr X

end Erdos634.Geometry.Row3

#print axioms Erdos634.Geometry.Row3.α456_pos
#print axioms Erdos634.Geometry.Row3.α456_lt_pi_div_two
#print axioms Erdos634.Geometry.Row3.α456_div_pi_irr
#print axioms Erdos634.Geometry.Row3.witness_step5_concrete
