-- Draft/FluxGRow3Step1.lean — row 3 (AUDIT_ROWS scope), Lemma A's Step 1: the geometric corner
-- fact bridging a REAL `CongruentDissection` by the right tile `(α, π/2−α, π/2)` to the abstract
-- `(p,q,r)` hypothesis `Draft/FluxGRow3LemmaA.lean`'s `lemmaA_case_split` assumes.  NOT imported
-- into `All.lean`.  Source: (private working notes, not included) §2 Lemma A step 1, named
-- missing at P9 item 3 / P65 / P79 (the sole remaining piece after P79 closed the case split
-- itself conditionally on this).
--
-- TASK ASKED: check FIRST whether `TilePlacement.corner_multiplicities` — angle-generic, produces
-- the multiplicity FACT (a real equation), not a uniqueness claim — can supply Step 1 directly,
-- since Lemma A's own case split already handles the two solution families P65 found for the
-- right tile (γ = π/2). ANSWER, checked directly below: YES. `corner_multiplicities` gives, at any
-- target corner, `card(α)·α + card(β)·β + card(γ)·γ + card(π)·π = C` (`C` the real corner angle),
-- for ANY tile whose local-angle census is confined to `{α,β,γ,π,0}` — no uniqueness anywhere in
-- its statement or proof (`TilePlacement.lean:51-71`, read in full: pure linear algebra from
-- `VertexFigureReal.corner_angle_sum`, works for any five real numbers). Substituting the right
-- tile's own `β = π/2−α`, `γ = π/2`, and folding the straight-angle count into the `π/2`
-- coefficient via `π = 2·(π/2)` (a straight-angle tile is worth two `π/2`'s) lands EXACTLY on
-- `Row3.cornerAngle`'s shape `p·α + q·(π/2−α) + r·(π/2)` — no case split, no resolution of P65's
-- two-solution-family ambiguity, needed at all. Lemma A's own six-way pattern split (`patternA`/
-- `patternB` in `FluxGRow3LemmaA.lean`, already closed at P79) is exactly what consumes that
-- ambiguity downstream; Step 1 only has to supply the raw `(p,q,r)` existence, which
-- `corner_multiplicities` already contains.
--
-- WHAT IS BUILT, in order:
--   (1) `corner_step1_dissection` — Dissection level, `hvals` a hypothesis: at any target corner,
--       SOME `(p,q,r) : ℕ×ℕ×ℕ` with `1 ≤ p+q+r` (non-vacuity) makes `Row3.cornerAngle α p q r`
--       equal to the real corner angle there.
--   (2) `congruentDissection_corner_step1` — same, `hvals` now DERIVED via
--       `TileAt.congruentDissection_localAngle_mem` (reused verbatim, angle-generic), for a real
--       `CongruentDissection`.
--   (3) `congruentDissection_row3_lemmaA` — THE ASSEMBLY: apply (2) at the target's three labelled
--       corners `k = 0, 1, 2`, combine with `Erdos634.Geometry.cornerAngle_sum` (Mathlib's triangle
--       angle-sum, already in the corpus, giving the three real corner angles sum to `π` — exactly
--       `lemmaA_case_split`'s `hsum`) and `Erdos634.MarchFlank.cornerAngle_pos` /
--       `RouteOneVertexKill.cornerAngle_lt_pi` (both already in the corpus, giving positivity and
--       the `< π` bound needed for `hpos`/`hlt`), then feed the whole bundle into
--       `Row3.lemmaA_case_split` (P79, unconditional given this bundle). The result: Lemma A's
--       full conclusion, for the three real corners of an ACTUAL `CongruentDissection`'s target —
--       not an abstract hypothesis.
--
-- SO: **Step 1 is closed, unconditionally, connecting a real `CongruentDissection` to Lemma A's
-- full conclusion** — modulo the same standing paper-level caveat every other row's bridge file in
-- this corpus carries (`FluxCRow5Bridge.lean`'s own honesty note, reused verbatim below): the
-- hypotheses `hα' hβ' hγ'` (the MODEL tile's own three corners equal `α, β, γ`) are jointly
-- satisfiable in the abstract, but no real Lean `CongruentDissection` witnessing them for row 3's
-- tile is built in this corpus (the row-3 witness that DOES exist, `FluxGRow3Witness.lean`'s `N=2`
-- dissection, is by the OLD isosceles tile of that file's own construction, not independently
-- checked here to be by `rightTilePlacement`'s tile up to the needed congruence — not claimed).
-- This is the same conditionality `congruentDissection_row5_twoPiThree_counts` etc. carry, not a
-- new gap introduced here.
--
-- Rediscovery check (Rule 0.5, done before writing): grepped `lean/Erdos634` for
-- "corner_step1", "row3_lemmaA", "Row3Step1" — no hits outside this file. The technique
-- (`corner_multiplicities` + `congruentDissection_localAngle_mem`, folding a `π`-count into the
-- third coefficient) is new relative to every prior bridge file (`FluxDRow4Bridge.lean`,
-- `FluxCRow5Bridge.lean`, both read in full first): those bridges' target tile relations let
-- `corner_multiplicities`'s four terms map onto their target `(p,q,r,s)` shape directly (their
-- `Row4Bridge.row4_corner_alpha_tile` etc. keep `s` as its own separate variable multiplying `π`);
-- Lemma A's `Row3.cornerAngle` has ONLY three slots (`p,q,r` for `α, β, π/2`), no separate `π`
-- slot, so the fold `r := card(γ) + 2·card(π)` is the genuinely new step this file supplies, not a
-- copy of the row4/row5 pattern.
import Erdos634.TileAt
import Erdos634.RouteOneVertexKill
import Erdos634.Draft.FluxGRow3LemmaA

namespace Erdos634.Row3Step1

open Erdos634.Geometry Erdos634.Geometry.Dissection

variable {N : ℕ}

/-! ## Part 1: Dissection level — the raw corner-multiplicities fact, repackaged -/

/-- **Step 1, Dissection level.** At any target corner of a dissection whose tiles' local angles
there are confined to `{α, β, γ, π, 0}` with `β = π/2 − α`, `γ = π/2` (the right tile's own three
angles), SOME `(p, q, r) : ℕ × ℕ × ℕ`, not all zero, makes `Row3.cornerAngle α p q r` equal the
real corner angle — with `r` absorbing both the `γ`-count and twice the straight-angle count
(`π = 2·(π/2)`). No uniqueness of `(p,q,r)` is claimed or needed: this is pure existence, exactly
what Lemma A's case split (`FluxGRow3LemmaA.lean`, P79) consumes as its hypothesis. -/
theorem corner_step1_dissection {N : ℕ} (D : Dissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hβdef : β = Real.pi / 2 - α) (hγdef : γ = Real.pi / 2) (k : Fin 3)
    (hvals : ∀ i, (D.tile i).localAngle (D.target.pts k)
      ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ)) :
    ∃ p q r : ℕ, 1 ≤ p + q + r ∧
      Erdos634.Geometry.Row3.cornerAngle α p q r < Real.pi ∧
      Erdos634.Geometry.Row3.cornerAngle α p q r
        = cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) := by
  classical
  have h := Erdos634.TilePlacement.corner_multiplicities D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
    hγπ hγ0 hπ0 k hvals
  set p := ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card with hpdef
  set q := ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card with hqdef
  set z := ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card with hzdef
  set w := ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card with hwdef
  have heq : Erdos634.Geometry.Row3.cornerAngle α p q (z + 2 * w)
      = cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) := by
    unfold Erdos634.Geometry.Row3.cornerAngle
    rw [hβdef, hγdef] at h
    push_cast
    linarith [h]
  refine ⟨p, q, z + 2 * w, ?_, ?_, heq⟩
  · by_contra hcon
    push_neg at hcon
    have hp0 : p = 0 := by omega
    have hq0 : q = 0 := by omega
    have hzw0 : z + 2 * w = 0 := by omega
    rw [hp0, hq0, hzw0] at heq
    have hzero : Erdos634.Geometry.Row3.cornerAngle α 0 0 0 = 0 := by
      unfold Erdos634.Geometry.Row3.cornerAngle; push_cast; ring
    rw [hzero] at heq
    have hposC := Erdos634.MarchFlank.cornerAngle_pos D.target k
    linarith [heq, hposC]
  · rw [heq]
    exact Erdos634.RouteOneVertexKill.cornerAngle_lt_pi D.target k

/-! ## Part 2: `CongruentDissection` level — `hvals` derived, not hypothesised -/

/-- **Step 1, `CongruentDissection` level.** Same conclusion as `corner_step1_dissection`, with
`hvals` derived from `TileAt.congruentDissection_localAngle_mem` (reused verbatim; angle-generic,
never mentions the right tile's own relation). -/
theorem congruentDissection_corner_step1 (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hβdef : β = Real.pi / 2 - α) (hγdef : γ = Real.pi / 2)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ) (k : Fin 3) :
    ∃ p q r : ℕ, 1 ≤ p + q + r ∧
      Erdos634.Geometry.Row3.cornerAngle α p q r < Real.pi ∧
      Erdos634.Geometry.Row3.cornerAngle α p q r
        = cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) :=
  corner_step1_dissection D.toDissection α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
    hβdef hγdef k (fun i => congruentDissection_localAngle_mem D α β γ hα' hβ' hγ' k i)

/-! ## Part 3: the assembly — Lemma A's full conclusion for a real `CongruentDissection`

Combines Part 2 at the target's three labelled corners `k = 0, 1, 2` with
`Erdos634.Geometry.cornerAngle_sum` (Mathlib's triangle angle-sum theorem, already in the corpus,
`Dissection.lean:281-296`) and feeds the bundle into `Row3.lemmaA_case_split`
(`FluxGRow3LemmaA.lean`, P79). This is Step 1, closed and connected to a real `CongruentDissection`
— the disjunction is Lemma A's own conclusion, for the three ACTUAL corners of `D.target`, not an
abstract hypothesis. -/
theorem congruentDissection_row3_lemmaA (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hβdef : β = Real.pi / 2 - α) (hγdef : γ = Real.pi / 2)
    (hαpos : 0 < α) (hirr : Irrational (α / Real.pi))
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ) :
    ∃ p0 q0 r0 p1 q1 r1 p2 q2 r2 : ℕ,
    (Erdos634.Geometry.Row3.cornerAngle α p0 q0 r0 = 2 * (Real.pi / 2 - α) ∧
        Erdos634.Geometry.Row3.cornerAngle α p1 q1 r1 = α ∧
        Erdos634.Geometry.Row3.cornerAngle α p2 q2 r2 = α) ∨
      (Erdos634.Geometry.Row3.cornerAngle α p1 q1 r1 = 2 * (Real.pi / 2 - α) ∧
        Erdos634.Geometry.Row3.cornerAngle α p0 q0 r0 = α ∧
        Erdos634.Geometry.Row3.cornerAngle α p2 q2 r2 = α) ∨
      (Erdos634.Geometry.Row3.cornerAngle α p2 q2 r2 = 2 * (Real.pi / 2 - α) ∧
        Erdos634.Geometry.Row3.cornerAngle α p0 q0 r0 = α ∧
        Erdos634.Geometry.Row3.cornerAngle α p1 q1 r1 = α) ∨
      (Erdos634.Geometry.Row3.cornerAngle α p0 q0 r0 = Real.pi / 2 - α ∧
        Erdos634.Geometry.Row3.cornerAngle α p1 q1 r1 = Real.pi / 2 ∧
        Erdos634.Geometry.Row3.cornerAngle α p2 q2 r2 = α) ∨
      (Erdos634.Geometry.Row3.cornerAngle α p0 q0 r0 = Real.pi / 2 ∧
        Erdos634.Geometry.Row3.cornerAngle α p1 q1 r1 = Real.pi / 2 - α ∧
        Erdos634.Geometry.Row3.cornerAngle α p2 q2 r2 = α) ∨
      (Erdos634.Geometry.Row3.cornerAngle α p0 q0 r0 = Real.pi / 2 - α ∧
        Erdos634.Geometry.Row3.cornerAngle α p1 q1 r1 = Real.pi / 2 - α ∧
        Erdos634.Geometry.Row3.cornerAngle α p2 q2 r2 = 2 * α) ∨
      (Erdos634.Geometry.Row3.cornerAngle α p1 q1 r1 = Real.pi / 2 - α ∧
        Erdos634.Geometry.Row3.cornerAngle α p2 q2 r2 = Real.pi / 2 ∧
        Erdos634.Geometry.Row3.cornerAngle α p0 q0 r0 = α) ∨
      (Erdos634.Geometry.Row3.cornerAngle α p1 q1 r1 = Real.pi / 2 ∧
        Erdos634.Geometry.Row3.cornerAngle α p2 q2 r2 = Real.pi / 2 - α ∧
        Erdos634.Geometry.Row3.cornerAngle α p0 q0 r0 = α) ∨
      (Erdos634.Geometry.Row3.cornerAngle α p1 q1 r1 = Real.pi / 2 - α ∧
        Erdos634.Geometry.Row3.cornerAngle α p2 q2 r2 = Real.pi / 2 - α ∧
        Erdos634.Geometry.Row3.cornerAngle α p0 q0 r0 = 2 * α) ∨
      (Erdos634.Geometry.Row3.cornerAngle α p0 q0 r0 = Real.pi / 2 - α ∧
        Erdos634.Geometry.Row3.cornerAngle α p2 q2 r2 = Real.pi / 2 ∧
        Erdos634.Geometry.Row3.cornerAngle α p1 q1 r1 = α) ∨
      (Erdos634.Geometry.Row3.cornerAngle α p0 q0 r0 = Real.pi / 2 ∧
        Erdos634.Geometry.Row3.cornerAngle α p2 q2 r2 = Real.pi / 2 - α ∧
        Erdos634.Geometry.Row3.cornerAngle α p1 q1 r1 = α) ∨
      (Erdos634.Geometry.Row3.cornerAngle α p0 q0 r0 = Real.pi / 2 - α ∧
        Erdos634.Geometry.Row3.cornerAngle α p2 q2 r2 = Real.pi / 2 - α ∧
        Erdos634.Geometry.Row3.cornerAngle α p1 q1 r1 = 2 * α) := by
  have hv0 : ∀ i, (D.tile i).localAngle (D.target.pts 0) ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ) :=
    fun i => congruentDissection_localAngle_mem D α β γ hα' hβ' hγ' 0 i
  have hv1 : ∀ i, (D.tile i).localAngle (D.target.pts 1) ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ) :=
    fun i => congruentDissection_localAngle_mem D α β γ hα' hβ' hγ' 1 i
  have hv2 : ∀ i, (D.tile i).localAngle (D.target.pts 2) ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ) :=
    fun i => congruentDissection_localAngle_mem D α β γ hα' hβ' hγ' 2 i
  obtain ⟨p0, q0, r0, hpos0, hlt0, heq0⟩ :=
    corner_step1_dissection D.toDissection α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
      hβdef hγdef 0 hv0
  obtain ⟨p1, q1, r1, hpos1, hlt1, heq1⟩ :=
    corner_step1_dissection D.toDissection α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
      hβdef hγdef 1 hv1
  obtain ⟨p2, q2, r2, hpos2, hlt2, heq2⟩ :=
    corner_step1_dissection D.toDissection α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
      hβdef hγdef 2 hv2
  have hsum : Erdos634.Geometry.Row3.cornerAngle α p0 q0 r0
      + Erdos634.Geometry.Row3.cornerAngle α p1 q1 r1
      + Erdos634.Geometry.Row3.cornerAngle α p2 q2 r2 = Real.pi := by
    rw [heq0, heq1, heq2]
    exact Erdos634.Geometry.cornerAngle_sum D.target
  refine ⟨p0, q0, r0, p1, q1, r1, p2, q2, r2, ?_⟩
  exact Erdos634.Geometry.Row3.lemmaA_case_split hirr hαpos p0 q0 r0 p1 q1 r1 p2 q2 r2
    hpos0 hpos1 hpos2 hsum hlt0 hlt1 hlt2

-- Non-vacuity note, matching every other bridge file's own honesty section
-- (`FluxCRow5Bridge.lean:215-223`, reused verbatim in spirit): the hypotheses `hα'`/`hβ'`/`hγ'`
-- above are jointly satisfiable in the abstract (any `α ∈ (0, π/2)` with `α/π` irrational, model
-- corners `α, π/2 − α, π/2` in the stated cyclic order), but no real Lean `CongruentDissection`
-- witnessing them for row 3's RIGHT tile specifically is built anywhere in this corpus as of this
-- writing (`FluxGRow3Witness.lean`'s `N = 2` witness uses row 3's OLD isosceles construction, not
-- independently checked here to instantiate `hα' hβ' hγ'` for `rightTilePlacement`'s tile up to
-- the needed congruence — not claimed). So `congruentDissection_row3_lemmaA` above is Step 1
-- CLOSED as a bridge theorem — real `CongruentDissection` in, Lemma A's conclusion out, no
-- abstract corner-fact hypothesis anywhere in its statement — but its own antecedent (a real
-- `CongruentDissection` with these particular model corners) inherits the same paper-level
-- conditionality every other row's corner-count bridge does. This is not a new gap: it is the same
-- "is there a real witness" question `FluxCRow5Bridge.lean`, `FluxDRow4Bridge.lean` and P74's own
-- N=2 witness already answer differently case by case, not attempted here.

end Erdos634.Row3Step1

#print axioms Erdos634.Row3Step1.corner_step1_dissection
#print axioms Erdos634.Row3Step1.congruentDissection_corner_step1
#print axioms Erdos634.Row3Step1.congruentDissection_row3_lemmaA
