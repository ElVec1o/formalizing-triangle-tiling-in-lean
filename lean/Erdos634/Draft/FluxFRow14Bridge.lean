-- Draft/FluxFRow14Bridge.lean — SCOPING TASK (private task, 2026-09-26): does the corner-count
-- machinery behind `TileAt.congruentDissection_base_corner_counts` generalize from the base-β
-- target's corners to row 14's target `(2α, β, α+β)`?
--
-- ANSWER: YES, and it already does, unconditionally — no new geometric machinery is needed.
-- Read in full before this file was written: `TileAt.congruentDissection_base_corner_counts`
-- (`lean/Erdos634/TileAt.lean:284-300`) and its proof, `TilePlacement.corner_multiplicities`/
-- `.base_corner_counts`/`.apex_counts` (`lean/Erdos634/TilePlacement.lean:51-122`), and
-- `Erdos634.Geometry.Dissection.vertex_multiplicities` (`lean/Erdos634/Dissection.lean:335-347`,
-- the same declaration `TilePlacement.base_corner_single_tile`/`.apex_counts` call).
--
-- THE KEY FACT, established by that reading, precisely: row 14's target is tiled by the *same*
-- tile as the base-β target — literally the `3α + 2β = π` tile with third angle `γ = 2α + β` and
-- `α ∉ ℚπ` (`Draft/FluxFRow14.lean:3`, its own header: "by the `3α + 2β = π` tile"). Only the
-- TARGET's corner angles differ (`2α, β, α+β` instead of base-β's `3α, β`). The machinery is
-- already factored exactly along this line:
--
--   * `TilePlacement.corner_multiplicities` — fully general, any three distinct nonzero
--     non-`π` angles `α, β, γ`, ANY target corner value (it is not even given the tile's `3α+2β=π`
--     relation; it only turns the angle-sum-at-a-vertex fact into a linear count identity).
--   * `Erdos634.Geometry.Dissection.vertex_multiplicities` — fully general in the TARGET side:
--     it is parameterized by arbitrary integers `s, t` and solves `x + 2z = s ∧ y + z = t` for the
--     tile's own multiplicities `x` (`α`-count), `y` (`β`-count), `z` (`γ`-count). It is NOT
--     parameterized in the tile: it hard-codes `γ = 2α + β` and `3α + 2β = π` (these are exactly
--     row 14's tile's own defining relations too, not something specific to the base-β TARGET).
--   * `TilePlacement.base_corner_single_tile`/`.apex_counts` are simply two INSTANCES of
--     `vertex_multiplicities` at `(s,t) = (0,1)` (target corner `β`) and `(s,t) = (3,0)` (target
--     corner `3α`), each closed off by `omega` after the nonnegativity of `p,q,r,s : ℕ` forces the
--     unique solution.
--
-- So row 14's three target-corner values need exactly three more such instances, at
-- `(s,t) = (2,0)` (corner `2α`), `(0,1)` (corner `β` — this ALREADY EXISTS, verbatim, as
-- `base_corner_single_tile`/`base_corner_counts`: no new declaration needed for this one corner),
-- and `(1,1)` (corner `α+β`). This file supplies the two missing instances (`2α` and `α+β`) at
-- every layer `TileAt.lean` supplies them at for base-β: the pure-arithmetic multiplicity solve,
-- the `Finset.card`-level corner count, and the `CongruentDissection`-level wrapper that derives
-- the `hvals` hypothesis for real geometry via the ALREADY-GENERAL
-- `TileAt.congruentDissection_localAngle_mem` (`TileAt.lean:231-273`) — that lemma is reused
-- verbatim below, not reproved: it never mentions a target corner value at all, only the tile's own
-- three angles, so it is exactly as valid for row 14's target as for base-β's.
--
-- WHAT THIS DOES NOT DO. It does not touch row 14's OWN open content (`Draft/FluxFRow14.lean`'s
-- own header is explicit: `hword`/`hF4` — F2's word equation and F4's "every side has a `c`-edge"
-- — are hypotheses there, not derived from a `CongruentDissection`). This file supplies corner
-- counts, i.e. "which tiles sit at the target's corners and how many", which is upstream
-- infrastructure that `F2`/`F4` would need to become real derivations rather than hypotheses, but
-- does not by itself derive `hword` or `hF4`. It is a bridge-layer contribution, not a closure of
-- row 14.
--
-- GENERALIZATION TO ROWS 3, 4, 5, 11, 13, 15 (the other rows sharing the corner/word-bridge gap
-- named in EVIDENCE.md P59/P60 and the task prompt): each row's target has its OWN corner-angle
-- values in terms of the tile's own angle vocabulary. For any row whose tile is this SAME
-- `3α + 2β = π, γ = 2α + β` tile (row 14 and row 15's targets both are — `FluxFRow15.lean`'s
-- header: target `(2α, α, 2β)`, same tile family), the corner-count layer generalizes exactly the
-- way this file demonstrates: each target corner value `v` expressible as `s·α + t·β` for integers
-- `s, t` gets its own three-line `vertex_multiplicities`-instance (arithmetic) plus a
-- `corner_multiplicities`-composition (card count) plus a `congruentDissection_localAngle_mem`
-- composition (real-geometry wrapper) — each instance is small (~15 lines total, see below) and
-- mechanical once `(s,t)` is read off the target's own corner-angle expression. For a row whose
-- tile is a DIFFERENT triangle (different defining relation between its three angles, not
-- `3α + 2β = π`), the reusable piece is only `TilePlacement.corner_multiplicities` (angle-generic);
-- `vertex_multiplicities` itself would need to be reproved for that tile's own relation — still
-- mechanical (same `angle_indep`-based method, `Dissection.lean:307-347`), but a NEW declaration,
-- not a reuse. This file did not check which of rows 3/4/5/11/13's tiles are the `3α+2β=π` tile;
-- that is a prerequisite for saying whether THIS file's specific reuse extends to them, still open.
--
-- Does not edit any existing file. Not imported into `All.lean`. Not progress on the three `/goal`
-- outcomes (formalization debt only, per the task's own framing).
import Erdos634.TileAt

namespace Erdos634.Row14Bridge

open Erdos634.Geometry Erdos634.Geometry.Dissection

variable {N : ℕ}

/-! ## Pure arithmetic: the two missing `vertex_multiplicities` instances

Mirrors `TilePlacement.base_corner_single_tile` (target `β`, i.e. `(s,t) = (0,1)`) and
`TilePlacement.apex_counts` (target `3α`, i.e. `(s,t) = (3,0)`) exactly. Row 14's other two target
corners are `2α` (`(s,t) = (2,0)`) and `α + β` (`(s,t) = (1,1)`); `β` itself is already covered by
`base_corner_single_tile`, reused directly below with no new arithmetic lemma. -/

/-- **A `2α`-corner fills uniquely as two `α`-tiles.**  Same method as `TilePlacement.apex_counts`
(target `3α`), instantiated at `(s,t) = (2,0)` instead of `(3,0)`. -/
theorem row14_corner_2alpha_tile {α β γ : ℝ} (hγ : γ = 2 * α + β)
    (hrel : 3 * α + 2 * β = Real.pi) (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (p q r s : ℕ)
    (hsum : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ + (s : ℝ) * Real.pi = 2 * α) :
    p = 2 ∧ q = 0 ∧ r = 0 ∧ s = 0 := by
  rw [hγ, ← hrel] at hsum
  have h' : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * (2 * α + β)
      = ((2 - 3 * (s : ℤ) : ℤ) : ℝ) * α + ((-2 * (s : ℤ) : ℤ) : ℝ) * β := by
    push_cast
    linarith [hsum]
  obtain ⟨h1, h2⟩ := Erdos634.Geometry.vertex_multiplicities hrel hirr p q r _ _ h'
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- **An `(α+β)`-corner fills uniquely as one `α`-tile and one `β`-tile.**  Same method,
instantiated at `(s,t) = (1,1)`. -/
theorem row14_corner_alphabeta_tile {α β γ : ℝ} (hγ : γ = 2 * α + β)
    (hrel : 3 * α + 2 * β = Real.pi) (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (p q r s : ℕ)
    (hsum : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ + (s : ℝ) * Real.pi = α + β) :
    p = 1 ∧ q = 1 ∧ r = 0 ∧ s = 0 := by
  rw [hγ, ← hrel] at hsum
  have h' : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * (2 * α + β)
      = ((1 - 3 * (s : ℤ) : ℤ) : ℝ) * α + ((1 - 2 * (s : ℤ) : ℤ) : ℝ) * β := by
    push_cast
    linarith [hsum]
  obtain ⟨h1, h2⟩ := Erdos634.Geometry.vertex_multiplicities hrel hirr p q r _ _ h'
  refine ⟨by omega, by omega, by omega, by omega⟩

/-! ## `Finset.card`-level corner counts

Mirrors `TilePlacement.base_corner_counts`/`.apex_counts` exactly: compose the angle-generic
`corner_multiplicities` with the arithmetic instance above. -/

/-- **Exactly two `α`-tiles at a `2α` corner, no `β`, `γ`, or straight-angle tile.** -/
theorem row14_corner_2alpha_counts {N : ℕ} (D : Dissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (k : Fin 3)
    (hvals : ∀ i, (D.tile i).localAngle (D.target.pts k)
      ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ))
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
      = 2 * α) :
    ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card = 2 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card = 0 := by
  have h := Erdos634.TilePlacement.corner_multiplicities D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
    hγπ hγ0 hπ0 k hvals
  rw [hcorner] at h
  exact row14_corner_2alpha_tile hγdef hrel hirr _ _ _ _ h

/-- **Exactly one `α`-tile and one `β`-tile at an `α+β` corner, no `γ` or straight-angle tile.** -/
theorem row14_corner_alphabeta_counts {N : ℕ} (D : Dissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (k : Fin 3)
    (hvals : ∀ i, (D.tile i).localAngle (D.target.pts k)
      ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ))
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
      = α + β) :
    ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card = 0 := by
  have h := Erdos634.TilePlacement.corner_multiplicities D α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0
    hγπ hγ0 hπ0 k hvals
  rw [hcorner] at h
  exact row14_corner_alphabeta_tile hγdef hrel hirr _ _ _ _ h

/-! ## `CongruentDissection`-level: `hvals` derived, not hypothesised

Mirrors `TileAt.congruentDissection_base_corner_counts`/`.congruentDissection_apex_counts`
exactly, reusing `TileAt.congruentDissection_localAngle_mem` VERBATIM (imported, not reproved) —
that lemma never mentions a target corner value, only the tile's own three angles, so it is exactly
as valid here as it is for the base-β target. -/

/-- **A `2α` corner of a real congruent dissection (row 14's target, first corner) fills uniquely
as two `α`-tiles.** -/
theorem congruentDissection_row14_2alpha_counts (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
      = 2 * α) :
    ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card = 2 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card = 0 :=
  row14_corner_2alpha_counts D.toDissection α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
    hγdef hrel hirr k
    (fun i => congruentDissection_localAngle_mem D α β γ hα' hβ' hγ' k i) hcorner

/-- **An `α+β` corner of a real congruent dissection (row 14's target, third corner) fills
uniquely as one `α`-tile and one `β`-tile.** -/
theorem congruentDissection_row14_alphabeta_counts (D : CongruentDissection N) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hαπ : α ≠ Real.pi) (hα0 : α ≠ 0)
    (hβγ : β ≠ γ) (hβπ : β ≠ Real.pi) (hβ0 : β ≠ 0)
    (hγπ : γ ≠ Real.pi) (hγ0 : γ ≠ 0) (hπ0 : Real.pi ≠ 0)
    (hγdef : γ = 2 * α + β) (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (k : Fin 3)
    (hcorner : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
      = α + β) :
    ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card = 1 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card = 0 ∧
    ({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card = 0 :=
  row14_corner_alphabeta_counts D.toDissection α β γ hαβ hαγ hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0
    hγdef hrel hirr k
    (fun i => congruentDissection_localAngle_mem D α β γ hα' hβ' hγ' k i) hcorner

-- The third corner, `β`, needs NO new declaration: `TileAt.congruentDissection_base_corner_counts`
-- already covers it verbatim (it derives from the SAME `hcorner : ... = β` shape; row 14's target
-- and the base-β target share this one corner value even though the rest of their corner sets
-- differ). Calling it out here rather than wrapping it again avoids a spurious duplicate
-- declaration.

end Erdos634.Row14Bridge

#print axioms Erdos634.Row14Bridge.row14_corner_2alpha_tile
#print axioms Erdos634.Row14Bridge.row14_corner_alphabeta_tile
#print axioms Erdos634.Row14Bridge.row14_corner_2alpha_counts
#print axioms Erdos634.Row14Bridge.row14_corner_alphabeta_counts
#print axioms Erdos634.Row14Bridge.congruentDissection_row14_2alpha_counts
#print axioms Erdos634.Row14Bridge.congruentDissection_row14_alphabeta_counts
