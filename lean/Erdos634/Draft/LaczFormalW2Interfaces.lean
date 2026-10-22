import Erdos634.Draft.LaczFormalW2Main
import Erdos634.Draft.LaczFormalW2Pos

/-!
# Rule W2: the remaining interface lemmas, stated exactly (not proved)

NOTE (2026-10-21, room LEAN_W2): SUPERSEDED.  `W2WedgeG1` is proved as `w2_wedge_G1` (LaczFormalW2G1); the whole rule
is proved as `w2_holds` / `W2Rule_holds` (LaczFormalW2Mirror, LaczFormalW2Final) by the chord version of the proof.

Erdős #634, base-`β` band.  Credit: AI assistant (item 3, band program, `PROOF_W2.md`), Beeson–Roșu, Beeson,
Laczkovich, Paliy.  UNAUDITED.  Statements only (`Prop`-valued definitions); no theorem here claims anything.

Proved so far (all Lean, axiom-clean): I0 `apex_dir`, I1 `w2_step1` (the tile `T' = (P₁,G₁,G₂)`),
I2 `L3_two_b_pos` (the two `b`-edges of a `2b` chord abut at the midpoint), I3 `far_side_of_shared_edge`
(same-side overlap), plus `L3_sum`, `two_circles`, `corner_far_edge`.

Remaining, in the order of `PROOF_W2.md`:
* `W2WedgeG1`  (I4): at `G₁` (a point of the open left leg) the free wedge `β` is filled by one tile `U'`
  with an edge along the leg and an edge along the ray `G₁ → G₂`.  Needs the fan at a side vertex
  (`vertex_fan_side`: cyclic order, `Par (p (e (n+1))) (q (e n))`), the figure `{α,β,γ}` at `G₁`
  (`congruentDissection_boundary_figure_cases_at_vertex`), and the direction `pT ∥ leg`.
* `W2WedgeG2`  (I5): at the interior point `G₂` the tiles `T₁ (γ)`, `T' (β)` leave the wedge `α` between the
  ray `G₂ → G₁` and the continuation of the chord `P₂G₂`; if the continuation lies in a far-side edge
  (case (Z)) the wedge is filled by one `α`-tile `W'` with `b`/`c` along the two rays.  Needs the fan at an
  interior vertex (`vertex_fan_ext`) and `wedge_fill_alpha`.
* `W2Overlap`  (I6): `W'` (edge `b` on `[G₂ − b, G₂]`) and `U'` (edge `a` on `[G₁, G₁ + a]`) both lie above
  the horizontal line `G₁G₂` and their edges overlap as `e² < a`; contradiction by
  `Dissection.sameside_edges_subsingleton` (the pattern of `walk_entry_tile_line`, `far_side_of_shared_edge`).
* `W2Dichotomy` (I7): for the chord `[P₂, G₂]` either no far-side edge passes through `G₂` (case (Y): far cover
  is one `b`-edge `W₁`) or one does (case (Z)); with `L3_sum`, `exists_start_edge`, `nstr_end_*`.
-/

namespace Erdos634.LaczJunction.Walk

open Erdos634.Geometry Erdos634.TilePlacement

variable {N : ℕ}

/-- **I4 (statement).** The tile `U'` at `G₁` with `β`, an edge of length `a`/`c` along the ray `G₁ → G₂`
and the other along the leg. -/
def W2WedgeG1 (D : CongruentDissection N) (β : ℝ) (G1 G2 P R : Plane) (i0 i' : Fin N) (a c : ℝ) : Prop :=
  ∃ iU : Fin N, iU ≠ i0 ∧ iU ≠ i' ∧ (D.tile iU).localAngle G1 = β ∧
    ∃ ka kb kc : Fin 3, ka ≠ kb ∧ ka ≠ kc ∧ kb ≠ kc ∧ (D.tile iU).pts ka = G1 ∧
      (∃ s : ℝ, 0 < s ∧ (D.tile iU).pts kb = G1 + s • (G2 - G1)) ∧
      (∃ s : ℝ, 0 < s ∧ (D.tile iU).pts kc = G1 + s • (R - P)) ∧
      ((dist G1 ((D.tile iU).pts kb) = a ∧ dist G1 ((D.tile iU).pts kc) = c) ∨
       (dist G1 ((D.tile iU).pts kb) = c ∧ dist G1 ((D.tile iU).pts kc) = a))

end Erdos634.LaczJunction.Walk
