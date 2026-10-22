/-
Draft/SideRunGCornerA.lean -- written 14 October 2026.  UNAUDITED.  In `AllThreshold`.  Module C1 of the plan for
`thm:cornerrun` (see the header of `Draft/SideRunGJChord.lean`).

**The side `s` from a corner `A'` of angle `2α` or `3α` (left end) to a corner `Q'` of angle `β` or `α + β` (right end), in normal
position**: `A' = (0, 0)`, `Q' = (L, 0)`, the third vertex `(ax, ay)`.  Paper: Theorem `thm:cornerrun`, "Let `s` be a side of a triangle
`Δ` that is cut ... from a corner `A'` of angle `2α` or `3α` to a corner `Q'` of angle `β` or `α + β`", the figures (F), and the
first sentence of the proof ("All tiles at `A'` show `α` (F), so the first tile of `s` is `B1` or `C1`").

CONTENTS.
* `CornersA e f L ax ay`: the two corners, in the style of `CornersG`.  Left: the apex lies on the ray from `A'` of direction `d(2α)`
  (`(K2² − 2f⁴, e K2 √(4f² − e²))`, `K2 = 2f² − e²`) or `d(3α)` (`(K2 (K2² − 3f⁴), e √(4f²−e²) (K2² − f⁴))`).  Right: it lies on the
  ray from `Q'` of the direction of the `a`-edge of a `C1` tile (angle `β`, as in `CornersG.hB`) or of direction `(−e, √(4f² − e²))`
  (angle `α + β`).  `CornersG` has the right corner `β` only, and its left corner `β` or `α + β`; the new left corners `2α`, `3α` and
  the new right corner `α + β` are here.
* Angles: `cos_alpha` (`cos α = (2f² − e²)/(2f²)`), `cos_two_alpha`, `cos_three_alpha`; `corner_left_two`, `corner_left_three`
  (the target has the angle `2α`, resp. `3α`, at `(0,0)`), `corner_right_ab` (the angle `α + β` at `(L, 0)`).
* Figures (F), as counting statements: `ab_zero` (`p α + q β = 0` with integers forces `p = q = 0`: irrationality of `α/π`),
  `corner_counts` (the local angles of the tiles at a vertex of the target are `a α + b β` with natural numbers `a, b` summing to the
  data of the corner), `figure_alpha` (**at a corner `n α` every tile shows `α` or does not contain the corner**: exactly what is proved
  for "all tiles at `A'` show `α`"), `figure_ab` (**at a corner `α + β` no tile shows `γ` and no two distinct tiles show `β`**).
* `first_tile_alpha`: the first tile of the chain at `A'` is `B1` or `C1`.
* The chords from `A'`: `hch_cornerA_two`, `hch_cornerA_three`, `hch_cornerA` (the open chords `(A', p(0, j))` are interior to Δ).
* The right corner `α + β`: `bad_corner_right` (the tile across the last `a`-edge of a run that ends at `Q'` does not show `γ` or `β`
  there: `False`), `hint_right_ab` (the open `a`-edge from `Q'` is interior to Δ).

* The tile `T` beside the first tile `X₀ = U(0,0)` (a `C1` tile at `A'`, `ε = 1`, `x = 0`): `corner_nextT` (a tile of the side σ of `ℓ`
  has a vertex at `A'` and another one at `p(0, t)`, `t > 0`, and `t · b ∈ {a, b, c}`; the clamp at `A'` is the boundary of the target)
  and `corner_K1J_or_b`: **(K1) at `A'` from "`T` lays `c`" (or `a`)**, in the form `K1J D e f 1 0 0` of `Draft/SideRunGJChord.lean`;
  otherwise `T` has the `b`-edge `[A', p(0,1)]` of `X₀` (**the mirror case**; its geometric content is `MirrorAt` of
  `Draft/SideRunGCornerRun.lean`, where the `α`-figure at `A'` is used).

WHAT IS PROVED, EXACTLY, FOR "ALL TILES AT `A'` SHOW `α`".  `figure_alpha`: for a vertex `v` of the target with `localAngle v = n α`
(`n` natural), every tile `m` has `localAngle (tile m) v = α` or `= 0`; since a tile that contains `v` has a vertex there with
`localAngle ≠ 0`, every tile that contains `A'` shows `α`.  In particular no tile shows `β`, `γ` or `π` at `A'`.

CHECKS.  (i) The corner statements of `CornersA` have no counterpart for a side with corners `β, β` or `α + β, β` (`CornersG`):
the right corner `β` is the same predicate as `CornersG.hB`, and `K3G_out_right` applies to it; the right corner `α + β` is new.
(ii) At `e = 1` the corner predicates read `ax = t ((2f² − 1)² − 2f⁴)`, `ay = t (2f² − 1) √(4f² − 1)` (`rtG_one`), etc.; there is no Lean
counterpart for `e = 1` (the paper: `thm:cornerrun` has none).  For the members `(f−1, f)`, which include `(1, 2)`, alternative (ii)
of the theorem needs `e + 1 ≤ k ≤ f − 1` with `e + 1 = f`: empty.  That deduction belongs to R2.

WITNESSES.  `CornersA` and the figure lemmas concern a triangle with a side from a corner `2α` to a corner `α + β` (`W_M(e, f)`, the
side `AQ`) or from `3α` to `β` (a leg of `T_M(e, f)`), etc.  The seed tilings of `W_f(e, f)` and `T_f(e, f)` (`setupG_witness_member`)
satisfy `SetupG` with the side `QB`, not with the side `AQ` on the `x`-axis: the normal form for the side `AQ` is not in this module
(it needs a `Tg` with the apex on the ray `d(2α)` and its own isometry, the analogue of `setup_WG`); it belongs to R2 (`W1`), and until
then `CornersA` has NO real witness in Lean.  The figure lemmas (`figure_alpha`, `figure_ab`) are about any `SetupG` and any vertex of the
target; at a corner `α + β`, they hold for the seed tilings (the left corner `Q` of the side `QB`, index `0`), but are not stated there.

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGSourcesB
import Erdos634.Draft.SideRunGJK

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.SideRunGA

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG Erdos634.Draft.SideRunGJ Set

variable {N : ℕ} {D : CongruentDissection N}

/-! ## 1. The corners -/

/-- **The corners of the side `s` from `A'` to `Q'`**: at `A' = (0,0)` the angle `2α` (first form) or `3α` (second form); at
`Q' = (L, 0)` the angle `β` (first form: the side `Q'A` runs along the `a`-edge of a `C1` tile) or `α + β` (second form: the side
`Q'A` has the direction `(−e, √(4f² − e²))`). -/
structure CornersA (e f : ℕ) (L ax ay : ℝ) : Prop where
  hA : (∃ t : ℝ, 0 < t ∧ ax = t * ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - 2 * (f : ℝ) ^ 4) ∧
        ay = t * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * rtG (e : ℝ) (f : ℝ))) ∨
      (∃ t : ℝ, 0 < t ∧
        ax = t * ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - 3 * (f : ℝ) ^ 4)) ∧
        ay = t * ((e : ℝ) * rtG (e : ℝ) (f : ℝ) * ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - (f : ℝ) ^ 4)))
  hQ : (∃ t : ℝ, 0 < t ∧ ax = L - t * uuG (e : ℝ) (f : ℝ) ∧ ay = t * hhG (e : ℝ) (f : ℝ)) ∨
      (∃ t : ℝ, 0 < t ∧ ax = L - t * (e : ℝ) ∧ ay = t * rtG (e : ℝ) (f : ℝ))

/-! ## 2. Arithmetic: irrationality of `α/π` for counts -/

/-- `p α + q β = 0` with integers `p, q` forces `p = q = 0` (`α/π` is irrational, `3α + 2β = π`) -/
theorem ab_zero {α β γ : ℝ} (hA : AngleData α β γ) {p q : ℤ}
    (h : (p : ℝ) * α + (q : ℝ) * β = 0) : p = 0 ∧ q = 0 := by
  have hrel := hA.hrel
  have h2 : (2 * (p : ℝ) - 3 * q) * α = -(q : ℝ) * Real.pi := by
    linear_combination 2 * h - (q : ℝ) * hrel
  by_cases hd : (2 * (p : ℝ) - 3 * q) = 0
  · rw [hd, zero_mul] at h2
    have hq : (q : ℝ) = 0 := by
      have h3 : (q : ℝ) * Real.pi = 0 := by linarith
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact h4
      · exact absurd h4 Real.pi_pos.ne'
    have hp : (p : ℝ) = 0 := by linarith
    exact ⟨by exact_mod_cast hp, by exact_mod_cast hq⟩
  · exfalso
    apply hA.hirr
    refine ⟨-(q : ℚ) / (2 * (p : ℚ) - 3 * (q : ℚ)), ?_⟩
    push_cast
    rw [div_mul_eq_mul_div, eq_div_iff hd]
    linarith

/-! ## 3. The cosines of `α`, `2α`, `3α` and the corner angles -/

section angles

variable {e f : ℕ} {α β γ L ax ay : ℝ}

theorem cos_alpha (S : SetupG D e f α β γ L ax ay) :
    Real.cos α = (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (2 * (f : ℝ) ^ 2) := by
  have hcg := S.cos_gamma
  have hαγ : α = 2 * γ - Real.pi := by linarith [S.hA.hγdef, S.hA.hrel]
  have hf0 : (f : ℝ) ≠ 0 := S.f0.ne'
  rw [hαγ, Real.cos_sub_pi, Real.cos_two_mul, hcg]
  field_simp
  ring

theorem cos_two_alpha (S : SetupG D e f α β γ L ax ay) :
    Real.cos (2 * α) = ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - 2 * (f : ℝ) ^ 4) / (2 * (f : ℝ) ^ 4) := by
  have hf0 : (f : ℝ) ≠ 0 := S.f0.ne'
  rw [Real.cos_two_mul, cos_alpha S]
  field_simp

theorem cos_three_alpha (S : SetupG D e f α β γ L ax ay) :
    Real.cos (3 * α) = ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) *
      ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - 3 * (f : ℝ) ^ 4)) / (2 * (f : ℝ) ^ 6) := by
  have hf0 : (f : ℝ) ≠ 0 := S.f0.ne'
  rw [Real.cos_three_mul, cos_alpha S]
  field_simp
  ring

/-- the corner at `A' = (0,0)` of angle `2α` -/
theorem corner_left_two (S : SetupG D e f α β γ L ax ay) {t : ℝ} (ht : 0 < t)
    (hax : ax = t * ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - 2 * (f : ℝ) ^ 4))
    (hay' : ay = t * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * rtG (e : ℝ) (f : ℝ))) :
    D.target.localAngle (mkPt 0 0) = 2 * α := by
  have he := S.e0
  have hef := S.hef'
  have hf0 := S.f0
  have hL := S.hL
  have hr := rtG_sq he hef
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hγdef := S.hA.hγdef
  have hrel := S.hA.hrel
  have hπ := Real.pi_pos
  have h0 : D.target.localAngle (mkPt 0 0)
      = cornerAngle (mkPt L 0) (mkPt 0 0) (mkPt ax ay) := by
    rw [S.tgt]
    have h := (Tg L ax ay S.hL S.hay).localAngle_vertex 0
    rw [show ((0 : Fin 3) + 1) = 1 by decide, show ((0 : Fin 3) + 2) = 2 by decide] at h
    exact h
  rw [h0]
  have h1 : dist (mkPt ax ay) (mkPt 0 0) = t * (2 * (f : ℝ) ^ 4) := by
    refine dist_eq_of_sq_eq ?_ dist_nonneg (by positivity)
    rw [dist_sq_mkPt, hax, hay']
    linear_combination (t ^ 2 * (e : ℝ) ^ 2 * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2) * hr
  have h2 : dist (mkPt L 0) (mkPt 0 0) = L := by
    have := dist_mkPt_base 0 L hL.le
    rw [zero_add] at this
    rw [dist_comm]; exact this
  have hcos := Erdos634.AngleThreshold.cos_of_sides (mkPt L 0) (mkPt 0 0) (mkPt ax ay)
    (by rw [h2]; exact hL.ne') (by rw [h1]; positivity)
  rw [h1, h2, dist_sq_mkPt] at hcos
  refine cornerAngle_eq_of_cos (by linarith) (by linarith) ?_
  rw [hcos, cos_two_alpha S]
  have hB : 2 * L * (t * (2 * (f : ℝ) ^ 4)) ≠ 0 := by positivity
  have hD : 2 * (f : ℝ) ^ 4 ≠ 0 := by positivity
  rw [div_eq_div_iff hB hD, hax, hay']
  linear_combination (-(2 * (f : ℝ) ^ 4 * t ^ 2 * (e : ℝ) ^ 2 * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2)) * hr

/-- the corner at `A' = (0,0)` of angle `3α` -/
theorem corner_left_three (S : SetupG D e f α β γ L ax ay) {t : ℝ} (ht : 0 < t)
    (hax : ax = t * ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) *
      ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - 3 * (f : ℝ) ^ 4)))
    (hay' : ay = t * ((e : ℝ) * rtG (e : ℝ) (f : ℝ) *
      ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - (f : ℝ) ^ 4))) :
    D.target.localAngle (mkPt 0 0) = 3 * α := by
  have he := S.e0
  have hef := S.hef'
  have hf0 := S.f0
  have hL := S.hL
  have hr := rtG_sq he hef
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hγdef := S.hA.hγdef
  have hrel := S.hA.hrel
  have hπ := Real.pi_pos
  have h0 : D.target.localAngle (mkPt 0 0)
      = cornerAngle (mkPt L 0) (mkPt 0 0) (mkPt ax ay) := by
    rw [S.tgt]
    have h := (Tg L ax ay S.hL S.hay).localAngle_vertex 0
    rw [show ((0 : Fin 3) + 1) = 1 by decide, show ((0 : Fin 3) + 2) = 2 by decide] at h
    exact h
  rw [h0]
  have h1 : dist (mkPt ax ay) (mkPt 0 0) = t * (2 * (f : ℝ) ^ 6) := by
    refine dist_eq_of_sq_eq ?_ dist_nonneg (by positivity)
    rw [dist_sq_mkPt, hax, hay']
    linear_combination (t ^ 2 * (e : ℝ) ^ 2 * ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - (f : ℝ) ^ 4) ^ 2) * hr
  have h2 : dist (mkPt L 0) (mkPt 0 0) = L := by
    have := dist_mkPt_base 0 L hL.le
    rw [zero_add] at this
    rw [dist_comm]; exact this
  have hcos := Erdos634.AngleThreshold.cos_of_sides (mkPt L 0) (mkPt 0 0) (mkPt ax ay)
    (by rw [h2]; exact hL.ne') (by rw [h1]; positivity)
  rw [h1, h2, dist_sq_mkPt] at hcos
  refine cornerAngle_eq_of_cos (by linarith) (by linarith) ?_
  rw [hcos, cos_three_alpha S]
  have hB : 2 * L * (t * (2 * (f : ℝ) ^ 6)) ≠ 0 := by positivity
  have hD : 2 * (f : ℝ) ^ 6 ≠ 0 := by positivity
  rw [div_eq_div_iff hB hD, hax, hay']
  linear_combination (-(2 * (f : ℝ) ^ 6 * t ^ 2 * (e : ℝ) ^ 2 *
    ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - (f : ℝ) ^ 4) ^ 2)) * hr

/-- the corner at `Q' = (L, 0)` of angle `α + β`: the neighbouring side has the direction `(−e, √(4f² − e²))` -/
theorem corner_right_ab (S : SetupG D e f α β γ L ax ay) {t : ℝ} (ht : 0 < t)
    (hax : ax = L - t * (e : ℝ)) (hay' : ay = t * rtG (e : ℝ) (f : ℝ)) :
    D.target.localAngle (mkPt L 0) = α + β := by
  have he := S.e0
  have hef := S.hef'
  have hf0 := S.f0
  have hL := S.hL
  have hπ := Real.pi_pos
  have hr := rtG_sq he hef
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hαβ : α + β = Real.pi - γ := by linarith
  have h0 : D.target.localAngle (mkPt L 0)
      = cornerAngle (mkPt ax ay) (mkPt L 0) (mkPt 0 0) := by
    rw [S.tgt]
    have h := (Tg L ax ay S.hL S.hay).localAngle_vertex 1
    rw [show ((1 : Fin 3) + 1) = 2 by decide, show ((1 : Fin 3) + 2) = 0 by decide] at h
    exact h
  rw [h0]
  have h1 : dist (mkPt ax ay) (mkPt L 0) = t * (2 * (f : ℝ)) := by
    refine dist_eq_of_sq_eq ?_ dist_nonneg (by positivity)
    rw [dist_sq_mkPt, hax, hay']
    linear_combination t ^ 2 * hr
  have h2 : dist (mkPt 0 0) (mkPt L 0) = L := by
    have := dist_mkPt_base 0 L hL.le
    rwa [zero_add] at this
  have hcos := Erdos634.AngleThreshold.cos_of_sides (mkPt ax ay) (mkPt L 0) (mkPt 0 0)
    (by rw [h1]; positivity) (by rw [h2]; exact hL.ne')
  rw [h1, h2, dist_sq_mkPt] at hcos
  refine cornerAngle_eq_of_cos (by linarith) (by linarith) ?_
  rw [hcos, hαβ, Real.cos_pi_sub, S.cos_gamma]
  have hB : 2 * (t * (2 * (f : ℝ))) * L ≠ 0 := by positivity
  have hD : 2 * (f : ℝ) ≠ 0 := by positivity
  have e' : -(-(e : ℝ) / (2 * (f : ℝ))) = (e : ℝ) / (2 * (f : ℝ)) := by ring
  rw [e', div_eq_div_iff hB hD, hax, hay']
  linear_combination (-(2 * (f : ℝ) * t ^ 2)) * hr

end angles

/-! ## 4. The figures (F) at a corner, as counting statements -/

section figures

variable {e f : ℕ} {α β γ L ax ay : ℝ}

/-- **The local angles of the tiles at a vertex of the target are `a α + b β` with natural `a, b`**, whose sums over the tiles are
the data `A, B` of the corner (`localAngle = A α + B β`); with the classification of the values `α, β, γ, π, 0`. -/
theorem corner_counts (S : SetupG D e f α β γ L ax ay) (k : Fin 3) {A B : ℕ}
    (hk : D.target.localAngle (D.target.pts k) = (A : ℝ) * α + (B : ℝ) * β) :
    ∃ a b : Fin N → ℕ,
      (∀ m, (D.tile m).localAngle (D.target.pts k) = (a m : ℝ) * α + (b m : ℝ) * β) ∧
      (∀ m, b m = 0 → (D.tile m).localAngle (D.target.pts k) = α ∨
        (D.tile m).localAngle (D.target.pts k) = 0) ∧
      (∀ m, (D.tile m).localAngle (D.target.pts k) = β → 1 ≤ b m) ∧
      (∀ m, ((D.tile m).localAngle (D.target.pts k) = γ ∨
        (D.tile m).localAngle (D.target.pts k) = Real.pi) → 2 ≤ a m) ∧
      ∑ m, a m = A ∧ ∑ m, b m = B := by
  classical
  obtain ⟨hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hγπ, hγ0, hπ0⟩ :=
    distinct_of_pos_ne S.hA.hα S.hA.hβ S.hA.hαβ S.hA.hγdef S.hA.hrel
  have hγdef := S.hA.hγdef
  have hrel := S.hA.hrel
  have hper : ∀ m, ∃ a b : ℕ,
      (D.tile m).localAngle (D.target.pts k) = (a : ℝ) * α + (b : ℝ) * β ∧
      (b = 0 → (D.tile m).localAngle (D.target.pts k) = α ∨
        (D.tile m).localAngle (D.target.pts k) = 0) ∧
      ((D.tile m).localAngle (D.target.pts k) = β → 1 ≤ b) ∧
      (((D.tile m).localAngle (D.target.pts k) = γ ∨
        (D.tile m).localAngle (D.target.pts k) = Real.pi) → 2 ≤ a) := by
    intro m
    have hmem := congruentDissection_localAngle_mem D α β γ S.hM.hα' S.hM.hβ' S.hM.hγ' k m
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h | h
    · refine ⟨1, 0, ?_, fun _ => Or.inl h, fun hb => absurd (h.symm.trans hb) hαβ, fun hg => ?_⟩
      · rw [h]; push_cast <;> ring
      · rcases hg with hg | hg
        · exact absurd (h.symm.trans hg) hαγ
        · exact absurd (h.symm.trans hg) hαπ
    · refine ⟨0, 1, ?_, fun hb => absurd hb one_ne_zero, fun _ => le_rfl, fun hg => ?_⟩
      · rw [h]; push_cast <;> ring
      · rcases hg with hg | hg
        · exact absurd (h.symm.trans hg) hβγ
        · exact absurd (h.symm.trans hg) hβπ
    · refine ⟨2, 1, ?_, fun hb => absurd hb one_ne_zero, fun _ => le_rfl, fun _ => le_rfl⟩
      rw [h, hγdef]; push_cast <;> ring
    · refine ⟨3, 2, ?_, fun hb => absurd hb (by norm_num), fun _ => by norm_num,
        fun _ => by norm_num⟩
      rw [h]; push_cast; linarith
    · refine ⟨0, 0, ?_, fun _ => Or.inr h, fun hb => absurd (h.symm.trans hb) hβ0.symm, fun hg => ?_⟩
      · rw [h]; push_cast <;> ring
      · rcases hg with hg | hg
        · exact absurd (h.symm.trans hg) hγ0.symm
        · exact absurd (h.symm.trans hg) hπ0.symm
  choose a b hab using hper
  refine ⟨a, b, fun m => (hab m).1, fun m => (hab m).2.1, fun m => (hab m).2.2.1,
    fun m => (hab m).2.2.2, ?_⟩
  have hs := D.toDissection.sum_localAngle_eq (D.target.pts k)
  rw [hk] at hs
  have hsum : ∑ m, (D.tile m).localAngle (D.target.pts k)
      = ((∑ m, a m : ℕ) : ℝ) * α + ((∑ m, b m : ℕ) : ℝ) * β := by
    rw [Nat.cast_sum, Nat.cast_sum, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun m _ => (hab m).1)
  have key : ((∑ m, a m : ℕ) : ℝ) * α + ((∑ m, b m : ℕ) : ℝ) * β
      = (A : ℝ) * α + (B : ℝ) * β := hsum.symm.trans hs
  generalize hSA : ∑ m, a m = SA at key
  generalize hSB : ∑ m, b m = SB at key
  obtain ⟨hp, hq⟩ := ab_zero S.hA (p := (SA : ℤ) - A) (q := (SB : ℤ) - B)
    (by push_cast; linear_combination key)
  exact ⟨by omega, by omega⟩

/-- **(F) at a corner `n α`: every tile shows `α` or does not contain the corner.**  (Used for the corners `2α` and `3α` of `A'`.) -/
theorem figure_alpha (S : SetupG D e f α β γ L ax ay) (k : Fin 3) (n : ℕ)
    (hk : D.target.localAngle (D.target.pts k) = (n : ℝ) * α) :
    ∀ m, (D.tile m).localAngle (D.target.pts k) = α ∨ (D.tile m).localAngle (D.target.pts k) = 0 := by
  obtain ⟨a, b, -, h0, -, -, -, hb⟩ := corner_counts S k (A := n) (B := 0)
    (by rw [hk]; simp)
  intro m
  exact h0 m (Finset.sum_eq_zero_iff.mp hb m (Finset.mem_univ m))

/-- **(F) at a corner `α + β`: no tile shows `γ`, and no two distinct tiles show `β`.** -/
theorem figure_ab (S : SetupG D e f α β γ L ax ay) (k : Fin 3)
    (hk : D.target.localAngle (D.target.pts k) = α + β) :
    (∀ m, (D.tile m).localAngle (D.target.pts k) ≠ γ) ∧
    (∀ i j, i ≠ j → (D.tile i).localAngle (D.target.pts k) = β →
      (D.tile j).localAngle (D.target.pts k) = β → False) := by
  obtain ⟨a, b, -, -, h3, h4, ha, hb⟩ := corner_counts S k (A := 1) (B := 1)
    (by rw [hk]; simp)
  constructor
  · intro m hm
    have h2 := h4 m (Or.inl hm)
    have h5 : a m ≤ ∑ m', a m' := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
    omega
  · intro i j hij hi hj
    have h1 := h3 i hi
    have h2 := h3 j hj
    have h5 : ∑ x ∈ ({i, j} : Finset (Fin N)), b x = b i + b j := Finset.sum_pair hij
    have h6 : ∑ x ∈ ({i, j} : Finset (Fin N)), b x ≤ ∑ x, b x :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    omega

theorem aL_pos {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (t : Ty) : 0 < t.aL α β γ := by
  cases t <;> simp only [Ty.aL] <;> assumption

theorem aL_alpha_cases {α β γ : ℝ} (h1 : α ≠ β) (h2 : α ≠ γ) (t : Ty) (ht : t.aL α β γ = α) :
    t = Ty.B1 ∨ t = Ty.C1 := by
  cases t
  · exact absurd (show α = β from ht.symm) h1
  · exact absurd (show α = γ from ht.symm) h2
  · exact Or.inl rfl
  · exact absurd (show α = γ from ht.symm) h2
  · exact Or.inr rfl
  · exact absurd (show α = β from ht.symm) h1

/-- **The first tile of the chain at `A'` is `B1` or `C1`** (it shows `α` at `A'`, by (F)): the corner of the target at `(0,0)` has
the angle `n α` -/
theorem first_tile_alpha (S : SetupG D e f α β γ L ax ay) {m : ℕ} {X : ℕ → ℝ} {tile : ℕ → Fin N}
    {τ : ℕ → Ty} (Ch : ChainG D e f L m X tile τ) (n : ℕ)
    (hA : D.target.localAngle (mkPt 0 0) = (n : ℝ) * α) : τ 0 = Ty.B1 ∨ τ 0 = Ty.C1 := by
  obtain ⟨hαβ, hαγ, -, -, -, -, -, -, -, -⟩ :=
    distinct_of_pos_ne S.hA.hα S.hA.hβ S.hA.hαβ S.hA.hγdef S.hA.hrel
  obtain ⟨hα, hβ, hγ2, hsum, hγπ⟩ := angle_facts S.hA
  have hγ0 : 0 < γ := by linarith [S.hA.hγdef]
  have h := Ch.htile 0 Ch.hm0
  rw [Ch.hX0] at h
  have ha := (S.angles h).1
  have hf := figure_alpha S 0 n (by rw [S.Q_eq]; exact hA) (tile 0)
  rw [S.Q_eq, ha] at hf
  have hpos := aL_pos hα hβ hγ0 (τ 0)
  rcases hf with hf | hf
  · exact aL_alpha_cases hαβ hαγ (τ 0) hf
  · rw [hf] at hpos; exact absurd hpos (lt_irrefl _)

end figures

/-! ## 5. The chords from `A'` are interior -/

section chords

variable {e f : ℕ} {α β γ L ax ay : ℝ}

/-- the chords from the corner `A'` of angle `2α` are interior to the target -/
theorem hch_cornerA_two (S : SetupG D e f α β γ L ax ay) {t : ℝ} (ht : 0 < t)
    (hax : ax = t * ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - 2 * (f : ℝ) ^ 4))
    (hay' : ay = t * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * rtG (e : ℝ) (f : ℝ)))
    (hP : mkPt 0 0 ∈ D.target.carrier) :
    ∀ j : ℕ, 1 ≤ j → lpG (e : ℝ) (f : ℝ) 1 0 0 j ∈ D.target.carrier →
      openSegment ℝ (lpG (e : ℝ) (f : ℝ) 1 0 0 0) (lpG (e : ℝ) (f : ℝ) 1 0 0 j)
        ⊆ interior D.target.carrier := by
  intro j hj hmem
  rw [lpG_zero]
  have he0 := S.e0
  have hef := S.hef'
  have hf0 := S.f0
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  have hhp := hhG_pos he0 hef
  have hu := uuG_spec he0 hef
  have hh' := hhG_spec he0 hef
  have hrt := rtG_pos he0 hef
  have hb := S.b_pos
  have key : 2 * (f : ℝ) ^ 2 * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * rtG (e : ℝ) (f : ℝ)
        * ((f : ℝ) ^ 2 - uuG (e : ℝ) (f : ℝ))
      - ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - 2 * (f : ℝ) ^ 4) * hhG (e : ℝ) (f : ℝ))
      = 2 * (f : ℝ) ^ 2 * ((f : ℝ) ^ 2 * (e : ℝ) * rtG (e : ℝ) (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := by
    linear_combination (-((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * rtG (e : ℝ) (f : ℝ))) * hu
      + (-((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - 2 * (f : ℝ) ^ 4)) * hh'
  have hX := mul_left_cancel₀ (two_f2_pos he0 hef).ne' key
  refine S.interior_seg hP hmem (Or.inr ?_) (Or.inr ?_) (Or.inl ?_)
  · rw [lpG_snd]; exact mul_pos hjpos hhp
  · unfold lpG
    rw [gA_mk, hax, hay']
    refine lt_of_lt_of_eq (b := t * (j : ℝ) * ((f : ℝ) ^ 2 * (e : ℝ) * rtG (e : ℝ) (f : ℝ)
      * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))) ?_ ?_
    · exact mul_pos (mul_pos ht hjpos) (mul_pos (mul_pos (mul_pos (pow_pos hf0 2) he0) hrt) hb)
    · linear_combination (-(t * (j : ℝ))) * hX
  · rw [gB_mk]; nlinarith [mul_pos S.hay S.hL]

/-- the chords from the corner `A'` of angle `3α` are interior to the target -/
theorem hch_cornerA_three (S : SetupG D e f α β γ L ax ay) {t : ℝ} (ht : 0 < t)
    (hax : ax = t * ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) *
      ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - 3 * (f : ℝ) ^ 4)))
    (hay' : ay = t * ((e : ℝ) * rtG (e : ℝ) (f : ℝ) *
      ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - (f : ℝ) ^ 4)))
    (hP : mkPt 0 0 ∈ D.target.carrier) :
    ∀ j : ℕ, 1 ≤ j → lpG (e : ℝ) (f : ℝ) 1 0 0 j ∈ D.target.carrier →
      openSegment ℝ (lpG (e : ℝ) (f : ℝ) 1 0 0 0) (lpG (e : ℝ) (f : ℝ) 1 0 0 j)
        ⊆ interior D.target.carrier := by
  intro j hj hmem
  rw [lpG_zero]
  have he0 := S.e0
  have hef := S.hef'
  have hf0 := S.f0
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  have hhp := hhG_pos he0 hef
  have hu := uuG_spec he0 hef
  have hh' := hhG_spec he0 hef
  have hrt := rtG_pos he0 hef
  have hb := S.b_pos
  have hK2 : (0 : ℝ) < 2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have := S.b_pos; have := S.c_pos; linarith
  have key : 2 * (f : ℝ) ^ 2 * ((e : ℝ) * rtG (e : ℝ) (f : ℝ) *
        ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - (f : ℝ) ^ 4) * ((f : ℝ) ^ 2 - uuG (e : ℝ) (f : ℝ))
      - (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) *
        ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - 3 * (f : ℝ) ^ 4) * hhG (e : ℝ) (f : ℝ))
      = 2 * (f : ℝ) ^ 2 * ((f : ℝ) ^ 2 * (e : ℝ) * rtG (e : ℝ) (f : ℝ) *
        (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) := by
    linear_combination
      (-((e : ℝ) * rtG (e : ℝ) (f : ℝ) * ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - (f : ℝ) ^ 4))) * hu
      + (-((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) *
        ((2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 - 3 * (f : ℝ) ^ 4))) * hh'
  have hX := mul_left_cancel₀ (two_f2_pos he0 hef).ne' key
  refine S.interior_seg hP hmem (Or.inr ?_) (Or.inr ?_) (Or.inl ?_)
  · rw [lpG_snd]; exact mul_pos hjpos hhp
  · unfold lpG
    rw [gA_mk, hax, hay']
    refine lt_of_lt_of_eq (b := t * (j : ℝ) * ((f : ℝ) ^ 2 * (e : ℝ) * rtG (e : ℝ) (f : ℝ) *
          (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))) ?_ ?_
    · exact mul_pos (mul_pos ht hjpos)
        (mul_pos (mul_pos (mul_pos (mul_pos (pow_pos hf0 2) he0) hrt) hK2) hb)
    · linear_combination (-(t * (j : ℝ))) * hX
  · rw [gB_mk]; nlinarith [mul_pos S.hay S.hL]

/-- **the open chords from `A'` along `ℓ` are interior to the target**, for the corner `2α` or `3α` -/
theorem hch_cornerA (S : SetupG D e f α β γ L ax ay) (Co : CornersA e f L ax ay)
    (hP : mkPt 0 0 ∈ D.target.carrier) :
    ∀ j : ℕ, 1 ≤ j → lpG (e : ℝ) (f : ℝ) 1 0 0 j ∈ D.target.carrier →
      openSegment ℝ (lpG (e : ℝ) (f : ℝ) 1 0 0 0) (lpG (e : ℝ) (f : ℝ) 1 0 0 j)
        ⊆ interior D.target.carrier := by
  rcases Co.hA with ⟨t, ht, hax, hay'⟩ | ⟨t, ht, hax, hay'⟩
  · exact hch_cornerA_two S ht hax hay' hP
  · exact hch_cornerA_three S ht hax hay' hP

/-- **the corner of the target at `A'` has the angle `2α` or `3α`** -/
theorem corner_A_angle (S : SetupG D e f α β γ L ax ay) (Co : CornersA e f L ax ay) :
    ∃ n : ℕ, (n = 2 ∨ n = 3) ∧ D.target.localAngle (mkPt 0 0) = (n : ℝ) * α := by
  rcases Co.hA with ⟨t, ht, hax, hay'⟩ | ⟨t, ht, hax, hay'⟩
  · exact ⟨2, Or.inl rfl, (corner_left_two S ht hax hay').trans (by norm_num)⟩
  · exact ⟨3, Or.inr rfl, (corner_left_three S ht hax hay').trans (by norm_num)⟩

end chords

/-! ## 6. The right corner `α + β` -/

section right

variable {e f : ℕ} {α β γ L ax ay : ℝ}

/-- **The tile across the last `a`-edge of a run that ends at the corner `Q'` of angle `α + β` does not show `γ` or `β` there**: the
tile `t₀` (the last tile of the run, with the vertices `A₀`, `Q'`, `G`) shows `β` at `Q'`, and the tile `W` with the vertices `Q'`, `G`,
`Z` (`Z` above the side) shows `γ` or `β`.  (Conclusion `False`: a contradiction engine for (K3).) -/
theorem bad_corner_right (S : SetupG D e f α β γ L ax ay)
    (hQ : D.target.localAngle (mkPt L 0) = α + β) {G A₀ Z : Plane} (hG1 : 0 < G 1) {t₀ : Fin N}
    (h0 : HasV D t₀ A₀ (mkPt L 0) G) (hA₀ : A₀ 1 = 0)
    (hβ0 : (D.tile t₀).localAngle (mkPt L 0) = β) {W : Fin N} (hW : HasV D W (mkPt L 0) G Z)
    (hθW : (D.tile W).localAngle (mkPt L 0) = γ ∨ (D.tile W).localAngle (mkPt L 0) = β)
    (hZ1 : 0 < Z 1) : False := by
  have hfig := figure_ab S 1 (by rw [S.B_eq]; exact hQ)
  have hne1 : ∀ {P Q : Plane}, P 1 = 0 → 0 < Q 1 → P ≠ Q := by
    intro P Q hP hQ h
    rw [h] at hP
    linarith
  have htW : t₀ ≠ W := by
    obtain ⟨k0, m0, j0, hkm0, -, -, hk0, hm0, -⟩ := h0
    have hAV : A₀ ≠ mkPt L 0 := fun h =>
      hkm0 ((D.tile t₀).indep.injective (hk0.trans (h.trans hm0.symm)))
    exact hW.ne_of_vertex hk0 hAV (hne1 hA₀ hG1) (hne1 hA₀ hZ1)
  rcases hθW with hw | hw
  · exact hfig.1 W (by rw [S.B_eq]; exact hw)
  · exact hfig.2 t₀ W htW (by rw [S.B_eq]; exact hβ0) (by rw [S.B_eq]; exact hw)

/-- **the open `a`-edge from the corner `Q'` of angle `α + β` is interior to the target**: `G = (L − uuG, hhG)` is the other end of
the `a`-edge of the last `C1` tile of the run -/
theorem hint_right_ab (S : SetupG D e f α β γ L ax ay) {t : ℝ} (ht : 0 < t)
    (hax : ax = L - t * (e : ℝ)) (hay' : ay = t * rtG (e : ℝ) (f : ℝ))
    (hRmem : mkPt L 0 ∈ D.target.carrier)
    (hGmem : mkPt (L - uuG (e : ℝ) (f : ℝ)) (hhG (e : ℝ) (f : ℝ)) ∈ D.target.carrier) :
    openSegment ℝ (mkPt L 0) (mkPt (L - uuG (e : ℝ) (f : ℝ)) (hhG (e : ℝ) (f : ℝ)))
      ⊆ interior D.target.carrier := by
  have he0 := S.e0
  have hef := S.hef'
  have hhp := hhG_pos he0 hef
  have hu := uuG_spec he0 hef
  have hh' := hhG_spec he0 hef
  have hrt := rtG_pos he0 hef
  have key : 2 * (f : ℝ) ^ 2 * (rtG (e : ℝ) (f : ℝ) * uuG (e : ℝ) (f : ℝ) - (e : ℝ) * hhG (e : ℝ) (f : ℝ))
      = 2 * (f : ℝ) ^ 2 * (rtG (e : ℝ) (f : ℝ) * (e : ℝ) ^ 2) := by
    linear_combination (rtG (e : ℝ) (f : ℝ)) * hu - (e : ℝ) * hh'
  have hX : rtG (e : ℝ) (f : ℝ) * uuG (e : ℝ) (f : ℝ) - (e : ℝ) * hhG (e : ℝ) (f : ℝ)
      = rtG (e : ℝ) (f : ℝ) * (e : ℝ) ^ 2 :=
    mul_left_cancel₀ (two_f2_pos he0 hef).ne' key
  refine S.interior_seg hRmem hGmem (Or.inr (by rw [mkPt_one]; exact hhp)) (Or.inl ?_) (Or.inr ?_)
  · rw [gA_mk]; nlinarith [mul_pos S.hay S.hL]
  · rw [gB_mk, hax, hay']
    refine lt_of_lt_of_eq (b := t * (rtG (e : ℝ) (f : ℝ) * (e : ℝ) ^ 2)) ?_ ?_
    · exact mul_pos ht (mul_pos hrt (pow_pos he0 2))
    · linear_combination (-t) * hX

end right


/-! ## 7. The tile `T` beside the first tile, and (K1) -/

section next

variable {e f : ℕ} {α β γ L ax ay : ℝ}

/-- **The tile `T` beside the first tile `X₀ = U(0,0)`** (σ side of `ℓ`): `P = p(0,0) = A'`, `ℓ` the line of the `b`-edge of `X₀`
(`ε = 1`, `x = 0`), the open `b`-edge `(P, p(0,1))` interior to the target.  A tile of the side σ (all its vertices have `FXG ≤ lv`)
has a vertex at `P` and another one at `p(0, t)`, `t > 0`, on the ray from `P` through `p(0,1)`, and `t · b` is `a`, `b` or `c`
(the edge `[P, p(0,t)]` of `T` along `ℓ`).  The clamp at `P` is the boundary of the target (`SetupG.below_out`): `A'` is on the side
and the extension of `ℓ` beyond `P` leaves the target. -/
theorem corner_nextT (S : SetupG D e f α β γ L ax ay) {t₀ : Fin N}
    (h0 : HasV D t₀ (lpG (e : ℝ) (f : ℝ) 1 0 0 0) (lpG (e : ℝ) (f : ℝ) 1 0 (0 + 1) 0)
      (lpG (e : ℝ) (f : ℝ) 1 0 0 (0 + 1)))
    (hch1 : openSegment ℝ (lpG (e : ℝ) (f : ℝ) 1 0 0 0) (lpG (e : ℝ) (f : ℝ) 1 0 0 1) ⊆
      interior D.target.carrier) :
    ∃ (iT : Fin N) (k m : Fin 3) (t : ℝ), k ≠ m ∧ (D.tile iT).pts k = lpG (e : ℝ) (f : ℝ) 1 0 0 0 ∧
      (D.tile iT).pts m = lpG (e : ℝ) (f : ℝ) 1 0 0 t ∧ 0 < t ∧
      (∀ i, FXG (e : ℝ) (f : ℝ) 1 ((D.tile iT).pts i) ≤ lvG (e : ℝ) (f : ℝ) 1 0 0) ∧
      (t * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) = (e : ℝ) * f ∨
        t * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∨
        t * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) = (f : ℝ) ^ 2) := by
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have he0 := S.e0
  have hef := S.hef'
  have hb := S.b_pos
  have hhp := hhG_pos he0 hef
  have hPQ : lpG (e : ℝ) (f : ℝ) 1 0 0 0 ≠ lpG (e : ℝ) (f : ℝ) 1 0 0 1 :=
    lpG_ne_eta he0 hef (by norm_num)
  have hfP : FXG (e : ℝ) (f : ℝ) 1 (lpG (e : ℝ) (f : ℝ) 1 0 0 0) = lvG (e : ℝ) (f : ℝ) 1 0 0 :=
    FXG_lp hε 0 0
  have hfQ : FXG (e : ℝ) (f : ℝ) 1 (lpG (e : ℝ) (f : ℝ) 1 0 0 1) = lvG (e : ℝ) (f : ℝ) 1 0 0 :=
    FXG_lp hε 0 1
  have hfP' := ext_level (FXG (e : ℝ) (f : ℝ) 1) hfP hfQ 1
  have hP' := mem_openSegment_ext (lpG (e : ℝ) (f : ℝ) 1 0 0 0) (lpG (e : ℝ) (f : ℝ) 1 0 0 1)
    (s := 1) one_pos
  have hwall : ∀ y ∈ openSegment ℝ (lpG (e : ℝ) (f : ℝ) 1 0 0 0) (lpG (e : ℝ) (f : ℝ) 1 0 0 1),
      ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    obtain ⟨k0, m0, j0, hkm0, hkj0, hmj0, hk0, hm0, hj0⟩ := h0
    refine seg_wall D.toDissection (t := t₀) hkj0 ?_
    rw [hk0, hj0, zero_add]
    exact openSegment_subset_segment ℝ _ _ hy
  have hP1 : (lpG (e : ℝ) (f : ℝ) 1 0 0 0) 1 = 0 := by rw [lpG_snd]; ring
  have hQ1 : 0 < (lpG (e : ℝ) (f : ℝ) 1 0 0 1) 1 := by rw [lpG_snd]; linarith
  have hclampP := clamp_out D.toDissection (FXG (e : ℝ) (f : ℝ) 1) (lvG (e : ℝ) (f : ℝ) 1 0 0)
    (S.below_out hP1 hQ1)
  obtain ⟨ed, hed, k, m, t, hkm, hk, ht, hm, hle, -, hdist⟩ :=
    next_tile D.toDissection (FXG (e : ℝ) (f : ℝ) 1) (FXG_ne he0 hef hε) (lvG (e : ℝ) (f : ℝ) 1 0 0)
      hPQ hfP hfQ hfP' hP' hch1 hwall hclampP
  have hl : AffineMap.lineMap (lpG (e : ℝ) (f : ℝ) 1 0 0 0) (lpG (e : ℝ) (f : ℝ) 1 0 0 1) t
      = lpG (e : ℝ) (f : ℝ) 1 0 0 t := by
    rw [lineMap_lpG]
    exact lpG_congr (by ring) (by ring)
  rw [hl] at hm hdist
  have hd : dist (lpG (e : ℝ) (f : ℝ) 1 0 0 0) (lpG (e : ℝ) (f : ℝ) 1 0 0 t)
      = t * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) :=
    dist_lpG he0 hef hε (mul_nonneg ht.le hb.le) (by unfold QfG; ring)
  have hlen := edge_length_casesG D S.hM ed.1 ed.2
  rw [hdist, hd] at hlen
  exact ⟨ed.1, k, m, t, hkm, hk, hm, ht, hle, hlen⟩

/-- **(K1) at the corner `A'` from the tile `T` beside the first tile, or the mirror**: either `T` lays `a` or `c` along `ℓ`
from `P` (then (K1) holds at `js = 0`, in the form `K1J`), or `T` has the whole `b`-edge `[P, p(0,1)]` of `X₀` (the tile beside
`X₀` has an edge of length `b` on `ℓ`; `t · b = b` gives `t = 1`). -/
theorem corner_K1J_or_b (S : SetupG D e f α β γ L ax ay) {t₀ : Fin N}
    (h0 : HasV D t₀ (lpG (e : ℝ) (f : ℝ) 1 0 0 0) (lpG (e : ℝ) (f : ℝ) 1 0 (0 + 1) 0)
      (lpG (e : ℝ) (f : ℝ) 1 0 0 (0 + 1)))
    (hch1 : openSegment ℝ (lpG (e : ℝ) (f : ℝ) 1 0 0 0) (lpG (e : ℝ) (f : ℝ) 1 0 0 1) ⊆
      interior D.target.carrier) :
    K1J D (e : ℝ) (f : ℝ) 1 0 0 ∨
    ∃ (iT : Fin N) (k m : Fin 3), k ≠ m ∧ (D.tile iT).pts k = lpG (e : ℝ) (f : ℝ) 1 0 0 0 ∧
      (D.tile iT).pts m = lpG (e : ℝ) (f : ℝ) 1 0 0 1 ∧
      ∀ i, FXG (e : ℝ) (f : ℝ) 1 ((D.tile iT).pts i) ≤ lvG (e : ℝ) (f : ℝ) 1 0 0 := by
  obtain ⟨iT, k, m, t, hkm, hk, hm, ht, hle, hlen⟩ := corner_nextT S h0 hch1
  have hb := S.b_pos
  rcases hlen with h | h | h
  · refine Or.inl ⟨iT, k, m, t, hkm, ?_, ?_, ht, Or.inl h, hle⟩
    · rw [Nat.cast_zero]; exact hk
    · rw [Nat.cast_zero, zero_add]; exact hm
  · refine Or.inr ⟨iT, k, m, hkm, hk, ?_, hle⟩
    have ht1 : t = 1 := by
      have h2 : (t - 1) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) = 0 := by linarith
      rcases mul_eq_zero.mp h2 with h3 | h3
      · linarith
      · exact absurd h3 hb.ne'
    subst ht1; exact hm
  · refine Or.inl ⟨iT, k, m, t, hkm, ?_, ?_, ht, Or.inr h, hle⟩
    · rw [Nat.cast_zero]; exact hk
    · rw [Nat.cast_zero, zero_add]; exact hm

end next

end Erdos634.Draft.SideRunGA

#print axioms Erdos634.Draft.SideRunGA.ab_zero
#print axioms Erdos634.Draft.SideRunGA.cos_alpha
#print axioms Erdos634.Draft.SideRunGA.corner_left_two
#print axioms Erdos634.Draft.SideRunGA.corner_left_three
#print axioms Erdos634.Draft.SideRunGA.corner_right_ab
#print axioms Erdos634.Draft.SideRunGA.corner_counts
#print axioms Erdos634.Draft.SideRunGA.figure_alpha
#print axioms Erdos634.Draft.SideRunGA.figure_ab
#print axioms Erdos634.Draft.SideRunGA.first_tile_alpha
#print axioms Erdos634.Draft.SideRunGA.hch_cornerA_two
#print axioms Erdos634.Draft.SideRunGA.hch_cornerA_three
#print axioms Erdos634.Draft.SideRunGA.hch_cornerA
#print axioms Erdos634.Draft.SideRunGA.corner_A_angle
#print axioms Erdos634.Draft.SideRunGA.bad_corner_right
#print axioms Erdos634.Draft.SideRunGA.hint_right_ab
#print axioms Erdos634.Draft.SideRunGA.corner_nextT
#print axioms Erdos634.Draft.SideRunGA.corner_K1J_or_b
